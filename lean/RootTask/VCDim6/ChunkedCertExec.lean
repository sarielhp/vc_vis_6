import RootTask.VCDim6.CaseCertFormat

/-!
# Zero-Mathlib Live-Cut Checkpointed RUP Verifier (`ChunkedCertExec`)

Splits large RUP proofs (`hints > 30,000`) into sequential top-level `theorem` chunks (`≤ 20,000`
hints each), so Lean's C++ kernel frees 100% of `m_whnf_core_cache` between chunks and peak RAM
stays under ~6 GB even on multi-million-hint certificates:
1. Core clauses are partitioned by their first-use chunk (`justChunk_c` decodes each core clause
   at most once across the entire proof, keeping its original `cid : PIdx`).
2. `inLive_c` / `outLive_c` encode raw `(id : PIdx, cl : Clause)` streams of clauses live across
   chunk boundaries (`born_chunk ≤ c < last_use_chunk`).
3. `checkMidChunk` verifies `inLive_c + justChunk_c --(RUP)--> outLive_c`, and `checkFinalChunk`
   verifies `inLive_{K-1} + justChunk_{K-1} --(RUP)--> []`.
-/

namespace VCDim6.FastTrieRUP

noncomputable section

/-- Direct `@PIdx.rec` equality test on `PIdx` (zero `DecidableEq` / `.brecOn`). -/
def pidxEq (a : PIdx) : PIdx → Bool :=
  @PIdx.rec (fun _ => PIdx → Bool)
    (fun b => match b with | .xH => true | _ => false)
    (fun _ ih b => match b with | .xO q => ih q | _ => false)
    (fun _ ih b => match b with | .xI q => ih q | _ => false)
    a

theorem pidxEq_iff (a b : PIdx) : pidxEq a b = true ↔ a = b := by
  induction a generalizing b with
  | xH => cases b <;> simp [pidxEq]
  | xO p ih =>
    cases b with
    | xO q => change pidxEq p q = true ↔ PIdx.xO p = PIdx.xO q; simp [ih q]
    | _ => simp [pidxEq]
  | xI p ih =>
    cases b with
    | xI q => change pidxEq p q = true ↔ PIdx.xI p = PIdx.xI q; simp [ih q]
    | _ => simp [pidxEq]

def litEqB (x y : Lit) : Bool :=
  match x.1, y.1 with
  | true, true => pidxEq x.2 y.2
  | false, false => pidxEq x.2 y.2
  | _, _ => false

theorem litEqB_iff (x y : Lit) : litEqB x y = true ↔ x = y := by
  rcases x with ⟨bx, px⟩; rcases y with ⟨by_, py⟩
  cases bx <;> cases by_ <;> simp [litEqB, pidxEq_iff]

/-- Direct `@List.rec` equality test on `Clause` (zero `.brecOn`). -/
def clauseEq (c1 : Clause) : Clause → Bool :=
  @List.rec Lit (fun _ => Clause → Bool)
    (fun c2 => match c2 with | [] => true | _ :: _ => false)
    (fun l1 _ ih c2 =>
      match c2 with
      | [] => false
      | l2 :: rest2 =>
        match litEqB l1 l2 with
        | true => ih rest2
        | false => false)
    c1

theorem clauseEq_iff (c1 c2 : Clause) : clauseEq c1 c2 = true ↔ c1 = c2 := by
  induction c1 generalizing c2 with
  | nil => cases c2 <;> simp [clauseEq]
  | cons l1 ls1 ih =>
    cases c2 with
    | nil => simp [clauseEq]
    | cons l2 ls2 =>
      change (match litEqB l1 l2 with | true => clauseEq ls1 ls2 | false => false) = true ↔
        l1 :: ls1 = l2 :: ls2
      cases h : litEqB l1 l2
      · constructor
        · intro hc; nomatch hc
        · intro hc
          injection hc with hl _
          subst hl
          rw [(litEqB_iff l1 l1).mpr rfl] at h
          nomatch h
      · simp [(litEqB_iff l1 l2).mp h, ih ls2]

/-! ## Generic `Nat.rec` State-Stream Tower (`Bool × σ × ByteStream`) -/

def chainStream2 {σ : Type}
    (f : σ → ByteStream → Option (Bool × σ × ByteStream)) (k : Nat) :
    σ → ByteStream → Option (Bool × σ × ByteStream) :=
  @Nat.rec (fun _ => σ → ByteStream → Option (Bool × σ × ByteStream))
    (fun st bs => some (false, st, bs))
    (fun _ ih st bs =>
      match f st bs with
      | none => none
      | some (true, st', bs') => some (true, st', bs')
      | some (false, st', bs') => ih st' bs')
    k

def runStreamTower {σ : Type}
    (step : σ → ByteStream → Option (Bool × σ × ByteStream)) (lvl : Nat) :
    σ → ByteStream → Option (Bool × σ × ByteStream) :=
  @Nat.rec (fun _ => σ → ByteStream → Option (Bool × σ × ByteStream))
    (chainStream2 step 16)
    (fun _ ih => chainStream2 ih 16)
    lvl

/-! ## 1. Raw `(id, cl)` Stream Loader & Verifier (`inLive` / `outLive`) -/

/-- Reads one raw `(id, cl)` entry (`0` = end of stream, `1` = `<id:PIdx> <nLits:Nat> <lits...>`). -/
def readOneRawEntry (bs : ByteStream) : Option (Option (PIdx × Clause) × ByteStream) :=
  match bs.next with
  | none => none
  | some (0, bs1) => some (none, bs1)
  | some (1, bs1) =>
    match bsReadPIdx bs1 with
    | none => none
    | some (id, bs2) =>
      match bsReadNat bs2 with
      | none => none
      | some (nLits, bs3) =>
        match bsReadLits nLits [] bs3 with
        | none => none
        | some (cl, bs4) => some (some (id, cl), bs4)
  | some (_, _) => none

def stepInsertRaw (db : BinTrie Clause) (bs : ByteStream) :
    Option (Bool × BinTrie Clause × ByteStream) :=
  match readOneRawEntry bs with
  | none => none
  | some (none, bs1) => some (true, db, bs1)
  | some (some (id, cl), bs1) =>
    let cl' := strictClause cl
    withStrictTrie (db.insert (strictPIdx id) cl') (fun db' =>
      some (false, db', bs1))

def insertRawTree (db : BinTrie Clause) (rawTree : ChunkTree) : Option (BinTrie Clause) :=
  match runStreamTower stepInsertRaw 4 db (ByteStream.ofTree rawTree) with
  | some (true, db', _) => some db'
  | _ => none

def stepVerifyRaw (db : BinTrie Clause) (_ : Unit) (bs : ByteStream) :
    Option (Bool × Unit × ByteStream) :=
  match readOneRawEntry bs with
  | none => none
  | some (none, bs1) => some (true, (), bs1)
  | some (some (id, cl), bs1) =>
    match db.get id with
    | none => none
    | some clDb =>
      match clauseEq cl clDb with
      | true => some (false, (), bs1)
      | false => none

def verifyRawTree (db : BinTrie Clause) (rawTree : ChunkTree) : Bool :=
  match runStreamTower (stepVerifyRaw db) 4 () (ByteStream.ofTree rawTree) with
  | some (true, _, _) => true
  | _ => false

/-! ## 2. Indexed Core-Clause Stream Loader (`justChunk`) -/

/-- Reads `0` (end) or `1, <cid : PIdx>, <decodeOneJust>`. -/
def stepIdJust (ctx : CertCtx) (db : BinTrie Clause) (bs : ByteStream) :
    Option (Bool × BinTrie Clause × ByteStream) :=
  match bs.next with
  | none => none
  | some (0, bs1) => some (true, db, bs1)
  | some (1, bs1) =>
    match bsReadPIdx bs1 with
    | none => none
    | some (cid, bs2) =>
      match decodeOneJust ctx bs2 with
      | some (some cl, bs3) =>
        let cl' := strictClause cl
        withStrictTrie (db.insert (strictPIdx cid) cl') (fun db' =>
          some (false, db', bs3))
      | _ => none
  | some (_, _) => none

def insertIdJustTree (ctx : CertCtx) (db : BinTrie Clause) (justChunk : ChunkTree) :
    Option (BinTrie Clause) :=
  match runStreamTower (stepIdJust ctx) 4 db (ByteStream.ofTree justChunk) with
  | some (true, db', _) => some db'
  | _ => none

/-! ## 3. Mid-Chunk RUP Executor (`rupChunk`) -/

/-- Reads `0` (end of mid-chunk) or `1, <execOneRupStep>`. -/
def stepMidRup (db : BinTrie Clause) (bs : ByteStream) :
    Option (Bool × BinTrie Clause × ByteStream) :=
  match bs.next with
  | none => none
  | some (0, bs1) => some (true, db, bs1)
  | some (1, bs1) =>
    match execOneRupStep db bs1 with
    | some (false, db', bs2) => some (false, db', bs2)
    | _ => none
  | some (_, _) => none

def execMidRupTree (db : BinTrie Clause) (rupChunk : ChunkTree) : Option (BinTrie Clause) :=
  match runStreamTower stepMidRup 4 db (ByteStream.ofTree rupChunk) with
  | some (true, db', _) => some db'
  | _ => none

/-! ## 4. Top-Level Pure-Kernel Verifier Entry Points -/

def checkVarTree (spec : CaseSpec) (varTree : ChunkTree) : Bool :=
  match buildTripleTrieTree (7 + spec.masks.length) varTree with
  | some _ => true
  | none => false

def mkCertCtx (spec : CaseSpec) (tripleTrie : TripleTrie) : CertCtx := {
  spec := spec
  n_pts := 7 + spec.masks.length
  bccw := buildBccw spec
  ptKeyTrie := .leaf
  maskTrie := buildMaskTrieAux .xH spec.masks .leaf
  tripleTrie := tripleTrie
}

/-- Verifies a non-final chunk `c`: loads `inLive`, decodes `justChunk`, runs `rupChunk`,
    and checks all clauses in `outLive` are present in the resulting `BinTrie Clause`. -/
def checkMidChunk (spec : CaseSpec)
    (varTree justChunk inLive rupChunk outLive : ChunkTree) : Bool :=
  match buildTripleTrieTree (7 + spec.masks.length) varTree with
  | none => false
  | some tripleTrie =>
    let ctx := mkCertCtx spec tripleTrie
    match insertRawTree .leaf inLive with
    | none => false
    | some db0 =>
      match insertIdJustTree ctx db0 justChunk with
      | none => false
      | some db1 =>
        match execMidRupTree db1 rupChunk with
        | none => false
        | some db2 => verifyRawTree db2 outLive

/-- Verifies the final chunk `K - 1`: loads `inLive`, decodes `justChunk`, and derives `[]`
    via `checkTreeRUP`. -/
def checkFinalChunk (spec : CaseSpec)
    (varTree justChunk inLive rupChunk : ChunkTree) : Bool :=
  match buildTripleTrieTree (7 + spec.masks.length) varTree with
  | none => false
  | some tripleTrie =>
    let ctx := mkCertCtx spec tripleTrie
    match insertRawTree .leaf inLive with
    | none => false
    | some db0 =>
      match insertIdJustTree ctx db0 justChunk with
      | none => false
      | some db1 => checkTreeRUP db1 rupChunk

end

end VCDim6.FastTrieRUP
