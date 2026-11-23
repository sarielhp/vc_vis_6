import RootTask.VCDim6.CaseCertFormat
import RootTask.VCDim6.ChunkedCertExec

/-!
# Zero-Mathlib Read-Only `BinTrie Clause` Master-Table Sharded RUP Verifier (`MasterTableRUP`)

Stores all clauses `1 .. m_core + n_rup - 1` directly as pre-decoded `Clause` (`List Lit`) values
in an immutable `BinTrie Clause` (`master`):
1. **Zero `Nat` arithmetic & zero `cache` copying during RUP verification**:
   `checkMidRupList` and `checkFinRupList` take `steps : List (List PIdx)` directly, check
   `allHintsLt cur hints = true` via pure constructor `pidxLt`, look up `master.get cur` in
   $O(\log N)$ pointer hops, and run `rupPropagate master fmap hints` directly on `master`!
2. **Core shards (`checkCoreShard`)**: verify `count` core justifications against `master.get cid`
   in $O(\text{count} \cdot \log N)$ steps.
-/

namespace VCDim6.FastTrieRUP

noncomputable section

/-- Positive integer semantics of `PIdx` (`xH ↦ 1`, `xO p ↦ 2p`, `xI p ↦ 2p + 1`). -/
def natOfPIdx : PIdx → Nat
  | .xH => 1
  | .xO p => 2 * natOfPIdx p
  | .xI p => 2 * natOfPIdx p + 1

/-- Simultaneous `(p < q, p ≤ q)` comparison on `PIdx` via direct `PIdx.rec` (zero `Nat` ops!). -/
def pidxCmpLtLe (p : PIdx) : PIdx → Bool × Bool :=
  @PIdx.rec (fun _ => PIdx → Bool × Bool)
    (fun q => match q with
      | .xH => (false, true)
      | .xO _ => (true, true)
      | .xI _ => (true, true))
    (fun _ ih q => match q with
      | .xH => (false, false)
      | .xO q' => ih q'
      | .xI q' => let r := ih q'; (r.2, r.2))
    (fun _ ih q => match q with
      | .xH => (false, false)
      | .xO q' => let r := ih q'; (r.1, r.1)
      | .xI q' => ih q')
    p

@[inline] def pidxLt (p q : PIdx) : Bool :=
  (pidxCmpLtLe p q).1

/-! ## 1. Core-Clause Verification Shard (`checkCoreShard`) -/

def stepCoreShard (ctx : CertCtx) (master : BinTrie Clause)
    (st : PIdx × Nat) (bs : ByteStream) : Option (Bool × (PIdx × Nat) × ByteStream) :=
  let (cid, rem) := st
  match rem with
  | 0 => some (true, (cid, 0), bs)
  | r + 1 =>
    match decodeOneJust ctx bs with
    | some (some cl, bs1) =>
      match master.get cid with
      | none => none
      | some clM =>
        match clauseEq clM cl with
        | false => none
        | true =>
          match strictPIdx cid.succ with
          | .xH => some (false, (.xH, r), bs1)
          | .xO p => some (false, (.xO p, r), bs1)
          | .xI p => some (false, (.xI p, r), bs1)
    | _ => none

/-- Verifies `count` consecutive core clauses from `startCid` to `endCid` (`PIdx`). -/
def checkCoreShard (spec : CaseSpec) (varTree : ChunkTree) (master : BinTrie Clause)
    (startCid endCid : PIdx) (count : Nat) (justShard : ChunkTree) : Bool :=
  match buildTripleTrieTree (7 + spec.masks.length) varTree with
  | none => false
  | some tripleTrie =>
    let ctx := mkCertCtx spec tripleTrie
    match runStreamTower (stepCoreShard ctx master) 3 (startCid, count)
        (ByteStream.ofTree justShard) with
    | some (true, (cidOut, 0), _) => pidxEq cidOut endCid
    | _ => false

/-! ## 2. Pure-Constructor RUP Verification Shards (`checkMidRupList` & `checkFinRupList`) -/

/-- Checks `pidxLt hid cid = true` for every `hid ∈ hints` via direct `@List.rec`. -/
def allHintsLt (cid : PIdx) (hints : List PIdx) : Bool :=
  @List.rec PIdx (fun _ => Bool)
    true
    (fun hid _ ih =>
      match pidxLt hid cid with
      | false => false
      | true => ih)
    hints

/-- Verifies a list of RUP hint lists starting at `cid : PIdx` directly against `master : BinTrie Clause`
    with zero `Nat` arithmetic and zero `BinTrie` insertions! -/
def checkRupList (master : BinTrie Clause) (steps : List (List PIdx)) (cid : PIdx) : Option PIdx :=
  @List.rec (List PIdx) (fun _ => PIdx → Option PIdx)
    (fun cur => some cur)
    (fun hints _ ih cur =>
      match allHintsLt cur hints with
      | false => none
      | true =>
        match master.get cur with
        | none => none
        | some cl =>
          let ok :=
            match initFalseLits .leaf cl with
            | none => true
            | some fmap => rupPropagate master fmap hints
          match ok with
          | false => none
          | true =>
            match strictPIdx cur.succ with
            | .xH => ih .xH
            | .xO p => ih (.xO p)
            | .xI p => ih (.xI p))
    steps cid

/-- Verifies non-final RUP steps from `startCid` to `endCid` (`PIdx`). -/
def checkMidRupList (master : BinTrie Clause) (startCid endCid : PIdx) (steps : List (List PIdx)) : Bool :=
  match checkRupList master steps startCid with
  | some cidOut => pidxEq cidOut endCid
  | none => false

/-- Verifies `midSteps.length` RUP steps starting at `startCid : PIdx` followed immediately
    by the final empty-clause (`[]`) RUP conflict step `finHints`! -/
def checkFinRupList (master : BinTrie Clause) (startCid : PIdx)
    (midSteps : List (List PIdx)) (finHints : List PIdx) : Bool :=
  match checkRupList master midSteps startCid with
  | none => false
  | some cidFin =>
    match allHintsLt cidFin finHints with
    | false => false
    | true => rupPropagate master .leaf finHints

/-- Zero-Mathlib composable RUP segment certificate so each shard file can verify sub-blocks
    of ~5,500 hints in separate `theorem` declarations (clearing Lean's kernel WHNF cache
    between sub-blocks and capping per-worker RAM at ~1.5 GB!). -/
inductive VerifiedMidRup (master : BinTrie Clause) : PIdx → PIdx → Prop
  | step {s e : PIdx} {steps : List (List PIdx)} :
      checkMidRupList master s e steps = true → VerifiedMidRup master s e
  | trans {a b c : PIdx} :
      VerifiedMidRup master a b → VerifiedMidRup master b c → VerifiedMidRup master a c

inductive VerifiedFinRup (master : BinTrie Clause) : PIdx → Prop
  | fin {s : PIdx} {steps : List (List PIdx)} {fh : List PIdx} :
      checkFinRupList master s steps fh = true → VerifiedFinRup master s
  | cons {a b : PIdx} :
      VerifiedMidRup master a b → VerifiedFinRup master b → VerifiedFinRup master a

end

end VCDim6.FastTrieRUP
