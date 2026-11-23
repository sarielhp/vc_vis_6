import RootTask.VCDim6.CoreClauseSoundness
import RootTask.VCDim6.ChunkedCertExec

open scoped Classical
open VCDim6.FastTrieRUP ChirotopeSoundness

noncomputable section

namespace VCDim6

/-!
# Soundness of Checkpointed Multi-Theorem RUP Verification (`ChunkedCertSoundness`)

Proves soundness of `checkVarTree`, `checkMidChunk`, and `checkFinalChunk` from `ChunkedCertExec`,
enabling multi-million-hint RUP refutations to be split into bounded-memory (`< 6 GB`) top-level
theorem chunks with zero `native_decide` and zero `trustCompiler`.
-/

/-- Semantic invariant carried across chunk boundaries: inserting `rawTree` into `.leaf`
    yields a trie of clauses all satisfied by `val`. -/
def EvalRawTree (val : PIdx → Bool) (rawTree : ChunkTree) : Prop :=
  ∀ db : BinTrie Clause, insertRawTree .leaf rawTree = some db → EvalTrieCNF val db

theorem evalTrieCNF_leaf (val : PIdx → Bool) : EvalTrieCNF val .leaf :=
  fun k _ hg => by rw [BinTrie.get_leaf] at hg; nomatch hg

/-- Base invariant for Chunk 0 (`inLive = .leaf 0`, encoding immediate end-of-stream byte `0`). -/
theorem evalRawTree_empty_stream (val : PIdx → Bool) : EvalRawTree val (.leaf 0) := by
  intro db hins
  have heq : insertRawTree .leaf (.leaf 0) = some .leaf := rfl
  rw [heq] at hins
  injection hins with hdb; subst hdb
  exact evalTrieCNF_leaf val

/-! ## Generic `chainStream2` / `runStreamTower` Soundness Helpers -/

private lemma chainStream2_preserve {val : PIdx → Bool}
    {step : BinTrie Clause → ByteStream → Option (Bool × BinTrie Clause × ByteStream)}
    (hstep : ∀ {db db' bs bs' done},
      step db bs = some (done, db', bs') → EvalTrieCNF val db → EvalTrieCNF val db') :
    ∀ (k : ℕ) {db db' : BinTrie Clause} {bs bs' : ByteStream} {done : Bool},
      chainStream2 step k db bs = some (done, db', bs') →
      EvalTrieCNF val db → EvalTrieCNF val db'
  | 0, _, _, _, _, _, h, hdb => by
    injection h with hp; rcases Prod.mk.inj hp with ⟨_, hp2⟩
    rcases Prod.mk.inj hp2 with ⟨rfl, _⟩; exact hdb
  | k + 1, db, _, bs, _, _, h, hdb => by
    unfold chainStream2 at h
    cases hex : step db bs with
    | none => simp only [hex] at h; nomatch h
    | some res =>
      rcases res with ⟨d1, db1, bs1⟩
      simp only [hex] at h
      have hdb1 := hstep hex hdb
      cases d1
      · exact chainStream2_preserve hstep k h hdb1
      · injection h with hp; rcases Prod.mk.inj hp with ⟨_, hp2⟩
        rcases Prod.mk.inj hp2 with ⟨rfl, _⟩; exact hdb1

private lemma runStreamTower_preserve {val : PIdx → Bool}
    {step : BinTrie Clause → ByteStream → Option (Bool × BinTrie Clause × ByteStream)}
    (hstep : ∀ {db db' bs bs' done},
      step db bs = some (done, db', bs') → EvalTrieCNF val db → EvalTrieCNF val db') :
    ∀ (lvl : ℕ) {db db' : BinTrie Clause} {bs bs' : ByteStream} {done : Bool},
      runStreamTower step lvl db bs = some (done, db', bs') →
      EvalTrieCNF val db → EvalTrieCNF val db'
  | 0, _, _, _, _, _, h, hdb => by
    unfold runStreamTower at h
    exact chainStream2_preserve hstep 16 h hdb
  | lvl + 1, _, _, _, _, _, h, hdb => by
    unfold runStreamTower at h
    exact chainStream2_preserve (runStreamTower_preserve hstep lvl) 16 h hdb

/-! ## Lockstep Soundness of `verifyRawTree` -> `insertRawTree` -/

private lemma stepVerify_insert_lockstep {val : PIdx → Bool} {dbSrc : BinTrie Clause}
    (hSrc : EvalTrieCNF val dbSrc)
    {u' : Unit} {db db' : BinTrie Clause} {bs bsV bsI : ByteStream} {dV dI : Bool}
    (hV : stepVerifyRaw dbSrc () bs = some (dV, u', bsV))
    (hI : stepInsertRaw db bs = some (dI, db', bsI))
    (hdb : EvalTrieCNF val db) :
    dV = dI ∧ bsV = bsI ∧ EvalTrieCNF val db' := by
  unfold stepVerifyRaw at hV
  unfold stepInsertRaw at hI
  cases hr : readOneRawEntry bs with
  | none => rw [hr] at hV; nomatch hV
  | some pr =>
    rcases pr with ⟨entOpt, bs1⟩
    rw [hr] at hV hI
    cases entOpt with
    | none =>
      injection hV with hpV; rcases Prod.mk.inj hpV with ⟨rfl, hpV2⟩
      rcases Prod.mk.inj hpV2 with ⟨_, rfl⟩
      injection hI with hpI; rcases Prod.mk.inj hpI with ⟨rfl, hpI2⟩
      rcases Prod.mk.inj hpI2 with ⟨rfl, rfl⟩
      exact ⟨rfl, rfl, hdb⟩
    | some ic =>
      rcases ic with ⟨id, cl⟩
      dsimp only at hV hI
      cases hg : dbSrc.get id with
      | none => simp only [hg] at hV; nomatch hV
      | some clDb =>
        simp only [hg] at hV
        cases heq : clauseEq cl clDb with
        | false => simp only [heq] at hV; nomatch hV
        | true =>
          simp only [heq] at hV
          simp only [withStrictTrie_eq, strictClause_eq, strictPIdx_eq] at hI
          injection hV with hpV; rcases Prod.mk.inj hpV with ⟨rfl, hpV2⟩
          rcases Prod.mk.inj hpV2 with ⟨_, rfl⟩
          injection hI with hpI; rcases Prod.mk.inj hpI with ⟨rfl, hpI2⟩
          rcases Prod.mk.inj hpI2 with ⟨rfl, rfl⟩
          have hcl_eq : cl = clDb := (clauseEq_iff cl clDb).mp heq
          subst hcl_eq
          exact ⟨rfl, rfl, evalTrieCNF_insert hdb id (hSrc id cl hg)⟩

private lemma chainStream2_lockstep {val : PIdx → Bool}
    {fV : Unit → ByteStream → Option (Bool × Unit × ByteStream)}
    {fI : BinTrie Clause → ByteStream → Option (Bool × BinTrie Clause × ByteStream)}
    (hf : ∀ {u' db db' bs bsV bsI dV dI},
      fV () bs = some (dV, u', bsV) →
      fI db bs = some (dI, db', bsI) →
      EvalTrieCNF val db →
      dV = dI ∧ bsV = bsI ∧ EvalTrieCNF val db') :
    ∀ (k : ℕ) {u' : Unit} {db db' : BinTrie Clause} {bs bsV bsI : ByteStream} {dV dI : Bool},
      chainStream2 fV k () bs = some (dV, u', bsV) →
      chainStream2 fI k db bs = some (dI, db', bsI) →
      EvalTrieCNF val db →
      dV = dI ∧ bsV = bsI ∧ EvalTrieCNF val db'
  | 0, _, _, _, _, _, _, _, _, hV, hI, hdb => by
    injection hV with hpV; rcases Prod.mk.inj hpV with ⟨rfl, hpV2⟩; rcases Prod.mk.inj hpV2 with ⟨_, rfl⟩
    injection hI with hpI; rcases Prod.mk.inj hpI with ⟨rfl, hpI2⟩; rcases Prod.mk.inj hpI2 with ⟨rfl, rfl⟩
    exact ⟨rfl, rfl, hdb⟩
  | k + 1, _, db, _, bs, _, _, _, _, hV, hI, hdb => by
    unfold chainStream2 at hV hI
    cases hexV : fV () bs with
    | none => simp only [hexV] at hV; nomatch hV
    | some rV =>
      cases hexI : fI db bs with
      | none => simp only [hexI] at hI; nomatch hI
      | some rI =>
        rcases rV with ⟨d1V, u1, bs1V⟩
        rcases rI with ⟨d1I, db1, bs1I⟩
        simp only [hexV] at hV; simp only [hexI] at hI
        obtain ⟨rfl, rfl, hdb1⟩ := hf hexV hexI hdb
        cases d1V
        · cases u1; exact chainStream2_lockstep hf k hV hI hdb1
        · injection hV with hpV; rcases Prod.mk.inj hpV with ⟨rfl, hpV2⟩; rcases Prod.mk.inj hpV2 with ⟨_, rfl⟩
          injection hI with hpI; rcases Prod.mk.inj hpI with ⟨rfl, hpI2⟩; rcases Prod.mk.inj hpI2 with ⟨rfl, rfl⟩
          exact ⟨rfl, rfl, hdb1⟩

private lemma runStreamTower_lockstep {val : PIdx → Bool} {dbSrc : BinTrie Clause}
    (hSrc : EvalTrieCNF val dbSrc) :
    ∀ (lvl : ℕ) {u' : Unit} {db db' : BinTrie Clause} {bs bsV bsI : ByteStream} {dV dI : Bool},
      runStreamTower (stepVerifyRaw dbSrc) lvl () bs = some (dV, u', bsV) →
      runStreamTower stepInsertRaw lvl db bs = some (dI, db', bsI) →
      EvalTrieCNF val db →
      dV = dI ∧ bsV = bsI ∧ EvalTrieCNF val db'
  | 0, _, _, _, _, _, _, _, _, hV, hI, hdb => by
    unfold runStreamTower at hV hI
    exact chainStream2_lockstep (stepVerify_insert_lockstep hSrc) 16 hV hI hdb
  | lvl + 1, _, _, _, _, _, _, _, _, hV, hI, hdb => by
    unfold runStreamTower at hV hI
    exact chainStream2_lockstep (runStreamTower_lockstep hSrc lvl) 16 hV hI hdb

private lemma verifyRawTree_sound {val : PIdx → Bool} {dbSrc : BinTrie Clause} {rawTree : ChunkTree}
    (hSrc : EvalTrieCNF val dbSrc) (hVer : verifyRawTree dbSrc rawTree = true) :
    EvalRawTree val rawTree := by
  intro dbOut hIns
  unfold verifyRawTree at hVer
  unfold insertRawTree at hIns
  cases hrV : runStreamTower (stepVerifyRaw dbSrc) 4 () (ByteStream.ofTree rawTree) with
  | none => rw [hrV] at hVer; exact Bool.noConfusion hVer
  | some pV =>
    rcases pV with ⟨dV, u', bsV⟩
    rw [hrV] at hVer
    cases dV; · exact Bool.noConfusion hVer
    cases hrI : runStreamTower stepInsertRaw 4 .leaf (ByteStream.ofTree rawTree) with
    | none => rw [hrI] at hIns; nomatch hIns
    | some pI =>
      rcases pI with ⟨dI, db', bsI⟩
      rw [hrI] at hIns
      cases dI; · nomatch hIns
      injection hIns with heq; subst heq
      exact (runStreamTower_lockstep hSrc 4 hrV hrI (evalTrieCNF_leaf val)).2.2

/-! ## Soundness of `insertIdJustTree` and `execMidRupTree` -/

private lemma stepIdJust_sound {P : Set (ℝ × ℝ)} {S : Fin 7 → ℝ × ℝ} {w : Finset (Fin 7) → ℝ × ℝ}
    {ctx : CertCtx}
    (hV : ValidCanonicalInstance P S w ctx.spec)
    (hM : ValidMasks ctx.spec.masks)
    (hn_pts : ctx.n_pts = 7 + ctx.spec.masks.length)
    (hbccw_eq : ctx.bccw = buildBccw ctx.spec)
    (hm_eq : ctx.maskTrie = buildMaskTrieAux .xH ctx.spec.masks .leaf)
    {val : PIdx → Bool}
    (hval : ∀ {i j k : ℕ} (hij : i < j) (hjk : j < k) (hk : k < ctx.n_pts) {v : PIdx},
      ctx.tripleTrie.get3 (ptKey i) (ptKey j) (ptKey k) = some v →
      val v = orientSign (pointSeq S w (specWitnessEmb hM) ⟨i, by omega⟩)
                         (pointSeq S w (specWitnessEmb hM) ⟨j, by omega⟩)
                         (pointSeq S w (specWitnessEmb hM) ⟨k, by omega⟩))
    {db db' : BinTrie Clause} {bs bs' : ByteStream} {done : Bool}
    (hstep : stepIdJust ctx db bs = some (done, db', bs'))
    (hdb : EvalTrieCNF val db) :
    EvalTrieCNF val db' := by
  unfold stepIdJust at hstep
  cases hn : bs.next with
  | none => rw [hn] at hstep; nomatch hstep
  | some pn =>
    rcases pn with ⟨b, bs1⟩
    rw [hn] at hstep
    cases b with
    | zero =>
      injection hstep with hp; rcases Prod.mk.inj hp with ⟨_, hp2⟩
      rcases Prod.mk.inj hp2 with ⟨rfl, _⟩; exact hdb
    | succ b0 =>
      cases b0 with
      | zero =>
        cases hpidx : bsReadPIdx bs1 with
        | none => simp only [hpidx] at hstep; nomatch hstep
        | some pp =>
          rcases pp with ⟨cid, bs2⟩
          simp only [hpidx] at hstep
          cases hd : decodeOneJust ctx bs2 with
          | none => simp only [hd] at hstep; nomatch hstep
          | some pd =>
            rcases pd with ⟨clOpt, bs3⟩
            simp only [hd] at hstep
            cases clOpt with
            | none => nomatch hstep
            | some cl =>
              simp only [withStrictTrie_eq, strictClause_eq, strictPIdx_eq] at hstep
              injection hstep with hp; rcases Prod.mk.inj hp with ⟨_, hp2⟩
              rcases Prod.mk.inj hp2 with ⟨hdb_eq, _⟩; subst hdb_eq
              exact evalTrieCNF_insert hdb cid (decodeOneJust_sound hV hM hn_pts hbccw_eq hm_eq hval hd)
      | succ _ => nomatch hstep

private lemma insertIdJustTree_sound {P : Set (ℝ × ℝ)} {S : Fin 7 → ℝ × ℝ} {w : Finset (Fin 7) → ℝ × ℝ}
    {ctx : CertCtx}
    (hV : ValidCanonicalInstance P S w ctx.spec)
    (hM : ValidMasks ctx.spec.masks)
    (hn_pts : ctx.n_pts = 7 + ctx.spec.masks.length)
    (hbccw_eq : ctx.bccw = buildBccw ctx.spec)
    (hm_eq : ctx.maskTrie = buildMaskTrieAux .xH ctx.spec.masks .leaf)
    {val : PIdx → Bool}
    (hval : ∀ {i j k : ℕ} (hij : i < j) (hjk : j < k) (hk : k < ctx.n_pts) {v : PIdx},
      ctx.tripleTrie.get3 (ptKey i) (ptKey j) (ptKey k) = some v →
      val v = orientSign (pointSeq S w (specWitnessEmb hM) ⟨i, by omega⟩)
                         (pointSeq S w (specWitnessEmb hM) ⟨j, by omega⟩)
                         (pointSeq S w (specWitnessEmb hM) ⟨k, by omega⟩))
    {db db' : BinTrie Clause} {justChunk : ChunkTree}
    (hins : insertIdJustTree ctx db justChunk = some db')
    (hdb : EvalTrieCNF val db) :
    EvalTrieCNF val db' := by
  unfold insertIdJustTree at hins
  cases hr : runStreamTower (stepIdJust ctx) 4 db (ByteStream.ofTree justChunk) with
  | none => rw [hr] at hins; nomatch hins
  | some pr =>
    rcases pr with ⟨done, db1, bs1⟩
    rw [hr] at hins
    cases done; · nomatch hins
    injection hins with heq; subst heq
    exact runStreamTower_preserve (stepIdJust_sound hV hM hn_pts hbccw_eq hm_eq hval) 4 hr hdb

private lemma stepMidRup_sound {val : PIdx → Bool}
    {db db' : BinTrie Clause} {bs bs' : ByteStream} {done : Bool}
    (hstep : stepMidRup db bs = some (done, db', bs'))
    (hdb : EvalTrieCNF val db) :
    EvalTrieCNF val db' := by
  unfold stepMidRup at hstep
  cases hn : bs.next with
  | none => rw [hn] at hstep; nomatch hstep
  | some pn =>
    rcases pn with ⟨b, bs1⟩
    rw [hn] at hstep
    cases b with
    | zero =>
      injection hstep with hp; rcases Prod.mk.inj hp with ⟨_, hp2⟩
      rcases Prod.mk.inj hp2 with ⟨rfl, _⟩; exact hdb
    | succ b0 =>
      cases b0 with
      | zero =>
        cases hex : execOneRupStep db bs1 with
        | none => simp only [hex] at hstep; nomatch hstep
        | some pr =>
          rcases pr with ⟨d, db1, bs2⟩
          simp only [hex] at hstep
          cases d
          · injection hstep with hp; rcases Prod.mk.inj hp with ⟨_, hp2⟩
            rcases Prod.mk.inj hp2 with ⟨rfl, _⟩
            exact (execOneRupStep_sound hex hdb).2 rfl
          · nomatch hstep
      | succ _ => nomatch hstep

private lemma execMidRupTree_sound {val : PIdx → Bool}
    {db db' : BinTrie Clause} {rupChunk : ChunkTree}
    (hex : execMidRupTree db rupChunk = some db')
    (hdb : EvalTrieCNF val db) :
    EvalTrieCNF val db' := by
  unfold execMidRupTree at hex
  cases hr : runStreamTower stepMidRup 4 db (ByteStream.ofTree rupChunk) with
  | none => rw [hr] at hex; nomatch hex
  | some pr =>
    rcases pr with ⟨done, db1, bs1⟩
    rw [hr] at hex
    cases done; · nomatch hex
    injection hex with heq; subst heq
    exact runStreamTower_preserve stepMidRup_sound 4 hr hdb

/-! ## Master Checkpointed Theorems (`init_chunked_val`, `checkMidChunk_sound`, `checkFinalChunk_sound`) -/

/-- Extracts the shared `tripleTrie` and geometric `orientSign` valuation `val : PIdx → Bool`
    once at the beginning of a multi-chunk `caseXX_unsat` proof (zero re-reduction of `varTree`!). -/
theorem init_chunked_val {P : Set (ℝ × ℝ)} {S : Fin 7 → ℝ × ℝ} {w : Finset (Fin 7) → ℝ × ℝ}
    {spec : CaseSpec} (hMasks : validMasksBool spec.masks = true)
    {varTree : ChunkTree} (hVar : checkVarTree spec varTree = true) :
    ∃ (hM : ValidMasks spec.masks) (tripleTrie : TripleTrie) (val : PIdx → Bool),
      buildTripleTrieTree (7 + spec.masks.length) varTree = some tripleTrie ∧
      (∀ {i j k : ℕ} (hij : i < j) (hjk : j < k) (hk : k < 7 + spec.masks.length) {v : PIdx},
        tripleTrie.get3 (ptKey i) (ptKey j) (ptKey k) = some v →
        val v = orientSign (pointSeq S w (specWitnessEmb hM) ⟨i, by omega⟩)
                           (pointSeq S w (specWitnessEmb hM) ⟨j, by omega⟩)
                           (pointSeq S w (specWitnessEmb hM) ⟨k, by omega⟩)) := by
  have hM : ValidMasks spec.masks := validMasks_of_bool hMasks
  unfold checkVarTree at hVar
  cases htt : buildTripleTrieTree (7 + spec.masks.length) varTree with
  | none => rw [htt] at hVar; exact Bool.noConfusion hVar
  | some tripleTrie =>
    obtain ⟨val, hval⟩ := buildTripleTrieTree_sound (by have := hM.1; omega)
      (pointSeq S w (specWitnessEmb hM)) htt
    exact ⟨hM, tripleTrie, val, rfl, hval⟩

/-- Propagates `EvalRawTree val inLive → EvalRawTree val outLive` across a verified `checkMidChunk`. -/
theorem checkMidChunk_sound {P : Set (ℝ × ℝ)} {S : Fin 7 → ℝ × ℝ} {w : Finset (Fin 7) → ℝ × ℝ}
    {spec : CaseSpec} (hV : ValidCanonicalInstance P S w spec)
    (hM : ValidMasks spec.masks)
    {varTree : ChunkTree} {tripleTrie : TripleTrie} {val : PIdx → Bool}
    (htt : buildTripleTrieTree (7 + spec.masks.length) varTree = some tripleTrie)
    (hval : ∀ {i j k : ℕ} (hij : i < j) (hjk : j < k) (hk : k < 7 + spec.masks.length) {v : PIdx},
      tripleTrie.get3 (ptKey i) (ptKey j) (ptKey k) = some v →
      val v = orientSign (pointSeq S w (specWitnessEmb hM) ⟨i, by omega⟩)
                         (pointSeq S w (specWitnessEmb hM) ⟨j, by omega⟩)
                         (pointSeq S w (specWitnessEmb hM) ⟨k, by omega⟩))
    {justChunk inLive rupChunk outLive : ChunkTree}
    (hMid : checkMidChunk spec varTree justChunk inLive rupChunk outLive = true)
    (hIn : EvalRawTree val inLive) :
    EvalRawTree val outLive := by
  unfold checkMidChunk at hMid
  rw [htt] at hMid; dsimp only at hMid
  cases h0 : insertRawTree .leaf inLive with
  | none => rw [h0] at hMid; exact Bool.noConfusion hMid
  | some db0 =>
    rw [h0] at hMid; dsimp only at hMid
    cases h1 : insertIdJustTree (mkCertCtx spec tripleTrie) db0 justChunk with
    | none => rw [h1] at hMid; exact Bool.noConfusion hMid
    | some db1 =>
      rw [h1] at hMid; dsimp only at hMid
      cases h2 : execMidRupTree db1 rupChunk with
      | none => rw [h2] at hMid; exact Bool.noConfusion hMid
      | some db2 =>
        rw [h2] at hMid; dsimp only at hMid
        have hdb0 : EvalTrieCNF val db0 := hIn db0 h0
        have hdb1 : EvalTrieCNF val db1 :=
          insertIdJustTree_sound hV hM rfl rfl rfl hval h1 hdb0
        have hdb2 : EvalTrieCNF val db2 := execMidRupTree_sound h2 hdb1
        exact verifyRawTree_sound hdb2 hMid

/-- Derives `False` from `EvalRawTree val inLive` and a verified `checkFinalChunk`. -/
theorem checkFinalChunk_sound {P : Set (ℝ × ℝ)} {S : Fin 7 → ℝ × ℝ} {w : Finset (Fin 7) → ℝ × ℝ}
    {spec : CaseSpec} (hV : ValidCanonicalInstance P S w spec)
    (hM : ValidMasks spec.masks)
    {varTree : ChunkTree} {tripleTrie : TripleTrie} {val : PIdx → Bool}
    (htt : buildTripleTrieTree (7 + spec.masks.length) varTree = some tripleTrie)
    (hval : ∀ {i j k : ℕ} (hij : i < j) (hjk : j < k) (hk : k < 7 + spec.masks.length) {v : PIdx},
      tripleTrie.get3 (ptKey i) (ptKey j) (ptKey k) = some v →
      val v = orientSign (pointSeq S w (specWitnessEmb hM) ⟨i, by omega⟩)
                         (pointSeq S w (specWitnessEmb hM) ⟨j, by omega⟩)
                         (pointSeq S w (specWitnessEmb hM) ⟨k, by omega⟩))
    {justChunk inLive rupChunk : ChunkTree}
    (hFin : checkFinalChunk spec varTree justChunk inLive rupChunk = true)
    (hIn : EvalRawTree val inLive) :
    False := by
  unfold checkFinalChunk at hFin
  rw [htt] at hFin; dsimp only at hFin
  cases h0 : insertRawTree .leaf inLive with
  | none => rw [h0] at hFin; exact Bool.noConfusion hFin
  | some db0 =>
    rw [h0] at hFin; dsimp only at hFin
    cases h1 : insertIdJustTree (mkCertCtx spec tripleTrie) db0 justChunk with
    | none => rw [h1] at hFin; exact Bool.noConfusion hFin
    | some db1 =>
      rw [h1] at hFin; dsimp only at hFin
      have hdb0 : EvalTrieCNF val db0 := hIn db0 h0
      have hdb1 : EvalTrieCNF val db1 :=
        insertIdJustTree_sound hV hM rfl rfl rfl hval h1 hdb0
      exact checkTreeRUP_sound hFin hdb1

end VCDim6

end
