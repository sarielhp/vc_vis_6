import RootTask.VCDim6.CoreClauseSoundness
import RootTask.VCDim6.ChunkedCertSoundness
import RootTask.VCDim6.MasterTableRUP

open scoped Classical
open VCDim6.FastTrieRUP ChirotopeSoundness

noncomputable section

namespace VCDim6

/-!
# Soundness of Read-Only Master-Table Sharded RUP Verification (`MasterTableSoundness`)

Proves soundness of `checkCoreShard`, `checkMidRupShard`, and `checkFinRupShard` from
`MasterTableRUP` with zero `sorry`, zero `native_decide`, and zero `Lean.trustCompiler`
(`[propext, Classical.choice, Quot.sound]` only).
-/

/-! ## 1. `natOfPIdx` & `pidxLt` Arithmetic Lemmas -/

private lemma pidx_succ_xH : PIdx.succ .xH = .xO .xH := rfl
private lemma pidx_succ_xO (p : PIdx) : PIdx.succ (.xO p) = .xI p := rfl
private lemma pidx_succ_xI (p : PIdx) : PIdx.succ (.xI p) = mkXO p.succ := rfl

lemma natOfPIdx_pos (p : PIdx) : 1 ≤ natOfPIdx p := by
  induction p with
  | xH => decide
  | xO p ih => simp only [natOfPIdx]; omega
  | xI p ih => simp only [natOfPIdx]; omega

lemma natOfPIdx_succ (p : PIdx) : natOfPIdx p.succ = natOfPIdx p + 1 := by
  induction p with
  | xH => rfl
  | xO p _ => simp only [pidx_succ_xO, natOfPIdx]
  | xI p ih => simp only [pidx_succ_xI, mkXO_eq, natOfPIdx, ih]; omega

lemma natOfPIdx_ofSmallNat (n : ℕ) : natOfPIdx (PIdx.ofSmallNat n) = n + 1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [PIdx.ofSmallNat, natOfPIdx_succ, ih]

lemma natOfPIdx_inj {p q : PIdx} (h : natOfPIdx p = natOfPIdx q) : p = q := by
  induction p generalizing q with
  | xH =>
    cases q with
    | xH => rfl
    | xO q => have := natOfPIdx_pos q; simp only [natOfPIdx] at h; omega
    | xI q => have := natOfPIdx_pos q; simp only [natOfPIdx] at h; omega
  | xO p ih =>
    cases q with
    | xH => have := natOfPIdx_pos p; simp only [natOfPIdx] at h; omega
    | xO q => simp only [natOfPIdx] at h; exact congrArg PIdx.xO (ih (by omega))
    | xI q => simp only [natOfPIdx] at h; omega
  | xI p ih =>
    cases q with
    | xH => have := natOfPIdx_pos p; simp only [natOfPIdx] at h; omega
    | xO q => simp only [natOfPIdx] at h; omega
    | xI q => simp only [natOfPIdx] at h; exact congrArg PIdx.xI (ih (by omega))

private lemma pidxCmp_xH (q : PIdx) :
    pidxCmpLtLe .xH q = (match q with | .xH => (false, true) | .xO _ => (true, true) | .xI _ => (true, true)) := rfl
private lemma pidxCmp_xO (p q : PIdx) :
    pidxCmpLtLe (.xO p) q = (match q with
      | .xH => (false, false)
      | .xO q' => pidxCmpLtLe p q'
      | .xI q' => let r := pidxCmpLtLe p q'; (r.2, r.2)) := rfl
private lemma pidxCmp_xI (p q : PIdx) :
    pidxCmpLtLe (.xI p) q = (match q with
      | .xH => (false, false)
      | .xO q' => let r := pidxCmpLtLe p q'; (r.1, r.1)
      | .xI q' => pidxCmpLtLe p q') := rfl

lemma pidxCmpLtLe_spec (p q : PIdx) :
    ((pidxCmpLtLe p q).1 = true ↔ natOfPIdx p < natOfPIdx q) ∧
    ((pidxCmpLtLe p q).2 = true ↔ natOfPIdx p ≤ natOfPIdx q) := by
  induction p generalizing q with
  | xH =>
    cases q with
    | xH => simp [pidxCmp_xH, natOfPIdx]
    | xO q => have := natOfPIdx_pos q; simp only [pidxCmp_xH, natOfPIdx, true_iff]; omega
    | xI q => have := natOfPIdx_pos q; simp only [pidxCmp_xH, natOfPIdx, true_iff]; omega
  | xO p ih =>
    cases q with
    | xH =>
      have := natOfPIdx_pos p
      simp only [pidxCmp_xO, natOfPIdx, Bool.false_eq_true, false_iff]; omega
    | xO q =>
      obtain ⟨ih1, ih2⟩ := ih q
      simp only [pidxCmp_xO, natOfPIdx, ih1, ih2]; constructor <;> omega
    | xI q =>
      obtain ⟨_, ih2⟩ := ih q
      simp only [pidxCmp_xO, natOfPIdx, ih2]; constructor <;> omega
  | xI p ih =>
    cases q with
    | xH =>
      have := natOfPIdx_pos p
      simp only [pidxCmp_xI, natOfPIdx, Bool.false_eq_true, false_iff]; omega
    | xO q =>
      obtain ⟨ih1, _⟩ := ih q
      simp only [pidxCmp_xI, natOfPIdx, ih1]; constructor <;> omega
    | xI q =>
      obtain ⟨ih1, ih2⟩ := ih q
      simp only [pidxCmp_xI, natOfPIdx, ih1, ih2]; constructor <;> omega

lemma pidxLt_iff (p q : PIdx) : pidxLt p q = true ↔ natOfPIdx p < natOfPIdx q :=
  (pidxCmpLtLe_spec p q).1

/-! ## 2. Prefix Invariant `MasterRangeSound` -/

/-- Every clause present in `master` at any key `p` with `natOfPIdx p ≤ bound0` is satisfied by `val`. -/
def MasterRangeSound (val : PIdx → Bool) (master : BinTrie Clause) (bound0 : ℕ) : Prop :=
  ∀ p : PIdx, natOfPIdx p ≤ bound0 →
    ∀ cl : Clause, master.get p = some cl → evalClause val cl = true

theorem masterRangeSound_zero (val : PIdx → Bool) (master : BinTrie Clause) :
    MasterRangeSound val master 0 := by
  intro p hp
  have := natOfPIdx_pos p
  omega

theorem masterRangeSound_xH (val : PIdx → Bool) (master : BinTrie Clause) :
    MasterRangeSound val master (natOfPIdx .xH - 1) :=
  masterRangeSound_zero val master

private lemma extend_masterRangeSound {val : PIdx → Bool} {master : BinTrie Clause}
    {n : ℕ} {cid : PIdx} {cl₀ : Clause}
    (hprev : MasterRangeSound val master n)
    (hcid : natOfPIdx cid = n + 1)
    (hlook : master.get cid = some cl₀)
    (heval : evalClause val cl₀ = true) :
    MasterRangeSound val master (n + 1) := by
  intro p hp cl hp_look
  by_cases hle : natOfPIdx p ≤ n
  · exact hprev p hle cl hp_look
  · have heq_nat : natOfPIdx p = natOfPIdx cid := by omega
    have hp_eq : p = cid := natOfPIdx_inj heq_nat
    subst hp_eq
    rw [hlook] at hp_look
    injection hp_look with hcl
    rwa [← hcl]

/-! ## 3. Generic Stream-Tower Preservation -/

private lemma chainStream2_inv {σ : Type} {P_inv : σ → Prop}
    {step : σ → ByteStream → Option (Bool × σ × ByteStream)}
    (hstep : ∀ {st st' bs bs' done}, step st bs = some (done, st', bs') → P_inv st → P_inv st') :
    ∀ (k : ℕ) {st st' : σ} {bs bs' : ByteStream} {done : Bool},
      chainStream2 step k st bs = some (done, st', bs') → P_inv st → P_inv st'
  | 0, _, _, _, _, _, h, hinv => by
    injection h with hp; rcases Prod.mk.inj hp with ⟨_, hp2⟩
    rcases Prod.mk.inj hp2 with ⟨rfl, _⟩; exact hinv
  | k + 1, st, _, bs, _, _, h, hinv => by
    unfold chainStream2 at h
    cases hex : step st bs with
    | none => simp only [hex] at h; nomatch h
    | some res =>
      rcases res with ⟨d1, st1, bs1⟩
      simp only [hex] at h
      have hinv1 := hstep hex hinv
      cases d1
      · exact chainStream2_inv hstep k h hinv1
      · injection h with hp; rcases Prod.mk.inj hp with ⟨_, hp2⟩
        rcases Prod.mk.inj hp2 with ⟨rfl, _⟩; exact hinv1

private lemma runStreamTower_inv {σ : Type} {P_inv : σ → Prop}
    {step : σ → ByteStream → Option (Bool × σ × ByteStream)}
    (hstep : ∀ {st st' bs bs' done}, step st bs = some (done, st', bs') → P_inv st → P_inv st') :
    ∀ (lvl : ℕ) {st st' : σ} {bs bs' : ByteStream} {done : Bool},
      runStreamTower step lvl st bs = some (done, st', bs') → P_inv st → P_inv st'
  | 0, _, _, _, _, _, h, hinv => by
    unfold runStreamTower at h; exact chainStream2_inv hstep 16 h hinv
  | lvl + 1, _, _, _, _, _, h, hinv => by
    unfold runStreamTower at h; exact chainStream2_inv (runStreamTower_inv hstep lvl) 16 h hinv

/-! ## 4. Soundness of `checkCoreShard` -/

private def CoreShardInv (val : PIdx → Bool) (master : BinTrie Clause) (endBound : ℕ)
    (st : PIdx × ℕ) : Prop :=
  natOfPIdx st.1 + st.2 = endBound + 1 ∧
  MasterRangeSound val master (natOfPIdx st.1 - 1)

private lemma stepCoreShard_sound {P : Set (ℝ × ℝ)} {S : Fin 7 → ℝ × ℝ} {w : Finset (Fin 7) → ℝ × ℝ}
    {ctx : CertCtx} {master : BinTrie Clause} {endBound : ℕ}
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
    {st st' : PIdx × ℕ} {bs bs' : ByteStream} {done : Bool}
    (hstep : stepCoreShard ctx master st bs = some (done, st', bs'))
    (hinv : CoreShardInv val master endBound st) :
    CoreShardInv val master endBound st' := by
  rcases st with ⟨cid, rem⟩
  unfold stepCoreShard at hstep
  cases rem with
  | zero =>
    injection hstep with hp; rcases Prod.mk.inj hp with ⟨_, hp2⟩
    rcases Prod.mk.inj hp2 with ⟨rfl, _⟩; exact hinv
  | succ r =>
    cases hd : decodeOneJust ctx bs with
    | none => simp only [hd] at hstep; nomatch hstep
    | some pd =>
      rcases pd with ⟨clOpt, bs1⟩
      simp only [hd] at hstep
      cases clOpt with
      | none => nomatch hstep
      | some cl =>
        cases hl : master.get cid with
        | none => simp only [hl] at hstep; nomatch hstep
        | some clM =>
          simp only [hl] at hstep
          cases heq : clauseEq clM cl with
          | false => simp only [heq] at hstep; nomatch hstep
          | true =>
            simp only [heq] at hstep
            have hcl_eq : clM = cl := (clauseEq_iff clM cl).mp heq
            have heval_cl : evalClause val cl = true :=
              decodeOneJust_sound hV hM hn_pts hbccw_eq hm_eq hval hd
            have heval_M : evalClause val clM = true := hcl_eq ▸ heval_cl
            have hcid_pos := natOfPIdx_pos cid
            have hst' : st' = (cid.succ, r) := by
              cases hs : strictPIdx cid.succ <;> rw [hs] at hstep <;>
                injection hstep with hp <;> rcases Prod.mk.inj hp with ⟨_, hp2⟩ <;>
                rcases Prod.mk.inj hp2 with ⟨hst_eq, _⟩ <;>
                rw [← hst_eq, ← hs, strictPIdx_eq]
            rw [hst']
            have hinv2 : MasterRangeSound val master (natOfPIdx cid - 1) := hinv.2
            refine ⟨?_, ?_⟩
            · dsimp only
              rw [natOfPIdx_succ]
              have := hinv.1; dsimp only at this; omega
            · dsimp only
              rw [natOfPIdx_succ, Nat.add_sub_cancel, ← Nat.sub_add_cancel hcid_pos]
              exact extend_masterRangeSound hinv2 (Nat.sub_add_cancel hcid_pos).symm hl heval_M

theorem checkCoreShard_sound {P : Set (ℝ × ℝ)} {S : Fin 7 → ℝ × ℝ} {w : Finset (Fin 7) → ℝ × ℝ}
    {spec : CaseSpec} (hV : ValidCanonicalInstance P S w spec)
    (hM : ValidMasks spec.masks)
    {varTree : ChunkTree} {tripleTrie : TripleTrie} {val : PIdx → Bool}
    (htt : buildTripleTrieTree (7 + spec.masks.length) varTree = some tripleTrie)
    (hval : ∀ {i j k : ℕ} (hij : i < j) (hjk : j < k) (hk : k < 7 + spec.masks.length) {v : PIdx},
      tripleTrie.get3 (ptKey i) (ptKey j) (ptKey k) = some v →
      val v = orientSign (pointSeq S w (specWitnessEmb hM) ⟨i, by omega⟩)
                         (pointSeq S w (specWitnessEmb hM) ⟨j, by omega⟩)
                         (pointSeq S w (specWitnessEmb hM) ⟨k, by omega⟩))
    {master : BinTrie Clause} {startCid endCid : PIdx} {count : ℕ} {justShard : ChunkTree}
    (hCore : checkCoreShard spec varTree master startCid endCid count justShard = true)
    (hIn : MasterRangeSound val master (natOfPIdx startCid - 1)) :
    MasterRangeSound val master (natOfPIdx endCid - 1) := by
  unfold checkCoreShard at hCore
  rw [htt] at hCore; dsimp only at hCore
  change (match runStreamTower (stepCoreShard (mkCertCtx spec tripleTrie) master) 3
      (startCid, count) (ByteStream.ofTree justShard) with
    | some (true, (cidOut, 0), _) => pidxEq cidOut endCid | _ => false) = true at hCore
  cases hr : runStreamTower (stepCoreShard (mkCertCtx spec tripleTrie) master) 3
      (startCid, count) (ByteStream.ofTree justShard) with
  | none => rw [hr] at hCore; exact Bool.noConfusion hCore
  | some pr =>
    rcases pr with ⟨done, ⟨cidOut, remOut⟩, bsOut⟩
    rw [hr] at hCore
    cases done; · exact Bool.noConfusion hCore
    cases remOut with
    | succ _ => exact Bool.noConfusion hCore
    | zero =>
      have hc_eq : cidOut = endCid := (pidxEq_iff cidOut endCid).mp hCore
      subst hc_eq
      have hcid_pos := natOfPIdx_pos startCid
      have hinit : CoreShardInv val master ((natOfPIdx startCid - 1) + count) (startCid, count) := by
        exact ⟨by dsimp; omega, hIn⟩
      have hout := runStreamTower_inv
        (stepCoreShard_sound hV hM rfl rfl rfl hval) 3 hr hinit
      exact hout.2

/-! ## 5. Soundness of `checkMidRupList` and `checkFinRupList` -/

private lemma allHintsLt_cons (cid hid : PIdx) (rest : List PIdx) :
    allHintsLt cid (hid :: rest) =
      (match pidxLt hid cid with | false => false | true => allHintsLt cid rest) := rfl

private lemma rupPropagate_range_false {val : PIdx → Bool} {master : BinTrie Clause} {cid : PIdx}
    (hM : MasterRangeSound val master (natOfPIdx cid - 1)) :
    ∀ (hints : List PIdx) (fmap : BinTrie Bool),
      allHintsLt cid hints = true →
      FMapSound val fmap →
      rupPropagate master fmap hints = true →
      False
  | [], _, _, _, hrup => Bool.noConfusion hrup
  | hid :: rest, fmap, hlt, hs, hrup => by
    rw [allHintsLt_cons] at hlt
    cases hp : pidxLt hid cid with
    | false => rw [hp] at hlt; exact Bool.noConfusion hlt
    | true =>
      rw [hp] at hlt
      have hlt_nat : natOfPIdx hid < natOfPIdx cid := (pidxLt_iff hid cid).mp hp
      rw [rupPropagate_cons] at hrup
      cases hget : master.get hid with
      | none => simp only [hget] at hrup; exact Bool.noConfusion hrup
      | some hcl =>
        simp only [hget] at hrup
        have hcl_true : evalClause val hcl = true := hM hid (by omega) hcl hget
        cases hscan : scanClause fmap none hcl with
        | none => simp only [hscan] at hrup; exact Bool.noConfusion hrup
        | some res =>
          simp only [hscan] at hrup
          have hspec := scanClause_spec fmap none res hcl hscan
          obtain ⟨x, hx_mem, hx_true⟩ := List.any_eq_true.mp hcl_true
          cases res with
          | none =>
            have hxf := evalLit_false_of_isFalsified hs (hspec.2 x hx_mem)
            rw [hxf] at hx_true; exact Bool.noConfusion hx_true
          | some u =>
            have hu_true : evalLit val u = true := by
              rcases hspec.2 x hx_mem with hxf | rfl
              · rw [evalLit_false_of_isFalsified hs hxf] at hx_true
                exact False.elim (Bool.noConfusion hx_true)
              · exact hx_true
            have hnu_false : evalLit val (!u.1, u.2) = false := by
              rw [evalLit_neg, hu_true]; rfl
            cases hadd : addFalseLit fmap (!u.1, u.2) with
            | none => exact addFalseLit_none_false hs hnu_false hadd
            | some fmap' =>
              simp only [hadd] at hrup
              exact rupPropagate_range_false hM rest fmap' hlt
                (addFalseLit_some_sound hs hnu_false hadd) hrup

private lemma checkRupList_sound {val : PIdx → Bool} {master : BinTrie Clause} :
    ∀ (steps : List (List PIdx)) {cid cidOut : PIdx},
      checkRupList master steps cid = some cidOut →
      MasterRangeSound val master (natOfPIdx cid - 1) →
      MasterRangeSound val master (natOfPIdx cidOut - 1)
  | [], cid, cidOut, h, hM => by
    change some cid = some cidOut at h
    injection h with heq; subst heq; exact hM
  | hints :: rest, cid, cidOut, h, hM => by
    change (match allHintsLt cid hints with
      | false => none
      | true =>
        match master.get cid with
        | none => none
        | some cl =>
          let ok := match initFalseLits .leaf cl with
            | none => true | some fmap => rupPropagate master fmap hints
          match ok with
          | false => none
          | true =>
            match strictPIdx cid.succ with
            | .xH => checkRupList master rest .xH
            | .xO p => checkRupList master rest (.xO p)
            | .xI p => checkRupList master rest (.xI p)) = some cidOut at h
    cases hlt : allHintsLt cid hints with
    | false => rw [hlt] at h; nomatch h
    | true =>
      rw [hlt] at h
      cases hget : master.get cid with
      | none => rw [hget] at h; nomatch h
      | some cl =>
        rw [hget] at h
        let ok := match initFalseLits .leaf cl with
          | none => true | some fmap => rupPropagate master fmap hints
        cases hok : ok with
        | false =>
          change (match ok with | false => none | true => _) = _ at h
          rw [hok] at h; nomatch h
        | true =>
          change (match ok with | false => none | true => _) = _ at h
          rw [hok] at h
          have hcl_true : evalClause val cl = true := by
            cases hcl : evalClause val cl
            · exfalso
              have hleaf : FMapSound val .leaf := fun p _ hg => by
                rw [BinTrie.get_leaf] at hg; nomatch hg
              obtain ⟨fmap, hinit, hfs⟩ := initFalseLits_spec .leaf cl hleaf hcl
              change (match initFalseLits .leaf cl with
                | none => true | some fmap => rupPropagate master fmap hints) = true at hok
              rw [hinit] at hok
              exact rupPropagate_range_false hM hints fmap hlt hfs hok
            · rfl
          have hrec : checkRupList master rest cid.succ = some cidOut := by
            cases hs : strictPIdx cid.succ <;> rw [hs] at h <;>
              rwa [← strictPIdx_eq cid.succ, hs]
          have hcid_pos := natOfPIdx_pos cid
          have hM1 : MasterRangeSound val master (natOfPIdx cid.succ - 1) := by
            rw [natOfPIdx_succ, Nat.add_sub_cancel, ← Nat.sub_add_cancel hcid_pos]
            exact extend_masterRangeSound hM (Nat.sub_add_cancel hcid_pos).symm hget hcl_true
          exact checkRupList_sound rest hrec hM1

theorem checkMidRupList_sound {val : PIdx → Bool} {master : BinTrie Clause}
    {startCid endCid : PIdx} {steps : List (List PIdx)}
    (hMid : checkMidRupList master startCid endCid steps = true)
    (hIn : MasterRangeSound val master (natOfPIdx startCid - 1)) :
    MasterRangeSound val master (natOfPIdx endCid - 1) := by
  unfold checkMidRupList at hMid
  cases hr : checkRupList master steps startCid with
  | none => rw [hr] at hMid; exact Bool.noConfusion hMid
  | some cidOut =>
    rw [hr] at hMid
    have hc_eq : cidOut = endCid := (pidxEq_iff cidOut endCid).mp hMid
    subst hc_eq
    exact checkRupList_sound steps hr hIn

theorem checkFinRupList_sound {val : PIdx → Bool} {master : BinTrie Clause}
    {startCid : PIdx} {midSteps : List (List PIdx)} {finHints : List PIdx}
    (hFin : checkFinRupList master startCid midSteps finHints = true)
    (hIn : MasterRangeSound val master (natOfPIdx startCid - 1)) :
    False := by
  unfold checkFinRupList at hFin
  cases hr : checkRupList master midSteps startCid with
  | none => rw [hr] at hFin; exact Bool.noConfusion hFin
  | some cidFin =>
    rw [hr] at hFin; dsimp only at hFin
    cases hlt : allHintsLt cidFin finHints with
    | false => rw [hlt] at hFin; exact Bool.noConfusion hFin
    | true =>
      rw [hlt] at hFin
      have hM_fin := checkRupList_sound midSteps hr hIn
      have hleaf : FMapSound val .leaf := fun p _ hg => by
        rw [BinTrie.get_leaf] at hg; nomatch hg
      exact rupPropagate_range_false hM_fin finHints .leaf hlt hleaf hFin

theorem verifiedMidRup_sound {val : PIdx → Bool} {master : BinTrie Clause}
    {startCid endCid : PIdx}
    (hMid : VerifiedMidRup master startCid endCid)
    (hIn : MasterRangeSound val master (natOfPIdx startCid - 1)) :
    MasterRangeSound val master (natOfPIdx endCid - 1) := by
  induction hMid with
  | step hs => exact checkMidRupList_sound hs hIn
  | trans _ _ ih1 ih2 => exact ih2 (ih1 hIn)

theorem verifiedFinRup_sound {val : PIdx → Bool} {master : BinTrie Clause}
    {startCid : PIdx}
    (hFin : VerifiedFinRup master startCid)
    (hIn : MasterRangeSound val master (natOfPIdx startCid - 1)) :
    False := by
  induction hFin with
  | fin hf => exact checkFinRupList_sound hf hIn
  | cons hm _ ih => exact ih (verifiedMidRup_sound hm hIn)

end VCDim6

end
