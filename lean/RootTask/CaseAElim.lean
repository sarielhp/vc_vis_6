import RootTask.CaseASweep

open Finset
open Classical
set_option maxRecDepth 4000

noncomputable section

namespace CaseA

/-- Left boundary key encoding asymptotic dominance of `F_i` near `t = 0⁺`. -/
def leftKey (P : DualConfig) (i : Fin 5) : ℝ :=
  if 0 < supportF P i 0 then -supportF P i 0 else posLeft P i

/-- Right boundary key encoding asymptotic dominance of `F_i` near `t = 3⁻`. -/
def rightKey (P : DualConfig) (i : Fin 5) : ℝ :=
  if 0 < supportF P i 3 then 3 + supportF P i 3 else posRight P i

/-- Permutation `σ` sorting `rightKey P` in strictly increasing order. -/
def rightPerm (P : DualConfig) : Equiv.Perm (Fin 5) :=
  if h : ∃ σ : Equiv.Perm (Fin 5), StrictMono (fun r : Fin 5 => rightKey P (σ r))
  then Classical.choose h
  else Equiv.refl (Fin 5)

/-- Inversion count `inv(σ) = |{(r, s) : r < s ∧ σ(r) > σ(s)}|` of `σ ∈ S_5`. -/
def permInversions (σ : Equiv.Perm (Fin 5)) : ℕ :=
  (((Finset.univ : Finset (Fin 5 × Fin 5)).filter
    fun p => p.1 < p.2 ∧ σ p.2 < σ p.1)).card

/-- Edge set `E(G_3^+)` of `3`-crossing pairs `{(i, j) : i < j ∧ |Z_{ij}^+| = 3}`. -/
def threeCrossGraph (P : DualConfig) : Finset (Fin 5 × Fin 5) :=
  (Finset.univ : Finset (Fin 5 × Fin 5)).filter
    fun p => p.1 < p.2 ∧ (posPairTies P p.1 p.2).card = 3

/-- Witness-nudge-free clipped cut potential `Φ_M^+(t)` counting inversions across `(M, Mᶜ)`. -/
def clippedCutPotential (P : DualConfig) (M : Finset (Fin 5)) (t : ℝ) : ℕ :=
  ((M ×ˢ (Finset.univ \ M)).filter
    fun p => clippedG P p.2 t ≤ clippedG P p.1 t).card

private lemma supportF_swap_eq (P : DualConfig) (i : Fin 5) (t : ℝ) :
    supportF P.swap i t = supportF P i (3 - t) := by
  unfold supportF DualConfig.swap
  dsimp
  have hg : gamma t = swap2 (gamma (3 - t)) := by
    have := gamma_swap_symm (3 - t)
    have h3 : 3 - (3 - t) = t := by ring
    rw [h3] at this
    exact this
  conv_lhs => rw [hg, dot2_swap2, dot2_swap2]
  exact max_comm _ _

private lemma supportF_continuous (P : DualConfig) (i : Fin 5) :
    Continuous (supportF P i) := by
  unfold supportF dot2
  exact Continuous.max
    ((continuous_const.mul (gamma_continuous.fst)).add (continuous_const.mul (gamma_continuous.snd)))
    ((continuous_const.mul (gamma_continuous.fst)).add (continuous_const.mul (gamma_continuous.snd)))

private lemma supportF_posLeft_zero (P : DualConfig) (hgp : IsGenPos P) (i : Fin 5)
    (hnonpos : ¬ 0 < supportF P i 0) :
    0 < posLeft P i ∧ supportF P i (posLeft P i) = 0 := by
  have hpi := posInterval_eq_Ioo P hgp i
  have hap := (supportF_branch_switch P hgp).2 i
  have h0_mem : (0 : ℝ) ∈ ({0, 1, 2, 3} : Finset ℝ) := by simp
  have hp1_nz := ((ray_ties_zeros_disjoint P hgp).2.1 0 h0_mem ⟨2 * i.val, by omega⟩ ⟨2 * i.val, by omega⟩).1
  have hp2_nz := ((ray_ties_zeros_disjoint P hgp).2.1 0 h0_mem ⟨2 * i.val + 1, by omega⟩ ⟨2 * i.val + 1, by omega⟩).1
  rw [P.vec_even i] at hp1_nz
  rw [P.vec_odd i] at hp2_nz
  have hneg0 : supportF P i 0 < 0 := by
    have hle : supportF P i 0 ≤ 0 := not_lt.mp hnonpos
    unfold supportF at hle ⊢
    exact max_lt (lt_of_le_of_ne (le_trans (le_max_left _ _) hle) hp1_nz)
                 (lt_of_le_of_ne (le_trans (le_max_right _ _) hle) hp2_nz)
  have hcont := supportF_continuous P i
  have hpos_left_pos : 0 < posLeft P i := by
    rcases eq_or_lt_of_le hpi.1 with heq | hgt
    · exfalso
      have hopen : IsOpen {t : ℝ | supportF P i t < 0} := isOpen_lt hcont continuous_const
      obtain ⟨δ, hδ, hsub⟩ := Metric.isOpen_iff.mp hopen 0 hneg0
      let t₁ : ℝ := min (δ / 2) (apexRay P i / 2)
      have ht1_pos : 0 < t₁ := lt_min (by linarith) (by linarith [hap.1])
      have ht1_lt_ap : t₁ < apexRay P i := lt_of_le_of_lt (min_le_right _ _) (by linarith [hap.1])
      have ht1_in_pos : 0 < supportF P i t₁ :=
        ((hpi.2.2.2.2 t₁).mpr ⟨by linarith [heq], lt_trans ht1_lt_ap hpi.2.2.1⟩).2.2
      have ht1_in_ball : t₁ ∈ Metric.ball (0 : ℝ) δ := by
        rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos ht1_pos]
        exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
      linarith [Set.mem_setOf.mp (hsub ht1_in_ball)]
    · exact hgt
  have hval0 : supportF P i (posLeft P i) = 0 := by
    rcases lt_trichotomy (supportF P i (posLeft P i)) 0 with hlt | heq | hgt
    · exfalso
      have hopen : IsOpen {t : ℝ | supportF P i t < 0} := isOpen_lt hcont continuous_const
      obtain ⟨δ, hδ, hsub⟩ := Metric.isOpen_iff.mp hopen (posLeft P i) hlt
      let t₁ : ℝ := min (posLeft P i + δ / 2) ((posLeft P i + apexRay P i) / 2)
      have ht1_gt : posLeft P i < t₁ := lt_min (by linarith) (by linarith [hpi.2.1])
      have ht1_lt : t₁ < posRight P i :=
        lt_trans (lt_of_le_of_lt (min_le_right _ _) (by linarith [hpi.2.1])) hpi.2.2.1
      have ht1_pos_f : 0 < supportF P i t₁ := ((hpi.2.2.2.2 t₁).mpr ⟨ht1_gt, ht1_lt⟩).2.2
      have ht1_ball : t₁ ∈ Metric.ball (posLeft P i) δ := by
        rw [Metric.mem_ball, Real.dist_eq, abs_of_pos (by linarith)]
        have : t₁ ≤ posLeft P i + δ / 2 := min_le_left _ _
        linarith
      linarith [Set.mem_setOf.mp (hsub ht1_ball)]
    · exact heq
    · exfalso
      have ht_lt3 : posLeft P i < 3 := lt_of_lt_of_le (lt_trans hpi.2.1 hpi.2.2.1) hpi.2.2.2.1
      have hmem := (hpi.2.2.2.2 (posLeft P i)).mp ⟨hpos_left_pos, ht_lt3, hgt⟩
      linarith [hmem.1]
  exact ⟨hpos_left_pos, hval0⟩

/-- Strict injectivity of `leftKey P` under general position. -/
theorem leftKey_injective (P : DualConfig) (hgp : IsGenPos P) :
    Function.Injective (leftKey P) := by
  intro i j hij
  by_contra hne
  unfold leftKey at hij
  have hpi := posInterval_eq_Ioo P hgp i
  have hpj := posInterval_eq_Ioo P hgp j
  have hrd := ray_ties_zeros_disjoint P hgp
  have hvc_even : ∀ k : Fin 5, vecColor ⟨2 * k.val, by omega⟩ = k := by
    intro k; ext; dsimp [vecColor]; omega
  have hvc_odd : ∀ k : Fin 5, vecColor ⟨2 * k.val + 1, by omega⟩ = k := by
    intro k; ext; dsimp [vecColor]; omega
  by_cases hi : 0 < supportF P i 0 <;> by_cases hj : 0 < supportF P j 0 <;>
    simp only [hi, hj, ↓reduceIte] at hij
  · have heq : supportF P i 0 = supportF P j 0 := by linarith
    obtain ⟨s₁, hs₁⟩ : ∃ a : Fin 10, vecColor a = i ∧ dot2 (P.vec a) (gamma 0) = supportF P i 0 := by
      unfold supportF
      rcases max_choice (dot2 (P.p1 i) (gamma 0)) (dot2 (P.p2 i) (gamma 0)) with h | h
      · exact ⟨⟨2 * i.val, by omega⟩, hvc_even i, by rw [P.vec_even i, h]⟩
      · exact ⟨⟨2 * i.val + 1, by omega⟩, hvc_odd i, by rw [P.vec_odd i, h]⟩
    obtain ⟨s₂, hs₂⟩ : ∃ b : Fin 10, vecColor b = j ∧ dot2 (P.vec b) (gamma 0) = supportF P j 0 := by
      unfold supportF
      rcases max_choice (dot2 (P.p1 j) (gamma 0)) (dot2 (P.p2 j) (gamma 0)) with h | h
      · exact ⟨⟨2 * j.val, by omega⟩, hvc_even j, by rw [P.vec_even j, h]⟩
      · exact ⟨⟨2 * j.val + 1, by omega⟩, hvc_odd j, by rw [P.vec_odd j, h]⟩
    have hs_ne : s₁ ≠ s₂ := fun h => hne (by rw [← hs₁.1, ← hs₂.1, h])
    exact (hrd.2.1 0 (by simp) s₁ s₂).2 hs_ne (by linarith [hs₁.2, hs₂.2])
  · linarith [hpi.1, hpj.1]
  · linarith [hpi.1, hpj.1]
  · obtain ⟨hpos_i, hz_i⟩ := supportF_posLeft_zero P hgp i hi
    obtain ⟨_, hz_j⟩ := supportF_posLeft_zero P hgp j hj
    rw [hij] at hz_i hpos_i
    have ht_lt3 : posLeft P j < 3 := lt_of_lt_of_le (lt_trans hpj.2.1 hpj.2.2.1) hpj.2.2.2.1
    obtain ⟨s₁, hs₁⟩ : ∃ a : Fin 10, vecColor a = i ∧ dot2 (P.vec a) (gamma (posLeft P j)) = 0 := by
      unfold supportF at hz_i
      rcases max_choice (dot2 (P.p1 i) (gamma (posLeft P j))) (dot2 (P.p2 i) (gamma (posLeft P j))) with h | h
      · exact ⟨⟨2 * i.val, by omega⟩, hvc_even i, by rw [P.vec_even i]; linarith⟩
      · exact ⟨⟨2 * i.val + 1, by omega⟩, hvc_odd i, by rw [P.vec_odd i]; linarith⟩
    obtain ⟨s₂, hs₂⟩ : ∃ b : Fin 10, vecColor b = j ∧ dot2 (P.vec b) (gamma (posLeft P j)) = 0 := by
      unfold supportF at hz_j
      rcases max_choice (dot2 (P.p1 j) (gamma (posLeft P j))) (dot2 (P.p2 j) (gamma (posLeft P j))) with h | h
      · exact ⟨⟨2 * j.val, by omega⟩, hvc_even j, by rw [P.vec_even j]; linarith⟩
      · exact ⟨⟨2 * j.val + 1, by omega⟩, hvc_odd j, by rw [P.vec_odd j]; linarith⟩
    have hs_ne : s₁ ≠ s₂ := fun h => hne (by rw [← hs₁.1, ← hs₂.1, h])
    exact hrd.2.2.1 (posLeft P j) hpos_i ht_lt3 s₁ s₂ s₁ hs_ne ⟨by linarith [hs₁.2, hs₂.2], hs₁.2⟩

private lemma ioo_eq_endpoints {a b c d : ℝ} (hab : a < b) (hcd : c < d)
    (hiff : ∀ t : ℝ, (a < t ∧ t < b) ↔ (c < t ∧ t < d)) : a = c ∧ b = d := by
  have hac : a = c := by
    rcases lt_trichotomy a c with hlt | heq | hgt
    · exfalso
      have hm_lt : a < min b c := lt_min hab hlt
      have hmin_b : min b c ≤ b := min_le_left b c
      have hmin_c : min b c ≤ c := min_le_right b c
      have hm_cd := (hiff ((a + min b c) / 2)).mp ⟨by linarith, by linarith⟩
      linarith [hm_cd.1]
    · exact heq
    · exfalso
      have hm_lt : c < min d a := lt_min hcd hgt
      have hmin_d : min d a ≤ d := min_le_left d a
      have hmin_a : min d a ≤ a := min_le_right d a
      have hm_ab := (hiff ((c + min d a) / 2)).mpr ⟨by linarith, by linarith⟩
      linarith [hm_ab.1]
  have hbd : b = d := by
    rcases lt_trichotomy b d with hlt | heq | hgt
    · exfalso
      have hm_gt : max c b < d := max_lt hcd hlt
      have hmax_c : c ≤ max c b := le_max_left c b
      have hmax_b : b ≤ max c b := le_max_right c b
      have hm_ab := (hiff ((max c b + d) / 2)).mpr ⟨by linarith, by linarith⟩
      linarith [hm_ab.2]
    · exact heq
    · exfalso
      have hm_gt : max a d < b := max_lt hab hgt
      have hmax_a : a ≤ max a d := le_max_left a d
      have hmax_d : d ≤ max a d := le_max_right a d
      have hm_cd := (hiff ((max a d + b) / 2)).mp ⟨by linarith, by linarith⟩
      linarith [hm_cd.2]
  exact ⟨hac, hbd⟩

/-- Exact swap duality `leftKey P.swap i = 3 - rightKey P i` and `rightKey P.swap i = 3 - leftKey P i`. -/
theorem boundaryKey_swap (P : DualConfig) (hgp : IsGenPos P) (i : Fin 5) :
    leftKey P.swap i = 3 - rightKey P i ∧
    rightKey P.swap i = 3 - leftKey P i := by
  have hQi := posInterval_eq_Ioo P hgp i
  have hQsw := posInterval_eq_Ioo P.swap ((P.swap_spec).2.1.mpr hgp) i
  have hiff : ∀ t : ℝ, (posLeft P.swap i < t ∧ t < posRight P.swap i) ↔
      (3 - posRight P i < t ∧ t < 3 - posLeft P i) := by
    intro t
    rw [← hQsw.2.2.2.2 t, supportF_swap_eq]
    have h3t := hQi.2.2.2.2 (3 - t)
    constructor
    · intro ⟨ht0, ht3, hf⟩
      have hm := h3t.mp ⟨by linarith, by linarith, hf⟩
      exact ⟨by linarith [hm.2], by linarith [hm.1]⟩
    · intro ⟨hlo, hhi⟩
      have hm := h3t.mpr ⟨by linarith, by linarith⟩
      exact ⟨by linarith [hm.2.1], by linarith [hm.1], hm.2.2⟩
  obtain ⟨heqL, heqR⟩ := ioo_eq_endpoints
    (lt_trans hQsw.2.1 hQsw.2.2.1) (by linarith [hQi.2.1, hQi.2.2.1]) hiff
  constructor
  · unfold leftKey rightKey
    rw [supportF_swap_eq P i 0, show (3 : ℝ) - 0 = 3 by ring]
    split_ifs <;> linarith
  · unfold rightKey leftKey
    rw [supportF_swap_eq P i 3, show (3 : ℝ) - 3 = 0 by ring]
    split_ifs <;> linarith

/-- Strict injectivity of `rightKey P` under general position. -/
theorem rightKey_injective (P : DualConfig) (hgp : IsGenPos P) :
    Function.Injective (rightKey P) := by
  intro i j hij
  have hgp_sw : IsGenPos P.swap := (P.swap_spec).2.1.mpr hgp
  have h1 := (boundaryKey_swap P hgp i).1
  have h2 := (boundaryKey_swap P hgp j).1
  have hsw_eq : leftKey P.swap i = leftKey P.swap j := by linarith
  have hswap_inj := leftKey_injective P.swap hgp_sw hsw_eq
  exact hswap_inj

/-- Color relabeling `i ↦ τ i` of a `DualConfig`. -/
def DualConfig.relabel (P : DualConfig) (τ : Equiv.Perm (Fin 5)) : DualConfig where
  p1 := fun i => P.p1 (τ i)
  p2 := fun i => P.p2 (τ i)
  h_det := fun i => P.h_det (τ i)
  h_apex := fun i => P.h_apex (τ i)

private def permLift10 (τ : Equiv.Perm (Fin 5)) : Equiv.Perm (Fin 10) where
  toFun a := ⟨2 * (τ ⟨a.val / 2, by omega⟩).val + a.val % 2, by omega⟩
  invFun a := ⟨2 * (τ.symm ⟨a.val / 2, by omega⟩).val + a.val % 2, by omega⟩
  left_inv a := by
    ext; dsimp
    have h1 : (2 * (τ ⟨a.val / 2, by omega⟩).val + a.val % 2) / 2 =
        (τ ⟨a.val / 2, by omega⟩).val := by omega
    have hfin : (⟨(2 * (τ ⟨a.val / 2, by omega⟩).val + a.val % 2) / 2, by omega⟩ : Fin 5) =
        τ ⟨a.val / 2, by omega⟩ := Fin.ext h1
    rw [hfin, Equiv.symm_apply_apply]
    dsimp; omega
  right_inv a := by
    ext; dsimp
    have h1 : (2 * (τ.symm ⟨a.val / 2, by omega⟩).val + a.val % 2) / 2 =
        (τ.symm ⟨a.val / 2, by omega⟩).val := by omega
    have hfin : (⟨(2 * (τ.symm ⟨a.val / 2, by omega⟩).val + a.val % 2) / 2, by omega⟩ : Fin 5) =
        τ.symm ⟨a.val / 2, by omega⟩ := Fin.ext h1
    rw [hfin, Equiv.apply_symm_apply]
    dsimp; omega

private lemma relabel_vec (P : DualConfig) (τ : Equiv.Perm (Fin 5)) (a : Fin 10) :
    (P.relabel τ).vec a = P.vec (permLift10 τ a) := by
  unfold DualConfig.vec DualConfig.relabel permLift10
  dsimp
  have hmod : (2 * (τ ⟨a.val / 2, by omega⟩).val + a.val % 2) % 2 = a.val % 2 := by omega
  have hdiv : (2 * (τ ⟨a.val / 2, by omega⟩).val + a.val % 2) / 2 =
      (τ ⟨a.val / 2, by omega⟩).val := by omega
  simp only [hmod]
  split_ifs
  · congr 1; exact Fin.ext hdiv.symm
  · congr 1; exact Fin.ext hdiv.symm

private lemma vecColor_permLift10 (τ : Equiv.Perm (Fin 5)) (a : Fin 10) :
    vecColor (permLift10 τ a) = τ (vecColor a) := by
  ext; dsimp [vecColor, permLift10]; omega

private lemma isGenPos_relabel (P : DualConfig) (τ : Equiv.Perm (Fin 5)) (hgp : IsGenPos P) :
    IsGenPos (P.relabel τ) := by
  let e := permLift10 τ
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro a; rw [relabel_vec]; exact hgp.1 (e a)
  · intro a b hab; rw [relabel_vec, relabel_vec]
    exact hgp.2.1 (e a) (e b) (e.injective.ne hab)
  · intro a b hab; rw [relabel_vec, relabel_vec]
    exact hgp.2.2.1 (e a) (e b) (e.injective.ne hab)
  · intro a b c hab; rw [relabel_vec, relabel_vec, relabel_vec]
    exact hgp.2.2.2.1 (e a) (e b) (e c) (e.injective.ne hab)
  · intro a b c d hab hcd hpair
    rw [relabel_vec, relabel_vec, relabel_vec, relabel_vec]
    have hea : e a ≠ e b := e.injective.ne (ne_of_lt hab)
    have hec : e c ≠ e d := e.injective.ne (ne_of_lt hcd)
    rcases lt_or_gt_of_ne hea with h1 | h1 <;> rcases lt_or_gt_of_ne hec with h2 | h2
    · exact hgp.2.2.2.2 (e a) (e b) (e c) (e d) h1 h2 fun hp =>
        hpair (Prod.ext (e.injective (congrArg Prod.fst hp)) (e.injective (congrArg Prod.snd hp)))
    · have hneg : det2 (P.vec (e a) - P.vec (e b)) (P.vec (e c) - P.vec (e d)) =
          -det2 (P.vec (e a) - P.vec (e b)) (P.vec (e d) - P.vec (e c)) := by
        simp only [det2, Prod.fst_sub, Prod.snd_sub]; ring
      rw [hneg, neg_ne_zero]
      exact hgp.2.2.2.2 (e a) (e b) (e d) (e c) h1 h2 fun hp => by
        have ha : a = d := e.injective (congrArg Prod.fst hp)
        have hb : b = c := e.injective (congrArg Prod.snd hp)
        subst ha hb; exact lt_asymm hab hcd
    · have hneg : det2 (P.vec (e a) - P.vec (e b)) (P.vec (e c) - P.vec (e d)) =
          -det2 (P.vec (e b) - P.vec (e a)) (P.vec (e c) - P.vec (e d)) := by
        simp only [det2, Prod.fst_sub, Prod.snd_sub]; ring
      rw [hneg, neg_ne_zero]
      exact hgp.2.2.2.2 (e b) (e a) (e c) (e d) h1 h2 fun hp => by
        have hb : b = c := e.injective (congrArg Prod.fst hp)
        have ha : a = d := e.injective (congrArg Prod.snd hp)
        subst hb ha; exact lt_asymm hab hcd
    · have heq : det2 (P.vec (e a) - P.vec (e b)) (P.vec (e c) - P.vec (e d)) =
          det2 (P.vec (e b) - P.vec (e a)) (P.vec (e d) - P.vec (e c)) := by
        simp only [det2, Prod.fst_sub, Prod.snd_sub]; ring
      rw [heq]
      exact hgp.2.2.2.2 (e b) (e a) (e d) (e c) h1 h2 fun hp =>
        hpair (Prod.ext (e.injective (congrArg Prod.snd hp)) (e.injective (congrArg Prod.fst hp)))

private lemma supportF_relabel (P : DualConfig) (τ : Equiv.Perm (Fin 5)) (i : Fin 5) (t : ℝ) :
    supportF (P.relabel τ) i t = supportF P (τ i) t := rfl

private lemma topEnv_relabel (P : DualConfig) (τ : Equiv.Perm (Fin 5)) (t : ℝ) :
    topEnv (P.relabel τ) t = topEnv P t := by
  unfold topEnv
  refine le_antisymm (Finset.sup'_le _ _ fun i _ => ?_) (Finset.sup'_le _ _ fun i _ => ?_)
  · rw [supportF_relabel]
    exact Finset.le_sup' (fun j : Fin 5 => supportF P j t) (Finset.mem_univ (τ i))
  · have hi : supportF P i t = supportF (P.relabel τ) (τ.symm i) t := by
      rw [supportF_relabel, Equiv.apply_symm_apply]
    rw [hi]
    exact Finset.le_sup' (fun j : Fin 5 => supportF (P.relabel τ) j t) (Finset.mem_univ (τ.symm i))

private lemma shat_relabel (P : DualConfig) (τ : Equiv.Perm (Fin 5))
    (h_shat : ∀ m : Fin 5 → Bool, ∃ z : ℝ × ℝ, InOmega z ∧ RealizesDualMask P m z) :
    ∀ m : Fin 5 → Bool, ∃ z : ℝ × ℝ, InOmega z ∧ RealizesDualMask (P.relabel τ) m z := by
  intro m
  obtain ⟨z, hz, hm⟩ := h_shat (fun j => m (τ.symm j))
  refine ⟨z, hz, fun i => ?_⟩
  have hmi := hm (τ i)
  simp only [Equiv.symm_apply_apply] at hmi
  exact hmi

private lemma leftKey_relabel (P : DualConfig) (τ : Equiv.Perm (Fin 5)) (i : Fin 5) :
    leftKey (P.relabel τ) i = leftKey P (τ i) := by
  unfold leftKey
  have hpos : posLeft (P.relabel τ) i = posLeft P (τ i) := by
    unfold posLeft; simp only [supportF_relabel]
  rw [supportF_relabel, hpos]

private lemma candTieGrid_relabel (P : DualConfig) (τ : Equiv.Perm (Fin 5)) :
    candTieGrid (P.relabel τ) = candTieGrid P := by
  let e := permLift10 τ
  ext x
  simp only [candTieGrid, Finset.mem_union, Finset.mem_biUnion, Finset.mem_univ, true_and]
  constructor
  · rintro (hx | ⟨⟨a, b⟩, hx⟩)
    · exact Or.inl hx
    · right; refine ⟨(e a, e b), ?_⟩
      simpa [relabel_vec] using hx
  · rintro (hx | ⟨⟨a, b⟩, hx⟩)
    · exact Or.inl hx
    · right; refine ⟨(e.symm a, e.symm b), ?_⟩
      simpa [relabel_vec, e] using hx

private lemma posPairTies_relabel (P : DualConfig) (τ : Equiv.Perm (Fin 5)) (i j : Fin 5) :
    posPairTies (P.relabel τ) i j = posPairTies P (τ i) (τ j) := by
  unfold posPairTies
  rw [candTieGrid_relabel]
  simp only [supportF_relabel]

private lemma posPairTies_comm (P : DualConfig) (i j : Fin 5) :
    posPairTies P i j = posPairTies P j i := by
  ext t
  simp only [posPairTies, Finset.mem_filter]
  constructor <;> rintro ⟨hg, h0, h3, heq, hpos⟩ <;>
    exact ⟨hg, h0, h3, heq.symm, heq ▸ hpos⟩

private lemma threeCrossGraph_relabel (P : DualConfig) (τ : Equiv.Perm (Fin 5))
    {i j : Fin 5} (hij : i < j) :
    (i, j) ∈ threeCrossGraph (P.relabel τ) ↔
      (min (τ i) (τ j), max (τ i) (τ j)) ∈ threeCrossGraph P := by
  have hne : τ i ≠ τ j := τ.injective.ne (ne_of_lt hij)
  simp only [threeCrossGraph, Finset.mem_filter, Finset.mem_univ, true_and, posPairTies_relabel]
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · simp [hij, hlt, min_eq_left (le_of_lt hlt), max_eq_right (le_of_lt hlt)]
  · simp [hij, hgt, min_eq_right (le_of_lt hgt), max_eq_left (le_of_lt hgt), posPairTies_comm]

private lemma allPosTieSet_relabel (P : DualConfig) (τ : Equiv.Perm (Fin 5)) :
    allPosTieSet (P.relabel τ) = allPosTieSet P := by
  have hmem : ∀ (Q : DualConfig) (t : ℝ),
      t ∈ allPosTieSet Q ↔ ∃ a b : Fin 5, a ≠ b ∧ t ∈ posPairTies Q a b := by
    intro Q t
    simp only [allPosTieSet, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨a, b⟩, hab, ht⟩; exact ⟨a, b, ne_of_lt hab, ht⟩
    · rintro ⟨a, b, hab, ht⟩
      rcases lt_or_gt_of_ne hab with hlt | hgt
      · exact ⟨(a, b), hlt, ht⟩
      · exact ⟨(b, a), hgt, posPairTies_comm Q a b ▸ ht⟩
  ext t
  rw [hmem, hmem]
  constructor
  · rintro ⟨a, b, hab, ht⟩
    rw [posPairTies_relabel] at ht
    exact ⟨τ a, τ b, τ.injective.ne hab, ht⟩
  · rintro ⟨a, b, hab, ht⟩
    refine ⟨τ.symm a, τ.symm b, τ.symm.injective.ne hab, ?_⟩
    rw [posPairTies_relabel, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    exact ht

private lemma list_ofFn_perm {α : Type*} (f : Fin 5 → α) (τ : Equiv.Perm (Fin 5)) :
    (List.ofFn (fun i : Fin 5 => f (τ i))).Perm (List.ofFn f) := by
  rw [List.ofFn_eq_map, List.ofFn_eq_map]
  have hperm : ((List.finRange 5).map τ).Perm (List.finRange 5) := by
    have hnd1 : ((List.finRange 5).map τ).Nodup := (List.nodup_finRange 5).map τ.injective
    have hnd2 : (List.finRange 5).Nodup := List.nodup_finRange 5
    refine (List.perm_ext_iff_of_nodup hnd1 hnd2).mpr fun x => ?_
    simp only [List.mem_map, List.mem_finRange, true_and]
    exact ⟨fun _ => trivial, fun _ => ⟨τ.symm x, by simp⟩⟩
  simpa [List.map_map, Function.comp_def] using hperm.map f

private lemma sortedG_relabel (P : DualConfig) (τ : Equiv.Perm (Fin 5)) (k : Fin 5) (t : ℝ) :
    sortedG (P.relabel τ) k t = sortedG P k t := by
  unfold sortedG
  have hclip : (fun i : Fin 5 => clippedG (P.relabel τ) i t) =
      (fun i : Fin 5 => clippedG P (τ i) t) := rfl
  rw [hclip]
  let l₁ := List.ofFn (fun i : Fin 5 => clippedG P (τ i) t)
  let l₂ := List.ofFn (fun i : Fin 5 => clippedG P i t)
  have hperm := list_ofFn_perm (fun i : Fin 5 => clippedG P i t) τ
  have hsort_perm : (l₁.mergeSort (· ≤ ·)).Perm (l₂.mergeSort (· ≤ ·)) :=
    (List.mergeSort_perm l₁ _).trans (hperm.trans (List.mergeSort_perm l₂ _).symm)
  have heq : l₁.mergeSort (· ≤ ·) = l₂.mergeSort (· ≤ ·) :=
    hsort_perm.eq_of_pairwise' (List.pairwise_mergeSort' (· ≤ ·) l₁)
      (List.pairwise_mergeSort' (· ≤ ·) l₂)
  rw [heq]

private lemma rankTieSet_relabel (P : DualConfig) (τ : Equiv.Perm (Fin 5)) (q : ℕ) :
    rankTieSet (P.relabel τ) q = rankTieSet P q := by
  unfold rankTieSet
  rw [allPosTieSet_relabel]
  simp only [sortedG_relabel]

private lemma sliceExcess_relabel (P : DualConfig) (τ : Equiv.Perm (Fin 5)) (q : ℕ) :
    sliceExcess (P.relabel τ) q = sliceExcess P q := by
  unfold sliceExcess
  rw [rankTieSet_relabel]

private lemma topTiePts_relabel (P : DualConfig) (τ : Equiv.Perm (Fin 5)) :
    topTiePts (P.relabel τ) = topTiePts P := by
  let e := permLift10 τ
  ext t
  simp only [topTiePts, Finset.mem_filter, candTieGrid_relabel, topEnv_relabel]
  refine and_congr_right fun _ => and_congr_right fun _ => and_congr_right fun _ => ?_
  constructor
  · rintro ⟨a, b, hab, ha, hb⟩
    refine ⟨e a, e b, e.injective.ne hab, ?_, ?_⟩
    · rw [← relabel_vec]; exact ha
    · rw [← relabel_vec]; exact hb
  · rintro ⟨a, b, hab, ha, hb⟩
    refine ⟨e.symm a, e.symm b, e.symm.injective.ne hab, ?_, ?_⟩ <;>
      simpa [relabel_vec, e]

private lemma compressAdj_map_inj (f : Fin 5 → Fin 5) (hf : Function.Injective f) :
    ∀ l : List (Fin 5), compressAdj (l.map f) = (compressAdj l).map f
  | [] => rfl
  | [_] => rfl
  | c₁ :: c₂ :: rest => by
    simp only [List.map_cons, compressAdj]
    have hiff : (f c₁ = f c₂) ↔ (c₁ = c₂) := hf.eq_iff
    by_cases h : c₁ = c₂
    · have hf' : f c₁ = f c₂ := hiff.mpr h
      simp only [h, hf', ↓reduceIte]
      simpa [List.map_cons] using compressAdj_map_inj f hf (c₂ :: rest)
    · have hf' : f c₁ ≠ f c₂ := mt hiff.mp h
      simp only [h, hf', ↓reduceIte, List.map_cons]
      congr 1
      simpa [List.map_cons] using compressAdj_map_inj f hf (c₂ :: rest)

private lemma hullBlockCount_relabel (P : DualConfig) (τ : Equiv.Perm (Fin 5)) (hgp : IsGenPos P) :
    hullBlockCount (P.relabel τ) = hullBlockCount P := by
  have hgp' := isGenPos_relabel P τ hgp
  have htop_eq : topTiePts (P.relabel τ) = topTiePts P := topTiePts_relabel P τ
  have hcard_eq : (topTiePts (P.relabel τ)).card = (topTiePts P).card := congrArg Finset.card htop_eq
  have hseam_eq : hullSeamList (P.relabel τ) = hullSeamList P := by
    unfold hullSeamList; rw [htop_eq]
  have hmid_eq : ∀ r : Fin ((topTiePts P).card + 1),
      hullMidpoint (P.relabel τ) (Fin.cast (by rw [hcard_eq]) r) = hullMidpoint P r := by
    intro r; unfold hullMidpoint; rw [hseam_eq]; rfl
  have hmid_mem_Ioo : ∀ r : Fin ((topTiePts P).card + 1),
      0 < hullMidpoint P r ∧ hullMidpoint P r < 3 ∧ hullMidpoint P r ∉ topTiePts P := by
    intro r
    let s : List ℝ := (topTiePts P).sort (· ≤ ·)
    have hs_sorted : s.Pairwise (· < ·) := (topTiePts P).sortedLT_sort.pairwise
    have hs_mem : ∀ x ∈ s, 0 < x ∧ x < 3 := by
      intro x hx
      have hx' : x ∈ topTiePts P := (Finset.mem_sort _).mp hx
      simp only [topTiePts, Finset.mem_filter] at hx'
      exact ⟨hx'.2.1, hx'.2.2.1⟩
    have hpts_pw : (hullSeamList P).Pairwise (· < ·) := by
      unfold hullSeamList
      change ([0] ++ s ++ [3]).Pairwise (· < ·)
      rw [List.singleton_append, List.cons_append, List.pairwise_cons]
      refine ⟨fun x hx => ?_, ?_⟩
      · simp only [List.mem_append, List.mem_singleton] at hx
        rcases hx with hx | rfl
        · exact (hs_mem x hx).1
        · norm_num
      · rw [List.pairwise_append]
        refine ⟨hs_sorted, List.pairwise_singleton _ _, fun x hx y hy => ?_⟩
        rw [List.mem_singleton] at hy; subst hy
        exact (hs_mem x hx).2
    have hlen : (hullSeamList P).length = (topTiePts P).card + 2 := by
      unfold hullSeamList
      simp [Finset.length_sort]
    have hr0 : r.val < (hullSeamList P).length := by omega
    have hr1 : r.val + 1 < (hullSeamList P).length := by omega
    have hget0 : (hullSeamList P).getD r.val 0 = (hullSeamList P)[r.val] := by
      simp [List.getD_eq_getElem?_getD, hr0]
    have hget1 : (hullSeamList P).getD (r.val + 1) 3 = (hullSeamList P)[r.val + 1] := by
      simp [List.getD_eq_getElem?_getD, hr1]
    have hlt_adj : (hullSeamList P)[r.val] < (hullSeamList P)[r.val + 1] :=
      List.pairwise_iff_getElem.mp hpts_pw r.val (r.val + 1) hr0 hr1 (by omega)
    have hge0 : 0 ≤ (hullSeamList P)[r.val] := by
      rcases Nat.eq_zero_or_pos r.val with hz | hp
      · simp [hz, hullSeamList]
      · exact le_of_lt (List.pairwise_iff_getElem.mp hpts_pw 0 r.val (by omega) hr0 hp |>.trans_le' (by simp [hullSeamList]))
    have hle3 : (hullSeamList P)[r.val + 1] ≤ 3 := by
      by_cases hlast : r.val + 1 = (topTiePts P).card + 1
      · have : (hullSeamList P)[r.val + 1] = 3 := by
          unfold hullSeamList
          simp [List.getElem_append_right, hlast]
        linarith
      · have hlast' : r.val + 1 < (topTiePts P).card + 1 := by omega
        have hlt3 := List.pairwise_iff_getElem.mp hpts_pw (r.val + 1) ((topTiePts P).card + 1) hr1
          (by omega) hlast'
        have h3 : (hullSeamList P)[(topTiePts P).card + 1] = 3 := by
          unfold hullSeamList
          simp [List.getElem_append_right]
        linarith
    have hmid_def : hullMidpoint P r = ((hullSeamList P)[r.val] + (hullSeamList P)[r.val + 1]) / 2 := by
      unfold hullMidpoint; rw [hget0, hget1]
    refine ⟨by linarith, by linarith, fun hmem => ?_⟩
    have hmem_s : hullMidpoint P r ∈ s := (Finset.mem_sort _).mpr hmem
    have hmem_seam : hullMidpoint P r ∈ hullSeamList P := by
      unfold hullSeamList; simp only [List.mem_append, List.mem_singleton, Finset.mem_sort]
      exact Or.inl (Or.inr hmem)
    obtain ⟨k, hk, hkeq⟩ := List.mem_iff_getElem.mp hmem_seam
    rcases lt_trichotomy k r.val with hkr | rfl | hkr
    · have := List.pairwise_iff_getElem.mp hpts_pw k r.val hk hr0 hkr
      linarith
    · linarith
    · have hge_r1 : r.val + 1 ≤ k := hkr
      rcases eq_or_lt_of_le hge_r1 with rfl | hk_gt
      · linarith
      · have := List.pairwise_iff_getElem.mp hpts_pw (r.val + 1) k hr1 hk hk_gt
        linarith
  have hidx_eq : ∀ r : Fin ((topTiePts P).card + 1),
      permLift10 τ (hullIdx (P.relabel τ) (Fin.cast (by rw [hcard_eq]) r)) = hullIdx P r := by
    intro r
    let r' : Fin ((topTiePts (P.relabel τ)).card + 1) := Fin.cast (by rw [hcard_eq]) r
    have hmid := hmid_eq r
    have hex1 : ∃ a : Fin 10, dot2 (P.vec a) (gamma (hullMidpoint P r)) = topEnv P (hullMidpoint P r) := by
      unfold topEnv
      obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
        (fun i : Fin 5 => supportF P i (hullMidpoint P r))
      unfold supportF at hi
      rcases max_choice (dot2 (P.p1 i) (gamma (hullMidpoint P r)))
          (dot2 (P.p2 i) (gamma (hullMidpoint P r))) with hm | hm
      · refine ⟨⟨2 * i.val, by omega⟩, ?_⟩
        rw [P.vec_even i, ← hm]
        change supportF P i (hullMidpoint P r) = _
        exact hi.symm
      · refine ⟨⟨2 * i.val + 1, by omega⟩, ?_⟩
        rw [P.vec_odd i, ← hm]
        change supportF P i (hullMidpoint P r) = _
        exact hi.symm
    have hex2 : ∃ a : Fin 10,
        dot2 ((P.relabel τ).vec a) (gamma (hullMidpoint (P.relabel τ) r')) =
          topEnv (P.relabel τ) (hullMidpoint (P.relabel τ) r') := by
      obtain ⟨a, ha⟩ := hex1
      refine ⟨(permLift10 τ).symm a, ?_⟩
      rw [relabel_vec, Equiv.apply_symm_apply, hmid, topEnv_relabel]
      exact ha
    have ha1 : dot2 (P.vec (hullIdx P r)) (gamma (hullMidpoint P r)) = topEnv P (hullMidpoint P r) := by
      unfold hullIdx; rw [dif_pos hex1]; exact Classical.choose_spec hex1
    have ha2 : dot2 (P.vec (permLift10 τ (hullIdx (P.relabel τ) r'))) (gamma (hullMidpoint P r)) =
        topEnv P (hullMidpoint P r) := by
      have hspec := Classical.choose_spec hex2
      have hidx_def : hullIdx (P.relabel τ) r' = Classical.choose hex2 := by
        unfold hullIdx; rw [dif_pos hex2]
      rw [← hidx_def, relabel_vec, hmid, topEnv_relabel] at hspec
      exact hspec
    by_contra hne
    obtain ⟨hm0, hm3, hm_not⟩ := hmid_mem_Ioo r
    exact hm_not ((ray_ties_zeros_disjoint P hgp).1 (hullMidpoint P r) |>.mpr
      ⟨hm0, hm3, _, _, hne, ha2, ha1⟩)
  have hcol_list : List.ofFn (hullColors (P.relabel τ)) =
      (List.ofFn (hullColors P)).map τ.symm := by
    refine List.ext_getElem (by simp [hcard_eq]) fun n hn1 hn2 => ?_
    simp only [List.getElem_ofFn, List.getElem_map]
    let r : Fin ((topTiePts P).card + 1) := ⟨n, by simp only [List.length_map, List.length_ofFn] at hn2; exact hn2⟩
    change hullColors (P.relabel τ) (Fin.cast (by rw [hcard_eq]) r) = τ.symm (hullColors P r)
    unfold hullColors
    rw [← hidx_eq r, vecColor_permLift10, Equiv.symm_apply_apply]
  unfold hullBlockCount compressedColors
  rw [hcol_list, compressAdj_map_inj τ.symm τ.symm.injective, List.length_map]

private lemma topEnv_swap (P : DualConfig) (t : ℝ) :
    topEnv P.swap t = topEnv P (3 - t) := by
  unfold topEnv
  congr 1; ext i
  exact supportF_swap_eq P i t

private lemma candTieGrid_swap_mem_Ioo_imp (P : DualConfig) {t : ℝ} (ht0 : 0 < t) (ht3 : t < 3)
    (ht : t ∈ candTieGrid P.swap) : (3 - t) ∈ candTieGrid P := by
  have hperm : ∃ e : Equiv.Perm (Fin 10), ∀ a : Fin 10, P.swap.vec a = swap2 (P.vec (e a)) := by
    refine ⟨{ toFun := fun a => ⟨2 * (a.val / 2) + (1 - a.val % 2), by omega⟩
              invFun := fun a => ⟨2 * (a.val / 2) + (1 - a.val % 2), by omega⟩
              left_inv := fun a => by ext; dsimp; omega
              right_inv := fun a => by ext; dsimp; omega }, fun a => ?_⟩
    fin_cases a <;> rfl
  obtain ⟨e, he⟩ := hperm
  simp only [candTieGrid, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
    Finset.mem_biUnion, Finset.mem_univ, true_and] at ht ⊢
  rcases ht with (rfl | rfl) | ⟨⟨a, b⟩, hmem⟩
  · left; right; norm_num
  · left; left; norm_num
  · right; refine ⟨(e a, e b), ?_⟩
    set w := P.vec (e a) - P.vec (e b)
    have hw_sw : P.swap.vec a - P.swap.vec b = (w.2, w.1) := by
      rw [he a, he b]; ext <;> rfl
    rw [hw_sw] at hmem
    rcases hmem with rfl | hmem
    · by_cases hsum : w.2 + w.1 = 0
      · have h0 : w.1 / (w.2 + w.1) = 0 := by rw [hsum, div_zero]
        linarith
      · have hsum' : w.1 + w.2 ≠ 0 := fun h => hsum (by linarith)
        right; right; field_simp; ring
    · rcases hmem with rfl | hmem
      · by_cases hdiff : w.2 - w.1 = 0
        · have h0 : (2 * w.2 - w.1) / (w.2 - w.1) = 0 := by rw [hdiff, div_zero]
          linarith
        · have hdiff' : w.1 - w.2 ≠ 0 := fun h => hdiff (by linarith)
          right; left; field_simp; ring
      · subst hmem
        by_cases hsum : w.2 + w.1 = 0
        · have h0 : (2 * w.2 + 3 * w.1) / (w.2 + w.1) = 0 := by rw [hsum, div_zero]
          linarith
        · have hsum' : w.1 + w.2 ≠ 0 := fun h => hsum (by linarith)
          left; field_simp; ring

private lemma candTieGrid_swap_mem_Ioo (P : DualConfig) {t : ℝ} (ht0 : 0 < t) (ht3 : t < 3) :
    t ∈ candTieGrid P.swap ↔ (3 - t) ∈ candTieGrid P := by
  constructor
  · exact candTieGrid_swap_mem_Ioo_imp P ht0 ht3
  · intro h
    have hsw : P.swap.swap = P := by cases P; simp [DualConfig.swap, swap2]
    have h1 := candTieGrid_swap_mem_Ioo_imp P.swap (by linarith) (by linarith) (hsw ▸ h)
    simpa using h1

private lemma posPairTies_swap (P : DualConfig) (i j : Fin 5) :
    posPairTies P.swap i j = (posPairTies P i j).image (3 - ·) := by
  ext t
  simp only [posPairTies, Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨hg, h0, h3, heq, hpos⟩
    refine ⟨3 - t, ⟨(candTieGrid_swap_mem_Ioo P h0 h3).mp hg, by linarith, by linarith, ?_, ?_⟩,
      by ring⟩
    · simpa [supportF_swap_eq] using heq
    · simpa [supportF_swap_eq] using hpos
  · rintro ⟨s, ⟨hg, h0, h3, heq, hpos⟩, rfl⟩
    refine ⟨(candTieGrid_swap_mem_Ioo P (by linarith) (by linarith)).mpr (by simpa using hg),
      by linarith, by linarith, ?_, ?_⟩
    · simp [supportF_swap_eq, heq]
    · simp [supportF_swap_eq, hpos]

private lemma threeCrossGraph_swap (P : DualConfig) :
    threeCrossGraph P.swap = threeCrossGraph P := by
  ext p
  simp only [threeCrossGraph, Finset.mem_filter, Finset.mem_univ, true_and, posPairTies_swap]
  rw [Finset.card_image_of_injective _ (fun a b (h : 3 - a = 3 - b) => by linarith)]

private lemma sortedG_swap (P : DualConfig) (k : Fin 5) (t : ℝ) :
    sortedG P.swap k t = sortedG P k (3 - t) := by
  unfold sortedG
  have hclip : (fun i : Fin 5 => clippedG P.swap i t) =
      (fun i : Fin 5 => clippedG P i (3 - t)) := by
    ext i; unfold clippedG; rw [supportF_swap_eq]
  rw [hclip]

private lemma allPosTieSet_swap (P : DualConfig) :
    allPosTieSet P.swap = (allPosTieSet P).image (3 - ·) := by
  ext t
  simp only [allPosTieSet, Finset.mem_biUnion, Finset.mem_image, Finset.mem_filter,
    Finset.mem_univ, true_and, posPairTies_swap]
  constructor
  · rintro ⟨p, hp, s, hs, rfl⟩; exact ⟨s, ⟨p, hp, hs⟩, rfl⟩
  · rintro ⟨s, ⟨p, hp, hs⟩, rfl⟩; exact ⟨p, hp, s, hs, rfl⟩

private lemma sliceExcess_swap (P : DualConfig) (q : ℕ) :
    sliceExcess P.swap q = sliceExcess P q := by
  unfold sliceExcess
  have hr : rankTieSet P.swap q = (rankTieSet P q).image (3 - ·) := by
    ext t
    simp only [rankTieSet, Finset.mem_filter, Finset.mem_image, allPosTieSet_swap]
    constructor
    · rintro ⟨⟨s, hs, rfl⟩, hcond⟩
      refine ⟨s, ⟨hs, ?_⟩, rfl⟩
      simpa [sortedG_swap] using hcond
    · rintro ⟨s, ⟨hs, hcond⟩, rfl⟩
      refine ⟨⟨s, hs, rfl⟩, ?_⟩
      simpa [sortedG_swap] using hcond
  rw [hr, Finset.card_image_of_injective _ (fun a b (h : 3 - a = 3 - b) => by linarith)]

private lemma rightPerm_strictMono (P : DualConfig) (hgp : IsGenPos P) :
    StrictMono (fun r : Fin 5 => rightKey P (rightPerm P r)) := by
  have hex : ∃ σ : Equiv.Perm (Fin 5), StrictMono (fun r : Fin 5 => rightKey P (σ r)) := by
    refine ⟨Tuple.sort (rightKey P), ?_⟩
    exact (Tuple.monotone_sort (rightKey P)).strictMono_of_injective
      ((rightKey_injective P hgp).comp (Tuple.sort (rightKey P)).injective)
  unfold rightPerm
  rw [dif_pos hex]
  exact Classical.choose_spec hex

private lemma exists_left_sort_perm (P : DualConfig) (hgp : IsGenPos P) :
    ∃ τ : Equiv.Perm (Fin 5), StrictMono (leftKey (P.relabel τ)) := by
  refine ⟨Tuple.sort (leftKey P), ?_⟩
  have hsm : StrictMono (fun i : Fin 5 => leftKey P (Tuple.sort (leftKey P) i)) :=
    (Tuple.monotone_sort (leftKey P)).strictMono_of_injective
      ((leftKey_injective P hgp).comp (Tuple.sort (leftKey P)).injective)
  intro i j hij
  rw [leftKey_relabel, leftKey_relabel]
  exact hsm hij

private lemma permInversions_ge_four_of_apply_four_eq_zero (σ : Equiv.Perm (Fin 5))
    (h4 : σ (4 : Fin 5) = (0 : Fin 5)) :
    4 ≤ permInversions σ := by
  have hS_card :
      ({((0 : Fin 5), (4 : Fin 5)), ((1 : Fin 5), (4 : Fin 5)),
        ((2 : Fin 5), (4 : Fin 5)), ((3 : Fin 5), (4 : Fin 5))} :
        Finset (Fin 5 × Fin 5)).card = 4 := by decide
  rw [← hS_card]
  refine Finset.card_le_card fun p hp => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  have hsub : p.1 < (4 : Fin 5) ∧ p.2 = (4 : Fin 5) := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl <;> exact ⟨by decide, rfl⟩
  rw [hsub.2, h4]
  refine ⟨hsub.1, ?_⟩
  have hne : σ p.1 ≠ (0 : Fin 5) := by
    rw [← h4]
    exact σ.injective.ne (ne_of_lt hsub.1)
  exact Fin.pos_of_ne_zero hne

private lemma candTieGrid_mem_of_tie (P : DualConfig) (hgp : IsGenPos P)
    {t : ℝ} (ht0 : 0 < t) (ht3 : t < 3) {i j : Fin 5} (hij : i ≠ j)
    (heq : supportF P i t = supportF P j t) : t ∈ candTieGrid P := by
  have hvc_even : ∀ k : Fin 5, vecColor ⟨2 * k.val, by omega⟩ = k := by
    intro k; ext; dsimp [vecColor]; omega
  have hvc_odd : ∀ k : Fin 5, vecColor ⟨2 * k.val + 1, by omega⟩ = k := by
    intro k; ext; dsimp [vecColor]; omega
  obtain ⟨a, ha_col, ha_dot⟩ :
      ∃ a : Fin 10, vecColor a = i ∧ dot2 (P.vec a) (gamma t) = supportF P i t := by
    unfold supportF
    rcases max_choice (dot2 (P.p1 i) (gamma t)) (dot2 (P.p2 i) (gamma t)) with h | h
    · exact ⟨⟨2 * i.val, by omega⟩, hvc_even i, by rw [P.vec_even i, h]⟩
    · exact ⟨⟨2 * i.val + 1, by omega⟩, hvc_odd i, by rw [P.vec_odd i, h]⟩
  obtain ⟨b, hb_col, hb_dot⟩ :
      ∃ b : Fin 10, vecColor b = j ∧ dot2 (P.vec b) (gamma t) = supportF P j t := by
    unfold supportF
    rcases max_choice (dot2 (P.p1 j) (gamma t)) (dot2 (P.p2 j) (gamma t)) with h | h
    · exact ⟨⟨2 * j.val, by omega⟩, hvc_even j, by rw [P.vec_even j, h]⟩
    · exact ⟨⟨2 * j.val + 1, by omega⟩, hvc_odd j, by rw [P.vec_odd j, h]⟩
  have hab : a ≠ b := fun h => hij (by rw [← ha_col, ← hb_col, h])
  have hw_ne := hgp.2.1 a b hab
  let w := P.vec a - P.vec b
  have hw1 : w.1 ≠ 0 := sub_ne_zero.mpr hw_ne.1
  have hw2 : w.2 ≠ 0 := sub_ne_zero.mpr hw_ne.2
  have hdot : dot2 w (gamma t) = 0 := by
    change dot2 (P.vec a - P.vec b) (gamma t) = 0
    simp only [dot2, Prod.fst_sub, Prod.snd_sub]
    have ha' : (P.vec a).1 * (gamma t).1 + (P.vec a).2 * (gamma t).2 = supportF P i t := ha_dot
    have hb' : (P.vec b).1 * (gamma t).1 + (P.vec b).2 * (gamma t).2 = supportF P j t := hb_dot
    linarith
  unfold candTieGrid
  apply Finset.mem_union_right
  refine Finset.mem_biUnion.mpr ⟨(a, b), Finset.mem_univ _, ?_⟩
  dsimp only
  simp only [Finset.mem_insert, Finset.mem_singleton]
  unfold gamma dot2 at hdot
  by_cases ht1 : t ≤ 1
  · rw [if_pos ht1] at hdot
    dsimp at hdot
    have hsum : w.1 + w.2 ≠ 0 := by
      intro h; apply hw2
      have : w.1 * (-t) + w.2 * (1 - t) = -(w.1 + w.2) * t + w.2 := by ring
      rw [this, h] at hdot; linarith
    left; rw [eq_div_iff hsum]; linear_combination -hdot
  · by_cases ht2 : t ≤ 2
    · rw [if_neg ht1, if_pos ht2] at hdot
      dsimp at hdot
      have hdiff : w.1 - w.2 ≠ 0 := by
        intro h; apply hw1
        have : w.1 * (t - 2) + w.2 * (1 - t) = (w.1 - w.2) * t - 2 * w.1 + w.2 := by ring
        rw [this, h] at hdot; linarith
      right; left; rw [eq_div_iff hdiff]; linear_combination hdot
    · rw [if_neg ht1, if_neg ht2] at hdot
      dsimp at hdot
      have hsum : w.1 + w.2 ≠ 0 := by
        intro h; apply hw1
        have : w.1 * (t - 2) + w.2 * (t - 3) = (w.1 + w.2) * t - 2 * w.1 - 3 * w.2 := by ring
        rw [this, h] at hdot; linarith
      right; right; rw [eq_div_iff hsum]; linear_combination hdot

private lemma posLeft_eq_zero_of_pos_at_zero (P : DualConfig) (hgp : IsGenPos P) (i : Fin 5)
    (h0 : 0 < supportF P i 0) : posLeft P i = 0 := by
  have hpi := posInterval_eq_Ioo P hgp i
  have hle0 : posLeft P i ≤ 0 := by
    by_contra hgt
    replace hgt : 0 < posLeft P i := not_le.mp hgt
    have hopen : IsOpen {t : ℝ | 0 < supportF P i t} :=
      isOpen_lt continuous_const (supportF_continuous P i)
    obtain ⟨δ, hδ, hsub⟩ := Metric.isOpen_iff.mp hopen 0 h0
    let t₁ : ℝ := min (posLeft P i / 2) (min (δ / 2) 1)
    have ht1_pos : 0 < t₁ := lt_min (by linarith) (lt_min (by linarith) (by norm_num))
    have ht1_lt3 : t₁ < 3 := lt_of_le_of_lt (min_le_right _ _) (lt_of_le_of_lt (min_le_right _ _) (by norm_num))
    have ht1_ball : t₁ ∈ Metric.ball (0 : ℝ) δ := by
      rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos ht1_pos]
      exact lt_of_le_of_lt (min_le_right _ _) (lt_of_le_of_lt (min_le_left _ _) (by linarith))
    have hf_pos : 0 < supportF P i t₁ := Set.mem_setOf.mp (hsub ht1_ball)
    have hmem := (hpi.2.2.2.2 t₁).mp ⟨ht1_pos, ht1_lt3, hf_pos⟩
    have : t₁ ≤ posLeft P i / 2 := min_le_left _ _
    linarith [hmem.1]
  exact le_antisymm hle0 hpi.1

private lemma left_dom_of_leftKey_lt (P : DualConfig) (hgp : IsGenPos P)
    (h_shat : ∀ m : Fin 5 → Bool, ∃ z : ℝ × ℝ, InOmega z ∧ RealizesDualMask P m z)
    {i j : Fin 5} (hij : leftKey P i < leftKey P j) :
    ∃ t_L : ℝ, 0 < t_L ∧ t_L < 3 ∧ 0 < supportF P i t_L ∧
      supportF P j t_L < supportF P i t_L ∧
      ∀ s ∈ posPairTies P i j, t_L < s := by
  have hpi := posInterval_eq_Ioo P hgp i
  have hpj := posInterval_eq_Ioo P hgp j
  let S := posPairTies P i j
  let b : ℝ := if h : S.Nonempty then S.min' h else 3
  have hb_pos : 0 < b := by
    dsimp [b]; split_ifs with h
    · have hs := h.choose_spec
      have hmem : S.min' h ∈ S := Finset.min'_mem S h
      simp only [S, posPairTies, Finset.mem_filter] at hmem
      exact hmem.2.1
    · norm_num
  have hb_le3 : b ≤ 3 := by
    dsimp [b]; split_ifs with h
    · have hmem : S.min' h ∈ S := Finset.min'_mem S h
      simp only [S, posPairTies, Finset.mem_filter] at hmem
      exact le_of_lt hmem.2.2.1
    · norm_num
  have hb_le_all : ∀ s ∈ posPairTies P i j, b ≤ s := by
    intro s hs
    dsimp [b]
    have hne : S.Nonempty := ⟨s, hs⟩
    rw [dif_pos hne]
    exact Finset.min'_le S s hs
  by_cases hi : 0 < supportF P i 0 <;> by_cases hj : 0 < supportF P j 0
  · have hlt0 : supportF P j 0 < supportF P i 0 := by
      unfold leftKey at hij; simp only [hi, hj, ↓reduceIte] at hij; linarith
    have hopen : IsOpen {t : ℝ | 0 < supportF P i t ∧ supportF P j t < supportF P i t} :=
      IsOpen.and (isOpen_lt continuous_const (supportF_continuous P i))
        (isOpen_lt (supportF_continuous P j) (supportF_continuous P i))
    obtain ⟨δ, hδ, hsub⟩ := Metric.isOpen_iff.mp hopen 0 ⟨hi, hlt0⟩
    let t_L : ℝ := min (δ / 2) (b / 2)
    have ht_pos : 0 < t_L := lt_min (by linarith) (by linarith)
    have ht_lt_b : t_L < b := lt_of_le_of_lt (min_le_right _ _) (by linarith)
    have ht_ball : t_L ∈ Metric.ball (0 : ℝ) δ := by
      rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos ht_pos]
      exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
    obtain ⟨hfi, hlt⟩ := Set.mem_setOf.mp (hsub ht_ball)
    exact ⟨t_L, ht_pos, lt_of_lt_of_le ht_lt_b hb_le3, hfi, hlt,
      fun s hs => lt_of_lt_of_le ht_lt_b (hb_le_all s hs)⟩
  · have hi_zero : posLeft P i = 0 := posLeft_eq_zero_of_pos_at_zero P hgp i hi
    obtain ⟨hj_pos, _⟩ := supportF_posLeft_zero P hgp j hj
    have hri_pos : 0 < posRight P i := lt_of_le_of_lt hpi.1 (lt_trans hpi.2.1 hpi.2.2.1)
    let t_L : ℝ := min (posLeft P j / 2) (min (posRight P i / 2) (b / 2))
    have ht_pos : 0 < t_L := lt_min (by linarith) (lt_min (by linarith) (by linarith))
    have ht_lt_pj : t_L < posLeft P j := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have ht_lt_ri : t_L < posRight P i :=
      lt_of_le_of_lt (min_le_right _ _) (lt_of_le_of_lt (min_le_left _ _) (by linarith))
    have ht_lt_b : t_L < b :=
      lt_of_le_of_lt (min_le_right _ _) (lt_of_le_of_lt (min_le_right _ _) (by linarith))
    have hfi : 0 < supportF P i t_L :=
      ((hpi.2.2.2.2 t_L).mpr ⟨by linarith [hi_zero], ht_lt_ri⟩).2.2
    have hfj_le : supportF P j t_L ≤ 0 := by
      by_contra hpos
      replace hpos : 0 < supportF P j t_L := not_le.mp hpos
      have hm := (hpj.2.2.2.2 t_L).mp ⟨ht_pos, lt_of_lt_of_le ht_lt_b hb_le3, hpos⟩
      linarith [hm.1]
    exact ⟨t_L, ht_pos, lt_of_lt_of_le ht_lt_b hb_le3, hfi, by linarith,
      fun s hs => lt_of_lt_of_le ht_lt_b (hb_le_all s hs)⟩
  · exfalso
    unfold leftKey at hij; simp only [hi, hj, ↓reduceIte] at hij
    linarith [hpi.1]
  · have hij_pos : posLeft P i < posLeft P j := by
      unfold leftKey at hij; simp only [hi, hj, ↓reduceIte] at hij; exact hij
    obtain ⟨t₀, _, _, ht0_all⟩ := posInterval_common_anchor P hgp h_shat
    have hpj_lt_ri : posLeft P j < posRight P i := lt_trans (ht0_all j).1 (ht0_all i).2
    have hpj_lt_b : posLeft P j < b := by
      dsimp [b]; split_ifs with h
      · have hmem : S.min' h ∈ S := Finset.min'_mem S h
        simp only [S, posPairTies, Finset.mem_filter] at hmem
        have hfj : 0 < supportF P j (S.min' h) := hmem.2.2.2.1 ▸ hmem.2.2.2.2
        exact ((hpj.2.2.2.2 (S.min' h)).mp ⟨hmem.2.1, hmem.2.2.1, hfj⟩).1
      · exact lt_of_lt_of_le (lt_trans hpj.2.1 hpj.2.2.1) hpj.2.2.2.1
    let t_L : ℝ := (posLeft P i + posLeft P j) / 2
    have ht_gt_pi : posLeft P i < t_L := by dsimp [t_L]; linarith
    have ht_lt_pj : t_L < posLeft P j := by dsimp [t_L]; linarith
    have ht_pos : 0 < t_L := lt_of_le_of_lt hpi.1 ht_gt_pi
    have ht_lt3 : t_L < 3 := lt_of_lt_of_le (lt_trans ht_lt_pj hpj_lt_b) hb_le3
    have hfi : 0 < supportF P i t_L :=
      ((hpi.2.2.2.2 t_L).mpr ⟨ht_gt_pi, lt_trans ht_lt_pj hpj_lt_ri⟩).2.2
    have hfj_le : supportF P j t_L ≤ 0 := by
      by_contra hpos
      replace hpos : 0 < supportF P j t_L := not_le.mp hpos
      have hm := (hpj.2.2.2.2 t_L).mp ⟨ht_pos, ht_lt3, hpos⟩
      linarith [hm.1]
    exact ⟨t_L, ht_pos, ht_lt3, hfi, by linarith,
      fun s hs => lt_of_lt_of_le (lt_trans ht_lt_pj hpj_lt_b) (hb_le_all s hs)⟩

private lemma right_dom_of_rightKey_lt (P : DualConfig) (hgp : IsGenPos P)
    (h_shat : ∀ m : Fin 5 → Bool, ∃ z : ℝ × ℝ, InOmega z ∧ RealizesDualMask P m z)
    {i j : Fin 5} (hij : rightKey P i < rightKey P j) :
    ∃ t_R : ℝ, 0 < t_R ∧ t_R < 3 ∧ 0 < supportF P j t_R ∧
      supportF P i t_R < supportF P j t_R ∧
      ∀ s ∈ posPairTies P i j, s < t_R := by
  have hgp_sw : IsGenPos P.swap := (P.swap_spec).2.1.mpr hgp
  have h_shat_sw : ∀ m : Fin 5 → Bool, ∃ z : ℝ × ℝ, InOmega z ∧ RealizesDualMask P.swap m z := by
    intro m; obtain ⟨z, hz, hm⟩ := h_shat m
    exact ⟨swap2 z, inOmega_swap2 hz, (P.swap_spec).2.2 m z |>.mpr hm⟩
  have hsw_lt : leftKey P.swap j < leftKey P.swap i := by
    rw [(boundaryKey_swap P hgp j).1, (boundaryKey_swap P hgp i).1]
    linarith
  obtain ⟨t', ht'0, ht'3, hfj', hlt', hall'⟩ :=
    left_dom_of_leftKey_lt P.swap hgp_sw h_shat_sw hsw_lt
  refine ⟨3 - t', by linarith, by linarith, ?_, ?_, fun s hs => ?_⟩
  · simpa [supportF_swap_eq] using hfj'
  · simpa [supportF_swap_eq] using hlt'
  · have hs' : 3 - s ∈ posPairTies P.swap j i := by
      rw [posPairTies_comm, posPairTies_swap]
      exact Finset.mem_image.mpr ⟨s, hs, rfl⟩
    linarith [hall' (3 - s) hs']

private lemma sign_change_at_posPairTie (P : DualConfig) (hgp : IsGenPos P)
    {i j : Fin 5} (hij : i ≠ j) {t : ℝ} (ht : t ∈ posPairTies P i j) :
    ∃ ε > 0, ∀ δ : ℝ, 0 < δ → δ ≤ ε → 0 < t - δ ∧ t + δ < 3 ∧
      (supportF P i (t - δ) - supportF P j (t - δ)) *
      (supportF P i (t + δ) - supportF P j (t + δ)) < 0 := by
  simp only [posPairTies, Finset.mem_filter] at ht
  rcases ht with ⟨_, ht0, ht3, heq, hpos⟩
  have hvc_even : ∀ k : Fin 5, vecColor ⟨2 * k.val, by omega⟩ = k := by
    intro k; ext; dsimp [vecColor]; omega
  have hvc_odd : ∀ k : Fin 5, vecColor ⟨2 * k.val + 1, by omega⟩ = k := by
    intro k; ext; dsimp [vecColor]; omega
  have hrd := ray_ties_zeros_disjoint P hgp
  have hget_vec : ∀ k : Fin 5, ∃ a : Fin 10,
      vecColor a = k ∧ dot2 (P.vec a) (gamma t) = supportF P k t := by
    intro k; unfold supportF
    rcases max_choice (dot2 (P.p1 k) (gamma t)) (dot2 (P.p2 k) (gamma t)) with h | h
    · exact ⟨⟨2 * k.val, by omega⟩, hvc_even k, by rw [P.vec_even k, h]⟩
    · exact ⟨⟨2 * k.val + 1, by omega⟩, hvc_odd k, by rw [P.vec_odd k, h]⟩
  obtain ⟨ai, hai_col, hai_dot⟩ := hget_vec i
  obtain ⟨aj, haj_col, haj_dot⟩ := hget_vec j
  have hai_ne_aj : ai ≠ aj := fun h => hij (by rw [← hai_col, ← haj_col, h])
  have ht_ne1 : t ≠ 1 := by
    intro h; subst h
    exact (hrd.2.1 1 (by simp) ai aj).2 hai_ne_aj (by linarith [hai_dot, haj_dot, heq])
  have ht_ne2 : t ≠ 2 := by
    intro h; subst h
    exact (hrd.2.1 2 (by simp) ai aj).2 hai_ne_aj (by linarith [hai_dot, haj_dot, heq])
  have hap_tie : ∀ k : Fin 5,
      dot2 (P.p1 k) (gamma (apexRay P k)) = dot2 (P.p2 k) (gamma (apexRay P k)) := by
    intro k
    obtain ⟨hq3, hd1, hd2, _⟩ := P.apex_spec k
    have hom : InOmega (P.apex k) := Or.inl hq3.1
    have hnorm := inOmega_norm_pos hom
    have hrec := gamma_rayParam_smul hom
    rw [← hrec, dot2_smul_right] at hd1 hd2
    have : (|(P.apex k).1| + |(P.apex k).2|) * dot2 (P.p1 k) (gamma (apexRay P k)) =
        (|(P.apex k).1| + |(P.apex k).2|) * dot2 (P.p2 k) (gamma (apexRay P k)) := by
      unfold apexRay; linarith
    exact mul_left_cancel₀ (ne_of_gt hnorm) this
  have ht_ne_ap_i : t ≠ apexRay P i := by
    intro h; subst h
    let a1 : Fin 10 := ⟨2 * i.val, by omega⟩
    let a2 : Fin 10 := ⟨2 * i.val + 1, by omega⟩
    have ha12 : a1 < a2 := by show 2 * i.val < 2 * i.val + 1; omega
    have h12 : dot2 (P.vec a1) (gamma (apexRay P i)) = dot2 (P.vec a2) (gamma (apexRay P i)) := by
      rw [P.vec_even i, P.vec_odd i]; exact hap_tie i
    have h1_sup : dot2 (P.vec a1) (gamma (apexRay P i)) = supportF P i (apexRay P i) := by
      rw [P.vec_even i]; unfold supportF; rw [hap_tie i, max_self]
    have haij_ne : a1 ≠ aj := fun h => hij (by rw [← hvc_even i, ← haj_col, ← h])
    rcases lt_or_gt_of_ne haij_ne with hlt | hgt
    · have hpair_ne : (a1, a2) ≠ (a1, aj) := fun h => by
        have : a2 = aj := congrArg Prod.snd h
        dsimp [a2] at this
        exact hij (by rw [← hvc_odd i, ← haj_col, ← this])
      exact hrd.2.2.2 (apexRay P i) ht0 ht3 a1 a2 a1 aj ha12 hlt hpair_ne
        ⟨h12, by linarith [h1_sup, haj_dot, heq]⟩
    · have hpair_ne : (a1, a2) ≠ (aj, a1) := fun h => by
        have : a1 = aj := congrArg Prod.fst h
        exact haij_ne this
      exact hrd.2.2.2 (apexRay P i) ht0 ht3 a1 a2 aj a1 ha12 hgt hpair_ne
        ⟨h12, by linarith [h1_sup, haj_dot, heq]⟩
  have ht_ne_ap_j : t ≠ apexRay P j := by
    intro h; subst h
    let b1 : Fin 10 := ⟨2 * j.val, by omega⟩
    let b2 : Fin 10 := ⟨2 * j.val + 1, by omega⟩
    have hb12 : b1 < b2 := by show 2 * j.val < 2 * j.val + 1; omega
    have h12 : dot2 (P.vec b1) (gamma (apexRay P j)) = dot2 (P.vec b2) (gamma (apexRay P j)) := by
      rw [P.vec_even j, P.vec_odd j]; exact hap_tie j
    have h1_sup : dot2 (P.vec b1) (gamma (apexRay P j)) = supportF P j (apexRay P j) := by
      rw [P.vec_even j]; unfold supportF; rw [hap_tie j, max_self]
    have hbij_ne : b1 ≠ ai := fun h => hij.symm (by rw [← hvc_even j, ← hai_col, ← h])
    rcases lt_or_gt_of_ne hbij_ne with hlt | hgt
    · have hpair_ne : (b1, b2) ≠ (b1, ai) := fun h => by
        have : b2 = ai := congrArg Prod.snd h
        dsimp [b2] at this
        exact hij.symm (by rw [← hvc_odd j, ← hai_col, ← this])
      exact hrd.2.2.2 (apexRay P j) ht0 ht3 b1 b2 b1 ai hb12 hlt hpair_ne
        ⟨h12, by linarith [h1_sup, hai_dot, heq]⟩
    · have hpair_ne : (b1, b2) ≠ (ai, b1) := fun h => by
        have : b1 = ai := congrArg Prod.fst h
        exact hbij_ne this
      exact hrd.2.2.2 (apexRay P j) ht0 ht3 b1 b2 ai b1 hb12 hgt hpair_ne
        ⟨h12, by linarith [h1_sup, hai_dot, heq]⟩
  let ε : ℝ :=
    min (min t (3 - t)) (min (min |t - 1| |t - 2|) (min |t - apexRay P i| |t - apexRay P j|)) / 2
  have hε_pos : 0 < ε := by
    dsimp [ε]
    have h1 : 0 < min t (3 - t) := lt_min ht0 (by linarith)
    have h2 : 0 < min |t - 1| |t - 2| :=
      lt_min (abs_sub_pos.mpr ht_ne1) (abs_sub_pos.mpr ht_ne2)
    have h3 : 0 < min |t - apexRay P i| |t - apexRay P j| :=
      lt_min (abs_sub_pos.mpr ht_ne_ap_i) (abs_sub_pos.mpr ht_ne_ap_j)
    exact div_pos (lt_min h1 (lt_min h2 h3)) (by norm_num)
  have hε_t : ε < t := by
    have : ε ≤ min t (3 - t) / 2 := by dsimp [ε]; exact div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
    linarith [min_le_left t (3 - t)]
  have hε_3 : t + ε < 3 := by
    have : ε ≤ min t (3 - t) / 2 := by
      dsimp [ε]
      exact div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
    linarith [min_le_right t (3 - t)]
  have hε_lt1 : ε < |t - 1| := by
    have : ε ≤ |t - 1| / 2 := by
      dsimp [ε]
      have := min_le_right (min t (3 - t)) (min (min |t - 1| |t - 2|) (min |t - apexRay P i| |t - apexRay P j|))
      have := min_le_left (min |t - 1| |t - 2|) (min |t - apexRay P i| |t - apexRay P j|)
      have := min_le_left |t - 1| |t - 2|
      linarith
    linarith [abs_sub_pos.mpr ht_ne1]
  have hε_lt2 : ε < |t - 2| := by
    have : ε ≤ |t - 2| / 2 := by
      dsimp [ε]
      have := min_le_right (min t (3 - t)) (min (min |t - 1| |t - 2|) (min |t - apexRay P i| |t - apexRay P j|))
      have := min_le_left (min |t - 1| |t - 2|) (min |t - apexRay P i| |t - apexRay P j|)
      have := min_le_right |t - 1| |t - 2|
      linarith
    linarith [abs_sub_pos.mpr ht_ne2]
  have hε_api : ε < |t - apexRay P i| := by
    have : ε ≤ |t - apexRay P i| / 2 := by
      dsimp [ε]
      have := min_le_right (min t (3 - t)) (min (min |t - 1| |t - 2|) (min |t - apexRay P i| |t - apexRay P j|))
      have := min_le_right (min |t - 1| |t - 2|) (min |t - apexRay P i| |t - apexRay P j|)
      have := min_le_left |t - apexRay P i| |t - apexRay P j|
      linarith
    linarith [abs_sub_pos.mpr ht_ne_ap_i]
  have hε_apj : ε < |t - apexRay P j| := by
    have : ε ≤ |t - apexRay P j| / 2 := by
      dsimp [ε]
      have := min_le_right (min t (3 - t)) (min (min |t - 1| |t - 2|) (min |t - apexRay P i| |t - apexRay P j|))
      have := min_le_right (min |t - 1| |t - 2|) (min |t - apexRay P i| |t - apexRay P j|)
      have := min_le_right |t - apexRay P i| |t - apexRay P j|
      linarith
    linarith [abs_sub_pos.mpr ht_ne_ap_j]
  have hε_lt2_span : ε < 2 := by
    have : ε ≤ min t (3 - t) / 2 := by
      dsimp [ε]
      exact div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
    have : min t (3 - t) ≤ 3 / 2 := by
      rcases le_total t (3 / 2) with h | h
      · exact le_trans (min_le_left _ _) h
      · exact le_trans (min_le_right _ _) (by linarith)
    linarith
  refine ⟨ε, hε_pos, fun δ hδ_pos hδ_le => ?_⟩
  have hδ_t : δ < t := lt_of_le_of_lt hδ_le hε_t
  have hδ_3 : t + δ < 3 := by linarith
  have hδ_lt1 : δ < |t - 1| := lt_of_le_of_lt hδ_le hε_lt1
  have hδ_lt2 : δ < |t - 2| := lt_of_le_of_lt hδ_le hε_lt2
  have hδ_api : δ < |t - apexRay P i| := lt_of_le_of_lt hδ_le hε_api
  have hδ_apj : δ < |t - apexRay P j| := lt_of_le_of_lt hδ_le hε_apj
  have hδ_lt2_span : δ < 2 := lt_of_le_of_lt hδ_le hε_lt2_span
  have hsw := (supportF_branch_switch P hgp).2
  have hbranch : ∀ k : Fin 5, t ≠ apexRay P k → δ < |t - apexRay P k| →
      ∃ ak : Fin 10, vecColor ak = k ∧
        ∀ s : ℝ, s = t - δ ∨ s = t ∨ s = t + δ →
          supportF P k s = dot2 (P.vec ak) (gamma s) := by
    intro k hne hlt_ap
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hsub_neg : t - apexRay P k < 0 := by linarith
      rw [abs_of_neg hsub_neg] at hlt_ap
      refine ⟨⟨2 * k.val, by omega⟩, hvc_even k, fun s hs => ?_⟩
      have hs_lt : s < apexRay P k := by rcases hs with rfl | rfl | rfl <;> linarith
      have hs0 : 0 ≤ s := by rcases hs with rfl | rfl | rfl <;> linarith
      have hcmp := (hsw k).2.2.2.1 s hs0 hs_lt
      rw [P.vec_even k]; unfold supportF; exact max_eq_left (le_of_lt hcmp)
    · have hsub_pos : 0 < t - apexRay P k := by linarith
      rw [abs_of_pos hsub_pos] at hlt_ap
      refine ⟨⟨2 * k.val + 1, by omega⟩, hvc_odd k, fun s hs => ?_⟩
      have hs_gt : apexRay P k < s := by rcases hs with rfl | rfl | rfl <;> linarith
      have hs3 : s ≤ 3 := by rcases hs with rfl | rfl | rfl <;> linarith
      have hcmp := (hsw k).2.2.2.2 s hs_gt hs3
      rw [P.vec_odd k]; unfold supportF; exact max_eq_right (le_of_lt hcmp)
  obtain ⟨bi, hbi_col, hbi_eq⟩ := hbranch i ht_ne_ap_i hδ_api
  obtain ⟨bj, hbj_col, hbj_eq⟩ := hbranch j ht_ne_ap_j hδ_apj
  have hbi_ne_bj : bi ≠ bj := fun h => hij (by rw [← hbi_col, ← hbj_col, h])
  have hgamma_mid : gamma (t + δ) + gamma (t - δ) = (2 : ℝ) • gamma t := by
    unfold gamma
    rcases lt_or_gt_of_ne ht_ne1 with hlt1 | hgt1
    · rw [abs_of_neg (by linarith)] at hδ_lt1
      rw [if_pos (by linarith), if_pos (by linarith), if_pos (by linarith)]
      ext <;> dsimp <;> ring
    · rw [abs_of_pos (by linarith)] at hδ_lt1
      rcases lt_or_gt_of_ne ht_ne2 with hlt2 | hgt2
      · rw [abs_of_neg (by linarith)] at hδ_lt2
        rw [if_neg (by linarith), if_pos (by linarith),
            if_neg (by linarith), if_pos (by linarith),
            if_neg (by linarith), if_pos (by linarith)]
        ext <;> dsimp <;> ring
      · rw [abs_of_pos (by linarith)] at hδ_lt2
        rw [if_neg (by linarith), if_neg (by linarith),
            if_neg (by linarith), if_neg (by linarith),
            if_neg (by linarith), if_neg (by linarith)]
        ext <;> dsimp <;> ring
  have hsum_zero : (supportF P i (t + δ) - supportF P j (t + δ)) +
      (supportF P i (t - δ) - supportF P j (t - δ)) = 0 := by
    rw [hbi_eq _ (Or.inr (Or.inr rfl)), hbj_eq _ (Or.inr (Or.inr rfl)),
        hbi_eq _ (Or.inl rfl), hbj_eq _ (Or.inl rfl)]
    have hmid_t : supportF P i t - supportF P j t = 0 := by linarith
    rw [hbi_eq _ (Or.inr (Or.inl rfl)), hbj_eq _ (Or.inr (Or.inl rfl))] at hmid_t
    have hdot_lin : ∀ u v : ℝ × ℝ, dot2 (P.vec bi) u - dot2 (P.vec bj) u +
        (dot2 (P.vec bi) v - dot2 (P.vec bj) v) =
        dot2 (P.vec bi - P.vec bj) (u + v) := by
      intro u v; simp only [dot2, Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add]; ring
    rw [hdot_lin, hgamma_mid, dot2_smul_right]
    have : dot2 (P.vec bi - P.vec bj) (gamma t) = 0 := by
      simp only [dot2, Prod.fst_sub, Prod.snd_sub] at hmid_t ⊢; linarith
    rw [this, mul_zero]
  have hnz_plus : supportF P i (t + δ) - supportF P j (t + δ) ≠ 0 := by
    intro hzero
    have hd1 : dot2 (P.vec bi - P.vec bj) (gamma t) = 0 := by
      have hmid_t : supportF P i t - supportF P j t = 0 := by linarith
      rw [hbi_eq _ (Or.inr (Or.inl rfl)), hbj_eq _ (Or.inr (Or.inl rfl))] at hmid_t
      simp only [dot2, Prod.fst_sub, Prod.snd_sub] at hmid_t ⊢; linarith
    have hd2 : dot2 (P.vec bi - P.vec bj) (gamma (t + δ)) = 0 := by
      rw [hbi_eq _ (Or.inr (Or.inr rfl)), hbj_eq _ (Or.inr (Or.inr rfl))] at hzero
      simp only [dot2, Prod.fst_sub, Prod.snd_sub] at hzero ⊢; linarith
    have hdet_g : 0 < det2 (gamma t) (gamma (t + δ)) :=
      (gamma_det2_sign (le_of_lt ht0) (by linarith) (le_of_lt hδ_3)).1.mpr (by linarith)
    have hc1 := cramer_dot (P.vec bi - P.vec bj) (gamma t) (1, 0) (gamma (t + δ))
    have h_elim1 : (P.vec bi - P.vec bj).1 * det2 (gamma t) (gamma (t + δ)) =
        det2 (1, 0) (gamma (t + δ)) * dot2 (P.vec bi - P.vec bj) (gamma t) +
        det2 (gamma t) (1, 0) * dot2 (P.vec bi - P.vec bj) (gamma (t + δ)) := by
      rw [mul_comm]
      simpa [dot2] using hc1
    rw [hd1, hd2, mul_zero, mul_zero, add_zero] at h_elim1
    have hw1_zero : (P.vec bi - P.vec bj).1 = 0 :=
      (mul_eq_zero.mp h_elim1).resolve_right (ne_of_gt hdet_g)
    have hw1_eq : (P.vec bi).1 = (P.vec bj).1 := sub_eq_zero.mp hw1_zero
    exact (hgp.2.1 bi bj hbi_ne_bj).1 hw1_eq
  refine ⟨by linarith, hδ_3, ?_⟩
  have hneg : supportF P i (t - δ) - supportF P j (t - δ) =
      -(supportF P i (t + δ) - supportF P j (t + δ)) := by linarith
  rw [hneg]
  have hsq : 0 < (supportF P i (t + δ) - supportF P j (t + δ)) ^ 2 :=
    sq_pos_of_ne_zero hnz_plus
  nlinarith

private lemma posPairTies_ne_two_of_same_order (P : DualConfig) (hgp : IsGenPos P)
    (h_shat : ∀ m : Fin 5 → Bool, ∃ z : ℝ × ℝ, InOmega z ∧ RealizesDualMask P m z)
    {i j : Fin 5} (hij_ne : i ≠ j)
    (hL : leftKey P i < leftKey P j) (hR : rightKey P i < rightKey P j) :
    (posPairTies P i j).card ≠ 2 := by
  intro hcard2
  obtain ⟨a, b, hab_ne, hab_eq⟩ := Finset.card_eq_two.mp hcard2
  let t₁ := min a b
  let t₂ := max a b
  have ht12 : t₁ < t₂ := by
    rcases lt_or_gt_of_ne hab_ne with h | h
    · simp [t₁, t₂, le_of_lt h, h]
    · simp [t₁, t₂, le_of_lt h, h]
  have hset_eq : posPairTies P i j = {t₁, t₂} := by
    rw [hab_eq]
    rcases le_total a b with h | h
    · simp [t₁, t₂, h]
    · simp [t₁, t₂, h, Finset.pair_comm]
  have ht1_mem : t₁ ∈ posPairTies P i j := by rw [hset_eq]; simp
  have ht2_mem : t₂ ∈ posPairTies P i j := by rw [hset_eq]; simp
  obtain ⟨t_L, htL0, htL3, htLi, htL_lt, htL_all⟩ := left_dom_of_leftKey_lt P hgp h_shat hL
  obtain ⟨t_R, htR0, htR3, htRj, htR_lt, htR_all⟩ := right_dom_of_rightKey_lt P hgp h_shat hR
  have htL_t1 : t_L < t₁ := htL_all t₁ ht1_mem
  have ht2_tR : t₂ < t_R := htR_all t₂ ht2_mem
  obtain ⟨ε₁, hε₁_pos, hopp1⟩ := sign_change_at_posPairTie P hgp hij_ne ht1_mem
  obtain ⟨ε₂, hε₂_pos, hopp2⟩ := sign_change_at_posPairTie P hgp hij_ne ht2_mem
  have hpi := posInterval_eq_Ioo P hgp i
  have hpj := posInterval_eq_Ioo P hgp j
  have ht1_pos_ij : 0 < supportF P i t₁ ∧ 0 < supportF P j t₁ := by
    have hm := ht1_mem; simp only [posPairTies, Finset.mem_filter] at hm
    exact ⟨hm.2.2.2.2, hm.2.2.2.1 ▸ hm.2.2.2.2⟩
  have ht2_pos_ij : 0 < supportF P i t₂ ∧ 0 < supportF P j t₂ := by
    have hm := ht2_mem; simp only [posPairTies, Finset.mem_filter] at hm
    exact ⟨hm.2.2.2.2, hm.2.2.2.1 ▸ hm.2.2.2.2⟩
  have htL_in_i : posLeft P i < t_L ∧ t_L < posRight P i :=
    (hpi.2.2.2.2 t_L).mp ⟨htL0, htL3, htLi⟩
  have ht1_in_i : posLeft P i < t₁ ∧ t₁ < posRight P i :=
    (hpi.2.2.2.2 t₁).mp ⟨(lt_trans htL0 htL_t1), (lt_trans ht12 (lt_trans ht2_tR htR3)), ht1_pos_ij.1⟩
  have ht2_in_i : posLeft P i < t₂ ∧ t₂ < posRight P i :=
    (hpi.2.2.2.2 t₂).mp ⟨(lt_trans htL0 (lt_trans htL_t1 ht12)), (lt_trans ht2_tR htR3), ht2_pos_ij.1⟩
  have ht2_in_j : posLeft P j < t₂ ∧ t₂ < posRight P j :=
    (hpj.2.2.2.2 t₂).mp ⟨(lt_trans htL0 (lt_trans htL_t1 ht12)), (lt_trans ht2_tR htR3), ht2_pos_ij.2⟩
  have htR_in_j : posLeft P j < t_R ∧ t_R < posRight P j :=
    (hpj.2.2.2.2 t_R).mp ⟨htR0, htR3, htRj⟩
  let f : ℝ → ℝ := fun t => supportF P i t - supportF P j t
  have hf_cont : Continuous f := (supportF_continuous P i).sub (supportF_continuous P j)
  have h_no_zero_L : ∀ s ∈ Set.Ico t_L t₁, f s ≠ 0 := by
    intro s ⟨hsL, hs1⟩ hzero
    have hs0 : 0 < s := lt_of_lt_of_le htL0 hsL
    have hs3 : s < 3 := lt_trans hs1 (lt_trans ht12 (lt_trans ht2_tR htR3))
    have hfi : 0 < supportF P i s :=
      ((hpi.2.2.2.2 s).mpr ⟨lt_of_lt_of_le htL_in_i.1 hsL, lt_trans hs1 ht1_in_i.2⟩).2.2
    have hs_mem : s ∈ posPairTies P i j := by
      simp only [posPairTies, Finset.mem_filter]
      exact ⟨candTieGrid_mem_of_tie P hgp hs0 hs3 hij_ne (by linarith), hs0, hs3, by linarith, hfi⟩
    rw [hset_eq] at hs_mem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hs_mem
    rcases hs_mem with rfl | rfl <;> linarith
  have h_no_zero_M : ∀ s ∈ Set.Ioo t₁ t₂, f s ≠ 0 := by
    intro s ⟨hs1, hs2⟩ hzero
    have hs0 : 0 < s := lt_trans (lt_trans htL0 htL_t1) hs1
    have hs3 : s < 3 := lt_trans hs2 (lt_trans ht2_tR htR3)
    have hfi : 0 < supportF P i s :=
      ((hpi.2.2.2.2 s).mpr ⟨lt_trans ht1_in_i.1 hs1, lt_trans hs2 ht2_in_i.2⟩).2.2
    have hs_mem : s ∈ posPairTies P i j := by
      simp only [posPairTies, Finset.mem_filter]
      exact ⟨candTieGrid_mem_of_tie P hgp hs0 hs3 hij_ne (by linarith), hs0, hs3, by linarith, hfi⟩
    rw [hset_eq] at hs_mem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hs_mem
    rcases hs_mem with rfl | rfl <;> linarith
  have h_no_zero_R : ∀ s ∈ Set.Ioc t₂ t_R, f s ≠ 0 := by
    intro s ⟨hs2, hsR⟩ hzero
    have hs0 : 0 < s := lt_trans (lt_trans htL0 (lt_trans htL_t1 ht12)) hs2
    have hs3 : s < 3 := lt_of_le_of_lt hsR htR3
    have hfj : 0 < supportF P j s :=
      ((hpj.2.2.2.2 s).mpr ⟨lt_trans ht2_in_j.1 hs2, lt_of_le_of_lt hsR htR_in_j.2⟩).2.2
    have hs_mem : s ∈ posPairTies P i j := by
      simp only [posPairTies, Finset.mem_filter]
      exact ⟨candTieGrid_mem_of_tie P hgp hs0 hs3 hij_ne (by linarith), hs0, hs3, by linarith, by linarith⟩
    rw [hset_eq] at hs_mem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hs_mem
    rcases hs_mem with rfl | rfl <;> linarith
  let δ₁ : ℝ := min ε₁ (min ((t₁ - t_L) / 3) ((t₂ - t₁) / 3))
  let δ₂ : ℝ := min ε₂ (min ((t₂ - t₁) / 3) ((t_R - t₂) / 3))
  have hδ₁_pos : 0 < δ₁ := lt_min hε₁_pos (lt_min (by linarith) (by linarith))
  have hδ₂_pos : 0 < δ₂ := lt_min hε₂_pos (lt_min (by linarith) (by linarith))
  have hδ₁_le : δ₁ ≤ ε₁ := min_le_left _ _
  have hδ₂_le : δ₂ ≤ ε₂ := min_le_left _ _
  have hδ₁_L : t_L < t₁ - δ₁ := by
    have : δ₁ ≤ (t₁ - t_L) / 3 := le_trans (min_le_right _ _) (min_le_left _ _)
    linarith
  have hδ₁_M : t₁ + δ₁ < t₂ - δ₂ := by
    have h1 : δ₁ ≤ (t₂ - t₁) / 3 := le_trans (min_le_right _ _) (min_le_right _ _)
    have h2 : δ₂ ≤ (t₂ - t₁) / 3 := le_trans (min_le_right _ _) (min_le_left _ _)
    linarith
  have hδ₂_R : t₂ + δ₂ < t_R := by
    have : δ₂ ≤ (t_R - t₂) / 3 := le_trans (min_le_right _ _) (min_le_right _ _)
    linarith
  have hpos_L : 0 < f (t₁ - δ₁) := by
    by_contra hle
    replace hle : f (t₁ - δ₁) ≤ 0 := not_lt.mp hle
    have hf_tL : 0 < f t_L := by dsimp [f]; linarith
    obtain ⟨u, hu, hu_eq⟩ := intermediate_value_Icc' (le_of_lt hδ₁_L) hf_cont.continuousOn
      (⟨hle, le_of_lt hf_tL⟩ : (0 : ℝ) ∈ Set.Icc (f (t₁ - δ₁)) (f t_L))
    exact h_no_zero_L u ⟨hu.1, lt_of_le_of_lt hu.2 (by linarith)⟩ hu_eq
  have hneg_1p : f (t₁ + δ₁) < 0 := by
    obtain ⟨_, _, hprod⟩ := hopp1 δ₁ hδ₁_pos hδ₁_le
    change f (t₁ - δ₁) * f (t₁ + δ₁) < 0 at hprod
    exact lt_of_not_ge fun hge => absurd hprod (not_lt.mpr (mul_nonneg (le_of_lt hpos_L) hge))
  have hneg_2m : f (t₂ - δ₂) < 0 := by
    by_contra hge
    replace hge : 0 ≤ f (t₂ - δ₂) := not_lt.mp hge
    obtain ⟨u, hu, hu_eq⟩ := intermediate_value_Icc (le_of_lt hδ₁_M) hf_cont.continuousOn
      (⟨le_of_lt hneg_1p, hge⟩ : (0 : ℝ) ∈ Set.Icc (f (t₁ + δ₁)) (f (t₂ - δ₂)))
    exact h_no_zero_M u ⟨lt_of_lt_of_le (by linarith) hu.1, lt_of_le_of_lt hu.2 (by linarith)⟩ hu_eq
  have hpos_2p : 0 < f (t₂ + δ₂) := by
    obtain ⟨_, _, hprod⟩ := hopp2 δ₂ hδ₂_pos hδ₂_le
    change f (t₂ - δ₂) * f (t₂ + δ₂) < 0 at hprod
    exact lt_of_not_ge fun hle => absurd hprod (not_lt.mpr (mul_nonneg_of_nonpos_of_nonpos (le_of_lt hneg_2m) hle))
  have hpos_R : 0 < f t_R := by
    by_contra hle
    replace hle : f t_R ≤ 0 := not_lt.mp hle
    obtain ⟨u, hu, hu_eq⟩ := intermediate_value_Icc' (le_of_lt hδ₂_R) hf_cont.continuousOn
      (⟨hle, le_of_lt hpos_2p⟩ : (0 : ℝ) ∈ Set.Icc (f t_R) (f (t₂ + δ₂)))
    exact h_no_zero_R u ⟨lt_of_lt_of_le (by linarith) hu.1, hu.2⟩ hu_eq
  have : f t_R < 0 := by dsimp [f]; linarith
  linarith

private lemma list5_eq {α : Type*} (l : List α) (hlen : l.length = 5) :
    l = [l[0]'(by omega), l[1]'(by omega), l[2]'(by omega), l[3]'(by omega), l[4]'(by omega)] := by
  refine List.ext_getElem (by simp [hlen]) fun i hi1 hi2 => ?_
  have hi5 : i < 5 := by omega
  interval_cases i <;> rfl

private lemma finset_sup'_eq_neg_inf' {ι : Type*} (S : Finset ι) (hS : S.Nonempty) (f : ι → ℝ) :
    S.sup' hS f = -S.inf' hS (fun i => -f i) := by
  refine le_antisymm ?_ ?_
  · refine Finset.sup'_le hS f fun i hi => ?_
    rw [le_neg]
    exact Finset.inf'_le (fun j => -f j) hi
  · rw [neg_le]
    refine Finset.le_inf' hS (fun j => -f j) fun i hi => ?_
    rw [neg_le_neg_iff]
    exact Finset.le_sup' f hi

private lemma continuous_finset_sup' {ι : Type*} (S : Finset ι) (hS : S.Nonempty)
    (f : ι → ℝ → ℝ) (hf : ∀ i ∈ S, Continuous (f i)) :
    Continuous (fun t => S.sup' hS (fun i => f i t)) := by
  simp_rw [finset_sup'_eq_neg_inf']
  exact (Continuous.finset_inf'_apply hS fun i hi => (hf i hi).neg).neg

private lemma rankTieSet_mem_of_cut_eq (P : DualConfig) (hgp : IsGenPos P)
    {q : ℕ} (hq1 : 1 ≤ q) (hq3 : q ≤ 3)
    (M : Finset (Fin 5)) (hM_card : M.card = q)
    {t : ℝ} (ht_rank : t ∈ rankInterval P q)
    (hM_ne : M.Nonempty) (hMc_ne : (Finset.univ \ M).Nonempty)
    (heq : M.sup' hM_ne (fun u => clippedG P u t) =
           (Finset.univ \ M).inf' hMc_ne (fun v => clippedG P v t)) :
    t ∈ rankTieSet P q := by
  let c : ℝ := M.sup' hM_ne (fun u => clippedG P u t)
  obtain ⟨u, huM, hueq⟩ := Finset.exists_mem_eq_sup' hM_ne (fun u => clippedG P u t)
  obtain ⟨v, hvMc, hveq⟩ := Finset.exists_mem_eq_inf' hMc_ne (fun v => clippedG P v t)
  have huv : u ≠ v := fun h => by
    rw [h] at huM
    exact (Finset.mem_sdiff.mp hvMc).2 huM
  have hu_eq : clippedG P u t = c := hueq.symm
  have hv_eq : clippedG P v t = c := by change (Finset.univ \ M).inf' hMc_ne (fun v => clippedG P v t) = clippedG P v t at hveq; linarith
  have hle_M : ∀ x ∈ M, clippedG P x t ≤ c := fun x hx => Finset.le_sup' (fun u => clippedG P u t) hx
  have hge_Mc : ∀ y ∈ Finset.univ \ M, c ≤ clippedG P y t := fun y hy => by
    change M.sup' hM_ne (fun u => clippedG P u t) ≤ clippedG P y t
    rw [heq]
    exact Finset.inf'_le (fun v => clippedG P v t) hy
  let l₀ : List ℝ := List.ofFn (fun i : Fin 5 => clippedG P i t)
  let l : List ℝ := l₀.mergeSort (· ≤ ·)
  have hperm : l.Perm l₀ := List.mergeSort_perm l₀ _
  have hpw : l.Pairwise (· ≤ ·) := List.pairwise_mergeSort' (· ≤ ·) l₀
  have hlen : l.length = 5 := by rw [hperm.length_eq]; simp [l₀]
  have hl5 := list5_eq l hlen
  have hq5 : q < 5 := by omega
  have hget_eq : ∀ k : Fin 5, sortedG P k t = l[k.val]'(by omega) := by
    intro k; unfold sortedG
    change l.getD k.val 0 = l[k.val]'(by omega)
    simp [List.getD_eq_getElem?_getD, hlen]
  have hq_sort : sortedG P ⟨q, hq5⟩ t = l[q]'(by omega) := hget_eq ⟨q, hq5⟩
  have hqm1_sort : sortedG P ⟨q - 1, by omega⟩ t = l[q - 1]'(by omega) := hget_eq ⟨q - 1, by omega⟩
  have h_lq_le : l[q]'(by omega) ≤ c := by
    by_contra hgt
    replace hgt : c < l[q]'(by omega) := not_le.mp hgt
    have hp_ge : q + 1 ≤ l₀.countP (fun x => decide (x ≤ c)) := by
      dsimp [l₀]; rw [List.ofFn_eq_map, List.countP_map]
      let p : Fin 5 → Bool := (fun x => decide (x ≤ c)) ∘ (fun i => clippedG P i t)
      change q + 1 ≤ (List.finRange 5).countP p
      rw [List.countP_eq_length_filter]
      have hnd : ((List.finRange 5).filter p).Nodup := (List.nodup_finRange 5).filter _
      rw [← List.toFinset_card_of_nodup hnd]
      have hsub : insert v M ⊆ ((List.finRange 5).filter p).toFinset := by
        intro x hx
        simp only [List.mem_toFinset, List.mem_filter, List.mem_finRange, true_and, p,
          Function.comp_apply, decide_eq_true_eq]
        rcases Finset.mem_insert.mp hx with rfl | hxM
        · exact le_of_eq hv_eq
        · exact hle_M x hxM
      have hv_notM : v ∉ M := (Finset.mem_sdiff.mp hvMc).2
      calc q + 1 = M.card + 1 := by rw [hM_card]
        _ = (insert v M).card := (Finset.card_insert_of_notMem hv_notM).symm
        _ ≤ _ := Finset.card_le_card hsub
    have h_l_le : l.countP (fun x => decide (x ≤ c)) ≤ q := by
      have hge_q : ∀ (m : ℕ) (hqm : q ≤ m) (hm5 : m < 5), ¬ (l[m]'(by omega) ≤ c) := by
        intro m hqm hm5
        rcases eq_or_lt_of_le hqm with rfl | hlt_qm
        · exact not_le.mpr hgt
        · exact not_le.mpr (lt_of_lt_of_le hgt (List.pairwise_iff_getElem.mp hpw q m (by omega) (by omega) hlt_qm))
      rw [hl5]
      rcases (show q = 1 ∨ q = 2 ∨ q = 3 by omega) with rfl | rfl | rfl
      · have h1 := hge_q 1 (by omega) (by omega)
        have h2 := hge_q 2 (by omega) (by omega)
        have h3 := hge_q 3 (by omega) (by omega)
        have h4 := hge_q 4 (by omega) (by omega)
        simp only [List.countP_cons, List.countP_nil, decide_eq_true_eq, h1, h2, h3, h4, ↓reduceIte, add_zero]
        split_ifs <;> omega
      · have h2 := hge_q 2 (by omega) (by omega)
        have h3 := hge_q 3 (by omega) (by omega)
        have h4 := hge_q 4 (by omega) (by omega)
        simp only [List.countP_cons, List.countP_nil, decide_eq_true_eq, h2, h3, h4, ↓reduceIte, add_zero]
        split_ifs <;> omega
      · have h3 := hge_q 3 (by omega) (by omega)
        have h4 := hge_q 4 (by omega) (by omega)
        simp only [List.countP_cons, List.countP_nil, decide_eq_true_eq, h3, h4, ↓reduceIte, add_zero]
        split_ifs <;> omega
    rw [← hperm.countP_eq] at hp_ge
    omega
  have h_c_le_qm1 : c ≤ l[q - 1]'(by omega) := by
    by_contra hlt
    replace hlt : l[q - 1]'(by omega) < c := not_le.mp hlt
    have hp_ge : (5 - q) + 1 ≤ l₀.countP (fun x => decide (c ≤ x)) := by
      dsimp [l₀]; rw [List.ofFn_eq_map, List.countP_map]
      let p : Fin 5 → Bool := (fun x => decide (c ≤ x)) ∘ (fun i => clippedG P i t)
      change (5 - q) + 1 ≤ (List.finRange 5).countP p
      rw [List.countP_eq_length_filter]
      have hnd : ((List.finRange 5).filter p).Nodup := (List.nodup_finRange 5).filter _
      rw [← List.toFinset_card_of_nodup hnd]
      have hsub : insert u (Finset.univ \ M) ⊆ ((List.finRange 5).filter p).toFinset := by
        intro x hx
        simp only [List.mem_toFinset, List.mem_filter, List.mem_finRange, true_and, p,
          Function.comp_apply, decide_eq_true_eq]
        rcases Finset.mem_insert.mp hx with rfl | hxMc
        · exact le_of_eq hu_eq.symm
        · exact hge_Mc x hxMc
      have hu_notMc : u ∉ Finset.univ \ M := fun h => (Finset.mem_sdiff.mp h).2 huM
      have hMc_card : (Finset.univ \ M).card = 5 - q := by
        simp [Finset.card_sdiff, hM_card]
      calc (5 - q) + 1 = (Finset.univ \ M).card + 1 := by rw [hMc_card]
        _ = (insert u (Finset.univ \ M)).card := (Finset.card_insert_of_notMem hu_notMc).symm
        _ ≤ _ := Finset.card_le_card hsub
    have h_l_le : l.countP (fun x => decide (c ≤ x)) ≤ 5 - q := by
      have hlt_q : ∀ (m : ℕ) (hmq : m ≤ q - 1), ¬ (c ≤ l[m]'(by omega)) := by
        intro m hmq
        rcases eq_or_lt_of_le hmq with rfl | hlt_mq
        · exact not_le.mpr hlt
        · exact not_le.mpr (lt_of_le_of_lt (List.pairwise_iff_getElem.mp hpw m (q - 1) (by omega) (by omega) hlt_mq) hlt)
      rw [hl5]
      rcases (show q = 1 ∨ q = 2 ∨ q = 3 by omega) with rfl | rfl | rfl
      · have h0 := hlt_q 0 (by omega)
        simp only [List.countP_cons, List.countP_nil, decide_eq_true_eq, h0, ↓reduceIte, zero_add]
        split_ifs <;> omega
      · have h0 := hlt_q 0 (by omega)
        have h1 := hlt_q 1 (by omega)
        simp only [List.countP_cons, List.countP_nil, decide_eq_true_eq, h0, h1, ↓reduceIte, zero_add]
        split_ifs <;> omega
      · have h0 := hlt_q 0 (by omega)
        have h1 := hlt_q 1 (by omega)
        have h2 := hlt_q 2 (by omega)
        simp only [List.countP_cons, List.countP_nil, decide_eq_true_eq, h0, h1, h2, ↓reduceIte, zero_add]
        split_ifs <;> omega
    rw [← hperm.countP_eq] at hp_ge
    omega
  have h_qm1_le_q : l[q - 1]'(by omega) ≤ l[q]'(by omega) :=
    List.pairwise_iff_getElem.mp hpw (q - 1) q (by omega) (by omega) (by omega)
  have hs_eq : sortedG P ⟨q - 1, by omega⟩ t = sortedG P ⟨q, hq5⟩ t := by
    rw [hqm1_sort, hq_sort]
    linarith
  have hs_val : sortedG P ⟨q, hq5⟩ t = c := by rw [hq_sort]; linarith
  simp only [rankInterval, hq5, ↓reduceDIte, Set.mem_setOf_eq] at ht_rank
  rcases ht_rank with ⟨ht0, ht3, hts_pos⟩
  have hc_pos : 0 < c := by linarith
  have hfu_pos : 0 < supportF P u t := by
    by_contra hle; replace hle : supportF P u t ≤ 0 := not_lt.mp hle
    have : clippedG P u t = 0 := max_eq_right hle
    linarith
  have hfv_pos : 0 < supportF P v t := by
    by_contra hle; replace hle : supportF P v t ≤ 0 := not_lt.mp hle
    have : clippedG P v t = 0 := max_eq_right hle
    linarith
  have hf_tie : supportF P u t = supportF P v t := by
    unfold clippedG at hu_eq hv_eq
    rw [max_eq_left (le_of_lt hfu_pos)] at hu_eq
    rw [max_eq_left (le_of_lt hfv_pos)] at hv_eq
    linarith
  have ht_grid : t ∈ candTieGrid P := candTieGrid_mem_of_tie P hgp ht0 ht3 huv hf_tie
  have ht_all : t ∈ allPosTieSet P := by
    simp only [allPosTieSet, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and]
    rcases lt_or_gt_of_ne huv with hlt | hgt
    · refine ⟨(u, v), hlt, ?_⟩
      simp only [posPairTies, Finset.mem_filter]
      exact ⟨ht_grid, ht0, ht3, hf_tie, hfu_pos⟩
    · refine ⟨(v, u), hgt, ?_⟩
      simp only [posPairTies, Finset.mem_filter]
      exact ⟨ht_grid, ht0, ht3, hf_tie.symm, hfv_pos⟩
  simp only [rankTieSet, Finset.mem_filter, show 0 < q ∧ q < 5 by omega, ↓reduceDIte]
  exact ⟨ht_all, hts_pos, hs_eq⟩

/-- Two-sided `0 → >0 → 0` cut-potential split witness for `M`. -/
def cutSplitWitness (P : DualConfig) (M : Finset (Fin 5)) : Prop :=
  ∃ τ₁ τ₂ τ₃ : ℝ, 0 < τ₁ ∧ τ₁ < τ₂ ∧ τ₂ < τ₃ ∧ τ₃ < 3 ∧
    clippedCutPotential P M τ₁ = 0 ∧
    0 < clippedCutPotential P M τ₂ ∧
    clippedCutPotential P M τ₃ = 0

private lemma clippedCutPotential_swap (P : DualConfig) (M : Finset (Fin 5)) (t : ℝ) :
    clippedCutPotential P.swap M t = clippedCutPotential P M (3 - t) := by
  unfold clippedCutPotential clippedG
  congr 1; ext p
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_sdiff, Finset.mem_univ, true_and,
    supportF_swap_eq]

private lemma cutSplitWitness_swap (P : DualConfig) (M : Finset (Fin 5)) :
    cutSplitWitness P.swap M ↔ cutSplitWitness P M := by
  constructor
  · rintro ⟨τ₁, τ₂, τ₃, h0, h12, h23, h3, h1, h2, h3'⟩
    refine ⟨3 - τ₃, 3 - τ₂, 3 - τ₁, by linarith, by linarith, by linarith, by linarith, ?_, ?_, ?_⟩
    · simpa [clippedCutPotential_swap] using h3'
    · simpa [clippedCutPotential_swap] using h2
    · simpa [clippedCutPotential_swap] using h1
  · rintro ⟨τ₁, τ₂, τ₃, h0, h12, h23, h3, h1, h2, h3'⟩
    refine ⟨3 - τ₃, 3 - τ₂, 3 - τ₁, by linarith, by linarith, by linarith, by linarith, ?_, ?_, ?_⟩
    · rw [clippedCutPotential_swap]; simpa using h3'
    · rw [clippedCutPotential_swap]; simpa using h2
    · rw [clippedCutPotential_swap]; simpa using h1

private lemma clippedCutPotential_relabel (P : DualConfig) (τ : Equiv.Perm (Fin 5))
    (M : Finset (Fin 5)) (t : ℝ) :
    clippedCutPotential (P.relabel τ) M t = clippedCutPotential P (M.image τ) t := by
  unfold clippedCutPotential
  let e : Fin 5 × Fin 5 → Fin 5 × Fin 5 := fun p => (τ p.1, τ p.2)
  have he_inj : Function.Injective e := fun p₁ p₂ h =>
    Prod.ext (τ.injective (congrArg Prod.fst h)) (τ.injective (congrArg Prod.snd h))
  refine Finset.card_bij (fun p _ => e p) ?_ (fun p₁ _ p₂ _ h => he_inj h) ?_
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_sdiff, Finset.mem_univ, true_and,
      Finset.mem_image] at hp ⊢
    refine ⟨⟨⟨p.1, hp.1.1, rfl⟩, fun ⟨x, hxM, hxeq⟩ => hp.1.2 (τ.injective hxeq ▸ hxM)⟩, ?_⟩
    simpa [clippedG, supportF_relabel] using hp.2
  · intro q hq
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_sdiff, Finset.mem_univ, true_and,
      Finset.mem_image] at hq ⊢
    refine ⟨(τ.symm q.1, τ.symm q.2), ⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
    · obtain ⟨x, hxM, hxeq⟩ := hq.1.1
      rw [← hxeq, Equiv.symm_apply_apply]; exact hxM
    · intro hs
      apply hq.1.2
      exact ⟨τ.symm q.2, hs, Equiv.apply_symm_apply τ q.2⟩
    · change clippedG P (τ (τ.symm q.2)) t ≤ clippedG P (τ (τ.symm q.1)) t
      rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
      exact hq.2
    · ext <;> simp [e]

private lemma cutSplitWitness_relabel (P : DualConfig) (τ : Equiv.Perm (Fin 5))
    (M : Finset (Fin 5)) :
    cutSplitWitness (P.relabel τ) M ↔ cutSplitWitness P (M.image τ) := by
  simp only [cutSplitWitness, clippedCutPotential_relabel]

private lemma cut_zero_mem_rankInterval (P : DualConfig) (hgp : IsGenPos P)
    {q : ℕ} (hq1 : 1 ≤ q) (hq3 : q ≤ 3) (S : Finset (Fin 5)) (hS_card : S.card = q)
    {t : ℝ} (ht0 : 0 < t) (ht3 : t < 3) (hcut : clippedCutPotential P S t = 0) :
    t ∈ rankInterval P q := by
  have hlt : ∀ u ∈ S, ∀ v ∈ Finset.univ \ S, clippedG P u t < clippedG P v t := by
    intro u hu v hv
    by_contra hle
    have hpos : 0 < clippedCutPotential P S t := Finset.card_pos.mpr ⟨(u, v), by
      simp only [Finset.mem_filter, Finset.mem_product]
      exact ⟨⟨hu, hv⟩, not_lt.mp hle⟩⟩
    omega
  have hS_ne : S.Nonempty := Finset.card_pos.mp (by omega)
  have hSc_ne : (Finset.univ \ S).Nonempty := by
    rw [← Finset.card_pos]
    simp [Finset.card_sdiff, hS_card]
    omega
  obtain ⟨u₀, hu₀, hmax⟩ := Finset.exists_mem_eq_sup' hS_ne (fun u => clippedG P u t)
  let c : ℝ := S.sup' hS_ne (fun u => clippedG P u t)
  have hc_ge0 : 0 ≤ c := by
    have : 0 ≤ clippedG P u₀ t := le_max_right _ _
    exact le_trans this (Finset.le_sup' (fun u => clippedG P u t) hu₀)
  have hv_gt : ∀ v ∈ Finset.univ \ S, c < clippedG P v t := fun v hv =>
    Finset.sup'_lt_iff hS_ne |>.mpr fun u hu => hlt u hu v hv
  let l₀ : List ℝ := List.ofFn (fun i : Fin 5 => clippedG P i t)
  let l : List ℝ := l₀.mergeSort (· ≤ ·)
  have hperm : l.Perm l₀ := List.mergeSort_perm l₀ _
  have hpw : l.Pairwise (· ≤ ·) := List.pairwise_mergeSort' (· ≤ ·) l₀
  have hlen : l.length = 5 := by rw [hperm.length_eq]; simp [l₀]
  have hl5 := list5_eq l hlen
  have hq5 : q < 5 := by omega
  have h_gt_c : c < l[q]'(by omega) := by
    by_contra hle
    replace hle : l[q]'(by omega) ≤ c := not_lt.mp hle
    have hp_ge : q + 1 ≤ l.countP (fun x => decide (x ≤ c)) := by
      have h_le_q : ∀ (m : ℕ) (hmq : m ≤ q), l[m]'(by omega) ≤ c := by
        intro m hmq
        rcases eq_or_lt_of_le hmq with rfl | hlt_mq
        · exact hle
        · exact le_trans (List.pairwise_iff_getElem.mp hpw m q (by omega) (by omega) hlt_mq) hle
      rw [hl5]
      rcases (show q = 1 ∨ q = 2 ∨ q = 3 by omega) with rfl | rfl | rfl
      · have h0 := h_le_q 0 (by omega); have h1 := h_le_q 1 (by omega)
        simp only [List.countP_cons, List.countP_nil, decide_eq_true_eq, h0, h1, ↓reduceIte]
        omega
      · have h0 := h_le_q 0 (by omega); have h1 := h_le_q 1 (by omega); have h2 := h_le_q 2 (by omega)
        simp only [List.countP_cons, List.countP_nil, decide_eq_true_eq, h0, h1, h2, ↓reduceIte]
        omega
      · have h0 := h_le_q 0 (by omega); have h1 := h_le_q 1 (by omega)
        have h2 := h_le_q 2 (by omega); have h3 := h_le_q 3 (by omega)
        simp only [List.countP_cons, List.countP_nil, decide_eq_true_eq, h0, h1, h2, h3, ↓reduceIte]
        omega
    have hp_le : l₀.countP (fun x => decide (x ≤ c)) ≤ q := by
      dsimp [l₀]; rw [List.ofFn_eq_map, List.countP_map]
      let p : Fin 5 → Bool := (fun x => decide (x ≤ c)) ∘ (fun i => clippedG P i t)
      change (List.finRange 5).countP p ≤ q
      rw [List.countP_eq_length_filter]
      have hnd : ((List.finRange 5).filter p).Nodup := (List.nodup_finRange 5).filter _
      rw [← List.toFinset_card_of_nodup hnd]
      have hsub : ((List.finRange 5).filter p).toFinset ⊆ S := by
        intro x hx
        simp only [List.mem_toFinset, List.mem_filter, List.mem_finRange, true_and, p,
          Function.comp_apply, decide_eq_true_eq] at hx
        by_contra hxS
        have hgt_x := hv_gt x (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hxS⟩)
        linarith
      calc _ ≤ S.card := Finset.card_le_card hsub
        _ = q := hS_card
    rw [hperm.countP_eq] at hp_ge
    omega
  simp only [rankInterval, hq5, ↓reduceDIte, Set.mem_setOf_eq]
  refine ⟨ht0, ht3, ?_⟩
  have hq_sort : sortedG P ⟨q, hq5⟩ t = l[q]'(by omega) := by
    unfold sortedG
    change l.getD q 0 = l[q]'(by omega)
    have hql : q < l.length := by omega
    simp [List.getD_eq_getElem?_getD, hql]
  rw [hq_sort]
  linarith

private lemma sliceExcess_ge_card_of_cutSplitWitnesses (P : DualConfig) (hgp : IsGenPos P)
    (htop : ∀ {t : ℝ}, 0 ≤ t → t ≤ 3 → 0 < topEnv P t)
    (h_shat : ∀ m : Fin 5 → Bool, ∃ z : ℝ × ℝ, InOmega z ∧ RealizesDualMask P m z)
    {q : ℕ} (hq1 : 1 ≤ q) (hq3 : q ≤ 3)
    (ℱ : Finset (Finset (Fin 5)))
    (hF_card : ∀ M ∈ ℱ, M.card = q)
    (hF_split : ∀ M ∈ ℱ, cutSplitWitness P M) :
    (ℱ.card : ℤ) ≤ sliceExcess P q := by
  let 𝒜 : Finset (Finset (Fin 5)) := Finset.powersetCard q Finset.univ
  have h𝒜_card : 𝒜.card = Nat.choose 5 q := by simp [𝒜, Finset.card_powersetCard]
  have hF_sub : ℱ ⊆ 𝒜 := fun M hM =>
    Finset.mem_powersetCard.mpr ⟨Finset.subset_univ M, hF_card M hM⟩
  let idx : ℝ → ℕ := fun t => ((rankTieSet P q).filter (· < t)).card
  have hidx_lt : ∀ t : ℝ, idx t < (rankTieSet P q).card + 1 := fun t =>
    Nat.lt_succ_of_le (Finset.card_le_card (Finset.filter_subset _ _))
  have h_clip_cont : ∀ i : Fin 5, Continuous (fun t => clippedG P i t) := fun i =>
    (supportF_continuous P i).max continuous_const
  have hr_Ioo := rankInterval_eq_Ioo P hgp htop h_shat hq1 (by omega)
  have h_shat_cut : ∀ S ∈ 𝒜, ∃ t : ℝ, t ∈ rankInterval P q ∧ clippedCutPotential P S t = 0 := by
    intro S hS
    have hS_card : S.card = q := (Finset.mem_powersetCard.mp hS).2
    obtain ⟨z, hz_om, hz_mask⟩ := h_shat (fun i => decide (i ∈ S))
    let t := rayParam z
    have ht := rayParam_mem_Ioo hz_om
    have hnorm := inOmega_norm_pos hz_om
    have hrec := gamma_rayParam_smul hz_om
    let η : ℝ := 1 / (|z.1| + |z.2|)
    have hη_pos : 0 < η := div_pos one_pos hnorm
    have h_cut_zero : clippedCutPotential P S t = 0 := by
      unfold clippedCutPotential
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro p hp
      simp only [Finset.mem_product, Finset.mem_sdiff, Finset.mem_univ, true_and] at hp
      have hmu := hz_mask p.1
      simp only [decide_eq_true_eq, hp.1, ↓reduceIte, DualConfig.MemOpen] at hmu
      have h1 : dot2 (P.p1 p.1) (gamma t) < η := by
        dsimp [η, t]; rw [lt_div_iff₀ hnorm, mul_comm, ← dot2_smul_right, hrec]; exact hmu.1
      have h2 : dot2 (P.p2 p.1) (gamma t) < η := by
        dsimp [η, t]; rw [lt_div_iff₀ hnorm, mul_comm, ← dot2_smul_right, hrec]; exact hmu.2
      have hfu : supportF P p.1 t < η := max_lt h1 h2
      have hmv := hz_mask p.2
      simp only [decide_eq_false hp.2, Bool.false_eq_true, ↓reduceIte, DualConfig.MemExt] at hmv
      have hfv : η < supportF P p.2 t := by
        unfold supportF
        rcases hmv with hv1 | hv2
        · have : η < dot2 (P.p1 p.2) (gamma t) := by
            dsimp [η, t]; rw [div_lt_iff₀ hnorm, mul_comm, ← dot2_smul_right, hrec]; exact hv1
          exact lt_of_lt_of_le this (le_max_left _ _)
        · have : η < dot2 (P.p2 p.2) (gamma t) := by
            dsimp [η, t]; rw [div_lt_iff₀ hnorm, mul_comm, ← dot2_smul_right, hrec]; exact hv2
          exact lt_of_lt_of_le this (le_max_right _ _)
      have hgu : clippedG P p.1 t < η := max_lt hfu hη_pos
      have hgv : η < clippedG P p.2 t := lt_of_lt_of_le hfv (le_max_left _ _)
      exact not_le.mpr (lt_trans hgu hgv)
    exact ⟨t, cut_zero_mem_rankInterval P hgp hq1 hq3 S hS_card ht.1 ht.2 h_cut_zero, h_cut_zero⟩
  have h_sep : ∀ S₁ ∈ 𝒜, ∀ S₂ ∈ 𝒜, S₁ ≠ S₂ → ∀ t₁ t₂ : ℝ,
      t₁ ∈ rankInterval P q → t₂ ∈ rankInterval P q →
      clippedCutPotential P S₁ t₁ = 0 → clippedCutPotential P S₂ t₂ = 0 →
      idx t₁ ≠ idx t₂ := by
    intro S₁ hS₁ S₂ hS₂ hne t₁ t₂ ht₁_rk ht₂_rk hc₁ hc₂
    have hS₁_card : S₁.card = q := (Finset.mem_powersetCard.mp hS₁).2
    have hS₂_card : S₂.card = q := (Finset.mem_powersetCard.mp hS₂).2
    have h_diff1 : (S₁ \ S₂).Nonempty := by
      by_contra h_emp
      rw [Finset.not_nonempty_iff_eq_empty, Finset.sdiff_eq_empty_iff_subset] at h_emp
      exact hne (Finset.eq_of_subset_of_card_le h_emp (by rw [hS₁_card, hS₂_card]))
    have h_diff2 : (S₂ \ S₁).Nonempty := by
      by_contra h_emp
      rw [Finset.not_nonempty_iff_eq_empty, Finset.sdiff_eq_empty_iff_subset] at h_emp
      exact hne.symm (Finset.eq_of_subset_of_card_le h_emp (by rw [hS₁_card, hS₂_card]))
    obtain ⟨u₀, hu₀⟩ := h_diff1
    obtain ⟨v₀, hv₀⟩ := h_diff2
    rw [Finset.mem_sdiff] at hu₀ hv₀
    have hcut_lt : ∀ S : Finset (Fin 5), ∀ t : ℝ, clippedCutPotential P S t = 0 →
        ∀ u ∈ S, ∀ v ∉ S, clippedG P u t < clippedG P v t := by
      intro S t hc u hu v hv
      by_contra hle
      have hpos : 0 < clippedCutPotential P S t := Finset.card_pos.mpr ⟨(u, v), by
        simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_sdiff, Finset.mem_univ, true_and]
        exact ⟨⟨hu, hv⟩, not_lt.mp hle⟩⟩
      omega
    have ht1_lt : clippedG P u₀ t₁ < clippedG P v₀ t₁ := hcut_lt S₁ t₁ hc₁ u₀ hu₀.1 v₀ hv₀.2
    have ht2_lt : clippedG P v₀ t₂ < clippedG P u₀ t₂ := hcut_lt S₂ t₂ hc₂ v₀ hv₀.1 u₀ hu₀.2
    have ht_ne : t₁ ≠ t₂ := fun h => by rw [h] at ht1_lt; linarith
    have hS₁_ne : S₁.Nonempty := ⟨u₀, hu₀.1⟩
    have hS₁c_ne : (Finset.univ \ S₁).Nonempty := ⟨v₀, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hv₀.2⟩⟩
    let g : ℝ → ℝ := fun t => S₁.sup' hS₁_ne (fun u => clippedG P u t) -
        (Finset.univ \ S₁).inf' hS₁c_ne (fun v => clippedG P v t)
    have hg_cont : Continuous g :=
      (continuous_finset_sup' S₁ hS₁_ne (fun u => clippedG P u) fun u _ => h_clip_cont u).sub
        (Continuous.finset_inf'_apply hS₁c_ne fun v _ => h_clip_cont v)
    have hg1 : g t₁ < 0 := by
      dsimp [g]; rw [sub_neg, Finset.sup'_lt_iff hS₁_ne]
      intro u hu
      rw [Finset.lt_inf'_iff hS₁c_ne]
      intro v hv
      exact hcut_lt S₁ t₁ hc₁ u hu v (Finset.mem_sdiff.mp hv).2
    have hg2 : 0 < g t₂ := by
      dsimp [g]; rw [sub_pos]
      have h1 : (Finset.univ \ S₁).inf' hS₁c_ne (fun v => clippedG P v t₂) ≤ clippedG P v₀ t₂ :=
        Finset.inf'_le _ (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hv₀.2⟩)
      have h2 : clippedG P u₀ t₂ ≤ S₁.sup' hS₁_ne (fun u => clippedG P u t₂) :=
        Finset.le_sup' (fun u => clippedG P u t₂) hu₀.1
      linarith
    rw [hr_Ioo.2] at ht₁_rk ht₂_rk
    rcases lt_or_gt_of_ne ht_ne with h12 | h21
    · obtain ⟨x, hx_mem, hx_zero⟩ := intermediate_value_Ioo (le_of_lt h12) hg_cont.continuousOn
        (⟨hg1, hg2⟩ : (0 : ℝ) ∈ Set.Ioo (g t₁) (g t₂))
      have hx_rk : x ∈ rankInterval P q := by
        rw [hr_Ioo.2]
        exact ⟨lt_trans ht₁_rk.1 hx_mem.1, lt_trans hx_mem.2 ht₂_rk.2⟩
      have hx_eq : S₁.sup' hS₁_ne (fun u => clippedG P u x) =
          (Finset.univ \ S₁).inf' hS₁c_ne (fun v => clippedG P v x) := by
        dsimp [g] at hx_zero; linarith
      have hx_tie : x ∈ rankTieSet P q :=
        rankTieSet_mem_of_cut_eq P hgp hq1 hq3 S₁ hS₁_card hx_rk hS₁_ne hS₁c_ne hx_eq
      have hsub : (rankTieSet P q).filter (· < t₁) ⊂ (rankTieSet P q).filter (· < t₂) := by
        rw [Finset.ssubset_iff_of_subset]
        · exact ⟨x, Finset.mem_filter.mpr ⟨hx_tie, hx_mem.2⟩, fun h => by
            have := (Finset.mem_filter.mp h).2; linarith [hx_mem.1]⟩
        · intro y hy
          simp only [Finset.mem_filter] at hy ⊢
          exact ⟨hy.1, lt_trans hy.2 h12⟩
      exact ne_of_lt (Finset.card_lt_card hsub)
    · obtain ⟨x, hx_mem, hx_zero⟩ := intermediate_value_Ioo' (le_of_lt h21) hg_cont.continuousOn
        (⟨hg1, hg2⟩ : (0 : ℝ) ∈ Set.Ioo (g t₁) (g t₂))
      have hx_rk : x ∈ rankInterval P q := by
        rw [hr_Ioo.2]
        exact ⟨lt_trans ht₂_rk.1 hx_mem.1, lt_trans hx_mem.2 ht₁_rk.2⟩
      have hx_eq : S₁.sup' hS₁_ne (fun u => clippedG P u x) =
          (Finset.univ \ S₁).inf' hS₁c_ne (fun v => clippedG P v x) := by
        dsimp [g] at hx_zero; linarith
      have hx_tie : x ∈ rankTieSet P q :=
        rankTieSet_mem_of_cut_eq P hgp hq1 hq3 S₁ hS₁_card hx_rk hS₁_ne hS₁c_ne hx_eq
      have hsub : (rankTieSet P q).filter (· < t₂) ⊂ (rankTieSet P q).filter (· < t₁) := by
        rw [Finset.ssubset_iff_of_subset]
        · exact ⟨x, Finset.mem_filter.mpr ⟨hx_tie, hx_mem.2⟩, fun h => by
            have := (Finset.mem_filter.mp h).2; linarith [hx_mem.1]⟩
        · intro y hy
          simp only [Finset.mem_filter] at hy ⊢
          exact ⟨hy.1, lt_trans hy.2 h21⟩
      exact ne_of_gt (Finset.card_lt_card hsub)
  have h_two : ∀ M : Finset (Fin 5), M ∈ ℱ →
      ∃ p : ℝ × ℝ, p.1 ∈ rankInterval P q ∧ p.2 ∈ rankInterval P q ∧
        clippedCutPotential P M p.1 = 0 ∧ clippedCutPotential P M p.2 = 0 ∧
        idx p.1 ≠ idx p.2 := by
    intro M hM
    obtain ⟨τ₁, τ₂, τ₃, h0, h12, h23, h3, hc1, hc2, hc3⟩ := hF_split M hM
    have hM_card := hF_card M hM
    have hτ₁_rk := cut_zero_mem_rankInterval P hgp hq1 hq3 M hM_card h0 (lt_trans h12 (lt_trans h23 h3)) hc1
    have hτ₃_rk := cut_zero_mem_rankInterval P hgp hq1 hq3 M hM_card (lt_trans h0 (lt_trans h12 h23)) h3 hc3
    have hM_ne : M.Nonempty := Finset.card_pos.mp (by omega)
    have hMc_ne : (Finset.univ \ M).Nonempty := by
      rw [← Finset.card_pos]
      simp [Finset.card_sdiff, hM_card]; omega
    let g : ℝ → ℝ := fun t => M.sup' hM_ne (fun u => clippedG P u t) -
        (Finset.univ \ M).inf' hMc_ne (fun v => clippedG P v t)
    have hg_cont : Continuous g :=
      (continuous_finset_sup' M hM_ne (fun u => clippedG P u) fun u _ => h_clip_cont u).sub
        (Continuous.finset_inf'_apply hMc_ne fun v _ => h_clip_cont v)
    have hg1 : g τ₁ < 0 := by
      dsimp [g]; rw [sub_neg, Finset.sup'_lt_iff hM_ne]
      intro u hu; rw [Finset.lt_inf'_iff hMc_ne]; intro v hv
      by_contra hle
      have hpos : 0 < clippedCutPotential P M τ₁ := Finset.card_pos.mpr ⟨(u, v), by
        simp only [Finset.mem_filter, Finset.mem_product]; exact ⟨⟨hu, hv⟩, not_lt.mp hle⟩⟩
      omega
    have hg2 : 0 ≤ g τ₂ := by
      obtain ⟨p, hp⟩ := Finset.card_pos.mp hc2
      simp only [Finset.mem_filter, Finset.mem_product] at hp
      have h1 : (Finset.univ \ M).inf' hMc_ne (fun v => clippedG P v τ₂) ≤ clippedG P p.2 τ₂ :=
        Finset.inf'_le _ hp.1.2
      have h2 : clippedG P p.1 τ₂ ≤ M.sup' hM_ne (fun u => clippedG P u τ₂) :=
        Finset.le_sup' (fun u => clippedG P u τ₂) hp.1.1
      dsimp [g]; linarith [hp.2]
    obtain ⟨x, hx_mem, hx_zero⟩ := intermediate_value_Icc (le_of_lt h12) hg_cont.continuousOn
      (⟨le_of_lt hg1, hg2⟩ : (0 : ℝ) ∈ Set.Icc (g τ₁) (g τ₂))
    have hx_gt1 : τ₁ < x := by
      rcases eq_or_lt_of_le hx_mem.1 with rfl | hgt
      · linarith [hg1]
      · exact hgt
    have hx_lt3 : x < τ₃ := lt_of_le_of_lt hx_mem.2 h23
    have hτ₁_rk' := hτ₁_rk
    have hτ₃_rk' := hτ₃_rk
    rw [hr_Ioo.2] at hτ₁_rk' hτ₃_rk'
    have hx_rk : x ∈ rankInterval P q := by
      rw [hr_Ioo.2]; exact ⟨lt_trans hτ₁_rk'.1 hx_gt1, lt_trans hx_lt3 hτ₃_rk'.2⟩
    have hx_eq : M.sup' hM_ne (fun u => clippedG P u x) =
        (Finset.univ \ M).inf' hMc_ne (fun v => clippedG P v x) := by
      dsimp [g] at hx_zero; linarith
    have hx_tie : x ∈ rankTieSet P q :=
      rankTieSet_mem_of_cut_eq P hgp hq1 hq3 M hM_card hx_rk hM_ne hMc_ne hx_eq
    have hsub : (rankTieSet P q).filter (· < τ₁) ⊂ (rankTieSet P q).filter (· < τ₃) := by
      rw [Finset.ssubset_iff_of_subset]
      · exact ⟨x, Finset.mem_filter.mpr ⟨hx_tie, hx_lt3⟩, fun h => by
          have := (Finset.mem_filter.mp h).2; linarith⟩
      · intro y hy
        simp only [Finset.mem_filter] at hy ⊢
        exact ⟨hy.1, lt_trans hy.2 (lt_trans h12 h23)⟩
    exact ⟨(τ₁, τ₃), hτ₁_rk, hτ₃_rk, hc1, hc3, ne_of_lt (Finset.card_lt_card hsub)⟩
  let f₀ : Finset (Fin 5) → ℝ := fun S =>
    if h : S ∈ 𝒜 then Classical.choose (h_shat_cut S h) else 0
  let pF : Finset (Fin 5) → ℝ × ℝ := fun M =>
    if h : M ∈ ℱ then Classical.choose (h_two M h) else (0, 0)
  let ptOf : Finset (Fin 5) × Bool → ℝ := fun x =>
    if x.2 then (pF x.1).2
    else if x.1 ∈ ℱ then (pF x.1).1
    else f₀ x.1
  let 𝒟 : Finset (Finset (Fin 5) × Bool) :=
    (𝒜.image (fun S => (S, false))) ∪ (ℱ.image (fun M => (M, true)))
  have h𝒟_pt : ∀ x ∈ 𝒟, x.1 ∈ 𝒜 ∧ ptOf x ∈ rankInterval P q ∧ clippedCutPotential P x.1 (ptOf x) = 0 := by
    intro x hx
    simp only [𝒟, Finset.mem_union, Finset.mem_image] at hx
    rcases hx with ⟨S, hS, rfl⟩ | ⟨M, hM, rfl⟩
    · dsimp [ptOf]
      split_ifs with hMF
      · have hs := Classical.choose_spec (h_two S hMF)
        dsimp [pF]; rw [dif_pos hMF]
        exact ⟨hS, hs.1, hs.2.2.1⟩
      · have hs := Classical.choose_spec (h_shat_cut S hS)
        dsimp [f₀]; rw [dif_pos hS]
        exact ⟨hS, hs.1, hs.2⟩
    · dsimp [ptOf, pF]; simp only [dif_pos hM]
      have hs := Classical.choose_spec (h_two M hM)
      exact ⟨hF_sub hM, hs.2.1, hs.2.2.2.1⟩
  have hcard_D : 𝒟.card = Nat.choose 5 q + ℱ.card := by
    have hdisj : Disjoint (𝒜.image (fun S => (S, false))) (ℱ.image (fun M => (M, true))) := by
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      simp only [Finset.mem_image] at hx1 hx2
      obtain ⟨_, _, rfl⟩ := hx1
      obtain ⟨_, _, heq⟩ := hx2
      simp only [Prod.mk.injEq, Bool.true_eq_false, and_false] at heq
    rw [Finset.card_union_of_disjoint hdisj,
      Finset.card_image_of_injective _ (fun a b h => congrArg Prod.fst h),
      Finset.card_image_of_injective _ (fun a b h => congrArg Prod.fst h),
      h𝒜_card]
  have hinj : Set.InjOn (fun x => idx (ptOf x)) (𝒟 : Set (Finset (Fin 5) × Bool)) := by
    rintro ⟨S₁, b₁⟩ hx₁ ⟨S₂, b₂⟩ hx₂ heq
    rcases h𝒟_pt (S₁, b₁) hx₁ with ⟨h1A, h1rk, h1c⟩
    rcases h𝒟_pt (S₂, b₂) hx₂ with ⟨h2A, h2rk, h2c⟩
    by_cases hS : S₁ = S₂
    · subst hS
      by_cases hb : b₁ = b₂
      · subst hb; rfl
      · exfalso
        have hM : S₁ ∈ ℱ := by
          rcases Bool.dichotomy b₁ with rfl | rfl <;> rcases Bool.dichotomy b₂ with rfl | rfl
          · exact absurd rfl hb
          · simp only [𝒟, Finset.mem_coe, Finset.mem_union, Finset.mem_image] at hx₂
            rcases hx₂ with ⟨_, _, hq⟩ | ⟨M, hM, hq⟩
            · simp at hq
            · cases hq; exact hM
          · simp only [𝒟, Finset.mem_coe, Finset.mem_union, Finset.mem_image] at hx₁
            rcases hx₁ with ⟨_, _, hq⟩ | ⟨M, hM, hq⟩
            · simp at hq
            · cases hq; exact hM
          · exact absurd rfl hb
        have hspec := (Classical.choose_spec (h_two S₁ hM)).2.2.2.2
        rcases Bool.dichotomy b₁ with rfl | rfl <;> rcases Bool.dichotomy b₂ with rfl | rfl
        · exact absurd rfl hb
        · have hpt1 : ptOf (S₁, false) = (Classical.choose (h_two S₁ hM)).1 := by
            dsimp [ptOf, pF]; simp [hM]
          have hpt2 : ptOf (S₁, true) = (Classical.choose (h_two S₁ hM)).2 := by
            dsimp [ptOf, pF]; simp [hM]
          dsimp only at heq
          rw [hpt1, hpt2] at heq; exact hspec heq
        · have hpt1 : ptOf (S₁, true) = (Classical.choose (h_two S₁ hM)).2 := by
            dsimp [ptOf, pF]; simp [hM]
          have hpt2 : ptOf (S₁, false) = (Classical.choose (h_two S₁ hM)).1 := by
            dsimp [ptOf, pF]; simp [hM]
          dsimp only at heq
          rw [hpt1, hpt2] at heq; exact hspec heq.symm
        · exact absurd rfl hb
    · exact absurd heq (h_sep S₁ h1A S₂ h2A hS (ptOf (S₁, b₁)) (ptOf (S₂, b₂)) h1rk h2rk h1c h2c)
  have hle_range : 𝒟.card ≤ (Finset.range ((rankTieSet P q).card + 1)).card :=
    Finset.card_le_card_of_injOn (fun x => idx (ptOf x))
      (fun x _ => Finset.mem_range.mpr (hidx_lt (ptOf x))) hinj
  rw [hcard_D, Finset.card_range] at hle_range
  unfold sliceExcess
  omega

/-- `1`D slice separation criterion: `0 → >0 → 0` of `Φ_M^+` forces `Δ_{|M|} ≥ 1`. -/
theorem duplicate_slice_of_cutPotential (P : DualConfig) (hgp : IsGenPos P)
    (htop : ∀ {t : ℝ}, 0 ≤ t → t ≤ 3 → 0 < topEnv P t)
    (h_shat : ∀ m : Fin 5 → Bool, ∃ z : ℝ × ℝ, InOmega z ∧ RealizesDualMask P m z)
    (M : Finset (Fin 5)) (hM1 : 1 ≤ M.card) (hM3 : M.card ≤ 3)
    {τ₁ τ₂ τ₃ : ℝ} (h0 : 0 < τ₁) (h12 : τ₁ < τ₂) (h23 : τ₂ < τ₃) (h3 : τ₃ < 3)
    (hφ1 : clippedCutPotential P M τ₁ = 0)
    (hφ2 : 0 < clippedCutPotential P M τ₂)
    (hφ3 : clippedCutPotential P M τ₃ = 0) :
    1 ≤ sliceExcess P M.card := by
  have h := sliceExcess_ge_card_of_cutSplitWitnesses P hgp htop h_shat hM1 hM3 {M}
    (fun N hN => by rw [Finset.mem_singleton.mp hN])
    (fun N hN => by
      rw [Finset.mem_singleton.mp hN]
      exact ⟨τ₁, τ₂, τ₃, h0, h12, h23, h3, hφ1, hφ2, hφ3⟩)
  simpa using h

private lemma branch_pos_tie_unique (P : DualConfig) (hgp : IsGenPos P)
    {a b : Fin 10} (hab : a ≠ b) {t₁ t₂ : ℝ}
    (ht1_0 : 0 ≤ t₁) (ht1_3 : t₁ ≤ 3) (ht2_0 : 0 ≤ t₂) (ht2_3 : t₂ ≤ 3)
    (hpos1 : 0 < dot2 (P.vec a) (gamma t₁))
    (heq1 : dot2 (P.vec a) (gamma t₁) = dot2 (P.vec b) (gamma t₁))
    (hpos2 : 0 < dot2 (P.vec a) (gamma t₂))
    (heq2 : dot2 (P.vec a) (gamma t₂) = dot2 (P.vec b) (gamma t₂)) :
    t₁ = t₂ := by
  rcases lt_trichotomy t₁ t₂ with hlt | heq | hgt
  · exfalso
    have hdet_g : 0 < det2 (gamma t₁) (gamma t₂) :=
      (omega_pos_span ht1_0 hlt ht2_3 hpos1 hpos2 (Or.inl (P.vec_inOmega a))).2
    have hcb := cauchy_binet_two (P.vec a) (P.vec b) (gamma t₁) (gamma t₂)
    rw [heq1, heq2, mul_comm (dot2 (P.vec b) (gamma t₁)), sub_self] at hcb
    have hdet_ab := hgp.2.2.1 a b hab
    have : det2 (P.vec a) (P.vec b) * det2 (gamma t₁) (gamma t₂) = 0 := hcb.symm
    rcases mul_eq_zero.mp this with h | h
    · exact hdet_ab h
    · exact hdet_g.ne' h
  · exact heq
  · exfalso
    have hdet_g : 0 < det2 (gamma t₂) (gamma t₁) :=
      (omega_pos_span ht2_0 hgt ht1_3 hpos2 hpos1 (Or.inl (P.vec_inOmega a))).2
    have hcb := cauchy_binet_two (P.vec a) (P.vec b) (gamma t₂) (gamma t₁)
    rw [heq1, heq2, mul_comm (dot2 (P.vec b) (gamma t₂)), sub_self] at hcb
    have hdet_ab := hgp.2.2.1 a b hab
    have : det2 (P.vec a) (P.vec b) * det2 (gamma t₂) (gamma t₁) = 0 := hcb.symm
    rcases mul_eq_zero.mp this with h | h
    · exact hdet_ab h
    · exact hdet_g.ne' h

private lemma posPairTie_ne_apexRay (P : DualConfig) (hgp : IsGenPos P)
    {i j : Fin 5} (hij : i ≠ j) {t : ℝ} (ht : t ∈ posPairTies P i j) :
    t ≠ apexRay P i ∧ t ≠ apexRay P j := by
  simp only [posPairTies, Finset.mem_filter] at ht
  rcases ht with ⟨_, ht0, ht3, heq, _⟩
  have hvc_even : ∀ k : Fin 5, vecColor ⟨2 * k.val, by omega⟩ = k := by
    intro k; ext; dsimp [vecColor]; omega
  have hvc_odd : ∀ k : Fin 5, vecColor ⟨2 * k.val + 1, by omega⟩ = k := by
    intro k; ext; dsimp [vecColor]; omega
  have hrd := ray_ties_zeros_disjoint P hgp
  have hget_vec : ∀ k : Fin 5, ∃ a : Fin 10,
      vecColor a = k ∧ dot2 (P.vec a) (gamma t) = supportF P k t := by
    intro k; unfold supportF
    rcases max_choice (dot2 (P.p1 k) (gamma t)) (dot2 (P.p2 k) (gamma t)) with h | h
    · exact ⟨⟨2 * k.val, by omega⟩, hvc_even k, by rw [P.vec_even k, h]⟩
    · exact ⟨⟨2 * k.val + 1, by omega⟩, hvc_odd k, by rw [P.vec_odd k, h]⟩
  obtain ⟨ai, hai_col, hai_dot⟩ := hget_vec i
  obtain ⟨aj, haj_col, haj_dot⟩ := hget_vec j
  have hap_tie : ∀ k : Fin 5,
      dot2 (P.p1 k) (gamma (apexRay P k)) = dot2 (P.p2 k) (gamma (apexRay P k)) := by
    intro k
    obtain ⟨hq3, hd1, hd2, _⟩ := P.apex_spec k
    have hom : InOmega (P.apex k) := Or.inl hq3.1
    have hnorm := inOmega_norm_pos hom
    have hrec := gamma_rayParam_smul hom
    rw [← hrec, dot2_smul_right] at hd1 hd2
    have : (|(P.apex k).1| + |(P.apex k).2|) * dot2 (P.p1 k) (gamma (apexRay P k)) =
        (|(P.apex k).1| + |(P.apex k).2|) * dot2 (P.p2 k) (gamma (apexRay P k)) := by
      unfold apexRay; linarith
    exact mul_left_cancel₀ (ne_of_gt hnorm) this
  constructor
  · intro h; subst h
    let a1 : Fin 10 := ⟨2 * i.val, by omega⟩
    let a2 : Fin 10 := ⟨2 * i.val + 1, by omega⟩
    have ha12 : a1 < a2 := by show 2 * i.val < 2 * i.val + 1; omega
    have h12 : dot2 (P.vec a1) (gamma (apexRay P i)) = dot2 (P.vec a2) (gamma (apexRay P i)) := by
      rw [P.vec_even i, P.vec_odd i]; exact hap_tie i
    have h1_sup : dot2 (P.vec a1) (gamma (apexRay P i)) = supportF P i (apexRay P i) := by
      rw [P.vec_even i]; unfold supportF; rw [hap_tie i, max_self]
    have haij_ne : a1 ≠ aj := fun h => hij (by rw [← hvc_even i, ← haj_col, ← h])
    rcases lt_or_gt_of_ne haij_ne with hlt | hgt
    · have hpair_ne : (a1, a2) ≠ (a1, aj) := fun h => by
        have : a2 = aj := congrArg Prod.snd h
        exact hij (by rw [← hvc_odd i, ← haj_col, ← this])
      exact hrd.2.2.2 (apexRay P i) ht0 ht3 a1 a2 a1 aj ha12 hlt hpair_ne
        ⟨h12, by linarith [h1_sup, haj_dot, heq]⟩
    · have hpair_ne : (a1, a2) ≠ (aj, a1) := fun h => haij_ne (congrArg Prod.fst h)
      exact hrd.2.2.2 (apexRay P i) ht0 ht3 a1 a2 aj a1 ha12 hgt hpair_ne
        ⟨h12, by linarith [h1_sup, haj_dot, heq]⟩
  · intro h; subst h
    let b1 : Fin 10 := ⟨2 * j.val, by omega⟩
    let b2 : Fin 10 := ⟨2 * j.val + 1, by omega⟩
    have hb12 : b1 < b2 := by show 2 * j.val < 2 * j.val + 1; omega
    have h12 : dot2 (P.vec b1) (gamma (apexRay P j)) = dot2 (P.vec b2) (gamma (apexRay P j)) := by
      rw [P.vec_even j, P.vec_odd j]; exact hap_tie j
    have h1_sup : dot2 (P.vec b1) (gamma (apexRay P j)) = supportF P j (apexRay P j) := by
      rw [P.vec_even j]; unfold supportF; rw [hap_tie j, max_self]
    have hbij_ne : b1 ≠ ai := fun h => hij.symm (by rw [← hvc_even j, ← hai_col, ← h])
    rcases lt_or_gt_of_ne hbij_ne with hlt | hgt
    · have hpair_ne : (b1, b2) ≠ (b1, ai) := fun h => by
        have : b2 = ai := congrArg Prod.snd h
        exact hij.symm (by rw [← hvc_odd j, ← hai_col, ← this])
      exact hrd.2.2.2 (apexRay P j) ht0 ht3 b1 b2 b1 ai hb12 hlt hpair_ne
        ⟨h12, by linarith [h1_sup, hai_dot, heq]⟩
    · have hpair_ne : (b1, b2) ≠ (ai, b1) := fun h => hbij_ne (congrArg Prod.fst h)
      exact hrd.2.2.2 (apexRay P j) ht0 ht3 b1 b2 ai b1 hb12 hgt hpair_ne
        ⟨h12, by linarith [h1_sup, hai_dot, heq]⟩

/-- Characterization of `3`-crossing pairs `{i, j} ∈ E(G_3^+)` (`i < j`). -/
theorem three_crossing_structure (P : DualConfig) (hgp : IsGenPos P)
    (h_shat : ∀ m : Fin 5 → Bool, ∃ z : ℝ × ℝ, InOmega z ∧ RealizesDualMask P m z)
    (hleft : StrictMono (leftKey P)) {i j : Fin 5} (hij : (i, j) ∈ threeCrossGraph P) :
    posLeft P j < apexRay P i ∧
    apexRay P i < apexRay P j ∧
    apexRay P j < posRight P i ∧
    clippedG P i (apexRay P i) < clippedG P j (apexRay P i) ∧
    clippedG P j (apexRay P j) < clippedG P i (apexRay P j) ∧
    rayParam (P.p1 i) < rayParam (P.p1 j) ∧
    rayParam (P.p1 j) < rayParam (P.p2 i) ∧
    rayParam (P.p2 i) < rayParam (P.p2 j) := by
  simp only [threeCrossGraph, Finset.mem_filter, Finset.mem_univ, true_and] at hij
  rcases hij with ⟨hij_lt, hcard3⟩
  have hij_ne : i ≠ j := ne_of_lt hij_lt
  obtain ⟨t₁, t₂, t₃, ht12, ht23, ht1_mem, ht2_mem, ht3_mem, hmem_iff⟩ :
      ∃ t₁ t₂ t₃ : ℝ, t₁ < t₂ ∧ t₂ < t₃ ∧
        t₁ ∈ posPairTies P i j ∧ t₂ ∈ posPairTies P i j ∧ t₃ ∈ posPairTies P i j ∧
        ∀ t : ℝ, t ∈ posPairTies P i j ↔ t = t₁ ∨ t = t₂ ∨ t = t₃ := by
    let s : List ℝ := (posPairTies P i j).sort (· ≤ ·)
    have hs_len : s.length = 3 := by simp [s, Finset.length_sort, hcard3]
    have hs_pw : s.Pairwise (· < ·) := (posPairTies P i j).sortedLT_sort.pairwise
    refine ⟨s[0]'(by omega), s[1]'(by omega), s[2]'(by omega),
      List.pairwise_iff_getElem.mp hs_pw 0 1 (by omega) (by omega) (by omega),
      List.pairwise_iff_getElem.mp hs_pw 1 2 (by omega) (by omega) (by omega),
      (Finset.mem_sort _).mp (List.getElem_mem (by rw [hs_len]; omega)),
      (Finset.mem_sort _).mp (List.getElem_mem (by rw [hs_len]; omega)),
      (Finset.mem_sort _).mp (List.getElem_mem (by rw [hs_len]; omega)), ?_⟩
    have hs_eq : s = [s[0]'(by omega), s[1]'(by omega), s[2]'(by omega)] := by
      refine List.ext_getElem (by simp [hs_len]) fun m hm1 hm2 => ?_
      have hm3 : m < 3 := by omega
      interval_cases m <;> rfl
    intro t; rw [← Finset.mem_sort (· ≤ ·)]
    change t ∈ s ↔ _; conv_lhs => rw [hs_eq]
    simp
  have hsw := supportF_branch_switch P hgp
  have hap_ne : apexRay P i ≠ apexRay P j := hsw.1.ne hij_ne
  obtain ⟨A, B, hA_def, hB_def, hAB, hA1, hB2⟩ :
      ∃ A B : ℝ, A = min (apexRay P i) (apexRay P j) ∧ B = max (apexRay P i) (apexRay P j) ∧
        A < B ∧ 1 < A ∧ B < 2 := by
    refine ⟨min (apexRay P i) (apexRay P j), max (apexRay P i) (apexRay P j), rfl, rfl,
      lt_of_le_of_ne min_le_max ?_, lt_min (hsw.2 i).1 (hsw.2 j).1, max_lt (hsw.2 i).2.1 (hsw.2 j).2.1⟩
    rcases lt_or_gt_of_ne hap_ne with h | h
    · rw [min_eq_left h.le, max_eq_right h.le]; exact ne_of_lt h
    · rw [min_eq_right h.le, max_eq_left h.le]; exact ne_of_lt h
  have ht_ne_AB : ∀ t ∈ posPairTies P i j, t ≠ A ∧ t ≠ B := by
    intro t ht
    have hne := posPairTie_ne_apexRay P hgp hij_ne ht
    rcases lt_or_gt_of_ne hap_ne with h | h
    · rw [hA_def, hB_def, min_eq_left h.le, max_eq_right h.le]; exact hne
    · rw [hA_def, hB_def, min_eq_right h.le, max_eq_left h.le]; exact ⟨hne.2, hne.1⟩
  have h_uniq_L : ∀ a b : ℝ, a ∈ posPairTies P i j → b ∈ posPairTies P i j →
      a < A → b < A → a = b := by
    intro a b ha hb haA hbA
    have ha_f := Finset.mem_filter.mp ha
    have hb_f := Finset.mem_filter.mp hb
    have hap_i := (hsw.2 i).2.2.2.1
    have hap_j := (hsw.2 j).2.2.2.1
    have ha_i : supportF P i a = dot2 (P.p1 i) (gamma a) := by
      unfold supportF; exact max_eq_left (le_of_lt (hap_i a (le_of_lt ha_f.2.1) (lt_of_lt_of_le haA (hA_def ▸ min_le_left _ _))))
    have ha_j : supportF P j a = dot2 (P.p1 j) (gamma a) := by
      unfold supportF; exact max_eq_left (le_of_lt (hap_j a (le_of_lt ha_f.2.1) (lt_of_lt_of_le haA (hA_def ▸ min_le_right _ _))))
    have hb_i : supportF P i b = dot2 (P.p1 i) (gamma b) := by
      unfold supportF; exact max_eq_left (le_of_lt (hap_i b (le_of_lt hb_f.2.1) (lt_of_lt_of_le hbA (hA_def ▸ min_le_left _ _))))
    have hb_j : supportF P j b = dot2 (P.p1 j) (gamma b) := by
      unfold supportF; exact max_eq_left (le_of_lt (hap_j b (le_of_lt hb_f.2.1) (lt_of_lt_of_le hbA (hA_def ▸ min_le_right _ _))))
    let vi : Fin 10 := ⟨2 * i.val, by omega⟩
    let vj : Fin 10 := ⟨2 * j.val, by omega⟩
    have hv_ne : vi ≠ vj := fun h => hij_ne (Fin.ext (by
      have := congrArg Fin.val h; dsimp [vi, vj] at this; omega))
    refine branch_pos_tie_unique P hgp hv_ne (le_of_lt ha_f.2.1) (le_of_lt ha_f.2.2.1)
      (le_of_lt hb_f.2.1) (le_of_lt hb_f.2.2.1) ?_ ?_ ?_ ?_
    · rw [P.vec_even i, ← ha_i]; exact ha_f.2.2.2.2
    · rw [P.vec_even i, P.vec_even j, ← ha_i, ← ha_j]; exact ha_f.2.2.2.1
    · rw [P.vec_even i, ← hb_i]; exact hb_f.2.2.2.2
    · rw [P.vec_even i, P.vec_even j, ← hb_i, ← hb_j]; exact hb_f.2.2.2.1
  have h_uniq_R : ∀ a b : ℝ, a ∈ posPairTies P i j → b ∈ posPairTies P i j →
      B < a → B < b → a = b := by
    intro a b ha hb haB hbB
    have ha_f := Finset.mem_filter.mp ha
    have hb_f := Finset.mem_filter.mp hb
    have hap_i := (hsw.2 i).2.2.2.2
    have hap_j := (hsw.2 j).2.2.2.2
    have ha_i : supportF P i a = dot2 (P.p2 i) (gamma a) := by
      unfold supportF; exact max_eq_right (le_of_lt (hap_i a (lt_of_le_of_lt (hB_def ▸ le_max_left _ _) haB) (le_of_lt ha_f.2.2.1)))
    have ha_j : supportF P j a = dot2 (P.p2 j) (gamma a) := by
      unfold supportF; exact max_eq_right (le_of_lt (hap_j a (lt_of_le_of_lt (hB_def ▸ le_max_right _ _) haB) (le_of_lt ha_f.2.2.1)))
    have hb_i : supportF P i b = dot2 (P.p2 i) (gamma b) := by
      unfold supportF; exact max_eq_right (le_of_lt (hap_i b (lt_of_le_of_lt (hB_def ▸ le_max_left _ _) hbB) (le_of_lt hb_f.2.2.1)))
    have hb_j : supportF P j b = dot2 (P.p2 j) (gamma b) := by
      unfold supportF; exact max_eq_right (le_of_lt (hap_j b (lt_of_le_of_lt (hB_def ▸ le_max_right _ _) hbB) (le_of_lt hb_f.2.2.1)))
    let vi : Fin 10 := ⟨2 * i.val + 1, by omega⟩
    let vj : Fin 10 := ⟨2 * j.val + 1, by omega⟩
    have hv_ne : vi ≠ vj := fun h => hij_ne (Fin.ext (by
      have := congrArg Fin.val h; dsimp [vi, vj] at this; omega))
    refine branch_pos_tie_unique P hgp hv_ne (le_of_lt ha_f.2.1) (le_of_lt ha_f.2.2.1)
      (le_of_lt hb_f.2.1) (le_of_lt hb_f.2.2.1) ?_ ?_ ?_ ?_
    · rw [P.vec_odd i, ← ha_i]; exact ha_f.2.2.2.2
    · rw [P.vec_odd i, P.vec_odd j, ← ha_i, ← ha_j]; exact ha_f.2.2.2.1
    · rw [P.vec_odd i, ← hb_i]; exact hb_f.2.2.2.2
    · rw [P.vec_odd i, P.vec_odd j, ← hb_i, ← hb_j]; exact hb_f.2.2.2.1
  have h_uniq_M : ∀ a b : ℝ, a ∈ posPairTies P i j → b ∈ posPairTies P i j →
      A < a → a < B → A < b → b < B → a = b := by
    intro a b ha hb haA haB hbA hbB
    have ha_f := Finset.mem_filter.mp ha
    have hb_f := Finset.mem_filter.mp hb
    rcases lt_or_gt_of_ne hap_ne with h_ij | h_ji
    · have hA_eq : A = apexRay P i := hA_def.trans (min_eq_left (le_of_lt h_ij))
      have hB_eq : B = apexRay P j := hB_def.trans (max_eq_right (le_of_lt h_ij))
      have hap_i := (hsw.2 i).2.2.2.2
      have hap_j := (hsw.2 j).2.2.2.1
      have ha_i : supportF P i a = dot2 (P.p2 i) (gamma a) := by
        unfold supportF; exact max_eq_right (le_of_lt (hap_i a (hA_eq ▸ haA) (le_of_lt ha_f.2.2.1)))
      have ha_j : supportF P j a = dot2 (P.p1 j) (gamma a) := by
        unfold supportF; exact max_eq_left (le_of_lt (hap_j a (le_of_lt ha_f.2.1) (hB_eq ▸ haB)))
      have hb_i : supportF P i b = dot2 (P.p2 i) (gamma b) := by
        unfold supportF; exact max_eq_right (le_of_lt (hap_i b (hA_eq ▸ hbA) (le_of_lt hb_f.2.2.1)))
      have hb_j : supportF P j b = dot2 (P.p1 j) (gamma b) := by
        unfold supportF; exact max_eq_left (le_of_lt (hap_j b (le_of_lt hb_f.2.1) (hB_eq ▸ hbB)))
      let vi : Fin 10 := ⟨2 * i.val + 1, by omega⟩
      let vj : Fin 10 := ⟨2 * j.val, by omega⟩
      have hv_ne : vi ≠ vj := fun h => hij_ne (Fin.ext (by
        have := congrArg Fin.val h; dsimp [vi, vj] at this; omega))
      refine branch_pos_tie_unique P hgp hv_ne (le_of_lt ha_f.2.1) (le_of_lt ha_f.2.2.1)
        (le_of_lt hb_f.2.1) (le_of_lt hb_f.2.2.1) ?_ ?_ ?_ ?_
      · rw [P.vec_odd i, ← ha_i]; exact ha_f.2.2.2.2
      · rw [P.vec_odd i, P.vec_even j, ← ha_i, ← ha_j]; exact ha_f.2.2.2.1
      · rw [P.vec_odd i, ← hb_i]; exact hb_f.2.2.2.2
      · rw [P.vec_odd i, P.vec_even j, ← hb_i, ← hb_j]; exact hb_f.2.2.2.1
    · have hA_eq : A = apexRay P j := hA_def.trans (min_eq_right (le_of_lt h_ji))
      have hB_eq : B = apexRay P i := hB_def.trans (max_eq_left (le_of_lt h_ji))
      have hap_i := (hsw.2 i).2.2.2.1
      have hap_j := (hsw.2 j).2.2.2.2
      have ha_i : supportF P i a = dot2 (P.p1 i) (gamma a) := by
        unfold supportF; exact max_eq_left (le_of_lt (hap_i a (le_of_lt ha_f.2.1) (hB_eq ▸ haB)))
      have ha_j : supportF P j a = dot2 (P.p2 j) (gamma a) := by
        unfold supportF; exact max_eq_right (le_of_lt (hap_j a (hA_eq ▸ haA) (le_of_lt ha_f.2.2.1)))
      have hb_i : supportF P i b = dot2 (P.p1 i) (gamma b) := by
        unfold supportF; exact max_eq_left (le_of_lt (hap_i b (le_of_lt hb_f.2.1) (hB_eq ▸ hbB)))
      have hb_j : supportF P j b = dot2 (P.p2 j) (gamma b) := by
        unfold supportF; exact max_eq_right (le_of_lt (hap_j b (hA_eq ▸ hbA) (le_of_lt hb_f.2.2.1)))
      let vi : Fin 10 := ⟨2 * i.val, by omega⟩
      let vj : Fin 10 := ⟨2 * j.val + 1, by omega⟩
      have hv_ne : vi ≠ vj := fun h => hij_ne (Fin.ext (by
        have := congrArg Fin.val h; dsimp [vi, vj] at this; omega))
      refine branch_pos_tie_unique P hgp hv_ne (le_of_lt ha_f.2.1) (le_of_lt ha_f.2.2.1)
        (le_of_lt hb_f.2.1) (le_of_lt hb_f.2.2.1) ?_ ?_ ?_ ?_
      · rw [P.vec_even i, ← ha_i]; exact ha_f.2.2.2.2
      · rw [P.vec_even i, P.vec_odd j, ← ha_i, ← ha_j]; exact ha_f.2.2.2.1
      · rw [P.vec_even i, ← hb_i]; exact hb_f.2.2.2.2
      · rw [P.vec_even i, P.vec_odd j, ← hb_i, ← hb_j]; exact hb_f.2.2.2.1
  have ht1_A : t₁ < A := by
    by_contra hge
    have h1 : A < t₁ := lt_of_le_of_ne (not_lt.mp hge) (ht_ne_AB t₁ ht1_mem).1.symm
    have h2 : A < t₂ := lt_trans h1 ht12
    have h3 : A < t₃ := lt_trans h2 ht23
    rcases lt_or_gt_of_ne (ht_ne_AB t₂ ht2_mem).2 with ht2B | ht2B
    · have := h_uniq_M t₁ t₂ ht1_mem ht2_mem h1 (lt_trans ht12 ht2B) h2 ht2B; linarith
    · have := h_uniq_R t₂ t₃ ht2_mem ht3_mem ht2B (lt_trans ht2B ht23); linarith
  have ht2_A : A < t₂ := by
    by_contra hle
    have h2 : t₂ < A := lt_of_le_of_ne (not_lt.mp hle) (ht_ne_AB t₂ ht2_mem).1
    have := h_uniq_L t₁ t₂ ht1_mem ht2_mem ht1_A h2; linarith
  have ht2_B : t₂ < B := by
    by_contra hge
    have h2 : B < t₂ := lt_of_le_of_ne (not_lt.mp hge) (ht_ne_AB t₂ ht2_mem).2.symm
    have := h_uniq_R t₂ t₃ ht2_mem ht3_mem h2 (lt_trans h2 ht23); linarith
  have ht3_B : B < t₃ := by
    by_contra hle
    have h3 : t₃ < B := lt_of_le_of_ne (not_lt.mp hle) (ht_ne_AB t₃ ht3_mem).2
    have := h_uniq_M t₂ t₃ ht2_mem ht3_mem ht2_A ht2_B (lt_trans ht2_A ht23) h3; linarith
  -- Track signs of `f(t) = supportF P i t - supportF P j t`
  have hpi := posInterval_eq_Ioo P hgp i
  have hpj := posInterval_eq_Ioo P hgp j
  have ht1_f := Finset.mem_filter.mp ht1_mem
  have ht2_f := Finset.mem_filter.mp ht2_mem
  have ht3_f := Finset.mem_filter.mp ht3_mem
  have ht1_in_i : posLeft P i < t₁ ∧ t₁ < posRight P i :=
    (hpi.2.2.2.2 t₁).mp ⟨ht1_f.2.1, ht1_f.2.2.1, ht1_f.2.2.2.2⟩
  have ht1_in_j : posLeft P j < t₁ ∧ t₁ < posRight P j :=
    (hpj.2.2.2.2 t₁).mp ⟨ht1_f.2.1, ht1_f.2.2.1, ht1_f.2.2.2.1 ▸ ht1_f.2.2.2.2⟩
  have ht3_in_i : posLeft P i < t₃ ∧ t₃ < posRight P i :=
    (hpi.2.2.2.2 t₃).mp ⟨ht3_f.2.1, ht3_f.2.2.1, ht3_f.2.2.2.2⟩
  have ht3_in_j : posLeft P j < t₃ ∧ t₃ < posRight P j :=
    (hpj.2.2.2.2 t₃).mp ⟨ht3_f.2.1, ht3_f.2.2.1, ht3_f.2.2.2.1 ▸ ht3_f.2.2.2.2⟩
  obtain ⟨t_L, htL0, htL3, htLi, htL_lt, htL_all⟩ := left_dom_of_leftKey_lt P hgp h_shat (hleft hij_lt)
  have htL_t1 : t_L < t₁ := htL_all t₁ ht1_mem
  have htL_in_i : posLeft P i < t_L ∧ t_L < posRight P i :=
    (hpi.2.2.2.2 t_L).mp ⟨htL0, htL3, htLi⟩
  obtain ⟨ε₁, hε₁_pos, hopp1⟩ := sign_change_at_posPairTie P hgp hij_ne ht1_mem
  obtain ⟨ε₂, hε₂_pos, hopp2⟩ := sign_change_at_posPairTie P hgp hij_ne ht2_mem
  obtain ⟨ε₃, hε₃_pos, hopp3⟩ := sign_change_at_posPairTie P hgp hij_ne ht3_mem
  let f : ℝ → ℝ := fun t => supportF P i t - supportF P j t
  have hf_cont : Continuous f := (supportF_continuous P i).sub (supportF_continuous P j)
  have h_no_L : ∀ u ∈ Set.Ico t_L t₁, f u ≠ 0 := by
    intro u ⟨huL, hu1⟩ hzero
    have hu0 : 0 < u := lt_of_lt_of_le htL0 huL
    have hu3 : u < 3 := lt_trans hu1 ht1_f.2.2.1
    have hui : 0 < supportF P i u :=
      ((hpi.2.2.2.2 u).mpr ⟨lt_of_lt_of_le htL_in_i.1 huL, lt_trans hu1 ht1_in_i.2⟩).2.2
    have hu_mem : u ∈ posPairTies P i j := by
      simp only [posPairTies, Finset.mem_filter]
      exact ⟨candTieGrid_mem_of_tie P hgp hu0 hu3 hij_ne (by linarith), hu0, hu3, by linarith, hui⟩
    rw [hmem_iff] at hu_mem
    rcases hu_mem with rfl | rfl | rfl <;> linarith
  have h_no_12 : ∀ u ∈ Set.Ioo t₁ t₂, f u ≠ 0 := by
    intro u ⟨hu1, hu2⟩ hzero
    have hu0 : 0 < u := lt_trans ht1_f.2.1 hu1
    have hu3 : u < 3 := lt_trans hu2 ht2_f.2.2.1
    have hui : 0 < supportF P i u :=
      ((hpi.2.2.2.2 u).mpr ⟨lt_trans ht1_in_i.1 hu1, lt_trans (lt_trans hu2 ht23) ht3_in_i.2⟩).2.2
    have hu_mem : u ∈ posPairTies P i j := by
      simp only [posPairTies, Finset.mem_filter]
      exact ⟨candTieGrid_mem_of_tie P hgp hu0 hu3 hij_ne (by linarith), hu0, hu3, by linarith, hui⟩
    rw [hmem_iff] at hu_mem
    rcases hu_mem with rfl | rfl | rfl <;> linarith
  have h_no_23 : ∀ u ∈ Set.Ioo t₂ t₃, f u ≠ 0 := by
    intro u ⟨hu2, hu3_lt⟩ hzero
    have hu0 : 0 < u := lt_trans ht2_f.2.1 hu2
    have hu3 : u < 3 := lt_trans hu3_lt ht3_f.2.2.1
    have hui : 0 < supportF P i u :=
      ((hpi.2.2.2.2 u).mpr ⟨lt_trans ht1_in_i.1 (lt_trans ht12 hu2), lt_trans hu3_lt ht3_in_i.2⟩).2.2
    have hu_mem : u ∈ posPairTies P i j := by
      simp only [posPairTies, Finset.mem_filter]
      exact ⟨candTieGrid_mem_of_tie P hgp hu0 hu3 hij_ne (by linarith), hu0, hu3, by linarith, hui⟩
    rw [hmem_iff] at hu_mem
    rcases hu_mem with rfl | rfl | rfl <;> linarith
  obtain ⟨δ₁, hδ₁_pos, hδ₁_ε, hδ₁_L, hδ₁_A⟩ :
      ∃ δ₁ : ℝ, 0 < δ₁ ∧ δ₁ ≤ ε₁ ∧ t_L < t₁ - δ₁ ∧ t₁ + δ₁ < A := by
    refine ⟨min ε₁ (min ((t₁ - t_L) / 3) (min ((A - t₁) / 3) ((t₂ - t₁) / 3))),
      lt_min hε₁_pos (lt_min (by linarith) (lt_min (by linarith) (by linarith))),
      min_le_left _ _, ?_, ?_⟩
    · have : min ε₁ (min ((t₁ - t_L) / 3) (min ((A - t₁) / 3) ((t₂ - t₁) / 3))) ≤ (t₁ - t_L) / 3 :=
        le_trans (min_le_right _ _) (min_le_left _ _)
      linarith
    · have : min ε₁ (min ((t₁ - t_L) / 3) (min ((A - t₁) / 3) ((t₂ - t₁) / 3))) ≤ (A - t₁) / 3 :=
        le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
      linarith
  obtain ⟨δ₂, hδ₂_pos, hδ₂_ε, hδ₂_A, hδ₂_B⟩ :
      ∃ δ₂ : ℝ, 0 < δ₂ ∧ δ₂ ≤ ε₂ ∧ A < t₂ - δ₂ ∧ t₂ + δ₂ < B := by
    refine ⟨min ε₂ (min ((t₂ - A) / 3) ((B - t₂) / 3)),
      lt_min hε₂_pos (lt_min (by linarith) (by linarith)), min_le_left _ _, ?_, ?_⟩
    · have : min ε₂ (min ((t₂ - A) / 3) ((B - t₂) / 3)) ≤ (t₂ - A) / 3 :=
        le_trans (min_le_right _ _) (min_le_left _ _)
      linarith
    · have : min ε₂ (min ((t₂ - A) / 3) ((B - t₂) / 3)) ≤ (B - t₂) / 3 :=
        le_trans (min_le_right _ _) (min_le_right _ _)
      linarith
  obtain ⟨δ₃, hδ₃_pos, hδ₃_ε, hδ₃_B, hδ₃_Ri, hδ₃_Rj⟩ :
      ∃ δ₃ : ℝ, 0 < δ₃ ∧ δ₃ ≤ ε₃ ∧ B < t₃ - δ₃ ∧ t₃ + δ₃ < posRight P i ∧ t₃ + δ₃ < posRight P j := by
    refine ⟨min ε₃ (min ((t₃ - B) / 3) (min ((posRight P i - t₃) / 3) ((posRight P j - t₃) / 3))),
      lt_min hε₃_pos (lt_min (by linarith) (lt_min (by linarith) (by linarith))),
      min_le_left _ _, ?_, ?_, ?_⟩
    · have : min ε₃ (min ((t₃ - B) / 3) (min ((posRight P i - t₃) / 3) ((posRight P j - t₃) / 3))) ≤ (t₃ - B) / 3 :=
        le_trans (min_le_right _ _) (min_le_left _ _)
      linarith
    · have : min ε₃ (min ((t₃ - B) / 3) (min ((posRight P i - t₃) / 3) ((posRight P j - t₃) / 3))) ≤ (posRight P i - t₃) / 3 :=
        le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
      linarith
    · have : min ε₃ (min ((t₃ - B) / 3) (min ((posRight P i - t₃) / 3) ((posRight P j - t₃) / 3))) ≤ (posRight P j - t₃) / 3 :=
        le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
      linarith
  have hδ₁_2 : t₁ + δ₁ < t₂ - δ₂ := lt_trans hδ₁_A hδ₂_A
  have hδ₂_3 : t₂ + δ₂ < t₃ - δ₃ := lt_trans hδ₂_B hδ₃_B
  have hpos_1m : 0 < f (t₁ - δ₁) := by
    by_contra hle; replace hle : f (t₁ - δ₁) ≤ 0 := not_lt.mp hle
    have hf_tL : 0 < f t_L := by dsimp [f]; linarith
    obtain ⟨u, hu, hu_eq⟩ := intermediate_value_Icc' (le_of_lt hδ₁_L) hf_cont.continuousOn
      (⟨hle, le_of_lt hf_tL⟩ : (0 : ℝ) ∈ Set.Icc (f (t₁ - δ₁)) (f t_L))
    exact h_no_L u ⟨hu.1, lt_of_le_of_lt hu.2 (by linarith)⟩ hu_eq
  have hneg_1p : f (t₁ + δ₁) < 0 := by
    obtain ⟨_, _, hprod⟩ := hopp1 δ₁ hδ₁_pos hδ₁_ε
    change f (t₁ - δ₁) * f (t₁ + δ₁) < 0 at hprod
    exact lt_of_not_ge fun hge => absurd hprod (not_lt.mpr (mul_nonneg (le_of_lt hpos_1m) hge))
  have hneg_12 : ∀ s ∈ Set.Ioo t₁ t₂, f s < 0 := by
    intro s ⟨hs1, hs2⟩
    by_contra hge; replace hge : 0 ≤ f s := not_lt.mp hge
    rcases lt_or_ge (t₁ + δ₁) s with hlt | hle
    · obtain ⟨u, hu, hu_eq⟩ := intermediate_value_Icc (le_of_lt hlt) hf_cont.continuousOn
        (⟨le_of_lt hneg_1p, hge⟩ : (0 : ℝ) ∈ Set.Icc (f (t₁ + δ₁)) (f s))
      exact h_no_12 u ⟨lt_of_lt_of_le (by linarith) hu.1, lt_of_le_of_lt hu.2 hs2⟩ hu_eq
    · obtain ⟨u, hu, hu_eq⟩ := intermediate_value_Icc' hle hf_cont.continuousOn
        (⟨le_of_lt hneg_1p, hge⟩ : (0 : ℝ) ∈ Set.Icc (f (t₁ + δ₁)) (f s))
      exact h_no_12 u ⟨lt_of_lt_of_le hs1 hu.1, lt_of_le_of_lt hu.2 (lt_trans hδ₁_A ht2_A)⟩ hu_eq
  have hneg_2m : f (t₂ - δ₂) < 0 := hneg_12 (t₂ - δ₂) ⟨lt_trans (by linarith) hδ₁_2, by linarith⟩
  have hpos_2p : 0 < f (t₂ + δ₂) := by
    obtain ⟨_, _, hprod⟩ := hopp2 δ₂ hδ₂_pos hδ₂_ε
    change f (t₂ - δ₂) * f (t₂ + δ₂) < 0 at hprod
    exact lt_of_not_ge fun hle => absurd hprod (not_lt.mpr (mul_nonneg_of_nonpos_of_nonpos (le_of_lt hneg_2m) hle))
  have hpos_23 : ∀ s ∈ Set.Ioo t₂ t₃, 0 < f s := by
    intro s ⟨hs2, hs3⟩
    by_contra hle; replace hle : f s ≤ 0 := not_lt.mp hle
    rcases lt_or_ge (t₂ + δ₂) s with hlt | hle'
    · obtain ⟨u, hu, hu_eq⟩ := intermediate_value_Icc' (le_of_lt hlt) hf_cont.continuousOn
        (⟨hle, le_of_lt hpos_2p⟩ : (0 : ℝ) ∈ Set.Icc (f s) (f (t₂ + δ₂)))
      exact h_no_23 u ⟨lt_of_lt_of_le (by linarith) hu.1, lt_of_le_of_lt hu.2 hs3⟩ hu_eq
    · obtain ⟨u, hu, hu_eq⟩ := intermediate_value_Icc hle' hf_cont.continuousOn
        (⟨hle, le_of_lt hpos_2p⟩ : (0 : ℝ) ∈ Set.Icc (f s) (f (t₂ + δ₂)))
      exact h_no_23 u ⟨lt_of_lt_of_le hs2 hu.1, lt_of_le_of_lt hu.2 (lt_trans hδ₂_B ht3_B)⟩ hu_eq
  have hpos_3m : 0 < f (t₃ - δ₃) := hpos_23 (t₃ - δ₃) ⟨lt_trans (by linarith) hδ₂_3, by linarith⟩
  have hneg_3p : f (t₃ + δ₃) < 0 := by
    obtain ⟨_, _, hprod⟩ := hopp3 δ₃ hδ₃_pos hδ₃_ε
    change f (t₃ - δ₃) * f (t₃ + δ₃) < 0 at hprod
    exact lt_of_not_ge fun hge => absurd hprod (not_lt.mpr (mul_nonneg (le_of_lt hpos_3m) hge))
  have hr_p1 : rayParam (P.p1 i) < rayParam (P.p1 j) := by
    have h1 : dot2 (P.p1 i) (gamma t₁) = dot2 (P.p1 j) (gamma t₁) := by
      have hi1 := (hsw.2 i).2.2.2.1 t₁ (le_of_lt ht1_f.2.1) (lt_of_lt_of_le ht1_A (hA_def ▸ min_le_left _ _))
      have hj1 := (hsw.2 j).2.2.2.1 t₁ (le_of_lt ht1_f.2.1) (lt_of_lt_of_le ht1_A (hA_def ▸ min_le_right _ _))
      have ei : supportF P i t₁ = dot2 (P.p1 i) (gamma t₁) := max_eq_left (le_of_lt hi1)
      have ej : supportF P j t₁ = dot2 (P.p1 j) (gamma t₁) := max_eq_left (le_of_lt hj1)
      linarith [ht1_f.2.2.2.1]
    have hpos1 : 0 < dot2 (P.p1 i) (gamma t₁) := by
      have hi1 := (hsw.2 i).2.2.2.1 t₁ (le_of_lt ht1_f.2.1) (lt_of_lt_of_le ht1_A (hA_def ▸ min_le_left _ _))
      have ei : supportF P i t₁ = dot2 (P.p1 i) (gamma t₁) := max_eq_left (le_of_lt hi1)
      linarith [ht1_f.2.2.2.2]
    have h2 : dot2 (P.p1 i) (gamma (t₁ + δ₁)) < dot2 (P.p1 j) (gamma (t₁ + δ₁)) := by
      have hi1 := (hsw.2 i).2.2.2.1 (t₁ + δ₁) (by linarith [ht1_f.2.1]) (lt_of_lt_of_le hδ₁_A (hA_def ▸ min_le_left _ _))
      have hj1 := (hsw.2 j).2.2.2.1 (t₁ + δ₁) (by linarith [ht1_f.2.1]) (lt_of_lt_of_le hδ₁_A (hA_def ▸ min_le_right _ _))
      have ei : supportF P i (t₁ + δ₁) = dot2 (P.p1 i) (gamma (t₁ + δ₁)) := max_eq_left (le_of_lt hi1)
      have ej : supportF P j (t₁ + δ₁) = dot2 (P.p1 j) (gamma (t₁ + δ₁)) := max_eq_left (le_of_lt hj1)
      dsimp [f] at hneg_1p; linarith
    have hpos2 : 0 < dot2 (P.p1 j) (gamma (t₁ + δ₁)) := by
      have ht1d_in_j : posLeft P j < t₁ + δ₁ ∧ t₁ + δ₁ < posRight P j :=
        ⟨by linarith [ht1_in_j.1], lt_trans (lt_trans hδ₁_A (lt_trans hAB ht3_B)) ht3_in_j.2⟩
      have hj_pos := ((hpj.2.2.2.2 (t₁ + δ₁)).mpr ht1d_in_j).2.2
      have hj1 := (hsw.2 j).2.2.2.1 (t₁ + δ₁) (by linarith [ht1_f.2.1]) (lt_of_lt_of_le hδ₁_A (hA_def ▸ min_le_right _ _))
      have ej : supportF P j (t₁ + δ₁) = dot2 (P.p1 j) (gamma (t₁ + δ₁)) := max_eq_left (le_of_lt hj1)
      linarith
    have h1p_lt3 : t₁ + δ₁ ≤ 3 := by linarith [hδ₁_A, hAB, hB2]
    exact (rayParam_lt_of_pos_tie (P.vec_inOmega ⟨2 * i.val, by omega⟩ |> fun h => by rwa [P.vec_even i] at h)
      (P.vec_inOmega ⟨2 * j.val, by omega⟩ |> fun h => by rwa [P.vec_even j] at h)
      (le_of_lt ht1_f.2.1) (le_of_lt ht1_f.2.2.1) (by linarith [ht1_f.2.1]) h1p_lt3
      h1 hpos1 (Or.inl ⟨by linarith, h2, hpos2⟩)).2
  have hap_ij : apexRay P i < apexRay P j := by
    by_contra hle
    have hji : apexRay P j < apexRay P i := lt_of_le_of_ne (not_lt.mp hle) hap_ne.symm
    have hA_eq : A = apexRay P j := hA_def.trans (min_eq_right (le_of_lt hji))
    have hB_eq : B = apexRay P i := hB_def.trans (max_eq_left (le_of_lt hji))
    have h1 : dot2 (P.p2 j) (gamma t₂) = dot2 (P.p1 i) (gamma t₂) := by
      have hi1 := (hsw.2 i).2.2.2.1 t₂ (le_of_lt ht2_f.2.1) (hB_eq ▸ ht2_B)
      have hj2 := (hsw.2 j).2.2.2.2 t₂ (hA_eq ▸ ht2_A) (le_of_lt ht2_f.2.2.1)
      have ei : supportF P i t₂ = dot2 (P.p1 i) (gamma t₂) := max_eq_left (le_of_lt hi1)
      have ej : supportF P j t₂ = dot2 (P.p2 j) (gamma t₂) := max_eq_right (le_of_lt hj2)
      linarith [ht2_f.2.2.2.1]
    have hpos1 : 0 < dot2 (P.p2 j) (gamma t₂) := by
      have hj2 := (hsw.2 j).2.2.2.2 t₂ (hA_eq ▸ ht2_A) (le_of_lt ht2_f.2.2.1)
      have ej : supportF P j t₂ = dot2 (P.p2 j) (gamma t₂) := max_eq_right (le_of_lt hj2)
      linarith [ht2_f.2.2.2.1, ht2_f.2.2.2.2]
    have h2 : dot2 (P.p2 j) (gamma (t₂ + δ₂)) < dot2 (P.p1 i) (gamma (t₂ + δ₂)) := by
      have hi1 := (hsw.2 i).2.2.2.1 (t₂ + δ₂) (by linarith [ht2_f.2.1]) (hB_eq ▸ hδ₂_B)
      have hj2 := (hsw.2 j).2.2.2.2 (t₂ + δ₂) (by linarith [hA_eq, ht2_A]) (by linarith [hδ₂_B, hB2])
      have ei : supportF P i (t₂ + δ₂) = dot2 (P.p1 i) (gamma (t₂ + δ₂)) := max_eq_left (le_of_lt hi1)
      have ej : supportF P j (t₂ + δ₂) = dot2 (P.p2 j) (gamma (t₂ + δ₂)) := max_eq_right (le_of_lt hj2)
      dsimp [f] at hpos_2p; linarith
    have hpos2 : 0 < dot2 (P.p1 i) (gamma (t₂ + δ₂)) := by
      have ht2d_in_i : posLeft P i < t₂ + δ₂ ∧ t₂ + δ₂ < posRight P i :=
        ⟨by linarith [ht1_in_i.1, ht12], lt_trans (lt_trans hδ₂_B ht3_B) ht3_in_i.2⟩
      have hi_pos := ((hpi.2.2.2.2 (t₂ + δ₂)).mpr ht2d_in_i).2.2
      have hi1 := (hsw.2 i).2.2.2.1 (t₂ + δ₂) (by linarith [ht2_f.2.1]) (hB_eq ▸ hδ₂_B)
      have ei : supportF P i (t₂ + δ₂) = dot2 (P.p1 i) (gamma (t₂ + δ₂)) := max_eq_left (le_of_lt hi1)
      linarith
    have hr_2j_1i : rayParam (P.p2 j) < rayParam (P.p1 i) :=
      (rayParam_lt_of_pos_tie (P.vec_inOmega ⟨2 * j.val + 1, by omega⟩ |> fun h => by rwa [P.vec_odd j] at h)
        (P.vec_inOmega ⟨2 * i.val, by omega⟩ |> fun h => by rwa [P.vec_even i] at h)
        (le_of_lt ht2_f.2.1) (le_of_lt ht2_f.2.2.1) (by linarith [ht2_f.2.1]) (by linarith [hδ₂_B, hB2])
        h1 hpos1 (Or.inl ⟨by linarith, h2, hpos2⟩)).2
    have hr_1j_2j : rayParam (P.p1 j) < rayParam (P.p2 j) := by
      have hap_tie_j : dot2 (P.p1 j) (gamma (apexRay P j)) = dot2 (P.p2 j) (gamma (apexRay P j)) := by
        obtain ⟨hq3, hd1, hd2, _⟩ := P.apex_spec j
        have hom : InOmega (P.apex j) := Or.inl hq3.1
        have hnorm := inOmega_norm_pos hom
        have hrec := gamma_rayParam_smul hom
        rw [← hrec, dot2_smul_right] at hd1 hd2
        have : (|(P.apex j).1| + |(P.apex j).2|) * dot2 (P.p1 j) (gamma (apexRay P j)) =
            (|(P.apex j).1| + |(P.apex j).2|) * dot2 (P.p2 j) (gamma (apexRay P j)) := by
          unfold apexRay; linarith
        exact mul_left_cancel₀ (ne_of_gt hnorm) this
      have hpos_j1 : 0 < dot2 (P.p1 j) (gamma (apexRay P j)) := by
        have hp := (hsw.2 j).2.2.1; unfold supportF at hp; rw [hap_tie_j, max_self] at hp; linarith
      have hpos_j2 : 0 < dot2 (P.p2 j) (gamma (apexRay P j)) := by linarith
      exact rayParam_lt_of_det2_pos_and_pos_dot
        (P.vec_inOmega ⟨2 * j.val, by omega⟩ |> fun h => by rwa [P.vec_even j] at h)
        (P.vec_inOmega ⟨2 * j.val + 1, by omega⟩ |> fun h => by rwa [P.vec_odd j] at h)
        (by linarith [(hsw.2 j).1]) (by linarith [(hsw.2 j).2.1]) (P.h_det j) hpos_j1 hpos_j2
    linarith
  have hA_eq : A = apexRay P i := hA_def.trans (min_eq_left (le_of_lt hap_ij))
  have hB_eq : B = apexRay P j := hB_def.trans (max_eq_right (le_of_lt hap_ij))
  have h_lt_api : f (apexRay P i) < 0 := hneg_12 (apexRay P i) ⟨hA_eq ▸ ht1_A, hA_eq ▸ ht2_A⟩
  have h_gt_apj : 0 < f (apexRay P j) := hpos_23 (apexRay P j) ⟨hB_eq ▸ ht2_B, hB_eq ▸ ht3_B⟩
  have hclip_api : clippedG P i (apexRay P i) < clippedG P j (apexRay P i) := by
    have hi_pos : 0 < supportF P i (apexRay P i) := (hsw.2 i).2.2.1
    have hj_pos : 0 < supportF P j (apexRay P i) := by dsimp [f] at h_lt_api; linarith
    unfold clippedG; rw [max_eq_left (le_of_lt hi_pos), max_eq_left (le_of_lt hj_pos)]
    dsimp [f] at h_lt_api; linarith
  have hclip_apj : clippedG P j (apexRay P j) < clippedG P i (apexRay P j) := by
    have hj_pos : 0 < supportF P j (apexRay P j) := (hsw.2 j).2.2.1
    have hi_pos : 0 < supportF P i (apexRay P j) := by dsimp [f] at h_gt_apj; linarith
    unfold clippedG; rw [max_eq_left (le_of_lt hi_pos), max_eq_left (le_of_lt hj_pos)]
    dsimp [f] at h_gt_apj; linarith
  have hp1_om : ∀ k : Fin 5, InOmega (P.p1 k) := fun k => by
    have h := P.vec_inOmega ⟨2 * k.val, by omega⟩; rwa [P.vec_even k] at h
  have hp2_om : ∀ k : Fin 5, InOmega (P.p2 k) := fun k => by
    have h := P.vec_inOmega ⟨2 * k.val + 1, by omega⟩; rwa [P.vec_odd k] at h
  have hr_1j_2i : rayParam (P.p1 j) < rayParam (P.p2 i) := by
    have hapi_t2 : apexRay P i < t₂ := hA_eq ▸ ht2_A
    have ht2_apj : t₂ < apexRay P j := hB_eq ▸ ht2_B
    have h2d_apj : t₂ + δ₂ < apexRay P j := hB_eq ▸ hδ₂_B
    have ht2d_3 : t₂ + δ₂ ≤ 3 := le_of_lt (lt_trans h2d_apj (hsw.2 j).2.1 |>.trans (by norm_num))
    have h1 : dot2 (P.p1 j) (gamma t₂) = dot2 (P.p2 i) (gamma t₂) := by
      have hi2 := (hsw.2 i).2.2.2.2 t₂ hapi_t2 (le_of_lt ht2_f.2.2.1)
      have hj1 := (hsw.2 j).2.2.2.1 t₂ (le_of_lt ht2_f.2.1) ht2_apj
      have ei : supportF P i t₂ = dot2 (P.p2 i) (gamma t₂) := max_eq_right (le_of_lt hi2)
      have ej : supportF P j t₂ = dot2 (P.p1 j) (gamma t₂) := max_eq_left (le_of_lt hj1)
      linarith [ht2_f.2.2.2.1]
    have hpos1 : 0 < dot2 (P.p1 j) (gamma t₂) := by
      have hj1 := (hsw.2 j).2.2.2.1 t₂ (le_of_lt ht2_f.2.1) ht2_apj
      have ej : supportF P j t₂ = dot2 (P.p1 j) (gamma t₂) := max_eq_left (le_of_lt hj1)
      linarith [ht2_f.2.2.2.1, ht2_f.2.2.2.2]
    have h2 : dot2 (P.p1 j) (gamma (t₂ + δ₂)) < dot2 (P.p2 i) (gamma (t₂ + δ₂)) := by
      have hi2 := (hsw.2 i).2.2.2.2 (t₂ + δ₂) (lt_trans hapi_t2 (by linarith)) ht2d_3
      have hj1 := (hsw.2 j).2.2.2.1 (t₂ + δ₂) (by linarith [ht2_f.2.1]) h2d_apj
      have ei : supportF P i (t₂ + δ₂) = dot2 (P.p2 i) (gamma (t₂ + δ₂)) := max_eq_right (le_of_lt hi2)
      have ej : supportF P j (t₂ + δ₂) = dot2 (P.p1 j) (gamma (t₂ + δ₂)) := max_eq_left (le_of_lt hj1)
      dsimp [f] at hpos_2p; linarith
    have hpos2 : 0 < dot2 (P.p2 i) (gamma (t₂ + δ₂)) := by
      have ht2d_in_i : posLeft P i < t₂ + δ₂ ∧ t₂ + δ₂ < posRight P i :=
        ⟨lt_trans ht1_in_i.1 (lt_trans ht12 (by linarith)), lt_trans (lt_trans hδ₂_B ht3_B) ht3_in_i.2⟩
      have hi_pos := ((hpi.2.2.2.2 (t₂ + δ₂)).mpr ht2d_in_i).2.2
      have hi2 := (hsw.2 i).2.2.2.2 (t₂ + δ₂) (lt_trans hapi_t2 (by linarith)) ht2d_3
      have ei : supportF P i (t₂ + δ₂) = dot2 (P.p2 i) (gamma (t₂ + δ₂)) := max_eq_right (le_of_lt hi2)
      linarith
    exact (rayParam_lt_of_pos_tie (hp1_om j) (hp2_om i)
      (le_of_lt ht2_f.2.1) (le_of_lt ht2_f.2.2.1) (by linarith [ht2_f.2.1]) ht2d_3
      h1 hpos1 (Or.inl ⟨by linarith, h2, hpos2⟩)).2
  have hr_2i_2j : rayParam (P.p2 i) < rayParam (P.p2 j) := by
    have hapj_t3 : apexRay P j < t₃ := hB_eq ▸ ht3_B
    have hapi_t3 : apexRay P i < t₃ := lt_trans hap_ij hapj_t3
    have h3p_lt3 : t₃ + δ₃ < 3 := lt_of_lt_of_le hδ₃_Ri hpi.2.2.2.1
    have h1 : dot2 (P.p2 i) (gamma t₃) = dot2 (P.p2 j) (gamma t₃) := by
      have hi2 := (hsw.2 i).2.2.2.2 t₃ hapi_t3 (le_of_lt ht3_f.2.2.1)
      have hj2 := (hsw.2 j).2.2.2.2 t₃ hapj_t3 (le_of_lt ht3_f.2.2.1)
      have ei : supportF P i t₃ = dot2 (P.p2 i) (gamma t₃) := max_eq_right (le_of_lt hi2)
      have ej : supportF P j t₃ = dot2 (P.p2 j) (gamma t₃) := max_eq_right (le_of_lt hj2)
      linarith [ht3_f.2.2.2.1]
    have hpos1 : 0 < dot2 (P.p2 i) (gamma t₃) := by
      have hi2 := (hsw.2 i).2.2.2.2 t₃ hapi_t3 (le_of_lt ht3_f.2.2.1)
      have ei : supportF P i t₃ = dot2 (P.p2 i) (gamma t₃) := max_eq_right (le_of_lt hi2)
      linarith [ht3_f.2.2.2.2]
    have h2 : dot2 (P.p2 i) (gamma (t₃ + δ₃)) < dot2 (P.p2 j) (gamma (t₃ + δ₃)) := by
      have hi2 := (hsw.2 i).2.2.2.2 (t₃ + δ₃) (lt_trans hapi_t3 (by linarith)) (le_of_lt h3p_lt3)
      have hj2 := (hsw.2 j).2.2.2.2 (t₃ + δ₃) (lt_trans hapj_t3 (by linarith)) (le_of_lt h3p_lt3)
      have ei : supportF P i (t₃ + δ₃) = dot2 (P.p2 i) (gamma (t₃ + δ₃)) := max_eq_right (le_of_lt hi2)
      have ej : supportF P j (t₃ + δ₃) = dot2 (P.p2 j) (gamma (t₃ + δ₃)) := max_eq_right (le_of_lt hj2)
      dsimp [f] at hneg_3p; linarith
    have hpos2 : 0 < dot2 (P.p2 j) (gamma (t₃ + δ₃)) := by
      have ht3d_in_j : posLeft P j < t₃ + δ₃ ∧ t₃ + δ₃ < posRight P j :=
        ⟨lt_trans ht3_in_j.1 (by linarith), hδ₃_Rj⟩
      have hj_pos := ((hpj.2.2.2.2 (t₃ + δ₃)).mpr ht3d_in_j).2.2
      have hj2 := (hsw.2 j).2.2.2.2 (t₃ + δ₃) (lt_trans hapj_t3 (by linarith)) (le_of_lt h3p_lt3)
      have ej : supportF P j (t₃ + δ₃) = dot2 (P.p2 j) (gamma (t₃ + δ₃)) := max_eq_right (le_of_lt hj2)
      linarith
    exact (rayParam_lt_of_pos_tie (hp2_om i) (hp2_om j)
      (le_of_lt ht3_f.2.1) (le_of_lt ht3_f.2.2.1) (by linarith [ht3_f.2.1]) (le_of_lt h3p_lt3)
      h1 hpos1 (Or.inl ⟨by linarith, h2, hpos2⟩)).2
  exact ⟨lt_trans ht1_in_j.1 (hA_eq ▸ ht1_A), hap_ij, lt_trans (hB_eq ▸ ht3_B) ht3_in_i.2,
    hclip_api, hclip_apj, hr_p1, hr_1j_2i, hr_2i_2j⟩

private lemma exists_vec_eq_topEnv (P : DualConfig) (t : ℝ) :
    ∃ a : Fin 10, dot2 (P.vec a) (gamma t) = topEnv P t := by
  unfold topEnv
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
    (fun i : Fin 5 => supportF P i t)
  unfold supportF at hi
  rcases max_choice (dot2 (P.p1 i) (gamma t)) (dot2 (P.p2 i) (gamma t)) with hm | hm
  · refine ⟨⟨2 * i.val, by omega⟩, ?_⟩
    rw [P.vec_even i, ← hm]; exact hi.symm
  · refine ⟨⟨2 * i.val + 1, by omega⟩, ?_⟩
    rw [P.vec_odd i, ← hm]; exact hi.symm

private lemma dot2_vec_le_supportF (P : DualConfig) (a : Fin 10) (t : ℝ) :
    dot2 (P.vec a) (gamma t) ≤ supportF P (vecColor a) t := by
  unfold DualConfig.vec supportF vecColor
  split_ifs
  · exact le_max_left _ _
  · exact le_max_right _ _

private lemma unique_top_on_Icc (P : DualConfig) {a b : ℝ} (hab : a < b)
    (h_no_tie : ∀ t ∈ Set.Icc a b, ∀ x y : Fin 10, x ≠ y →
      dot2 (P.vec x) (gamma t) = topEnv P t → dot2 (P.vec y) (gamma t) = topEnv P t → False) :
    ∃ c : Fin 10, ∀ t ∈ Set.Icc a b, ∀ y : Fin 10, y ≠ c →
      dot2 (P.vec y) (gamma t) < dot2 (P.vec c) (gamma t) := by
  let U : Fin 10 → Set ℝ := fun x =>
    {t : ℝ | ∀ y : Fin 10, y ≠ x → dot2 (P.vec y) (gamma t) < dot2 (P.vec x) (gamma t)}
  have hdot_cont : ∀ y : Fin 10, Continuous (fun t => dot2 (P.vec y) (gamma t)) := by
    intro y; unfold dot2
    exact (continuous_const.mul gamma_continuous.fst).add (continuous_const.mul gamma_continuous.snd)
  have hU_open : ∀ x : Fin 10, IsOpen (U x) := by
    intro x
    have : U x = ⋂ y : Fin 10, if y ≠ x then {t : ℝ | dot2 (P.vec y) (gamma t) < dot2 (P.vec x) (gamma t)} else Set.univ := by
      ext t; simp [U, Set.mem_iInter]
    rw [this]
    refine isOpen_iInter_of_finite fun y => ?_
    split_ifs
    · exact isOpen_lt (hdot_cont y) (hdot_cont x)
    · exact isOpen_univ
  have hU_mem_of_top : ∀ t ∈ Set.Icc a b, ∃ x : Fin 10, t ∈ U x := by
    intro t ht
    obtain ⟨x, hx⟩ := exists_vec_eq_topEnv P t
    refine ⟨x, fun y hy => ?_⟩
    have hle : dot2 (P.vec y) (gamma t) ≤ topEnv P t :=
      le_trans (dot2_vec_le_supportF P y t)
        (Finset.le_sup' (fun k : Fin 5 => supportF P k t) (Finset.mem_univ (vecColor y)))
    refine lt_of_le_of_ne (hx ▸ hle) fun heq => h_no_tie t ht x y hy.symm hx (heq.trans hx)
  obtain ⟨c, hc_a⟩ := hU_mem_of_top a (Set.left_mem_Icc.mpr hab.le)
  let V : Set ℝ := U c
  let W : Set ℝ := ⋃ x : Fin 10, if x ≠ c then U x else ∅
  have hV_open : IsOpen V := hU_open c
  have hW_open : IsOpen W := by
    refine isOpen_iUnion fun x => ?_
    split_ifs
    · exact hU_open x
    · exact isOpen_empty
  have hcov : Set.Icc a b ⊆ V ∪ W := by
    intro t ht
    obtain ⟨x, hx⟩ := hU_mem_of_top t ht
    by_cases hxc : x = c
    · subst hxc; exact Or.inl hx
    · exact Or.inr (Set.mem_iUnion.mpr ⟨x, by simp [hxc, hx]⟩)
  have hdisj : Disjoint V W := by
    rw [Set.disjoint_left]
    intro t htV htW
    simp only [W, Set.mem_iUnion] at htW
    obtain ⟨x, hxW⟩ := htW
    split_ifs at hxW with hxc
    · exact lt_asymm (htV x hxc) (hxW c hxc.symm)
    · exact hxW
  refine ⟨c, fun t ht => ?_⟩
  by_contra ht_notV
  have htW : t ∈ W := (hcov ht).resolve_left ht_notV
  obtain ⟨u, _, huV, huW⟩ := isPreconnected_Icc V W hV_open hW_open hcov
    ⟨a, Set.left_mem_Icc.mpr hab.le, hc_a⟩ ⟨t, ht, htW⟩
  exact (Set.disjoint_left.mp hdisj) huV huW

private lemma card_posPairTies_eq_two_iff_rightKey_gt (P : DualConfig) (hgp : IsGenPos P)
    (h_shat : ∀ m : Fin 5 → Bool, ∃ z : ℝ × ℝ, InOmega z ∧ RealizesDualMask P m z)
    (hleft : StrictMono (leftKey P)) {i j : Fin 5} (hij : i < j) :
    (posPairTies P i j).card = 2 ↔ rightKey P j < rightKey P i := by
  have hij_ne : i ≠ j := ne_of_lt hij
  constructor
  · intro h2
    by_contra hle
    have hlt : rightKey P i < rightKey P j :=
      lt_of_le_of_ne (not_lt.mp hle) ((rightKey_injective P hgp).ne hij_ne)
    exact posPairTies_ne_two_of_same_order P hgp h_shat hij_ne (hleft hij) hlt h2
  · intro hR
    by_contra hne2
    have hbounds := (card_posPairTies_bounds P hgp h_shat).1 i j hij
    obtain ⟨t_L, htL0, htL3, htLi, htL_lt, htL_all⟩ :=
      left_dom_of_leftKey_lt P hgp h_shat (hleft hij)
    obtain ⟨t_R, htR0, htR3, htRi, htR_lt, htR_all_ji⟩ :=
      right_dom_of_rightKey_lt P hgp h_shat hR
    have htR_all : ∀ s ∈ posPairTies P i j, s < t_R := by
      intro s hs; exact htR_all_ji s (posPairTies_comm P i j ▸ hs)
    have hpi := posInterval_eq_Ioo P hgp i
    have htL_in_i : posLeft P i < t_L ∧ t_L < posRight P i :=
      (hpi.2.2.2.2 t_L).mp ⟨htL0, htL3, htLi⟩
    have htR_in_i : posLeft P i < t_R ∧ t_R < posRight P i :=
      (hpi.2.2.2.2 t_R).mp ⟨htR0, htR3, htRi⟩
    let f : ℝ → ℝ := fun t => supportF P i t - supportF P j t
    have hf_cont : Continuous f := (supportF_continuous P i).sub (supportF_continuous P j)
    have h_f_tL : 0 < f t_L := by dsimp [f]; linarith
    have h_f_tR : 0 < f t_R := by dsimp [f]; linarith
    have h_no_tie_Icc : ∀ u ∈ Set.Icc t_L t_R, u ∉ posPairTies P i j → f u ≠ 0 := by
      intro u ⟨huL, huR⟩ hu_not hzero
      have hu0 : 0 < u := lt_of_lt_of_le htL0 huL
      have hu3 : u < 3 := lt_of_le_of_lt huR htR3
      have hui : 0 < supportF P i u :=
        ((hpi.2.2.2.2 u).mpr ⟨lt_of_lt_of_le htL_in_i.1 huL, lt_of_le_of_lt huR htR_in_i.2⟩).2.2
      apply hu_not
      simp only [posPairTies, Finset.mem_filter]
      exact ⟨candTieGrid_mem_of_tie P hgp hu0 hu3 hij_ne (by linarith), hu0, hu3, by linarith, hui⟩
    rcases (by omega : (posPairTies P i j).card = 1 ∨ (posPairTies P i j).card = 3) with h1 | h3
    · obtain ⟨t₁, ht1_eq⟩ := Finset.card_eq_one.mp h1
      have ht1_mem : t₁ ∈ posPairTies P i j := by rw [ht1_eq]; simp
      have htL1 : t_L < t₁ := htL_all t₁ ht1_mem
      have ht1R : t₁ < t_R := htR_all t₁ ht1_mem
      obtain ⟨ε₁, hε₁_pos, hopp1⟩ := sign_change_at_posPairTie P hgp hij_ne ht1_mem
      obtain ⟨δ₁, hδ₁_pos, hδ₁_ε, hδ₁_L, hδ₁_R⟩ :
          ∃ δ₁ : ℝ, 0 < δ₁ ∧ δ₁ ≤ ε₁ ∧ t_L < t₁ - δ₁ ∧ t₁ + δ₁ < t_R := by
        refine ⟨min ε₁ (min ((t₁ - t_L) / 3) ((t_R - t₁) / 3)),
          lt_min hε₁_pos (lt_min (by linarith) (by linarith)), min_le_left _ _, ?_, ?_⟩
        · have : min ε₁ (min ((t₁ - t_L) / 3) ((t_R - t₁) / 3)) ≤ (t₁ - t_L) / 3 :=
            le_trans (min_le_right _ _) (min_le_left _ _)
          linarith
        · have : min ε₁ (min ((t₁ - t_L) / 3) ((t_R - t₁) / 3)) ≤ (t_R - t₁) / 3 :=
            le_trans (min_le_right _ _) (min_le_right _ _)
          linarith
      have hpos_1m : 0 < f (t₁ - δ₁) := by
        by_contra hle; replace hle : f (t₁ - δ₁) ≤ 0 := not_lt.mp hle
        obtain ⟨u, hu, hu_eq⟩ := intermediate_value_Icc' (le_of_lt hδ₁_L) hf_cont.continuousOn
          (⟨hle, le_of_lt h_f_tL⟩ : (0 : ℝ) ∈ Set.Icc (f (t₁ - δ₁)) (f t_L))
        exact h_no_tie_Icc u ⟨hu.1, lt_trans (lt_of_le_of_lt hu.2 (by linarith)) ht1R |>.le⟩
          (by rw [ht1_eq, Finset.mem_singleton]; linarith [hu.2]) hu_eq
      have hneg_1p : f (t₁ + δ₁) < 0 := by
        obtain ⟨_, _, hprod⟩ := hopp1 δ₁ hδ₁_pos hδ₁_ε
        change f (t₁ - δ₁) * f (t₁ + δ₁) < 0 at hprod
        exact lt_of_not_ge fun hge => absurd hprod (not_lt.mpr (mul_nonneg (le_of_lt hpos_1m) hge))
      obtain ⟨u, hu, hu_eq⟩ := intermediate_value_Icc (le_of_lt hδ₁_R) hf_cont.continuousOn
        (⟨le_of_lt hneg_1p, le_of_lt h_f_tR⟩ : (0 : ℝ) ∈ Set.Icc (f (t₁ + δ₁)) (f t_R))
      exact h_no_tie_Icc u ⟨lt_trans htL1 (lt_of_lt_of_le (by linarith) hu.1) |>.le, hu.2⟩
        (by rw [ht1_eq, Finset.mem_singleton]; linarith [hu.1]) hu_eq
    · obtain ⟨t₁, t₂, t₃, ht12, ht23, ht1_mem, ht2_mem, ht3_mem, hmem_iff⟩ :
          ∃ t₁ t₂ t₃ : ℝ, t₁ < t₂ ∧ t₂ < t₃ ∧
            t₁ ∈ posPairTies P i j ∧ t₂ ∈ posPairTies P i j ∧ t₃ ∈ posPairTies P i j ∧
            ∀ t : ℝ, t ∈ posPairTies P i j ↔ t = t₁ ∨ t = t₂ ∨ t = t₃ := by
        let s : List ℝ := (posPairTies P i j).sort (· ≤ ·)
        have hs_len : s.length = 3 := by simp [s, Finset.length_sort, h3]
        have hs_pw : s.Pairwise (· < ·) := (posPairTies P i j).sortedLT_sort.pairwise
        refine ⟨s[0]'(by omega), s[1]'(by omega), s[2]'(by omega),
          List.pairwise_iff_getElem.mp hs_pw 0 1 (by omega) (by omega) (by omega),
          List.pairwise_iff_getElem.mp hs_pw 1 2 (by omega) (by omega) (by omega),
          (Finset.mem_sort _).mp (List.getElem_mem (by rw [hs_len]; omega)),
          (Finset.mem_sort _).mp (List.getElem_mem (by rw [hs_len]; omega)),
          (Finset.mem_sort _).mp (List.getElem_mem (by rw [hs_len]; omega)), ?_⟩
        have hs_eq : s = [s[0]'(by omega), s[1]'(by omega), s[2]'(by omega)] := by
          refine List.ext_getElem (by simp [hs_len]) fun m hm1 hm2 => ?_
          have hm3 : m < 3 := by omega
          interval_cases m <;> rfl
        intro t; rw [← Finset.mem_sort (· ≤ ·)]
        change t ∈ s ↔ _; conv_lhs => rw [hs_eq]
        simp
      have htL1 : t_L < t₁ := htL_all t₁ ht1_mem
      have ht3R : t₃ < t_R := htR_all t₃ ht3_mem
      obtain ⟨ε₁, hε₁_pos, hopp1⟩ := sign_change_at_posPairTie P hgp hij_ne ht1_mem
      obtain ⟨ε₂, hε₂_pos, hopp2⟩ := sign_change_at_posPairTie P hgp hij_ne ht2_mem
      obtain ⟨ε₃, hε₃_pos, hopp3⟩ := sign_change_at_posPairTie P hgp hij_ne ht3_mem
      obtain ⟨δ₁, hδ₁_pos, hδ₁_ε, hδ₁_L, hδ₁_R⟩ :
          ∃ δ₁ : ℝ, 0 < δ₁ ∧ δ₁ ≤ ε₁ ∧ t_L < t₁ - δ₁ ∧ t₁ + δ₁ < t₂ := by
        refine ⟨min ε₁ (min ((t₁ - t_L) / 3) ((t₂ - t₁) / 3)),
          lt_min hε₁_pos (lt_min (by linarith) (by linarith)), min_le_left _ _, ?_, ?_⟩
        · have : min ε₁ (min ((t₁ - t_L) / 3) ((t₂ - t₁) / 3)) ≤ (t₁ - t_L) / 3 :=
            le_trans (min_le_right _ _) (min_le_left _ _)
          linarith
        · have : min ε₁ (min ((t₁ - t_L) / 3) ((t₂ - t₁) / 3)) ≤ (t₂ - t₁) / 3 :=
            le_trans (min_le_right _ _) (min_le_right _ _)
          linarith
      obtain ⟨δ₂, hδ₂_pos, hδ₂_ε, hδ₂_L, hδ₂_R⟩ :
          ∃ δ₂ : ℝ, 0 < δ₂ ∧ δ₂ ≤ ε₂ ∧ t₁ + δ₁ < t₂ - δ₂ ∧ t₂ + δ₂ < t₃ := by
        refine ⟨min ε₂ (min ((t₂ - (t₁ + δ₁)) / 3) ((t₃ - t₂) / 3)),
          lt_min hε₂_pos (lt_min (by linarith) (by linarith)), min_le_left _ _, ?_, ?_⟩
        · have : min ε₂ (min ((t₂ - (t₁ + δ₁)) / 3) ((t₃ - t₂) / 3)) ≤ (t₂ - (t₁ + δ₁)) / 3 :=
            le_trans (min_le_right _ _) (min_le_left _ _)
          linarith
        · have : min ε₂ (min ((t₂ - (t₁ + δ₁)) / 3) ((t₃ - t₂) / 3)) ≤ (t₃ - t₂) / 3 :=
            le_trans (min_le_right _ _) (min_le_right _ _)
          linarith
      obtain ⟨δ₃, hδ₃_pos, hδ₃_ε, hδ₃_L, hδ₃_R⟩ :
          ∃ δ₃ : ℝ, 0 < δ₃ ∧ δ₃ ≤ ε₃ ∧ t₂ + δ₂ < t₃ - δ₃ ∧ t₃ + δ₃ < t_R := by
        refine ⟨min ε₃ (min ((t₃ - (t₂ + δ₂)) / 3) ((t_R - t₃) / 3)),
          lt_min hε₃_pos (lt_min (by linarith) (by linarith)), min_le_left _ _, ?_, ?_⟩
        · have : min ε₃ (min ((t₃ - (t₂ + δ₂)) / 3) ((t_R - t₃) / 3)) ≤ (t₃ - (t₂ + δ₂)) / 3 :=
            le_trans (min_le_right _ _) (min_le_left _ _)
          linarith
        · have : min ε₃ (min ((t₃ - (t₂ + δ₂)) / 3) ((t_R - t₃) / 3)) ≤ (t_R - t₃) / 3 :=
            le_trans (min_le_right _ _) (min_le_right _ _)
          linarith
      have hpos_1m : 0 < f (t₁ - δ₁) := by
        by_contra hle; replace hle : f (t₁ - δ₁) ≤ 0 := not_lt.mp hle
        obtain ⟨u, hu, hu_eq⟩ := intermediate_value_Icc' (le_of_lt hδ₁_L) hf_cont.continuousOn
          (⟨hle, le_of_lt h_f_tL⟩ : (0 : ℝ) ∈ Set.Icc (f (t₁ - δ₁)) (f t_L))
        exact h_no_tie_Icc u ⟨hu.1, le_of_lt (lt_of_le_of_lt hu.2 (by linarith))⟩
          (fun hm => by rw [hmem_iff] at hm; rcases hm with rfl | rfl | rfl <;> linarith [hu.2]) hu_eq
      have hneg_1p : f (t₁ + δ₁) < 0 := by
        obtain ⟨_, _, hprod⟩ := hopp1 δ₁ hδ₁_pos hδ₁_ε
        change f (t₁ - δ₁) * f (t₁ + δ₁) < 0 at hprod
        exact lt_of_not_ge fun hge => absurd hprod (not_lt.mpr (mul_nonneg (le_of_lt hpos_1m) hge))
      have hneg_2m : f (t₂ - δ₂) < 0 := by
        by_contra hge; replace hge : 0 ≤ f (t₂ - δ₂) := not_lt.mp hge
        obtain ⟨u, hu, hu_eq⟩ := intermediate_value_Icc (le_of_lt hδ₂_L) hf_cont.continuousOn
          (⟨le_of_lt hneg_1p, hge⟩ : (0 : ℝ) ∈ Set.Icc (f (t₁ + δ₁)) (f (t₂ - δ₂)))
        exact h_no_tie_Icc u ⟨by linarith [hu.1], by linarith [hu.2]⟩
          (fun hm => by rw [hmem_iff] at hm; rcases hm with rfl | rfl | rfl <;> linarith [hu.1, hu.2]) hu_eq
      have hpos_2p : 0 < f (t₂ + δ₂) := by
        obtain ⟨_, _, hprod⟩ := hopp2 δ₂ hδ₂_pos hδ₂_ε
        change f (t₂ - δ₂) * f (t₂ + δ₂) < 0 at hprod
        exact lt_of_not_ge fun hle => absurd hprod (not_lt.mpr (mul_nonneg_of_nonpos_of_nonpos (le_of_lt hneg_2m) hle))
      have hpos_3m : 0 < f (t₃ - δ₃) := by
        by_contra hle; replace hle : f (t₃ - δ₃) ≤ 0 := not_lt.mp hle
        obtain ⟨u, hu, hu_eq⟩ := intermediate_value_Icc' (le_of_lt hδ₃_L) hf_cont.continuousOn
          (⟨hle, le_of_lt hpos_2p⟩ : (0 : ℝ) ∈ Set.Icc (f (t₃ - δ₃)) (f (t₂ + δ₂)))
        exact h_no_tie_Icc u ⟨by linarith [hu.1], by linarith [hu.2]⟩
          (fun hm => by rw [hmem_iff] at hm; rcases hm with rfl | rfl | rfl <;> linarith [hu.1, hu.2]) hu_eq
      have hneg_3p : f (t₃ + δ₃) < 0 := by
        obtain ⟨_, _, hprod⟩ := hopp3 δ₃ hδ₃_pos hδ₃_ε
        change f (t₃ - δ₃) * f (t₃ + δ₃) < 0 at hprod
        exact lt_of_not_ge fun hge => absurd hprod (not_lt.mpr (mul_nonneg (le_of_lt hpos_3m) hge))
      obtain ⟨u, hu, hu_eq⟩ := intermediate_value_Icc (le_of_lt hδ₃_R) hf_cont.continuousOn
        (⟨le_of_lt hneg_3p, le_of_lt h_f_tR⟩ : (0 : ℝ) ∈ Set.Icc (f (t₃ + δ₃)) (f t_R))
      exact h_no_tie_Icc u ⟨by linarith [hu.1], hu.2⟩
        (fun hm => by rw [hmem_iff] at hm; rcases hm with rfl | rfl | rfl <;> linarith [hu.1]) hu_eq

private lemma cons_append_getD_last {α : Type*} (d3 : α) :
    ∀ (l : List α) (d0 d_fb : α) (hl : 0 < l.length),
      (d0 :: (l ++ [d3])).getD l.length d_fb = l[l.length - 1]'(Nat.sub_lt hl Nat.one_pos)
  | [], _, _, hl => absurd hl (by simp)
  | [a], d0, d_fb, _ => rfl
  | a :: b :: t, d0, d_fb, _ => by
    simp only [List.length_cons, List.cons_append, List.getD_cons_succ]
    exact cons_append_getD_last d3 (b :: t) a d_fb (by simp)

private lemma cons_append_getD_end {α : Type*} (d3 d_fb : α) :
    ∀ (l : List α) (d0 : α),
      (d0 :: (l ++ [d3])).getD (l.length + 1) d_fb = d3
  | [], _ => rfl
  | a :: t, _ => by
    simp only [List.length_cons, List.cons_append, List.getD_cons_succ]
    exact cons_append_getD_end d3 d_fb t a

private lemma hullMidpoint_zero_spec (P : DualConfig) (hgp : IsGenPos P)
    (htop : ∀ {t : ℝ}, 0 ≤ t → t ≤ 3 → 0 < topEnv P t) :
    ∃ x : ℝ, (∀ t ∈ topTiePts P, x ≤ t) ∧ 0 < x ∧ x < 3 ∧
      0 < hullMidpoint P ⟨0, Nat.zero_lt_succ _⟩ ∧
      hullMidpoint P ⟨0, Nat.zero_lt_succ _⟩ < x := by
  obtain ⟨s, hs_eq, hs_pw⟩ :
      ∃ s : List ℝ, s = (topTiePts P).sort (· ≤ ·) ∧ s.Pairwise (· < ·) :=
    ⟨_, rfl, (topTiePts P).sortedLT_sort.pairwise⟩
  have hspec := hullVerts_spec P hgp htop
  have hs_len : s.length = (topTiePts P).card := by rw [hs_eq]; exact Finset.length_sort _
  have hs_pos : 0 < s.length := by rw [hs_len]; exact hspec.1
  have hs_cons : ∃ a l, s = a :: l := by
    cases s with
    | nil => simp at hs_pos
    | cons a l => exact ⟨a, l, rfl⟩
  obtain ⟨a, l, rfl⟩ := hs_cons
  have ha_mem : a ∈ topTiePts P := by
    have hmem : a ∈ (a :: l) := by simp
    rwa [hs_eq, Finset.mem_sort] at hmem
  have ha_bounds : (0 : ℝ) < a ∧ a < (3 : ℝ) := by
    have hm := ha_mem
    simp only [topTiePts, Finset.mem_filter] at hm
    exact ⟨hm.2.1, hm.2.2.1⟩
  have hmid_eq : hullMidpoint P ⟨0, Nat.zero_lt_succ _⟩ = a / 2 := by
    unfold hullMidpoint hullSeamList
    rw [← hs_eq]
    change (([0] ++ (a :: l) ++ [3]).getD 0 0 + ([0] ++ (a :: l) ++ [3]).getD 1 3) / 2 = a / 2
    have h0 : ([0] ++ (a :: l) ++ [3]).getD 0 0 = 0 := rfl
    have h1 : ([0] ++ (a :: l) ++ [3]).getD 1 3 = a := rfl
    rw [h0, h1, zero_add]
  refine ⟨a, fun t ht => ?_, ha_bounds.1, ha_bounds.2, ?_, ?_⟩
  · have hts : t ∈ a :: l := by rwa [hs_eq, Finset.mem_sort]
    rcases List.mem_cons.mp hts with rfl | ht_l
    · exact le_rfl
    · exact le_of_lt ((List.pairwise_cons.mp hs_pw).1 t ht_l)
  · rw [hmid_eq]; linarith [ha_bounds.1]
  · rw [hmid_eq]; linarith [ha_bounds.1]

private lemma hullMidpoint_last_spec (P : DualConfig) (hgp : IsGenPos P)
    (htop : ∀ {t : ℝ}, 0 ≤ t → t ≤ 3 → 0 < topEnv P t) :
    ∃ x : ℝ, (∀ t ∈ topTiePts P, t ≤ x) ∧ 0 < x ∧ x < 3 ∧
      x < hullMidpoint P ⟨(topTiePts P).card, Nat.lt_succ_self _⟩ ∧
      hullMidpoint P ⟨(topTiePts P).card, Nat.lt_succ_self _⟩ < 3 := by
  obtain ⟨s, hs_eq, hs_pw⟩ :
      ∃ s : List ℝ, s = (topTiePts P).sort (· ≤ ·) ∧ s.Pairwise (· < ·) :=
    ⟨_, rfl, (topTiePts P).sortedLT_sort.pairwise⟩
  have hspec := hullVerts_spec P hgp htop
  have hs_len : s.length = (topTiePts P).card := by rw [hs_eq]; exact Finset.length_sort _
  have hs_pos : 0 < s.length := by rw [hs_len]; exact hspec.1
  have hsN_lt : s.length - 1 < s.length := Nat.sub_lt hs_pos Nat.one_pos
  have hx_mem : s[s.length - 1]'hsN_lt ∈ topTiePts P := by
    rw [← Finset.mem_sort (· ≤ ·), ← hs_eq]
    exact List.getElem_mem hsN_lt
  have hx_bounds : (0 : ℝ) < s[s.length - 1]'hsN_lt ∧ s[s.length - 1]'hsN_lt < (3 : ℝ) := by
    have hm := hx_mem
    simp only [topTiePts, Finset.mem_filter] at hm
    exact ⟨hm.2.1, hm.2.2.1⟩
  have hmid_eq : hullMidpoint P ⟨(topTiePts P).card, Nat.lt_succ_self _⟩ =
      (s[s.length - 1]'hsN_lt + 3) / 2 := by
    unfold hullMidpoint hullSeamList
    rw [← hs_eq, ← hs_len]
    change ((0 :: (s ++ [3])).getD s.length 0 + (0 :: (s ++ [3])).getD (s.length + 1) 3) / 2 =
      (s[s.length - 1]'(Nat.sub_lt hs_pos Nat.one_pos) + 3) / 2
    rw [cons_append_getD_last 3 s 0 0 hs_pos, cons_append_getD_end 3 3 s 0]
  refine ⟨s[s.length - 1]'hsN_lt, fun t ht => ?_, hx_bounds.1, hx_bounds.2, ?_, ?_⟩
  · have hts : t ∈ s := by rwa [hs_eq, Finset.mem_sort]
    obtain ⟨k, hk, hkeq⟩ := List.mem_iff_getElem.mp hts
    have hk_le : k ≤ s.length - 1 := by omega
    rcases eq_or_lt_of_le hk_le with rfl | hk_lt
    · exact le_of_eq hkeq.symm
    · exact le_of_lt (hkeq ▸ List.pairwise_iff_getElem.mp hs_pw k (s.length - 1) hk hsN_lt hk_lt)
  · rw [hmid_eq]; linarith [hx_bounds.2]
  · rw [hmid_eq]; linarith [hx_bounds.2]

private lemma clippedG_ne_at_apexRay (P : DualConfig) (hgp : IsGenPos P) {i j : Fin 5} (hij : i ≠ j) :
    clippedG P i (apexRay P j) ≠ clippedG P j (apexRay P j) := by
  intro heq
  let tj := apexRay P j
  have hapj := (supportF_branch_switch P hgp).2 j
  have htj_pos : 0 < supportF P j tj := hapj.2.2.1
  have htj_clip_pos : 0 < clippedG P j tj := lt_of_lt_of_le htj_pos (le_max_left _ _)
  have hi_pos : 0 < supportF P i tj := by
    by_contra hle; replace hle : supportF P i tj ≤ 0 := not_lt.mp hle
    have : clippedG P i tj = 0 := max_eq_right hle
    linarith
  have hfij : supportF P i tj = supportF P j tj := by
    unfold clippedG at heq
    rw [max_eq_left (le_of_lt hi_pos), max_eq_left (le_of_lt htj_pos)] at heq
    exact heq
  have hap_tie_j : dot2 (P.p1 j) (gamma tj) = dot2 (P.p2 j) (gamma tj) := by
    obtain ⟨hq3, hd1, hd2, _⟩ := P.apex_spec j
    have hom : InOmega (P.apex j) := Or.inl hq3.1
    have hnorm := inOmega_norm_pos hom
    have hrec := gamma_rayParam_smul hom
    rw [← hrec, dot2_smul_right] at hd1 hd2
    have : (|(P.apex j).1| + |(P.apex j).2|) * dot2 (P.p1 j) (gamma tj) =
        (|(P.apex j).1| + |(P.apex j).2|) * dot2 (P.p2 j) (gamma tj) := by
      dsimp [tj]; unfold apexRay; linarith
    exact mul_left_cancel₀ (ne_of_gt hnorm) this
  let j1 : Fin 10 := ⟨2 * j.val, by omega⟩
  let j2 : Fin 10 := ⟨2 * j.val + 1, by omega⟩
  have hsupj : dot2 (P.vec j1) (gamma tj) = supportF P j tj := by
    rw [P.vec_even j]; unfold supportF; rw [hap_tie_j, max_self]
  have hvc_even : ∀ k : Fin 5, vecColor ⟨2 * k.val, by omega⟩ = k := by
    intro k; ext; dsimp [vecColor]; omega
  have hvc_odd : ∀ k : Fin 5, vecColor ⟨2 * k.val + 1, by omega⟩ = k := by
    intro k; ext; dsimp [vecColor]; omega
  obtain ⟨ai, hai_col, hai_dot⟩ :
      ∃ a : Fin 10, vecColor a = i ∧ dot2 (P.vec a) (gamma tj) = supportF P i tj := by
    unfold supportF
    rcases max_choice (dot2 (P.p1 i) (gamma tj)) (dot2 (P.p2 i) (gamma tj)) with h | h
    · exact ⟨⟨2 * i.val, by omega⟩, hvc_even i, by rw [P.vec_even i, h]⟩
    · exact ⟨⟨2 * i.val + 1, by omega⟩, hvc_odd i, by rw [P.vec_odd i, h]⟩
  have hai_ne_j1 : ai ≠ j1 := fun h => hij (by rw [← hai_col, h, hvc_even j])
  have htie_j12 : dot2 (P.vec j1) (gamma tj) = dot2 (P.vec j2) (gamma tj) := by
    rw [P.vec_even j, P.vec_odd j]; exact hap_tie_j
  have hj12 : j1 < j2 := by show 2 * j.val < 2 * j.val + 1; omega
  have hrd := (ray_ties_zeros_disjoint P hgp).2.2.2 tj
    (lt_trans (by norm_num) hapj.1) (lt_trans hapj.2.1 (by norm_num))
  rcases lt_or_gt_of_ne hai_ne_j1 with hlt | hgt
  · have hpair_ne : (j1, j2) ≠ (ai, j1) := fun h => hai_ne_j1 (congrArg Prod.fst h).symm
    exact hrd j1 j2 ai j1 hj12 hlt hpair_ne ⟨htie_j12, by linarith⟩
  · have hpair_ne : (j1, j2) ≠ (j1, ai) := fun h => by
      have : j2 = ai := congrArg Prod.snd h
      exact hij (by rw [← hai_col, ← this, hvc_odd j])
    exact hrd j1 j2 j1 ai hj12 hgt hpair_ne ⟨htie_j12, by linarith⟩

/-- Crossing parity and inversion law: under canonical left-key order, `T_2^+ = inv(rightPerm P)`. -/
theorem crossing_parity_inv (P : DualConfig) (hgp : IsGenPos P)
    (htop : ∀ {t : ℝ}, 0 ≤ t → t ≤ 3 → 0 < topEnv P t)
    (h_shat : ∀ m : Fin 5 → Bool, ∃ z : ℝ × ℝ, InOmega z ∧ RealizesDualMask P m z)
    (hleft : StrictMono (leftKey P)) :
    crossCountOfMult P 2 = permInversions (rightPerm P) ∧
    hullColors P ⟨0, by omega⟩ = ⟨0, by omega⟩ ∧
    hullColors P ⟨(topTiePts P).card, by omega⟩ = rightPerm P ⟨4, by omega⟩ := by
  let σ := rightPerm P
  have hσ_mono : StrictMono (fun r : Fin 5 => rightKey P (σ r)) := rightPerm_strictMono P hgp
  have h1 : crossCountOfMult P 2 = permInversions σ := by
    unfold crossCountOfMult permInversions
    refine Finset.card_bij (fun p _ => (σ.symm p.2, σ.symm p.1)) ?_ ?_ ?_
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
      have hR := (card_posPairTies_eq_two_iff_rightKey_gt P hgp h_shat hleft hp.1).mp hp.2
      refine ⟨?_, by simpa using hp.1⟩
      by_contra hle
      have hord : σ.symm p.1 ≤ σ.symm p.2 := not_lt.mp hle
      have hkm : rightKey P (σ (σ.symm p.1)) ≤ rightKey P (σ (σ.symm p.2)) := hσ_mono.monotone hord
      simp only [σ, Equiv.apply_symm_apply] at hkm
      linarith
    · intro p₁ _ p₂ _ heq
      exact Prod.ext (σ.symm.injective (congrArg Prod.snd heq))
        (σ.symm.injective (congrArg Prod.fst heq))
    · intro q hq
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq
      refine ⟨(σ q.2, σ q.1), ?_, by ext <;> simp⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨hq.2, (card_posPairTies_eq_two_iff_rightKey_gt P hgp h_shat hleft hq.2).mpr ?_⟩
      exact hσ_mono hq.1
  have hrd := ray_ties_zeros_disjoint P hgp
  obtain ⟨s0, hs0_min, hs0_pos, hs0_lt3, hm0_pos, hm0_lt_s0⟩ :=
    hullMidpoint_zero_spec P hgp htop
  have hno_tie_L : ∀ t ∈ Set.Icc (0 : ℝ) (hullMidpoint P ⟨0, by omega⟩), ∀ x y : Fin 10, x ≠ y →
      dot2 (P.vec x) (gamma t) = topEnv P t → dot2 (P.vec y) (gamma t) = topEnv P t → False := by
    intro t ⟨ht0, htm⟩ x y hxy hx hy
    rcases eq_or_lt_of_le ht0 with rfl | ht_pos
    · exact (hrd.2.1 0 (by simp) x y).2 hxy (by linarith)
    · have ht_mem : t ∈ topTiePts P :=
        (hrd.1 t).mpr ⟨ht_pos, lt_of_le_of_lt htm (lt_trans hm0_lt_s0 hs0_lt3), x, y, hxy, hx, hy⟩
      have := hs0_min t ht_mem
      linarith
  obtain ⟨c₀, hc₀_prop⟩ := unique_top_on_Icc P hm0_pos hno_tie_L
  have hidx0 : hullIdx P ⟨0, by omega⟩ = c₀ := by
    have hex0 := exists_vec_eq_topEnv P (hullMidpoint P ⟨0, by omega⟩)
    have hspec0 : dot2 (P.vec (hullIdx P ⟨0, by omega⟩)) (gamma (hullMidpoint P ⟨0, by omega⟩)) =
        topEnv P (hullMidpoint P ⟨0, by omega⟩) := by
      unfold hullIdx; rw [dif_pos hex0]; exact Classical.choose_spec hex0
    have hc₀_top : dot2 (P.vec c₀) (gamma (hullMidpoint P ⟨0, by omega⟩)) =
        topEnv P (hullMidpoint P ⟨0, by omega⟩) := by
      obtain ⟨a, _⟩ := hex0
      by_cases hac : a = c₀
      · rwa [← hac]
      · exfalso
        have hlt := hc₀_prop (hullMidpoint P ⟨0, by omega⟩) (Set.right_mem_Icc.mpr hm0_pos.le) a hac
        have hsub : dot2 (P.vec c₀) (gamma (hullMidpoint P ⟨0, by omega⟩)) ≤
            topEnv P (hullMidpoint P ⟨0, by omega⟩) :=
          le_trans (dot2_vec_le_supportF P c₀ _)
            (Finset.le_sup' (fun k : Fin 5 => supportF P k _) (Finset.mem_univ (vecColor c₀)))
        linarith
    by_contra hne
    exact absurd hspec0 (ne_of_lt (hc₀_top ▸ hc₀_prop (hullMidpoint P ⟨0, by omega⟩)
      (Set.right_mem_Icc.mpr hm0_pos.le) (hullIdx P ⟨0, by omega⟩) hne))
  have hc0_col : hullColors P ⟨0, by omega⟩ = ⟨0, by omega⟩ := by
    unfold hullColors
    rw [hidx0]
    let col0 := vecColor c₀
    have h0_top : dot2 (P.vec c₀) (gamma 0) = topEnv P 0 := by
      obtain ⟨a, _⟩ := exists_vec_eq_topEnv P 0
      by_cases hac : a = c₀
      · rwa [← hac]
      · exfalso
        have hlt := hc₀_prop 0 (Set.left_mem_Icc.mpr hm0_pos.le) a hac
        have hsub : dot2 (P.vec c₀) (gamma 0) ≤ topEnv P 0 :=
          le_trans (dot2_vec_le_supportF P c₀ 0)
            (Finset.le_sup' (fun k : Fin 5 => supportF P k 0) (Finset.mem_univ col0))
        linarith
    have hcol0_pos : 0 < supportF P col0 0 := by
      have hpos0 := htop (le_refl 0) (by norm_num)
      have hsub : dot2 (P.vec c₀) (gamma 0) ≤ supportF P col0 0 := dot2_vec_le_supportF P c₀ 0
      linarith
    have hcol0_min : ∀ j : Fin 5, j ≠ col0 → leftKey P col0 < leftKey P j := by
      intro j hj
      have hj_lt : supportF P j 0 < supportF P col0 0 := by
        unfold supportF
        have h1 : dot2 (P.p1 j) (gamma 0) < dot2 (P.vec c₀) (gamma 0) := by
          rw [← P.vec_even j]
          refine hc₀_prop 0 (Set.left_mem_Icc.mpr hm0_pos.le) ⟨2 * j.val, by omega⟩ fun h => hj ?_
          have hvc : vecColor ⟨2 * j.val, by omega⟩ = col0 := congrArg vecColor h
          have hj_eq : vecColor ⟨2 * j.val, by omega⟩ = j := by ext; dsimp [vecColor]; omega
          exact hj_eq ▸ hvc
        have h2 : dot2 (P.p2 j) (gamma 0) < dot2 (P.vec c₀) (gamma 0) := by
          rw [← P.vec_odd j]
          refine hc₀_prop 0 (Set.left_mem_Icc.mpr hm0_pos.le) ⟨2 * j.val + 1, by omega⟩ fun h => hj ?_
          have hvc : vecColor ⟨2 * j.val + 1, by omega⟩ = col0 := congrArg vecColor h
          have hj_eq : vecColor ⟨2 * j.val + 1, by omega⟩ = j := by ext; dsimp [vecColor]; omega
          exact hj_eq ▸ hvc
        have hsub : dot2 (P.vec c₀) (gamma 0) ≤ supportF P col0 0 := dot2_vec_le_supportF P c₀ 0
        exact max_lt (lt_of_lt_of_le h1 hsub) (lt_of_lt_of_le h2 hsub)
      unfold leftKey; simp only [hcol0_pos, ↓reduceIte]
      split_ifs with hj0
      · linarith
      · have hlp := (supportF_posLeft_zero P hgp j hj0).1
        linarith
    by_contra hne0
    have hlt : leftKey P ⟨0, by omega⟩ < leftKey P col0 := hleft (Fin.pos_of_ne_zero hne0)
    have hmin := hcol0_min ⟨0, by omega⟩ (Ne.symm hne0)
    exact lt_asymm hlt hmin
  -- Right endpoint `3`: `hullColors P N = σ 4`
  obtain ⟨sN, hsN_max, hsN_pos, hsN_lt3, hsN_lt_mN, hmN_lt3⟩ :=
    hullMidpoint_last_spec P hgp htop
  have hno_tie_R : ∀ t ∈ Set.Icc (hullMidpoint P ⟨(topTiePts P).card, Nat.lt_succ_self _⟩) (3 : ℝ),
      ∀ x y : Fin 10, x ≠ y →
      dot2 (P.vec x) (gamma t) = topEnv P t → dot2 (P.vec y) (gamma t) = topEnv P t → False := by
    intro t ⟨htm, ht3⟩ x y hxy hx hy
    rcases eq_or_lt_of_le ht3 with rfl | ht_lt3
    · exact (hrd.2.1 3 (by simp) x y).2 hxy (by linarith)
    · have ht_mem : t ∈ topTiePts P :=
        (hrd.1 t).mpr ⟨lt_of_lt_of_le (lt_trans hsN_pos hsN_lt_mN) htm, ht_lt3, x, y, hxy, hx, hy⟩
      have := hsN_max t ht_mem
      linarith
  obtain ⟨c₁, hc₁_prop⟩ := unique_top_on_Icc P hmN_lt3 hno_tie_R
  have hidxN : hullIdx P ⟨(topTiePts P).card, Nat.lt_succ_self _⟩ = c₁ := by
    have hexN := exists_vec_eq_topEnv P (hullMidpoint P ⟨(topTiePts P).card, Nat.lt_succ_self _⟩)
    have hspecN : dot2 (P.vec (hullIdx P ⟨(topTiePts P).card, Nat.lt_succ_self _⟩))
        (gamma (hullMidpoint P ⟨(topTiePts P).card, Nat.lt_succ_self _⟩)) =
        topEnv P (hullMidpoint P ⟨(topTiePts P).card, Nat.lt_succ_self _⟩) := by
      unfold hullIdx; rw [dif_pos hexN]; exact Classical.choose_spec hexN
    have hc₁_top : dot2 (P.vec c₁) (gamma (hullMidpoint P ⟨(topTiePts P).card, Nat.lt_succ_self _⟩)) =
        topEnv P (hullMidpoint P ⟨(topTiePts P).card, Nat.lt_succ_self _⟩) := by
      obtain ⟨a, _⟩ := hexN
      by_cases hac : a = c₁
      · rwa [← hac]
      · exfalso
        have hlt := hc₁_prop (hullMidpoint P ⟨(topTiePts P).card, Nat.lt_succ_self _⟩)
          (Set.left_mem_Icc.mpr hmN_lt3.le) a hac
        have hsub : dot2 (P.vec c₁) (gamma (hullMidpoint P ⟨(topTiePts P).card, Nat.lt_succ_self _⟩)) ≤
            topEnv P (hullMidpoint P ⟨(topTiePts P).card, Nat.lt_succ_self _⟩) :=
          le_trans (dot2_vec_le_supportF P c₁ _)
            (Finset.le_sup' (fun k : Fin 5 => supportF P k _) (Finset.mem_univ (vecColor c₁)))
        linarith
    by_contra hne
    exact absurd hspecN (ne_of_lt (hc₁_top ▸ hc₁_prop (hullMidpoint P ⟨(topTiePts P).card, Nat.lt_succ_self _⟩)
      (Set.left_mem_Icc.mpr hmN_lt3.le) (hullIdx P ⟨(topTiePts P).card, Nat.lt_succ_self _⟩) hne))
  have hcN_col : hullColors P ⟨(topTiePts P).card, by omega⟩ = σ ⟨4, by omega⟩ := by
    unfold hullColors
    rw [show (⟨(topTiePts P).card, by omega⟩ : Fin ((topTiePts P).card + 1)) =
        ⟨(topTiePts P).card, Nat.lt_succ_self _⟩ from rfl, hidxN]
    let col1 := vecColor c₁
    have h3_top : dot2 (P.vec c₁) (gamma 3) = topEnv P 3 := by
      obtain ⟨a, _⟩ := exists_vec_eq_topEnv P 3
      by_cases hac : a = c₁
      · rwa [← hac]
      · exfalso
        have hlt := hc₁_prop 3 (Set.right_mem_Icc.mpr hmN_lt3.le) a hac
        have hsub : dot2 (P.vec c₁) (gamma 3) ≤ topEnv P 3 :=
          le_trans (dot2_vec_le_supportF P c₁ 3)
            (Finset.le_sup' (fun k : Fin 5 => supportF P k 3) (Finset.mem_univ col1))
        linarith
    have hcol1_pos : 0 < supportF P col1 3 := by
      have hpos3 := htop (by norm_num) le_rfl
      have hsub : dot2 (P.vec c₁) (gamma 3) ≤ supportF P col1 3 := dot2_vec_le_supportF P c₁ 3
      linarith
    have hcol1_max : ∀ j : Fin 5, j ≠ col1 → rightKey P j < rightKey P col1 := by
      intro j hj
      have hj_lt : supportF P j 3 < supportF P col1 3 := by
        unfold supportF
        have h1 : dot2 (P.p1 j) (gamma 3) < dot2 (P.vec c₁) (gamma 3) := by
          rw [← P.vec_even j]
          refine hc₁_prop 3 (Set.right_mem_Icc.mpr hmN_lt3.le) ⟨2 * j.val, by omega⟩ fun h => hj ?_
          have hvc : vecColor ⟨2 * j.val, by omega⟩ = col1 := congrArg vecColor h
          have hj_eq : vecColor ⟨2 * j.val, by omega⟩ = j := by ext; dsimp [vecColor]; omega
          exact hj_eq ▸ hvc
        have h2 : dot2 (P.p2 j) (gamma 3) < dot2 (P.vec c₁) (gamma 3) := by
          rw [← P.vec_odd j]
          refine hc₁_prop 3 (Set.right_mem_Icc.mpr hmN_lt3.le) ⟨2 * j.val + 1, by omega⟩ fun h => hj ?_
          have hvc : vecColor ⟨2 * j.val + 1, by omega⟩ = col1 := congrArg vecColor h
          have hj_eq : vecColor ⟨2 * j.val + 1, by omega⟩ = j := by ext; dsimp [vecColor]; omega
          exact hj_eq ▸ hvc
        have hsub : dot2 (P.vec c₁) (gamma 3) ≤ supportF P col1 3 := dot2_vec_le_supportF P c₁ 3
        exact max_lt (lt_of_lt_of_le h1 hsub) (lt_of_lt_of_le h2 hsub)
      unfold rightKey; simp only [hcol1_pos, ↓reduceIte]
      split_ifs with hj3
      · linarith
      · have hrp := (posInterval_eq_Ioo P hgp j).2.2.2.1
        linarith
    by_contra hne4
    have hlt_inv : σ.symm col1 < ⟨4, by omega⟩ :=
      lt_of_le_of_ne (Fin.is_le _) (fun h => hne4 (by rw [← h, Equiv.apply_symm_apply]))
    have hm := hσ_mono hlt_inv
    simp only [σ, Equiv.apply_symm_apply] at hm
    have hmax := hcol1_max (σ ⟨4, by omega⟩) (Ne.symm hne4)
    exact lt_asymm hm hmax
  exact ⟨h1, hc0_col, hcN_col⟩

/-- Complete elimination of `n_Ω = 6` (ruling out `(1, 6)` via `inv(σ) ≥ 4` and `6 + 4 > 9`). -/
theorem elim_n6_all (P : DualConfig) (hgp : IsGenPos P)
    (htop : ∀ {t : ℝ}, 0 ≤ t → t ≤ 3 → 0 < topEnv P t)
    (h_shat : ∀ m : Fin 5 → Bool, ∃ z : ℝ × ℝ, InOmega z ∧ RealizesDualMask P m z) :
    hullBlockCount P ≠ 6 := by
  intro hn6
  obtain ⟨τ, hleft⟩ := exists_left_sort_perm P hgp
  let P' := P.relabel τ
  have hgp' : IsGenPos P' := isGenPos_relabel P τ hgp
  have htop' : ∀ {t : ℝ}, 0 ≤ t → t ≤ 3 → 0 < topEnv P' t := fun ht0 ht3 => by
    rw [topEnv_relabel]; exact htop ht0 ht3
  have h_shat' : ∀ m : Fin 5 → Bool, ∃ z : ℝ × ℝ, InOmega z ∧ RealizesDualMask P' m z :=
    shat_relabel P τ h_shat
  have hn6' : hullBlockCount P' = 6 := by
    dsimp [P']; rw [hullBlockCount_relabel P τ hgp, hn6]
  have heq_ends := elim_n6_except_1_6 P' hgp' htop' h_shat' hn6'
  obtain ⟨hinv, hc0, hc_last⟩ := crossing_parity_inv P' hgp' htop' h_shat' hleft
  have hr4 : rightPerm P' ⟨4, by omega⟩ = ⟨0, by omega⟩ := by
    rw [← hc_last, ← heq_ends, hc0]
  have hge4 : 4 ≤ crossCountOfMult P' 2 := by
    rw [hinv]
    exact permInversions_ge_four_of_apply_four_eq_zero (rightPerm P') hr4
  have hlaw := conservation_law P' hgp' htop' h_shat'
  have hd1 := slice_surj_masks P' hgp' htop' h_shat' (q := 1) (by omega) (by omega)
  have hd2 := slice_surj_masks P' hgp' htop' h_shat' (q := 2) (by omega) (by omega)
  have hd3 := slice_surj_masks P' hgp' htop' h_shat' (q := 3) (by omega) (by omega)
  rw [hn6'] at hlaw
  omega

private lemma sortedG1_pos_of_unique_min (P : DualConfig) (t : ℝ) (c : Fin 5)
    (hmin : ∀ j : Fin 5, j ≠ c → clippedG P c t < clippedG P j t)
    (hpos : ∃ j : Fin 5, j ≠ c ∧ 0 < clippedG P j t) :
    0 < sortedG P 1 t := by
  unfold sortedG
  let l₀ := List.ofFn (fun i : Fin 5 => clippedG P i t)
  let l := l₀.mergeSort (· ≤ ·)
  have hperm : l.Perm l₀ := List.mergeSort_perm l₀ _
  have hpw : l.Pairwise (· ≤ ·) := List.pairwise_mergeSort' (· ≤ ·) l₀
  have hlen : l.length = 5 := by rw [hperm.length_eq]; simp [l₀]
  have hget1 : l.getD 1 0 = l[1] := by simp [List.getD_eq_getElem?_getD, hlen]
  change 0 < l.getD 1 0
  rw [hget1]
  by_contra hle0
  replace hle0 : l[1] ≤ 0 := not_lt.mp hle0
  have hl01 : l[0] ≤ l[1] := List.pairwise_iff_getElem.mp hpw 0 1 (by omega) (by omega) (by omega)
  have h_le_c : ∀ j : Fin 5, j ≠ c → 0 < clippedG P j t := by
    intro j hj
    obtain ⟨j₀, hj₀_ne, hj₀_pos⟩ := hpos
    by_cases hc_pos : 0 < clippedG P c t
    · exact lt_trans hc_pos (hmin j hj)
    · have h0_le : 0 ≤ clippedG P c t := le_max_right _ _
      have hc_zero : clippedG P c t = 0 := le_antisymm (not_lt.mp hc_pos) h0_le
      simpa [hc_zero] using hmin j hj
  have hc_ge : 2 ≤ l.countP (fun x => decide (x ≤ 0)) := by
    have h0 : l[0] ≤ 0 := le_trans hl01 hle0
    have hl_take : l = [l[0], l[1], l[2], l[3], l[4]] := by
      refine List.ext_getElem (by simp [hlen]) fun m hm1 hm2 => ?_
      have hm5 : m < 5 := by rw [← hlen]; exact hm1
      cases m with
      | zero => rfl
      | succ m => cases m with
        | zero => rfl
        | succ m => cases m with
          | zero => rfl
          | succ m => cases m with
            | zero => rfl
            | succ m => cases m with
              | zero => rfl
              | succ m => omega
    conv_rhs => rw [hl_take]
    simp [h0, hle0]
  have hc_le : l₀.countP (fun x => decide (x ≤ 0)) ≤ 1 := by
    dsimp [l₀]
    rw [List.ofFn_eq_map, List.countP_map]
    let p : Fin 5 → Bool := (fun x => decide (x ≤ 0)) ∘ (fun i => clippedG P i t)
    change (List.finRange 5).countP p ≤ 1
    rw [List.countP_eq_length_filter]
    have hnd : ((List.finRange 5).filter p).Nodup := (List.nodup_finRange 5).filter _
    rw [← List.toFinset_card_of_nodup hnd]
    have hsub : ((List.finRange 5).filter p).toFinset ⊆ {c} := by
      intro i hi
      simp only [List.mem_toFinset, List.mem_filter, List.mem_finRange, true_and, p,
        Function.comp_apply, decide_eq_true_eq] at hi
      rw [Finset.mem_singleton]
      by_contra hne
      linarith [h_le_c i hne]
    exact le_trans (Finset.card_le_card hsub) (by simp)
  rw [hperm.countP_eq] at hc_ge
  omega

private lemma sortedG_zero_eq_one_of_tie_min (P : DualConfig) (t : ℝ) {c₁ c₂ : Fin 5}
    (hne : c₁ ≠ c₂) (htie : clippedG P c₁ t = clippedG P c₂ t)
    (hle : ∀ k : Fin 5, clippedG P c₁ t ≤ clippedG P k t) :
    sortedG P 0 t = sortedG P 1 t := by
  unfold sortedG
  let l₀ := List.ofFn (fun i : Fin 5 => clippedG P i t)
  let l := l₀.mergeSort (· ≤ ·)
  have hperm : l.Perm l₀ := List.mergeSort_perm l₀ _
  have hpw : l.Pairwise (· ≤ ·) := List.pairwise_mergeSort' (· ≤ ·) l₀
  have hlen : l.length = 5 := by rw [hperm.length_eq]; simp [l₀]
  have hget0 : l.getD 0 0 = l[0] := by simp [List.getD_eq_getElem?_getD, hlen]
  have hget1 : l.getD 1 0 = l[1] := by simp [List.getD_eq_getElem?_getD, hlen]
  change l.getD 0 0 = l.getD 1 0
  rw [hget0, hget1]
  let v := clippedG P c₁ t
  have hl0_eq : l[0] = v := by
    have hv_mem : v ∈ l := hperm.mem_iff.mpr (List.mem_ofFn.mpr ⟨c₁, rfl⟩)
    obtain ⟨m, hm, hmeq⟩ := List.mem_iff_getElem.mp hv_mem
    have hl0_le : l[0] ≤ v := by
      rcases Nat.eq_zero_or_pos m with rfl | hm_pos
      · exact le_of_eq hmeq
      · rw [← hmeq]; exact List.pairwise_iff_getElem.mp hpw 0 m (by omega) hm hm_pos
    have hv_le : v ≤ l[0] := by
      have h0_lt : 0 < l.length := by rw [hlen]; omega
      have h0_mem : l[0] ∈ l := List.getElem_mem h0_lt
      have hm0 : l[0] ∈ l₀ := hperm.mem_iff.mp h0_mem
      obtain ⟨k, hk⟩ := List.mem_ofFn.mp hm0
      rw [← hk]; exact hle k
    exact le_antisymm hl0_le hv_le
  have hl01 : l[0] ≤ l[1] := List.pairwise_iff_getElem.mp hpw 0 1 (by omega) (by omega) (by omega)
  refine le_antisymm hl01 ?_
  by_contra hgt
  replace hgt : v < l[1] := by rw [← hl0_eq]; exact not_le.mp hgt
  have hl_take : l = [l[0], l[1], l[2], l[3], l[4]] := by
    refine List.ext_getElem (by simpa using hlen) ?_
    intro i hi1 hi2
    have hi5 : i < 5 := by omega
    interval_cases i <;> rfl
  have hpw_ge1 : ∀ (m : ℕ) (_hm1 : 1 ≤ m) (hm5 : m < 5), v < l[m]'(by rw [hlen]; omega) := by
    intro m hm1 hm5
    rcases eq_or_lt_of_le hm1 with rfl | hm_gt
    · exact hgt
    · exact lt_of_lt_of_le hgt (List.pairwise_iff_getElem.mp hpw 1 m (by omega) (by omega) hm_gt)
  have hc_le : l.countP (fun x => decide (x ≤ v)) ≤ 1 := by
    rw [hl_take]
    have h1 : ¬ l[1] ≤ v := not_le.mpr (hpw_ge1 1 (by omega) (by omega))
    have h2 : ¬ l[2] ≤ v := not_le.mpr (hpw_ge1 2 (by omega) (by omega))
    have h3 : ¬ l[3] ≤ v := not_le.mpr (hpw_ge1 3 (by omega) (by omega))
    have h4 : ¬ l[4] ≤ v := not_le.mpr (hpw_ge1 4 (by omega) (by omega))
    simp [hl0_eq, h1, h2, h3, h4]
  have hc_ge : 2 ≤ l₀.countP (fun x => decide (x ≤ v)) := by
    dsimp [l₀]
    rw [List.ofFn_eq_map, List.countP_map]
    let p : Fin 5 → Bool := (fun x => decide (x ≤ v)) ∘ (fun i => clippedG P i t)
    change 2 ≤ (List.finRange 5).countP p
    rw [List.countP_eq_length_filter]
    have hnd : ((List.finRange 5).filter p).Nodup := (List.nodup_finRange 5).filter _
    rw [← List.toFinset_card_of_nodup hnd]
    have hsub : {c₁, c₂} ⊆ ((List.finRange 5).filter p).toFinset := by
      intro i hi
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi
      simp only [List.mem_toFinset, List.mem_filter, List.mem_finRange, true_and, p,
        Function.comp_apply, decide_eq_true_eq]
      rcases hi with rfl | rfl
      · exact le_rfl
      · exact le_of_eq htie.symm
    exact le_trans (by rw [Finset.card_pair hne]) (Finset.card_le_card hsub)
  rw [← hperm.countP_eq] at hc_ge
  omega

private lemma left_min_4_witness_of_dom (P : DualConfig) (hgp : IsGenPos P)
    (hleft : StrictMono (leftKey P))
    (h04_ap : posLeft P 4 < apexRay P 0)
    (h_right_dom : ∀ j : Fin 5, j < (4 : Fin 5) → apexRay P 0 < posRight P j) :
    ∃ τ₁ : ℝ, 0 < τ₁ ∧ τ₁ < apexRay P 0 ∧
      (∀ j : Fin 5, j ≠ 4 → clippedG P 4 τ₁ < clippedG P j τ₁) ∧
      0 < sortedG P 1 τ₁ := by
  have hap0 := (supportF_branch_switch P hgp).2 0
  by_cases h4 : 0 < supportF P 4 0
  · have hj_pos : ∀ j : Fin 5, j ≠ 4 → 0 < supportF P j 0 ∧ supportF P 4 0 < supportF P j 0 := by
      intro j hj
      have hj_lt : j < 4 := lt_of_le_of_ne (Fin.is_le j) hj
      have hlk := hleft hj_lt
      unfold leftKey at hlk
      simp only [h4, ↓reduceIte] at hlk
      split_ifs at hlk with hj0
      · exact ⟨hj0, by linarith⟩
      · exfalso
        have hpi := (posInterval_eq_Ioo P hgp j).1
        linarith
    have hopen : IsOpen {t : ℝ | 0 < supportF P 4 t ∧ ∀ j : Fin 5, j ≠ 4 → supportF P 4 t < supportF P j t} := by
      have h1 : IsOpen {t : ℝ | 0 < supportF P 4 t} :=
        isOpen_lt continuous_const (supportF_continuous P 4)
      have h2 : IsOpen (⋂ j : Fin 5, if j ≠ 4 then {t : ℝ | supportF P 4 t < supportF P j t} else Set.univ) := by
        refine isOpen_iInter_of_finite fun j => ?_
        split_ifs
        · exact isOpen_lt (supportF_continuous P 4) (supportF_continuous P j)
        · exact isOpen_univ
      convert IsOpen.inter h1 h2 using 1
      ext t; simp [Set.mem_iInter]
    obtain ⟨δ, hδ, hsub⟩ := Metric.isOpen_iff.mp hopen 0 ⟨h4, fun j hj => (hj_pos j hj).2⟩
    let τ₁ : ℝ := min (δ / 2) (apexRay P 0 / 2)
    have hτ₁_pos : 0 < τ₁ := lt_min (by linarith) (by linarith [hap0.1])
    have hτ₁_lt : τ₁ < apexRay P 0 := lt_of_le_of_lt (min_le_right _ _) (by linarith [hap0.1])
    have hτ₁_ball : τ₁ ∈ Metric.ball (0 : ℝ) δ := by
      rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hτ₁_pos]
      exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
    obtain ⟨hf4, hlt_all⟩ := Set.mem_setOf.mp (hsub hτ₁_ball)
    have hclip : ∀ j : Fin 5, j ≠ 4 → clippedG P 4 τ₁ < clippedG P j τ₁ := by
      intro j hj
      have hj_gt := hlt_all j hj
      have hj_pos' := lt_trans hf4 hj_gt
      unfold clippedG
      rw [max_eq_left (le_of_lt hf4), max_eq_left (le_of_lt hj_pos')]
      exact hj_gt
    exact ⟨τ₁, hτ₁_pos, hτ₁_lt, hclip,
      sortedG1_pos_of_unique_min P τ₁ 4 hclip ⟨0, by decide, by
        have := hlt_all 0 (by decide)
        unfold clippedG; linarith [le_max_left (supportF P 0 τ₁) 0]⟩⟩
  · obtain ⟨hp4_pos, hf4_zero⟩ := supportF_posLeft_zero P hgp 4 h4
    have hclip : ∀ j : Fin 5, j ≠ 4 → clippedG P 4 (posLeft P 4) < clippedG P j (posLeft P 4) := by
      intro j hj
      have hj_lt : j < 4 := lt_of_le_of_ne (Fin.is_le j) hj
      have hpj_lt : posLeft P j < posLeft P 4 := by
        by_cases hj0 : 0 < supportF P j 0
        · rw [posLeft_eq_zero_of_pos_at_zero P hgp j hj0]; exact hp4_pos
        · have hlk := hleft hj_lt
          unfold leftKey at hlk
          simp only [hj0, h4, ↓reduceIte] at hlk
          exact hlk
      have hfj_pos : 0 < supportF P j (posLeft P 4) :=
        ((posInterval_eq_Ioo P hgp j).2.2.2.2 (posLeft P 4)).mpr
          ⟨hpj_lt, lt_trans h04_ap (h_right_dom j hj_lt)⟩ |>.2.2
      unfold clippedG
      rw [hf4_zero, max_self, max_eq_left (le_of_lt hfj_pos)]
      exact hfj_pos
    exact ⟨posLeft P 4, hp4_pos, h04_ap, hclip,
      sortedG1_pos_of_unique_min P (posLeft P 4) 4 hclip ⟨0, by decide, hclip 0 (by decide) |>.trans_le' (le_max_right _ _)⟩⟩

private lemma left_min_4_witness (P : DualConfig) (hgp : IsGenPos P)
    (h_shat : ∀ m : Fin 5 → Bool, ∃ z : ℝ × ℝ, InOmega z ∧ RealizesDualMask P m z)
    (hleft : StrictMono (leftKey P))
    (h_edges : ∀ i : Fin 5, i < (4 : Fin 5) → (i, (4 : Fin 5)) ∈ threeCrossGraph P) :
    ∃ τ₁ : ℝ, 0 < τ₁ ∧ τ₁ < apexRay P 0 ∧
      (∀ j : Fin 5, j ≠ 4 → clippedG P 4 τ₁ < clippedG P j τ₁) ∧
      0 < sortedG P 1 τ₁ := by
  have h04 := three_crossing_structure P hgp h_shat hleft (h_edges 0 (by decide))
  refine left_min_4_witness_of_dom P hgp hleft h04.1 fun j hj => ?_
  have hj4 := three_crossing_structure P hgp h_shat hleft (h_edges j hj)
  exact lt_trans h04.2.1 hj4.2.2.1

private lemma left_cert_witness (P : DualConfig) (hgp : IsGenPos P)
    (h_shat : ∀ m : Fin 5 → Bool, ∃ z : ℝ × ℝ, InOmega z ∧ RealizesDualMask P m z)
    (hleft : StrictMono (leftKey P))
    (he0 : (⟨0, by omega⟩, ⟨4, by omega⟩) ∈ threeCrossGraph P)
    (he1 : (⟨1, by omega⟩, ⟨4, by omega⟩) ∈ threeCrossGraph P)
    (he2 : (⟨2, by omega⟩, ⟨4, by omega⟩) ∈ threeCrossGraph P) :
    ∃ M : Finset (Fin 5), (M = ({4} : Finset (Fin 5)) ∨ M = ({3, 4} : Finset (Fin 5))) ∧
      cutSplitWitness P M := by
  have h04 := three_crossing_structure P hgp h_shat hleft he0
  have h14 := three_crossing_structure P hgp h_shat hleft he1
  have h24 := three_crossing_structure P hgp h_shat hleft he2
  let t₀ := apexRay P 0
  let t₄ := apexRay P 4
  have ht0_lt_t4 : t₀ < t₄ := h04.2.1
  have hap0 := (supportF_branch_switch P hgp).2 0
  have hap4 := (supportF_branch_switch P hgp).2 4
  have h34_ne : clippedG P 3 t₄ ≠ clippedG P 4 t₄ :=
    clippedG_ne_at_apexRay P hgp (Fin.ne_of_val_ne (by decide))
  rcases lt_or_gt_of_ne h34_ne with h34 | h43
  · -- Case `clippedG P 3 t₄ < clippedG P 4 t₄`: `M = {3, 4}`
    refine ⟨({3, 4} : Finset (Fin 5)), Or.inr rfl, ?_⟩
    have hM_cut_t4 : clippedCutPotential P ({3, 4} : Finset (Fin 5)) t₄ = 0 := by
      unfold clippedCutPotential
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      rintro ⟨u, v⟩ hp
      simp only [Finset.mem_product, Finset.mem_sdiff, Finset.mem_univ, true_and,
        Finset.mem_insert, Finset.mem_singleton] at hp
      have hp1_le : clippedG P u t₄ ≤ clippedG P 4 t₄ := by
        rcases hp.1 with rfl | rfl
        · exact le_of_lt h34
        · exact le_rfl
      have hp2_gt : clippedG P 4 t₄ < clippedG P v t₄ := by
        fin_cases v
        · exact h04.2.2.2.2.1
        · exact h14.2.2.2.2.1
        · exact h24.2.2.2.2.1
        · exact absurd (Or.inl rfl) hp.2
        · exact absurd (Or.inr rfl) hp.2
      exact not_le.mpr (lt_of_le_of_lt hp1_le hp2_gt)
    have hM_cut_t0 : 0 < clippedCutPotential P ({3, 4} : Finset (Fin 5)) t₀ := by
      refine Finset.card_pos.mpr ⟨((4 : Fin 5), (0 : Fin 5)), ?_⟩
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_sdiff, Finset.mem_univ,
        true_and, Finset.mem_insert, Finset.mem_singleton]
      exact ⟨by simp, le_of_lt h04.2.2.2.1⟩
    have h_right_lt2 : ∀ v : Fin 5, v < 3 → t₀ < posRight P v := by
      intro v hv
      fin_cases v
      · exact lt_trans h04.2.1 h04.2.2.1
      · exact lt_trans h04.2.1 h14.2.2.1
      · exact lt_trans h04.2.1 h24.2.2.1
      · exact absurd hv (by decide)
      · exact absurd hv (by decide)
    have hτ₁_ex : ∃ τ₁ : ℝ, 0 < τ₁ ∧ τ₁ < t₀ ∧
        clippedCutPotential P ({3, 4} : Finset (Fin 5)) τ₁ = 0 := by
      by_cases h3_0 : 0 < supportF P 3 0
      · have hv_gt : ∀ v : Fin 5, v < 3 → 0 < supportF P v 0 ∧ supportF P 3 0 < supportF P v 0 := by
          intro v hv
          have hlk := hleft (show v < 3 from hv)
          unfold leftKey at hlk
          simp only [h3_0, ↓reduceIte] at hlk
          split_ifs at hlk with hv0
          · exact ⟨hv0, by linarith⟩
          · exfalso; linarith [(posInterval_eq_Ioo P hgp v).1]
        have h4_lt : supportF P 4 0 < supportF P 3 0 := by
          have hlk := hleft (show (3 : Fin 5) < 4 by decide)
          unfold leftKey at hlk
          simp only [h3_0, ↓reduceIte] at hlk
          split_ifs at hlk with h40
          · linarith
          · exact lt_of_le_of_lt (not_lt.mp h40) h3_0
        have hopen : IsOpen {t : ℝ | 0 < supportF P 3 t ∧
            supportF P 4 t < supportF P 3 t ∧
            ∀ v : Fin 5, v < 3 → supportF P 3 t < supportF P v t} := by
          have h1 : IsOpen {t : ℝ | 0 < supportF P 3 t} :=
            isOpen_lt continuous_const (supportF_continuous P 3)
          have h2 : IsOpen {t : ℝ | supportF P 4 t < supportF P 3 t} :=
            isOpen_lt (supportF_continuous P 4) (supportF_continuous P 3)
          have h3 : IsOpen (⋂ v : Fin 5, if v < 3 then {t : ℝ | supportF P 3 t < supportF P v t} else Set.univ) := by
            refine isOpen_iInter_of_finite fun v => ?_
            split_ifs
            · exact isOpen_lt (supportF_continuous P 3) (supportF_continuous P v)
            · exact isOpen_univ
          convert IsOpen.inter h1 (IsOpen.inter h2 h3) using 1
          ext t; simp [Set.mem_iInter]
        obtain ⟨δ, hδ, hsub⟩ := Metric.isOpen_iff.mp hopen 0
          ⟨h3_0, h4_lt, fun v hv => (hv_gt v hv).2⟩
        let τ₁ : ℝ := min (δ / 2) (t₀ / 2)
        have hτ₁_pos : 0 < τ₁ := lt_min (by linarith) (by linarith [hap0.1])
        have hτ₁_lt : τ₁ < t₀ := lt_of_le_of_lt (min_le_right _ _) (by linarith [hap0.1])
        have hτ₁_ball : τ₁ ∈ Metric.ball (0 : ℝ) δ := by
          rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hτ₁_pos]
          exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
        obtain ⟨hf3, hf43, hlt_v⟩ := Set.mem_setOf.mp (hsub hτ₁_ball)
        refine ⟨τ₁, hτ₁_pos, hτ₁_lt, ?_⟩
        unfold clippedCutPotential
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        rintro ⟨u, v⟩ hp
        simp only [Finset.mem_product, Finset.mem_sdiff, Finset.mem_univ, true_and,
          Finset.mem_insert, Finset.mem_singleton] at hp
        have hp2_lt3 : v < 3 := by
          fin_cases v
          · decide
          · decide
          · decide
          · exact absurd (Or.inl rfl) hp.2
          · exact absurd (Or.inr rfl) hp.2
        have hv_gt' := hlt_v v hp2_lt3
        have hv_pos := lt_trans hf3 hv_gt'
        have hp1_le : clippedG P u τ₁ ≤ supportF P 3 τ₁ := by
          rcases hp.1 with rfl | rfl
          · exact le_of_eq (max_eq_left (le_of_lt hf3))
          · unfold clippedG; exact max_le (le_of_lt hf43) (le_of_lt hf3)
        have hp2_eq : clippedG P v τ₁ = supportF P v τ₁ := max_eq_left (le_of_lt hv_pos)
        exact not_le.mpr (lt_of_le_of_lt hp1_le (by linarith))
      · obtain ⟨hp3_pos, hf3_zero⟩ := supportF_posLeft_zero P hgp 3 h3_0
        have h4_0 : ¬ 0 < supportF P 4 0 := by
          intro h4_pos
          have hlk := hleft (show (3 : Fin 5) < 4 by decide)
          unfold leftKey at hlk
          simp only [h3_0, h4_pos, ↓reduceIte] at hlk
          linarith [(posInterval_eq_Ioo P hgp 3).1]
        have hp3_lt_p4 : posLeft P 3 < posLeft P 4 := by
          have hlk := hleft (show (3 : Fin 5) < 4 by decide)
          unfold leftKey at hlk
          simp only [h3_0, h4_0, ↓reduceIte] at hlk
          exact hlk
        have hp3_lt_t0 : posLeft P 3 < t₀ := lt_trans hp3_lt_p4 h04.1
        have hf4_at_p3 : supportF P 4 (posLeft P 3) ≤ 0 := by
          by_contra hpos; replace hpos : 0 < supportF P 4 (posLeft P 3) := not_le.mp hpos
          have hm := ((posInterval_eq_Ioo P hgp 4).2.2.2.2 (posLeft P 3)).mp
            ⟨hp3_pos, lt_trans hp3_lt_t0 (lt_trans hap0.2.1 (by norm_num)), hpos⟩
          linarith [hm.1]
        by_cases h2_0 : 0 < supportF P 2 0
        · refine ⟨posLeft P 3, hp3_pos, hp3_lt_t0, ?_⟩
          unfold clippedCutPotential
          rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
          rintro ⟨u, v⟩ hp
          simp only [Finset.mem_product, Finset.mem_sdiff, Finset.mem_univ, true_and,
            Finset.mem_insert, Finset.mem_singleton] at hp
          have hp2_lt3 : v < 3 := by
            fin_cases v
            · decide
            · decide
            · decide
            · exact absurd (Or.inl rfl) hp.2
            · exact absurd (Or.inr rfl) hp.2
          have hp2_0 : 0 < supportF P v 0 := by
            rcases eq_or_lt_of_le (show v ≤ 2 by fin_cases v <;> simp at hp2_lt3 ⊢ <;> decide) with rfl | hv2
            · exact h2_0
            · have hlk := hleft hv2
              unfold leftKey at hlk
              simp only [h2_0, ↓reduceIte] at hlk
              split_ifs at hlk with hv0
              · exact hv0
              · exfalso; linarith [(posInterval_eq_Ioo P hgp v).1]
          have hp2_posL : posLeft P v = 0 := posLeft_eq_zero_of_pos_at_zero P hgp v hp2_0
          have hp2_pos : 0 < supportF P v (posLeft P 3) :=
            ((posInterval_eq_Ioo P hgp v).2.2.2.2 (posLeft P 3)).mpr
              ⟨hp2_posL ▸ hp3_pos, lt_trans hp3_lt_t0 (h_right_lt2 v hp2_lt3)⟩ |>.2.2
          have hp1_zero : clippedG P u (posLeft P 3) = 0 := by
            rcases hp.1 with rfl | rfl
            · unfold clippedG; rw [hf3_zero, max_self]
            · unfold clippedG; exact max_eq_right hf4_at_p3
          have hp2_clip : 0 < clippedG P v (posLeft P 3) :=
            lt_of_lt_of_le hp2_pos (le_max_left _ _)
          exact not_le.mpr (by linarith)
        · obtain ⟨hp2_pos, _⟩ := supportF_posLeft_zero P hgp 2 h2_0
          have hp2_lt_p3 : posLeft P 2 < posLeft P 3 := by
            have hlk := hleft (show (2 : Fin 5) < 3 by decide)
            unfold leftKey at hlk
            simp only [h2_0, h3_0, ↓reduceIte] at hlk
            exact hlk
          let τ₁ : ℝ := (posLeft P 2 + posLeft P 3) / 2
          have hτ₁_gt2 : posLeft P 2 < τ₁ := by dsimp [τ₁]; linarith
          have hτ₁_lt3 : τ₁ < posLeft P 3 := by dsimp [τ₁]; linarith
          have hτ₁_pos : 0 < τ₁ := lt_trans hp2_pos hτ₁_gt2
          have hτ₁_lt_t0 : τ₁ < t₀ := lt_trans hτ₁_lt3 hp3_lt_t0
          have hτ₁_lt3_bound : τ₁ < 3 := lt_trans hτ₁_lt_t0 (lt_trans hap0.2.1 (by norm_num))
          refine ⟨τ₁, hτ₁_pos, hτ₁_lt_t0, ?_⟩
          unfold clippedCutPotential
          rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
          rintro ⟨u, v⟩ hp
          simp only [Finset.mem_product, Finset.mem_sdiff, Finset.mem_univ, true_and,
            Finset.mem_insert, Finset.mem_singleton] at hp
          have hp2_lt3 : v < 3 := by
            fin_cases v
            · decide
            · decide
            · decide
            · exact absurd (Or.inl rfl) hp.2
            · exact absurd (Or.inr rfl) hp.2
          have hp2_posL_le : posLeft P v ≤ posLeft P 2 := by
            rcases eq_or_lt_of_le (show v ≤ 2 by fin_cases v <;> simp at hp2_lt3 ⊢ <;> decide) with rfl | hv2
            · exact le_rfl
            · by_cases hv0 : 0 < supportF P v 0
              · rw [posLeft_eq_zero_of_pos_at_zero P hgp v hv0]; exact hp2_pos.le
              · have hlk := hleft hv2
                unfold leftKey at hlk
                simp only [hv0, h2_0, ↓reduceIte] at hlk
                exact hlk.le
          have hp2_pos : 0 < supportF P v τ₁ :=
            ((posInterval_eq_Ioo P hgp v).2.2.2.2 τ₁).mpr
              ⟨lt_of_le_of_lt hp2_posL_le hτ₁_gt2, lt_trans hτ₁_lt_t0 (h_right_lt2 v hp2_lt3)⟩ |>.2.2
          have hp1_zero : clippedG P u τ₁ = 0 := by
            rcases hp.1 with rfl | rfl
            · unfold clippedG; refine max_eq_right (not_lt.mp fun hpos => ?_)
              have hm := ((posInterval_eq_Ioo P hgp 3).2.2.2.2 τ₁).mp ⟨hτ₁_pos, hτ₁_lt3_bound, hpos⟩
              linarith [hm.1]
            · unfold clippedG; refine max_eq_right (not_lt.mp fun hpos => ?_)
              have hm := ((posInterval_eq_Ioo P hgp 4).2.2.2.2 τ₁).mp ⟨hτ₁_pos, hτ₁_lt3_bound, hpos⟩
              linarith [hm.1]
          have hp2_clip : 0 < clippedG P v τ₁ :=
            lt_of_lt_of_le hp2_pos (le_max_left _ _)
          exact not_le.mpr (by linarith)
    obtain ⟨τ₁, hτ₁_pos, hτ₁_t0, hM_cut_t1⟩ := hτ₁_ex
    exact ⟨τ₁, t₀, t₄, hτ₁_pos, hτ₁_t0, ht0_lt_t4, lt_trans hap4.2.1 (by norm_num),
      hM_cut_t1, hM_cut_t0, hM_cut_t4⟩
  · -- Case `clippedG P 4 t₄ < clippedG P 3 t₄`: `M = {4}`
    refine ⟨({4} : Finset (Fin 5)), Or.inl rfl, ?_⟩
    have ht4_pos3 : 0 < supportF P 3 t₄ := by
      by_contra hle; replace hle : supportF P 3 t₄ ≤ 0 := not_lt.mp hle
      have : clippedG P 3 t₄ = 0 := max_eq_right hle
      have ht4_clip_pos : 0 < clippedG P 4 t₄ := lt_of_lt_of_le hap4.2.2.1 (le_max_left _ _)
      linarith
    have ht4_in3 : t₄ < posRight P 3 :=
      ((posInterval_eq_Ioo P hgp 3).2.2.2.2 t₄).mp
        ⟨lt_trans (by norm_num) hap4.1, lt_trans hap4.2.1 (by norm_num), ht4_pos3⟩ |>.2
    have h_right_dom : ∀ j : Fin 5, j < (4 : Fin 5) → t₀ < posRight P j := by
      intro j hj
      fin_cases j
      · exact lt_trans h04.2.1 h04.2.2.1
      · exact lt_trans h04.2.1 h14.2.2.1
      · exact lt_trans h04.2.1 h24.2.2.1
      · exact lt_trans ht0_lt_t4 ht4_in3
      · exact absurd hj (by decide)
    obtain ⟨τ₁, hτ₁_pos, hτ₁_t0, hτ₁_min, _⟩ :=
      left_min_4_witness_of_dom P hgp hleft h04.1 h_right_dom
    have hM_cut_t1 : clippedCutPotential P ({4} : Finset (Fin 5)) τ₁ = 0 := by
      unfold clippedCutPotential
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      rintro ⟨u, v⟩ hp
      simp only [Finset.mem_product, Finset.mem_sdiff, Finset.mem_univ, true_and,
        Finset.mem_singleton] at hp
      rw [hp.1]
      exact not_le.mpr (hτ₁_min v hp.2)
    have hM_cut_t0 : 0 < clippedCutPotential P ({4} : Finset (Fin 5)) t₀ := by
      refine Finset.card_pos.mpr ⟨((4 : Fin 5), (0 : Fin 5)), ?_⟩
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_sdiff, Finset.mem_univ,
        true_and, Finset.mem_singleton]
      exact ⟨by simp, le_of_lt h04.2.2.2.1⟩
    have hM_cut_t4 : clippedCutPotential P ({4} : Finset (Fin 5)) t₄ = 0 := by
      unfold clippedCutPotential
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      rintro ⟨u, v⟩ hp
      simp only [Finset.mem_product, Finset.mem_sdiff, Finset.mem_univ, true_and,
        Finset.mem_singleton] at hp
      rw [hp.1]
      have hlt : clippedG P 4 t₄ < clippedG P v t₄ := by
        fin_cases v
        · exact h04.2.2.2.2.1
        · exact h14.2.2.2.2.1
        · exact h24.2.2.2.2.1
        · exact h43
        · exact absurd rfl hp.2
      exact not_le.mpr hlt
    exact ⟨τ₁, t₀, t₄, hτ₁_pos, hτ₁_t0, ht0_lt_t4, lt_trans hap4.2.1 (by norm_num),
      hM_cut_t1, hM_cut_t0, hM_cut_t4⟩

/-- Left Duplicate-Cell Certificate at `t_5` when `{1,5}, {2,5}, {3,5} ∈ E(G_3^+)`. -/
theorem left_certificate (P : DualConfig) (hgp : IsGenPos P)
    (htop : ∀ {t : ℝ}, 0 ≤ t → t ≤ 3 → 0 < topEnv P t)
    (h_shat : ∀ m : Fin 5 → Bool, ∃ z : ℝ × ℝ, InOmega z ∧ RealizesDualMask P m z)
    (hleft : StrictMono (leftKey P))
    (he0 : (⟨0, by omega⟩, ⟨4, by omega⟩) ∈ threeCrossGraph P)
    (he1 : (⟨1, by omega⟩, ⟨4, by omega⟩) ∈ threeCrossGraph P)
    (he2 : (⟨2, by omega⟩, ⟨4, by omega⟩) ∈ threeCrossGraph P) :
    1 ≤ sliceExcess P 1 + sliceExcess P 2 := by
  obtain ⟨M, hM_cases, τ₁, τ₂, τ₃, h0, h12, h23, h3, hc1, hc2, hc3⟩ :=
    left_cert_witness P hgp h_shat hleft he0 he1 he2
  have hd1 := slice_surj_masks P hgp htop h_shat (q := 1) (by omega) (by omega)
  have hd2 := slice_surj_masks P hgp htop h_shat (q := 2) (by omega) (by omega)
  rcases hM_cases with rfl | rfl
  · have hM1 := duplicate_slice_of_cutPotential P hgp htop h_shat ({4} : Finset (Fin 5))
      (by simp) (by simp) h0 h12 h23 h3 hc1 hc2 hc3
    simp only [Finset.card_singleton] at hM1; omega
  · have hM2 := duplicate_slice_of_cutPotential P hgp htop h_shat ({3, 4} : Finset (Fin 5))
      (by simp) (by simp) h0 h12 h23 h3 hc1 hc2 hc3
    rw [Finset.card_pair (by decide)] at hM2; omega

private lemma right_cert_witness (P : DualConfig) (hgp : IsGenPos P)
    (h_shat : ∀ m : Fin 5 → Bool, ∃ z : ℝ × ℝ, InOmega z ∧ RealizesDualMask P m z)
    (he2 : (min (rightPerm P ⟨0, by omega⟩) (rightPerm P ⟨2, by omega⟩),
            max (rightPerm P ⟨0, by omega⟩) (rightPerm P ⟨2, by omega⟩)) ∈ threeCrossGraph P)
    (he3 : (min (rightPerm P ⟨0, by omega⟩) (rightPerm P ⟨3, by omega⟩),
            max (rightPerm P ⟨0, by omega⟩) (rightPerm P ⟨3, by omega⟩)) ∈ threeCrossGraph P)
    (he4 : (min (rightPerm P ⟨0, by omega⟩) (rightPerm P ⟨4, by omega⟩),
            max (rightPerm P ⟨0, by omega⟩) (rightPerm P ⟨4, by omega⟩)) ∈ threeCrossGraph P) :
    ∃ M : Finset (Fin 5),
      (M = {rightPerm P ⟨0, by omega⟩} ∨
       M = {rightPerm P ⟨0, by omega⟩, rightPerm P ⟨1, by omega⟩}) ∧
      cutSplitWitness P M := by
  let rev5 : Equiv.Perm (Fin 5) :=
    { toFun := fun r => ⟨4 - r.val, by omega⟩
      invFun := fun r => ⟨4 - r.val, by omega⟩
      left_inv := fun r => by ext; dsimp; omega
      right_inv := fun r => by ext; dsimp; omega }
  let ρ : Equiv.Perm (Fin 5) := rev5.trans (rightPerm P)
  let P' := P.swap.relabel ρ
  have hgp_sw : IsGenPos P.swap := (P.swap_spec).2.1.mpr hgp
  have hgp' : IsGenPos P' := isGenPos_relabel P.swap ρ hgp_sw
  have h_shat_sw : ∀ m : Fin 5 → Bool, ∃ z : ℝ × ℝ, InOmega z ∧ RealizesDualMask P.swap m z := by
    intro m; obtain ⟨z, hz, hm⟩ := h_shat m
    exact ⟨swap2 z, inOmega_swap2 hz, (P.swap_spec).2.2 m z |>.mpr hm⟩
  have h_shat' : ∀ m : Fin 5 → Bool, ∃ z : ℝ × ℝ, InOmega z ∧ RealizesDualMask P' m z :=
    shat_relabel P.swap ρ h_shat_sw
  have hleft' : StrictMono (leftKey P') := by
    intro r₁ r₂ hr
    rw [leftKey_relabel, leftKey_relabel, (boundaryKey_swap P hgp (ρ r₁)).1,
      (boundaryKey_swap P hgp (ρ r₂)).1]
    have hrev : rev5 r₂ < rev5 r₁ := by
      show (4 - r₂.val : ℕ) < 4 - r₁.val
      have : r₁.val < r₂.val := hr
      omega
    have hsm := rightPerm_strictMono P hgp hrev
    dsimp [ρ]; linarith
  have he0' : (⟨0, by omega⟩, ⟨4, by omega⟩) ∈ threeCrossGraph P' := by
    rw [threeCrossGraph_relabel P.swap ρ (by decide), threeCrossGraph_swap]
    simpa [ρ, rev5, min_comm, max_comm] using he4
  have he1' : (⟨1, by omega⟩, ⟨4, by omega⟩) ∈ threeCrossGraph P' := by
    rw [threeCrossGraph_relabel P.swap ρ (by decide), threeCrossGraph_swap]
    simpa [ρ, rev5, min_comm, max_comm] using he3
  have he2' : (⟨2, by omega⟩, ⟨4, by omega⟩) ∈ threeCrossGraph P' := by
    rw [threeCrossGraph_relabel P.swap ρ (by decide), threeCrossGraph_swap]
    simpa [ρ, rev5, min_comm, max_comm] using he2
  obtain ⟨M', hM'_cases, hwit'⟩ := left_cert_witness P' hgp' h_shat' hleft' he0' he1' he2'
  refine ⟨M'.image ρ, ?_, ?_⟩
  · rcases hM'_cases with rfl | rfl
    · left; simp [ρ, rev5]
    · right; ext x; simp [ρ, rev5, or_comm]
  · rw [← cutSplitWitness_swap P (M'.image ρ), ← cutSplitWitness_relabel P.swap ρ M']
    exact hwit'

/-- Right Duplicate-Cell Certificate via swap duality on `P.swap`. -/
theorem right_certificate (P : DualConfig) (hgp : IsGenPos P)
    (htop : ∀ {t : ℝ}, 0 ≤ t → t ≤ 3 → 0 < topEnv P t)
    (h_shat : ∀ m : Fin 5 → Bool, ∃ z : ℝ × ℝ, InOmega z ∧ RealizesDualMask P m z)
    (hleft : StrictMono (leftKey P))
    (he2 : (min (rightPerm P ⟨0, by omega⟩) (rightPerm P ⟨2, by omega⟩),
            max (rightPerm P ⟨0, by omega⟩) (rightPerm P ⟨2, by omega⟩)) ∈ threeCrossGraph P)
    (he3 : (min (rightPerm P ⟨0, by omega⟩) (rightPerm P ⟨3, by omega⟩),
            max (rightPerm P ⟨0, by omega⟩) (rightPerm P ⟨3, by omega⟩)) ∈ threeCrossGraph P)
    (he4 : (min (rightPerm P ⟨0, by omega⟩) (rightPerm P ⟨4, by omega⟩),
            max (rightPerm P ⟨0, by omega⟩) (rightPerm P ⟨4, by omega⟩)) ∈ threeCrossGraph P) :
    1 ≤ sliceExcess P 1 + sliceExcess P 2 := by
  let _ := hleft
  obtain ⟨M, hM_cases, τ₁, τ₂, τ₃, h0, h12, h23, h3, hc1, hc2, hc3⟩ :=
    right_cert_witness P hgp h_shat he2 he3 he4
  have hd1 := slice_surj_masks P hgp htop h_shat (q := 1) (by omega) (by omega)
  have hd2 := slice_surj_masks P hgp htop h_shat (q := 2) (by omega) (by omega)
  have h01_ne : rightPerm P ⟨0, by omega⟩ ≠ rightPerm P ⟨1, by omega⟩ :=
    (rightPerm P).injective.ne (fun h => by have := congrArg Fin.val h; simp at this)
  rcases hM_cases with rfl | rfl
  · have hM1 := duplicate_slice_of_cutPotential P hgp htop h_shat {rightPerm P ⟨0, by omega⟩}
      (by simp) (by simp) h0 h12 h23 h3 hc1 hc2 hc3
    simp only [Finset.card_singleton] at hM1; omega
  · have hM2 := duplicate_slice_of_cutPotential P hgp htop h_shat
      {rightPerm P ⟨0, by omega⟩, rightPerm P ⟨1, by omega⟩}
      (by rw [Finset.card_pair h01_ne]; omega) (by rw [Finset.card_pair h01_ne]; omega)
      h0 h12 h23 h3 hc1 hc2 hc3
    rw [Finset.card_pair h01_ne] at hM2; omega

private lemma rankTieSet1_ge_six_of_T3_eq_ten (P : DualConfig) (hgp : IsGenPos P)
    (htop : ∀ {t : ℝ}, 0 ≤ t → t ≤ 3 → 0 < topEnv P t)
    (h_shat : ∀ m : Fin 5 → Bool, ∃ z : ℝ × ℝ, InOmega z ∧ RealizesDualMask P m z)
    (hleft : StrictMono (leftKey P))
    (hT3 : (threeCrossGraph P).card = 10) :
    6 ≤ (rankTieSet P 1).card := by
  let pairs : Finset (Fin 5 × Fin 5) := (Finset.univ : Finset (Fin 5 × Fin 5)).filter (fun p => p.1 < p.2)
  have hpairs_card : pairs.card = 10 := by decide
  have hsub_pairs : threeCrossGraph P ⊆ pairs := fun p hp => by
    simp only [threeCrossGraph, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    simp only [pairs, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hp.1
  have hG3_eq : threeCrossGraph P = pairs :=
    Finset.eq_of_subset_of_card_le hsub_pairs (by rw [hpairs_card, hT3])
  have h_all_edges : ∀ i j : Fin 5, i < j → (i, j) ∈ threeCrossGraph P := by
    intro i j hij
    rw [hG3_eq]
    simp only [pairs, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hij
  have hT2_zero : crossCountOfMult P 2 = 0 := by
    have hb := (card_posPairTies_bounds P hgp h_shat).2.1
    have hT3' : crossCountOfMult P 3 = 10 := by
      change (threeCrossGraph P).card = 10; exact hT3
    omega
  have hR_mono : StrictMono (rightKey P) := by
    have hinv_zero : permInversions (rightPerm P) = 0 := by
      rw [← (crossing_parity_inv P hgp htop h_shat hleft).1, hT2_zero]
    have hσ_mono : StrictMono (rightPerm P) := by
      intro r s hrs
      by_contra hle
      have hgt : rightPerm P s < rightPerm P r := lt_of_le_of_ne (not_lt.mp hle)
        ((rightPerm P).injective.ne (ne_of_gt hrs))
      have hmem : (r, s) ∈ (Finset.univ : Finset (Fin 5 × Fin 5)).filter
          (fun p => p.1 < p.2 ∧ rightPerm P p.2 < rightPerm P p.1) := by
        simp [hrs, hgt]
      have hpos : 0 < permInversions (rightPerm P) := Finset.card_pos.mpr ⟨(r, s), hmem⟩
      omega
    intro i j hij
    let r := (rightPerm P).symm i
    let s := (rightPerm P).symm j
    have hrs : r < s := by
      by_contra hle
      have hsr : s ≤ r := not_lt.mp hle
      have hle_ij : rightPerm P s ≤ rightPerm P r := hσ_mono.monotone hsr
      simp only [r, s, Equiv.apply_symm_apply] at hle_ij
      exact not_lt.mpr hle_ij hij
    have hsm := rightPerm_strictMono P hgp hrs
    simpa [r, s] using hsm
  obtain ⟨τ₁, hτ₁_0, hτ₁_ap0, hτ₁_min, hτ₁_s1⟩ :=
    left_min_4_witness P hgp h_shat hleft (fun i hi => h_all_edges i 4 hi)
  let τ₂ : ℝ := apexRay P 0
  have hap0 := (supportF_branch_switch P hgp).2 0
  have hτ₂_min : ∀ j : Fin 5, j ≠ 0 → clippedG P 0 τ₂ < clippedG P j τ₂ := by
    intro j hj
    have hj_pos : 0 < j := Fin.pos_of_ne_zero hj
    exact (three_crossing_structure P hgp h_shat hleft (h_all_edges 0 j hj_pos)).2.2.2.1
  have hτ₂_s1 : 0 < sortedG P 1 τ₂ :=
    sortedG1_pos_of_unique_min P τ₂ 0 hτ₂_min
      ⟨4, by decide, (le_max_right (supportF P 0 τ₂) 0).trans_lt (hτ₂_min 4 (by decide))⟩
  let τ₃ : ℝ := apexRay P 4
  have hap4 := (supportF_branch_switch P hgp).2 4
  have h04 := three_crossing_structure P hgp h_shat hleft (h_all_edges 0 4 (by decide))
  have hτ₂_τ₃ : τ₂ < τ₃ := h04.2.1
  have hτ₃_min : ∀ j : Fin 5, j ≠ 4 → clippedG P 4 τ₃ < clippedG P j τ₃ := by
    intro j hj
    have hj_lt : j < 4 := lt_of_le_of_ne (Fin.is_le j) hj
    exact (three_crossing_structure P hgp h_shat hleft (h_all_edges j 4 hj_lt)).2.2.2.2.1
  have hτ₃_s1 : 0 < sortedG P 1 τ₃ :=
    sortedG1_pos_of_unique_min P τ₃ 4 hτ₃_min
      ⟨0, by decide, (le_max_right (supportF P 4 τ₃) 0).trans_lt (hτ₃_min 0 (by decide))⟩
  -- Point τ₄ near 3⁻ using P.swap.relabel rev5
  let rev5 : Equiv.Perm (Fin 5) :=
    { toFun := fun r => ⟨4 - r.val, by omega⟩
      invFun := fun r => ⟨4 - r.val, by omega⟩
      left_inv := fun r => by ext; dsimp; omega
      right_inv := fun r => by ext; dsimp; omega }
  let Q := P.swap.relabel rev5
  have hgp_sw : IsGenPos P.swap := (P.swap_spec).2.1.mpr hgp
  have hgpQ : IsGenPos Q := isGenPos_relabel P.swap rev5 hgp_sw
  have h_shat_sw : ∀ m : Fin 5 → Bool, ∃ z : ℝ × ℝ, InOmega z ∧ RealizesDualMask P.swap m z := by
    intro m; obtain ⟨z, hz, hm⟩ := h_shat m
    exact ⟨swap2 z, inOmega_swap2 hz, (P.swap_spec).2.2 m z |>.mpr hm⟩
  have h_shatQ : ∀ m : Fin 5 → Bool, ∃ z : ℝ × ℝ, InOmega z ∧ RealizesDualMask Q m z :=
    shat_relabel P.swap rev5 h_shat_sw
  have hleftQ : StrictMono (leftKey Q) := by
    intro r₁ r₂ hr
    rw [leftKey_relabel, leftKey_relabel, (boundaryKey_swap P hgp (rev5 r₁)).1,
      (boundaryKey_swap P hgp (rev5 r₂)).1]
    have hrev : rev5 r₂ < rev5 r₁ := by show (4 - r₂.val : ℕ) < 4 - r₁.val; have : r₁.val < r₂.val := hr; omega
    linarith [hR_mono hrev]
  have hQ_edges : ∀ i : Fin 5, i < 4 → (i, (4 : Fin 5)) ∈ threeCrossGraph Q := by
    intro i hi
    rw [threeCrossGraph_relabel P.swap rev5 hi, threeCrossGraph_swap]
    have hne : rev5 i ≠ rev5 4 := rev5.injective.ne (ne_of_lt hi)
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · rw [min_eq_left (le_of_lt hlt), max_eq_right (le_of_lt hlt)]
      exact h_all_edges _ _ hlt
    · rw [min_eq_right (le_of_lt hgt), max_eq_left (le_of_lt hgt)]
      exact h_all_edges _ _ hgt
  obtain ⟨τ₄', hτ₄'_0, hτ₄'_ap0, hτ₄'_min, hτ₄'_s1⟩ :=
    left_min_4_witness Q hgpQ h_shatQ hleftQ hQ_edges
  have hap_Q0 : apexRay Q 0 = 3 - τ₃ := by
    have hQ_ap : Q.apex 0 = P.swap.apex 4 := by
      unfold Q DualConfig.apex DualConfig.relabel; rfl
    unfold apexRay
    rw [hQ_ap, (P.swap_spec).1 4]
    exact rayParam_swap2 (Or.inl (P.h_apex 4).1)
  let τ₄ : ℝ := 3 - τ₄'
  have hτ₃_τ₄ : τ₃ < τ₄ := by dsimp [τ₄]; linarith
  have hτ₄_3 : τ₄ < 3 := by dsimp [τ₄]; linarith
  have hτ₄_min : ∀ j : Fin 5, j ≠ 0 → clippedG P 0 τ₄ < clippedG P j τ₄ := by
    intro j hj
    have hj_ne4 : rev5 j ≠ 4 := fun h => hj (rev5.injective (by simpa [rev5] using h))
    have hm := hτ₄'_min (rev5 j) hj_ne4
    have hclip_eq : ∀ k : Fin 5, clippedG Q (rev5 k) τ₄' = clippedG P k τ₄ := by
      intro k; unfold clippedG Q
      rw [supportF_relabel, supportF_swap_eq]
      have hkk : rev5 (rev5 k) = k := rev5.apply_symm_apply k
      rw [hkk]
    have hrev0 : (4 : Fin 5) = rev5 0 := rfl
    rw [hrev0, hclip_eq 0, hclip_eq j] at hm
    exact hm
  have hτ₄_s1 : 0 < sortedG P 1 τ₄ := by
    have heq : sortedG Q 1 τ₄' = sortedG P 1 τ₄ := by
      dsimp [Q]; rw [sortedG_relabel, sortedG_swap]
    linarith
  -- Witnesses s₁, s₂, s₃ for k = 1, 2, 3
  have h_mid_wit : ∀ k : Fin 5, ∃ s : ℝ, 0 < s ∧ s < 3 ∧
      (∀ j : Fin 5, j ≠ k → clippedG P k s < clippedG P j s) ∧ 0 < sortedG P 1 s := by
    intro k
    obtain ⟨z, hz_om, hz_mask⟩ := h_shat (fun i => decide (i = k))
    let s := rayParam z
    have hs := rayParam_mem_Ioo hz_om
    have hnorm := inOmega_norm_pos hz_om
    have hrec := gamma_rayParam_smul hz_om
    let η : ℝ := 1 / (|z.1| + |z.2|)
    have hη_pos : 0 < η := div_pos one_pos hnorm
    have hk_lt : supportF P k s < η := by
      have hmk := hz_mask k
      simp only [decide_true, ↓reduceIte, DualConfig.MemOpen] at hmk
      unfold supportF
      have h1 : dot2 (P.p1 k) (gamma s) < η := by
        dsimp [η, s]; rw [lt_div_iff₀ hnorm, mul_comm, ← dot2_smul_right, hrec]; exact hmk.1
      have h2 : dot2 (P.p2 k) (gamma s) < η := by
        dsimp [η, s]; rw [lt_div_iff₀ hnorm, mul_comm, ← dot2_smul_right, hrec]; exact hmk.2
      exact max_lt h1 h2
    have hj_gt : ∀ j : Fin 5, j ≠ k → η < supportF P j s := by
      intro j hj
      have hmj := hz_mask j
      simp only [decide_eq_false hj, Bool.false_eq_true, ↓reduceIte, DualConfig.MemExt] at hmj
      unfold supportF
      rcases hmj with h1 | h2
      · have : η < dot2 (P.p1 j) (gamma s) := by
          dsimp [η, s]; rw [div_lt_iff₀ hnorm, mul_comm, ← dot2_smul_right, hrec]; exact h1
        exact lt_of_lt_of_le this (le_max_left _ _)
      · have : η < dot2 (P.p2 j) (gamma s) := by
          dsimp [η, s]; rw [div_lt_iff₀ hnorm, mul_comm, ← dot2_smul_right, hrec]; exact h2
        exact lt_of_lt_of_le this (le_max_right _ _)
    have hclip : ∀ j : Fin 5, j ≠ k → clippedG P k s < clippedG P j s := by
      intro j hj
      have hj' := hj_gt j hj
      have hj_pos := lt_trans hη_pos hj'
      unfold clippedG
      rw [max_eq_left (le_of_lt hj_pos)]
      exact lt_trans (max_lt hk_lt hη_pos) hj'
    let j₀ : Fin 5 := if k = 0 then 1 else 0
    have hj₀ : j₀ ≠ k := by
      dsimp [j₀]; split_ifs with h
      · rw [h]; decide
      · exact Ne.symm h
    exact ⟨s, hs.1, hs.2, hclip, sortedG1_pos_of_unique_min P s k hclip
      ⟨j₀, hj₀, by unfold clippedG; exact lt_of_lt_of_le (lt_trans hη_pos (hj_gt j₀ hj₀)) (le_max_left _ _)⟩⟩
  obtain ⟨s₁, hs1_0, hs1_3, hs1_min, hs1_s1⟩ := h_mid_wit 1
  obtain ⟨s₂, hs2_0, hs2_3, hs2_min, hs2_s1⟩ := h_mid_wit 2
  obtain ⟨s₃, hs3_0, hs3_3, hs3_min, hs3_s1⟩ := h_mid_wit 3
  let pts : Fin 7 → ℝ := ![τ₁, τ₂, τ₃, τ₄, s₁, s₂, s₃]
  let cols : Fin 7 → Fin 5 := ![4, 0, 4, 0, 1, 2, 3]
  have hpts_prop : ∀ m : Fin 7, 0 < pts m ∧ pts m < 3 ∧
      (∀ j : Fin 5, j ≠ cols m → clippedG P (cols m) (pts m) < clippedG P j (pts m)) ∧
      0 < sortedG P 1 (pts m) := by
    intro m; fin_cases m
    · exact ⟨hτ₁_0, lt_trans hτ₁_ap0 (lt_trans hτ₂_τ₃ (lt_trans hτ₃_τ₄ hτ₄_3)), hτ₁_min, hτ₁_s1⟩
    · exact ⟨lt_trans (by norm_num : (0 : ℝ) < 1) hap0.1, lt_trans hap0.2.1 (by norm_num), hτ₂_min, hτ₂_s1⟩
    · exact ⟨lt_trans (by norm_num : (0 : ℝ) < 1) hap4.1, lt_trans hap4.2.1 (by norm_num), hτ₃_min, hτ₃_s1⟩
    · exact ⟨lt_trans (lt_trans (by norm_num : (0 : ℝ) < 1) hap4.1) hτ₃_τ₄, hτ₄_3, hτ₄_min, hτ₄_s1⟩
    · exact ⟨hs1_0, hs1_3, hs1_min, hs1_s1⟩
    · exact ⟨hs2_0, hs2_3, hs2_min, hs2_s1⟩
    · exact ⟨hs3_0, hs3_3, hs3_min, hs3_s1⟩
  have hτ₁_τ₂ : τ₁ < τ₂ := hτ₁_ap0
  have hpts_inj : Function.Injective pts := by
    intro m₁ m₂ heq
    by_contra hne
    by_cases hcol : cols m₁ = cols m₂
    · fin_cases m₁ <;> fin_cases m₂ <;> simp [cols] at hcol <;>
        (try contradiction) <;> simp [pts] at heq <;> linarith
    · have h1 := (hpts_prop m₁).2.2.1 (cols m₂) (Ne.symm hcol)
      have h2 := (hpts_prop m₂).2.2.1 (cols m₁) hcol
      rw [heq] at h1
      linarith
  let ρ : Equiv.Perm (Fin 7) := Tuple.sort pts
  let u : Fin 7 → ℝ := fun r => pts (ρ r)
  let c : Fin 7 → Fin 5 := fun r => cols (ρ r)
  have hu_mono : StrictMono u :=
    (Tuple.monotone_sort pts).strictMono_of_injective (hpts_inj.comp ρ.injective)
  have hcol_pair : ∀ a b : Fin 7, a ≠ b → cols a = cols b →
      (a = 0 ∧ b = 2) ∨ (a = 2 ∧ b = 0) ∨ (a = 1 ∧ b = 3) ∨ (a = 3 ∧ b = 1) := by
    intro a b hab hcol
    fin_cases a <;> fin_cases b <;> revert hab hcol <;> decide
  have hcol_adj : ∀ r : Fin 6, c ⟨r.val, by omega⟩ ≠ c ⟨r.val + 1, by omega⟩ := by
    intro r heq_col
    let r₀ : Fin 7 := ⟨r.val, by omega⟩
    let r₁ : Fin 7 := ⟨r.val + 1, by omega⟩
    have hr01 : r₀ < r₁ := by show r.val < r.val + 1; omega
    have hu01 : u r₀ < u r₁ := hu_mono hr01
    have h_mid_absurd : ∀ k : Fin 7, u r₀ < pts k → pts k < u r₁ → False := by
      intro k hk1 hk2
      let rk := ρ.symm k
      have hk_eq : u rk = pts k := by dsimp [u, rk]; simp
      rw [← hk_eq] at hk1 hk2
      have h1 : r₀ < rk := hu_mono.lt_iff_lt.mp hk1
      have h2 : rk < r₁ := hu_mono.lt_iff_lt.mp hk2
      have : r₀.val < rk.val ∧ rk.val < r₁.val := ⟨h1, h2⟩
      dsimp [r₀, r₁] at this; omega
    dsimp [c] at heq_col
    have h_cases := hcol_pair (ρ r₀) (ρ r₁) (ρ.injective.ne (ne_of_lt hr01)) heq_col
    rcases h_cases with ⟨h0, h1⟩ | ⟨h0, h1⟩ | ⟨h0, h1⟩ | ⟨h0, h1⟩
    · have hu0 : u r₀ = τ₁ := by dsimp [u]; rw [h0]; rfl
      have hu1 : u r₁ = τ₃ := by dsimp [u]; rw [h1]; rfl
      exact h_mid_absurd 1 (by rw [hu0]; exact hτ₁_τ₂) (by rw [hu1]; exact hτ₂_τ₃)
    · have hu0 : u r₀ = τ₃ := by dsimp [u]; rw [h0]; rfl
      have hu1 : u r₁ = τ₁ := by dsimp [u]; rw [h1]; rfl
      linarith [hu01, hτ₁_τ₂, hτ₂_τ₃]
    · have hu0 : u r₀ = τ₂ := by dsimp [u]; rw [h0]; rfl
      have hu1 : u r₁ = τ₄ := by dsimp [u]; rw [h1]; rfl
      exact h_mid_absurd 2 (by rw [hu0]; exact hτ₂_τ₃) (by rw [hu1]; exact hτ₃_τ₄)
    · have hu0 : u r₀ = τ₄ := by dsimp [u]; rw [h0]; rfl
      have hu1 : u r₁ = τ₂ := by dsimp [u]; rw [h1]; rfl
      linarith [hu01, hτ₂_τ₃, hτ₃_τ₄]
  have h_clip_cont : ∀ j : Fin 5, Continuous (fun t => clippedG P j t) := fun j =>
    (supportF_continuous P j).max continuous_const
  have hr1_Ioo := rankInterval_eq_Ioo P hgp htop h_shat (q := 1) (by omega) (by omega)
  have h_tie_in_interval : ∀ r : Fin 6, ∃ t : ℝ,
      u ⟨r.val, by omega⟩ < t ∧ t < u ⟨r.val + 1, by omega⟩ ∧ t ∈ rankTieSet P 1 := by
    intro r
    let r₀ : Fin 7 := ⟨r.val, by omega⟩
    let r₁ : Fin 7 := ⟨r.val + 1, by omega⟩
    have hab : u r₀ < u r₁ := hu_mono (by show r.val < r.val + 1; omega)
    let c₁ : Fin 5 := c r₀
    let c₂ : Fin 5 := c r₁
    have hc12 : c₁ ≠ c₂ := hcol_adj r
    let S₁ : Finset (Fin 5) := Finset.univ.erase c₁
    have hS₁ : S₁.Nonempty := ⟨c₂, Finset.mem_erase.mpr ⟨hc12.symm, Finset.mem_univ _⟩⟩
    let g : ℝ → ℝ := fun t => clippedG P c₁ t - S₁.inf' hS₁ (fun j => clippedG P j t)
    have hg_cont : Continuous g :=
      (h_clip_cont c₁).sub (Continuous.finset_inf'_apply hS₁ fun j _ => h_clip_cont j)
    have hga : g (u r₀) < 0 := by
      dsimp [g, u, c₁, c]
      rw [sub_neg, Finset.lt_inf'_iff]
      intro j hj
      exact (hpts_prop (ρ r₀)).2.2.1 j (Finset.mem_erase.mp hj).1
    have hgb : 0 < g (u r₁) := by
      dsimp [g, u, c₁, c]
      rw [sub_pos]
      have hc2_mem : c₂ ∈ S₁ := Finset.mem_erase.mpr ⟨hc12.symm, Finset.mem_univ _⟩
      have hle_inf : S₁.inf' hS₁ (fun j => clippedG P j (pts (ρ r₁))) ≤
          clippedG P c₂ (pts (ρ r₁)) := Finset.inf'_le _ hc2_mem
      have hlt_c1 : clippedG P c₂ (pts (ρ r₁)) < clippedG P c₁ (pts (ρ r₁)) :=
        (hpts_prop (ρ r₁)).2.2.1 c₁ hc12
      exact lt_of_le_of_lt hle_inf hlt_c1
    obtain ⟨t, ht_mem, ht_zero⟩ := intermediate_value_Ioo (le_of_lt hab) hg_cont.continuousOn
      (⟨hga, hgb⟩ : (0 : ℝ) ∈ Set.Ioo (g (u r₀)) (g (u r₁)))
    have ht_eq_inf : clippedG P c₁ t = S₁.inf' hS₁ (fun j => clippedG P j t) := by
      dsimp [g] at ht_zero; linarith
    obtain ⟨j, hj_mem, hj_eq⟩ := Finset.exists_mem_eq_inf' hS₁ (fun j => clippedG P j t)
    have hj_ne : j ≠ c₁ := (Finset.mem_erase.mp hj_mem).1
    have hle_all : ∀ k : Fin 5, clippedG P c₁ t ≤ clippedG P k t := by
      intro k
      by_cases hk : k = c₁
      · subst hk; exact le_rfl
      · rw [ht_eq_inf]
        exact Finset.inf'_le _ (Finset.mem_erase.mpr ⟨hk, Finset.mem_univ _⟩)
    have hs01 : sortedG P 0 t = sortedG P 1 t :=
      sortedG_zero_eq_one_of_tie_min P t hj_ne.symm (by rw [ht_eq_inf, hj_eq]) hle_all
    have ha_in_rank : u r₀ ∈ rankInterval P 1 := by
      have hp := hpts_prop (ρ r₀)
      simp only [rankInterval, show (1 : ℕ) < 5 by omega, ↓reduceDIte, Set.mem_setOf_eq]
      exact ⟨hp.1, hp.2.1, hp.2.2.2⟩
    have hb_in_rank : u r₁ ∈ rankInterval P 1 := by
      have hp := hpts_prop (ρ r₁)
      simp only [rankInterval, show (1 : ℕ) < 5 by omega, ↓reduceDIte, Set.mem_setOf_eq]
      exact ⟨hp.1, hp.2.1, hp.2.2.2⟩
    rw [hr1_Ioo.2] at ha_in_rank hb_in_rank
    have ht_in_rank : t ∈ rankInterval P 1 := by
      rw [hr1_Ioo.2]
      exact ⟨lt_trans ha_in_rank.1 ht_mem.1, lt_trans ht_mem.2 hb_in_rank.2⟩
    simp only [rankInterval, show (1 : ℕ) < 5 by omega, ↓reduceDIte, Set.mem_setOf_eq] at ht_in_rank
    rcases ht_in_rank with ⟨ht0, ht3, hts1⟩
    have hs0_eq : sortedG P 0 t = clippedG P c₁ t := by
      unfold sortedG
      let l₀ := List.ofFn (fun i : Fin 5 => clippedG P i t)
      let l := l₀.mergeSort (· ≤ ·)
      have hperm : l.Perm l₀ := List.mergeSort_perm l₀ _
      have hpw : l.Pairwise (· ≤ ·) := List.pairwise_mergeSort' (· ≤ ·) l₀
      have hlen : l.length = 5 := by rw [hperm.length_eq]; simp [l₀]
      have hget0 : l.getD 0 0 = l[0] := by simp [List.getD_eq_getElem?_getD, hlen]
      change l.getD 0 0 = clippedG P c₁ t
      rw [hget0]
      have hv_mem : clippedG P c₁ t ∈ l := hperm.mem_iff.mpr (List.mem_ofFn.mpr ⟨c₁, rfl⟩)
      obtain ⟨m, hm, hmeq⟩ := List.mem_iff_getElem.mp hv_mem
      have hl0_le : l[0] ≤ clippedG P c₁ t := by
        rcases Nat.eq_zero_or_pos m with rfl | hm_pos
        · exact le_of_eq hmeq
        · rw [← hmeq]; exact List.pairwise_iff_getElem.mp hpw 0 m (by omega) hm hm_pos
      have hv_le : clippedG P c₁ t ≤ l[0] := by
        have h0_lt : 0 < l.length := by rw [hlen]; omega
        have h0_mem : l[0] ∈ l := List.getElem_mem h0_lt
        have hm0 : l[0] ∈ l₀ := hperm.mem_iff.mp h0_mem
        obtain ⟨k, hk⟩ := List.mem_ofFn.mp hm0
        rw [← hk]; exact hle_all k
      exact le_antisymm hl0_le hv_le
    have hclip_pos : 0 < clippedG P c₁ t := by
      rw [← hs0_eq, hs01]
      exact hts1
    have hclip_eq : clippedG P c₁ t = clippedG P j t := by rw [ht_eq_inf, hj_eq]
    have hfj_pos : 0 < supportF P j t := by
      by_contra hle; replace hle : supportF P j t ≤ 0 := not_lt.mp hle
      have : clippedG P j t = 0 := max_eq_right hle
      linarith
    have hfc1_pos : 0 < supportF P c₁ t := by
      by_contra hle; replace hle : supportF P c₁ t ≤ 0 := not_lt.mp hle
      have : clippedG P c₁ t = 0 := max_eq_right hle
      linarith
    have hf_tie : supportF P c₁ t = supportF P j t := by
      unfold clippedG at hclip_eq
      rw [max_eq_left (le_of_lt hfc1_pos), max_eq_left (le_of_lt hfj_pos)] at hclip_eq
      exact hclip_eq
    have ht_grid : t ∈ candTieGrid P := candTieGrid_mem_of_tie P hgp ht0 ht3 hj_ne.symm hf_tie
    have ht_all : t ∈ allPosTieSet P := by
      simp only [allPosTieSet, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and]
      rcases lt_or_gt_of_ne hj_ne.symm with hlt | hgt
      · refine ⟨(c₁, j), hlt, ?_⟩
        simp only [posPairTies, Finset.mem_filter]
        exact ⟨ht_grid, ht0, ht3, hf_tie, hfc1_pos⟩
      · refine ⟨(j, c₁), hgt, ?_⟩
        simp only [posPairTies, Finset.mem_filter]
        exact ⟨ht_grid, ht0, ht3, hf_tie.symm, hfj_pos⟩
    refine ⟨t, ht_mem.1, ht_mem.2, ?_⟩
    simp only [rankTieSet, Finset.mem_filter, show 0 < (1 : ℕ) ∧ (1 : ℕ) < 5 by omega]
    exact ⟨ht_all, hts1, hs01⟩
  choose f_tie hf_lo hf_hi hf_mem using h_tie_in_interval
  have hf_inj : Function.Injective f_tie := by
    intro r₁ r₂ heq
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hle : (⟨r₁.val + 1, by omega⟩ : Fin 7) ≤ ⟨r₂.val, by omega⟩ := by
        show r₁.val + 1 ≤ r₂.val; exact hlt
      have hmono := hu_mono.monotone hle
      have h1 := hf_hi r₁
      have h2 := hf_lo r₂
      rw [heq] at h1
      linarith
    · have hle : (⟨r₂.val + 1, by omega⟩ : Fin 7) ≤ ⟨r₁.val, by omega⟩ := by
        show r₂.val + 1 ≤ r₁.val; exact hgt
      have hmono := hu_mono.monotone hle
      have h1 := hf_hi r₂
      have h2 := hf_lo r₁
      rw [heq] at h2
      linarith
  have hcard6 : (Finset.univ : Finset (Fin 6)).card ≤ (rankTieSet P 1).card :=
    Finset.card_le_card_of_injOn f_tie (fun r _ => hf_mem r) (fun r₁ _ r₂ _ h => hf_inj h)
  simpa using hcard6

/-- Elimination of `8 ≤ n_Ω ≤ 10` via `T̄_3^+ + T_1^+ + Δ_1 + Δ_2 ≥ 2`. -/
theorem elim_n8_to_10 (P : DualConfig) (hgp : IsGenPos P)
    (htop : ∀ {t : ℝ}, 0 ≤ t → t ≤ 3 → 0 < topEnv P t)
    (h_shat : ∀ m : Fin 5 → Bool, ∃ z : ℝ × ℝ, InOmega z ∧ RealizesDualMask P m z) :
    hullBlockCount P ≤ 7 := by
  obtain ⟨τ, hleft⟩ := exists_left_sort_perm P hgp
  let P' := P.relabel τ
  have hgp' : IsGenPos P' := isGenPos_relabel P τ hgp
  have htop' : ∀ {t : ℝ}, 0 ≤ t → t ≤ 3 → 0 < topEnv P' t := fun ht0 ht3 => by
    rw [topEnv_relabel]; exact htop ht0 ht3
  have h_shat' : ∀ m : Fin 5 → Bool, ∃ z : ℝ × ℝ, InOmega z ∧ RealizesDualMask P' m z :=
    shat_relabel P τ h_shat
  have hlaw := conservation_law P' hgp' htop' h_shat'
  have hd1 := slice_surj_masks P' hgp' htop' h_shat' (q := 1) (by omega) (by omega)
  have hd2 := slice_surj_masks P' hgp' htop' h_shat' (q := 2) (by omega) (by omega)
  have hd3 := slice_surj_masks P' hgp' htop' h_shat' (q := 3) (by omega) (by omega)
  have hbounds := card_posPairTies_bounds P' hgp' h_shat'
  have hcount_eq : hullBlockCount P' = hullBlockCount P := hullBlockCount_relabel P τ hgp
  rw [← hcount_eq]
  by_cases hT1 : 1 ≤ crossCountOfMult P' 1
  · omega
  · have hT1_zero : crossCountOfMult P' 1 = 0 := by omega
    by_cases hT2 : 2 ≤ crossCountOfMult P' 2
    · omega
    · have hT2_le1 : crossCountOfMult P' 2 ≤ 1 := by omega
      rcases Nat.eq_zero_or_pos (crossCountOfMult P' 2) with hT2_zero | hT2_pos
      · have hT3_10 : (threeCrossGraph P').card = 10 := by
          have hb := hbounds.2.1
          change crossCountOfMult P' 1 + crossCountOfMult P' 2 + (threeCrossGraph P').card = 10 at hb
          omega
        have h6 := rankTieSet1_ge_six_of_T3_eq_ten P' hgp' htop' h_shat' hleft hT3_10
        have hΔ1 : 2 ≤ sliceExcess P' 1 := by
          unfold sliceExcess
          have : Nat.choose 5 1 = 5 := by decide
          omega
        omega
      · have hT2_one : crossCountOfMult P' 2 = 1 := by omega
        have hinv_one : permInversions (rightPerm P') = 1 := by
          rw [← (crossing_parity_inv P' hgp' htop' h_shat' hleft).1, hT2_one]
        have hR_lt4 : ∀ i : Fin 5, i < (3 : Fin 5) → rightKey P' i < rightKey P' 4 := by
          intro i hi
          have hσ_mono := rightPerm_strictMono P' hgp'
          let r := (rightPerm P').symm i
          let s := (rightPerm P').symm 4
          have hne_rs : r ≠ s := fun h => by
            have := congrArg (rightPerm P') h
            simp only [r, s, Equiv.apply_symm_apply] at this
            have h1 : i.val = 4 := congrArg Fin.val this
            have h2 : i.val < 3 := hi
            omega
          by_contra hle
          have hlt_R : rightKey P' 4 < rightKey P' i :=
            lt_of_le_of_ne (not_lt.mp hle) ((rightKey_injective P' hgp').ne (by
              intro h; have h1 : (4 : Fin 5).val = i.val := congrArg Fin.val h
              have h2 : i.val < 3 := hi; omega))
          have hsr : s < r := by
            by_contra hrs_le
            have hrs : r < s := lt_of_le_of_ne (not_lt.mp hrs_le) hne_rs
            have hm := hσ_mono hrs
            simp only [r, s, Equiv.apply_symm_apply] at hm
            linarith
          let k : Fin 5 := 3
          let t := (rightPerm P').symm k
          have hne_ts : t ≠ s := fun h => by
            have := congrArg (rightPerm P') h
            simp only [t, s, Equiv.apply_symm_apply] at this
            exact absurd this (by decide)
          have h_inv_ge2 : 2 ≤ permInversions (rightPerm P') := by
            rcases lt_or_gt_of_ne hne_ts with hts | hst
            · have h_sub : ({(s, r), (t, r)} : Finset (Fin 5 × Fin 5)) ⊆
                  (Finset.univ : Finset (Fin 5 × Fin 5)).filter
                    (fun p => p.1 < p.2 ∧ rightPerm P' p.2 < rightPerm P' p.1) := by
                intro p hp
                simp only [Finset.mem_insert, Finset.mem_singleton] at hp
                simp only [Finset.mem_filter, Finset.mem_univ, true_and]
                rcases hp with rfl | rfl
                · exact ⟨hsr, by simp [s, r]; show i.val < 4; have : i.val < 3 := hi; omega⟩
                · exact ⟨lt_trans hts hsr, by simp [t, r]; show i.val < 3; exact hi⟩
              have hpair_ne : (s, r) ≠ (t, r) := fun h => hne_ts (congrArg Prod.fst h).symm
              calc 2 = ({(s, r), (t, r)} : Finset (Fin 5 × Fin 5)).card := (Finset.card_pair hpair_ne).symm
                _ ≤ permInversions (rightPerm P') := Finset.card_le_card h_sub
            · have h_sub : ({(s, r), (s, t)} : Finset (Fin 5 × Fin 5)) ⊆
                  (Finset.univ : Finset (Fin 5 × Fin 5)).filter
                    (fun p => p.1 < p.2 ∧ rightPerm P' p.2 < rightPerm P' p.1) := by
                intro p hp
                simp only [Finset.mem_insert, Finset.mem_singleton] at hp
                simp only [Finset.mem_filter, Finset.mem_univ, true_and]
                rcases hp with rfl | rfl
                · exact ⟨hsr, by simp [s, r]; show i.val < 4; have : i.val < 3 := hi; omega⟩
                · exact ⟨hst, by simp [s, t]; decide⟩
              have hpair_ne : (s, r) ≠ (s, t) := fun h => by
                have heq : r = t := congrArg Prod.snd h
                have := congrArg (rightPerm P') heq
                simp only [r, t, Equiv.apply_symm_apply] at this
                have h1 : i.val = 3 := congrArg Fin.val this
                have h2 : i.val < 3 := hi
                omega
              calc 2 = ({(s, r), (s, t)} : Finset (Fin 5 × Fin 5)).card := (Finset.card_pair hpair_ne).symm
                _ ≤ permInversions (rightPerm P') := Finset.card_le_card h_sub
          omega
        have h_edge_3 : ∀ i : Fin 5, i < (3 : Fin 5) → (i, (4 : Fin 5)) ∈ threeCrossGraph P' := by
          intro i hi
          have hi4 : i < 4 := lt_trans hi (by decide)
          have hne2 := posPairTies_ne_two_of_same_order P' hgp' h_shat' (ne_of_lt hi4)
            (hleft hi4) (hR_lt4 i hi)
          have hne1 : (posPairTies P' i 4).card ≠ 1 := by
            intro h1
            have hpos1 : 0 < crossCountOfMult P' 1 :=
              Finset.card_pos.mpr ⟨(i, 4), by simp [hi4, h1]⟩
            omega
          have hb := hbounds.1 i 4 hi4
          simp only [threeCrossGraph, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨hi4, by omega⟩
        have hcert := left_certificate P' hgp' htop' h_shat' hleft
          (h_edge_3 0 (by decide)) (h_edge_3 1 (by decide)) (h_edge_3 2 (by decide))
        omega

private lemma permInversions_symm (σ : Equiv.Perm (Fin 5)) :
    permInversions σ.symm = permInversions σ := by
  unfold permInversions
  refine Finset.card_bij (fun p _ => (σ.symm p.2, σ.symm p.1)) ?_ ?_ ?_
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
    exact ⟨hp.2, by simpa using hp.1⟩
  · intro p₁ _ p₂ _ heq
    exact Prod.ext (σ.symm.injective (congrArg Prod.snd heq))
      (σ.symm.injective (congrArg Prod.fst heq))
  · intro q hq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq
    exact ⟨(σ q.2, σ q.1), by simp [hq.1, hq.2], by ext <;> simp⟩

private lemma inv_one_bounds (σ : Equiv.Perm (Fin 5)) (hinv : permInversions σ = 1) :
    (∀ i : Fin 5, i < (3 : Fin 5) → σ.symm i < σ.symm 4) ∧
    (∀ k : Fin 5, (1 : Fin 5) < k → σ 0 < σ k) ∧
    σ 0 < (2 : Fin 5) ∧ σ 0 ≠ 4 ∧ σ 1 ≠ 4 := by
  have hsymm_inv : permInversions σ.symm = 1 := by rw [permInversions_symm, hinv]
  have hL : ∀ i : Fin 5, i < (3 : Fin 5) → σ.symm i < σ.symm 4 := by
    intro i hi
    by_contra hle
    have h4i : σ.symm 4 < σ.symm i :=
      lt_of_le_of_ne (not_lt.mp hle) (σ.symm.injective.ne (fun h => by
        have hv : (4 : Fin 5).val = i.val := congrArg Fin.val h
        have hi3 : i.val < 3 := hi
        omega))
    let q : Fin 5 × Fin 5 :=
      if σ.symm 3 < σ.symm i then (i, 3) else (3, 4)
    have hq_mem : q ∈ (Finset.univ : Finset (Fin 5 × Fin 5)).filter
        (fun p => p.1 < p.2 ∧ σ.symm p.2 < σ.symm p.1) := by
      dsimp [q]; split_ifs with h3i
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨hi, h3i⟩
      · have hi3 : σ.symm i < σ.symm 3 :=
          lt_of_le_of_ne (not_lt.mp h3i) (σ.symm.injective.ne (ne_of_lt hi))
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨by decide, lt_trans h4i hi3⟩
    have hi4_mem : (i, (4 : Fin 5)) ∈ (Finset.univ : Finset (Fin 5 × Fin 5)).filter
        (fun p => p.1 < p.2 ∧ σ.symm p.2 < σ.symm p.1) := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨lt_trans hi (by decide), h4i⟩
    have hne : (i, (4 : Fin 5)) ≠ q := by
      dsimp [q]; split_ifs with h3i
      · intro h; have := congrArg Fin.val (congrArg Prod.snd h); simp at this
      · intro h
        have : i.val = 3 := congrArg Fin.val (congrArg Prod.fst h)
        have hi3 : i.val < 3 := hi
        omega
    have hle2 : 2 ≤ permInversions σ.symm :=
      calc 2 = ({(i, (4 : Fin 5)), q} : Finset (Fin 5 × Fin 5)).card := (Finset.card_pair hne).symm
        _ ≤ permInversions σ.symm := Finset.card_le_card (Finset.insert_subset_iff.mpr ⟨hi4_mem, Finset.singleton_subset_iff.mpr hq_mem⟩)
    omega
  have hR : ∀ k : Fin 5, (1 : Fin 5) < k → σ 0 < σ k := by
    intro k hk
    by_contra hle
    have hk0 : σ k < σ 0 :=
      lt_of_le_of_ne (not_lt.mp hle) (σ.injective.ne (fun h => by
        have hv : k.val = 0 := congrArg Fin.val h
        have hk1 : 1 < k.val := hk
        omega))
    let q : Fin 5 × Fin 5 := if σ 1 < σ 0 then (0, 1) else (1, k)
    have hq_mem : q ∈ (Finset.univ : Finset (Fin 5 × Fin 5)).filter
        (fun p => p.1 < p.2 ∧ σ p.2 < σ p.1) := by
      dsimp [q]; split_ifs with h10
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨by decide, h10⟩
      · have h01 : σ 0 < σ 1 := lt_of_le_of_ne (not_lt.mp h10) (σ.injective.ne (by decide))
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨hk, lt_trans hk0 h01⟩
    have h0k_mem : ((0 : Fin 5), k) ∈ (Finset.univ : Finset (Fin 5 × Fin 5)).filter
        (fun p => p.1 < p.2 ∧ σ p.2 < σ p.1) := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨lt_trans (by decide) hk, hk0⟩
    have hne : ((0 : Fin 5), k) ≠ q := by
      dsimp [q]; split_ifs with h10
      · intro h
        have : k.val = 1 := congrArg Fin.val (congrArg Prod.snd h)
        have hk1 : 1 < k.val := hk
        omega
      · intro h; have := congrArg Fin.val (congrArg Prod.fst h); simp at this
    have hle2 : 2 ≤ permInversions σ :=
      calc 2 = ({((0 : Fin 5), k), q} : Finset (Fin 5 × Fin 5)).card := (Finset.card_pair hne).symm
        _ ≤ permInversions σ := Finset.card_le_card (Finset.insert_subset_iff.mpr ⟨h0k_mem, Finset.singleton_subset_iff.mpr hq_mem⟩)
    omega
  have h0_lt2 : σ 0 < (2 : Fin 5) := by
    by_contra hle
    have hge : (2 : Fin 5) ≤ σ 0 := not_lt.mp hle
    have hsub : ({((0 : Fin 5), σ.symm 0), ((0 : Fin 5), σ.symm 1)} : Finset (Fin 5 × Fin 5)) ⊆
        (Finset.univ : Finset (Fin 5 × Fin 5)).filter (fun p => p.1 < p.2 ∧ σ p.2 < σ p.1) := by
      intro p hp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rcases hp with rfl | rfl
      · have hne0 : σ.symm 0 ≠ 0 := fun h => by
          have h0 : σ 0 = 0 := by simpa using (congrArg σ h).symm
          rw [h0] at hge; exact absurd hge (by decide)
        exact ⟨Fin.pos_of_ne_zero hne0, by simpa using (by decide : (0 : Fin 5) < 2).trans_le hge⟩
      · have hne1 : σ.symm 1 ≠ 0 := fun h => by
          have h1 : σ 0 = 1 := by simpa using (congrArg σ h).symm
          rw [h1] at hge; exact absurd hge (by decide)
        exact ⟨Fin.pos_of_ne_zero hne1, by simpa using (by decide : (1 : Fin 5) < 2).trans_le hge⟩
    have hp_ne : ((0 : Fin 5), σ.symm 0) ≠ ((0 : Fin 5), σ.symm 1) := fun h =>
      absurd (σ.symm.injective (congrArg Prod.snd h)) (by decide)
    have hle2 : 2 ≤ permInversions σ :=
      calc 2 = ({((0 : Fin 5), σ.symm 0), ((0 : Fin 5), σ.symm 1)} : Finset (Fin 5 × Fin 5)).card :=
          (Finset.card_pair hp_ne).symm
        _ ≤ permInversions σ := Finset.card_le_card hsub
    omega
  have h0_ne4 : σ 0 ≠ 4 := fun h => by
    have : σ 0 < 2 := h0_lt2
    rw [h] at this; exact absurd this (by decide)
  have h1_ne4 : σ 1 ≠ 4 := fun h => by
    have hsub : ({((1 : Fin 5), (2 : Fin 5)), ((1 : Fin 5), (3 : Fin 5)), ((1 : Fin 5), (4 : Fin 5))} : Finset (Fin 5 × Fin 5)) ⊆
        (Finset.univ : Finset (Fin 5 × Fin 5)).filter (fun p => p.1 < p.2 ∧ σ p.2 < σ p.1) := by
      intro p hp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rcases hp with rfl | rfl | rfl
      · exact ⟨by decide, by rw [h]; exact lt_of_le_of_ne (Fin.is_le _) (fun he => absurd (σ.injective (he.trans h.symm)) (by decide))⟩
      · exact ⟨by decide, by rw [h]; exact lt_of_le_of_ne (Fin.is_le _) (fun he => absurd (σ.injective (he.trans h.symm)) (by decide))⟩
      · exact ⟨by decide, by rw [h]; exact lt_of_le_of_ne (Fin.is_le _) (fun he => absurd (σ.injective (he.trans h.symm)) (by decide))⟩
    have hcard3 : ({((1 : Fin 5), (2 : Fin 5)), ((1 : Fin 5), (3 : Fin 5)), ((1 : Fin 5), (4 : Fin 5))} : Finset (Fin 5 × Fin 5)).card = 3 := by decide
    have hle3 : 3 ≤ permInversions σ := hcard3 ▸ Finset.card_le_card hsub
    omega
  exact ⟨hL, hR, h0_lt2, h0_ne4, h1_ne4⟩

private lemma inv_two_left_or_right (σ : Equiv.Perm (Fin 5)) (hinv : permInversions σ = 2) :
    (∀ i : Fin 5, i < (3 : Fin 5) → σ.symm i < σ.symm 4) ∨
    (∀ k : Fin 5, (1 : Fin 5) < k → σ 0 < σ k) := by
  by_cases hL : ∀ i : Fin 5, i < (3 : Fin 5) → σ.symm i < σ.symm 4
  · exact Or.inl hL
  · right
    push Not at hL
    obtain ⟨i, hi, hle⟩ := hL
    let τ := σ.symm
    have hτ_inv : permInversions τ = 2 := by dsimp [τ]; rw [permInversions_symm, hinv]
    have h4i : τ 4 < τ i := lt_of_le_of_ne hle (τ.injective.ne (fun h => by
      have : (4 : Fin 5).val = i.val := congrArg Fin.val h
      have : i.val < 3 := hi; omega))
    have hi_vals : i = 0 ∨ i = 1 ∨ i = 2 := by
      fin_cases i <;> simp at hi ⊢
    rcases hi_vals with rfl | rfl | rfl
    · exfalso
      let q₁ : Fin 5 × Fin 5 := if τ 1 < τ 0 then (0, 1) else (1, 4)
      let q₂ : Fin 5 × Fin 5 := if τ 2 < τ 0 then (0, 2) else (2, 4)
      have hsub : ({((0 : Fin 5), (4 : Fin 5)), q₁, q₂} : Finset (Fin 5 × Fin 5)) ⊆
          (Finset.univ : Finset (Fin 5 × Fin 5)).filter (fun p => p.1 < p.2 ∧ τ p.2 < τ p.1) := by
        intro p hp
        simp only [Finset.mem_insert, Finset.mem_singleton] at hp
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rcases hp with rfl | rfl | rfl
        · exact ⟨by decide, h4i⟩
        · dsimp [q₁]; split_ifs with h10
          · exact ⟨by decide, h10⟩
          · exact ⟨by decide, lt_trans h4i (lt_of_le_of_ne (not_lt.mp h10) (τ.injective.ne (by decide)))⟩
        · dsimp [q₂]; split_ifs with h20
          · exact ⟨by decide, h20⟩
          · exact ⟨by decide, lt_trans h4i (lt_of_le_of_ne (not_lt.mp h20) (τ.injective.ne (by decide)))⟩
      have hcard3 : ({((0 : Fin 5), (4 : Fin 5)), q₁, q₂} : Finset (Fin 5 × Fin 5)).card = 3 := by
        by_cases h10 : τ 1 < τ 0 <;> by_cases h20 : τ 2 < τ 0 <;>
          simp only [q₁, q₂, h10, h20, ↓reduceIte] <;> decide
      have hle3 : 3 ≤ permInversions τ := hcard3 ▸ Finset.card_le_card hsub
      omega
    · exfalso
      let q₁ : Fin 5 × Fin 5 := if τ 2 < τ 1 then (1, 2) else (2, 4)
      let q₂ : Fin 5 × Fin 5 := if τ 3 < τ 1 then (1, 3) else (3, 4)
      have hsub : ({((1 : Fin 5), (4 : Fin 5)), q₁, q₂} : Finset (Fin 5 × Fin 5)) ⊆
          (Finset.univ : Finset (Fin 5 × Fin 5)).filter (fun p => p.1 < p.2 ∧ τ p.2 < τ p.1) := by
        intro p hp
        simp only [Finset.mem_insert, Finset.mem_singleton] at hp
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rcases hp with rfl | rfl | rfl
        · exact ⟨by decide, h4i⟩
        · dsimp [q₁]; split_ifs with h21
          · exact ⟨by decide, h21⟩
          · exact ⟨by decide, lt_trans h4i (lt_of_le_of_ne (not_lt.mp h21) (τ.injective.ne (by decide)))⟩
        · dsimp [q₂]; split_ifs with h31
          · exact ⟨by decide, h31⟩
          · exact ⟨by decide, lt_trans h4i (lt_of_le_of_ne (not_lt.mp h31) (τ.injective.ne (by decide)))⟩
      have hcard3 : ({((1 : Fin 5), (4 : Fin 5)), q₁, q₂} : Finset (Fin 5 × Fin 5)).card = 3 := by
        by_cases h21 : τ 2 < τ 1 <;> by_cases h31 : τ 3 < τ 1 <;>
          simp only [q₁, q₂, h21, h31, ↓reduceIte] <;> decide
      have hle3 : 3 ≤ permInversions τ := hcard3 ▸ Finset.card_le_card hsub
      omega
    · have hσ0 : σ 0 = 0 := by
        by_contra hne0
        let j : Fin 5 := σ 0
        have hj_pos : 0 < j := Fin.pos_of_ne_zero hne0
        have hτ0_pos : 0 < τ 0 := Fin.pos_of_ne_zero fun h => hne0 (by
          have := congrArg σ h; simp only [τ, Equiv.apply_symm_apply] at this; exact this.symm)
        have hτj : τ j = 0 := Equiv.symm_apply_apply σ 0
        let q₁ : Fin 5 × Fin 5 := if τ 3 < τ 2 then (2, 3) else (3, 4)
        have hsub : ({((2 : Fin 5), (4 : Fin 5)), q₁, ((0 : Fin 5), j)} : Finset (Fin 5 × Fin 5)) ⊆
            (Finset.univ : Finset (Fin 5 × Fin 5)).filter (fun p => p.1 < p.2 ∧ τ p.2 < τ p.1) := by
          intro p hp
          simp only [Finset.mem_insert, Finset.mem_singleton] at hp
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          rcases hp with rfl | rfl | rfl
          · exact ⟨by decide, h4i⟩
          · dsimp [q₁]; split_ifs with h32
            · exact ⟨by decide, h32⟩
            · exact ⟨by decide, lt_trans h4i (lt_of_le_of_ne (not_lt.mp h32) (τ.injective.ne (by decide)))⟩
          · exact ⟨hj_pos, hτj ▸ hτ0_pos⟩
        have h0j_ne1 : ((0 : Fin 5), j) ≠ ((2 : Fin 5), (4 : Fin 5)) := fun h => by
          have hv := congrArg Prod.fst h; simp at hv
        have h0j_ne2 : ((0 : Fin 5), j) ≠ q₁ := by
          dsimp [q₁]; split_ifs <;> intro h <;> have hv := congrArg Prod.fst h <;> simp at hv
        have h24_ne : ((2 : Fin 5), (4 : Fin 5)) ≠ q₁ := by
          by_cases h32 : τ 3 < τ 2 <;> simp only [q₁, h32, ↓reduceIte] <;> decide
        have hcard3 : ({((2 : Fin 5), (4 : Fin 5)), q₁, ((0 : Fin 5), j)} : Finset (Fin 5 × Fin 5)).card = 3 := by
          rw [Finset.card_insert_of_notMem (by simp [h24_ne, h0j_ne1.symm]),
            Finset.card_pair h0j_ne2.symm]
        have hle3 : 3 ≤ permInversions τ := hcard3 ▸ Finset.card_le_card hsub
        omega
      intro k hk
      rw [hσ0]
      exact Fin.pos_of_ne_zero fun h => by
        have : k = 0 := σ.injective (h.trans hσ0.symm)
        rw [this] at hk; exact absurd hk (by decide)

private lemma case3_left_witness (P : DualConfig) (hgp : IsGenPos P)
    (h_shat : ∀ m : Fin 5 → Bool, ∃ z : ℝ × ℝ, InOmega z ∧ RealizesDualMask P m z)
    (hleft : StrictMono (leftKey P))
    (h_edges : ∀ i j : Fin 5, i < j → (i, j) ≠ (0, 4) → (i, j) ∈ threeCrossGraph P) :
    ∃ τm : ℝ, 0 < τm ∧ τm < apexRay P 1 ∧
      ∀ v : Fin 5, v ≠ 4 → clippedG P 4 τm < clippedG P v τm := by
  have hap1 := (supportF_branch_switch P hgp).2 1
  by_cases h4 : 0 < supportF P 4 0
  · have hj_pos : ∀ j : Fin 5, j ≠ 4 → 0 < supportF P j 0 ∧ supportF P 4 0 < supportF P j 0 := by
      intro j hj
      have hj_lt : j < 4 := lt_of_le_of_ne (Fin.is_le j) hj
      have hlk := hleft hj_lt
      unfold leftKey at hlk
      simp only [h4, ↓reduceIte] at hlk
      split_ifs at hlk with hj0
      · exact ⟨hj0, by linarith⟩
      · exfalso; linarith [(posInterval_eq_Ioo P hgp j).1]
    have hopen : IsOpen {t : ℝ | 0 < supportF P 4 t ∧ ∀ j : Fin 5, j ≠ 4 → supportF P 4 t < supportF P j t} := by
      have h1 : IsOpen {t : ℝ | 0 < supportF P 4 t} :=
        isOpen_lt continuous_const (supportF_continuous P 4)
      have h2 : IsOpen (⋂ j : Fin 5, if j ≠ 4 then {t : ℝ | supportF P 4 t < supportF P j t} else Set.univ) := by
        refine isOpen_iInter_of_finite fun j => ?_
        split_ifs
        · exact isOpen_lt (supportF_continuous P 4) (supportF_continuous P j)
        · exact isOpen_univ
      convert IsOpen.inter h1 h2 using 1
      ext t; simp [Set.mem_iInter]
    obtain ⟨δ, hδ, hsub⟩ := Metric.isOpen_iff.mp hopen 0 ⟨h4, fun j hj => (hj_pos j hj).2⟩
    let τm : ℝ := min (δ / 2) (apexRay P 1 / 2)
    have hτ_pos : 0 < τm := lt_min (by linarith) (by linarith [hap1.1])
    have hτ_lt : τm < apexRay P 1 := lt_of_le_of_lt (min_le_right _ _) (by linarith [hap1.1])
    have hτ_ball : τm ∈ Metric.ball (0 : ℝ) δ := by
      rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hτ_pos]
      exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
    obtain ⟨hf4, hlt_all⟩ := Set.mem_setOf.mp (hsub hτ_ball)
    refine ⟨τm, hτ_pos, hτ_lt, fun j hj => ?_⟩
    have hj_gt := hlt_all j hj
    have hj_pos' := lt_trans hf4 hj_gt
    unfold clippedG
    rw [max_eq_left (le_of_lt hf4), max_eq_left (le_of_lt hj_pos')]
    exact hj_gt
  · obtain ⟨hp4_pos, hf4_zero⟩ := supportF_posLeft_zero P hgp 4 h4
    have h14 := three_crossing_structure P hgp h_shat hleft
      (h_edges 1 4 (by decide) (by decide))
    have h01 := three_crossing_structure P hgp h_shat hleft
      (h_edges 0 1 (by decide) (by decide))
    refine ⟨posLeft P 4, hp4_pos, h14.1, fun v hv => ?_⟩
    have hv_lt : v < 4 := lt_of_le_of_ne (Fin.is_le v) hv
    have hpv_lt : posLeft P v < posLeft P 4 := by
      by_cases hv0 : 0 < supportF P v 0
      · rw [posLeft_eq_zero_of_pos_at_zero P hgp v hv0]; exact hp4_pos
      · have hlk := hleft hv_lt
        unfold leftKey at hlk
        simp only [hv0, h4, ↓reduceIte] at hlk
        exact hlk
    have h_ap1_lt_Rv : apexRay P 1 < posRight P v := by
      fin_cases v
      · exact h01.2.2.1
      · exact (posInterval_eq_Ioo P hgp 1).2.2.1
      · have h24 := three_crossing_structure P hgp h_shat hleft (h_edges 2 4 (by decide) (by decide))
        have h12 := three_crossing_structure P hgp h_shat hleft (h_edges 1 2 (by decide) (by decide))
        exact lt_trans h12.2.1 (lt_trans h24.2.1 h24.2.2.1)
      · have h34 := three_crossing_structure P hgp h_shat hleft (h_edges 3 4 (by decide) (by decide))
        have h13 := three_crossing_structure P hgp h_shat hleft (h_edges 1 3 (by decide) (by decide))
        exact lt_trans h13.2.1 (lt_trans h34.2.1 h34.2.2.1)
      · exact absurd rfl hv
    have hfv_pos : 0 < supportF P v (posLeft P 4) :=
      ((posInterval_eq_Ioo P hgp v).2.2.2.2 (posLeft P 4)).mpr
        ⟨hpv_lt, lt_trans h14.1 h_ap1_lt_Rv⟩ |>.2.2
    unfold clippedG
    rw [hf4_zero, max_self, max_eq_left (le_of_lt hfv_pos)]
    exact hfv_pos

private def normPair5 (a b : Nat) : Nat × Nat :=
  if a ≤ b then (a, b) else (b, a)

private def checkN7T3bar0Diagonals : Bool :=
  let khat : List Nat := [0, 1, 2, 3, 4, 0, 1, 2, 3, 4]
  let diags : List (Nat × Nat) := [(0, 2), (0, 3), (1, 3), (1, 4), (2, 4)]
  let interiorPos : List Nat := [1, 2, 3, 4, 5, 6, 7, 8]
  interiorPos.all fun i1 =>
    interiorPos.all fun i2 =>
      interiorPos.all fun i3 =>
        if !(i1 < i2 && i2 < i3) then true
        else
          let rem : List Nat := [i1, i2, i3]
          let hullIdx : List Nat := (List.range 10).filter (fun p => !(rem.contains p))
          let adj := hullIdx.zip hullIdx.tail
          let adjDistinct := adj.all fun (a, b) => khat.getD a 0 != khat.getD b 0
          if !adjDistinct then true
          else
            let a2 : List (Nat × Nat) :=
              adj.map fun (a, b) => normPair5 (khat.getD a 0) (khat.getD b 0)
            let b2 : List (Nat × Nat) :=
              (adj.product rem).flatMap fun ((a, b), r) =>
                if a < r && r < b then
                  [normPair5 (khat.getD r 0) (khat.getD a 0),
                   normPair5 (khat.getD r 0) (khat.getD b 0)]
                else []
            let realizedPairs := a2 ++ b2
            !(diags.all fun d => realizedPairs.contains d)

private theorem v_n7_T3bar0_diagonals_lt_5 : checkN7T3bar0Diagonals = true := by
  decide

private lemma compressAdj_length_le : ∀ l : List (Fin 5), (compressAdj l).length ≤ l.length
  | [] => le_rfl
  | [_] => le_rfl
  | c₁ :: c₂ :: rest => by
    simp only [compressAdj]
    split_ifs
    · exact le_trans (compressAdj_length_le (c₂ :: rest)) (by simp)
    · have := compressAdj_length_le (c₂ :: rest)
      simp only [List.length_cons] at this ⊢; omega

private lemma compressAdj_eq_self_of_adj_ne :
    ∀ l : List (Fin 5), (∀ (i : ℕ) (hi : i + 1 < l.length),
      l[i]'(by omega) ≠ l[i + 1]'hi) → compressAdj l = l
  | [], _ => rfl
  | [_], _ => rfl
  | c₁ :: c₂ :: rest, hadj => by
    have hne : c₁ ≠ c₂ := hadj 0 (by simp)
    simp only [compressAdj, hne, ↓reduceIte]
    congr 1
    refine compressAdj_eq_self_of_adj_ne (c₂ :: rest) fun i hi => ?_
    exact hadj (i + 1) (by simpa using hi)

private lemma perm_eq_id_of_inv_zero (σ : Equiv.Perm (Fin 5)) (hinv : permInversions σ = 0) :
    ∀ r : Fin 5, σ r = r := by
  have hstrict : ∀ τ : Equiv.Perm (Fin 5), StrictMono τ → ∀ r : Fin 5, r.val ≤ (τ r).val := by
    intro τ hτ r
    have h_ind : ∀ n : ℕ, (hn : n < 5) → n ≤ (τ ⟨n, hn⟩).val := by
      intro n hn
      induction n with
      | zero => exact Nat.zero_le _
      | succ m ih =>
        have hlt := hτ (show (⟨m, by omega⟩ : Fin 5) < ⟨m + 1, hn⟩ by show m < m + 1; omega)
        have ihm := ih (by omega)
        have hlt' : (τ ⟨m, by omega⟩).val < (τ ⟨m + 1, hn⟩).val := hlt
        omega
    exact h_ind r.val r.isLt
  have hσ_mono : StrictMono σ := by
    intro r s hrs; by_contra hle
    have hgt : σ s < σ r := lt_of_le_of_ne (not_lt.mp hle) (σ.injective.ne (ne_of_gt hrs))
    have hpos : 0 < permInversions σ := Finset.card_pos.mpr ⟨(r, s), by simp [hrs, hgt]⟩
    omega
  have hσ_symm_mono : StrictMono σ.symm := by
    intro r s hrs; by_contra hle
    have hord : σ.symm s ≤ σ.symm r := not_lt.mp hle
    have hm := hσ_mono.monotone hord
    simp only [Equiv.apply_symm_apply] at hm
    exact not_lt.mpr hm hrs
  intro r
  have h1 := hstrict σ hσ_mono r
  have h2 := hstrict σ.symm hσ_symm_mono (σ r)
  rw [Equiv.symm_apply_apply] at h2
  exact Fin.ext (le_antisymm h2 h1)

private def seq10Equiv : Equiv.Perm (Fin 10) where
  toFun k := if hk : k.val < 5 then ⟨2 * k.val, by omega⟩
    else ⟨2 * (k.val - 5) + 1, by have := k.isLt; omega⟩
  invFun a := if ha : a.val % 2 = 0 then ⟨a.val / 2, by have := a.isLt; omega⟩
    else ⟨a.val / 2 + 5, by have := a.isLt; omega⟩
  left_inv k := by
    rcases k with ⟨k, hk⟩
    interval_cases k <;> simp
  right_inv a := by
    rcases a with ⟨a, ha⟩
    interval_cases a <;> simp

private lemma seq10Equiv_color (k : Fin 10) :
    (vecColor (seq10Equiv k)).val = k.val % 5 := by
  have := k.isLt
  dsimp [vecColor, seq10Equiv]
  split_ifs <;> dsimp <;> omega

private lemma mem_pureHullPairs_iff_adj (P : DualConfig) (hgp : IsGenPos P)
    (htop : ∀ {t : ℝ}, 0 ≤ t → t ≤ 3 → 0 < topEnv P t)
    (h_adj_ne : ∀ (r : Fin ((topTiePts P).card)),
      hullColors P ⟨r.val, by omega⟩ ≠ hullColors P ⟨r.val + 1, by omega⟩)
    (S : Finset (Fin 5)) (hS_card : S.card = 2) (hS : S ∈ pureHullPairs P) :
    ∃ r : Fin ((topTiePts P).card),
      ({hullColors P ⟨r.val, by omega⟩, hullColors P ⟨r.val + 1, by omega⟩} : Finset (Fin 5)) = S := by
  obtain ⟨r₁, r₂, hr12, himg⟩ := (pure_hull_pairs_eq P hgp htop S hS_card).mp hS
  have hlt12 : r₁ < r₂ := by
    by_contra hle
    have heq : r₁ = r₂ := le_antisymm hr12 (not_lt.mp hle)
    subst heq
    have h1 : (((Finset.univ : Finset (Fin ((topTiePts P).card + 1))).filter
        (fun r => r₁ ≤ r ∧ r ≤ r₁)).image (hullColors P)).card ≤ 1 := by
      have : (Finset.univ : Finset (Fin ((topTiePts P).card + 1))).filter (fun r => r₁ ≤ r ∧ r ≤ r₁) = {r₁} := by
        ext r; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        exact ⟨fun ⟨a, b⟩ => le_antisymm b a, fun h => h ▸ ⟨le_rfl, le_rfl⟩⟩
      rw [this, Finset.image_singleton, Finset.card_singleton]
    rw [himg, hS_card] at h1; omega
  refine ⟨⟨r₁.val, by have : r₁.val < r₂.val := hlt12; omega⟩, ?_⟩
  let r₀ : Fin ((topTiePts P).card + 1) := ⟨r₁.val, by omega⟩
  let r₁' : Fin ((topTiePts P).card + 1) := ⟨r₁.val + 1, by have : r₁.val < r₂.val := hlt12; omega⟩
  have hr₀_mem : hullColors P r₀ ∈ S := by
    rw [← himg]; exact Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_rfl, hr12⟩)
  have hr₁_mem : hullColors P r₁' ∈ S := by
    rw [← himg]; exact Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
      change r₁.val ≤ r₁.val + 1; omega, hlt12⟩)
  have hpair_sub : ({hullColors P r₀, hullColors P r₁'} : Finset (Fin 5)) ⊆ S := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact hr₀_mem
    · rw [Finset.mem_singleton.mp hx]; exact hr₁_mem
  have hne := h_adj_ne ⟨r₁.val, by have : r₁.val < r₂.val := hlt12; omega⟩
  exact Finset.eq_of_subset_of_card_le hpair_sub (by rw [hS_card, Finset.card_pair hne])

private lemma list_eq_of_pairwise_lt_of_perm :
    ∀ {l₁ l₂ : List ℕ}, l₁.Pairwise (· < ·) → l₂.Pairwise (· < ·) →
      (∀ n, n ∈ l₁ ↔ n ∈ l₂) → l₁ = l₂
  | [], [], _, _, _ => rfl
  | [], b :: _, _, _, h => absurd ((h b).mpr (by simp)) (by simp)
  | a :: _, [], _, _, h => absurd ((h a).mp (by simp)) (by simp)
  | a :: t₁, b :: t₂, hp₁, hp₂, h => by
    have ha2 : a ∈ b :: t₂ := (h a).mp (by simp)
    have hb1 : b ∈ a :: t₁ := (h b).mpr (by simp)
    have ha_le : a ≤ b := by
      rcases List.mem_cons.mp hb1 with rfl | hb
      · exact le_rfl
      · exact le_of_lt ((List.pairwise_cons.mp hp₁).1 b hb)
    have hb_le : b ≤ a := by
      rcases List.mem_cons.mp ha2 with rfl | ha
      · exact le_rfl
      · exact le_of_lt ((List.pairwise_cons.mp hp₂).1 a ha)
    have hab : a = b := le_antisymm ha_le hb_le
    subst hab
    congr 1
    refine list_eq_of_pairwise_lt_of_perm
      (List.pairwise_cons.mp hp₁).2 (List.pairwise_cons.mp hp₂).2 fun n => ?_
    have h1 := (List.pairwise_cons.mp hp₁).1 n
    have h2 := (List.pairwise_cons.mp hp₂).1 n
    constructor
    · intro hn
      rcases List.mem_cons.mp ((h n).mp (by simp [hn])) with rfl | hmem
      · exact absurd hn (fun hm => (lt_irrefl _) (h1 hm))
      · exact hmem
    · intro hn
      rcases List.mem_cons.mp ((h n).mpr (by simp [hn])) with rfl | hmem
      · exact absurd hn (fun hm => (lt_irrefl _) (h2 hm))
      · exact hmem

private lemma elim_n7_case4_hull_contra
    (P' : DualConfig) (hgp' : IsGenPos P')
    (htop' : ∀ {t : ℝ}, 0 ≤ t → t ≤ 3 → 0 < topEnv P' t)
    (h_shat' : ∀ m : Fin 5 → Bool, ∃ z : ℝ × ℝ, InOmega z ∧ RealizesDualMask P' m z)
    (hcard7 : (topTiePts P').card + 1 = 7)
    (pos : Fin 7 → Fin 10)
    (hpos_eq : ∀ r : Fin 7, hullIdx P' (Fin.cast hcard7.symm r) = seq10Equiv (pos r))
    (hpos_mono : StrictMono pos)
    (hseq_mono : StrictMono (fun k : Fin 10 => rayParam (P'.vec (seq10Equiv k))))
    (h_adj_ne : ∀ r : Fin 6,
      hullColors P' ⟨r.val, by omega⟩ ≠ hullColors P' ⟨r.val + 1, by omega⟩)
    (hpos0 : pos ⟨0, by omega⟩ = ⟨0, by omega⟩)
    (hpos6 : pos ⟨6, by omega⟩ = ⟨9, by omega⟩) : False := by
  let Rem : Finset (Fin 10) := Finset.univ \ Finset.univ.image pos
  have hRem_card : Rem.card = 3 := by
    rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin,
      Finset.card_image_of_injective _ hpos_mono.injective, Finset.card_fin]
  let remSort : List (Fin 10) := Rem.sort (· ≤ ·)
  have hremSort_len : remSort.length = 3 := by simp [remSort, Finset.length_sort, hRem_card]
  have hrem0 : 0 < remSort.length := by rw [hremSort_len]; omega
  have hrem1 : 1 < remSort.length := by rw [hremSort_len]; omega
  have hrem2 : 2 < remSort.length := by rw [hremSort_len]; omega
  have hremSort_pw : remSort.Pairwise (· < ·) := Rem.sortedLT_sort.pairwise
  obtain ⟨i₁, i₂, i₃, hi12, hi23, hi1_ge1, hi3_le8, hrem_eq⟩ :
      ∃ i₁ i₂ i₃ : ℕ, i₁ < i₂ ∧ i₂ < i₃ ∧ 1 ≤ i₁ ∧ i₃ ≤ 8 ∧
        remSort.map Fin.val = [i₁, i₂, i₃] := by
    refine ⟨(remSort[0]'hrem0).val, (remSort[1]'hrem1).val, (remSort[2]'hrem2).val,
      List.pairwise_iff_getElem.mp hremSort_pw 0 1 hrem0 hrem1 (by omega),
      List.pairwise_iff_getElem.mp hremSort_pw 1 2 hrem1 hrem2 (by omega), ?_, ?_, ?_⟩
    · have hm : remSort[0]'hrem0 ∈ Rem := (Rem.mem_sort (· ≤ ·)).mp (List.getElem_mem hrem0)
      have hnot : remSort[0]'hrem0 ≠ ⟨0, by omega⟩ := fun h =>
        (Finset.mem_sdiff.mp hm).2 (Finset.mem_image.mpr ⟨⟨0, by omega⟩, Finset.mem_univ _, hpos0.trans h.symm⟩)
      have hv : (remSort[0]'hrem0).val ≠ 0 := fun h => hnot (Fin.ext h)
      omega
    · have hm : remSort[2]'hrem2 ∈ Rem := (Rem.mem_sort (· ≤ ·)).mp (List.getElem_mem hrem2)
      have hnot : remSort[2]'hrem2 ≠ ⟨9, by omega⟩ := fun h =>
        (Finset.mem_sdiff.mp hm).2 (Finset.mem_image.mpr ⟨⟨6, by omega⟩, Finset.mem_univ _, hpos6.trans h.symm⟩)
      have hv : (remSort[2]'hrem2).val ≠ 9 := fun h => hnot (Fin.ext h)
      have hlt10 : (remSort[2]'hrem2).val < 10 := (remSort[2]'hrem2).isLt
      omega
    · refine List.ext_getElem (by simp [hremSort_len]) fun m hm1 hm2 => ?_
      have hm3 : m < 3 := by simp [hremSort_len] at hm1; exact hm1
      interval_cases m <;> simp
  let remList : List ℕ := [i₁, i₂, i₃]
  let hullNat : List ℕ := (List.range 10).filter (fun p => !(remList.contains p))
  have hmem_remList : ∀ x : Fin 10, x.val ∈ remList ↔ x ∈ Rem := by
    intro x
    have h1 : x.val ∈ remSort.map Fin.val ↔ x ∈ Rem := by
      simp only [List.mem_map, Fin.val_inj, exists_eq_right, remSort, Finset.mem_sort]
    change x.val ∈ [i₁, i₂, i₃] ↔ x ∈ Rem
    rw [← hrem_eq]
    exact h1
  have hhullNat_eq : hullNat = List.ofFn (fun r : Fin 7 => (pos r).val) := by
    have hp1 : hullNat.Pairwise (· < ·) :=
      (List.pairwise_lt_range.filter _).imp (fun h => h)
    have hp2 : (List.ofFn (fun r : Fin 7 => (pos r).val)).Pairwise (· < ·) := by
      rw [List.pairwise_iff_getElem]
      intro a b ha hb hab
      rw [List.length_ofFn] at ha hb
      simp only [List.getElem_ofFn]
      exact hpos_mono (show (⟨a, ha⟩ : Fin 7) < ⟨b, hb⟩ from hab)
    refine list_eq_of_pairwise_lt_of_perm hp1 hp2 fun n => ?_
    simp only [hullNat, List.mem_filter, List.mem_range, Bool.not_eq_true', List.mem_ofFn]
    constructor
    · intro ⟨hn10, hnot⟩
      have hn_not_rem : (⟨n, hn10⟩ : Fin 10) ∉ Rem := fun h =>
        absurd (by simpa [remList] using (hmem_remList ⟨n, hn10⟩).mpr h)
          (by simpa [remList] using hnot)
      have hn_img : (⟨n, hn10⟩ : Fin 10) ∈ Finset.univ.image pos := by
        by_contra hni; exact hn_not_rem (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hni⟩)
      obtain ⟨r, _, hr⟩ := Finset.mem_image.mp hn_img
      exact ⟨r, congrArg Fin.val hr⟩
    · rintro ⟨r, rfl⟩
      refine ⟨(pos r).isLt, ?_⟩
      rw [Bool.eq_false_iff]; intro hc
      have hr_rem := (hmem_remList (pos r)).mp (by simpa [remList] using hc)
      exact (Finset.mem_sdiff.mp hr_rem).2 (Finset.mem_image_of_mem _ (Finset.mem_univ r))
  let khat : List ℕ := [0, 1, 2, 3, 4, 0, 1, 2, 3, 4]
  have hkhat_eq : ∀ x : Fin 10, khat.getD x.val 0 = (vecColor (seq10Equiv x)).val := by
    intro x
    rw [seq10Equiv_color]
    fin_cases x <;> rfl
  let adj := hullNat.zip hullNat.tail
  have hlen_adj : adj.length = 6 := by
    dsimp [adj]; rw [hhullNat_eq, List.length_zip, List.length_tail, List.length_ofFn]; omega
  have hget_adj : ∀ (m : ℕ) (hm : m < adj.length),
      adj[m]'hm = ((pos ⟨m, by omega⟩).val, (pos ⟨m + 1, by omega⟩).val) := by
    intro m hm
    dsimp [adj]
    rw [List.getElem_zip]
    simp only [hhullNat_eq, List.getElem_tail, List.getElem_ofFn]
  have hadj_pair : ∀ r : Fin 6, ((pos ⟨r.val, by omega⟩).val, (pos ⟨r.val + 1, by omega⟩).val) ∈ adj := by
    intro r
    have hr6 : r.val < adj.length := by rw [hlen_adj]; exact r.isLt
    rw [← hget_adj r.val hr6]
    exact List.getElem_mem hr6
  let a2 : List (ℕ × ℕ) :=
    adj.map fun (a, b) => normPair5 (khat.getD a 0) (khat.getD b 0)
  let b2 : List (ℕ × ℕ) :=
    (adj.product remList).flatMap fun ((a, b), r) =>
      if a < r && r < b then
        [normPair5 (khat.getD r 0) (khat.getD a 0),
         normPair5 (khat.getD r 0) (khat.getD b 0)]
      else []
  let diags : List (ℕ × ℕ) := [(0, 2), (0, 3), (1, 3), (1, 4), (2, 4)]
  have hdiag_covered : ∀ d ∈ diags, (a2 ++ b2).contains d = true := by
    intro d hd
    have hd_lt : d.1 < d.2 ∧ d.2 < 5 := by
      simp only [diags, List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl | rfl | rfl | rfl <;> omega
    let c₁ : Fin 5 := ⟨d.1, by omega⟩
    let c₂ : Fin 5 := ⟨d.2, by omega⟩
    have hc12 : c₁ ≠ c₂ := fun h => by have := congrArg Fin.val h; dsimp [c₁, c₂] at this; omega
    let S : Finset (Fin 5) := {c₁, c₂}
    have hS_card : S.card = 2 := Finset.card_pair hc12
    have hnorm_pair : ∀ x y : Fin 5, ({x, y} : Finset (Fin 5)) = S →
        normPair5 x.val y.val = d := by
      intro x y hxy
      have hx : x ∈ S := hxy ▸ Finset.mem_insert_self x _
      have hy : y ∈ S := hxy ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self y)
      have hne_xy : x ≠ y := fun h => by
        rw [h, Finset.pair_eq_singleton] at hxy
        have := congrArg Finset.card hxy
        rw [Finset.card_singleton, hS_card] at this; omega
      simp only [S, Finset.mem_insert, Finset.mem_singleton] at hx hy
      dsimp [normPair5]
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
      · exact absurd rfl hne_xy
      · rw [if_pos (le_of_lt hd_lt.1)]
      · rw [if_neg (not_le.mpr hd_lt.1)]
      · exact absurd rfl hne_xy
    rw [List.contains_eq_mem, decide_eq_true_eq]
    by_cases hpure : S ∈ pureHullPairs P'
    · obtain ⟨r, hr_eq⟩ := mem_pureHullPairs_iff_adj P' hgp' htop'
        (fun r => h_adj_ne ⟨r.val, by omega⟩) S hS_card hpure
      have hr6 : r.val < 6 := by have := r.isLt; omega
      refine List.mem_append_left b2 (List.mem_map.mpr
        ⟨((pos ⟨r.val, by omega⟩).val, (pos ⟨r.val + 1, by omega⟩).val),
          hadj_pair ⟨r.val, hr6⟩, ?_⟩)
      dsimp only
      rw [hkhat_eq, hkhat_eq]
      have hc_l : vecColor (seq10Equiv (pos ⟨r.val, by omega⟩)) = hullColors P' ⟨r.val, by omega⟩ := by
        unfold hullColors; rw [← hpos_eq ⟨r.val, by omega⟩]; rfl
      have hc_r : vecColor (seq10Equiv (pos ⟨r.val + 1, by omega⟩)) = hullColors P' ⟨r.val + 1, by omega⟩ := by
        unfold hullColors; rw [← hpos_eq ⟨r.val + 1, by omega⟩]; rfl
      rw [hc_l, hc_r]
      exact hnorm_pair _ _ hr_eq
    · obtain ⟨z, hz, hreal⟩ := h_shat' (fun i => !decide (i ∈ S))
      obtain ⟨a, ha_not, ha_mem, ha_gt, ha_lt⟩ :=
        interior_assisted_pairs P' hgp' htop' S hS_card hpure z hz hreal
      let xa : Fin 10 := seq10Equiv.symm a
      have hxa_not : xa ∉ Finset.univ.image pos := by
        intro hx
        obtain ⟨r, _, hr⟩ := Finset.mem_image.mp hx
        apply ha_not (Fin.cast hcard7.symm r)
        have := congrArg seq10Equiv hr
        rw [← hpos_eq r] at this
        simpa [xa] using this
      have hxa_rem : xa.val ∈ remList :=
        (hmem_remList xa).mpr (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hxa_not⟩)
      have hdom := hull_domination P' hgp' htop' a ha_not
      rcases hdom with ⟨hray, _⟩ | ⟨hray, _⟩ | ⟨r, hr, hlt1, hlt2, hact⟩
      · exfalso
        have ha_eq : P'.vec a = P'.vec (seq10Equiv xa) := by simp [xa]
        rw [ha_eq] at hray
        unfold hullVerts at hray
        have h0_eq : hullIdx P' ⟨0, by omega⟩ = seq10Equiv (pos ⟨0, by omega⟩) := by
          simpa using hpos_eq ⟨0, by omega⟩
        rw [h0_eq, hpos0] at hray
        have hle : (⟨0, by omega⟩ : Fin 10) ≤ xa := Fin.zero_le xa
        have hm := hseq_mono.monotone hle
        linarith
      · exfalso
        have ha_eq : P'.vec a = P'.vec (seq10Equiv xa) := by simp [xa]
        rw [ha_eq] at hray
        unfold hullVerts at hray
        have h6_eq : hullIdx P' ⟨(topTiePts P').card + 1 - 1, by omega⟩ = seq10Equiv (pos ⟨6, by omega⟩) := by
          have := hpos_eq ⟨6, by omega⟩
          convert this using 2; ext; simp only [Fin.val_cast]; omega
        rw [h6_eq, hpos6] at hray
        have hle : xa ≤ ⟨9, by omega⟩ := Fin.is_le _
        have hm := hseq_mono.monotone hle
        linarith
      · have hr6 : r.val < 6 := by omega
        have ha_eq : P'.vec a = P'.vec (seq10Equiv xa) := by simp [xa]
        have hl_eq : hullVerts P' r = P'.vec (seq10Equiv (pos ⟨r.val, by omega⟩)) := by
          unfold hullVerts; rw [← hpos_eq ⟨r.val, by omega⟩]; rfl
        have hr_eq : hullVerts P' ⟨r.val + 1, hr⟩ = P'.vec (seq10Equiv (pos ⟨r.val + 1, by omega⟩)) := by
          unfold hullVerts; rw [← hpos_eq ⟨r.val + 1, by omega⟩]; rfl
        rw [ha_eq, hl_eq] at hlt1
        rw [ha_eq, hr_eq] at hlt2
        have hxa_gt : (pos ⟨r.val, by omega⟩).val < xa.val := hseq_mono.lt_iff_lt.mp hlt1
        have hxa_lt : xa.val < (pos ⟨r.val + 1, by omega⟩).val := hseq_mono.lt_iff_lt.mp hlt2
        have hb_cond : (((pos ⟨r.val, by omega⟩).val < xa.val && xa.val < (pos ⟨r.val + 1, by omega⟩).val)) = true := by
          simp [hxa_gt, hxa_lt]
        have hmem_pair_b2 :
            normPair5 (khat.getD xa.val 0) (khat.getD (pos ⟨r.val, by omega⟩).val 0) ∈ b2 ∧
            normPair5 (khat.getD xa.val 0) (khat.getD (pos ⟨r.val + 1, by omega⟩).val 0) ∈ b2 := by
          have hmem_prod : (((pos ⟨r.val, by omega⟩).val, (pos ⟨r.val + 1, by omega⟩).val), xa.val) ∈ adj.product remList :=
            List.mem_product.mpr ⟨hadj_pair ⟨r.val, hr6⟩, hxa_rem⟩
          constructor
          · refine List.mem_flatMap.mpr ⟨_, hmem_prod, ?_⟩; dsimp only; rw [if_pos hb_cond]; simp
          · refine List.mem_flatMap.mpr ⟨_, hmem_prod, ?_⟩; dsimp only; rw [if_pos hb_cond]; simp
        have hcol_open : ∀ r' : Fin ((topTiePts P').card + 1), 1 < dot2 (hullVerts P' r') z →
            hullColors P' r' ∈ S ∧ hullColors P' r' ≠ vecColor a := by
          intro r' hdot
          refine ⟨?_, fun he => by linarith [ha_lt r' he]⟩
          by_contra hnot
          have hm := hreal (hullColors P' r')
          simp only [decide_eq_false hnot, Bool.not_false, ↓reduceIte, DualConfig.MemOpen] at hm
          unfold hullVerts at hdot; unfold hullColors at hm
          have hd_le : dot2 (P'.vec (hullIdx P' r')) z < 1 := by
            unfold DualConfig.vec
            split_ifs
            · exact hm.1
            · exact hm.2
          linarith
        rcases hact z hz (le_of_lt ha_gt) with h1 | h2
        · obtain ⟨hcol_mem, hcol_ne⟩ := hcol_open r h1
          have hset_eq : ({vecColor a, hullColors P' r} : Finset (Fin 5)) = S :=
            Finset.eq_of_subset_of_card_le
              (Finset.insert_subset_iff.mpr ⟨ha_mem, Finset.singleton_subset_iff.mpr hcol_mem⟩)
              (by rw [hS_card, Finset.card_pair hcol_ne.symm])
          refine List.mem_append_right a2 ?_
          convert hmem_pair_b2.1 using 1
          rw [hkhat_eq, hkhat_eq]
          have hxa_col : vecColor (seq10Equiv xa) = vecColor a := by simp [xa]
          have hr_col : vecColor (seq10Equiv (pos ⟨r.val, by omega⟩)) = hullColors P' r := by
            unfold hullColors; rw [← hpos_eq ⟨r.val, by omega⟩]; rfl
          rw [hxa_col, hr_col]
          exact (hnorm_pair _ _ hset_eq).symm
        · obtain ⟨hcol_mem, hcol_ne⟩ := hcol_open ⟨r.val + 1, hr⟩ h2
          have hset_eq : ({vecColor a, hullColors P' ⟨r.val + 1, hr⟩} : Finset (Fin 5)) = S :=
            Finset.eq_of_subset_of_card_le
              (Finset.insert_subset_iff.mpr ⟨ha_mem, Finset.singleton_subset_iff.mpr hcol_mem⟩)
              (by rw [hS_card, Finset.card_pair hcol_ne.symm])
          refine List.mem_append_right a2 ?_
          convert hmem_pair_b2.2 using 1
          rw [hkhat_eq, hkhat_eq]
          have hxa_col : vecColor (seq10Equiv xa) = vecColor a := by simp [xa]
          have hr_col : vecColor (seq10Equiv (pos ⟨r.val + 1, by omega⟩)) = hullColors P' ⟨r.val + 1, hr⟩ := by
            unfold hullColors; rw [← hpos_eq ⟨r.val + 1, by omega⟩]; rfl
          rw [hxa_col, hr_col]
          exact (hnorm_pair _ _ hset_eq).symm
  -- Connect with `v_n7_T3bar0_diagonals_lt_5`
  have hcheck := v_n7_T3bar0_diagonals_lt_5
  unfold checkN7T3bar0Diagonals at hcheck
  have hi1_mem : i₁ ∈ ([1, 2, 3, 4, 5, 6, 7, 8] : List ℕ) := by simp; omega
  have hi2_mem : i₂ ∈ ([1, 2, 3, 4, 5, 6, 7, 8] : List ℕ) := by simp; omega
  have hi3_mem : i₃ ∈ ([1, 2, 3, 4, 5, 6, 7, 8] : List ℕ) := by simp; omega
  rw [List.all_eq_true] at hcheck
  have h1 := hcheck i₁ hi1_mem
  rw [List.all_eq_true] at h1
  have h2 := h1 i₂ hi2_mem
  rw [List.all_eq_true] at h2
  have h3 := h2 i₃ hi3_mem
  have hadj_true : (adj.all fun (a, b) => khat.getD a 0 != khat.getD b 0) = true := by
    rw [List.all_eq_true]
    intro ⟨a, b⟩ hab
    obtain ⟨m, hm, hm_eq⟩ := List.mem_iff_getElem.mp hab
    have hm6 : m < 6 := by omega
    have hget_m := hget_adj m hm
    rw [hm_eq] at hget_m
    have ha_eq : a = (pos ⟨m, by omega⟩).val := congrArg Prod.fst hget_m
    have hb_eq : b = (pos ⟨m + 1, by omega⟩).val := congrArg Prod.snd hget_m
    dsimp only
    rw [ha_eq, hb_eq, hkhat_eq, hkhat_eq]
    have hcol_a : vecColor (seq10Equiv (pos ⟨m, by omega⟩)) = hullColors P' ⟨m, by omega⟩ := by
      unfold hullColors; rw [← hpos_eq ⟨m, by omega⟩]; rfl
    have hcol_b : vecColor (seq10Equiv (pos ⟨m + 1, by omega⟩)) = hullColors P' ⟨m + 1, by omega⟩ := by
      unfold hullColors; rw [← hpos_eq ⟨m + 1, by omega⟩]; rfl
    rw [hcol_a, hcol_b]
    have hne_ab := h_adj_ne ⟨m, hm6⟩
    simp only [bne_iff_ne, ne_eq]
    exact fun h => hne_ab (Fin.ext h)
  have hnot_adj : (!(adj.all fun (a, b) => khat.getD a 0 != khat.getD b 0)) = false := by
    rw [hadj_true]; rfl
  dsimp only at h3
  rw [show (!(decide (i₁ < i₂) && decide (i₂ < i₃))) = false by simp [hi12, hi23], if_neg Bool.false_ne_true] at h3
  change (if !(adj.all fun (a, b) => khat.getD a 0 != khat.getD b 0) then true else !(diags.all fun d => (a2 ++ b2).contains d)) = true at h3
  rw [hnot_adj, if_neg Bool.false_ne_true, Bool.not_eq_true'] at h3
  have hall_true : (diags.all fun d => (a2 ++ b2).contains d) = true := List.all_eq_true.mpr hdiag_covered
  rw [hall_true] at h3
  exact Bool.false_ne_true h3.symm

private lemma elim_n7_case4 (P' : DualConfig) (hgp' : IsGenPos P')
    (htop' : ∀ {t : ℝ}, 0 ≤ t → t ≤ 3 → 0 < topEnv P' t)
    (h_shat' : ∀ m : Fin 5 → Bool, ∃ z : ℝ × ℝ, InOmega z ∧ RealizesDualMask P' m z)
    (hleft : StrictMono (leftKey P')) (hn7 : hullBlockCount P' = 7)
    (h_all_edges : ∀ i j : Fin 5, i < j → (i, j) ∈ threeCrossGraph P')
    (hσ_id : ∀ r : Fin 5, rightPerm P' r = r) : False := by
  have hp1_lt_p2 : ∀ i : Fin 5, rayParam (P'.p1 i) < rayParam (P'.p2 i) := by
    intro i
    have hap_tie_i : dot2 (P'.p1 i) (gamma (apexRay P' i)) = dot2 (P'.p2 i) (gamma (apexRay P' i)) := by
      obtain ⟨hq3, hd1, hd2, _⟩ := P'.apex_spec i
      have hom : InOmega (P'.apex i) := Or.inl hq3.1
      have hnorm := inOmega_norm_pos hom
      have hrec := gamma_rayParam_smul hom
      rw [← hrec, dot2_smul_right] at hd1 hd2
      have : (|(P'.apex i).1| + |(P'.apex i).2|) * dot2 (P'.p1 i) (gamma (apexRay P' i)) =
          (|(P'.apex i).1| + |(P'.apex i).2|) * dot2 (P'.p2 i) (gamma (apexRay P' i)) := by
        unfold apexRay; linarith
      exact mul_left_cancel₀ (ne_of_gt hnorm) this
    have hsw := (supportF_branch_switch P' hgp').2 i
    have hpos1 : 0 < dot2 (P'.p1 i) (gamma (apexRay P' i)) := by
      have hp := hsw.2.2.1; unfold supportF at hp; rw [hap_tie_i, max_self] at hp; linarith
    have hpos2 : 0 < dot2 (P'.p2 i) (gamma (apexRay P' i)) := by linarith
    have hp1_om : InOmega (P'.p1 i) := by
      have h := P'.vec_inOmega ⟨2 * i.val, by omega⟩; rwa [P'.vec_even i] at h
    have hp2_om : InOmega (P'.p2 i) := by
      have h := P'.vec_inOmega ⟨2 * i.val + 1, by omega⟩; rwa [P'.vec_odd i] at h
    exact rayParam_lt_of_det2_pos_and_pos_dot hp1_om hp2_om
      (by linarith [hsw.1]) (by linarith [hsw.2.1]) (P'.h_det i) hpos1 hpos2
  have hseq_mono : StrictMono (fun k : Fin 10 => rayParam (P'.vec (seq10Equiv k))) := by
    intro k₁ k₂ hk
    have hp1_mono : ∀ i j : Fin 5, i < j → rayParam (P'.p1 i) < rayParam (P'.p1 j) := fun i j hij =>
      (three_crossing_structure P' hgp' h_shat' hleft (h_all_edges i j hij)).2.2.2.2.2.1
    have hp2_mono : ∀ i j : Fin 5, i < j → rayParam (P'.p2 i) < rayParam (P'.p2 j) := fun i j hij =>
      (three_crossing_structure P' hgp' h_shat' hleft (h_all_edges i j hij)).2.2.2.2.2.2.2
    have hp1_lt_p2_all : ∀ j i : Fin 5, rayParam (P'.p1 j) < rayParam (P'.p2 i) := by
      intro j i
      rcases lt_trichotomy i j with hij | rfl | hji
      · exact (three_crossing_structure P' hgp' h_shat' hleft (h_all_edges i j hij)).2.2.2.2.2.2.1
      · exact hp1_lt_p2 i
      · exact lt_trans (hp1_mono j i hji) (hp1_lt_p2 i)
    dsimp [seq10Equiv]
    split_ifs with h1 h2 h2
    · rw [P'.vec_even ⟨k₁.val, by omega⟩, P'.vec_even ⟨k₂.val, by omega⟩]
      exact hp1_mono ⟨k₁.val, by omega⟩ ⟨k₂.val, by omega⟩ hk
    · rw [P'.vec_even ⟨k₁.val, by omega⟩, P'.vec_odd ⟨k₂.val - 5, by omega⟩]
      exact hp1_lt_p2_all ⟨k₁.val, by omega⟩ ⟨k₂.val - 5, by omega⟩
    · have hk1 : k₁.val < 5 := by omega
      have hk2 : k₂.val < 5 := by omega
      have hlt : k₁.val < k₂.val := hk
      omega
    · rw [P'.vec_odd ⟨k₁.val - 5, by omega⟩, P'.vec_odd ⟨k₂.val - 5, by omega⟩]
      exact hp2_mono ⟨k₁.val - 5, by omega⟩ ⟨k₂.val - 5, by omega⟩
        (by show k₁.val - 5 < k₂.val - 5; have : k₁.val < k₂.val := hk; omega)
  have hspec := hullVerts_spec P' hgp' htop'
  obtain ⟨h, hh_def⟩ : ∃ h : ℕ, h = (topTiePts P').card + 1 := ⟨_, rfl⟩
  have hh_ge7 : 7 ≤ h := by
    have := compressAdj_length_le (List.ofFn (hullColors P'))
    change hullBlockCount P' ≤ (List.ofFn (hullColors P')).length at this
    rw [List.length_ofFn, ← hh_def, hn7] at this
    exact this
  have hh_le10 : h ≤ 10 := by rw [hh_def]; exact hspec.2.1
  obtain ⟨pos, hpos_spec⟩ : ∃ pos : Fin h → Fin 10,
      ∀ r : Fin h, pos r = seq10Equiv.symm (hullIdx P' (Fin.cast (by rw [hh_def]) r)) :=
    ⟨_, fun _ => rfl⟩
  have hpos_mono : StrictMono pos := by
    intro r₁ r₂ hr
    have hray := hspec.2.2.2.1 (show Fin.cast (by rw [hh_def]) r₁ < Fin.cast (by rw [hh_def]) r₂ from hr)
    unfold hullVerts at hray
    have hray' : rayParam (P'.vec (seq10Equiv (pos r₁))) < rayParam (P'.vec (seq10Equiv (pos r₂))) := by
      rw [hpos_spec r₁, hpos_spec r₂]; simpa only [Equiv.apply_symm_apply] using hray
    exact hseq_mono.lt_iff_lt.mp hray'
  have h_adj_ne : ∀ r : Fin (h - 1),
      hullColors P' ⟨r.val, by rw [← hh_def]; omega⟩ ≠
      hullColors P' ⟨r.val + 1, by rw [← hh_def]; omega⟩ := by
    intro r heq_col
    let r₀ : Fin h := ⟨r.val, by omega⟩
    let r₁ : Fin h := ⟨r.val + 1, by omega⟩
    have hr01 : r₀ < r₁ := by show r.val < r.val + 1; omega
    have hlt_pos := hpos_mono hr01
    have hcol0 : (vecColor (seq10Equiv (pos r₀))).val = (pos r₀).val % 5 := seq10Equiv_color _
    have hcol1 : (vecColor (seq10Equiv (pos r₁))).val = (pos r₁).val % 5 := seq10Equiv_color _
    have hc_eq : (hullColors P' ⟨r.val, by rw [← hh_def]; omega⟩).val =
        (hullColors P' ⟨r.val + 1, by rw [← hh_def]; omega⟩).val := congrArg Fin.val heq_col
    have hm_eq : (pos r₀).val % 5 = (pos r₁).val % 5 := by
      rw [← hcol0, ← hcol1, hpos_spec r₀, hpos_spec r₁]
      unfold hullColors at hc_eq
      simpa [r₀, r₁, Equiv.apply_symm_apply] using hc_eq
    have hgap5 : (pos r₀).val + 5 ≤ (pos r₁).val := by
      have hlt' : (pos r₀).val < (pos r₁).val := hlt_pos
      omega
    let gaps : Finset (Fin 10) :=
      (Finset.univ : Finset (Fin 4)).image fun d => ⟨(pos r₀).val + 1 + d.val, by omega⟩
    have hgaps_card : gaps.card = 4 := by
      rw [Finset.card_image_of_injective _ (fun a b h => Fin.ext (by
        have := congrArg Fin.val h; dsimp at this; omega)), Finset.card_fin]
    have hdisj : Disjoint (Finset.univ.image pos) gaps := by
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      simp only [Finset.mem_image, Finset.mem_univ, true_and] at hx1
      simp only [gaps, Finset.mem_image, Finset.mem_univ, true_and] at hx2
      obtain ⟨s, rfl⟩ := hx1
      obtain ⟨d, hd⟩ := hx2
      have hbounds : (pos r₀).val < (pos s).val ∧ (pos s).val < (pos r₁).val := by
        have hv : (pos s).val = (pos r₀).val + 1 + d.val := congrArg Fin.val hd.symm
        omega
      have hs1 : r₀ < s := hpos_mono.lt_iff_lt.mp hbounds.1
      have hs2 : s < r₁ := hpos_mono.lt_iff_lt.mp hbounds.2
      have hs1' : r₀.val < s.val := hs1
      have hs2' : s.val < r₁.val := hs2
      dsimp [r₀, r₁] at hs1' hs2'; omega
    have hsum := Finset.card_union_of_disjoint hdisj
    have hle10 : (Finset.univ.image pos ∪ gaps).card ≤ 10 :=
      (Finset.card_le_univ _).trans (by simp)
    rw [Finset.card_image_of_injective _ hpos_mono.injective, Finset.card_fin, hgaps_card] at hsum
    omega
  have hh_eq7 : h = 7 := by
    have hcomp : compressAdj (List.ofFn (hullColors P')) = List.ofFn (hullColors P') := by
      refine compressAdj_eq_self_of_adj_ne _ fun i hi => ?_
      rw [List.length_ofFn, ← hh_def] at hi
      simp only [List.getElem_ofFn]
      exact h_adj_ne ⟨i, by omega⟩
    have hlen_eq : hullBlockCount P' = h := by
      unfold hullBlockCount compressedColors
      rw [hcomp, List.length_ofFn, hh_def]
    omega
  subst hh_eq7
  have hcard7 : (topTiePts P').card + 1 = 7 := hh_def.symm
  have hpos_eq : ∀ r : Fin 7, hullIdx P' (Fin.cast hcard7.symm r) = seq10Equiv (pos r) := by
    intro r; rw [hpos_spec r]; simp only [Equiv.apply_symm_apply]
  have hcp := crossing_parity_inv P' hgp' htop' h_shat' hleft
  have hpos0 : pos ⟨0, by omega⟩ = ⟨0, by omega⟩ := by
    have hc0 : (vecColor (seq10Equiv (pos ⟨0, by omega⟩))).val = 0 := by
      rw [← hpos_eq ⟨0, by omega⟩]
      simpa [hullColors] using congrArg Fin.val hcp.2.1
    rw [seq10Equiv_color] at hc0
    have hle6 : (pos ⟨0, by omega⟩).val + 6 ≤ (pos ⟨6, by omega⟩).val := by
      have h_ind : ∀ m : ℕ, (hm : m < 7) → (pos ⟨0, by omega⟩).val + m ≤ (pos ⟨m, hm⟩).val := by
        intro m hm; induction m with
        | zero => exact le_rfl
        | succ k ih =>
          have hlt := hpos_mono (show (⟨k, by omega⟩ : Fin 7) < ⟨k + 1, hm⟩ by show k < k + 1; omega)
          have := ih (by omega)
          have hlt' : (pos ⟨k, by omega⟩).val < (pos ⟨k + 1, hm⟩).val := hlt
          omega
      exact h_ind 6 (by omega)
    have hlt10 : (pos ⟨6, by omega⟩).val < 10 := (pos ⟨6, by omega⟩).isLt
    exact Fin.ext (by simp only [Fin.val_mk]; omega)
  have hpos6 : pos ⟨6, by omega⟩ = ⟨9, by omega⟩ := by
    have hc6 : (vecColor (seq10Equiv (pos ⟨6, by omega⟩))).val = 4 := by
      rw [← hpos_eq ⟨6, by omega⟩]
      have hfin : (Fin.cast hcard7.symm ⟨6, by omega⟩ : Fin ((topTiePts P').card + 1)) =
          ⟨(topTiePts P').card, by omega⟩ := by
        ext; simp only [Fin.val_cast]; omega
      rw [hfin]
      have hcol : hullColors P' ⟨(topTiePts P').card, by omega⟩ = ⟨4, by omega⟩ := by
        rw [hcp.2.2, hσ_id ⟨4, by omega⟩]
      simpa [hullColors] using congrArg Fin.val hcol
    rw [seq10Equiv_color] at hc6
    have hge6 : 6 ≤ (pos ⟨6, by omega⟩).val := by
      have h_ind : ∀ m : ℕ, (hm : m < 7) → m ≤ (pos ⟨m, hm⟩).val := by
        intro m hm; induction m with
        | zero => exact Nat.zero_le _
        | succ k ih =>
          have hlt := hpos_mono (show (⟨k, by omega⟩ : Fin 7) < ⟨k + 1, hm⟩ by show k < k + 1; omega)
          have := ih (by omega)
          have hlt' : (pos ⟨k, by omega⟩).val < (pos ⟨k + 1, hm⟩).val := hlt
          omega
      exact h_ind 6 (by omega)
    have hlt10 : (pos ⟨6, by omega⟩).val < 10 := (pos ⟨6, by omega⟩).isLt
    exact Fin.ext (by simp only [Fin.val_mk]; omega)
  exact elim_n7_case4_hull_contra P' hgp' htop' h_shat' hcard7 pos hpos_eq hpos_mono hseq_mono
    (fun r => h_adj_ne ⟨r.val, by omega⟩) hpos0 hpos6

/-- Final bounded-regime contradiction eliminating `n_Ω = 7` across `T̄_3^+ ∈ {2, 1, 0}` and
combining with `5 ≤ n_Ω ≤ 7`, `n_Ω ≠ 5`, `n_Ω ≠ 6`. -/
theorem elim_n7_all (P : DualConfig) (hgp : IsGenPos P)
    (htop : ∀ {t : ℝ}, 0 ≤ t → t ≤ 3 → 0 < topEnv P t)
    (h_shat : ∀ m : Fin 5 → Bool, ∃ z : ℝ × ℝ, InOmega z ∧ RealizesDualMask P m z) :
    False := by
  have h5_10 := hull_five_colors P hgp htop h_shat
  have hne5 := elim_n5 P hgp htop h_shat
  have hne6 := elim_n6_all P hgp htop h_shat
  have hle7 := elim_n8_to_10 P hgp htop h_shat
  have hn7_orig : hullBlockCount P = 7 := by omega
  obtain ⟨τ, hleft⟩ := exists_left_sort_perm P hgp
  let P' := P.relabel τ
  have hgp' : IsGenPos P' := isGenPos_relabel P τ hgp
  have htop' : ∀ {t : ℝ}, 0 ≤ t → t ≤ 3 → 0 < topEnv P' t := fun ht0 ht3 => by
    rw [topEnv_relabel]; exact htop ht0 ht3
  have h_shat' : ∀ m : Fin 5 → Bool, ∃ z : ℝ × ℝ, InOmega z ∧ RealizesDualMask P' m z :=
    shat_relabel P τ h_shat
  have hn7 : hullBlockCount P' = 7 := by
    dsimp [P']; rw [hullBlockCount_relabel P τ hgp, hn7_orig]
  have hlaw := conservation_law P' hgp' htop' h_shat'
  have hd1 := slice_surj_masks P' hgp' htop' h_shat' (q := 1) (by omega) (by omega)
  have hd2 := slice_surj_masks P' hgp' htop' h_shat' (q := 2) (by omega) (by omega)
  have hd3 := slice_surj_masks P' hgp' htop' h_shat' (q := 3) (by omega) (by omega)
  have hbounds := card_posPairTies_bounds P' hgp' h_shat'
  let σ := rightPerm P'
  have hinv_eq : crossCountOfMult P' 2 = permInversions σ :=
    (crossing_parity_inv P' hgp' htop' h_shat' hleft).1
  rw [hn7] at hlaw
  -- `(T1 + T2) + T1 + Δ₁ + Δ₂ + Δ₃ = 2` gives `T1 ≤ 1` and `T2 ≤ 2`
  rcases (show crossCountOfMult P' 1 = 0 ∨ crossCountOfMult P' 1 = 1 by omega) with hT1_0 | hT1_1
  · have hno1 : ∀ i j : Fin 5, i < j → (posPairTies P' i j).card ≠ 1 := by
      intro i j hij h1
      have hpos : 0 < crossCountOfMult P' 1 := Finset.card_pos.mpr ⟨(i, j), by simp [hij, h1]⟩
      omega
    have h_edge_iff : ∀ i j : Fin 5, i < j →
        ((i, j) ∈ threeCrossGraph P' ↔ σ.symm i < σ.symm j) := by
      intro i j hij
      have h2 := card_posPairTies_eq_two_iff_rightKey_gt P' hgp' h_shat' hleft hij
      have hσ_mono := rightPerm_strictMono P' hgp'
      have hR_iff : rightKey P' j < rightKey P' i ↔ σ.symm j < σ.symm i := by
        constructor
        · intro hlt
          by_contra hle
          have hord : σ.symm i ≤ σ.symm j := not_lt.mp hle
          have hm := hσ_mono.monotone hord
          simp only [σ, Equiv.apply_symm_apply] at hm
          linarith
        · intro hlt
          have hm := hσ_mono hlt
          simp only [σ, Equiv.apply_symm_apply] at hm
          exact hm
      have hne1 := hno1 i j hij
      have hb := hbounds.1 i j hij
      simp only [threeCrossGraph, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro ⟨_, h3⟩
        by_contra hle
        have hlt : σ.symm j < σ.symm i :=
          lt_of_le_of_ne (not_lt.mp hle) (σ.symm.injective.ne (ne_of_gt hij))
        have hc2 := h2.mpr (hR_iff.mpr hlt)
        omega
      · intro hlt
        refine ⟨hij, ?_⟩
        have hc_ne2 : (posPairTies P' i j).card ≠ 2 := fun h => by
          have := hR_iff.mp (h2.mp h)
          exact lt_asymm hlt this
        omega
    rcases (show crossCountOfMult P' 2 = 2 ∨ crossCountOfMult P' 2 = 1 ∨ crossCountOfMult P' 2 = 0 by omega)
        with hT2_2 | hT2_1 | hT2_0
    · -- Case 1: `(T̄_3, T_1) = (2, 0)`
      have hinv2 : permInversions σ = 2 := by rw [← hinv_eq, hT2_2]
      rcases inv_two_left_or_right σ hinv2 with hL | hR
      · have hcert := left_certificate P' hgp' htop' h_shat' hleft
          ((h_edge_iff 0 4 (by decide)).mpr (hL 0 (by decide)))
          ((h_edge_iff 1 4 (by decide)).mpr (hL 1 (by decide)))
          ((h_edge_iff 2 4 (by decide)).mpr (hL 2 (by decide)))
        omega
      · have h_edge_min : ∀ k : Fin 5, (1 : Fin 5) < k →
            (min (σ 0) (σ k), max (σ 0) (σ k)) ∈ threeCrossGraph P' := by
          intro k hk
          have hlt := hR k hk
          rw [min_eq_left hlt.le, max_eq_right hlt.le]
          refine (h_edge_iff (σ 0) (σ k) hlt).mpr ?_
          simp only [σ, Equiv.symm_apply_apply]
          exact lt_trans (by decide) hk
        have hcert := right_certificate P' hgp' htop' h_shat' hleft
          (h_edge_min 2 (by decide)) (h_edge_min 3 (by decide)) (h_edge_min 4 (by decide))
        omega
    · -- Case 2: `(T̄_3, T_1) = (1, 0)`
      have hinv1 : permInversions σ = 1 := by rw [← hinv_eq, hT2_1]
      obtain ⟨hL, hR, h0_lt2, h0_ne4, h1_ne4⟩ := inv_one_bounds σ hinv1
      obtain ⟨M_L, hML_cases, hwL⟩ := left_cert_witness P' hgp' h_shat' hleft
        ((h_edge_iff 0 4 (by decide)).mpr (hL 0 (by decide)))
        ((h_edge_iff 1 4 (by decide)).mpr (hL 1 (by decide)))
        ((h_edge_iff 2 4 (by decide)).mpr (hL 2 (by decide)))
      have h_edge_min : ∀ k : Fin 5, (1 : Fin 5) < k →
            (min (σ 0) (σ k), max (σ 0) (σ k)) ∈ threeCrossGraph P' := by
        intro k hk
        have hlt := hR k hk
        rw [min_eq_left hlt.le, max_eq_right hlt.le]
        refine (h_edge_iff (σ 0) (σ k) hlt).mpr ?_
        simp only [σ, Equiv.symm_apply_apply]
        exact lt_trans (by decide) hk
      obtain ⟨M_R, hMR_cases, hwR⟩ := right_cert_witness P' hgp' h_shat'
        (h_edge_min 2 (by decide)) (h_edge_min 3 (by decide)) (h_edge_min 4 (by decide))
      have hML_ne_MR : M_L ≠ M_R := by
        rcases hML_cases with rfl | rfl <;> rcases hMR_cases with rfl | rfl
        · intro h
          have h4_mem : (4 : Fin 5) ∈ ({σ 0} : Finset (Fin 5)) := h ▸ Finset.mem_singleton_self 4
          exact h0_ne4 (Finset.mem_singleton.mp h4_mem).symm
        · intro h
          have : ({4} : Finset (Fin 5)).card = ({σ 0, σ 1} : Finset (Fin 5)).card := congrArg Finset.card h
          rw [Finset.card_singleton, Finset.card_pair (σ.injective.ne (by decide))] at this
          omega
        · intro h
          have : ({3, 4} : Finset (Fin 5)).card = ({σ 0} : Finset (Fin 5)).card := congrArg Finset.card h
          rw [Finset.card_pair (by decide), Finset.card_singleton] at this
          omega
        · intro h
          have h4_mem : (4 : Fin 5) ∈ ({σ 0, σ 1} : Finset (Fin 5)) :=
            h ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self 4)
          rcases Finset.mem_insert.mp h4_mem with h4 | h4
          · exact h0_ne4 h4.symm
          · exact h1_ne4 (Finset.mem_singleton.mp h4).symm
      rcases hML_cases with rfl | rfl <;> rcases hMR_cases with rfl | rfl
      · have hex2 := sliceExcess_ge_card_of_cutSplitWitnesses P' hgp' htop' h_shat' (q := 1)
          (by omega) (by omega) {({4} : Finset (Fin 5)), {σ 0}}
          (fun M hM => by
            rcases Finset.mem_insert.mp hM with rfl | hM
            · simp
            · rw [Finset.mem_singleton.mp hM, Finset.card_singleton])
          (fun M hM => by
            rcases Finset.mem_insert.mp hM with rfl | hM
            · exact hwL
            · rw [Finset.mem_singleton.mp hM]; exact hwR)
        rw [Finset.card_pair] at hex2
        · omega
        · simpa using hML_ne_MR
      · obtain ⟨a₁, a₂, a₃, ha0, ha12, ha23, ha3, hac1, hac2, hac3⟩ := hwL
        obtain ⟨b₁, b₂, b₃, hb0, hb12, hb23, hb3, hbc1, hbc2, hbc3⟩ := hwR
        have hM1 := duplicate_slice_of_cutPotential P' hgp' htop' h_shat' {4}
          (by simp) (by simp) ha0 ha12 ha23 ha3 hac1 hac2 hac3
        have hM2 := duplicate_slice_of_cutPotential P' hgp' htop' h_shat' {σ 0, σ 1}
          (by rw [Finset.card_pair (σ.injective.ne (Fin.ne_of_val_ne (by decide)))]; omega)
          (by rw [Finset.card_pair (σ.injective.ne (Fin.ne_of_val_ne (by decide)))]; omega)
          hb0 hb12 hb23 hb3 hbc1 hbc2 hbc3
        rw [Finset.card_singleton] at hM1
        rw [Finset.card_pair (σ.injective.ne (Fin.ne_of_val_ne (by decide)))] at hM2
        omega
      · obtain ⟨a₁, a₂, a₃, ha0, ha12, ha23, ha3, hac1, hac2, hac3⟩ := hwL
        obtain ⟨b₁, b₂, b₃, hb0, hb12, hb23, hb3, hbc1, hbc2, hbc3⟩ := hwR
        have hM2 := duplicate_slice_of_cutPotential P' hgp' htop' h_shat' {3, 4}
          (by rw [Finset.card_pair (Fin.ne_of_val_ne (by decide))]; omega)
          (by rw [Finset.card_pair (Fin.ne_of_val_ne (by decide))]; omega)
          ha0 ha12 ha23 ha3 hac1 hac2 hac3
        have hM1 := duplicate_slice_of_cutPotential P' hgp' htop' h_shat' {σ 0}
          (by simp) (by simp) hb0 hb12 hb23 hb3 hbc1 hbc2 hbc3
        rw [Finset.card_pair (Fin.ne_of_val_ne (by decide))] at hM2
        rw [Finset.card_singleton] at hM1
        omega
      · have hex2 := sliceExcess_ge_card_of_cutSplitWitnesses P' hgp' htop' h_shat' (q := 2)
          (by omega) (by omega) {({3, 4} : Finset (Fin 5)), {σ 0, σ 1}}
          (fun M hM => by
            rcases Finset.mem_insert.mp hM with rfl | hM
            · exact Finset.card_pair (Fin.ne_of_val_ne (by decide))
            · rw [Finset.mem_singleton.mp hM]
              exact Finset.card_pair (σ.injective.ne (Fin.ne_of_val_ne (by decide))))
          (fun M hM => by
            rcases Finset.mem_insert.mp hM with rfl | hM
            · exact hwL
            · rw [Finset.mem_singleton.mp hM]; exact hwR)
        rw [Finset.card_pair] at hex2
        · omega
        · simpa using hML_ne_MR
    · -- Case 4: `(T̄_3, T_1) = (0, 0)` (`G_3 = K_5`, `σ = id`)
      have hT3_10 : (threeCrossGraph P').card = 10 := by
        have hb := hbounds.2.1
        change crossCountOfMult P' 1 + crossCountOfMult P' 2 + (threeCrossGraph P').card = 10 at hb
        omega
      have h_all_edges : ∀ i j : Fin 5, i < j → (i, j) ∈ threeCrossGraph P' := by
        intro i j hij
        let pairs : Finset (Fin 5 × Fin 5) := (Finset.univ : Finset (Fin 5 × Fin 5)).filter (fun p => p.1 < p.2)
        have hpairs_card : pairs.card = 10 := by decide
        have hsub : threeCrossGraph P' ⊆ pairs := fun p hp => by
          simp only [threeCrossGraph, Finset.mem_filter, Finset.mem_univ, true_and] at hp
          simp only [pairs, Finset.mem_filter, Finset.mem_univ, true_and]; exact hp.1
        have heq : threeCrossGraph P' = pairs := Finset.eq_of_subset_of_card_le hsub (by rw [hpairs_card, hT3_10])
        rw [heq]; simp [pairs, hij]
      have hinv0 : permInversions σ = 0 := by rw [← hinv_eq, hT2_0]
      exact elim_n7_case4 P' hgp' htop' h_shat' hleft hn7 h_all_edges (perm_eq_id_of_inv_zero σ hinv0)
  · -- Case 3: `(T̄_3, T_1) = (1, 1)` (`T_2 = 0`, `σ = id`, unique non-edge `(0, 4)`)
    have hT1_zero_or : crossCountOfMult P' 2 = 0 := by omega
    have hinv0 : permInversions σ = 0 := by rw [← hinv_eq, hT1_zero_or]
    have hσ_id : ∀ r : Fin 5, σ r = r := perm_eq_id_of_inv_zero σ hinv0
    have hT3_9 : (threeCrossGraph P').card = 9 := by
      have hb := hbounds.2.1
      change crossCountOfMult P' 1 + crossCountOfMult P' 2 + (threeCrossGraph P').card = 10 at hb
      omega
    let pairs : Finset (Fin 5 × Fin 5) := (Finset.univ : Finset (Fin 5 × Fin 5)).filter (fun p => p.1 < p.2)
    have hpairs_card : pairs.card = 10 := by decide
    have hsub : threeCrossGraph P' ⊆ pairs := fun p hp => by
      simp only [threeCrossGraph, Finset.mem_filter, Finset.mem_univ, true_and] at hp
      simp only [pairs, Finset.mem_filter, Finset.mem_univ, true_and]; exact hp.1
    have hdiff_card : (pairs \ threeCrossGraph P').card = 1 := by
      rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hsub, hpairs_card, hT3_9]
    obtain ⟨e₀, he₀_eq⟩ := Finset.card_eq_one.mp hdiff_card
    have he₀_not_mem : ∀ p ∈ pairs, p ≠ e₀ → p ∈ threeCrossGraph P' := by
      intro p hp hpne
      by_contra hnot
      have hpm : p ∈ pairs \ threeCrossGraph P' := Finset.mem_sdiff.mpr ⟨hp, hnot⟩
      rw [he₀_eq, Finset.mem_singleton] at hpm
      exact hpne hpm
    have h04_mem_pairs : ((0 : Fin 5), (4 : Fin 5)) ∈ pairs := by decide
    have hL_not_all : ¬ (((0 : Fin 5), (4 : Fin 5)) ∈ threeCrossGraph P' ∧
        ((1 : Fin 5), (4 : Fin 5)) ∈ threeCrossGraph P' ∧
        ((2 : Fin 5), (4 : Fin 5)) ∈ threeCrossGraph P') := by
      intro ⟨h0, h1, h2⟩
      have hcert := left_certificate P' hgp' htop' h_shat' hleft h0 h1 h2
      omega
    have hR_not_all : ¬ (((0 : Fin 5), (2 : Fin 5)) ∈ threeCrossGraph P' ∧
        ((0 : Fin 5), (3 : Fin 5)) ∈ threeCrossGraph P' ∧
        ((0 : Fin 5), (4 : Fin 5)) ∈ threeCrossGraph P') := by
      intro ⟨h2, h3, h4⟩
      have he2' : (min (σ 0) (σ 2), max (σ 0) (σ 2)) ∈ threeCrossGraph P' := by
        rw [hσ_id 0, hσ_id 2]; simpa using h2
      have he3' : (min (σ 0) (σ 3), max (σ 0) (σ 3)) ∈ threeCrossGraph P' := by
        rw [hσ_id 0, hσ_id 3]; simpa using h3
      have he4' : (min (σ 0) (σ 4), max (σ 0) (σ 4)) ∈ threeCrossGraph P' := by
        rw [hσ_id 0, hσ_id 4]; simpa using h4
      have hcert := right_certificate P' hgp' htop' h_shat' hleft he2' he3' he4'
      omega
    have he₀_eq_04 : e₀ = ((0 : Fin 5), (4 : Fin 5)) := by
      by_contra hne04
      have he₀_L : e₀ = ((1 : Fin 5), (4 : Fin 5)) ∨ e₀ = ((2 : Fin 5), (4 : Fin 5)) := by
        by_contra hnot
        push Not at hnot
        exact hL_not_all ⟨he₀_not_mem _ (by decide) (Ne.symm hne04),
          he₀_not_mem _ (by decide) (Ne.symm hnot.1),
          he₀_not_mem _ (by decide) (Ne.symm hnot.2)⟩
      have he₀_R : e₀ = ((0 : Fin 5), (2 : Fin 5)) ∨ e₀ = ((0 : Fin 5), (3 : Fin 5)) := by
        by_contra hnot
        push Not at hnot
        exact hR_not_all ⟨he₀_not_mem _ (by decide) (Ne.symm hnot.1),
          he₀_not_mem _ (by decide) (Ne.symm hnot.2),
          he₀_not_mem _ (by decide) (Ne.symm hne04)⟩
      rcases he₀_L with rfl | rfl <;> rcases he₀_R with h | h <;> exact absurd h (by decide)
    have h_edges : ∀ i j : Fin 5, i < j → (i, j) ≠ (0, 4) → (i, j) ∈ threeCrossGraph P' := by
      intro i j hij hne
      exact he₀_not_mem (i, j) (by simp [pairs, hij]) (he₀_eq_04 ▸ hne)
    have h01 := three_crossing_structure P' hgp' h_shat' hleft (h_edges 0 1 (by decide) (by decide))
    have h02 := three_crossing_structure P' hgp' h_shat' hleft (h_edges 0 2 (by decide) (by decide))
    have h03 := three_crossing_structure P' hgp' h_shat' hleft (h_edges 0 3 (by decide) (by decide))
    have h14 := three_crossing_structure P' hgp' h_shat' hleft (h_edges 1 4 (by decide) (by decide))
    have h24 := three_crossing_structure P' hgp' h_shat' hleft (h_edges 2 4 (by decide) (by decide))
    have h34 := three_crossing_structure P' hgp' h_shat' hleft (h_edges 3 4 (by decide) (by decide))
    let t₀ := apexRay P' 0
    let t₁ := apexRay P' 1
    let t₄ := apexRay P' 4
    have ht01 : t₀ < t₁ := h01.2.1
    have ht14 : t₁ < t₄ := h14.2.1
    have hap0 := (supportF_branch_switch P' hgp').2 0
    have hap4 := (supportF_branch_switch P' hgp').2 4
    obtain ⟨τm, hτm_0, hτm_t1, hτm_min⟩ := case3_left_witness P' hgp' h_shat' hleft h_edges
    -- Construct `τ₊ ∈ (t₁, 3)` via `Q = P'.swap.relabel rev5`
    let rev5 : Equiv.Perm (Fin 5) :=
      { toFun := fun r => ⟨4 - r.val, by omega⟩
        invFun := fun r => ⟨4 - r.val, by omega⟩
        left_inv := fun r => by ext; dsimp; omega
        right_inv := fun r => by ext; dsimp; omega }
    let Q := P'.swap.relabel rev5
    have hgp_sw : IsGenPos P'.swap := (P'.swap_spec).2.1.mpr hgp'
    have hgpQ : IsGenPos Q := isGenPos_relabel P'.swap rev5 hgp_sw
    have h_shat_sw : ∀ m : Fin 5 → Bool, ∃ z : ℝ × ℝ, InOmega z ∧ RealizesDualMask P'.swap m z := by
      intro m; obtain ⟨z, hz, hm⟩ := h_shat' m
      exact ⟨swap2 z, inOmega_swap2 hz, (P'.swap_spec).2.2 m z |>.mpr hm⟩
    have h_shatQ : ∀ m : Fin 5 → Bool, ∃ z : ℝ × ℝ, InOmega z ∧ RealizesDualMask Q m z :=
      shat_relabel P'.swap rev5 h_shat_sw
    have hR_mono : StrictMono (rightKey P') := by
      intro r₁ r₂ hr
      have hsm := rightPerm_strictMono P' hgp' hr
      dsimp only at hsm
      rwa [hσ_id r₁, hσ_id r₂] at hsm
    have hleftQ : StrictMono (leftKey Q) := by
      intro r₁ r₂ hr
      rw [leftKey_relabel, leftKey_relabel, (boundaryKey_swap P' hgp' (rev5 r₁)).1,
        (boundaryKey_swap P' hgp' (rev5 r₂)).1]
      have hrev : rev5 r₂ < rev5 r₁ := by show (4 - r₂.val : ℕ) < 4 - r₁.val; have : r₁.val < r₂.val := hr; omega
      linarith [hR_mono hrev]
    have hQ_edges : ∀ i j : Fin 5, i < j → (i, j) ≠ (0, 4) → (i, j) ∈ threeCrossGraph Q := by
      intro i j hij hne
      rw [threeCrossGraph_relabel P'.swap rev5 hij, threeCrossGraph_swap]
      have hne_rev : rev5 i ≠ rev5 j := rev5.injective.ne (ne_of_lt hij)
      have hpair_ne04 : (min (rev5 i) (rev5 j), max (rev5 i) (rev5 j)) ≠ (0, 4) := by
        intro heq
        have hmin0 : min (rev5 i) (rev5 j) = 0 := congrArg Prod.fst heq
        have hmax4 : max (rev5 i) (rev5 j) = 4 := congrArg Prod.snd heq
        have : (rev5 i = 0 ∧ rev5 j = 4) ∨ (rev5 i = 4 ∧ rev5 j = 0) := by
          rcases le_total (rev5 i) (rev5 j) with h | h
          · rw [min_eq_left h] at hmin0; rw [max_eq_right h] at hmax4; exact Or.inl ⟨hmin0, hmax4⟩
          · rw [min_eq_right h] at hmin0; rw [max_eq_left h] at hmax4; exact Or.inr ⟨hmax4, hmin0⟩
        rcases this with ⟨hi0, hj4⟩ | ⟨hi4, hj0⟩
        · have hi' : i = 4 := by dsimp [rev5] at hi0; exact Fin.ext (by have := congrArg Fin.val hi0; dsimp at this; omega)
          have hj' : j = 0 := by dsimp [rev5] at hj4; exact Fin.ext (by have := congrArg Fin.val hj4; dsimp at this; omega)
          subst hi' hj'; exact absurd hij (by decide)
        · have hi' : i = 0 := by dsimp [rev5] at hi4; exact Fin.ext (by have := congrArg Fin.val hi4; dsimp at this; omega)
          have hj' : j = 4 := by dsimp [rev5] at hj0; exact Fin.ext (by have := congrArg Fin.val hj0; dsimp at this; omega)
          exact hne (Prod.ext hi' hj')
      rcases lt_or_gt_of_ne hne_rev with hlt | hgt
      · rw [min_eq_left hlt.le, max_eq_right hlt.le] at hpair_ne04 ⊢
        exact h_edges _ _ hlt hpair_ne04
      · rw [min_eq_right hgt.le, max_eq_left hgt.le] at hpair_ne04 ⊢
        exact h_edges _ _ hgt hpair_ne04
    obtain ⟨τp', hτp_0, hτp_ap1, hτp_min⟩ := case3_left_witness Q hgpQ h_shatQ hleftQ hQ_edges
    have hQ13 := three_crossing_structure Q hgpQ h_shatQ hleftQ (hQ_edges 1 3 (by decide) (by decide))
    have hap_Q3 : apexRay Q 3 = 3 - t₁ := by
      have hQ_ap : Q.apex 3 = P'.swap.apex 1 := rfl
      unfold apexRay; rw [hQ_ap, (P'.swap_spec).1 1]
      exact rayParam_swap2 (Or.inl (P'.h_apex 1).1)
    let τp : ℝ := 3 - τp'
    have hτp_gt_t1 : t₁ < τp := by dsimp [τp]; linarith [hQ13.2.1]
    have hτp_lt3 : τp < 3 := by dsimp [τp]; linarith
    have hτp_min0 : ∀ v : Fin 5, v ≠ 0 → clippedG P' 0 τp < clippedG P' v τp := by
      intro v hv
      have hv_ne4 : rev5 v ≠ 4 := fun h => hv (rev5.injective (by simpa [rev5] using h))
      have hm := hτp_min (rev5 v) hv_ne4
      have hclip_eq : ∀ k : Fin 5, clippedG Q (rev5 k) τp' = clippedG P' k τp := by
        intro k; unfold clippedG Q
        rw [supportF_relabel, supportF_swap_eq]
        have hkk : rev5 (rev5 k) = k := rev5.apply_symm_apply k
        rw [hkk]
      have hrev0 : (4 : Fin 5) = rev5 0 := rfl
      rw [hrev0, hclip_eq 0, hclip_eq v] at hm
      exact hm
    have h04_ne_t0 : clippedG P' 0 t₀ ≠ clippedG P' 4 t₀ :=
      (clippedG_ne_at_apexRay P' hgp' (by decide : (4 : Fin 5) ≠ 0)).symm
    have h04_ne_t4 : clippedG P' 0 t₄ ≠ clippedG P' 4 t₄ :=
      clippedG_ne_at_apexRay P' hgp' (by decide : (0 : Fin 5) ≠ 4)
    rcases lt_or_gt_of_ne h04_ne_t4 with h04_t4 | h40_t4
    · rcases lt_or_gt_of_ne h04_ne_t0 with h04_t0 | h40_t0
      · -- `M = {0}` splits across `(t₀, t₁, τp)`
        have hc1 : clippedCutPotential P' ({0} : Finset (Fin 5)) t₀ = 0 := by
          unfold clippedCutPotential; rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
          rintro ⟨u, v⟩ hp
          simp only [Finset.mem_product, Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_singleton] at hp
          rw [hp.1]
          have hlt : clippedG P' 0 t₀ < clippedG P' v t₀ := by
            fin_cases v
            · exact absurd rfl hp.2
            · exact h01.2.2.2.1
            · exact h02.2.2.2.1
            · exact h03.2.2.2.1
            · exact h04_t0
          exact not_le.mpr hlt
        have hc2 : 0 < clippedCutPotential P' ({0} : Finset (Fin 5)) t₁ := by
          refine Finset.card_pos.mpr ⟨((0 : Fin 5), (1 : Fin 5)), ?_⟩
          simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_singleton]
          exact ⟨by simp, le_of_lt h01.2.2.2.2.1⟩
        have hc3 : clippedCutPotential P' ({0} : Finset (Fin 5)) τp = 0 := by
          unfold clippedCutPotential; rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
          rintro ⟨u, v⟩ hp
          simp only [Finset.mem_product, Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_singleton] at hp
          rw [hp.1]; exact not_le.mpr (hτp_min0 v hp.2)
        have hM := duplicate_slice_of_cutPotential P' hgp' htop' h_shat' ({0} : Finset (Fin 5))
          (by simp) (by simp) (lt_trans (by norm_num) hap0.1) ht01 hτp_gt_t1 hτp_lt3 hc1 hc2 hc3
        simp only [Finset.card_singleton] at hM; omega
      · -- `M = {0, 4}` splits across `(t₀, t₁, t₄)`
        have hc1 : clippedCutPotential P' ({0, 4} : Finset (Fin 5)) t₀ = 0 := by
          unfold clippedCutPotential; rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
          rintro ⟨u, v⟩ hp
          simp only [Finset.mem_product, Finset.mem_sdiff, Finset.mem_univ, true_and,
            Finset.mem_insert, Finset.mem_singleton] at hp
          have hu_le : clippedG P' u t₀ ≤ clippedG P' 0 t₀ := by
            rcases hp.1 with rfl | rfl <;> [exact le_rfl; exact le_of_lt h40_t0]
          have hv_gt : clippedG P' 0 t₀ < clippedG P' v t₀ := by
            fin_cases v
            · exact absurd (Or.inl rfl) hp.2
            · exact h01.2.2.2.1
            · exact h02.2.2.2.1
            · exact h03.2.2.2.1
            · exact absurd (Or.inr rfl) hp.2
          exact not_le.mpr (lt_of_le_of_lt hu_le hv_gt)
        have hc2 : 0 < clippedCutPotential P' ({0, 4} : Finset (Fin 5)) t₁ := by
          refine Finset.card_pos.mpr ⟨((0 : Fin 5), (1 : Fin 5)), ?_⟩
          simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_sdiff, Finset.mem_univ,
            true_and, Finset.mem_insert, Finset.mem_singleton]
          exact ⟨by simp, le_of_lt h01.2.2.2.2.1⟩
        have hc3 : clippedCutPotential P' ({0, 4} : Finset (Fin 5)) t₄ = 0 := by
          unfold clippedCutPotential; rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
          rintro ⟨u, v⟩ hp
          simp only [Finset.mem_product, Finset.mem_sdiff, Finset.mem_univ, true_and,
            Finset.mem_insert, Finset.mem_singleton] at hp
          have hu_le : clippedG P' u t₄ ≤ clippedG P' 4 t₄ := by
            rcases hp.1 with rfl | rfl <;> [exact le_of_lt h04_t4; exact le_rfl]
          have hv_gt : clippedG P' 4 t₄ < clippedG P' v t₄ := by
            fin_cases v
            · exact absurd (Or.inl rfl) hp.2
            · exact h14.2.2.2.2.1
            · exact h24.2.2.2.2.1
            · exact h34.2.2.2.2.1
            · exact absurd (Or.inr rfl) hp.2
          exact not_le.mpr (lt_of_le_of_lt hu_le hv_gt)
        have hM := duplicate_slice_of_cutPotential P' hgp' htop' h_shat' ({0, 4} : Finset (Fin 5))
          (by simp) (by simp) (lt_trans (by norm_num) hap0.1) ht01 ht14 (lt_trans hap4.2.1 (by norm_num))
          hc1 hc2 hc3
        rw [Finset.card_pair (by decide)] at hM; omega
    · -- `M = {4}` splits across `(τm, t₁, t₄)`
      have hc1 : clippedCutPotential P' ({4} : Finset (Fin 5)) τm = 0 := by
        unfold clippedCutPotential; rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        rintro ⟨u, v⟩ hp
        simp only [Finset.mem_product, Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_singleton] at hp
        rw [hp.1]; exact not_le.mpr (hτm_min v hp.2)
      have hc2 : 0 < clippedCutPotential P' ({4} : Finset (Fin 5)) t₁ := by
        refine Finset.card_pos.mpr ⟨((4 : Fin 5), (1 : Fin 5)), ?_⟩
        simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_singleton]
        exact ⟨by simp, le_of_lt h14.2.2.2.1⟩
      have hc3 : clippedCutPotential P' ({4} : Finset (Fin 5)) t₄ = 0 := by
        unfold clippedCutPotential; rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        rintro ⟨u, v⟩ hp
        simp only [Finset.mem_product, Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_singleton] at hp
        rw [hp.1]
        have hlt : clippedG P' 4 t₄ < clippedG P' v t₄ := by
          fin_cases v
          · exact h40_t4
          · exact h14.2.2.2.2.1
          · exact h24.2.2.2.2.1
          · exact h34.2.2.2.2.1
          · exact absurd rfl hp.2
        exact not_le.mpr hlt
      have hM := duplicate_slice_of_cutPotential P' hgp' htop' h_shat' ({4} : Finset (Fin 5))
        (by simp) (by simp) hτm_0 hτm_t1 ht14 (lt_trans hap4.2.1 (by norm_num)) hc1 hc2 hc3
      simp only [Finset.card_singleton] at hM; omega

end CaseA
end
