import RootTask.CaseAHull

open Finset
open Classical
set_option maxRecDepth 4000

noncomputable section

namespace CaseA

/-- Apex ray parameter `t_i = rayParam (P.apex i) ∈ (1, 2)` of wedge `i`. -/
def apexRay (P : DualConfig) (i : Fin 5) : ℝ :=
  rayParam (P.apex i)

/-- Left endpoint `α_i ∈ [0, t_i)` of the open positivity interval `I_i^+` on `(0, 3)`. -/
def posLeft (P : DualConfig) (i : Fin 5) : ℝ :=
  sInf {t : ℝ | 0 < t ∧ t < 3 ∧ 0 < supportF P i t}

/-- Right endpoint `β_i ∈ (t_i, 3]` of the open positivity interval `I_i^+` on `(0, 3)`. -/
def posRight (P : DualConfig) (i : Fin 5) : ℝ :=
  sSup {t : ℝ | 0 < t ∧ t < 3 ∧ 0 < supportF P i t}

/-- Finite set `Z_{ij}^+` of strictly positive ray ties between `F_i` and `F_j` on `(0, 3)`. -/
def posPairTies (P : DualConfig) (i j : Fin 5) : Finset ℝ :=
  (candTieGrid P).filter fun t =>
    0 < t ∧ t < 3 ∧ supportF P i t = supportF P j t ∧ 0 < supportF P i t

/-- Total positive crossing locus `𝒳^+ = ⋃_{i < j} Z_{ij}^+` on `(0, 3)`. -/
def allPosTieSet (P : DualConfig) : Finset ℝ :=
  ((Finset.univ : Finset (Fin 5 × Fin 5)).filter (fun p => p.1 < p.2)).biUnion
    fun p => posPairTies P p.1 p.2

/-- Clipped continuous wedge support utility `G_i(t) = max(F_i(t), 0)`. -/
def clippedG (P : DualConfig) (i : Fin 5) (t : ℝ) : ℝ :=
  max (supportF P i t) 0

/-- Sorted `k`-th order statistic `G_{(k+1)}(t)` (`k ∈ Fin 5`, bottom-to-top) of `clippedG`. -/
def sortedG (P : DualConfig) (k : Fin 5) (t : ℝ) : ℝ :=
  ((List.ofFn (fun i : Fin 5 => clippedG P i t)).mergeSort (· ≤ ·)).getD k.val 0

/-- Rank positivity locus `J_{q+1} = {t ∈ (0, 3) : G_{(q+1)}(t) > 0}` (`q ∈ {1, 2, 3, 4}`). -/
def rankInterval (P : DualConfig) (q : ℕ) : Set ℝ :=
  if h : q < 5 then {t : ℝ | 0 < t ∧ t < 3 ∧ 0 < sortedG P ⟨q, h⟩ t}
  else ∅

/-- Rank-`(q, q+1)` tie set `X_q^+ = {t ∈ J_{q+1} : G_{(q)}(t) = G_{(q+1)}(t)}`. -/
def rankTieSet (P : DualConfig) (q : ℕ) : Finset ℝ :=
  (allPosTieSet P).filter fun t =>
    if h : 0 < q ∧ q < 5 then
      0 < sortedG P ⟨q, h.2⟩ t ∧ sortedG P ⟨q - 1, by omega⟩ t = sortedG P ⟨q, h.2⟩ t
    else False

/-- Open `1`D slice intervals `I_{q, 0}, ..., I_{q, k_q^+}` partitioning `J_{q+1} \ X_q^+`. -/
def sliceIntervals (P : DualConfig) (q : ℕ) : List (Set ℝ) :=
  let a := sInf (rankInterval P q)
  let b := sSup (rankInterval P q)
  let pts := [a] ++ (rankTieSet P q).sort (· ≤ ·) ++ [b]
  (List.range (pts.length - 1)).map fun ℓ =>
    Set.Ioo (pts.getD ℓ 0) (pts.getD (ℓ + 1) 3)

/-- Number `T_m^+` of unordered pairs `{i, j}` (`i < j`) with `|Z_{ij}^+| = m`. -/
def crossCountOfMult (P : DualConfig) (m : ℕ) : ℕ :=
  (((Finset.univ : Finset (Fin 5 × Fin 5)).filter
    (fun p => p.1 < p.2 ∧ (posPairTies P p.1 p.2).card = m))).card

/-- Slice-excess count `Δ_q = (1 + k_q^+) - Nat.choose 5 q` (`q ∈ {1, 2, 3}`). -/
def sliceExcess (P : DualConfig) (q : ℕ) : ℤ :=
  (1 + (rankTieSet P q).card : ℤ) - (Nat.choose 5 q : ℤ)

/-- Single branch switch of `supportF P i` at `apexRay P i ∈ (1, 2)`. -/
theorem supportF_branch_switch (P : DualConfig) (hgp : IsGenPos P) :
    Function.Injective (apexRay P) ∧
    (∀ i : Fin 5, 1 < apexRay P i ∧ apexRay P i < 2 ∧
      0 < supportF P i (apexRay P i) ∧
      (∀ t : ℝ, 0 ≤ t → t < apexRay P i →
        dot2 (P.p2 i) (gamma t) < dot2 (P.p1 i) (gamma t)) ∧
      (∀ t : ℝ, apexRay P i < t → t ≤ 3 →
        dot2 (P.p1 i) (gamma t) < dot2 (P.p2 i) (gamma t))) := by
  have hmain : ∀ i : Fin 5, 1 < apexRay P i ∧ apexRay P i < 2 ∧
      0 < supportF P i (apexRay P i) ∧
      (∀ t : ℝ, 0 ≤ t → t < apexRay P i →
        dot2 (P.p2 i) (gamma t) < dot2 (P.p1 i) (gamma t)) ∧
      (∀ t : ℝ, apexRay P i < t → t ≤ 3 →
        dot2 (P.p1 i) (gamma t) < dot2 (P.p2 i) (gamma t)) := by
    intro i
    obtain ⟨hq3, hp1_ap, _, hdiff⟩ := P.apex_spec i
    have hom : InOmega (P.apex i) := Or.inl hq3.1
    have h12 : 1 < apexRay P i ∧ apexRay P i < 2 := (inQ3_iff_rayParam hom).mp hq3
    have hnorm : 0 < |(P.apex i).1| + |(P.apex i).2| := inOmega_norm_pos hom
    have hrec : (|(P.apex i).1| + |(P.apex i).2|) • gamma (apexRay P i) = P.apex i :=
      gamma_rayParam_smul hom
    have hpos_ap : 0 < supportF P i (apexRay P i) := by
      rw [← hrec, dot2_smul_right] at hp1_ap
      have hp1_g : 0 < dot2 (P.p1 i) (gamma (apexRay P i)) :=
        pos_of_mul_pos_right (by linarith) (le_of_lt hnorm)
      exact lt_of_lt_of_le hp1_g (le_max_left _ _)
    have hdet_pos : 0 < det2 (P.p1 i) (P.p2 i) := P.h_det i
    have hsub_dot : ∀ u v w : ℝ × ℝ, dot2 (u - v) w = dot2 u w - dot2 v w := by
      intro u v w; simp only [dot2, Prod.fst_sub, Prod.snd_sub]; ring
    refine ⟨h12.1, h12.2, hpos_ap, ?_, ?_⟩
    · intro t ht0 hlt
      have hd_pos : 0 < det2 (gamma t) (gamma (apexRay P i)) :=
        (gamma_det2_sign ht0 hlt (by linarith [h12.2])).1.mpr (by linarith [h12.2])
      have hd_neg : det2 (P.apex i) (gamma t) < 0 := by
        rw [← hrec, det2_smul_left, det2_antisymm]
        nlinarith
      have hd := hdiff (gamma t)
      rw [hsub_dot] at hd
      nlinarith
    · intro t hgt ht3
      have hd_pos : 0 < det2 (gamma (apexRay P i)) (gamma t) :=
        (gamma_det2_sign (by linarith [h12.1]) hgt ht3).1.mpr (by linarith [h12.1])
      have hd_ap : 0 < det2 (P.apex i) (gamma t) := by
        rw [← hrec, det2_smul_left]
        exact mul_pos hnorm hd_pos
      have hd := hdiff (gamma t)
      rw [hsub_dot] at hd
      nlinarith
  refine ⟨?_, hmain⟩
  intro i j hij
  by_contra hne
  obtain ⟨hq3_i, _, _, hdiff_i⟩ := P.apex_spec i
  obtain ⟨hq3_j, _, _, hdiff_j⟩ := P.apex_spec j
  have hom_i : InOmega (P.apex i) := Or.inl hq3_i.1
  have hom_j : InOmega (P.apex j) := Or.inl hq3_j.1
  have hrec_i := gamma_rayParam_smul hom_i
  have hrec_j := gamma_rayParam_smul hom_j
  have hnorm_i := inOmega_norm_pos hom_i
  have hdet_ap : det2 (P.apex i) (P.apex j) = 0 := by
    change rayParam (P.apex i) = rayParam (P.apex j) at hij
    rw [← hrec_i, ← hrec_j, hij, det2_smul_left, det2_smul_right, det2_self]
    ring
  have hd_i : dot2 (P.p2 i - P.p1 i) (P.apex j) = 0 := by
    rw [hdiff_i (P.apex j), hdet_ap, mul_zero]
  have hd_j : dot2 (P.p2 j - P.p1 j) (P.apex j) = 0 := by
    rw [hdiff_j (P.apex j), det2_self, mul_zero]
  have hapj_nz : (P.apex j).1 ≠ 0 := ne_of_lt hq3_j.1
  have hdet_diff_zero : det2 (P.p1 i - P.p2 i) (P.p1 j - P.p2 j) = 0 := by
    unfold dot2 at hd_i hd_j
    simp only [Prod.fst_sub, Prod.snd_sub] at hd_i hd_j
    have hcomb : (P.apex j).1 * det2 (P.p1 i - P.p2 i) (P.p1 j - P.p2 j) =
        ((P.p1 i).2 - (P.p2 i).2) * (((P.p2 j).1 - (P.p1 j).1) * (P.apex j).1 + ((P.p2 j).2 - (P.p1 j).2) * (P.apex j).2) -
        ((P.p1 j).2 - (P.p2 j).2) * (((P.p2 i).1 - (P.p1 i).1) * (P.apex j).1 + ((P.p2 i).2 - (P.p1 i).2) * (P.apex j).2) := by
      simp only [det2, Prod.fst_sub, Prod.snd_sub]; ring
    rw [hd_j, hd_i] at hcomb
    simp at hcomb
    exact hcomb.resolve_left hapj_nz
  let a : Fin 10 := ⟨2 * i.val, by omega⟩
  let b : Fin 10 := ⟨2 * i.val + 1, by omega⟩
  let c : Fin 10 := ⟨2 * j.val, by omega⟩
  let d : Fin 10 := ⟨2 * j.val + 1, by omega⟩
  have hab : a < b := by show 2 * i.val < 2 * i.val + 1; omega
  have hcd : c < d := by show 2 * j.val < 2 * j.val + 1; omega
  have hpair_ne : (a, b) ≠ (c, d) := by
    intro hp
    have : a.val = c.val := congrArg (fun x => x.1.val) hp
    dsimp [a, c] at this
    exact hne (Fin.ext (by omega))
  have hgp5 := hgp.2.2.2.2 a b c d hab hcd hpair_ne
  rw [P.vec_even i, P.vec_odd i, P.vec_even j, P.vec_odd j] at hgp5
  exact hgp5 hdet_diff_zero

private lemma supportF_continuous (P : DualConfig) (i : Fin 5) :
    Continuous (supportF P i) := by
  unfold supportF dot2
  exact Continuous.max
    ((continuous_const.mul gamma_continuous.fst).add (continuous_const.mul gamma_continuous.snd))
    ((continuous_const.mul gamma_continuous.fst).add (continuous_const.mul gamma_continuous.snd))

private lemma supportF_apex_dots (P : DualConfig) (i : Fin 5) :
    dot2 (P.p1 i) (gamma (apexRay P i)) = supportF P i (apexRay P i) ∧
    dot2 (P.p2 i) (gamma (apexRay P i)) = supportF P i (apexRay P i) := by
  obtain ⟨hq3, hd1, hd2, _⟩ := P.apex_spec i
  have hom : InOmega (P.apex i) := Or.inl hq3.1
  have hnorm := inOmega_norm_pos hom
  have hrec := gamma_rayParam_smul hom
  have hne : |((P.apex i).1)| + |((P.apex i).2)| ≠ 0 := ne_of_gt hnorm
  have heq : dot2 (P.p1 i) (gamma (apexRay P i)) = dot2 (P.p2 i) (gamma (apexRay P i)) := by
    apply mul_left_cancel₀ hne
    rw [← dot2_smul_right, ← dot2_smul_right]
    change dot2 (P.p1 i) ((|(P.apex i).1| + |(P.apex i).2|) • gamma (rayParam (P.apex i))) =
      dot2 (P.p2 i) ((|(P.apex i).1| + |(P.apex i).2|) • gamma (rayParam (P.apex i)))
    rw [hrec, hd1, hd2]
  unfold supportF
  rw [heq, max_self]
  exact ⟨rfl, rfl⟩

/-- Each `I_i^+ = {t ∈ (0, 3) : F_i(t) > 0}` equals the open interval `(posLeft P i, posRight P i)`. -/
theorem posInterval_eq_Ioo (P : DualConfig) (hgp : IsGenPos P) (i : Fin 5) :
    0 ≤ posLeft P i ∧ posLeft P i < apexRay P i ∧
    apexRay P i < posRight P i ∧ posRight P i ≤ 3 ∧
    ∀ t : ℝ, (0 < t ∧ t < 3 ∧ 0 < supportF P i t) ↔
      posLeft P i < t ∧ t < posRight P i := by
  have hap := (supportF_branch_switch P hgp).2 i
  have hap_dots := supportF_apex_dots P i
  let S : Set ℝ := {t : ℝ | 0 < t ∧ t < 3 ∧ 0 < supportF P i t}
  have hap_mem : apexRay P i ∈ S := ⟨by linarith [hap.1], by linarith [hap.2.1], hap.2.2.1⟩
  have hne : S.Nonempty := ⟨apexRay P i, hap_mem⟩
  have hbdd_below : BddBelow S := ⟨0, fun _ ht => le_of_lt ht.1⟩
  have hbdd_above : BddAbove S := ⟨3, fun _ ht => le_of_lt ht.2.1⟩
  have h0_le : 0 ≤ posLeft P i := le_csInf hne fun _ ht => le_of_lt ht.1
  have h_le3 : posRight P i ≤ 3 := csSup_le hne fun _ ht => le_of_lt ht.2.1
  have hopen : IsOpen S := by
    have hS_eq : S = Set.Ioo (0 : ℝ) 3 ∩ {t : ℝ | 0 < supportF P i t} := by
      ext t; simp [S, and_assoc]
    rw [hS_eq]
    exact isOpen_Ioo.inter
      (isOpen_lt (continuous_const : Continuous fun _ => (0 : ℝ)) (supportF_continuous P i))
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hopen (apexRay P i) hap_mem
  have hleft_lt : posLeft P i < apexRay P i := by
    have hmem : apexRay P i - δ / 2 ∈ S := hball (by
      rw [Metric.mem_ball, Real.dist_eq, abs_sub_comm, sub_sub_cancel, abs_of_pos (by linarith)]
      linarith)
    have h1 := csInf_le hbdd_below hmem
    change posLeft P i ≤ _ at h1
    linarith
  have hright_gt : apexRay P i < posRight P i := by
    have hmem : apexRay P i + δ / 2 ∈ S := hball (by
      rw [Metric.mem_ball, Real.dist_eq, add_sub_cancel_left, abs_of_pos (by linarith)]
      linarith)
    have h1 := le_csSup hbdd_above hmem
    change _ ≤ posRight P i at h1
    linarith
  have hpos_left_wing : ∀ t₁ s : ℝ, 0 < t₁ → t₁ < s → s ≤ apexRay P i →
      0 < supportF P i t₁ → 0 < supportF P i s := by
    intro t₁ s ht1 hts hs hft1
    have hp1_t1 : 0 < dot2 (P.p1 i) (gamma t₁) := by
      have hlt := hap.2.2.2.1 t₁ (le_of_lt ht1) (lt_of_lt_of_le hts hs)
      unfold supportF at hft1
      rw [max_eq_left (le_of_lt hlt)] at hft1
      exact hft1
    have hp1_ap : 0 < dot2 (P.p1 i) (gamma (apexRay P i)) := by
      rw [hap_dots.1]; exact hap.2.2.1
    rcases eq_or_lt_of_le hs with rfl | hs_lt
    · exact hap.2.2.1
    · have hspan : apexRay P i - t₁ < 2 := by linarith [hap.2.1]
      have hd_outer : 0 < det2 (gamma t₁) (gamma (apexRay P i)) :=
        (gamma_det2_sign (le_of_lt ht1) (lt_trans hts hs_lt) (by linarith [hap.2.1])).1.mpr hspan
      have hd_left : 0 < det2 (gamma t₁) (gamma s) :=
        (gamma_det2_sign (le_of_lt ht1) hts (by linarith [hap.2.1])).1.mpr (by linarith)
      have hd_right : 0 < det2 (gamma s) (gamma (apexRay P i)) :=
        (gamma_det2_sign (le_of_lt (lt_trans ht1 hts)) hs_lt (by linarith [hap.2.1])).1.mpr (by linarith)
      have hcr := cramer_dot (P.p1 i) (gamma t₁) (gamma s) (gamma (apexRay P i))
      have hmul : 0 < det2 (gamma t₁) (gamma (apexRay P i)) * dot2 (P.p1 i) (gamma s) := by
        rw [hcr]
        exact add_pos (mul_pos hd_right hp1_t1) (mul_pos hd_left hp1_ap)
      have hp1_s : 0 < dot2 (P.p1 i) (gamma s) := pos_of_mul_pos_right hmul (le_of_lt hd_outer)
      exact lt_of_lt_of_le hp1_s (le_max_left _ _)
  have hpos_right_wing : ∀ s t₂ : ℝ, apexRay P i ≤ s → s < t₂ → t₂ < 3 →
      0 < supportF P i t₂ → 0 < supportF P i s := by
    intro s t₂ hs hst ht2 hft2
    have hp2_t2 : 0 < dot2 (P.p2 i) (gamma t₂) := by
      have hlt := hap.2.2.2.2 t₂ (lt_of_le_of_lt hs hst) (le_of_lt ht2)
      unfold supportF at hft2
      rw [max_eq_right (le_of_lt hlt)] at hft2
      exact hft2
    have hp2_ap : 0 < dot2 (P.p2 i) (gamma (apexRay P i)) := by
      rw [hap_dots.2]; exact hap.2.2.1
    rcases eq_or_lt_of_le hs with rfl | hs_gt
    · exact hap.2.2.1
    · have hspan : t₂ - apexRay P i < 2 := by linarith [hap.1]
      have hd_outer : 0 < det2 (gamma (apexRay P i)) (gamma t₂) :=
        (gamma_det2_sign (by linarith [hap.1]) (lt_trans hs_gt hst) (le_of_lt ht2)).1.mpr hspan
      have hd_left : 0 < det2 (gamma (apexRay P i)) (gamma s) :=
        (gamma_det2_sign (by linarith [hap.1]) hs_gt (by linarith)).1.mpr (by linarith)
      have hd_right : 0 < det2 (gamma s) (gamma t₂) :=
        (gamma_det2_sign (by linarith [hap.1]) hst (le_of_lt ht2)).1.mpr (by linarith)
      have hcr := cramer_dot (P.p2 i) (gamma (apexRay P i)) (gamma s) (gamma t₂)
      have hmul : 0 < det2 (gamma (apexRay P i)) (gamma t₂) * dot2 (P.p2 i) (gamma s) := by
        rw [hcr]
        exact add_pos (mul_pos hd_right hp2_ap) (mul_pos hd_left hp2_t2)
      have hp2_s : 0 < dot2 (P.p2 i) (gamma s) := pos_of_mul_pos_right hmul (le_of_lt hd_outer)
      exact lt_of_lt_of_le hp2_s (le_max_right _ _)
  refine ⟨h0_le, hleft_lt, hright_gt, h_le3, fun t => ?_⟩
  constructor
  · intro ht
    have hmem : t ∈ S := ht
    have hle_lo : posLeft P i ≤ t := csInf_le hbdd_below hmem
    have hle_hi : t ≤ posRight P i := le_csSup hbdd_above hmem
    obtain ⟨δ', hδ', hball'⟩ := Metric.isOpen_iff.mp hopen t hmem
    have ht_lo : posLeft P i < t := by
      have hmem' : t - δ' / 2 ∈ S := hball' (by
        rw [Metric.mem_ball, Real.dist_eq, abs_sub_comm, sub_sub_cancel, abs_of_pos (by linarith)]
        linarith)
      have h1 := csInf_le hbdd_below hmem'
      change posLeft P i ≤ _ at h1
      linarith
    have ht_hi : t < posRight P i := by
      have hmem' : t + δ' / 2 ∈ S := hball' (by
        rw [Metric.mem_ball, Real.dist_eq, add_sub_cancel_left, abs_of_pos (by linarith)]
        linarith)
      have h1 := le_csSup hbdd_above hmem'
      change _ ≤ posRight P i at h1
      linarith
    exact ⟨ht_lo, ht_hi⟩
  · rintro ⟨ht_lo, ht_hi⟩
    refine ⟨by linarith, by linarith, ?_⟩
    rcases le_or_gt t (apexRay P i) with hle | hgt
    · obtain ⟨t₁, ht1_mem, ht1_lt⟩ := exists_lt_of_csInf_lt hne ht_lo
      exact hpos_left_wing t₁ t ht1_mem.1 ht1_lt hle ht1_mem.2.2
    · obtain ⟨t₂, ht2_mem, ht2_gt⟩ := exists_lt_of_lt_csSup hne ht_hi
      exact hpos_right_wing t t₂ (le_of_lt hgt) ht2_gt ht2_mem.2.1 ht2_mem.2.2

/-- All five positivity intervals share the ray parameter `t_{00000}` of the all-`false` witness. -/
theorem posInterval_common_anchor (P : DualConfig) (hgp : IsGenPos P)
    (h_shat : ∀ m : Fin 5 → Bool, ∃ z : ℝ × ℝ, InOmega z ∧ RealizesDualMask P m z) :
    ∃ t₀ : ℝ, 0 < t₀ ∧ t₀ < 3 ∧
      ∀ i : Fin 5, posLeft P i < t₀ ∧ t₀ < posRight P i := by
  obtain ⟨z₀, hz₀_om, hz₀_mask⟩ := h_shat (fun _ => false)
  have ht₀ := rayParam_mem_Ioo hz₀_om
  have hnorm := inOmega_norm_pos hz₀_om
  have hrec := gamma_rayParam_smul hz₀_om
  refine ⟨rayParam z₀, ht₀.1, ht₀.2, fun i => ?_⟩
  rw [← (posInterval_eq_Ioo P hgp i).2.2.2.2 (rayParam z₀)]
  refine ⟨ht₀.1, ht₀.2, ?_⟩
  have hm_i := hz₀_mask i
  simp only [Bool.false_eq_true, ↓reduceIte, DualConfig.MemExt] at hm_i
  unfold supportF
  rcases hm_i with h1 | h2
  · rw [← hrec, dot2_smul_right] at h1
    exact lt_of_lt_of_le (pos_of_mul_pos_right (by linarith) (le_of_lt hnorm)) (le_max_left _ _)
  · rw [← hrec, dot2_smul_right] at h2
    exact lt_of_lt_of_le (pos_of_mul_pos_right (by linarith) (le_of_lt hnorm)) (le_max_right _ _)

private lemma supportF_tie_at_vec (P : DualConfig) (i : Fin 5) (t : ℝ) :
    ∃ a : Fin 10, vecColor a = i ∧ dot2 (P.vec a) (gamma t) = supportF P i t := by
  unfold supportF
  rcases max_choice (dot2 (P.p1 i) (gamma t)) (dot2 (P.p2 i) (gamma t)) with h | h
  · exact ⟨⟨2 * i.val, by omega⟩, Fin.ext (by dsimp [vecColor]; omega), by rw [P.vec_even i, h]⟩
  · exact ⟨⟨2 * i.val + 1, by omega⟩, Fin.ext (by dsimp [vecColor]; omega), by rw [P.vec_odd i, h]⟩

private lemma ray_tie_in_candTieGrid_sweep (P : DualConfig) (hgp : IsGenPos P)
    {t : ℝ} (ht0 : 0 < t) (ht3 : t < 3) {a b : Fin 10} (hab : a ≠ b)
    (heq : dot2 (P.vec a) (gamma t) = dot2 (P.vec b) (gamma t)) :
    t ∈ candTieGrid P := by
  have hdot_w : dot2 (P.vec a - P.vec b) (gamma t) = 0 := by
    simp only [dot2, Prod.fst_sub, Prod.snd_sub] at *; linarith
  have hw1 : (P.vec a - P.vec b).1 ≠ 0 := sub_ne_zero.mpr (hgp.2.1 a b hab).1
  have hw2 : (P.vec a - P.vec b).2 ≠ 0 := sub_ne_zero.mpr (hgp.2.1 a b hab).2
  set w := P.vec a - P.vec b
  have ht_eq : t = w.2 / (w.1 + w.2) ∨ t = (2 * w.1 - w.2) / (w.1 - w.2) ∨
      t = (2 * w.1 + 3 * w.2) / (w.1 + w.2) := by
    unfold gamma dot2 at hdot_w
    split_ifs at hdot_w with h1 h2
    · left
      have hne : w.1 + w.2 ≠ 0 := by
        intro hsum
        have : w.2 = 0 := by linear_combination t * hsum + hdot_w
        exact hw2 this
      exact eq_div_of_mul_eq hne (by linear_combination -hdot_w)
    · right; left
      have hne : w.1 - w.2 ≠ 0 := by
        intro hdiff
        have : -w.1 = 0 := by linear_combination (1 - t) * hdiff + hdot_w
        exact hw1 (by linarith)
      exact eq_div_of_mul_eq hne (by linear_combination hdot_w)
    · right; right
      have hne : w.1 + w.2 ≠ 0 := by
        intro hsum
        have : w.1 = 0 := by linear_combination (3 - t) * hsum + hdot_w
        exact hw1 this
      exact eq_div_of_mul_eq hne (by linear_combination hdot_w)
  simp only [candTieGrid, Finset.mem_union, Finset.mem_biUnion, Finset.mem_univ, true_and,
    Finset.mem_insert, Finset.mem_singleton]
  right
  refine ⟨(a, b), ?_⟩
  simpa [w] using ht_eq

private lemma posPairTies_comm_sweep (P : DualConfig) (i j : Fin 5) :
    posPairTies P i j = posPairTies P j i := by
  ext t
  simp only [posPairTies, Finset.mem_filter]
  constructor <;> rintro ⟨hg, h0, h3, heq, hpos⟩ <;>
    exact ⟨hg, h0, h3, heq.symm, heq ▸ hpos⟩

private lemma posPairTies_disjoint (P : DualConfig) (hgp : IsGenPos P)
    {i₁ j₁ i₂ j₂ : Fin 5} (hij1 : i₁ < j₁) (hij2 : i₂ < j₂) (hne : (i₁, j₁) ≠ (i₂, j₂)) :
    Disjoint (posPairTies P i₁ j₁) (posPairTies P i₂ j₂) := by
  rw [Finset.disjoint_left]
  intro t ht1 ht2
  simp only [posPairTies, Finset.mem_filter] at ht1 ht2
  obtain ⟨a₁, ha1_col, ha1_dot⟩ := supportF_tie_at_vec P i₁ t
  obtain ⟨b₁, hb1_col, hb1_dot⟩ := supportF_tie_at_vec P j₁ t
  obtain ⟨a₂, ha2_col, ha2_dot⟩ := supportF_tie_at_vec P i₂ t
  obtain ⟨b₂, hb2_col, hb2_dot⟩ := supportF_tie_at_vec P j₂ t
  have hlt1 : a₁ < b₁ := by
    have : a₁.val / 2 < b₁.val / 2 := by
      have h1 := congrArg Fin.val ha1_col
      have h2 := congrArg Fin.val hb1_col
      dsimp [vecColor] at h1 h2
      change i₁.val < j₁.val at hij1
      omega
    change a₁.val < b₁.val; omega
  have hlt2 : a₂ < b₂ := by
    have : a₂.val / 2 < b₂.val / 2 := by
      have h1 := congrArg Fin.val ha2_col
      have h2 := congrArg Fin.val hb2_col
      dsimp [vecColor] at h1 h2
      change i₂.val < j₂.val at hij2
      omega
    change a₂.val < b₂.val; omega
  have hpair_ne : (a₁, b₁) ≠ (a₂, b₂) := by
    intro hp
    apply hne
    have h1 := congrArg (fun p : Fin 10 × Fin 10 => vecColor p.1) hp
    have h2 := congrArg (fun p : Fin 10 × Fin 10 => vecColor p.2) hp
    dsimp at h1 h2
    rw [ha1_col, ha2_col] at h1
    rw [hb1_col, hb2_col] at h2
    exact Prod.ext h1 h2
  exact (ray_ties_zeros_disjoint P hgp).2.2.2 t ht1.2.1 ht1.2.2.1 a₁ b₁ a₂ b₂ hlt1 hlt2 hpair_ne
    ⟨ha1_dot.trans (ht1.2.2.2.1.trans hb1_dot.symm),
     ha2_dot.trans (ht2.2.2.2.1.trans hb2_dot.symm)⟩

private lemma posPairTies_card_le_three (P : DualConfig) (hgp : IsGenPos P)
    {i j : Fin 5} (hij : i < j) :
    (posPairTies P i j).card ≤ 3 := by
  have hap := (supportF_branch_switch P hgp).2
  have hap_i := hap i
  have hap_j := hap j
  let u₁ := min (apexRay P i) (apexRay P j)
  let u₂ := max (apexRay P i) (apexRay P j)
  have hu_lt : u₁ < u₂ := by
    have hne : apexRay P i ≠ apexRay P j := fun h => hij.ne ((supportF_branch_switch P hgp).1 h)
    rcases lt_or_gt_of_ne hne with h | h <;> simp [u₁, u₂, min_eq_left, min_eq_right, max_eq_left, max_eq_right, le_of_lt, h]
  have hu1_gt1 : 1 < u₁ := lt_min hap_i.1 hap_j.1
  have hu2_lt2 : u₂ < 2 := max_lt hap_i.2.1 hap_j.2.1
  have hnot_ap : ∀ t ∈ posPairTies P i j, t ≠ apexRay P i ∧ t ≠ apexRay P j := by
    intro t ht
    simp only [posPairTies, Finset.mem_filter] at ht
    have hrd := (ray_ties_zeros_disjoint P hgp).2.2.2 t ht.2.1 ht.2.2.1
    refine ⟨fun hti => ?_, fun htj => ?_⟩
    · subst hti
      have hd := supportF_apex_dots P i
      obtain ⟨b, hb_col, hb_dot⟩ := supportF_tie_at_vec P j (apexRay P i)
      let a₁ : Fin 10 := ⟨2 * i.val, by omega⟩
      let a₂ : Fin 10 := ⟨2 * i.val + 1, by omega⟩
      have ha12 : a₁ < a₂ := by change 2 * i.val < 2 * i.val + 1; omega
      have hbi : a₁ ≠ b := fun h => hij.ne (by rw [← hb_col, ← h]; ext; dsimp [vecColor, a₁]; omega)
      have heq1 : dot2 (P.vec a₁) (gamma (apexRay P i)) = dot2 (P.vec a₂) (gamma (apexRay P i)) := by
        rw [P.vec_even i, P.vec_odd i, hd.1, hd.2]
      have heq2 : dot2 (P.vec a₁) (gamma (apexRay P i)) = dot2 (P.vec b) (gamma (apexRay P i)) := by
        rw [P.vec_even i, hd.1, ht.2.2.2.1, hb_dot]
      rcases lt_or_gt_of_ne hbi with h1 | h1
      · exact hrd a₁ a₂ a₁ b ha12 h1 (fun hp => by
          have := congrArg (fun p : Fin 10 × Fin 10 => vecColor p.2) hp
          dsimp [a₂] at this
          rw [hb_col] at this
          exact hij.ne (by rw [← this]; ext; dsimp [vecColor]; omega)) ⟨heq1, heq2⟩
      · exact hrd a₁ a₂ b a₁ ha12 h1 (fun hp => by
          have := congrArg (fun p : Fin 10 × Fin 10 => vecColor p.1) hp
          dsimp [a₁] at this
          rw [hb_col] at this
          exact hij.ne (by rw [← this]; ext; dsimp [vecColor]; omega)) ⟨heq1, heq2.symm⟩
    · subst htj
      have hd := supportF_apex_dots P j
      obtain ⟨b, hb_col, hb_dot⟩ := supportF_tie_at_vec P i (apexRay P j)
      let a₁ : Fin 10 := ⟨2 * j.val, by omega⟩
      let a₂ : Fin 10 := ⟨2 * j.val + 1, by omega⟩
      have ha12 : a₁ < a₂ := by change 2 * j.val < 2 * j.val + 1; omega
      have hbi : a₁ ≠ b := fun h => hij.ne ((by rw [← hb_col, ← h]; ext; dsimp [vecColor, a₁]; omega : j = i).symm)
      have heq1 : dot2 (P.vec a₁) (gamma (apexRay P j)) = dot2 (P.vec a₂) (gamma (apexRay P j)) := by
        rw [P.vec_even j, P.vec_odd j, hd.1, hd.2]
      have heq2 : dot2 (P.vec a₁) (gamma (apexRay P j)) = dot2 (P.vec b) (gamma (apexRay P j)) := by
        rw [P.vec_even j, hd.1, ← ht.2.2.2.1, hb_dot]
      rcases lt_or_gt_of_ne hbi with h1 | h1
      · exact hrd a₁ a₂ a₁ b ha12 h1 (fun hp => by
          have := congrArg (fun p : Fin 10 × Fin 10 => vecColor p.2) hp
          dsimp [a₂] at this
          rw [hb_col] at this
          exact hij.ne ((by rw [← this]; ext; dsimp [vecColor]; omega : j = i).symm)) ⟨heq1, heq2⟩
      · exact hrd a₁ a₂ b a₁ ha12 h1 (fun hp => by
          have := congrArg (fun p : Fin 10 × Fin 10 => vecColor p.1) hp
          dsimp [a₁] at this
          rw [hb_col] at this
          exact hij.ne ((by rw [← this]; ext; dsimp [vecColor]; omega : j = i).symm)) ⟨heq1, heq2.symm⟩
  have hno_two_on_seg : ∀ (a b : Fin 10), vecColor a = i → vecColor b = j →
      ∀ s₁ s₂ : ℝ, 0 < s₁ → s₁ < s₂ → s₂ < 3 → s₂ - s₁ < 2 →
      0 < dot2 (P.vec a) (gamma s₁) →
      dot2 (P.vec a) (gamma s₁) = dot2 (P.vec b) (gamma s₁) →
      dot2 (P.vec a) (gamma s₂) = dot2 (P.vec b) (gamma s₂) → False := by
    intro a b ha_col hb_col s₁ s₂ hs1 hlt hs2 hspan hpos1 heq1 heq2
    have hdet_g : 0 < det2 (gamma s₁) (gamma s₂) :=
      (gamma_det2_sign (le_of_lt hs1) hlt (le_of_lt hs2)).1.mpr hspan
    have hcb := cauchy_binet_two (P.vec a) (P.vec b) (gamma s₁) (gamma s₂)
    rw [heq1, heq2] at hcb
    have hzero : det2 (P.vec a) (P.vec b) * det2 (gamma s₁) (gamma s₂) = 0 := by linarith
    have hab : a ≠ b := fun h => hij.ne (by rw [← ha_col, ← hb_col, h])
    exact hgp.2.2.1 a b hab ((mul_eq_zero.mp hzero).resolve_right (ne_of_gt hdet_g))
  have hseg1 : ((posPairTies P i j).filter (fun t => t < u₁)).card ≤ 1 := by
    rw [Finset.card_le_one]
    have hlt_impl : ∀ s₁ ∈ (posPairTies P i j).filter (fun t => t < u₁),
        ∀ s₂ ∈ (posPairTies P i j).filter (fun t => t < u₁), s₁ < s₂ → False := by
      intro s₁ hs₁ s₂ hs₂ hlt
      simp only [Finset.mem_filter, posPairTies] at hs₁ hs₂
      have hs1_i : s₁ < apexRay P i := lt_of_lt_of_le hs₁.2 (min_le_left _ _)
      have hs1_j : s₁ < apexRay P j := lt_of_lt_of_le hs₁.2 (min_le_right _ _)
      have hs2_i : s₂ < apexRay P i := lt_of_lt_of_le hs₂.2 (min_le_left _ _)
      have hs2_j : s₂ < apexRay P j := lt_of_lt_of_le hs₂.2 (min_le_right _ _)
      have hd_i1 : supportF P i s₁ = dot2 (P.p1 i) (gamma s₁) := by
        unfold supportF; exact max_eq_left (le_of_lt (hap_i.2.2.2.1 s₁ (le_of_lt hs₁.1.2.1) hs1_i))
      have hd_j1 : supportF P j s₁ = dot2 (P.p1 j) (gamma s₁) := by
        unfold supportF; exact max_eq_left (le_of_lt (hap_j.2.2.2.1 s₁ (le_of_lt hs₁.1.2.1) hs1_j))
      have hd_i2 : supportF P i s₂ = dot2 (P.p1 i) (gamma s₂) := by
        unfold supportF; exact max_eq_left (le_of_lt (hap_i.2.2.2.1 s₂ (le_of_lt hs₂.1.2.1) hs2_i))
      have hd_j2 : supportF P j s₂ = dot2 (P.p1 j) (gamma s₂) := by
        unfold supportF; exact max_eq_left (le_of_lt (hap_j.2.2.2.1 s₂ (le_of_lt hs₂.1.2.1) hs2_j))
      refine hno_two_on_seg ⟨2 * i.val, by omega⟩ ⟨2 * j.val, by omega⟩
        (Fin.ext (by dsimp [vecColor]; omega)) (Fin.ext (by dsimp [vecColor]; omega))
        s₁ s₂ hs₁.1.2.1 hlt hs₂.1.2.2.1 (by linarith [hap_i.2.1, min_le_left (apexRay P i) (apexRay P j), hs₂.2])
        (by rw [P.vec_even i, ← hd_i1]; exact hs₁.1.2.2.2.2)
        (by rw [P.vec_even i, P.vec_even j, ← hd_i1, ← hd_j1]; exact hs₁.1.2.2.2.1)
        (by rw [P.vec_even i, P.vec_even j, ← hd_i2, ← hd_j2]; exact hs₂.1.2.2.2.1)
    intro s₁ hs₁ s₂ hs₂
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact hlt_impl s₁ hs₁ s₂ hs₂ hlt
    · exact hlt_impl s₂ hs₂ s₁ hs₁ hlt
  have hseg2 : ((posPairTies P i j).filter (fun t => u₁ < t ∧ t < u₂)).card ≤ 1 := by
    rw [Finset.card_le_one]
    have hlt_impl : ∀ s₁ ∈ (posPairTies P i j).filter (fun t => u₁ < t ∧ t < u₂),
        ∀ s₂ ∈ (posPairTies P i j).filter (fun t => u₁ < t ∧ t < u₂), s₁ < s₂ → False := by
      intro s₁ hs₁ s₂ hs₂ hlt
      simp only [Finset.mem_filter, posPairTies] at hs₁ hs₂
      rcases lt_or_gt_of_ne (fun h => hij.ne ((supportF_branch_switch P hgp).1 h)) with hij_ap | hji_ap
      · have hu1_eq : u₁ = apexRay P i := min_eq_left (le_of_lt hij_ap)
        have hu2_eq : u₂ = apexRay P j := max_eq_right (le_of_lt hij_ap)
        have hs1_i : apexRay P i < s₁ := by linarith [hs₁.2.1]
        have hs1_j : s₁ < apexRay P j := by linarith [hs₁.2.2]
        have hs2_i : apexRay P i < s₂ := by linarith [hs₂.2.1]
        have hs2_j : s₂ < apexRay P j := by linarith [hs₂.2.2]
        have hd_i1 : supportF P i s₁ = dot2 (P.p2 i) (gamma s₁) := by
          unfold supportF; exact max_eq_right (le_of_lt (hap_i.2.2.2.2 s₁ hs1_i (le_of_lt hs₁.1.2.2.1)))
        have hd_j1 : supportF P j s₁ = dot2 (P.p1 j) (gamma s₁) := by
          unfold supportF; exact max_eq_left (le_of_lt (hap_j.2.2.2.1 s₁ (le_of_lt hs₁.1.2.1) hs1_j))
        have hd_i2 : supportF P i s₂ = dot2 (P.p2 i) (gamma s₂) := by
          unfold supportF; exact max_eq_right (le_of_lt (hap_i.2.2.2.2 s₂ hs2_i (le_of_lt hs₂.1.2.2.1)))
        have hd_j2 : supportF P j s₂ = dot2 (P.p1 j) (gamma s₂) := by
          unfold supportF; exact max_eq_left (le_of_lt (hap_j.2.2.2.1 s₂ (le_of_lt hs₂.1.2.1) hs2_j))
        refine hno_two_on_seg ⟨2 * i.val + 1, by omega⟩ ⟨2 * j.val, by omega⟩
          (Fin.ext (by dsimp [vecColor]; omega)) (Fin.ext (by dsimp [vecColor]; omega))
          s₁ s₂ hs₁.1.2.1 hlt hs₂.1.2.2.1 (by linarith [hs₁.2.1, hs₂.2.2])
          (by rw [P.vec_odd i, ← hd_i1]; exact hs₁.1.2.2.2.2)
          (by rw [P.vec_odd i, P.vec_even j, ← hd_i1, ← hd_j1]; exact hs₁.1.2.2.2.1)
          (by rw [P.vec_odd i, P.vec_even j, ← hd_i2, ← hd_j2]; exact hs₂.1.2.2.2.1)
      · have hu1_eq : u₁ = apexRay P j := min_eq_right (le_of_lt hji_ap)
        have hu2_eq : u₂ = apexRay P i := max_eq_left (le_of_lt hji_ap)
        have hs1_j : apexRay P j < s₁ := by linarith [hs₁.2.1]
        have hs1_i : s₁ < apexRay P i := by linarith [hs₁.2.2]
        have hs2_j : apexRay P j < s₂ := by linarith [hs₂.2.1]
        have hs2_i : s₂ < apexRay P i := by linarith [hs₂.2.2]
        have hd_i1 : supportF P i s₁ = dot2 (P.p1 i) (gamma s₁) := by
          unfold supportF; exact max_eq_left (le_of_lt (hap_i.2.2.2.1 s₁ (le_of_lt hs₁.1.2.1) hs1_i))
        have hd_j1 : supportF P j s₁ = dot2 (P.p2 j) (gamma s₁) := by
          unfold supportF; exact max_eq_right (le_of_lt (hap_j.2.2.2.2 s₁ hs1_j (le_of_lt hs₁.1.2.2.1)))
        have hd_i2 : supportF P i s₂ = dot2 (P.p1 i) (gamma s₂) := by
          unfold supportF; exact max_eq_left (le_of_lt (hap_i.2.2.2.1 s₂ (le_of_lt hs₂.1.2.1) hs2_i))
        have hd_j2 : supportF P j s₂ = dot2 (P.p2 j) (gamma s₂) := by
          unfold supportF; exact max_eq_right (le_of_lt (hap_j.2.2.2.2 s₂ hs2_j (le_of_lt hs₂.1.2.2.1)))
        refine hno_two_on_seg ⟨2 * i.val, by omega⟩ ⟨2 * j.val + 1, by omega⟩
          (Fin.ext (by dsimp [vecColor]; omega)) (Fin.ext (by dsimp [vecColor]; omega))
          s₁ s₂ hs₁.1.2.1 hlt hs₂.1.2.2.1 (by linarith [hs₁.2.1, hs₂.2.2])
          (by rw [P.vec_even i, ← hd_i1]; exact hs₁.1.2.2.2.2)
          (by rw [P.vec_even i, P.vec_odd j, ← hd_i1, ← hd_j1]; exact hs₁.1.2.2.2.1)
          (by rw [P.vec_even i, P.vec_odd j, ← hd_i2, ← hd_j2]; exact hs₂.1.2.2.2.1)
    intro s₁ hs₁ s₂ hs₂
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact hlt_impl s₁ hs₁ s₂ hs₂ hlt
    · exact hlt_impl s₂ hs₂ s₁ hs₁ hlt
  have hseg3 : ((posPairTies P i j).filter (fun t => u₂ < t)).card ≤ 1 := by
    rw [Finset.card_le_one]
    have hlt_impl : ∀ s₁ ∈ (posPairTies P i j).filter (fun t => u₂ < t),
        ∀ s₂ ∈ (posPairTies P i j).filter (fun t => u₂ < t), s₁ < s₂ → False := by
      intro s₁ hs₁ s₂ hs₂ hlt
      simp only [Finset.mem_filter, posPairTies] at hs₁ hs₂
      have hs1_i : apexRay P i < s₁ := lt_of_le_of_lt (le_max_left _ _) hs₁.2
      have hs1_j : apexRay P j < s₁ := lt_of_le_of_lt (le_max_right _ _) hs₁.2
      have hs2_i : apexRay P i < s₂ := lt_of_le_of_lt (le_max_left _ _) hs₂.2
      have hs2_j : apexRay P j < s₂ := lt_of_le_of_lt (le_max_right _ _) hs₂.2
      have hd_i1 : supportF P i s₁ = dot2 (P.p2 i) (gamma s₁) := by
        unfold supportF; exact max_eq_right (le_of_lt (hap_i.2.2.2.2 s₁ hs1_i (le_of_lt hs₁.1.2.2.1)))
      have hd_j1 : supportF P j s₁ = dot2 (P.p2 j) (gamma s₁) := by
        unfold supportF; exact max_eq_right (le_of_lt (hap_j.2.2.2.2 s₁ hs1_j (le_of_lt hs₁.1.2.2.1)))
      have hd_i2 : supportF P i s₂ = dot2 (P.p2 i) (gamma s₂) := by
        unfold supportF; exact max_eq_right (le_of_lt (hap_i.2.2.2.2 s₂ hs2_i (le_of_lt hs₂.1.2.2.1)))
      have hd_j2 : supportF P j s₂ = dot2 (P.p2 j) (gamma s₂) := by
        unfold supportF; exact max_eq_right (le_of_lt (hap_j.2.2.2.2 s₂ hs2_j (le_of_lt hs₂.1.2.2.1)))
      refine hno_two_on_seg ⟨2 * i.val + 1, by omega⟩ ⟨2 * j.val + 1, by omega⟩
        (Fin.ext (by dsimp [vecColor]; omega)) (Fin.ext (by dsimp [vecColor]; omega))
        s₁ s₂ hs₁.1.2.1 hlt hs₂.1.2.2.1 (by linarith [hu1_gt1, hu_lt, hs₁.2, hs₂.1.2.2.1])
        (by rw [P.vec_odd i, ← hd_i1]; exact hs₁.1.2.2.2.2)
        (by rw [P.vec_odd i, P.vec_odd j, ← hd_i1, ← hd_j1]; exact hs₁.1.2.2.2.1)
        (by rw [P.vec_odd i, P.vec_odd j, ← hd_i2, ← hd_j2]; exact hs₂.1.2.2.2.1)
    intro s₁ hs₁ s₂ hs₂
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact hlt_impl s₁ hs₁ s₂ hs₂ hlt
    · exact hlt_impl s₂ hs₂ s₁ hs₁ hlt
  have hcov : posPairTies P i j ⊆
      ((posPairTies P i j).filter (fun t => t < u₁)) ∪
      ((posPairTies P i j).filter (fun t => u₁ < t ∧ t < u₂)) ∪
      ((posPairTies P i j).filter (fun t => u₂ < t)) := by
    intro t ht
    have hnap := hnot_ap t ht
    have htu1 : t ≠ u₁ := by dsimp [u₁]; rcases min_choice (apexRay P i) (apexRay P j) with h | h <;> rw [h] <;> [exact hnap.1; exact hnap.2]
    have htu2 : t ≠ u₂ := by dsimp [u₂]; rcases max_choice (apexRay P i) (apexRay P j) with h | h <;> rw [h] <;> [exact hnap.1; exact hnap.2]
    simp only [Finset.mem_union, Finset.mem_filter]
    rcases lt_or_gt_of_ne htu1 with h1 | h1
    · left; left; exact ⟨ht, h1⟩
    · rcases lt_or_gt_of_ne htu2 with h2 | h2
      · left; right; exact ⟨ht, h1, h2⟩
      · right; exact ⟨ht, h2⟩
  have hle_sum : (posPairTies P i j).card ≤
      ((posPairTies P i j).filter (fun t => t < u₁)).card +
      ((posPairTies P i j).filter (fun t => u₁ < t ∧ t < u₂)).card +
      ((posPairTies P i j).filter (fun t => u₂ < t)).card :=
    (Finset.card_le_card hcov).trans (Finset.card_union_le _ _ |>.trans (Nat.add_le_add_right (Finset.card_union_le _ _) _))
  omega

private lemma posPairTies_nonempty_of_ne (P : DualConfig) (hgp : IsGenPos P)
    (h_shat : ∀ m : Fin 5 → Bool, ∃ z : ℝ × ℝ, InOmega z ∧ RealizesDualMask P m z)
    {i j : Fin 5} (hne : i ≠ j) :
    1 ≤ (posPairTies P i j).card := by
  by_contra h0
  replace h0 : posPairTies P i j = ∅ := Finset.card_eq_zero.mp (by omega)
  obtain ⟨t₀, ht0_lo, ht0_hi, ht0_pos⟩ := posInterval_common_anchor P hgp h_shat
  have hFi0 : 0 < supportF P i t₀ :=
    ((posInterval_eq_Ioo P hgp i).2.2.2.2 t₀).mpr (ht0_pos i) |>.2.2
  have hFj0 : 0 < supportF P j t₀ :=
    ((posInterval_eq_Ioo P hgp j).2.2.2.2 t₀).mpr (ht0_pos j) |>.2.2
  have hnot_eq0 : supportF P i t₀ ≠ supportF P j t₀ := by
    intro heq
    obtain ⟨a, ha_col, ha_dot⟩ := supportF_tie_at_vec P i t₀
    obtain ⟨b, hb_col, hb_dot⟩ := supportF_tie_at_vec P j t₀
    have hab : a ≠ b := fun h => hne (by rw [← ha_col, ← hb_col, h])
    have hgrid := ray_tie_in_candTieGrid_sweep P hgp ht0_lo ht0_hi hab (ha_dot.trans (heq.trans hb_dot.symm))
    have hmem : t₀ ∈ posPairTies P i j := Finset.mem_filter.mpr ⟨hgrid, ht0_lo, ht0_hi, heq, hFi0⟩
    rw [h0] at hmem
    simp at hmem
  have aux : ∀ (u v : Fin 5), u ≠ v → posPairTies P u v = ∅ →
      0 < supportF P u t₀ → 0 < supportF P v t₀ →
      supportF P v t₀ < supportF P u t₀ → False := by
    intro u v huv hempty hFu0 hFv0 hlt0
    have hlt_all : ∀ t : ℝ, posLeft P v < t → t < posRight P v → supportF P v t < supportF P u t := by
      intro t htv1 htv2
      by_contra hle
      replace hle : supportF P u t ≤ supportF P v t := not_lt.mp hle
      let g : ℝ → ℝ := fun x => supportF P u x - supportF P v x
      have hg_cont : Continuous g := (supportF_continuous P u).sub (supportF_continuous P v)
      have hg0 : 0 < g t₀ := sub_pos.mpr hlt0
      have hgt : g t ≤ 0 := sub_nonpos.mpr hle
      have hs_ex : ∃ s : ℝ, posLeft P v < s ∧ s < posRight P v ∧ g s = 0 := by
        rcases le_or_gt t₀ t with ht0t | htt0
        · obtain ⟨s, hs_mem, hs0⟩ :=
            intermediate_value_Icc' ht0t hg_cont.continuousOn ⟨hgt, le_of_lt hg0⟩
          exact ⟨s, lt_of_lt_of_le (ht0_pos v).1 hs_mem.1, lt_of_le_of_lt hs_mem.2 htv2, hs0⟩
        · obtain ⟨s, hs_mem, hs0⟩ :=
            intermediate_value_Icc (le_of_lt htt0) hg_cont.continuousOn ⟨hgt, le_of_lt hg0⟩
          exact ⟨s, lt_of_lt_of_le htv1 hs_mem.1, lt_of_le_of_lt hs_mem.2 (ht0_pos v).2, hs0⟩
      obtain ⟨s, hsv1, hsv2, hs0⟩ := hs_ex
      have hvs_spec := ((posInterval_eq_Ioo P hgp v).2.2.2.2 s).mpr ⟨hsv1, hsv2⟩
      have heq_s : supportF P u s = supportF P v s := sub_eq_zero.mp hs0
      obtain ⟨a, ha_col, ha_dot⟩ := supportF_tie_at_vec P u s
      obtain ⟨b, hb_col, hb_dot⟩ := supportF_tie_at_vec P v s
      have hab : a ≠ b := fun h => huv (by rw [← ha_col, ← hb_col, h])
      have hgrid := ray_tie_in_candTieGrid_sweep P hgp hvs_spec.1 hvs_spec.2.1 hab
        (ha_dot.trans (heq_s.trans hb_dot.symm))
      have hmem : s ∈ posPairTies P u v :=
        Finset.mem_filter.mpr ⟨hgrid, hvs_spec.1, hvs_spec.2.1, heq_s, heq_s ▸ hvs_spec.2.2⟩
      rw [hempty] at hmem
      simp at hmem
    obtain ⟨z, hz_om, hz_mask⟩ := h_shat (fun k => decide (k = u))
    have hopen_u : P.MemOpen u z := by simpa using hz_mask u
    have hext_v : P.MemExt v z := by simpa [huv.symm] using hz_mask v
    have hnorm := inOmega_norm_pos hz_om
    have hrec := gamma_rayParam_smul hz_om
    have htz := rayParam_mem_Ioo hz_om
    have hFu_lt : supportF P u (rayParam z) < 1 / (|z.1| + |z.2|) := by
      unfold supportF
      rw [max_lt_iff]
      constructor
      · have h1 := hopen_u.1
        rw [← hrec, dot2_smul_right] at h1
        exact (lt_div_iff₀' hnorm).mpr h1
      · have h2 := hopen_u.2
        rw [← hrec, dot2_smul_right] at h2
        exact (lt_div_iff₀' hnorm).mpr h2
    have hFv_gt : 1 / (|z.1| + |z.2|) < supportF P v (rayParam z) := by
      unfold supportF
      rw [lt_max_iff]
      rcases hext_v with h1 | h2
      · left; rw [← hrec, dot2_smul_right] at h1; exact (div_lt_iff₀' hnorm).mpr h1
      · right; rw [← hrec, dot2_smul_right] at h2; exact (div_lt_iff₀' hnorm).mpr h2
    have hFv_pos : 0 < supportF P v (rayParam z) := lt_trans (div_pos one_pos hnorm) hFv_gt
    have htv_mem := ((posInterval_eq_Ioo P hgp v).2.2.2.2 (rayParam z)).mp ⟨htz.1, htz.2, hFv_pos⟩
    linarith [hlt_all (rayParam z) htv_mem.1 htv_mem.2]
  rcases lt_or_gt_of_ne hnot_eq0 with hlt | hgt
  · exact aux j i hne.symm (posPairTies_comm_sweep P i j ▸ h0) hFj0 hFi0 hlt
  · exact aux i j hne h0 hFi0 hFj0 hgt

/-- Pairwise positive crossing bounds `1 ≤ |Z_{ij}^+| ≤ 3` and total crossing sum. -/
theorem card_posPairTies_bounds (P : DualConfig) (hgp : IsGenPos P)
    (h_shat : ∀ m : Fin 5 → Bool, ∃ z : ℝ × ℝ, InOmega z ∧ RealizesDualMask P m z) :
    (∀ i j : Fin 5, i < j →
      1 ≤ (posPairTies P i j).card ∧ (posPairTies P i j).card ≤ 3) ∧
    crossCountOfMult P 1 + crossCountOfMult P 2 + crossCountOfMult P 3 = 10 ∧
    (allPosTieSet P).card + (crossCountOfMult P 1 + crossCountOfMult P 2) +
      crossCountOfMult P 1 = 30 := by
  have hbounds : ∀ i j : Fin 5, i < j →
      1 ≤ (posPairTies P i j).card ∧ (posPairTies P i j).card ≤ 3 :=
    fun i j hij => ⟨posPairTies_nonempty_of_ne P hgp h_shat hij.ne, posPairTies_card_le_three P hgp hij⟩
  let pairs : Finset (Fin 5 × Fin 5) := Finset.univ.filter fun p => p.1 < p.2
  have hpairs_card : pairs.card = 10 := by decide
  have hall_sum : (allPosTieSet P).card = ∑ p ∈ pairs, (posPairTies P p.1 p.2).card := by
    unfold allPosTieSet
    change (pairs.biUnion fun p => posPairTies P p.1 p.2).card = _
    refine Finset.card_biUnion fun p hp q hq hpq => ?_
    exact posPairTies_disjoint P hgp (Finset.mem_filter.mp hp).2 (Finset.mem_filter.mp hq).2 hpq
  have hpart_m : ∀ m : ℕ, crossCountOfMult P m =
      (pairs.filter fun p => (posPairTies P p.1 p.2).card = m).card := by
    intro m; unfold crossCountOfMult pairs; congr 1; ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  have hmem_123 : ∀ p ∈ pairs, (posPairTies P p.1 p.2).card ∈ ({1, 2, 3} : Finset ℕ) := by
    intro p hp
    have hb := hbounds p.1 p.2 (Finset.mem_filter.mp hp).2
    simp only [Finset.mem_insert, Finset.mem_singleton]
    omega
  have hpairs_split : pairs =
      (pairs.filter fun p => (posPairTies P p.1 p.2).card = 1) ∪
      (pairs.filter fun p => (posPairTies P p.1 p.2).card = 2) ∪
      (pairs.filter fun p => (posPairTies P p.1 p.2).card = 3) := by
    ext p
    simp only [Finset.mem_union, Finset.mem_filter]
    constructor
    · intro hp
      have hm := hmem_123 p hp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hm
      rcases hm with h | h | h
      · left; left; exact ⟨hp, h⟩
      · left; right; exact ⟨hp, h⟩
      · right; exact ⟨hp, h⟩
    · rintro ((⟨hp, _⟩ | ⟨hp, _⟩) | ⟨hp, _⟩) <;> exact hp
  have hd12 : Disjoint (pairs.filter fun p => (posPairTies P p.1 p.2).card = 1)
      (pairs.filter fun p => (posPairTies P p.1 p.2).card = 2) := by
    rw [Finset.disjoint_left]; intro p h1 h2
    simp only [Finset.mem_filter] at h1 h2; omega
  have hd123 : Disjoint ((pairs.filter fun p => (posPairTies P p.1 p.2).card = 1) ∪
      (pairs.filter fun p => (posPairTies P p.1 p.2).card = 2))
      (pairs.filter fun p => (posPairTies P p.1 p.2).card = 3) := by
    rw [Finset.disjoint_left]; intro p h12 h3
    simp only [Finset.mem_union, Finset.mem_filter] at h12 h3
    rcases h12 with ⟨_, h⟩ | ⟨_, h⟩ <;> omega
  have hT_sum : crossCountOfMult P 1 + crossCountOfMult P 2 + crossCountOfMult P 3 = 10 := by
    rw [hpart_m 1, hpart_m 2, hpart_m 3, ← Finset.card_union_of_disjoint hd12,
      ← Finset.card_union_of_disjoint hd123, ← hpairs_split, hpairs_card]
  have hsum_eq : ∑ p ∈ pairs, (posPairTies P p.1 p.2).card =
      1 * crossCountOfMult P 1 + 2 * crossCountOfMult P 2 + 3 * crossCountOfMult P 3 := by
    rw [hpart_m 1, hpart_m 2, hpart_m 3]
    conv_lhs => rw [hpairs_split]
    rw [Finset.sum_union hd123, Finset.sum_union hd12]
    have hs1 : ∑ p ∈ pairs.filter (fun p => (posPairTies P p.1 p.2).card = 1),
        (posPairTies P p.1 p.2).card =
        1 * (pairs.filter fun p => (posPairTies P p.1 p.2).card = 1).card := by
      rw [Finset.sum_congr rfl fun p hp => (Finset.mem_filter.mp hp).2, Finset.sum_const, smul_eq_mul, mul_comm]
    have hs2 : ∑ p ∈ pairs.filter (fun p => (posPairTies P p.1 p.2).card = 2),
        (posPairTies P p.1 p.2).card =
        2 * (pairs.filter fun p => (posPairTies P p.1 p.2).card = 2).card := by
      rw [Finset.sum_congr rfl fun p hp => (Finset.mem_filter.mp hp).2, Finset.sum_const, smul_eq_mul, mul_comm]
    have hs3 : ∑ p ∈ pairs.filter (fun p => (posPairTies P p.1 p.2).card = 3),
        (posPairTies P p.1 p.2).card =
        3 * (pairs.filter fun p => (posPairTies P p.1 p.2).card = 3).card := by
      rw [Finset.sum_congr rfl fun p hp => (Finset.mem_filter.mp hp).2, Finset.sum_const, smul_eq_mul, mul_comm]
    rw [hs1, hs2, hs3]
  refine ⟨hbounds, hT_sum, ?_⟩
  rw [hall_sum, hsum_eq]
  omega

private lemma list_ofFn_filter_len {α : Type*} (f : Fin 5 → α) (p : α → Bool) :
    ((List.ofFn f).filter p).length = (Finset.univ.filter (fun i : Fin 5 => p (f i) = true)).card := by
  rw [List.ofFn_eq_map, List.filter_map, List.length_map]
  have hnd : ((List.finRange 5).filter (p ∘ f)).Nodup :=
    (List.nodup_finRange 5).filter _
  rw [← List.toFinset_card_of_nodup hnd]
  congr 1
  ext i
  simp [Function.comp_def]

private lemma sortedG_getElem (P : DualConfig) (k : Fin 5) (t : ℝ) :
    let l := (List.ofFn (fun i : Fin 5 => clippedG P i t)).mergeSort (· ≤ ·)
    have hlen : l.length = 5 := by simp [l]
    sortedG P k t = l[k.val]'(by rw [hlen]; exact k.isLt) := by
  intro l hlen
  unfold sortedG
  simp [l, List.getD_eq_getElem?_getD, hlen, k.isLt]

private lemma sortedG_gt_iff (P : DualConfig) (k : Fin 5) (t ρ : ℝ) :
    ρ < sortedG P k t ↔
      5 - k.val ≤ (Finset.univ.filter (fun i : Fin 5 => ρ < clippedG P i t)).card := by
  let l := (List.ofFn (fun i : Fin 5 => clippedG P i t)).mergeSort (· ≤ ·)
  have hlen : l.length = 5 := by simp [l]
  have hpw : l.Pairwise (· ≤ ·) := List.pairwise_mergeSort' (· ≤ ·) _
  have hperm : l.Perm (List.ofFn (fun i : Fin 5 => clippedG P i t)) := List.mergeSort_perm _ _
  rw [sortedG_getElem P k t]
  have hcount : (Finset.univ.filter (fun i : Fin 5 => ρ < clippedG P i t)).card =
      (l.filter (fun y => decide (ρ < y))).length := by
    have := list_ofFn_filter_len (fun i : Fin 5 => clippedG P i t) (fun y => decide (ρ < y))
    simp only [decide_eq_true_eq] at this
    rw [← this]
    exact (hperm.symm.filter _).length_eq
  rw [hcount]
  have hlen_fin : (l.filter (fun y => decide (ρ < y))).length =
      (Finset.univ.filter (fun j : Fin 5 => ρ < l[j.val]'(by rw [hlen]; exact j.isLt))).card := by
    have heq : l = List.ofFn (fun j : Fin 5 => l[j.val]'(by rw [hlen]; exact j.isLt)) := by
      refine List.ext_getElem (by rw [List.length_ofFn]; exact hlen) fun n hn1 hn2 => ?_
      rw [List.getElem_ofFn]
    conv_lhs => rw [heq]
    rw [list_ofFn_filter_len]
    simp
  rw [hlen_fin]
  constructor
  · intro hlt
    have hsub : (Finset.univ.filter (fun j : Fin 5 => k.val ≤ j.val)) ⊆
        (Finset.univ.filter (fun j : Fin 5 => ρ < l[j.val]'(by rw [hlen]; exact j.isLt))) := by
      intro j hj
      rw [Finset.mem_filter] at hj ⊢
      refine ⟨Finset.mem_univ _, lt_of_lt_of_le hlt ?_⟩
      rcases eq_or_lt_of_le hj.2 with heq | hlt_j
      · have hjk_eq : k = j := Fin.ext heq; subst hjk_eq; rfl
      · exact List.pairwise_iff_getElem.mp hpw k.val j.val (by rw [hlen]; exact k.isLt)
          (by rw [hlen]; exact j.isLt) hlt_j
    have hcard_k : (Finset.univ.filter (fun j : Fin 5 => k.val ≤ j.val)).card = 5 - k.val := by
      have hk := k.isLt
      fin_cases k <;> decide
    rw [← hcard_k]
    exact Finset.card_le_card hsub
  · intro hle
    by_contra hnot
    replace hnot : l[k.val]'(by rw [hlen]; exact k.isLt) ≤ ρ := not_lt.mp hnot
    have hsub : (Finset.univ.filter (fun j : Fin 5 => ρ < l[j.val]'(by rw [hlen]; exact j.isLt))) ⊆
        (Finset.univ.filter (fun j : Fin 5 => k.val < j.val)) := by
      intro j hj
      rw [Finset.mem_filter] at hj ⊢
      refine ⟨Finset.mem_univ _, ?_⟩
      by_contra hjk
      replace hjk : j.val ≤ k.val := not_lt.mp hjk
      have hle_j : l[j.val]'(by rw [hlen]; exact j.isLt) ≤ l[k.val]'(by rw [hlen]; exact k.isLt) := by
        rcases eq_or_lt_of_le hjk with heq | hlt_j
        · have hjk_eq : j = k := Fin.ext heq; subst hjk_eq; rfl
        · exact List.pairwise_iff_getElem.mp hpw j.val k.val (by rw [hlen]; exact j.isLt)
            (by rw [hlen]; exact k.isLt) hlt_j
      linarith [hj.2]
    have hcard_lt : (Finset.univ.filter (fun j : Fin 5 => k.val < j.val)).card = 4 - k.val := by
      have hk := k.isLt
      fin_cases k <;> decide
    have h1 := (Finset.card_le_card hsub).trans_eq hcard_lt
    have hk := k.isLt
    omega

private lemma sortedG_lt_iff (P : DualConfig) (k : Fin 5) (t ρ : ℝ) :
    sortedG P k t < ρ ↔
      k.val + 1 ≤ (Finset.univ.filter (fun i : Fin 5 => clippedG P i t < ρ)).card := by
  let l := (List.ofFn (fun i : Fin 5 => clippedG P i t)).mergeSort (· ≤ ·)
  have hlen : l.length = 5 := by simp [l]
  have hpw : l.Pairwise (· ≤ ·) := List.pairwise_mergeSort' (· ≤ ·) _
  have hperm : l.Perm (List.ofFn (fun i : Fin 5 => clippedG P i t)) := List.mergeSort_perm _ _
  rw [sortedG_getElem P k t]
  have hcount : (Finset.univ.filter (fun i : Fin 5 => clippedG P i t < ρ)).card =
      (l.filter (fun y => decide (y < ρ))).length := by
    have := list_ofFn_filter_len (fun i : Fin 5 => clippedG P i t) (fun y => decide (y < ρ))
    simp only [decide_eq_true_eq] at this
    rw [← this]
    exact (hperm.symm.filter _).length_eq
  rw [hcount]
  have hlen_fin : (l.filter (fun y => decide (y < ρ))).length =
      (Finset.univ.filter (fun j : Fin 5 => l[j.val]'(by rw [hlen]; exact j.isLt) < ρ)).card := by
    have heq : l = List.ofFn (fun j : Fin 5 => l[j.val]'(by rw [hlen]; exact j.isLt)) := by
      refine List.ext_getElem (by rw [List.length_ofFn]; exact hlen) fun n hn1 hn2 => ?_
      rw [List.getElem_ofFn]
    conv_lhs => rw [heq]
    rw [list_ofFn_filter_len]
    simp
  rw [hlen_fin]
  constructor
  · intro hlt
    have hsub : (Finset.univ.filter (fun j : Fin 5 => j.val ≤ k.val)) ⊆
        (Finset.univ.filter (fun j : Fin 5 => l[j.val]'(by rw [hlen]; exact j.isLt) < ρ)) := by
      intro j hj
      rw [Finset.mem_filter] at hj ⊢
      refine ⟨Finset.mem_univ _, lt_of_le_of_lt ?_ hlt⟩
      rcases eq_or_lt_of_le hj.2 with heq | hlt_j
      · have hjk_eq : j = k := Fin.ext heq; subst hjk_eq; rfl
      · exact List.pairwise_iff_getElem.mp hpw j.val k.val (by rw [hlen]; exact j.isLt)
          (by rw [hlen]; exact k.isLt) hlt_j
    have hcard_k : (Finset.univ.filter (fun j : Fin 5 => j.val ≤ k.val)).card = k.val + 1 := by
      have hk := k.isLt
      fin_cases k <;> decide
    rw [← hcard_k]
    exact Finset.card_le_card hsub
  · intro hle
    by_contra hnot
    replace hnot : ρ ≤ l[k.val]'(by rw [hlen]; exact k.isLt) := not_lt.mp hnot
    have hsub : (Finset.univ.filter (fun j : Fin 5 => l[j.val]'(by rw [hlen]; exact j.isLt) < ρ)) ⊆
        (Finset.univ.filter (fun j : Fin 5 => j.val < k.val)) := by
      intro j hj
      rw [Finset.mem_filter] at hj ⊢
      refine ⟨Finset.mem_univ _, ?_⟩
      by_contra hkj
      replace hkj : k.val ≤ j.val := not_lt.mp hkj
      have hle_j : l[k.val]'(by rw [hlen]; exact k.isLt) ≤ l[j.val]'(by rw [hlen]; exact j.isLt) := by
        rcases eq_or_lt_of_le hkj with heq | hlt_j
        · have hkj_eq : k = j := Fin.ext heq; subst hkj_eq; rfl
        · exact List.pairwise_iff_getElem.mp hpw k.val j.val (by rw [hlen]; exact k.isLt)
            (by rw [hlen]; exact j.isLt) hlt_j
      linarith [hj.2]
    have hcard_lt : (Finset.univ.filter (fun j : Fin 5 => j.val < k.val)).card = k.val := by
      have hk := k.isLt
      fin_cases k <;> decide
    have h1 := (Finset.card_le_card hsub).trans_eq hcard_lt
    omega

private lemma sortedG_continuous (P : DualConfig) (k : Fin 5) :
    Continuous (sortedG P k) := by
  let fam : Finset (Finset (Fin 5)) := Finset.univ.filter fun S : Finset (Fin 5) => S.card = 5 - k.val
  have hfam_ne : fam.Nonempty := by
    obtain ⟨S, _, hS⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset (Fin 5))) (n := 5 - k.val)
      (by simp)
    exact ⟨S, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hS⟩⟩
  have hS_ne : ∀ S ∈ fam, S.Nonempty := by
    intro S hS
    have hcard := (Finset.mem_filter.mp hS).2
    have hk := k.isLt
    exact Finset.card_pos.mp (by omega)
  let g : ℝ → ℝ := fun t => fam.sup' hfam_ne fun S =>
    if hS : S.Nonempty then S.inf' hS (fun i => clippedG P i t) else 0
  have hg_eq : sortedG P k = g := by
    ext t
    have hiff : ∀ ρ : ℝ, ρ < sortedG P k t ↔ ρ < g t := by
      intro ρ
      rw [sortedG_gt_iff]
      constructor
      · intro hcard
        obtain ⟨S, hS_sub, hS_card⟩ := Finset.exists_subset_card_eq hcard
        have hS_fam : S ∈ fam := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hS_card⟩
        have hSne := hS_ne S hS_fam
        rw [Finset.lt_sup'_iff]
        refine ⟨S, hS_fam, ?_⟩
        rw [dif_pos hSne, Finset.lt_inf'_iff]
        intro i hi
        exact (Finset.mem_filter.mp (hS_sub hi)).2
      · intro hlt
        rw [Finset.lt_sup'_iff] at hlt
        obtain ⟨S, hS_fam, hS_lt⟩ := hlt
        have hSne := hS_ne S hS_fam
        rw [dif_pos hSne, Finset.lt_inf'_iff] at hS_lt
        have hsub : S ⊆ Finset.univ.filter (fun i : Fin 5 => ρ < clippedG P i t) := by
          intro i hi
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hS_lt i hi⟩
        have := (Finset.mem_filter.mp hS_fam).2
        rw [← this]
        exact Finset.card_le_card hsub
    by_contra hne
    rcases lt_or_gt_of_ne hne with h1 | h2
    · exact lt_irrefl _ ((hiff (sortedG P k t)).mpr h1)
    · exact lt_irrefl _ ((hiff (g t)).mp h2)
  rw [hg_eq]
  refine Continuous.finset_sup'_apply hfam_ne fun S hS => ?_
  have hSne := hS_ne S hS
  simp only [dif_pos hSne]
  exact Continuous.finset_inf'_apply hSne fun i _ => (supportF_continuous P i).max continuous_const

private lemma sortedG_mono (P : DualConfig) {k₁ k₂ : Fin 5} (h : k₁ ≤ k₂) (t : ℝ) :
    sortedG P k₁ t ≤ sortedG P k₂ t := by
  let l := (List.ofFn (fun i : Fin 5 => clippedG P i t)).mergeSort (· ≤ ·)
  have hlen : l.length = 5 := by simp [l]
  have hpw : l.Pairwise (· ≤ ·) := List.pairwise_mergeSort' (· ≤ ·) _
  rw [sortedG_getElem P k₁ t, sortedG_getElem P k₂ t]
  rcases eq_or_lt_of_le h with rfl | hlt
  · rfl
  · exact List.pairwise_iff_getElem.mp hpw k₁.val k₂.val (by rw [hlen]; exact k₁.isLt)
      (by rw [hlen]; exact k₂.isLt) hlt

private lemma sortedG_tie_exists_distinct (P : DualConfig) {k : Fin 5} (hk : 0 < k.val) (t : ℝ)
    (hpos : 0 < sortedG P k t) (heq : sortedG P ⟨k.val - 1, by omega⟩ t = sortedG P k t) :
    ∃ i j : Fin 5, i ≠ j ∧ supportF P i t = sortedG P k t ∧ supportF P j t = sortedG P k t := by
  let l := (List.ofFn (fun i : Fin 5 => clippedG P i t)).mergeSort (· ≤ ·)
  have hlen : l.length = 5 := by simp [l]
  have hperm : l.Perm (List.ofFn (fun i : Fin 5 => clippedG P i t)) := List.mergeSort_perm _ _
  let v := sortedG P k t
  have hk1_lt : k.val - 1 < 5 := by omega
  have hv_k : l[k.val]'(by rw [hlen]; exact k.isLt) = v := (sortedG_getElem P k t).symm
  have hv_km1 : l[k.val - 1]'(by rw [hlen]; exact hk1_lt) = v := by
    have h1 := sortedG_getElem P ⟨k.val - 1, by omega⟩ t
    dsimp at h1
    exact h1.symm.trans heq
  have hcount_ge2 : 2 ≤ (List.ofFn (fun i : Fin 5 => clippedG P i t)).count v := by
    rw [← hperm.count_eq]
    have hcount_eq_filter : l.count v = (l.filter (· == v)).length := by
      simp [List.count_eq_length_filter]
    have hfin_eq : (l.filter (· == v)).length =
        (Finset.univ.filter (fun j : Fin 5 => l[j.val]'(by rw [hlen]; exact j.isLt) = v)).card := by
      have heq_l : l = List.ofFn (fun j : Fin 5 => l[j.val]'(by rw [hlen]; exact j.isLt)) := by
        refine List.ext_getElem (by rw [List.length_ofFn]; exact hlen) fun n hn1 hn2 => ?_
        rw [List.getElem_ofFn]
      conv_lhs => rw [heq_l]
      rw [list_ofFn_filter_len]
      simp
    rw [hcount_eq_filter, hfin_eq]
    have hsub : ({⟨k.val - 1, hk1_lt⟩, k} : Finset (Fin 5)) ⊆
        Finset.univ.filter (fun j : Fin 5 => l[j.val]'(by rw [hlen]; exact j.isLt) = v) := by
      intro j hj
      simp only [Finset.mem_insert, Finset.mem_singleton] at hj
      rcases hj with rfl | rfl
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv_km1⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv_k⟩
    have hne_fin : (⟨k.val - 1, hk1_lt⟩ : Fin 5) ≠ k := by
      intro h; have := congrArg Fin.val h; dsimp at this; omega
    calc 2 = ({⟨k.val - 1, hk1_lt⟩, k} : Finset (Fin 5)).card := (Finset.card_pair hne_fin).symm
      _ ≤ _ := Finset.card_le_card hsub
  have hcard_ge2 : 2 ≤ (Finset.univ.filter (fun i : Fin 5 => clippedG P i t = v)).card := by
    have hlen_f := list_ofFn_filter_len (fun i : Fin 5 => clippedG P i t) (· == v)
    simp only [beq_iff_eq] at hlen_f
    rw [← hlen_f]
    simpa [List.count_eq_length_filter] using hcount_ge2
  obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.mp (Nat.lt_of_lt_of_le (by omega) hcard_ge2)
  rw [Finset.mem_filter] at hi hj
  have hi_eq : supportF P i t = v := by
    have hmi := hi.2; unfold clippedG at hmi
    by_cases h0 : 0 ≤ supportF P i t
    · rw [max_eq_left h0] at hmi; exact hmi
    · rw [max_eq_right (le_of_not_ge h0)] at hmi; exfalso; exact hpos.ne hmi
  have hj_eq : supportF P j t = v := by
    have hmj := hj.2; unfold clippedG at hmj
    by_cases h0 : 0 ≤ supportF P j t
    · rw [max_eq_left h0] at hmj; exact hmj
    · rw [max_eq_right (le_of_not_ge h0)] at hmj; exfalso; exact hpos.ne hmj
  exact ⟨i, j, hij, hi_eq, hj_eq⟩

/-- Connectedness of the rank positivity locus `J_{q+1}` (`1 ≤ q ≤ 4`). -/
theorem rankInterval_eq_Ioo (P : DualConfig) (hgp : IsGenPos P)
    (htop : ∀ {t : ℝ}, 0 ≤ t → t ≤ 3 → 0 < topEnv P t)
    (h_shat : ∀ m : Fin 5 → Bool, ∃ z : ℝ × ℝ, InOmega z ∧ RealizesDualMask P m z)
    {q : ℕ} (hq1 : 1 ≤ q) (hq4 : q ≤ 4) :
    sInf (rankInterval P q) < sSup (rankInterval P q) ∧
    rankInterval P q = Set.Ioo (sInf (rankInterval P q)) (sSup (rankInterval P q)) := by
  have hq5 : q < 5 := by omega
  obtain ⟨t₀, ht0_lo, ht0_hi, ht0_pos⟩ := posInterval_common_anchor P hgp h_shat
  have hchar : ∀ t : ℝ, t ∈ rankInterval P q ↔
      ∃ S : Finset (Fin 5), S.card = 5 - q ∧
        ∀ i ∈ S, posLeft P i < t ∧ t < posRight P i := by
    intro t
    unfold rankInterval
    rw [dif_pos hq5]
    simp only [Set.mem_setOf_eq]
    rw [sortedG_gt_iff]
    dsimp
    constructor
    · rintro ⟨ht0, ht3, hcard⟩
      obtain ⟨S, hS_sub, hS_card⟩ := Finset.exists_subset_card_eq hcard
      refine ⟨S, hS_card, fun i hi => ?_⟩
      have hclip_pos : 0 < clippedG P i t := (Finset.mem_filter.mp (hS_sub hi)).2
      have hsup_pos : 0 < supportF P i t := by
        unfold clippedG at hclip_pos; exact lt_of_lt_of_le hclip_pos (by
          by_cases h : 0 ≤ supportF P i t
          · rw [max_eq_left h]
          · rw [max_eq_right (le_of_not_ge h)] at hclip_pos; linarith)
      exact ((posInterval_eq_Ioo P hgp i).2.2.2.2 t).mp ⟨ht0, ht3, hsup_pos⟩
    · rintro ⟨S, hS_card, hS_mem⟩
      have hS_ne : S.Nonempty := Finset.card_pos.mp (by omega)
      obtain ⟨i₀, hi₀⟩ := hS_ne
      have ht_i0 := ((posInterval_eq_Ioo P hgp i₀).2.2.2.2 t).mpr (hS_mem i₀ hi₀)
      refine ⟨ht_i0.1, ht_i0.2.1, ?_⟩
      have hsub : S ⊆ Finset.univ.filter (fun i : Fin 5 => 0 < clippedG P i t) := by
        intro i hi
        have hti := ((posInterval_eq_Ioo P hgp i).2.2.2.2 t).mpr (hS_mem i hi)
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, lt_of_lt_of_le hti.2.2 (le_max_left _ _)⟩
      rw [← hS_card]
      exact Finset.card_le_card hsub
  let fam : Finset (Finset (Fin 5)) := Finset.univ.filter fun S : Finset (Fin 5) => S.card = 5 - q
  have hfam_ne : fam.Nonempty := by
    obtain ⟨S, _, hS⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset (Fin 5))) (n := 5 - q)
      (by simp)
    exact ⟨S, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hS⟩⟩
  have hS_ne : ∀ S ∈ fam, S.Nonempty := fun S hS =>
    Finset.card_pos.mp (by have := (Finset.mem_filter.mp hS).2; omega)
  let aS : Finset (Fin 5) → ℝ := fun S =>
    if hS : S.Nonempty then S.sup' hS (posLeft P) else 0
  let bS : Finset (Fin 5) → ℝ := fun S =>
    if hS : S.Nonempty then S.inf' hS (posRight P) else 3
  let a := fam.inf' hfam_ne aS
  let b := fam.sup' hfam_ne bS
  have ha_lt_t0 : a < t₀ := by
    rw [Finset.inf'_lt_iff]
    obtain ⟨S, hS⟩ := hfam_ne
    refine ⟨S, hS, ?_⟩
    have hSne := hS_ne S hS
    dsimp [aS]; rw [dif_pos hSne, Finset.sup'_lt_iff]
    intro i _; exact (ht0_pos i).1
  have ht0_lt_b : t₀ < b := by
    rw [Finset.lt_sup'_iff]
    obtain ⟨S, hS⟩ := hfam_ne
    refine ⟨S, hS, ?_⟩
    have hSne := hS_ne S hS
    dsimp [bS]; rw [dif_pos hSne, Finset.lt_inf'_iff]
    intro i _; exact (ht0_pos i).2
  have h_eq_Ioo : rankInterval P q = Set.Ioo a b := by
    ext t
    rw [hchar t, Set.mem_Ioo]
    constructor
    · rintro ⟨S, hS_card, hS_mem⟩
      have hS_fam : S ∈ fam := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hS_card⟩
      have hSne := hS_ne S hS_fam
      have ha_le : a ≤ aS S := Finset.inf'_le aS hS_fam
      have hb_ge : bS S ≤ b := Finset.le_sup' bS hS_fam
      have haS_lt : aS S < t := by
        dsimp [aS]; rw [dif_pos hSne, Finset.sup'_lt_iff]
        intro i hi; exact (hS_mem i hi).1
      have hlt_bS : t < bS S := by
        dsimp [bS]; rw [dif_pos hSne, Finset.lt_inf'_iff]
        intro i hi; exact (hS_mem i hi).2
      exact ⟨lt_of_le_of_lt ha_le haS_lt, lt_of_lt_of_le hlt_bS hb_ge⟩
    · rintro ⟨hat, htb⟩
      rcases le_or_gt t t₀ with htt0 | ht0t
      · rw [Finset.inf'_lt_iff] at hat
        obtain ⟨S, hS_fam, haS_lt⟩ := hat
        have hSne := hS_ne S hS_fam
        dsimp [aS] at haS_lt; rw [dif_pos hSne, Finset.sup'_lt_iff] at haS_lt
        refine ⟨S, (Finset.mem_filter.mp hS_fam).2, fun i hi => ?_⟩
        exact ⟨haS_lt i hi, lt_of_le_of_lt htt0 (ht0_pos i).2⟩
      · rw [Finset.lt_sup'_iff] at htb
        obtain ⟨S, hS_fam, hlt_bS⟩ := htb
        have hSne := hS_ne S hS_fam
        dsimp [bS] at hlt_bS; rw [dif_pos hSne, Finset.lt_inf'_iff] at hlt_bS
        refine ⟨S, (Finset.mem_filter.mp hS_fam).2, fun i hi => ?_⟩
        exact ⟨lt_trans (ht0_pos i).1 ht0t, hlt_bS i hi⟩
  have hab : a < b := lt_trans ha_lt_t0 ht0_lt_b
  rw [h_eq_Ioo, csInf_Ioo hab, csSup_Ioo hab]
  exact ⟨hab, rfl⟩

/-- Partition of `allPosTieSet P` by vertical rank `(q, q+1)` (`1 ≤ q ≤ 4`). -/
theorem allPosTieSet_partition (P : DualConfig) (hgp : IsGenPos P) :
    (allPosTieSet P).card =
      (rankTieSet P 1).card + (rankTieSet P 2).card +
      (rankTieSet P 3).card + (rankTieSet P 4).card := by
  have hall_in : allPosTieSet P = rankTieSet P 1 ∪ rankTieSet P 2 ∪ rankTieSet P 3 ∪ rankTieSet P 4 := by
    ext t
    simp only [Finset.mem_union]
    constructor
    · intro ht
      have ht' := ht
      simp only [allPosTieSet, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and] at ht'
      obtain ⟨⟨i, j⟩, hij, hij_mem⟩ := ht'
      simp only [posPairTies, Finset.mem_filter] at hij_mem
      obtain ⟨_, ht0, ht3, heq_ij, hpos_i⟩ := hij_mem
      let v := clippedG P i t
      have hv_pos : 0 < v := lt_of_lt_of_le hpos_i (le_max_left _ _)
      have hv_eq_j : clippedG P j t = v := by dsimp only [v]; unfold clippedG; rw [heq_ij]
      have hlt_other : ∀ m : Fin 5, m ≠ i → m ≠ j → clippedG P m t ≠ v := by
        intro m hmi hmj heqm
        have hsup_m : supportF P m t = supportF P i t := by
          dsimp only [v] at heqm
          unfold clippedG at heqm
          have hle_m : 0 < supportF P m t := by
            by_contra hle; rw [max_eq_right (not_lt.mp hle)] at heqm; exact hv_pos.ne heqm
          rw [max_eq_left (le_of_lt hle_m), max_eq_left (le_of_lt hpos_i)] at heqm
          exact heqm
        obtain ⟨ai, hai_col, hai_dot⟩ := supportF_tie_at_vec P i t
        obtain ⟨aj, haj_col, haj_dot⟩ := supportF_tie_at_vec P j t
        obtain ⟨am, ham_col, ham_dot⟩ := supportF_tie_at_vec P m t
        have h1 : ai ≠ aj := fun h => hij.ne (by rw [← hai_col, ← haj_col, h])
        have h2 : ai ≠ am := fun h => hmi (by rw [← hai_col, ← ham_col, h])
        rcases lt_or_gt_of_ne h1 with h1' | h1' <;> rcases lt_or_gt_of_ne h2 with h2' | h2'
        · exact (ray_ties_zeros_disjoint P hgp).2.2.2 t ht0 ht3 ai aj ai am h1' h2'
            (fun hp => hmj (by
              have := congrArg (fun p : Fin 10 × Fin 10 => vecColor p.2) hp
              dsimp at this; rw [haj_col, ham_col] at this; exact this.symm))
            ⟨hai_dot.trans (heq_ij.trans haj_dot.symm), hai_dot.trans (hsup_m.symm.trans ham_dot.symm)⟩
        · exact (ray_ties_zeros_disjoint P hgp).2.2.2 t ht0 ht3 ai aj am ai h1' h2'
            (fun hp => hmi (by
              have := congrArg (fun p : Fin 10 × Fin 10 => vecColor p.1) hp
              dsimp at this; rw [hai_col, ham_col] at this; exact this.symm))
            ⟨hai_dot.trans (heq_ij.trans haj_dot.symm), ham_dot.trans (hsup_m.trans hai_dot.symm)⟩
        · exact (ray_ties_zeros_disjoint P hgp).2.2.2 t ht0 ht3 aj ai ai am h1' h2'
            (fun hp => hij.ne (by
              have := congrArg (fun p : Fin 10 × Fin 10 => vecColor p.1) hp
              dsimp at this; rw [haj_col, hai_col] at this; exact this.symm))
            ⟨haj_dot.trans (heq_ij.symm.trans hai_dot.symm), hai_dot.trans (hsup_m.symm.trans ham_dot.symm)⟩
        · exact (ray_ties_zeros_disjoint P hgp).2.2.2 t ht0 ht3 aj ai am ai h1' h2'
            (fun hp => hmj (by
              have := congrArg (fun p : Fin 10 × Fin 10 => vecColor p.1) hp
              dsimp at this; rw [haj_col, ham_col] at this; exact this.symm))
            ⟨haj_dot.trans (heq_ij.symm.trans hai_dot.symm), ham_dot.trans (hsup_m.trans hai_dot.symm)⟩
      let l := (List.ofFn (fun m : Fin 5 => clippedG P m t)).mergeSort (· ≤ ·)
      have hlen : l.length = 5 := by simp [l]
      have hperm : l.Perm (List.ofFn (fun m : Fin 5 => clippedG P m t)) := List.mergeSort_perm _ _
      have hcount_v : l.count v = 2 := by
        rw [hperm.count_eq]
        have hlen_f := list_ofFn_filter_len (fun m : Fin 5 => clippedG P m t) (· == v)
        simp only [beq_iff_eq] at hlen_f
        have hfilt_eq : Finset.univ.filter (fun m : Fin 5 => clippedG P m t = v) = {i, j} := by
          ext m
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton]
          constructor
          · intro hm
            by_contra hno
            push Not at hno
            exact hlt_other m hno.1 hno.2 hm
          · rintro (rfl | rfl) <;> [rfl; exact hv_eq_j]
        rw [List.count_eq_length_filter, hlen_f, hfilt_eq, Finset.card_pair hij.ne]
      have h_ex : ∃ q : ℕ, ∃ hq0 : 0 < q, ∃ hq5 : q < 5,
          sortedG P ⟨q - 1, by omega⟩ t = v ∧ sortedG P ⟨q, hq5⟩ t = v := by
        have hmem_l : v ∈ l := List.count_pos_iff.mp (by omega)
        let S_v := Finset.univ.filter (fun k : Fin 5 => l[k.val]'(by rw [hlen]; exact k.isLt) = v)
        have hSv_card : S_v.card = 2 := by
          have heq_l : l = List.ofFn (fun k : Fin 5 => l[k.val]'(by rw [hlen]; exact k.isLt)) := by
            refine List.ext_getElem (by rw [List.length_ofFn]; exact hlen) fun n hn1 hn2 => ?_
            rw [List.getElem_ofFn]
          have hlen_f := list_ofFn_filter_len (fun k : Fin 5 => l[k.val]'(by rw [hlen]; exact k.isLt)) (· == v)
          simp only [beq_iff_eq] at hlen_f
          rw [← hlen_f, ← heq_l, ← List.count_eq_length_filter, hcount_v]
        obtain ⟨k₁, hk₁, k₂, hk₂, hk12⟩ := Finset.one_lt_card.mp (by omega : 1 < S_v.card)
        have hlt_order : ∀ a₁ a₂ : Fin 5, a₁ ∈ S_v → a₂ ∈ S_v → a₁ < a₂ →
            ∃ q : ℕ, ∃ hq0 : 0 < q, ∃ hq5 : q < 5,
              sortedG P ⟨q - 1, by omega⟩ t = v ∧ sortedG P ⟨q, hq5⟩ t = v := by
          intro a₁ a₂ ha₁ ha₂ hlt_k
          have hpw := List.pairwise_mergeSort' (· ≤ ·) (List.ofFn (fun m : Fin 5 => clippedG P m t))
          change l.Pairwise (· ≤ ·) at hpw
          have hk_succ : a₂.val = a₁.val + 1 := by
            by_contra hne_s
            have hmid_lt : a₁.val + 1 < a₂.val := by omega
            let km : Fin 5 := ⟨a₁.val + 1, by omega⟩
            have h1 : l[a₁.val]'(by rw [hlen]; exact a₁.isLt) ≤ l[km.val]'(by rw [hlen]; exact km.isLt) :=
              List.pairwise_iff_getElem.mp hpw _ _ (by rw [hlen]; exact a₁.isLt) (by rw [hlen]; exact km.isLt) (by dsimp [km]; omega)
            have h2 : l[km.val]'(by rw [hlen]; exact km.isLt) ≤ l[a₂.val]'(by rw [hlen]; exact a₂.isLt) :=
              List.pairwise_iff_getElem.mp hpw _ _ (by rw [hlen]; exact km.isLt) (by rw [hlen]; exact a₂.isLt) (by dsimp [km]; exact hmid_lt)
            rw [Finset.mem_filter] at ha₁ ha₂
            have hkm_v : km ∈ S_v := Finset.mem_filter.mpr ⟨Finset.mem_univ _, by linarith [ha₁.2, ha₂.2]⟩
            have hsub : ({a₁, km, a₂} : Finset (Fin 5)) ⊆ S_v := by
              intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
              rcases hx with rfl | rfl | rfl <;> [exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha₁.2⟩; exact hkm_v; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha₂.2⟩]
            have h3 : ({a₁, km, a₂} : Finset (Fin 5)).card = 3 := by
              rw [Finset.card_insert_of_notMem, Finset.card_pair]
              · intro h; have := congrArg Fin.val h; dsimp [km] at this; omega
              · simp only [Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff]
                dsimp [km]; omega
            have := Finset.card_le_card hsub
            omega
          have ha2_lt : a₂.val < 5 := a₂.isLt
          have h0_lt : 0 < a₂.val := by change a₁.val < a₂.val at hlt_k; omega
          refine ⟨a₂.val, h0_lt, ha2_lt, ?_, ?_⟩
          · rw [sortedG_getElem]
            have hk1' : (⟨a₂.val - 1, by omega⟩ : Fin 5) = a₁ := by ext; dsimp; omega
            rw [hk1']
            exact (Finset.mem_filter.mp ha₁).2
          · rw [sortedG_getElem]
            exact (Finset.mem_filter.mp ha₂).2
        rcases lt_or_gt_of_ne hk12 with hlt_k | hlt_k
        · exact hlt_order k₁ k₂ hk₁ hk₂ hlt_k
        · exact hlt_order k₂ k₁ hk₂ hk₁ hlt_k
      obtain ⟨q, hq0, hq5, hqm1, hq⟩ := h_ex
      have hmem_q : t ∈ rankTieSet P q := by
        unfold rankTieSet
        rw [Finset.mem_filter, dif_pos ⟨hq0, hq5⟩]
        exact ⟨ht, by rw [hq]; exact hv_pos, hqm1.trans hq.symm⟩
      rcases (by omega : q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4) with rfl | rfl | rfl | rfl
      · left; left; left; exact hmem_q
      · left; left; right; exact hmem_q
      · left; right; exact hmem_q
      · right; exact hmem_q
    · rintro (((h | h) | h) | h) <;> exact (Finset.mem_filter.mp h).1
  have hdisj : ∀ q₁ q₂ : ℕ, 1 ≤ q₁ → q₁ < q₂ → q₂ ≤ 4 →
      Disjoint (rankTieSet P q₁) (rankTieSet P q₂) := by
    intro q₁ q₂ hq1 hlt hq2
    rw [Finset.disjoint_left]
    intro t ht1 ht2
    unfold rankTieSet at ht1 ht2
    rw [Finset.mem_filter, dif_pos (by omega)] at ht1
    rw [Finset.mem_filter, dif_pos (by omega)] at ht2
    have hall := ht1.1
    obtain ⟨hpos1, heq1⟩ := ht1.2
    obtain ⟨hpos2, heq2⟩ := ht2.2
    have ht_mem := hall
    simp only [allPosTieSet, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and] at ht_mem
    obtain ⟨⟨i, j⟩, hij, hij_mem⟩ := ht_mem
    simp only [posPairTies, Finset.mem_filter] at hij_mem
    obtain ⟨_, ht0, ht3, heq_ij, hpos_i⟩ := hij_mem
    obtain ⟨a₁, b₁, hab1, ha1, hb1⟩ := sortedG_tie_exists_distinct P (by dsimp; omega) t hpos1 heq1
    obtain ⟨a₂, b₂, hab2, ha2, hb2⟩ := sortedG_tie_exists_distinct P (by dsimp; omega) t hpos2 heq2
    have hpair_eq : ∀ u v : Fin 5, u ≠ v → 0 < supportF P u t → supportF P u t = supportF P v t →
        ({u, v} : Finset (Fin 5)) = {i, j} := by
      intro u v huv hupos huv_eq
      by_contra hne_set
      have hex_notin : ∃ w ∈ ({u, v} : Finset (Fin 5)), w ≠ i ∧ w ≠ j := by
        by_cases hu : u = i ∨ u = j
        · by_cases hv : v = i ∨ v = j
          · exfalso; apply hne_set
            have hsub : ({u, v} : Finset (Fin 5)) ⊆ {i, j} := by
              intro w hw
              simp only [Finset.mem_insert, Finset.mem_singleton] at hw ⊢
              rcases hw with rfl | rfl <;> assumption
            exact Finset.eq_of_subset_of_card_le hsub (by rw [Finset.card_pair huv, Finset.card_pair hij.ne])
          · push Not at hv; exact ⟨v, by simp, hv⟩
        · push Not at hu; exact ⟨u, by simp, hu⟩
      obtain ⟨w, hw_mem, hwi, hwj⟩ := hex_notin
      have hw_eq : supportF P w t = supportF P u t := by
        simp only [Finset.mem_insert, Finset.mem_singleton] at hw_mem
        rcases hw_mem with rfl | rfl <;> [rfl; exact huv_eq.symm]
      let other := if w = u then v else u
      have hw_ne_other : w ≠ other := by
        dsimp [other]
        split_ifs with hwu
        · rw [hwu]; exact huv
        · exact hwu
      have hother_eq : supportF P other t = supportF P w t := by
        dsimp [other]
        split_ifs with hwu
        · rw [hwu]; exact huv_eq.symm
        · have hwv : w = v := by
            simp only [Finset.mem_insert, Finset.mem_singleton] at hw_mem
            exact hw_mem.resolve_left hwu
          rw [hwv]; exact huv_eq
      obtain ⟨aw, haw_col, haw_dot⟩ := supportF_tie_at_vec P w t
      obtain ⟨ao, hao_col, hao_dot⟩ := supportF_tie_at_vec P other t
      obtain ⟨ai, hai_col, hai_dot⟩ := supportF_tie_at_vec P i t
      obtain ⟨aj, haj_col, haj_dot⟩ := supportF_tie_at_vec P j t
      have h1 : ai < aj := by
        have := congrArg Fin.val hai_col; have := congrArg Fin.val haj_col
        dsimp [vecColor] at *; change i.val < j.val at hij; change ai.val < aj.val; omega
      have h2 : aw ≠ ao := fun h => hw_ne_other (by rw [← haw_col, ← hao_col, h])
      rcases lt_or_gt_of_ne h2 with h2' | h2'
      · exact (ray_ties_zeros_disjoint P hgp).2.2.2 t ht0 ht3 ai aj aw ao h1 h2'
          (fun hp => hwi (by
            have := congrArg (fun p : Fin 10 × Fin 10 => vecColor p.1) hp
            dsimp at this; rw [hai_col, haw_col] at this; exact this.symm))
          ⟨hai_dot.trans (heq_ij.trans haj_dot.symm), haw_dot.trans (hother_eq.symm.trans hao_dot.symm)⟩
      · exact (ray_ties_zeros_disjoint P hgp).2.2.2 t ht0 ht3 ai aj ao aw h1 h2'
          (fun hp => hwj (by
            have := congrArg (fun p : Fin 10 × Fin 10 => vecColor p.2) hp
            dsimp at this; rw [haj_col, haw_col] at this; exact this.symm))
          ⟨hai_dot.trans (heq_ij.trans haj_dot.symm), hao_dot.trans (hother_eq.trans haw_dot.symm)⟩
    have hs1 := hpair_eq a₁ b₁ hab1 (by linarith) (ha1.trans hb1.symm)
    have hs2 := hpair_eq a₂ b₂ hab2 (by linarith) (ha2.trans hb2.symm)
    have hv12 : sortedG P ⟨q₁, by omega⟩ t = sortedG P ⟨q₂, by omega⟩ t := by
      have ha1_eq : a₁ = i ∨ a₁ = j := by
        have : a₁ ∈ ({i, j} : Finset (Fin 5)) := by rw [← hs1]; simp
        simpa using this
      have ha2_eq : a₂ = i ∨ a₂ = j := by
        have : a₂ ∈ ({i, j} : Finset (Fin 5)) := by rw [← hs2]; simp
        simpa using this
      rcases ha1_eq with rfl | rfl <;> rcases ha2_eq with rfl | rfl
      · exact ha1.symm.trans ha2
      · exact ha1.symm.trans (heq_ij.trans ha2)
      · exact ha1.symm.trans (heq_ij.symm.trans ha2)
      · exact ha1.symm.trans ha2
    have hq1_le : sortedG P ⟨q₁, by omega⟩ t ≤ sortedG P ⟨q₂ - 1, by omega⟩ t :=
      sortedG_mono P (Fin.mk_le_mk.mpr (by omega)) t
    have hval_eq : sortedG P ⟨q₁ - 1, by omega⟩ t = sortedG P ⟨q₁, by omega⟩ t ∧
        sortedG P ⟨q₁, by omega⟩ t = sortedG P ⟨q₂ - 1, by omega⟩ t ∧
        sortedG P ⟨q₂ - 1, by omega⟩ t = sortedG P ⟨q₂, by omega⟩ t :=
      ⟨heq1, le_antisymm hq1_le (by rw [heq2, ← hv12]), heq2⟩
    let l := (List.ofFn (fun m : Fin 5 => clippedG P m t)).mergeSort (· ≤ ·)
    have hlen : l.length = 5 := by simp [l]
    have hperm : l.Perm (List.ofFn (fun m : Fin 5 => clippedG P m t)) := List.mergeSort_perm _ _
    let v := sortedG P ⟨q₁, by omega⟩ t
    have hv_k1 : l[q₁ - 1]'(by rw [hlen]; omega) = v := by
      dsimp only [v]; rw [← heq1]; exact (sortedG_getElem P ⟨q₁ - 1, by omega⟩ t).symm
    have hv_k2 : l[q₁]'(by rw [hlen]; omega) = v :=
      (sortedG_getElem P ⟨q₁, by omega⟩ t).symm
    have hv_k3 : l[q₂]'(by rw [hlen]; omega) = v := by
      dsimp only [v]; rw [hv12]; exact (sortedG_getElem P ⟨q₂, by omega⟩ t).symm
    have hcount_ge3 : 3 ≤ (Finset.univ.filter (fun m : Fin 5 => clippedG P m t = v)).card := by
      have heq_l : l = List.ofFn (fun k : Fin 5 => l[k.val]'(by rw [hlen]; exact k.isLt)) := by
        refine List.ext_getElem (by rw [List.length_ofFn]; exact hlen) fun n hn1 hn2 => ?_
        rw [List.getElem_ofFn]
      have hlen_f := list_ofFn_filter_len (fun m : Fin 5 => clippedG P m t) (· == v)
      have hlen_l := list_ofFn_filter_len (fun k : Fin 5 => l[k.val]'(by rw [hlen]; exact k.isLt)) (· == v)
      simp only [beq_iff_eq] at hlen_f hlen_l
      rw [← hlen_f, ← List.count_eq_length_filter, ← hperm.count_eq, List.count_eq_length_filter,
        heq_l, hlen_l]
      have hsub : ({⟨q₁ - 1, by omega⟩, ⟨q₁, by omega⟩, ⟨q₂, by omega⟩} : Finset (Fin 5)) ⊆
          Finset.univ.filter (fun k : Fin 5 => l[k.val]'(by rw [hlen]; exact k.isLt) = v) := by
        intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl <;> exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
          first | exact hv_k1 | exact hv_k2 | exact hv_k3⟩
      have h3 : ({⟨q₁ - 1, by omega⟩, ⟨q₁, by omega⟩, ⟨q₂, by omega⟩} : Finset (Fin 5)).card = 3 := by
        rw [Finset.card_insert_of_notMem, Finset.card_pair]
        · intro h; have := congrArg Fin.val h; dsimp at this; omega
        · simp only [Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff]; omega
      rw [← h3]
      exact Finset.card_le_card hsub
    have hsub_ij : Finset.univ.filter (fun m : Fin 5 => clippedG P m t = v) ⊆ {i, j} := by
      intro m hm
      have hm_eq : clippedG P m t = v := (Finset.mem_filter.mp hm).2
      have hv_sup : supportF P a₁ t = v := ha1
      have ha1_in : a₁ = i ∨ a₁ = j := by
        simpa using (by rw [← hs1]; simp : a₁ ∈ ({i, j} : Finset (Fin 5)))
      have hi_v : clippedG P i t = v := by
        have hsup_i : supportF P i t = v := by
          rcases ha1_in with rfl | rfl
          · exact hv_sup
          · exact heq_ij.trans hv_sup
        unfold clippedG; rw [hsup_i, max_eq_left (le_of_lt hpos1)]
      have hj_v : clippedG P j t = v := by
        have hsup_j : supportF P j t = v := by
          rcases ha1_in with rfl | rfl
          · exact heq_ij.symm.trans hv_sup
          · exact hv_sup
        unfold clippedG; rw [hsup_j, max_eq_left (le_of_lt hpos1)]
      have hmi_or : m = i ∨ m = j := by
        by_contra hno; push Not at hno
        obtain ⟨am, ham_col, ham_dot⟩ := supportF_tie_at_vec P m t
        obtain ⟨ai, hai_col, hai_dot⟩ := supportF_tie_at_vec P i t
        obtain ⟨aj, haj_col, haj_dot⟩ := supportF_tie_at_vec P j t
        have hsup_m : supportF P m t = supportF P i t := by
          have := hm_eq.trans hi_v.symm
          unfold clippedG at this
          have hm_pos : 0 < supportF P m t := by
            by_contra hle; rw [max_eq_right (not_lt.mp hle)] at this; exact hpos1.ne (this.trans hi_v)
          have hi_pos : 0 < supportF P i t := by
            by_contra hle; unfold clippedG at hi_v; rw [max_eq_right (not_lt.mp hle)] at hi_v
            dsimp only [v] at hi_v; exact hpos1.ne hi_v
          rw [max_eq_left (le_of_lt hm_pos), max_eq_left (le_of_lt hi_pos)] at this
          exact this
        have h1 : ai < aj := by
          have := congrArg Fin.val hai_col; have := congrArg Fin.val haj_col
          dsimp [vecColor] at *; change i.val < j.val at hij; change ai.val < aj.val; omega
        have h2 : ai ≠ am := fun h => hno.1 (by rw [← hai_col, ← ham_col, h])
        rcases lt_or_gt_of_ne h2 with h2' | h2'
        · exact (ray_ties_zeros_disjoint P hgp).2.2.2 t ht0 ht3 ai aj ai am h1 h2'
            (fun hp => hno.2 (by
              have := congrArg (fun p : Fin 10 × Fin 10 => vecColor p.2) hp
              dsimp at this; rw [haj_col, ham_col] at this; exact this.symm))
            ⟨hai_dot.trans (heq_ij.trans haj_dot.symm), hai_dot.trans (hsup_m.symm.trans ham_dot.symm)⟩
        · exact (ray_ties_zeros_disjoint P hgp).2.2.2 t ht0 ht3 ai aj am ai h1 h2'
            (fun hp => hno.1 (by
              have := congrArg (fun p : Fin 10 × Fin 10 => vecColor p.1) hp
              dsimp at this; rw [hai_col, ham_col] at this; exact this.symm))
            ⟨hai_dot.trans (heq_ij.trans haj_dot.symm), ham_dot.trans (hsup_m.trans hai_dot.symm)⟩
      rcases hmi_or with rfl | rfl <;> simp
    have := (Finset.card_le_card hsub_ij).trans (Finset.card_pair hij.ne).le
    omega
  rw [hall_in, Finset.card_union_of_disjoint, Finset.card_union_of_disjoint, Finset.card_union_of_disjoint]
  · exact hdisj 1 2 (by norm_num) (by norm_num) (by norm_num)
  · exact Finset.disjoint_union_left.mpr ⟨hdisj 1 3 (by norm_num) (by norm_num) (by norm_num),
      hdisj 2 3 (by norm_num) (by norm_num) (by norm_num)⟩
  · exact Finset.disjoint_union_left.mpr ⟨Finset.disjoint_union_left.mpr
      ⟨hdisj 1 4 (by norm_num) (by norm_num) (by norm_num),
       hdisj 2 4 (by norm_num) (by norm_num) (by norm_num)⟩,
      hdisj 3 4 (by norm_num) (by norm_num) (by norm_num)⟩

private lemma clippedG_mem_sortedG (P : DualConfig) (i : Fin 5) (t : ℝ) :
    ∃ k : Fin 5, clippedG P i t = sortedG P k t := by
  let l := (List.ofFn (fun j : Fin 5 => clippedG P j t)).mergeSort (· ≤ ·)
  have hlen : l.length = 5 := by simp [l]
  have hperm : l.Perm (List.ofFn (fun j : Fin 5 => clippedG P j t)) := List.mergeSort_perm _ _
  have hmem : clippedG P i t ∈ l := hperm.mem_iff.mpr (List.mem_ofFn.mpr ⟨i, rfl⟩)
  obtain ⟨k, hk, hkeq⟩ := List.mem_iff_getElem.mp hmem
  exact ⟨⟨k, by rw [← hlen]; exact hk⟩, by rw [sortedG_getElem]; exact hkeq.symm⟩

private lemma rankInterval_mem_iff_pts {a b : ℝ} (hab : a < b) (S : Finset ℝ)
    (hS : ∀ x ∈ S, a < x ∧ x < b) (t : ℝ) (ht : a < t ∧ t < b) (ht_not : t ∉ S) :
    let pts := [a] ++ S.sort (· ≤ ·) ++ [b]
    ∃ ℓ : Fin (S.card + 1),
      pts[ℓ.val]'(by simp [pts, Finset.length_sort]) < t ∧
      t < pts[ℓ.val + 1]'(by simp [pts, Finset.length_sort]; omega) := by
  intro pts
  have hs_pw : (S.sort (· ≤ ·)).Pairwise (· < ·) := S.sortedLT_sort.pairwise
  have hpts_pw : pts.Pairwise (· < ·) := by
    dsimp [pts]
    rw [List.pairwise_cons]
    refine ⟨fun x hx => ?_, ?_⟩
    · simp only [List.mem_append, List.mem_singleton, Finset.mem_sort] at hx
      rcases hx with hx | rfl
      · exact (hS x hx).1
      · exact hab
    · rw [List.pairwise_append]
      refine ⟨hs_pw, List.pairwise_singleton _ _, fun x hx y hy => ?_⟩
      rw [List.mem_singleton] at hy; subst hy
      exact (hS x ((Finset.mem_sort _).mp hx)).2
  have hlen : pts.length = S.card + 2 := by simp [pts, Finset.length_sort]
  let idxSet : Finset (Fin (S.card + 1)) :=
    Finset.univ.filter fun ℓ : Fin (S.card + 1) => pts[ℓ.val]'(by rw [hlen]; omega) < t
  have h0 : pts[0]'(by rw [hlen]; omega) = a := by simp [pts]
  have hL : pts[S.card + 1]'(by rw [hlen]; omega) = b := by
    dsimp [pts]; simp [List.getElem_append_right, Finset.length_sort]
  have hne : idxSet.Nonempty := ⟨⟨0, by omega⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [h0]; exact ht.1⟩⟩
  let ℓ := idxSet.max' hne
  have hℓ_lt : pts[ℓ.val]'(by rw [hlen]; omega) < t := (Finset.mem_filter.mp (Finset.max'_mem idxSet hne)).2
  have hℓ1_ge : t ≤ pts[ℓ.val + 1]'(by rw [hlen]; omega) := by
    by_cases hlast : ℓ.val + 1 = S.card + 1
    · have : pts[ℓ.val + 1]'(by rw [hlen]; omega) = b := by simpa [hlast] using hL
      linarith
    · let ℓ' : Fin (S.card + 1) := ⟨ℓ.val + 1, by omega⟩
      have hnot : ℓ' ∉ idxSet := by
        intro hm
        have hle := Finset.le_max' idxSet ℓ' hm
        change ℓ.val + 1 ≤ ℓ.val at hle; omega
      rw [Finset.mem_filter] at hnot
      exact not_lt.mp fun hlt => hnot ⟨Finset.mem_univ _, hlt⟩
  have hℓ1_ne : t ≠ pts[ℓ.val + 1]'(by rw [hlen]; omega) := by
    intro heq
    have hmem : t ∈ pts := by rw [heq]; exact List.getElem_mem _
    dsimp [pts] at hmem
    simp only [List.mem_cons, List.mem_append, List.mem_singleton, List.mem_nil_iff,
      or_false, Finset.mem_sort] at hmem
    rcases hmem with rfl | (hm | rfl)
    · exact ht.1.ne rfl
    · exact ht_not hm
    · exact ht.2.ne rfl
  exact ⟨ℓ, hℓ_lt, lt_of_le_of_ne hℓ1_ge hℓ1_ne⟩

private lemma list_getElem_eq_of_idx_sw {α : Type*} (xs : List α) {i j : ℕ} (hi : i < xs.length)
    (hj : j < xs.length) (hij : i = j) : xs[j]'hj = xs[i]'hi := by
  subst hij; rfl

/-- Surjection of `1`D slice intervals onto realized masks of weight `q ∈ {1, 2, 3}`,
forcing `Δ_q ≥ 0`. -/
theorem slice_surj_masks (P : DualConfig) (hgp : IsGenPos P)
    (htop : ∀ {t : ℝ}, 0 ≤ t → t ≤ 3 → 0 < topEnv P t)
    (h_shat : ∀ m : Fin 5 → Bool, ∃ z : ℝ × ℝ, InOmega z ∧ RealizesDualMask P m z)
    {q : ℕ} (hq1 : 1 ≤ q) (hq3 : q ≤ 3) :
    0 ≤ sliceExcess P q := by
  have hq4 : q ≤ 4 := by omega
  have hq5 : q < 5 := by omega
  obtain ⟨hab, hIoo⟩ := rankInterval_eq_Ioo P hgp htop h_shat hq1 hq4
  let a := sInf (rankInterval P q)
  let b := sSup (rankInterval P q)
  have hS_in : ∀ x ∈ rankTieSet P q, a < x ∧ x < b := by
    intro x hx
    unfold rankTieSet at hx
    rw [Finset.mem_filter, dif_pos ⟨by omega, hq5⟩] at hx
    have hall := hx.1
    simp only [allPosTieSet, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and] at hall
    obtain ⟨_, _, ht_mem⟩ := hall
    simp only [posPairTies, Finset.mem_filter] at ht_mem
    have hmem_rank : x ∈ rankInterval P q := by
      unfold rankInterval; rw [dif_pos hq5]
      exact ⟨ht_mem.2.1, ht_mem.2.2.1, hx.2.1⟩
    rw [hIoo] at hmem_rank
    exact hmem_rank
  let pts := [a] ++ (rankTieSet P q).sort (· ≤ ·) ++ [b]
  have hpts_len : pts.length = (rankTieSet P q).card + 2 := by
    simp [pts, Finset.length_sort]
  have hpts_pw : pts.Pairwise (· < ·) := by
    dsimp [pts]
    rw [List.pairwise_cons]
    refine ⟨fun x hx => ?_, ?_⟩
    · simp only [List.mem_append, List.mem_singleton, Finset.mem_sort] at hx
      rcases hx with hx | rfl
      · exact (hS_in x hx).1
      · exact hab
    · rw [List.pairwise_append]
      refine ⟨(rankTieSet P q).sortedLT_sort.pairwise, List.pairwise_singleton _ _, fun x hx y hy => ?_⟩
      rw [List.mem_singleton] at hy; subst hy
      exact (hS_in x ((Finset.mem_sort _).mp hx)).2
  have h0_eq : pts[0]'(by rw [hpts_len]; omega) = a := by simp [pts]
  have hL_eq : pts[(rankTieSet P q).card + 1]'(by rw [hpts_len]; omega) = b := by
    simp only [pts, List.singleton_append, List.cons_append, List.getElem_cons_succ]
    rw [List.getElem_append_right (by simp [Finset.length_sort])]
    simp [Finset.length_sort]
  let masks : Finset (Finset (Fin 5)) := Finset.univ.powersetCard q
  have hmasks_card : masks.card = Nat.choose 5 q := by
    simp [masks, Finset.card_powersetCard, Fintype.card_fin]
  have hwit : ∀ M : Finset (Fin 5), M ∈ masks →
      ∃ t : ℝ, a < t ∧ t < b ∧ t ∉ rankTieSet P q ∧
        sortedG P ⟨q - 1, by omega⟩ t < sortedG P ⟨q, hq5⟩ t ∧
        (∀ i : Fin 5, i ∈ M ↔ clippedG P i t ≤ sortedG P ⟨q - 1, by omega⟩ t) ∧
        (∀ i : Fin 5, i ∉ M ↔ sortedG P ⟨q, hq5⟩ t ≤ clippedG P i t) := by
    intro M hM
    have hM_card : M.card = q := (Finset.mem_powersetCard.mp hM).2
    obtain ⟨z, hz_om, hz_mask⟩ := h_shat (fun i => decide (i ∈ M))
    have hnorm := inOmega_norm_pos hz_om
    have hrec := gamma_rayParam_smul hz_om
    have htz := rayParam_mem_Ioo hz_om
    let t := rayParam z
    let ρ := 1 / (|z.1| + |z.2|)
    have hρ_pos : 0 < ρ := div_pos one_pos hnorm
    have hM_lt : ∀ i ∈ M, clippedG P i t < ρ := by
      intro i hiM
      have hmi := hz_mask i
      simp only [hiM, decide_true, ↓reduceIte, DualConfig.MemOpen] at hmi
      unfold clippedG supportF
      rw [max_lt_iff, max_lt_iff]
      refine ⟨⟨?_, ?_⟩, hρ_pos⟩
      · have h1 := hmi.1; rw [← hrec, dot2_smul_right] at h1
        exact (lt_div_iff₀' hnorm).mpr h1
      · have h2 := hmi.2; rw [← hrec, dot2_smul_right] at h2
        exact (lt_div_iff₀' hnorm).mpr h2
    have hMc_gt : ∀ j ∉ M, ρ < clippedG P j t := by
      intro j hjM
      have hmj := hz_mask j
      simp only [hjM, decide_false, Bool.false_eq_true, ↓reduceIte, DualConfig.MemExt] at hmj
      refine lt_of_lt_of_le ?_ (le_max_left _ _)
      unfold supportF
      rw [lt_max_iff]
      rcases hmj with h1 | h2
      · left; rw [← hrec, dot2_smul_right] at h1; exact (div_lt_iff₀' hnorm).mpr h1
      · right; rw [← hrec, dot2_smul_right] at h2; exact (div_lt_iff₀' hnorm).mpr h2
    have hqm1_lt : sortedG P ⟨q - 1, by omega⟩ t < ρ := by
      rw [sortedG_lt_iff]
      dsimp
      have hsub : M ⊆ Finset.univ.filter (fun i : Fin 5 => clippedG P i t < ρ) :=
        fun i hi => Finset.mem_filter.mpr ⟨Finset.mem_univ _, hM_lt i hi⟩
      have := Finset.card_le_card hsub
      omega
    have hq_gt : ρ < sortedG P ⟨q, hq5⟩ t := by
      rw [sortedG_gt_iff]
      dsimp
      have hsub : (Finset.univ \ M) ⊆ Finset.univ.filter (fun j : Fin 5 => ρ < clippedG P j t) :=
        fun j hj => Finset.mem_filter.mpr ⟨Finset.mem_univ _, hMc_gt j (Finset.mem_sdiff.mp hj).2⟩
      have hcard_c : (Finset.univ \ M).card = 5 - q := by
        rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin, hM_card]
      rw [← hcard_c]
      exact Finset.card_le_card hsub
    have ht_rank : t ∈ rankInterval P q := by
      unfold rankInterval; rw [dif_pos hq5]
      exact ⟨htz.1, htz.2, lt_trans hρ_pos hq_gt⟩
    rw [hIoo] at ht_rank
    have ht_not : t ∉ rankTieSet P q := by
      intro hmem
      unfold rankTieSet at hmem
      rw [Finset.mem_filter, dif_pos ⟨by omega, hq5⟩] at hmem
      linarith [hmem.2.2]
    refine ⟨t, ht_rank.1, ht_rank.2, ht_not, lt_trans hqm1_lt hq_gt, ?_, ?_⟩
    · intro i
      constructor
      · intro hiM
        obtain ⟨k, hk⟩ := clippedG_mem_sortedG P i t
        have hk_lt : k.val < q := by
          by_contra hge
          replace hge : q ≤ k.val := not_lt.mp hge
          have hle := sortedG_mono P (Fin.mk_le_mk.mpr hge : (⟨q, hq5⟩ : Fin 5) ≤ k) t
          linarith [hM_lt i hiM]
        rw [hk]
        exact sortedG_mono P (Fin.mk_le_mk.mpr (by omega) : k ≤ ⟨q - 1, by omega⟩) t
      · intro hle
        by_contra hiM
        linarith [hMc_gt i hiM]
    · intro i
      constructor
      · intro hiM
        obtain ⟨k, hk⟩ := clippedG_mem_sortedG P i t
        have hk_ge : q ≤ k.val := by
          by_contra hlt
          have hk_le : k.val ≤ q - 1 := by omega
          have hle := sortedG_mono P (Fin.mk_le_mk.mpr hk_le : k ≤ ⟨q - 1, by omega⟩) t
          linarith [hMc_gt i hiM]
        rw [hk]
        exact sortedG_mono P (Fin.mk_le_mk.mpr hk_ge : (⟨q, hq5⟩ : Fin 5) ≤ k) t
      · intro hle
        intro hiM
        linarith [hM_lt i hiM]
  let witT : Finset (Fin 5) → ℝ := fun M =>
    if hM : M ∈ masks then Classical.choose (hwit M hM) else 0
  let sliceIdx : Finset (Fin 5) → Fin ((rankTieSet P q).card + 1) := fun M =>
    if hM : M ∈ masks then
      have hs := Classical.choose_spec (hwit M hM)
      Classical.choose (rankInterval_mem_iff_pts hab (rankTieSet P q) hS_in
        (witT M) (by dsimp [witT]; rw [dif_pos hM]; exact ⟨hs.1, hs.2.1⟩)
        (by dsimp [witT]; rw [dif_pos hM]; exact hs.2.2.1))
    else ⟨0, by omega⟩
  have hwit_spec : ∀ M (hM : M ∈ masks),
      a < witT M ∧ witT M < b ∧ witT M ∉ rankTieSet P q ∧
      sortedG P ⟨q - 1, by omega⟩ (witT M) < sortedG P ⟨q, hq5⟩ (witT M) ∧
      (∀ i : Fin 5, i ∈ M ↔ clippedG P i (witT M) ≤ sortedG P ⟨q - 1, by omega⟩ (witT M)) ∧
      (∀ i : Fin 5, i ∉ M ↔ sortedG P ⟨q, hq5⟩ (witT M) ≤ clippedG P i (witT M)) := by
    intro M hM
    dsimp only [witT]
    rw [dif_pos hM]
    exact Classical.choose_spec (hwit M hM)
  have hslice_spec : ∀ M (hM : M ∈ masks),
      pts[(sliceIdx M).val]'(by rw [hpts_len]; omega) < witT M ∧
      witT M < pts[(sliceIdx M).val + 1]'(by rw [hpts_len]; omega) := by
    intro M hM
    dsimp only [sliceIdx]
    split_ifs
    exact Classical.choose_spec (rankInterval_mem_iff_pts hab (rankTieSet P q) hS_in
      (witT M) (by dsimp [witT]; rw [dif_pos hM]; exact ⟨(Classical.choose_spec (hwit M hM)).1, (Classical.choose_spec (hwit M hM)).2.1⟩)
      (by dsimp [witT]; rw [dif_pos hM]; exact (Classical.choose_spec (hwit M hM)).2.2.1))
  have hinj : Set.InjOn sliceIdx (masks : Set (Finset (Fin 5))) := by
    intro M₁ hM1 M₂ hM2 heq
    rw [Finset.mem_coe] at hM1 hM2
    have hspec1 := hwit_spec M₁ hM1
    have hspec2 := hwit_spec M₂ hM2
    let t₁ := witT M₁
    let t₂ := witT M₂
    let ℓ₁ := sliceIdx M₁
    let ℓ₂ := sliceIdx M₂
    have hℓ1_spec := hslice_spec M₁ hM1
    have hℓ2_spec := hslice_spec M₂ hM2
    have hℓ_eq : ℓ₁ = ℓ₂ := heq
    let lo_p := pts[ℓ₁.val]'(by rw [hpts_len]; omega)
    let hi_p := pts[ℓ₁.val + 1]'(by rw [hpts_len]; omega)
    have hlo_eq : pts[ℓ₂.val]'(by rw [hpts_len]; omega) = pts[ℓ₁.val]'(by rw [hpts_len]; omega) :=
      list_getElem_eq_of_idx_sw pts _ _ (congrArg Fin.val hℓ_eq)
    have hhi_eq : pts[ℓ₂.val + 1]'(by rw [hpts_len]; omega) = pts[ℓ₁.val + 1]'(by rw [hpts_len]; omega) :=
      list_getElem_eq_of_idx_sw pts _ _ (congrArg (fun x : Fin ((rankTieSet P q).card + 1) => x.val + 1) hℓ_eq)
    have ht1_in : lo_p < t₁ ∧ t₁ < hi_p := hℓ1_spec
    have ht2_in : lo_p < t₂ ∧ t₂ < hi_p :=
      ⟨by change lo_p < witT M₂; dsimp only [lo_p]; rw [← hlo_eq]; exact hℓ2_spec.1,
       by change witT M₂ < hi_p; dsimp only [hi_p]; rw [← hhi_eq]; exact hℓ2_spec.2⟩
    have hno_tie_sub : ∀ u : ℝ, lo_p < u → u < hi_p →
        sortedG P ⟨q - 1, by omega⟩ u < sortedG P ⟨q, hq5⟩ u := by
      intro u hu1 hu2
      have h0_le : a ≤ lo_p := by
        rw [← h0_eq]
        rcases Nat.eq_zero_or_pos ℓ₁.val with hz | hp
        · simp [lo_p, hz]
        · exact le_of_lt (List.pairwise_iff_getElem.mp hpts_pw 0 ℓ₁.val (by rw [hpts_len]; omega)
            (by rw [hpts_len]; omega) hp)
      have hi_le_b : hi_p ≤ b := by
        rw [← hL_eq]
        by_cases hlast : ℓ₁.val + 1 = (rankTieSet P q).card + 1
        · simp [hi_p, hlast]
        · exact le_of_lt (List.pairwise_iff_getElem.mp hpts_pw (ℓ₁.val + 1) ((rankTieSet P q).card + 1)
            (by rw [hpts_len]; omega) (by rw [hpts_len]; omega) (by omega))
      have hu_rank : u ∈ rankInterval P q := by rw [hIoo]; exact ⟨by linarith, by linarith⟩
      have hu_pos : 0 < sortedG P ⟨q, hq5⟩ u := by
        unfold rankInterval at hu_rank; rw [dif_pos hq5] at hu_rank; exact hu_rank.2.2
      have hu_not_tie : u ∉ rankTieSet P q := by
        intro hmem
        have hmem_s : u ∈ (rankTieSet P q).sort (· ≤ ·) := (Finset.mem_sort _).mpr hmem
        have hmem_pts : u ∈ pts := by
          dsimp [pts]; simp only [List.mem_cons, List.mem_append, List.mem_singleton]
          exact Or.inr (Or.inl hmem_s)
        obtain ⟨k, hk, hkeq⟩ := List.mem_iff_getElem.mp hmem_pts
        rcases lt_or_ge k (ℓ₁.val + 1) with hlt | hge
        · have hle : k ≤ ℓ₁.val := by omega
          have hle_p : pts[k]'hk ≤ lo_p := by
            rcases eq_or_lt_of_le hle with rfl | hk_lt
            · rfl
            · exact le_of_lt (List.pairwise_iff_getElem.mp hpts_pw k ℓ₁.val hk (by rw [hpts_len]; omega) hk_lt)
          rw [hkeq] at hle_p; linarith
        · have hge_p : hi_p ≤ pts[k]'hk := by
            rcases eq_or_lt_of_le hge with rfl | hk_gt
            · rfl
            · exact le_of_lt (List.pairwise_iff_getElem.mp hpts_pw (ℓ₁.val + 1) k (by rw [hpts_len]; omega) hk hk_gt)
          rw [hkeq] at hge_p; linarith
      refine lt_of_le_of_ne (sortedG_mono P (Fin.mk_le_mk.mpr (by omega)) u) fun heq_u => hu_not_tie ?_
      obtain ⟨i, j, hij, hi_eq, hj_eq⟩ := sortedG_tie_exists_distinct P (by dsimp; omega) u hu_pos heq_u
      have hu_ioo : 0 < u ∧ u < 3 := by
        unfold rankInterval at hu_rank; rw [dif_pos hq5] at hu_rank; exact ⟨hu_rank.1, hu_rank.2.1⟩
      obtain ⟨ai, hai_col, hai_dot⟩ := supportF_tie_at_vec P i u
      obtain ⟨aj, haj_col, haj_dot⟩ := supportF_tie_at_vec P j u
      have haij : ai ≠ aj := fun h => hij (by rw [← hai_col, ← haj_col, h])
      have hgrid := ray_tie_in_candTieGrid_sweep P hgp hu_ioo.1 hu_ioo.2 haij
        (hai_dot.trans (hi_eq.trans (hj_eq.symm.trans haj_dot.symm)))
      have hmem_ij : u ∈ posPairTies P i j := Finset.mem_filter.mpr ⟨hgrid, hu_ioo.1, hu_ioo.2,
        hi_eq.trans hj_eq.symm, by rw [hi_eq]; exact hu_pos⟩
      have hmem_all : u ∈ allPosTieSet P := by
        unfold allPosTieSet
        rw [Finset.mem_biUnion]
        rcases lt_or_gt_of_ne hij with h | h
        · exact ⟨(i, j), Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩, hmem_ij⟩
        · exact ⟨(j, i), Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩, posPairTies_comm_sweep P i j ▸ hmem_ij⟩
      unfold rankTieSet
      rw [Finset.mem_filter, dif_pos ⟨by omega, hq5⟩]
      exact ⟨hmem_all, hu_pos, heq_u⟩
    ext i
    let g : ℝ → ℝ := fun u => clippedG P i u - (sortedG P ⟨q - 1, by omega⟩ u + sortedG P ⟨q, hq5⟩ u) / 2
    have hg_cont : Continuous g :=
      ((supportF_continuous P i).max continuous_const).sub
        (((sortedG_continuous P ⟨q - 1, by omega⟩).add (sortedG_continuous P ⟨q, hq5⟩)).div_const 2)
    have hg_nz : ∀ u : ℝ, lo_p < u → u < hi_p → g u ≠ 0 := by
      intro u hu1 hu2 hg0
      have hlt_mid := hno_tie_sub u hu1 hu2
      have heq_mid : clippedG P i u = (sortedG P ⟨q - 1, by omega⟩ u + sortedG P ⟨q, hq5⟩ u) / 2 :=
        sub_eq_zero.mp hg0
      obtain ⟨k, hk⟩ := clippedG_mem_sortedG P i u
      rw [hk] at heq_mid
      rcases lt_or_ge k.val q with hk_lt | hk_ge
      · have := sortedG_mono P (Fin.mk_le_mk.mpr (by omega) : k ≤ ⟨q - 1, by omega⟩) u
        linarith
      · have := sortedG_mono P (Fin.mk_le_mk.mpr hk_ge : (⟨q, hq5⟩ : Fin 5) ≤ k) u
        linarith
    have h_no_flip : ∀ a₁ a₂ : ℝ, lo_p < a₁ → a₁ ≤ a₂ → a₂ < hi_p →
        ((g a₁ < 0 ∧ 0 < g a₂) ∨ (0 < g a₁ ∧ g a₂ < 0)) → False := by
      intro a₁ a₂ ha1 ha12 ha2 hpair
      rcases hpair with ⟨hg1, hg2⟩ | ⟨hg1, hg2⟩
      · obtain ⟨s, hs_mem, hs0⟩ :=
          intermediate_value_Icc ha12 hg_cont.continuousOn ⟨le_of_lt hg1, le_of_lt hg2⟩
        exact hg_nz s (lt_of_lt_of_le ha1 hs_mem.1) (lt_of_le_of_lt hs_mem.2 ha2) hs0
      · obtain ⟨s, hs_mem, hs0⟩ :=
          intermediate_value_Icc' ha12 hg_cont.continuousOn ⟨le_of_lt hg2, le_of_lt hg1⟩
        exact hg_nz s (lt_of_lt_of_le ha1 hs_mem.1) (lt_of_le_of_lt hs_mem.2 ha2) hs0
    have hg_sgn : g t₁ < 0 ↔ g t₂ < 0 := by
      constructor
      · intro hg1
        by_contra hge
        have hg2 : 0 < g t₂ := lt_of_le_of_ne (not_lt.mp hge) (hg_nz t₂ ht2_in.1 ht2_in.2).symm
        rcases le_or_gt t₁ t₂ with h12 | h21
        · exact h_no_flip t₁ t₂ ht1_in.1 h12 ht2_in.2 (Or.inl ⟨hg1, hg2⟩)
        · exact h_no_flip t₂ t₁ ht2_in.1 (le_of_lt h21) ht1_in.2 (Or.inr ⟨hg2, hg1⟩)
      · intro hg2
        by_contra hge
        have hg1 : 0 < g t₁ := lt_of_le_of_ne (not_lt.mp hge) (hg_nz t₁ ht1_in.1 ht1_in.2).symm
        rcases le_or_gt t₁ t₂ with h12 | h21
        · exact h_no_flip t₁ t₂ ht1_in.1 h12 ht2_in.2 (Or.inr ⟨hg1, hg2⟩)
        · exact h_no_flip t₂ t₁ ht2_in.1 (le_of_lt h21) ht1_in.2 (Or.inl ⟨hg2, hg1⟩)
    have hM1_iff : i ∈ M₁ ↔ g t₁ < 0 := by
      rw [hspec1.2.2.2.2.1 i]
      have hlt1 := hspec1.2.2.2.1
      constructor
      · intro hle; dsimp [g]; linarith
      · intro hg1
        by_contra hiM
        have hiM' : i ∉ M₁ := by rw [hspec1.2.2.2.2.1 i]; exact hiM
        have hge := (hspec1.2.2.2.2.2 i).mp hiM'
        dsimp [g] at hg1; linarith
    have hM2_iff : i ∈ M₂ ↔ g t₂ < 0 := by
      rw [hspec2.2.2.2.2.1 i]
      have hlt2 := hspec2.2.2.2.1
      constructor
      · intro hle; dsimp [g]; linarith
      · intro hg2
        by_contra hiM
        have hiM' : i ∉ M₂ := by rw [hspec2.2.2.2.2.1 i]; exact hiM
        have hge := (hspec2.2.2.2.2.2 i).mp hiM'
        dsimp [g] at hg2; linarith
    exact hM1_iff.trans (hg_sgn.trans hM2_iff.symm)
  have hle_card : masks.card ≤ (Finset.univ : Finset (Fin ((rankTieSet P q).card + 1))).card :=
    Finset.card_le_card_of_injOn sliceIdx (fun _ _ => Finset.mem_coe.mpr (Finset.mem_univ _)) hinj
  rw [hmasks_card, Finset.card_univ, Fintype.card_fin] at hle_card
  unfold sliceExcess
  omega

private def countTransitions : List (Fin 5) → ℕ
  | [] => 0
  | [_] => 0
  | c₁ :: c₂ :: rest =>
      (if c₁ = c₂ then 0 else 1) + countTransitions (c₂ :: rest)

private lemma one_add_transitions_eq_compressAdj_length
    (l : List (Fin 5)) (hl : l ≠ []) :
    1 + countTransitions l = (compressAdj l).length := by
  induction l with
  | nil => contradiction
  | cons c₁ tail ih =>
    cases tail with
    | nil => rfl
    | cons c₂ rest =>
      have hne : c₂ :: rest ≠ [] := List.cons_ne_nil c₂ rest
      have hih := ih hne
      simp only [countTransitions, compressAdj]
      split_ifs
      · simpa using hih
      · simp only [List.length_cons]
        omega

private lemma countTransitions_ofFn {n : ℕ} (f : Fin (n + 1) → Fin 5) :
    countTransitions (List.ofFn f) =
      (Finset.univ.filter fun k : Fin n => f k.castSucc ≠ f k.succ).card := by
  induction n with
  | zero => simp [countTransitions]
  | succ m ih =>
    rw [List.ofFn_succ]
    have hcons : List.ofFn (fun i : Fin (m + 1) => f i.succ) =
        f ⟨1, by omega⟩ :: List.ofFn (fun i : Fin m => f i.succ.succ) := by
      rw [List.ofFn_succ]; rfl
    have ih' := ih (fun i => f i.succ)
    rw [hcons, countTransitions, ← hcons, ih']
    have hcard_split : (Finset.univ.filter fun k : Fin (m + 1) => f k.castSucc ≠ f k.succ).card =
        (if f 0 = f ⟨1, by omega⟩ then 0 else 1) +
        (Finset.univ.filter fun k : Fin m => f k.succ.castSucc ≠ f k.succ.succ).card := by
      have hpart : (Finset.univ.filter fun k : Fin (m + 1) => f k.castSucc ≠ f k.succ) =
          (if f 0 = f ⟨1, by omega⟩ then ∅ else {0}) ∪
          ((Finset.univ.filter fun k : Fin m => f k.succ.castSucc ≠ f k.succ.succ).image Fin.succ) := by
        ext k
        simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
        cases k using Fin.cases with
        | zero =>
          split_ifs with h0
          · simp [h0]
          · simpa using h0
        | succ k' =>
          split_ifs with h0
          · simp only [Finset.notMem_empty, false_or]
            exact ⟨fun hk => ⟨k', hk, rfl⟩, fun ⟨j, hj, hjk⟩ => by cases Fin.succ_injective _ hjk; exact hj⟩
          · simp only [Finset.mem_singleton, Fin.succ_ne_zero, false_or]
            exact ⟨fun hk => ⟨k', hk, rfl⟩, fun ⟨j, hj, hjk⟩ => by cases Fin.succ_injective _ hjk; exact hj⟩
      rw [hpart, Finset.card_union_of_disjoint, Finset.card_image_of_injective _ (Fin.succ_injective _)]
      · split_ifs <;> simp
      · split_ifs <;> simp [Finset.disjoint_left]
    simpa [Fin.castSucc_succ] using hcard_split.symm

private lemma hullSeamList_pairwise_sw (P : DualConfig) :
    (hullSeamList P).Pairwise (· < ·) := by
  let s : List ℝ := (topTiePts P).sort (· ≤ ·)
  have hs_sorted : s.Pairwise (· < ·) := (topTiePts P).sortedLT_sort.pairwise
  have hs_mem : ∀ x ∈ s, 0 < x ∧ x < 3 := by
    intro x hx
    have hx' : x ∈ topTiePts P := (Finset.mem_sort _).mp hx
    simp only [topTiePts, Finset.mem_filter] at hx'
    exact ⟨hx'.2.1, hx'.2.2.1⟩
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

private lemma hullSeamList_length_sw (P : DualConfig) :
    (hullSeamList P).length = (topTiePts P).card + 2 := by
  unfold hullSeamList; simp [Finset.length_sort]

private lemma hullMidpoint_spec_sw (P : DualConfig) (r : Fin ((topTiePts P).card + 1)) :
    let L := hullSeamList P
    have hr0 : r.val < L.length := by rw [hullSeamList_length_sw]; omega
    have hr1 : r.val + 1 < L.length := by rw [hullSeamList_length_sw]; omega
    L[r.val]'hr0 < hullMidpoint P r ∧ hullMidpoint P r < L[r.val + 1]'hr1 ∧
    0 ≤ L[r.val]'hr0 ∧ L[r.val + 1]'hr1 ≤ 3 ∧
    0 < hullMidpoint P r ∧ hullMidpoint P r < 3 ∧
    (∀ t : ℝ, L[r.val]'hr0 < t → t < L[r.val + 1]'hr1 → t ∉ topTiePts P) := by
  have hpw := hullSeamList_pairwise_sw P
  have hlen := hullSeamList_length_sw P
  have hr0 : r.val < (hullSeamList P).length := by rw [hlen]; omega
  have hr1 : r.val + 1 < (hullSeamList P).length := by rw [hlen]; omega
  have hget0 : (hullSeamList P).getD r.val 0 = (hullSeamList P)[r.val] := by
    simp [List.getD_eq_getElem?_getD, hr0]
  have hget1 : (hullSeamList P).getD (r.val + 1) 3 = (hullSeamList P)[r.val + 1] := by
    simp [List.getD_eq_getElem?_getD, hr1]
  have hlt_adj : (hullSeamList P)[r.val] < (hullSeamList P)[r.val + 1] :=
    List.pairwise_iff_getElem.mp hpw r.val (r.val + 1) hr0 hr1 (by omega)
  have hge0 : 0 ≤ (hullSeamList P)[r.val] := by
    rcases Nat.eq_zero_or_pos r.val with hz | hp
    · have : (hullSeamList P)[r.val] = 0 := by simp [hz, hullSeamList]
      exact ge_of_eq this
    · have h0lt := List.pairwise_iff_getElem.mp hpw 0 r.val (by omega) hr0 hp
      have hz0 : (hullSeamList P)[0]'(by rw [hlen]; omega) = 0 := by simp [hullSeamList]
      exact le_of_lt (hz0 ▸ h0lt)
  have hle3 : (hullSeamList P)[r.val + 1] ≤ 3 := by
    have h3 : (hullSeamList P)[(topTiePts P).card + 1]'(by rw [hlen]; omega) = 3 := by
      unfold hullSeamList; simp [List.getElem_append_right]
    by_cases hlast : r.val + 1 = (topTiePts P).card + 1
    · exact le_of_eq ((show (hullSeamList P)[r.val + 1] =
        (hullSeamList P)[(topTiePts P).card + 1]'(by rw [hlen]; omega) by simp [hlast]).trans h3)
    · have hlt_last := List.pairwise_iff_getElem.mp hpw (r.val + 1) ((topTiePts P).card + 1)
        hr1 (by rw [hlen]; omega) (by omega)
      exact le_of_lt (h3 ▸ hlt_last)
  have hmid : hullMidpoint P r = ((hullSeamList P)[r.val] + (hullSeamList P)[r.val + 1]) / 2 := by
    unfold hullMidpoint; rw [hget0, hget1]
  refine ⟨hmid ▸ left_lt_add_div_two.mpr hlt_adj, hmid ▸ add_div_two_lt_right.mpr hlt_adj,
    hge0, hle3, lt_of_le_of_lt hge0 (hmid ▸ left_lt_add_div_two.mpr hlt_adj),
    lt_of_lt_of_le (hmid ▸ add_div_two_lt_right.mpr hlt_adj) hle3, fun t ht1 ht2 hmem => ?_⟩
  have hmem_seam : t ∈ hullSeamList P := by
    unfold hullSeamList
    simp only [List.mem_append, List.mem_singleton, Finset.mem_sort]
    exact Or.inl (Or.inr hmem)
  obtain ⟨k, hk, hkeq⟩ := List.mem_iff_getElem.mp hmem_seam
  rcases lt_trichotomy k r.val with hkr | rfl | hkr
  · have hlt := List.pairwise_iff_getElem.mp hpw k r.val hk hr0 hkr
    exact lt_asymm ht1 (hkeq ▸ hlt)
  · exact ht1.ne hkeq
  · have hge : r.val + 1 ≤ k := hkr
    rcases eq_or_lt_of_le hge with rfl | hgt
    · exact ht2.ne' hkeq
    · have hlt := List.pairwise_iff_getElem.mp hpw (r.val + 1) k hr1 hk hgt
      exact lt_asymm ht2 (hkeq ▸ hlt)

private lemma exists_vec_eq_topEnv_sw (P : DualConfig) (t : ℝ) :
    ∃ a : Fin 10, dot2 (P.vec a) (gamma t) = topEnv P t := by
  unfold topEnv
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty (fun i : Fin 5 => supportF P i t)
  unfold supportF at hi
  rcases max_choice (dot2 (P.p1 i) (gamma t)) (dot2 (P.p2 i) (gamma t)) with hm | hm
  · exact ⟨⟨2 * i.val, by omega⟩, by rw [P.vec_even i, ← hm]; exact hi.symm⟩
  · exact ⟨⟨2 * i.val + 1, by omega⟩, by rw [P.vec_odd i, ← hm]; exact hi.symm⟩

private lemma dot2_vec_continuous_sw (P : DualConfig) (a : Fin 10) :
    Continuous (fun t : ℝ => dot2 (P.vec a) (gamma t)) := by
  unfold dot2
  exact (continuous_const.mul gamma_continuous.fst).add (continuous_const.mul gamma_continuous.snd)

private lemma hullIdx_dot_eq_topEnv_sw (P : DualConfig) (hgp : IsGenPos P)
    (r : Fin ((topTiePts P).card + 1)) :
    let L := hullSeamList P
    have hr0 : r.val < L.length := by rw [hullSeamList_length_sw]; omega
    have hr1 : r.val + 1 < L.length := by rw [hullSeamList_length_sw]; omega
    ∀ t : ℝ, L[r.val]'hr0 ≤ t → t ≤ L[r.val + 1]'hr1 →
      dot2 (hullVerts P r) (gamma t) = topEnv P t := by
  have hm := hullMidpoint_spec_sw P r
  set L := hullSeamList P
  have hr0 : r.val < L.length := by rw [hullSeamList_length_sw]; omega
  have hr1 : r.val + 1 < L.length := by rw [hullSeamList_length_sw]; omega
  have hex := exists_vec_eq_topEnv_sw P (hullMidpoint P r)
  have hmid_eq : dot2 (hullVerts P r) (gamma (hullMidpoint P r)) = topEnv P (hullMidpoint P r) := by
    unfold hullVerts hullIdx; rw [dif_pos hex]; exact Classical.choose_spec hex
  have hm_not : hullMidpoint P r ∉ topTiePts P := hm.2.2.2.2.2.2 _ hm.1 hm.2.1
  have hstrict : ∀ t : ℝ, L[r.val] < t → t < L[r.val + 1] →
      ∀ b : Fin 10, b ≠ hullIdx P r →
        dot2 (P.vec b) (gamma t) < dot2 (hullVerts P r) (gamma t) := by
    intro t ht_lo ht_hi b hne
    by_contra hge
    replace hge : dot2 (hullVerts P r) (gamma t) ≤ dot2 (P.vec b) (gamma t) := not_lt.mp hge
    let g : ℝ → ℝ := fun u =>
      (Finset.univ.erase (hullIdx P r)).sup'
        ⟨b, Finset.mem_erase.mpr ⟨hne, Finset.mem_univ b⟩⟩
        (fun c : Fin 10 => dot2 (P.vec c) (gamma u)) -
      dot2 (hullVerts P r) (gamma u)
    have hg_cont : Continuous g := by
      refine Continuous.sub ?_ (dot2_vec_continuous_sw P (hullIdx P r))
      exact Continuous.finset_sup'_apply _ fun c _ => dot2_vec_continuous_sw P c
    have hg_mid : g (hullMidpoint P r) < 0 := by
      dsimp [g]
      rw [sub_neg, Finset.sup'_lt_iff]
      intro c hc
      have hc_ne : c ≠ hullIdx P r := (Finset.mem_erase.mp hc).1
      have hle := le_trans (dot2_vec_le_topEnv P c (hullMidpoint P r)) hmid_eq.symm.le
      refine lt_of_le_of_ne hle fun heq => hm_not ?_
      exact (ray_ties_zeros_disjoint P hgp).1 (hullMidpoint P r) |>.mpr
        ⟨hm.2.2.2.2.1, hm.2.2.2.2.2.1, c, hullIdx P r, hc_ne, heq.trans hmid_eq, hmid_eq⟩
    have hg_t : 0 ≤ g t := by
      dsimp [g]
      have hle_sup : dot2 (P.vec b) (gamma t) ≤
          (Finset.univ.erase (hullIdx P r)).sup'
            ⟨b, Finset.mem_erase.mpr ⟨hne, Finset.mem_univ b⟩⟩
            (fun c : Fin 10 => dot2 (P.vec c) (gamma t)) :=
        Finset.le_sup' (fun c : Fin 10 => dot2 (P.vec c) (gamma t))
          (Finset.mem_erase.mpr ⟨hne, Finset.mem_univ b⟩)
      linarith
    rcases le_or_gt t (hullMidpoint P r) with htm | hmt
    · obtain ⟨s, hs_mem, hs0⟩ :=
        intermediate_value_Icc' htm hg_cont.continuousOn ⟨le_of_lt hg_mid, hg_t⟩
      have hs_not := hm.2.2.2.2.2.2 s (lt_of_lt_of_le ht_lo hs_mem.1) (lt_of_le_of_lt hs_mem.2 hm.2.1)
      have hs0' : (Finset.univ.erase (hullIdx P r)).sup' _
          (fun c : Fin 10 => dot2 (P.vec c) (gamma s)) =
          dot2 (hullVerts P r) (gamma s) := sub_eq_zero.mp hs0
      obtain ⟨c, hc_mem, hc_eq⟩ := Finset.exists_mem_eq_sup'
        ⟨b, Finset.mem_erase.mpr ⟨hne, Finset.mem_univ b⟩⟩
        (fun c : Fin 10 => dot2 (P.vec c) (gamma s))
      have hc_ne : c ≠ hullIdx P r := (Finset.mem_erase.mp hc_mem).1
      have htop_s : dot2 (hullVerts P r) (gamma s) = topEnv P s := by
        refine le_antisymm (dot2_vec_le_topEnv P (hullIdx P r) s) ?_
        obtain ⟨d, hd⟩ := exists_vec_eq_topEnv_sw P s
        rw [← hd]
        by_cases hdc : d = hullIdx P r
        · rw [hdc]; rfl
        · rw [← hs0']
          exact Finset.le_sup' (fun c : Fin 10 => dot2 (P.vec c) (gamma s))
            (Finset.mem_erase.mpr ⟨hdc, Finset.mem_univ d⟩)
      exact hs_not ((ray_ties_zeros_disjoint P hgp).1 s |>.mpr
        ⟨lt_of_le_of_lt hm.2.2.1 (lt_of_lt_of_le ht_lo hs_mem.1),
         lt_of_lt_of_le (lt_of_le_of_lt hs_mem.2 hm.2.1) hm.2.2.2.1,
         c, hullIdx P r, hc_ne, hc_eq.symm.trans (hs0'.trans htop_s), htop_s⟩)
    · obtain ⟨s, hs_mem, hs0⟩ :=
        intermediate_value_Icc (le_of_lt hmt) hg_cont.continuousOn ⟨le_of_lt hg_mid, hg_t⟩
      have hs_not := hm.2.2.2.2.2.2 s (lt_of_lt_of_le hm.1 hs_mem.1) (lt_of_le_of_lt hs_mem.2 ht_hi)
      have hs0' : (Finset.univ.erase (hullIdx P r)).sup' _
          (fun c : Fin 10 => dot2 (P.vec c) (gamma s)) =
          dot2 (hullVerts P r) (gamma s) := sub_eq_zero.mp hs0
      obtain ⟨c, hc_mem, hc_eq⟩ := Finset.exists_mem_eq_sup'
        ⟨b, Finset.mem_erase.mpr ⟨hne, Finset.mem_univ b⟩⟩
        (fun c : Fin 10 => dot2 (P.vec c) (gamma s))
      have hc_ne : c ≠ hullIdx P r := (Finset.mem_erase.mp hc_mem).1
      have htop_s : dot2 (hullVerts P r) (gamma s) = topEnv P s := by
        refine le_antisymm (dot2_vec_le_topEnv P (hullIdx P r) s) ?_
        obtain ⟨d, hd⟩ := exists_vec_eq_topEnv_sw P s
        rw [← hd]
        by_cases hdc : d = hullIdx P r
        · rw [hdc]; rfl
        · rw [← hs0']
          exact Finset.le_sup' (fun c : Fin 10 => dot2 (P.vec c) (gamma s))
            (Finset.mem_erase.mpr ⟨hdc, Finset.mem_univ d⟩)
      exact hs_not ((ray_ties_zeros_disjoint P hgp).1 s |>.mpr
        ⟨lt_of_le_of_lt hm.2.2.1 (lt_of_lt_of_le hm.1 hs_mem.1),
         lt_of_lt_of_le (lt_of_le_of_lt hs_mem.2 ht_hi) hm.2.2.2.1,
         c, hullIdx P r, hc_ne, hc_eq.symm.trans (hs0'.trans htop_s), htop_s⟩)
  intro _ _ _ t ht_lo ht_hi
  refine le_antisymm (dot2_vec_le_topEnv P (hullIdx P r) t) ?_
  obtain ⟨b, hb⟩ := exists_vec_eq_topEnv_sw P t
  rw [← hb]
  by_cases hbr : b = hullIdx P r
  · rw [hbr]; rfl
  · by_contra hlt
    replace hlt : dot2 (hullVerts P r) (gamma t) < dot2 (P.vec b) (gamma t) := not_le.mp hlt
    have hopen : IsOpen {u : ℝ | dot2 (hullVerts P r) (gamma u) < dot2 (P.vec b) (gamma u)} :=
      isOpen_lt (dot2_vec_continuous_sw P (hullIdx P r)) (dot2_vec_continuous_sw P b)
    obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hopen t hlt
    rcases eq_or_lt_of_le ht_lo with rfl | ht_lo'
    · let u := min (hullMidpoint P r) (L[r.val] + δ / 2)
      have hu_lo : L[r.val] < u := lt_min hm.1 (by linarith)
      have hu_hi : u < L[r.val + 1] := lt_of_le_of_lt (min_le_left _ _) hm.2.1
      have hu_ball : u ∈ Metric.ball L[r.val] δ := by
        rw [Metric.mem_ball, Real.dist_eq, abs_of_pos (by linarith)]
        have : u ≤ L[r.val] + δ / 2 := min_le_right _ _
        linarith
      have hu_lt := Set.mem_setOf.mp (hball hu_ball)
      linarith [hstrict u hu_lo hu_hi b hbr]
    · rcases eq_or_lt_of_le ht_hi with rfl | ht_hi'
      · let u := max (hullMidpoint P r) (L[r.val + 1] - δ / 2)
        have hu_lo : L[r.val] < u := lt_of_lt_of_le hm.1 (le_max_left _ _)
        have hu_hi : u < L[r.val + 1] := max_lt hm.2.1 (by linarith)
        have hu_ball : u ∈ Metric.ball L[r.val + 1] δ := by
          rw [Metric.mem_ball, Real.dist_eq, abs_of_neg (by linarith)]
          have : L[r.val + 1] - δ / 2 ≤ u := le_max_right _ _
          linarith
        have hu_lt := Set.mem_setOf.mp (hball hu_ball)
        linarith [hstrict u hu_lo hu_hi b hbr]
      · linarith [hstrict t ht_lo' ht_hi' b hbr]

/-- Top-rank seam identity `1 + k_4^+ = n_Ω`. -/
theorem topRank_ties_eq_hullBlocks (P : DualConfig) (hgp : IsGenPos P)
    (htop : ∀ {t : ℝ}, 0 ≤ t → t ≤ 3 → 0 < topEnv P t) :
    1 + (rankTieSet P 4).card = hullBlockCount P := by
  have hne_l : List.ofFn (hullColors P) ≠ [] := by
    rw [List.ofFn_succ]; exact List.cons_ne_nil _ _
  have h1 : 1 + countTransitions (List.ofFn (hullColors P)) = hullBlockCount P :=
    one_add_transitions_eq_compressAdj_length (List.ofFn (hullColors P)) hne_l
  rw [← h1, countTransitions_ofFn]
  congr 1
  let s := (topTiePts P).sort (· ≤ ·)
  have hs_len : s.length = (topTiePts P).card := Finset.length_sort _
  have hs_pw : s.Pairwise (· < ·) := (topTiePts P).sortedLT_sort.pairwise
  let f : Fin (topTiePts P).card → ℝ := fun k => s[k.val]'(by rw [hs_len]; exact k.isLt)
  have hf_inj : Function.Injective f := by
    intro k₁ k₂ heq
    by_contra hne
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hlt | hgt
    · have := List.pairwise_iff_getElem.mp hs_pw k₁.val k₂.val (by rw [hs_len]; exact k₁.isLt)
        (by rw [hs_len]; exact k₂.isLt) hlt
      change f k₁ < f k₂ at this; linarith
    · have := List.pairwise_iff_getElem.mp hs_pw k₂.val k₁.val (by rw [hs_len]; exact k₂.isLt)
        (by rw [hs_len]; exact k₁.isLt) hgt
      change f k₂ < f k₁ at this; linarith
  let transSet := Finset.univ.filter fun k : Fin (topTiePts P).card =>
    hullColors P k.castSucc ≠ hullColors P k.succ
  have himg_eq : transSet.image f = rankTieSet P 4 := by
    ext t
    have hsorted4 : ∀ u : ℝ, 0 < topEnv P u → sortedG P ⟨4, by omega⟩ u = topEnv P u := by
      intro u htop_u
      refine le_antisymm ?_ ?_
      · unfold topEnv
        obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty (fun i : Fin 5 => supportF P i u)
        -- Actually sortedG 4 u is in List.ofFn clippedG, so it equals clippedG i u for some i ≤ max(topEnv, 0) = topEnv
        obtain ⟨j, hj⟩ : ∃ j : Fin 5, sortedG P ⟨4, by omega⟩ u = clippedG P j u := by
          let l := (List.ofFn (fun i : Fin 5 => clippedG P i u)).mergeSort (· ≤ ·)
          have hlen : l.length = 5 := by simp [l]
          have hperm : l.Perm (List.ofFn (fun i : Fin 5 => clippedG P i u)) := List.mergeSort_perm _ _
          have hmem : sortedG P ⟨4, by omega⟩ u ∈ List.ofFn (fun i : Fin 5 => clippedG P i u) := by
            rw [← hperm.mem_iff, sortedG_getElem]
            exact List.getElem_mem _
          obtain ⟨j, hj⟩ := List.mem_ofFn.mp hmem
          exact ⟨j, hj.symm⟩
        rw [hj]
        unfold clippedG
        exact max_le (le_topEnv P j u) (le_of_lt htop_u)
      · unfold topEnv
        refine Finset.sup'_le _ _ fun i _ => ?_
        have hle_sup : supportF P i u ≤ clippedG P i u := le_max_left _ _
        obtain ⟨k, hk⟩ := clippedG_mem_sortedG P i u
        exact hle_sup.trans (hk ▸ sortedG_mono P (Fin.mk_le_mk.mpr (by omega) : k ≤ ⟨4, by omega⟩) u)
    constructor
    · intro ht
      obtain ⟨k, hk_mem, rfl⟩ := Finset.mem_image.mp ht
      have hk_ne : hullColors P k.castSucc ≠ hullColors P k.succ := (Finset.mem_filter.mp hk_mem).2
      have hfk_mem : f k ∈ topTiePts P := (Finset.mem_sort _).mp (List.getElem_mem _)
      have ht_bounds := (ray_ties_zeros_disjoint P hgp).1 (f k) |>.mp hfk_mem
      have hL_eq : (hullSeamList P)[k.val + 1]'(by rw [hullSeamList_length_sw]; omega) = f k := by
        unfold hullSeamList
        have hs_pos : k.val < s.length := by rw [hs_len]; exact k.isLt
        simp [List.getElem_append_left, List.getElem_append_right, hs_pos, f, s]
      have hm1 := hullMidpoint_spec_sw P k.castSucc
      have hm2 := hullMidpoint_spec_sw P k.succ
      have hd1 : dot2 (hullVerts P k.castSucc) (gamma (f k)) = topEnv P (f k) := by
        rw [← hL_eq]
        exact hullIdx_dot_eq_topEnv_sw P hgp k.castSucc _
          (le_of_lt (lt_trans hm1.1 hm1.2.1)) le_rfl
      have hd2 : dot2 (hullVerts P k.succ) (gamma (f k)) = topEnv P (f k) := by
        have hL_eq' : (hullSeamList P)[k.succ.val]'(by rw [hullSeamList_length_sw]; omega) = f k := hL_eq
        rw [← hL_eq']
        exact hullIdx_dot_eq_topEnv_sw P hgp k.succ _
          le_rfl (le_of_lt (lt_trans hm2.1 hm2.2.1))
      have htop_pos : 0 < topEnv P (f k) := htop (le_of_lt ht_bounds.1) (le_of_lt ht_bounds.2.1)
      have hsup1 : supportF P (hullColors P k.castSucc) (f k) = topEnv P (f k) := by
        refine le_antisymm (le_topEnv P _ _) ?_
        rw [← hd1]
        unfold hullVerts hullColors vecColor DualConfig.vec supportF
        split_ifs
        · exact le_max_left _ _
        · exact le_max_right _ _
      have hsup2 : supportF P (hullColors P k.succ) (f k) = topEnv P (f k) := by
        refine le_antisymm (le_topEnv P _ _) ?_
        rw [← hd2]
        unfold hullVerts hullColors vecColor DualConfig.vec supportF
        split_ifs
        · exact le_max_left _ _
        · exact le_max_right _ _
      have hgrid : f k ∈ candTieGrid P := by
        simp only [topTiePts, Finset.mem_filter] at hfk_mem; exact hfk_mem.1
      have hmem_pair : f k ∈ posPairTies P (hullColors P k.castSucc) (hullColors P k.succ) :=
        Finset.mem_filter.mpr ⟨hgrid, ht_bounds.1, ht_bounds.2.1, hsup1.trans hsup2.symm, by rw [hsup1]; exact htop_pos⟩
      have hmem_all : f k ∈ allPosTieSet P := by
        unfold allPosTieSet
        rw [Finset.mem_biUnion]
        rcases lt_or_gt_of_ne hk_ne with h | h
        · exact ⟨(hullColors P k.castSucc, hullColors P k.succ),
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩, hmem_pair⟩
        · exact ⟨(hullColors P k.succ, hullColors P k.castSucc),
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩, posPairTies_comm_sweep P _ _ ▸ hmem_pair⟩
      unfold rankTieSet
      rw [Finset.mem_filter, dif_pos (by omega)]
      refine ⟨hmem_all, by rw [hsorted4 (f k) htop_pos]; exact htop_pos, ?_⟩
      rw [hsorted4 (f k) htop_pos]
      refine le_antisymm (hsorted4 (f k) htop_pos ▸ sortedG_mono P (Fin.mk_le_mk.mpr (by omega) : (⟨3, by omega⟩ : Fin 5) ≤ ⟨4, by omega⟩) (f k)) ?_
      -- Since two distinct colors achieve topEnv P (f k), sortedG 3 = topEnv
      have hsub : ({hullColors P k.castSucc, hullColors P k.succ} : Finset (Fin 5)) ⊆
          Finset.univ.filter (fun i : Fin 5 => topEnv P (f k) ≤ clippedG P i (f k)) := by
        intro c hc
        simp only [Finset.mem_insert, Finset.mem_singleton] at hc
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
        rcases hc with rfl | rfl
        · rw [← hsup1]; exact le_max_left _ _
        · rw [← hsup2]; exact le_max_left _ _
      by_contra hlt3
      replace hlt3 : sortedG P ⟨3, by omega⟩ (f k) < topEnv P (f k) := not_le.mp hlt3
      rw [sortedG_lt_iff] at hlt3
      dsimp at hlt3
      have hdisj_sub : Disjoint ({hullColors P k.castSucc, hullColors P k.succ} : Finset (Fin 5))
          (Finset.univ.filter (fun i : Fin 5 => clippedG P i (f k) < topEnv P (f k))) := by
        rw [Finset.disjoint_left]
        intro c hc1 hc2
        have h1 := (Finset.mem_filter.mp (hsub hc1)).2
        have h2 := (Finset.mem_filter.mp hc2).2
        linarith
      have hcard_un := Finset.card_union_of_disjoint hdisj_sub
      have hle5 : ({hullColors P k.castSucc, hullColors P k.succ} ∪
          Finset.univ.filter (fun i : Fin 5 => clippedG P i (f k) < topEnv P (f k))).card ≤ 5 :=
        (Finset.card_le_univ _).trans (by simp)
      rw [hcard_un, Finset.card_pair hk_ne] at hle5
      omega
    · intro ht
      unfold rankTieSet at ht
      rw [Finset.mem_filter, dif_pos (by omega)] at ht
      have hall := ht.1
      obtain ⟨hpos4, heq34⟩ := ht.2
      have ht_bounds : 0 < t ∧ t < 3 := by
        simp only [allPosTieSet, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and] at hall
        obtain ⟨_, _, hm⟩ := hall
        simp only [posPairTies, Finset.mem_filter] at hm
        exact ⟨hm.2.1, hm.2.2.1⟩
      have htop_pos : 0 < topEnv P t := htop (le_of_lt ht_bounds.1) (le_of_lt ht_bounds.2)
      rw [hsorted4 t htop_pos] at heq34
      obtain ⟨i, j, hij, hi_eq, hj_eq⟩ := sortedG_tie_exists_distinct P (by dsimp; omega) t hpos4 (by rw [hsorted4 t htop_pos]; exact heq34)
      rw [hsorted4 t htop_pos] at hi_eq hj_eq
      obtain ⟨ai, hai_col, hai_dot⟩ := supportF_tie_at_vec P i t
      obtain ⟨aj, haj_col, haj_dot⟩ := supportF_tie_at_vec P j t
      have haij : ai ≠ aj := fun h => hij (by rw [← hai_col, ← haj_col, h])
      have ht_top : t ∈ topTiePts P := (ray_ties_zeros_disjoint P hgp).1 t |>.mpr
        ⟨ht_bounds.1, ht_bounds.2, ai, aj, haij, hai_dot.trans hi_eq, haj_dot.trans hj_eq⟩
      have ht_s : t ∈ s := (Finset.mem_sort _).mpr ht_top
      obtain ⟨k, hk, hkeq⟩ := List.mem_iff_getElem.mp ht_s
      let kf : Fin (topTiePts P).card := ⟨k, by rw [← hs_len]; exact hk⟩
      refine Finset.mem_image.mpr ⟨kf, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, hkeq⟩
      intro hcol_eq
      have hL_eq : (hullSeamList P)[kf.val + 1]'(by rw [hullSeamList_length_sw]; omega) = t := by
        unfold hullSeamList
        have hs_pos : kf.val < s.length := by rw [hs_len]; exact kf.isLt
        simp [List.getElem_append_left, List.getElem_append_right, hs_pos, s]
        exact hkeq
      have hm1 := hullMidpoint_spec_sw P kf.castSucc
      have hm2 := hullMidpoint_spec_sw P kf.succ
      have hd1 : dot2 (hullVerts P kf.castSucc) (gamma t) = topEnv P t := by
        rw [← hL_eq]
        exact hullIdx_dot_eq_topEnv_sw P hgp kf.castSucc _ (le_of_lt (lt_trans hm1.1 hm1.2.1)) le_rfl
      have hd2 : dot2 (hullVerts P kf.succ) (gamma t) = topEnv P t := by
        have hL_eq' : (hullSeamList P)[kf.succ.val]'(by rw [hullSeamList_length_sw]; omega) = t := hL_eq
        rw [← hL_eq']
        exact hullIdx_dot_eq_topEnv_sw P hgp kf.succ _ le_rfl (le_of_lt (lt_trans hm2.1 hm2.2.1))
      have hidx_ne : hullIdx P kf.castSucc ≠ hullIdx P kf.succ :=
        (hullVerts_spec P hgp htop).2.2.1.ne (Fin.ne_of_val_ne (by dsimp [Fin.castSucc, Fin.succ]; omega))
      -- `hullIdx P kf.castSucc` and `hullIdx P kf.succ` both have color `c`, while `ai` and `aj` have distinct colors `i ≠ j`!
      have hc_ne : hullColors P kf.castSucc ≠ i ∨ hullColors P kf.castSucc ≠ j := by
        by_contra hno; push Not at hno; exact hij (hno.1.symm.trans hno.2)
      obtain ⟨d, hd_col, hd_dot⟩ : ∃ d : Fin 10, vecColor d ≠ hullColors P kf.castSucc ∧ dot2 (P.vec d) (gamma t) = topEnv P t := by
        rcases hc_ne with hi_ne | hj_ne
        · exact ⟨ai, by rw [hai_col]; exact hi_ne.symm, hai_dot.trans hi_eq⟩
        · exact ⟨aj, by rw [haj_col]; exact hj_ne.symm, haj_dot.trans hj_eq⟩
      have hd_ne1 : d ≠ hullIdx P kf.castSucc := fun h => hd_col (by rw [h]; rfl)
      have hd_ne2 : d ≠ hullIdx P kf.succ := fun h => hd_col (by rw [h]; exact hcol_eq.symm)
      rcases lt_or_gt_of_ne hidx_ne with h12 | h21 <;> rcases lt_or_gt_of_ne hd_ne1 with hdu | uhd
      · exact (ray_ties_zeros_disjoint P hgp).2.2.2 t ht_bounds.1 ht_bounds.2
          d (hullIdx P kf.castSucc) (hullIdx P kf.castSucc) (hullIdx P kf.succ) hdu h12
          (fun hp => hd_ne1 (congrArg Prod.fst hp)) ⟨hd_dot.trans hd1.symm, hd1.trans hd2.symm⟩
      · exact (ray_ties_zeros_disjoint P hgp).2.2.2 t ht_bounds.1 ht_bounds.2
          (hullIdx P kf.castSucc) d (hullIdx P kf.castSucc) (hullIdx P kf.succ) uhd h12
          (fun hp => hd_ne2 (congrArg Prod.snd hp)) ⟨hd1.trans hd_dot.symm, hd1.trans hd2.symm⟩
      · exact (ray_ties_zeros_disjoint P hgp).2.2.2 t ht_bounds.1 ht_bounds.2
          d (hullIdx P kf.castSucc) (hullIdx P kf.succ) (hullIdx P kf.castSucc) hdu h21
          (fun hp => hd_ne2 (congrArg Prod.fst hp)) ⟨hd_dot.trans hd1.symm, hd2.trans hd1.symm⟩
      · exact (ray_ties_zeros_disjoint P hgp).2.2.2 t ht_bounds.1 ht_bounds.2
          (hullIdx P kf.castSucc) d (hullIdx P kf.succ) (hullIdx P kf.castSucc) uhd h21
          (fun hp => hd_ne1 (congrArg Prod.snd hp)) ⟨hd1.trans hd_dot.symm, hd2.trans hd1.symm⟩
  rw [← himg_eq, Finset.card_image_of_injective _ hf_inj]

/-- Exact `1`D sweep conservation law `n_Ω + T̄_3^+ + T_1^+ + Δ_1 + Δ_2 + Δ_3 = 9`. -/
theorem conservation_law (P : DualConfig) (hgp : IsGenPos P)
    (htop : ∀ {t : ℝ}, 0 ≤ t → t ≤ 3 → 0 < topEnv P t)
    (h_shat : ∀ m : Fin 5 → Bool, ∃ z : ℝ × ℝ, InOmega z ∧ RealizesDualMask P m z) :
    (hullBlockCount P : ℤ) +
      ((crossCountOfMult P 1 + crossCountOfMult P 2 : ℕ) : ℤ) +
      (crossCountOfMult P 1 : ℤ) +
      sliceExcess P 1 + sliceExcess P 2 + sliceExcess P 3 = 9 := by
  have hc := (card_posPairTies_bounds P hgp h_shat).2.2
  have hp := allPosTieSet_partition P hgp
  have ht := topRank_ties_eq_hullBlocks P hgp htop
  unfold sliceExcess
  have c1 : Nat.choose 5 1 = 5 := by decide
  have c2 : Nat.choose 5 2 = 10 := by decide
  have c3 : Nat.choose 5 3 = 10 := by decide
  rw [c1, c2, c3]
  omega

end CaseA
end
