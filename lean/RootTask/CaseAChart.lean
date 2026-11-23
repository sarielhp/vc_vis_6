import Mathlib

noncomputable section

namespace CaseA

/-- Open L-shaped domain `Ω = {p ∈ ℝ² : p.1 < 0 ∨ p.2 < 0}`. -/
def InOmega (p : ℝ × ℝ) : Prop :=
  p.1 < 0 ∨ p.2 < 0

/-- Open third quadrant `Q₃ = (-∞, 0)²`. -/
def InQ3 (p : ℝ × ℝ) : Prop :=
  p.1 < 0 ∧ p.2 < 0

/-- Standard Euclidean dot product on `ℝ × ℝ`. -/
def dot2 (u v : ℝ × ℝ) : ℝ :=
  u.1 * v.1 + u.2 * v.2

/-- Planar `2 × 2` determinant on `ℝ × ℝ`. -/
def det2 (u v : ℝ × ℝ) : ℝ :=
  u.1 * v.2 - u.2 * v.1

/-- Coordinate transposition `(u.1, u.2) ↦ (u.2, u.1)`. -/
def swap2 (u : ℝ × ℝ) : ℝ × ℝ :=
  (u.2, u.1)

/-- Piecewise-linear `ℓ₁`-diamond contour `γ : ℝ → ℝ × ℝ` on `[0, 3]`. -/
def gamma (t : ℝ) : ℝ × ℝ :=
  if t ≤ 1 then (-t, 1 - t)
  else if t ≤ 2 then (t - 2, 1 - t)
  else (t - 2, t - 3)

/-- Explicit rational inverse ray parameter `Ω → (0, 3)` for the `ℓ₁`-diamond chart. -/
def rayParam (z : ℝ × ℝ) : ℝ :=
  if 0 ≤ z.2 then -z.1 / (|z.1| + |z.2|)
  else 2 + z.1 / (|z.1| + |z.2|)

/-- Reciprocal polar map `(t, η) ↦ η⁻¹ • γ(t)`. -/
def polarPhi (t η : ℝ) : ℝ × ℝ :=
  (1 / η) • gamma t

/-- Planar Cramer / Grassmann-Plücker vector identity. -/
theorem cramer_vec (a b c : ℝ × ℝ) :
    det2 a c • b = det2 b c • a + det2 a b • c := by
  ext <;> simp [det2] <;> ring

/-- Scalar dot-product form of the planar Cramer identity. -/
theorem cramer_dot (q a b c : ℝ × ℝ) :
    det2 a c * dot2 q b = det2 b c * dot2 q a + det2 a b * dot2 q c := by
  simp only [dot2, det2]
  ring

/-- Planar Cauchy-Binet identity relating dot products and `2 × 2` determinants. -/
theorem cauchy_binet_two (a b u v : ℝ × ℝ) :
    dot2 a u * dot2 b v - dot2 a v * dot2 b u = det2 a b * det2 u v := by
  simp only [dot2, det2]
  ring

/-- Dot product invariance under coordinate transposition `swap2`. -/
theorem dot2_swap2 (a b : ℝ × ℝ) :
    dot2 (swap2 a) (swap2 b) = dot2 a b := by
  simp only [dot2, swap2]
  ring

/-- Determinant sign reversal under coordinate transposition `swap2`. -/
theorem det2_swap2 (a b : ℝ × ℝ) :
    det2 (swap2 a) (swap2 b) = -det2 a b := by
  simp only [det2, swap2]
  ring

@[simp]
theorem swap2_swap2 (a : ℝ × ℝ) : swap2 (swap2 a) = a := by
  cases a
  rfl

@[simp]
theorem det2_self (a : ℝ × ℝ) : det2 a a = 0 := by
  simp only [det2]
  ring

theorem det2_antisymm (a b : ℝ × ℝ) : det2 a b = -det2 b a := by
  simp only [det2]
  ring

theorem dot2_comm (a b : ℝ × ℝ) : dot2 a b = dot2 b a := by
  simp only [dot2]
  ring

theorem dot2_smul_right (a v : ℝ × ℝ) (r : ℝ) : dot2 a (r • v) = r * dot2 a v := by
  simp only [dot2, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

theorem dot2_smul_left (a v : ℝ × ℝ) (r : ℝ) : dot2 (r • a) v = r * dot2 a v := by
  simp only [dot2, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

theorem det2_smul_left (a b : ℝ × ℝ) (r : ℝ) : det2 (r • a) b = r * det2 a b := by
  simp only [det2, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

theorem det2_smul_right (a b : ℝ × ℝ) (r : ℝ) : det2 a (r • b) = r * det2 a b := by
  simp only [det2, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

@[simp]
theorem gamma_zero : gamma 0 = (0, 1) := by
  norm_num [gamma]

@[simp]
theorem gamma_one : gamma 1 = (-1, 0) := by
  norm_num [gamma]

@[simp]
theorem gamma_two : gamma 2 = (0, -1) := by
  norm_num [gamma]

@[simp]
theorem gamma_three : gamma 3 = (1, 0) := by
  norm_num [gamma]

/-- Continuity of the piecewise-linear diamond contour `γ`. -/
theorem gamma_continuous : Continuous gamma := by
  unfold gamma
  refine Continuous.if_le ?_ ?_ continuous_id continuous_const (by intro x hx; subst hx; norm_num)
  · exact Continuous.prodMk continuous_neg (continuous_const.sub continuous_id)
  · refine Continuous.if_le ?_ ?_ continuous_id continuous_const
      (by intro x hx; subst hx; norm_num)
    · exact Continuous.prodMk (continuous_id.sub continuous_const)
        (continuous_const.sub continuous_id)
    · exact Continuous.prodMk (continuous_id.sub continuous_const)
        (continuous_id.sub continuous_const)

/-- Unit `ℓ₁`-norm of `γ(t)` on `[0, 3]`. -/
theorem gamma_norm_one {t : ℝ} (ht0 : 0 ≤ t) (ht3 : t ≤ 3) :
    |(gamma t).1| + |(gamma t).2| = 1 := by
  unfold gamma
  split_ifs with h1 h2
  · rw [abs_of_nonpos (by linarith), abs_of_nonneg (by linarith)]
    ring
  · rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
    ring
  · rw [abs_of_nonneg (by linarith), abs_of_nonpos (by linarith)]
    ring

theorem gamma_ne_zero {t : ℝ} (ht0 : 0 ≤ t) (ht3 : t ≤ 3) : gamma t ≠ (0, 0) := by
  intro h
  have hn := gamma_norm_one ht0 ht3
  rw [h] at hn
  norm_num at hn

/-- Reflection symmetry `γ(3 - t) = swap2 (γ(t))`. -/
theorem gamma_swap_symm (t : ℝ) : gamma (3 - t) = swap2 (gamma t) := by
  unfold gamma swap2
  split_ifs <;> ext <;> dsimp <;> linarith

theorem gamma_add_two {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    gamma (t + 2) = -gamma t := by
  unfold gamma
  by_cases h : t = 0
  · subst h; norm_num
  · have ht_pos : 0 < t := lt_of_le_of_ne ht0 (Ne.symm h)
    rw [if_neg (by linarith), if_neg (by linarith), if_pos ht1]
    ext <;> dsimp <;> ring

/-- Exact Determinant Sign Law on `[0, 3]`: `det2 (γ t₁) (γ t₂)` has the sign of `2 - (t₂ - t₁)`. -/
theorem gamma_det2_sign {t₁ t₂ : ℝ} (h0 : 0 ≤ t₁) (hlt : t₁ < t₂) (h3 : t₂ ≤ 3) :
    (0 < det2 (gamma t₁) (gamma t₂) ↔ t₂ - t₁ < 2) ∧
    (det2 (gamma t₁) (gamma t₂) = 0 ↔ t₂ - t₁ = 2) ∧
    (det2 (gamma t₁) (gamma t₂) < 0 ↔ 2 < t₂ - t₁) := by
  have hval : (t₂ - t₁ < 2 → 0 < det2 (gamma t₁) (gamma t₂)) ∧
      (t₂ - t₁ = 2 → det2 (gamma t₁) (gamma t₂) = 0) ∧
      (2 < t₂ - t₁ → det2 (gamma t₁) (gamma t₂) < 0) := by
    unfold gamma det2
    split_ifs with ha1 ha2 hb1 hb2 hb2' hc2 hc2'
    · refine ⟨fun _ => by nlinarith, fun h => by linarith, fun h => by linarith⟩
    · refine ⟨fun hlt2 => ?_, fun heq2 => ?_, fun hgt2 => by linarith⟩
      · have hprod1 : 0 ≤ (1 - t₁) * (2 - t₂) := mul_nonneg (by linarith) (by linarith)
        have hprod2 : 0 ≤ t₁ * (t₂ - 1) := mul_nonneg (by linarith) (by linarith)
        by_cases ht1_zero : t₁ = 0
        · subst ht1_zero; nlinarith
        · have ht1_pos : 0 < t₁ := lt_of_le_of_ne h0 (Ne.symm ht1_zero)
          have hstrict : 0 < t₁ * (t₂ - 1) := mul_pos ht1_pos (by linarith)
          nlinarith
      · have ht1_eq : t₁ = 0 := by linarith
        have ht2_eq : t₂ = 2 := by linarith
        subst ht1_eq ht2_eq; ring
    · have hlin : (-t₁) * (t₂ - 3) - (1 - t₁) * (t₂ - 2) = 2 - (t₂ - t₁) := by ring
      dsimp
      rw [hlin]
      exact ⟨fun h => by linarith, fun h => by linarith, fun h => by linarith⟩
    · linarith
    · refine ⟨fun _ => by nlinarith, fun h => by linarith, fun h => by linarith⟩
    · refine ⟨fun hlt2 => ?_, fun heq2 => by linarith, fun hgt2 => by linarith⟩
      have hprod1 : 0 ≤ (2 - t₁) * (3 - t₂) := mul_nonneg (by linarith) (by linarith)
      have hprod2 : 0 < (t₁ - 1) * (t₂ - 2) := mul_pos (by linarith) (by linarith)
      nlinarith
    · linarith
    · linarith
    · refine ⟨fun _ => by nlinarith, fun h => by linarith, fun h => by linarith⟩
  rcases hval with ⟨hpos, hzero, hneg⟩
  refine ⟨⟨fun h => ?_, hpos⟩, ⟨fun h => ?_, hzero⟩, ⟨fun h => ?_, hneg⟩⟩
  · by_contra hge
    rcases lt_or_eq_of_le (not_lt.mp hge) with hgt | heq
    · linarith [hneg hgt]
    · linarith [hzero heq.symm]
  · by_contra hne
    rcases lt_or_gt_of_ne hne with hlt2 | hgt2
    · linarith [hpos hlt2]
    · linarith [hneg hgt2]
  · by_contra hle
    rcases lt_or_eq_of_le (not_lt.mp hle) with hlt2 | heq
    · linarith [hpos hlt2]
    · linarith [hzero heq]

/-- Sub-interval determinant inheritance along `γ`. -/
theorem gamma_det2_subinterval {t₁ s₁ s₂ t₂ : ℝ}
    (ht1 : 0 ≤ t₁) (hs1 : t₁ ≤ s₁) (hlt : s₁ < s₂) (hs2 : s₂ ≤ t₂) (ht2 : t₂ ≤ 3)
    (hdet : 0 < det2 (gamma t₁) (gamma t₂)) :
    0 < det2 (gamma s₁) (gamma s₂) := by
  have hlt_outer : t₁ < t₂ := lt_of_le_of_lt hs1 (lt_of_lt_of_le hlt hs2)
  have hspan : t₂ - t₁ < 2 := (gamma_det2_sign ht1 hlt_outer ht2).1.mp hdet
  exact (gamma_det2_sign (le_trans ht1 hs1) hlt (le_trans hs2 ht2)).1.mpr (by linarith)

theorem gamma_inOmega {t : ℝ} (ht0 : 0 < t) (ht3 : t < 3) : InOmega (gamma t) := by
  unfold gamma InOmega
  split_ifs <;> [left; right; right] <;> dsimp <;> linarith

theorem gamma_inQ3_iff {t : ℝ} :
    InQ3 (gamma t) ↔ 1 < t ∧ t < 2 := by
  unfold gamma InQ3
  split_ifs with h1 h2 <;> dsimp
  · exact ⟨fun ⟨_, h⟩ => by linarith, fun ⟨h, _⟩ => by linarith⟩
  · exact ⟨fun ⟨h, _⟩ => ⟨by linarith, by linarith⟩,
           fun ⟨h, h'⟩ => ⟨by linarith, by linarith⟩⟩
  · exact ⟨fun ⟨h, _⟩ => by linarith, fun ⟨_, h⟩ => by linarith⟩

theorem inOmega_norm_pos {z : ℝ × ℝ} (hz : InOmega z) : 0 < |z.1| + |z.2| := by
  rcases hz with h1 | h2
  · have : 0 < |z.1| := abs_pos.mpr (ne_of_lt h1)
    linarith [abs_nonneg z.2]
  · have : 0 < |z.2| := abs_pos.mpr (ne_of_lt h2)
    linarith [abs_nonneg z.1]

theorem polarPhi_inOmega {t η : ℝ} (ht0 : 0 < t) (ht3 : t < 3) (hη : 0 < η) :
    InOmega (polarPhi t η) := by
  have hpos : 0 < 1 / η := div_pos one_pos hη
  rcases gamma_inOmega ht0 ht3 with h1 | h2
  · left; dsimp [polarPhi]; nlinarith
  · right; dsimp [polarPhi]; nlinarith

theorem polarPhi_norm {t η : ℝ} (ht0 : 0 ≤ t) (ht3 : t ≤ 3) (hη : 0 < η) :
    |(polarPhi t η).1| + |(polarPhi t η).2| = 1 / η := by
  have hpos : 0 ≤ 1 / η := le_of_lt (div_pos one_pos hη)
  dsimp [polarPhi]
  rw [abs_mul, abs_mul, abs_of_nonneg hpos, ← mul_add, gamma_norm_one ht0 ht3, mul_one]

theorem rayParam_polarPhi {t η : ℝ} (ht0 : 0 < t) (ht3 : t < 3) (hη : 0 < η) :
    rayParam (polarPhi t η) = t := by
  have hnorm := polarPhi_norm (le_of_lt ht0) (le_of_lt ht3) hη
  have hinv_pos : 0 < 1 / η := div_pos one_pos hη
  have hinv_ne : 1 / η ≠ 0 := ne_of_gt hinv_pos
  unfold rayParam
  rw [hnorm]
  by_cases ht1 : t ≤ 1
  · have h2 : 0 ≤ (polarPhi t η).2 := by simp [polarPhi, gamma, ht1]; nlinarith [inv_pos.mpr hη]
    rw [if_pos h2]; simp [polarPhi, gamma, ht1]; field_simp [ne_of_gt hη]
  · by_cases ht2 : t ≤ 2
    · have h2 : ¬ 0 ≤ (polarPhi t η).2 := by simp [polarPhi, gamma, ht1, ht2]; nlinarith [inv_pos.mpr hη]
      rw [if_neg h2]; simp [polarPhi, gamma, ht1, ht2]; field_simp [ne_of_gt hη]; ring
    · have h2 : ¬ 0 ≤ (polarPhi t η).2 := by simp [polarPhi, gamma, ht1, ht2]; nlinarith [inv_pos.mpr hη]
      rw [if_neg h2]; simp [polarPhi, gamma, ht1, ht2]; field_simp [ne_of_gt hη]; ring

theorem rayParam_mem_Ioo {z : ℝ × ℝ} (hz : InOmega z) :
    0 < rayParam z ∧ rayParam z < 3 := by
  have hnorm : 0 < |z.1| + |z.2| := inOmega_norm_pos hz
  unfold rayParam
  split_ifs with hz2
  · have hz1 : z.1 < 0 := by
      rcases hz with h | h
      · exact h
      · linarith
    have habs1 : |z.1| = -z.1 := abs_of_neg hz1
    have habs2 : |z.2| = z.2 := abs_of_nonneg hz2
    refine ⟨div_pos (by linarith) hnorm, ?_⟩
    have hle1 : -z.1 / (|z.1| + |z.2|) ≤ 1 := (div_le_one hnorm).mpr (by linarith)
    linarith
  · replace hz2 : z.2 < 0 := not_le.mp hz2
    have habs2 : |z.2| = -z.2 := abs_of_neg hz2
    by_cases hz1 : z.1 ≤ 0
    · have habs1 : |z.1| = -z.1 := abs_of_nonpos hz1
      have hge : -1 < z.1 / (|z.1| + |z.2|) := (lt_div_iff₀ hnorm).mpr (by linarith)
      have hle : z.1 / (|z.1| + |z.2|) ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg hz1 (le_of_lt hnorm)
      exact ⟨by linarith, by linarith⟩
    · replace hz1 : 0 < z.1 := not_le.mp hz1
      have habs1 : |z.1| = z.1 := abs_of_pos hz1
      have hgt : 0 < z.1 / (|z.1| + |z.2|) := div_pos hz1 hnorm
      have hlt1 : z.1 / (|z.1| + |z.2|) < 1 := (div_lt_one hnorm).mpr (by linarith)
      exact ⟨by linarith, by linarith⟩

theorem gamma_rayParam_smul {z : ℝ × ℝ} (hz : InOmega z) :
    (|z.1| + |z.2|) • gamma (rayParam z) = z := by
  have hnorm : 0 < |z.1| + |z.2| := inOmega_norm_pos hz
  have hne : |z.1| + |z.2| ≠ 0 := ne_of_gt hnorm
  unfold rayParam
  split_ifs with hz2
  · have hz1 : z.1 < 0 := by
      rcases hz with h | h
      · exact h
      · linarith
    have habs1 : |z.1| = -z.1 := abs_of_neg hz1
    have habs2 : |z.2| = z.2 := abs_of_nonneg hz2
    have ht_le1 : -z.1 / (|z.1| + |z.2|) ≤ 1 := (div_le_one hnorm).mpr (by linarith)
    unfold gamma
    rw [if_pos ht_le1]
    ext <;> dsimp
    · field_simp [hne]
    · field_simp [hne]; linarith
  · replace hz2 : z.2 < 0 := not_le.mp hz2
    have habs2 : |z.2| = -z.2 := abs_of_neg hz2
    by_cases hz1 : z.1 ≤ 0
    · have habs1 : |z.1| = -z.1 := abs_of_nonpos hz1
      have ht_gt1 : ¬ (2 + z.1 / (|z.1| + |z.2|) ≤ 1) := by
        have : -1 < z.1 / (|z.1| + |z.2|) := (lt_div_iff₀ hnorm).mpr (by linarith)
        linarith
      have ht_le2 : 2 + z.1 / (|z.1| + |z.2|) ≤ 2 := by
        have : z.1 / (|z.1| + |z.2|) ≤ 0 :=
          div_nonpos_of_nonpos_of_nonneg hz1 (le_of_lt hnorm)
        linarith
      unfold gamma
      rw [if_neg ht_gt1, if_pos ht_le2]
      ext <;> dsimp
      · field_simp [hne]; ring
      · field_simp [hne]; linarith
    · replace hz1 : 0 < z.1 := not_le.mp hz1
      have habs1 : |z.1| = z.1 := abs_of_pos hz1
      have hpos_div : 0 < z.1 / (|z.1| + |z.2|) := div_pos hz1 hnorm
      unfold gamma
      rw [if_neg (by linarith), if_neg (by linarith)]
      ext <;> dsimp
      · field_simp [hne]; ring
      · field_simp [hne]; linarith

theorem polarPhi_rayParam {z : ℝ × ℝ} (hz : InOmega z) :
    polarPhi (rayParam z) (1 / (|z.1| + |z.2|)) = z := by
  unfold polarPhi
  rw [one_div_one_div]
  exact gamma_rayParam_smul hz

theorem inQ3_iff_rayParam {z : ℝ × ℝ} (hz : InOmega z) :
    InQ3 z ↔ 1 < rayParam z ∧ rayParam z < 2 := by
  have hnorm : 0 < |z.1| + |z.2| := inOmega_norm_pos hz
  have hrec := gamma_rayParam_smul hz
  have hq3_smul : InQ3 ((|z.1| + |z.2|) • gamma (rayParam z)) ↔ InQ3 (gamma (rayParam z)) := by
    unfold InQ3
    dsimp
    exact ⟨fun ⟨h1, h2⟩ => ⟨by nlinarith, by nlinarith⟩,
           fun ⟨h1, h2⟩ => ⟨by nlinarith, by nlinarith⟩⟩
  conv_lhs => rw [← hrec]
  rw [hq3_smul]
  exact gamma_inQ3_iff

theorem inOmega_swap2 {z : ℝ × ℝ} (hz : InOmega z) : InOmega (swap2 z) := by
  rcases hz with h1 | h2
  · exact Or.inr h1
  · exact Or.inl h2

theorem rayParam_swap2 {z : ℝ × ℝ} (hz : InOmega z) :
    rayParam (swap2 z) = 3 - rayParam z := by
  have hnorm : 0 < |z.1| + |z.2| := inOmega_norm_pos hz
  have hbounds := rayParam_mem_Ioo hz
  have hη : 0 < 1 / (|z.1| + |z.2|) := div_pos one_pos hnorm
  have hswap_eq : swap2 z = polarPhi (3 - rayParam z) (1 / (|z.1| + |z.2|)) := by
    unfold polarPhi
    rw [one_div_one_div, gamma_swap_symm]
    have hrec := gamma_rayParam_smul hz
    conv_lhs => rw [← hrec]
    ext <;> dsimp [swap2]
  rw [hswap_eq]
  exact rayParam_polarPhi (by linarith) (by linarith) hη

/-- Complete polar bijection specification on `Ω` and `Q₃`. -/
theorem polarPhi_spec :
    (∀ {t η : ℝ}, 0 < t → t < 3 → 0 < η →
      InOmega (polarPhi t η) ∧
      |(polarPhi t η).1| + |(polarPhi t η).2| = 1 / η ∧
      rayParam (polarPhi t η) = t) ∧
    (∀ {z : ℝ × ℝ}, InOmega z →
      0 < |z.1| + |z.2| ∧
      0 < rayParam z ∧ rayParam z < 3 ∧
      polarPhi (rayParam z) (1 / (|z.1| + |z.2|)) = z ∧
      (InQ3 z ↔ 1 < rayParam z ∧ rayParam z < 2) ∧
      rayParam (swap2 z) = 3 - rayParam z) := by
  refine ⟨fun ht0 ht3 hη => ⟨polarPhi_inOmega ht0 ht3 hη,
    polarPhi_norm (le_of_lt ht0) (le_of_lt ht3) hη, rayParam_polarPhi ht0 ht3 hη⟩,
    fun hz => ⟨inOmega_norm_pos hz, (rayParam_mem_Ioo hz).1, (rayParam_mem_Ioo hz).2,
      polarPhi_rayParam hz, inQ3_iff_rayParam hz, rayParam_swap2 hz⟩⟩

/-- `Ω`-Positivity Span Bound: if `q` pairs positively with `γ(t₁)` and `γ(t₂)` on `[0, 3]`
and avoids `Q₁`, then `t₂ - t₁ < 2` and `det2 (γ t₁) (γ t₂) > 0`. -/
theorem omega_pos_span {q : ℝ × ℝ} {t₁ t₂ : ℝ}
    (ht1 : 0 ≤ t₁) (hlt : t₁ < t₂) (ht2 : t₂ ≤ 3)
    (hp1 : 0 < dot2 q (gamma t₁)) (hp2 : 0 < dot2 q (gamma t₂))
    (hq : InOmega q ∨ (0 < t₁ ∧ q.1 ≤ 0) ∨ (t₂ < 3 ∧ q.2 ≤ 0)) :
    t₂ - t₁ < 2 ∧ 0 < det2 (gamma t₁) (gamma t₂) := by
  have hlt2 : t₂ - t₁ < 2 := by
    by_contra hge
    replace hge : 2 ≤ t₂ - t₁ := not_lt.mp hge
    have ht1_le1 : t₁ ≤ 1 := by linarith
    have ht2_gt2 : 2 ≤ t₂ := by linarith
    rcases eq_or_lt_of_le hge with heq | hgt
    · have ht2_eq : t₂ = t₁ + 2 := by linarith
      rw [ht2_eq, gamma_add_two ht1 ht1_le1] at hp2
      have hneg : dot2 q (-gamma t₁) = -dot2 q (gamma t₁) := by simp [dot2]; ring
      linarith
    · have hg1 : gamma t₁ = (-t₁, 1 - t₁) := by unfold gamma; rw [if_pos ht1_le1]
      have hg2 : gamma t₂ = (t₂ - 2, t₂ - 3) := by
        unfold gamma; rw [if_neg (by linarith), if_neg (by linarith)]
      rw [hg1] at hp1
      rw [hg2] at hp2
      unfold dot2 at hp1 hp2
      dsimp at hp1 hp2
      have hcomb1 : (t₂ - t₁ - 2) * q.1 =
          (3 - t₂) * (q.1 * -t₁ + q.2 * (1 - t₁)) +
          (1 - t₁) * (q.1 * (t₂ - 2) + q.2 * (t₂ - 3)) := by ring
      have hcomb2 : (t₂ - t₁ - 2) * q.2 =
          (t₂ - 2) * (q.1 * -t₁ + q.2 * (1 - t₁)) +
          t₁ * (q.1 * (t₂ - 2) + q.2 * (t₂ - 3)) := by ring
      have hq1_pos : 0 < q.1 := by
        have h1 : 0 ≤ (3 - t₂) * (q.1 * -t₁ + q.2 * (1 - t₁)) :=
          mul_nonneg (by linarith) (le_of_lt hp1)
        have h2 : 0 < (1 - t₁) * (q.1 * (t₂ - 2) + q.2 * (t₂ - 3)) :=
          mul_pos (by linarith) hp2
        have hprod : 0 < (t₂ - t₁ - 2) * q.1 := by linarith
        exact pos_of_mul_pos_right hprod (by linarith)
      have hq2_pos : 0 < q.2 := by
        have h1 : 0 < (t₂ - 2) * (q.1 * -t₁ + q.2 * (1 - t₁)) :=
          mul_pos (by linarith) hp1
        have h2 : 0 ≤ t₁ * (q.1 * (t₂ - 2) + q.2 * (t₂ - 3)) :=
          mul_nonneg ht1 (le_of_lt hp2)
        have hprod : 0 < (t₂ - t₁ - 2) * q.2 := by linarith
        exact pos_of_mul_pos_right hprod (by linarith)
      rcases hq with (h | h) | ⟨_, h⟩ | ⟨_, h⟩ <;> linarith
  exact ⟨hlt2, (gamma_det2_sign ht1 hlt ht2).1.mpr hlt2⟩

/-- Positive determinant and common positive pairing with `γ(t_*)` force `rayParam a < rayParam b`. -/
theorem rayParam_lt_of_det2_pos_and_pos_dot {a b : ℝ × ℝ} {t₀ : ℝ}
    (ha : InOmega a) (hb : InOmega b) (ht0_lo : 0 ≤ t₀) (ht0_hi : t₀ ≤ 3)
    (hdet : 0 < det2 a b)
    (hpa : 0 < dot2 a (gamma t₀)) (hpb : 0 < dot2 b (gamma t₀)) :
    rayParam a < rayParam b := by
  have hna := inOmega_norm_pos ha
  have hnb := inOmega_norm_pos hb
  have hsa := rayParam_mem_Ioo ha
  have hsb := rayParam_mem_Ioo hb
  have hreca := gamma_rayParam_smul ha
  have hrecb := gamma_rayParam_smul hb
  have hdet_g : 0 < det2 (gamma (rayParam a)) (gamma (rayParam b)) := by
    rw [← hreca, ← hrecb, det2_smul_left, det2_smul_right] at hdet
    have hprod_pos : 0 < (|a.1| + |a.2|) * (|b.1| + |b.2|) := mul_pos hna hnb
    nlinarith
  have hga_pos : 0 < dot2 (gamma (rayParam a)) (gamma t₀) := by
    rw [← hreca, dot2_smul_left] at hpa
    exact pos_of_mul_pos_right hpa (le_of_lt hna)
  have hgb_pos : 0 < dot2 (gamma (rayParam b)) (gamma t₀) := by
    rw [← hrecb, dot2_smul_left] at hpb
    exact pos_of_mul_pos_right hpb (le_of_lt hnb)
  rcases lt_trichotomy (rayParam a) (rayParam b) with hlt | heq | hgt
  · exact hlt
  · rw [heq, det2_self] at hdet_g; linarith
  · have hdet_rev : det2 (gamma (rayParam b)) (gamma (rayParam a)) < 0 := by
      rw [det2_antisymm]; linarith
    have hspan_gt2 : 2 < rayParam a - rayParam b :=
      (gamma_det2_sign (le_of_lt hsb.1) hgt (le_of_lt hsa.2)).2.2.mp hdet_rev
    have hsb_lt1 : rayParam b < 1 := by linarith [hsa.2]
    have hsa_gt2 : 2 < rayParam a := by linarith [hsb.1]
    rcases eq_or_lt_of_le ht0_lo with rfl | ht0_pos
    · rw [gamma_zero] at hga_pos
      unfold gamma dot2 at hga_pos
      rw [if_neg (by linarith), if_neg (by linarith)] at hga_pos
      dsimp at hga_pos
      linarith [hsa.2]
    · rcases eq_or_lt_of_le ht0_hi with rfl | ht0_lt3
      · rw [gamma_three] at hgb_pos
        unfold gamma dot2 at hgb_pos
        rw [if_pos (le_of_lt hsb_lt1)] at hgb_pos
        dsimp at hgb_pos
        linarith [hsb.1]
      · have hq_om : InOmega (gamma t₀) := gamma_inOmega ht0_pos ht0_lt3
        have hgb_c : 0 < dot2 (gamma t₀) (gamma (rayParam b)) := by rw [dot2_comm]; exact hgb_pos
        have hga_c : 0 < dot2 (gamma t₀) (gamma (rayParam a)) := by rw [dot2_comm]; exact hga_pos
        have hspan_lt2 := (omega_pos_span (le_of_lt hsb.1) hgt (le_of_lt hsa.2)
          hgb_c hga_c (Or.inl hq_om)).1
        linarith

/-- Positive-Tie Ray Ordering: if `a, b ∈ Ω` tie positively at `t₁` and `b` beats `a` (with `b > 0`)
to the right (`t₁ < t₂`), or `a` beats `b` (with `a > 0`) to the left (`t₂ < t₁`), then
`det2 a b > 0` and `rayParam a < rayParam b`. -/
theorem rayParam_lt_of_pos_tie {a b : ℝ × ℝ} {t₁ t₂ : ℝ}
    (ha : InOmega a) (hb : InOmega b)
    (ht1_lo : 0 ≤ t₁) (ht1_hi : t₁ ≤ 3) (ht2_lo : 0 ≤ t₂) (ht2_hi : t₂ ≤ 3)
    (htie : dot2 a (gamma t₁) = dot2 b (gamma t₁))
    (hpos1 : 0 < dot2 a (gamma t₁))
    (hord : (t₁ < t₂ ∧ dot2 a (gamma t₂) < dot2 b (gamma t₂) ∧ 0 < dot2 b (gamma t₂)) ∨
            (t₂ < t₁ ∧ dot2 b (gamma t₂) < dot2 a (gamma t₂) ∧ 0 < dot2 a (gamma t₂))) :
    0 < det2 a b ∧ rayParam a < rayParam b := by
  have hpos1_b : 0 < dot2 b (gamma t₁) := htie ▸ hpos1
  rcases hord with ⟨hlt, hbeat, hpos2⟩ | ⟨hlt, hbeat, hpos2⟩
  · have hdet_g : 0 < det2 (gamma t₁) (gamma t₂) :=
      (omega_pos_span ht1_lo hlt ht2_hi hpos1_b hpos2 (Or.inl hb)).2
    have hcb := cauchy_binet_two a b (gamma t₁) (gamma t₂)
    have hprod : 0 < det2 a b * det2 (gamma t₁) (gamma t₂) := by
      rw [← hcb, ← htie]
      have : dot2 a (gamma t₁) * dot2 b (gamma t₂) - dot2 a (gamma t₂) * dot2 a (gamma t₁) =
          dot2 a (gamma t₁) * (dot2 b (gamma t₂) - dot2 a (gamma t₂)) := by ring
      rw [this]
      exact mul_pos hpos1 (sub_pos.mpr hbeat)
    have hdet_ab : 0 < det2 a b := pos_of_mul_pos_left hprod (le_of_lt hdet_g)
    exact ⟨hdet_ab, rayParam_lt_of_det2_pos_and_pos_dot ha hb ht1_lo ht1_hi hdet_ab hpos1 hpos1_b⟩
  · have hdet_g : 0 < det2 (gamma t₂) (gamma t₁) :=
      (omega_pos_span ht2_lo hlt ht1_hi hpos2 hpos1 (Or.inl ha)).2
    have hcb := cauchy_binet_two a b (gamma t₂) (gamma t₁)
    have hprod : 0 < det2 a b * det2 (gamma t₂) (gamma t₁) := by
      rw [← hcb, ← htie]
      have : dot2 a (gamma t₂) * dot2 a (gamma t₁) - dot2 a (gamma t₁) * dot2 b (gamma t₂) =
          dot2 a (gamma t₁) * (dot2 a (gamma t₂) - dot2 b (gamma t₂)) := by ring
      rw [this]
      exact mul_pos hpos1 (sub_pos.mpr hbeat)
    have hdet_ab : 0 < det2 a b := pos_of_mul_pos_left hprod (le_of_lt hdet_g)
    exact ⟨hdet_ab, rayParam_lt_of_det2_pos_and_pos_dot ha hb ht1_lo ht1_hi hdet_ab hpos1 hpos1_b⟩

end CaseA
end
