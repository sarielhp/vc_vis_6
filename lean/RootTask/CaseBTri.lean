import Mathlib
import RootTask.Defs

open scoped Classical BigOperators
open Finset

noncomputable section

namespace CaseB

/-! ## Basic Planar Regions and Wedge Convexity -/

def inOmega (p : ℝ × ℝ) : Prop := p.1 < 0 ∨ p.2 < 0

def inQ1Bar (p : ℝ × ℝ) : Prop := 0 ≤ p.1 ∧ 0 ≤ p.2

def inQ3 (p : ℝ × ℝ) : Prop := p.1 < 0 ∧ p.2 < 0

lemma omega_iff_not_q1bar (p : ℝ × ℝ) : inOmega p ↔ ¬ inQ1Bar p := by
  unfold inOmega inQ1Bar
  constructor
  · rintro (h | h) ⟨h1, h2⟩ <;> linarith
  · intro h
    by_contra hnot
    push Not at hnot
    exact h ⟨hnot.1, hnot.2⟩

lemma isOpen_omega : IsOpen {p : ℝ × ℝ | inOmega p} := by
  have h1 : IsOpen {p : ℝ × ℝ | p.1 < 0} := isOpen_lt continuous_fst continuous_const
  have h2 : IsOpen {p : ℝ × ℝ | p.2 < 0} := isOpen_lt continuous_snd continuous_const
  exact h1.union h2

lemma isConnected_omega : IsConnected {p : ℝ × ℝ | inOmega p} := by
  have hconv1 : Convex ℝ {p : ℝ × ℝ | p.1 < 0} := by
    intro x hx y hy a b ha hb hab
    change a * x.1 + b * y.1 < 0
    have h1 : a * x.1 ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ha (le_of_lt hx)
    have h2 : b * y.1 ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hb (le_of_lt hy)
    rcases eq_or_lt_of_le ha with rfl | ha'
    · simp only [zero_mul, zero_add] at hab ⊢
      rw [hab, one_mul]; exact hy
    · linarith [mul_neg_of_pos_of_neg ha' hx]
  have hconv2 : Convex ℝ {p : ℝ × ℝ | p.2 < 0} := by
    intro x hx y hy a b ha hb hab
    change a * x.2 + b * y.2 < 0
    have h2 : b * y.2 ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hb (le_of_lt hy)
    rcases eq_or_lt_of_le ha with rfl | ha'
    · simp only [zero_mul, zero_add] at hab ⊢
      rw [hab, one_mul]; exact hy
    · linarith [mul_neg_of_pos_of_neg ha' hx]
  have hc1 : IsPreconnected {p : ℝ × ℝ | p.1 < 0} := hconv1.isPreconnected
  have hc2 : IsPreconnected {p : ℝ × ℝ | p.2 < 0} := hconv2.isPreconnected
  refine ⟨⟨(-1, -1), Or.inl (by norm_num)⟩, ?_⟩
  exact hc1.union (-1, -1) (by norm_num : (-1 : ℝ) < 0) (by norm_num : (-1 : ℝ) < 0) hc2

lemma memOpen_convex (W : OpenWedge) : Convex ℝ {p : ℝ × ℝ | W.MemOpen p} := by
  intro x hx y hy a b ha hb hab
  obtain ⟨hx1, hx2⟩ := hx
  obtain ⟨hy1, hy2⟩ := hy
  have e1 : W.u₁.1 * ((a • x + b • y).1 - W.y.1) + W.u₁.2 * ((a • x + b • y).2 - W.y.2) =
      a * (W.u₁.1 * (x.1 - W.y.1) + W.u₁.2 * (x.2 - W.y.2)) +
      b * (W.u₁.1 * (y.1 - W.y.1) + W.u₁.2 * (y.2 - W.y.2)) := by
    simp only [Prod.smul_fst, Prod.smul_snd, Prod.fst_add, Prod.snd_add, smul_eq_mul]
    linear_combination (W.u₁.1 * W.y.1 + W.u₁.2 * W.y.2) * hab
  have e2 : W.u₂.1 * ((a • x + b • y).1 - W.y.1) + W.u₂.2 * ((a • x + b • y).2 - W.y.2) =
      a * (W.u₂.1 * (x.1 - W.y.1) + W.u₂.2 * (x.2 - W.y.2)) +
      b * (W.u₂.1 * (y.1 - W.y.1) + W.u₂.2 * (y.2 - W.y.2)) := by
    simp only [Prod.smul_fst, Prod.smul_snd, Prod.fst_add, Prod.snd_add, smul_eq_mul]
    linear_combination (W.u₂.1 * W.y.1 + W.u₂.2 * W.y.2) * hab
  constructor
  · rw [e1]
    rcases eq_or_lt_of_le ha with rfl | ha'
    · simp only [zero_mul, zero_add] at hab ⊢; rw [hab, one_mul]; exact hy1
    · have hb_nn : 0 ≤ b * (W.u₁.1 * (y.1 - W.y.1) + W.u₁.2 * (y.2 - W.y.2)) :=
        mul_nonneg hb (le_of_lt hy1)
      linarith [mul_pos ha' hx1]
  · rw [e2]
    rcases eq_or_lt_of_le ha with rfl | ha'
    · simp only [zero_mul, zero_add] at hab ⊢; rw [hab, one_mul]; exact hy2
    · have hb_nn : 0 ≤ b * (W.u₂.1 * (y.1 - W.y.1) + W.u₂.2 * (y.2 - W.y.2)) :=
        mul_nonneg hb (le_of_lt hy2)
      linarith [mul_pos ha' hx2]

lemma isOpen_memOpen (W : OpenWedge) : IsOpen {p : ℝ × ℝ | W.MemOpen p} := by
  have f1 : Continuous fun p : ℝ × ℝ => W.u₁.1 * (p.1 - W.y.1) + W.u₁.2 * (p.2 - W.y.2) := by
    fun_prop
  have f2 : Continuous fun p : ℝ × ℝ => W.u₂.1 * (p.1 - W.y.1) + W.u₂.2 * (p.2 - W.y.2) := by
    fun_prop
  exact (isOpen_lt continuous_const f1).inter (isOpen_lt continuous_const f2)

lemma isOpen_memExt (W : OpenWedge) : IsOpen {p : ℝ × ℝ | W.MemExt p} := by
  have f1 : Continuous fun p : ℝ × ℝ => W.u₁.1 * (p.1 - W.y.1) + W.u₁.2 * (p.2 - W.y.2) := by
    fun_prop
  have f2 : Continuous fun p : ℝ × ℝ => W.u₂.1 * (p.1 - W.y.1) + W.u₂.2 * (p.2 - W.y.2) := by
    fun_prop
  exact (isOpen_lt f1 continuous_const).union (isOpen_lt f2 continuous_const)

lemma memOpen_memExt_disjoint (W : OpenWedge) (p : ℝ × ℝ) :
    ¬ (W.MemOpen p ∧ W.MemExt p) := by
  rintro ⟨⟨h1, h2⟩, h3 | h4⟩ <;> linarith

/-! ## Case B Normalization & Apex Trichotomy -/

lemma caseB_pa_pb_signs
    (W : Fin 5 → OpenWedge)
    (pa pb : ℝ × ℝ)
    (hpa1 : 0 < pa.1) (hpa : ∀ i : Fin 5, (W i).MemOpen pa)
    (hpb2 : 0 < pb.2) (hpb : ∀ i : Fin 5, (W i).MemOpen pb)
    (h_disj_q1 : ¬ ∃ q : ℝ × ℝ, 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ ∀ i : Fin 5, (W i).MemOpen q) :
    pa.2 < 0 ∧ pb.1 < 0 ∧ pa.1 * pb.2 - pa.2 * pb.1 < 0 := by
  have hpa2 : pa.2 < 0 := by
    by_contra h
    push Not at h
    exact h_disj_q1 ⟨pa, le_of_lt hpa1, h, hpa⟩
  have hpb1 : pb.1 < 0 := by
    by_contra h
    push Not at h
    exact h_disj_q1 ⟨pb, h, le_of_lt hpb2, hpb⟩
  have hC : pa.1 * pb.2 - pa.2 * pb.1 < 0 := by
    by_contra hCge
    push Not at hCge
    have hden : 0 < pa.1 - pb.1 := by linarith
    let t : ℝ := -pb.1 / (pa.1 - pb.1)
    have ht0 : 0 ≤ t := div_nonneg (by linarith) (le_of_lt hden)
    have ht1 : 0 ≤ 1 - t := by
      have : 1 - t = pa.1 / (pa.1 - pb.1) := by dsimp [t]; field_simp [ne_of_gt hden]; ring
      rw [this]; exact div_nonneg (le_of_lt hpa1) (le_of_lt hden)
    have hsum : (1 - t) + t = 1 := by ring
    let q : ℝ × ℝ := (1 - t) • pb + t • pa
    have hq1 : q.1 = 0 := by
      dsimp [q, t]; field_simp [ne_of_gt hden]; ring
    have hq2 : 0 ≤ q.2 := by
      have hq2_eq : q.2 = (pa.1 * pb.2 - pa.2 * pb.1) / (pa.1 - pb.1) := by
        dsimp [q, t]; field_simp [ne_of_gt hden]; ring
      rw [hq2_eq]
      exact div_nonneg hCge (le_of_lt hden)
    have hq_mem : ∀ i : Fin 5, (W i).MemOpen q := fun i =>
      memOpen_convex (W i) (hpb i) (hpa i) ht1 ht0 hsum
    exact h_disj_q1 ⟨q, le_of_eq hq1.symm, hq2, hq_mem⟩
  exact ⟨hpa2, hpb1, hC⟩

def isLlt (W : OpenWedge) (pa pb : ℝ × ℝ) : Prop :=
  (pb.2 - pa.2) * W.y.1 + (pa.1 - pb.1) * W.y.2 < pa.1 * pb.2 - pa.2 * pb.1

def isLgt (W : OpenWedge) (pa pb : ℝ × ℝ) : Prop :=
  pa.1 * pb.2 - pa.2 * pb.1 < (pb.2 - pa.2) * W.y.1 + (pa.1 - pb.1) * W.y.2

lemma caseB_dichotomy (W : OpenWedge) (pa pb : ℝ × ℝ)
    (hy1 : W.y.1 < 0) (hy2 : W.y.2 < 0)
    (hxa : 0 < pa.1) (hya : pa.2 < 0) (hxb : pb.1 < 0) (hyb : 0 < pb.2)
    (hC : pa.1 * pb.2 - pa.2 * pb.1 < 0)
    (ha : W.MemOpen pa) (hb : W.MemOpen pb) :
    isLlt W pa pb ∨ isLgt W pa pb := by
  have hneq := case_b_apex_not_on_line W pa pb hy1 hy2 hxa hya hxb hyb hC ha hb
  rcases lt_trichotomy ((pb.2 - pa.2) * W.y.1 + (pa.1 - pb.1) * W.y.2) (pa.1 * pb.2 - pa.2 * pb.1)
    with h | h | h
  · exact Or.inl h
  · exact False.elim (hneq h)
  · exact Or.inr h

lemma caseB_Lgt_nonempty (W : Fin 5 → OpenWedge) (pa pb : ℝ × ℝ)
    (h_apex : ∀ i : Fin 5, (W i).y.1 < 0 ∧ (W i).y.2 < 0)
    (hxa : 0 < pa.1) (hya : pa.2 < 0) (hxb : pb.1 < 0) (hyb : 0 < pb.2)
    (hC : pa.1 * pb.2 - pa.2 * pb.1 < 0)
    (ha : ∀ i : Fin 5, (W i).MemOpen pa) (hb : ∀ i : Fin 5, (W i).MemOpen pb)
    (h_disj_q1 : ¬ ∃ q : ℝ × ℝ, 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ ∀ i : Fin 5, (W i).MemOpen q) :
    ∃ i : Fin 5, isLgt (W i) pa pb := by
  by_contra hnone
  push Not at hnone
  have h0 : ∀ i : Fin 5, (W i).MemOpen (0, 0) := by
    intro i
    rcases caseB_dichotomy (W i) pa pb (h_apex i).1 (h_apex i).2 hxa hya hxb hyb hC (ha i) (hb i)
      with hlt | hgt
    · exact case_b_origin_in_wedge (W i) pa pb (h_apex i).1 (h_apex i).2 hxa hya hxb hyb hC
        (ha i) (hb i) hlt
    · exact False.elim ((hnone i) hgt)
  exact h_disj_q1 ⟨(0, 0), le_rfl, le_rfl, h0⟩

lemma caseB_Lgt_contains_axes
    (Xa Ya Xb Yb xi ui : ℝ)
    (hXa : 0 < Xa) (hYa : Ya < 0) (hXb : Xb < 0) (hYb : 0 < Yb)
    (_hC : Xa * Yb - Xb * Ya < 0) (hxi : xi < 0) (hui : ui < 0)
    (hL : (Yb - Ya) * xi + (Xa - Xb) * ui > Xa * Yb - Xb * Ya) :
    ∃ α1 β1 α2 β2 : ℝ, 0 < α1 ∧ 0 < β1 ∧ 0 < α2 ∧ 0 < β2 ∧
      α1 * (Xb - xi) + β1 * (Xa - xi) = -1 ∧
      α1 * (Yb - ui) + β1 * (Ya - ui) = 0 ∧
      α2 * (Xb - xi) + β2 * (Xa - xi) = 0 ∧
      α2 * (Yb - ui) + β2 * (Ya - ui) = -1 := by
  have hXb_lt : Xb - xi < 0 := by nlinarith
  have hYb_gt : 0 < Yb - ui := by nlinarith
  have hXa_gt : 0 < Xa - xi := by linarith
  have hYa_lt : Ya - ui < 0 := by nlinarith
  have hΔ : 0 < (Xb - xi) * (Ya - ui) - (Yb - ui) * (Xa - xi) := by nlinarith
  let Δ := (Xb - xi) * (Ya - ui) - (Yb - ui) * (Xa - xi)
  have hΔ_ne : Δ ≠ 0 := ne_of_gt hΔ
  refine ⟨-(Ya - ui) / Δ, (Yb - ui) / Δ, (Xa - xi) / Δ, -(Xb - xi) / Δ,
    div_pos (by linarith) hΔ, div_pos hYb_gt hΔ, div_pos hXa_gt hΔ, div_pos (by linarith) hΔ, ?_, ?_, ?_, ?_⟩
  · rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, div_eq_iff hΔ_ne]; dsimp [Δ]; ring
  · rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, div_eq_zero_iff]; left; ring
  · rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, div_eq_zero_iff]; left; ring
  · rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, div_eq_iff hΔ_ne]; dsimp [Δ]; ring

lemma caseB_Lgt_normals_neg (W : OpenWedge) (pa pb : ℝ × ℝ)
    (hy1 : W.y.1 < 0) (hy2 : W.y.2 < 0)
    (hxa : 0 < pa.1) (hya : pa.2 < 0) (hxb : pb.1 < 0) (hyb : 0 < pb.2)
    (hC : pa.1 * pb.2 - pa.2 * pb.1 < 0)
    (ha : W.MemOpen pa) (hb : W.MemOpen pb)
    (hgt : isLgt W pa pb) :
    W.u₁.1 < 0 ∧ W.u₁.2 < 0 ∧ W.u₂.1 < 0 ∧ W.u₂.2 < 0 := by
  obtain ⟨α1, β1, α2, β2, hα1, hβ1, hα2, hβ2, e1, e2, e3, e4⟩ :=
    caseB_Lgt_contains_axes pa.1 pa.2 pb.1 pb.2 W.y.1 W.y.2 hxa hya hxb hyb
      (by linarith) hy1 hy2 (by dsimp [isLgt] at hgt; linarith)
  obtain ⟨ha1, ha2⟩ := ha
  obtain ⟨hb1, hb2⟩ := hb
  have hu1_1 : -W.u₁.1 =
      α1 * (W.u₁.1 * (pb.1 - W.y.1) + W.u₁.2 * (pb.2 - W.y.2)) +
      β1 * (W.u₁.1 * (pa.1 - W.y.1) + W.u₁.2 * (pa.2 - W.y.2)) := by
    calc -W.u₁.1 = W.u₁.1 * (-1) + W.u₁.2 * 0 := by ring
      _ = W.u₁.1 * (α1 * (pb.1 - W.y.1) + β1 * (pa.1 - W.y.1)) +
          W.u₁.2 * (α1 * (pb.2 - W.y.2) + β1 * (pa.2 - W.y.2)) := by rw [e1, e2]
      _ = _ := by ring
  have hu1_2 : -W.u₁.2 =
      α2 * (W.u₁.1 * (pb.1 - W.y.1) + W.u₁.2 * (pb.2 - W.y.2)) +
      β2 * (W.u₁.1 * (pa.1 - W.y.1) + W.u₁.2 * (pa.2 - W.y.2)) := by
    calc -W.u₁.2 = W.u₁.1 * 0 + W.u₁.2 * (-1) := by ring
      _ = W.u₁.1 * (α2 * (pb.1 - W.y.1) + β2 * (pa.1 - W.y.1)) +
          W.u₁.2 * (α2 * (pb.2 - W.y.2) + β2 * (pa.2 - W.y.2)) := by rw [e3, e4]
      _ = _ := by ring
  have hu2_1 : -W.u₂.1 =
      α1 * (W.u₂.1 * (pb.1 - W.y.1) + W.u₂.2 * (pb.2 - W.y.2)) +
      β1 * (W.u₂.1 * (pa.1 - W.y.1) + W.u₂.2 * (pa.2 - W.y.2)) := by
    calc -W.u₂.1 = W.u₂.1 * (-1) + W.u₂.2 * 0 := by ring
      _ = W.u₂.1 * (α1 * (pb.1 - W.y.1) + β1 * (pa.1 - W.y.1)) +
          W.u₂.2 * (α1 * (pb.2 - W.y.2) + β1 * (pa.2 - W.y.2)) := by rw [e1, e2]
      _ = _ := by ring
  have hu2_2 : -W.u₂.2 =
      α2 * (W.u₂.1 * (pb.1 - W.y.1) + W.u₂.2 * (pb.2 - W.y.2)) +
      β2 * (W.u₂.1 * (pa.1 - W.y.1) + W.u₂.2 * (pa.2 - W.y.2)) := by
    calc -W.u₂.2 = W.u₂.1 * 0 + W.u₂.2 * (-1) := by ring
      _ = W.u₂.1 * (α2 * (pb.1 - W.y.1) + β2 * (pa.1 - W.y.1)) +
          W.u₂.2 * (α2 * (pb.2 - W.y.2) + β2 * (pa.2 - W.y.2)) := by rw [e3, e4]
      _ = _ := by ring
  refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith

lemma caseB_Lgt_contains_sublevel (W : OpenWedge) (pa pb z : ℝ × ℝ)
    (hy1 : W.y.1 < 0) (hy2 : W.y.2 < 0)
    (hxa : 0 < pa.1) (hya : pa.2 < 0) (hxb : pb.1 < 0) (hyb : 0 < pb.2)
    (hC : pa.1 * pb.2 - pa.2 * pb.1 < 0)
    (ha : W.MemOpen pa) (hb : W.MemOpen pb) (hgt : isLgt W pa pb)
    (hz1 : z.1 < 0) (hz2 : z.2 < 0)
    (hz_le : (pb.2 - pa.2) * z.1 + (pa.1 - pb.1) * z.2 ≤ pa.1 * pb.2 - pa.2 * pb.1) :
    W.MemOpen z := by
  obtain ⟨hu11, hu12, hu21, hu22⟩ :=
    caseB_Lgt_normals_neg W pa pb hy1 hy2 hxa hya hxb hyb hC ha hb hgt
  have hA : 0 < pb.2 - pa.2 := by linarith
  have hB : 0 < pa.1 - pb.1 := by linarith
  have hL_neg : (pb.2 - pa.2) * z.1 + (pa.1 - pb.1) * z.2 < 0 := by nlinarith
  let lam : ℝ := (pa.1 * pb.2 - pa.2 * pb.1) / ((pb.2 - pa.2) * z.1 + (pa.1 - pb.1) * z.2)
  have hlam_pos : 0 < lam := div_pos_of_neg_of_neg hC hL_neg
  have hlam_le : lam ≤ 1 := by
    dsimp [lam]
    rw [div_le_iff_of_neg hL_neg]
    linarith
  -- `lam • z` lies strictly on the open segment `(pb, pa)`
  have hden : 0 < pa.1 - pb.1 := hB
  let t : ℝ := (lam * z.1 - pb.1) / (pa.1 - pb.1)
  have heq_lam : lam * ((pb.2 - pa.2) * z.1 + (pa.1 - pb.1) * z.2) = pa.1 * pb.2 - pa.2 * pb.1 :=
    div_mul_cancel₀ _ (ne_of_lt hL_neg)
  have ht_pos : 0 < t := by
    have hnum : pb.1 < lam * z.1 := by
      have hprod : ((pb.2 - pa.2) * z.1 + (pa.1 - pb.1) * z.2) * (lam * z.1 - pb.1) =
          (pa.1 - pb.1) * (pb.2 * z.1 - pb.1 * z.2) := by
        linear_combination z.1 * heq_lam
      have hp1 : pb.2 * z.1 < 0 := mul_neg_of_pos_of_neg hyb hz1
      have hp2 : 0 < pb.1 * z.2 := mul_pos_of_neg_of_neg hxb hz2
      have hrhs : (pa.1 - pb.1) * (pb.2 * z.1 - pb.1 * z.2) < 0 := mul_neg_of_pos_of_neg hden (by linarith)
      nlinarith
    exact div_pos (by linarith) hden
  have h1mt_pos : 0 < 1 - t := by
    have heq : 1 - t = (pa.1 - lam * z.1) / (pa.1 - pb.1) := by
      dsimp [t]; field_simp [ne_of_gt hden]; ring
    rw [heq]
    have hnum : lam * z.1 < pa.1 := by
      have hprod : ((pb.2 - pa.2) * z.1 + (pa.1 - pb.1) * z.2) * (pa.1 - lam * z.1) =
          (pa.1 - pb.1) * (pa.1 * z.2 - pa.2 * z.1) := by
        linear_combination -z.1 * heq_lam
      have hp1 : pa.1 * z.2 < 0 := mul_neg_of_pos_of_neg hxa hz2
      have hp2 : 0 < pa.2 * z.1 := mul_pos_of_neg_of_neg hya hz1
      have hrhs : (pa.1 - pb.1) * (pa.1 * z.2 - pa.2 * z.1) < 0 := mul_neg_of_pos_of_neg hden (by linarith)
      nlinarith
    exact div_pos (by linarith) hden
  have hlamz1 : (1 - t) * pb.1 + t * pa.1 = lam * z.1 := by
    dsimp [t]; field_simp [ne_of_gt hden]; ring
  have hlamz2 : (1 - t) * pb.2 + t * pa.2 = lam * z.2 := by
    have hden_ne : pa.1 - pb.1 ≠ 0 := ne_of_gt hden
    have ht_mul : t * (pa.1 - pb.1) = lam * z.1 - pb.1 := div_mul_cancel₀ _ hden_ne
    have h_eq : ((1 - t) * pb.2 + t * pa.2) * (pa.1 - pb.1) = lam * z.2 * (pa.1 - pb.1) := by
      calc ((1 - t) * pb.2 + t * pa.2) * (pa.1 - pb.1)
          = (pa.1 - pb.1) * pb.2 - (t * (pa.1 - pb.1)) * pb.2 + (t * (pa.1 - pb.1)) * pa.2 := by ring
        _ = (pa.1 - pb.1) * pb.2 - (lam * z.1 - pb.1) * pb.2 + (lam * z.1 - pb.1) * pa.2 := by rw [ht_mul]
        _ = lam * z.2 * (pa.1 - pb.1) := by linarith [heq_lam]
    exact mul_right_cancel₀ hden_ne h_eq
  have hlamz_open : W.MemOpen (lam * z.1, lam * z.2) := by
    have hseg := memOpen_convex W hb ha (le_of_lt h1mt_pos) (le_of_lt ht_pos) (by ring)
    have hprod : ((1 - t) • pb + t • pa) = (lam * z.1, lam * z.2) :=
      Prod.ext hlamz1 hlamz2
    rwa [hprod] at hseg
  have h1mlam : 0 ≤ 1 - lam := sub_nonneg.mpr hlam_le
  have hz1_nonpos : (1 - lam) * z.1 ≤ 0 := mul_nonpos_of_nonneg_of_nonpos h1mlam (le_of_lt hz1)
  have hz2_nonpos : (1 - lam) * z.2 ≤ 0 := mul_nonpos_of_nonneg_of_nonpos h1mlam (le_of_lt hz2)
  obtain ⟨hl1, hl2⟩ := hlamz_open
  constructor
  · have e1 : W.u₁.1 * (z.1 - W.y.1) + W.u₁.2 * (z.2 - W.y.2) =
        (W.u₁.1 * (lam * z.1 - W.y.1) + W.u₁.2 * (lam * z.2 - W.y.2)) +
        W.u₁.1 * ((1 - lam) * z.1) + W.u₁.2 * ((1 - lam) * z.2) := by ring
    rw [e1]
    nlinarith
  · have e2 : W.u₂.1 * (z.1 - W.y.1) + W.u₂.2 * (z.2 - W.y.2) =
        (W.u₂.1 * (lam * z.1 - W.y.1) + W.u₂.2 * (lam * z.2 - W.y.2)) +
        W.u₂.1 * ((1 - lam) * z.1) + W.u₂.2 * ((1 - lam) * z.2) := by ring
    rw [e2]
    nlinarith

lemma caseB_Llt_in_Lgt (Wi Wj : OpenWedge) (pa pb : ℝ × ℝ)
    (hyi1 : Wi.y.1 < 0) (hyi2 : Wi.y.2 < 0)
    (hyj1 : Wj.y.1 < 0) (hyj2 : Wj.y.2 < 0)
    (hxa : 0 < pa.1) (hya : pa.2 < 0) (hxb : pb.1 < 0) (hyb : 0 < pb.2)
    (hC : pa.1 * pb.2 - pa.2 * pb.1 < 0)
    (haj : Wj.MemOpen pa) (hbj : Wj.MemOpen pb)
    (hlt_i : isLlt Wi pa pb) (hgt_j : isLgt Wj pa pb) :
    Wj.MemOpen Wi.y :=
  caseB_Lgt_contains_sublevel Wj pa pb Wi.y hyj1 hyj2 hxa hya hxb hyb hC haj hbj hgt_j
    hyi1 hyi2 (le_of_lt hlt_i)

/-! ## Elimination of `k = 5` -/

lemma caseB_k5_elim
    (h_thm1 : ∀ f : Fin 5 → VFunc, ¬ (∀ m : Fin 5 → Bool, ∃ p : ℝ × ℝ, RealizesVMask f m p))
    (W : Fin 5 → OpenWedge) (pa pb : ℝ × ℝ)
    (h_apex : ∀ i : Fin 5, (W i).y.1 < 0 ∧ (W i).y.2 < 0)
    (hxa : 0 < pa.1) (hya : pa.2 < 0) (hxb : pb.1 < 0) (hyb : 0 < pb.2)
    (hC : pa.1 * pb.2 - pa.2 * pb.1 < 0)
    (ha : ∀ i : Fin 5, (W i).MemOpen pa) (hb : ∀ i : Fin 5, (W i).MemOpen pb)
    (h_all_gt : ∀ i : Fin 5, isLgt (W i) pa pb)
    (h_all : ∀ m : Fin 5 → Bool, ∃ p : ℝ × ℝ, RealizesWedgeMask W m p) :
    False := by
  have hneg : ∀ i : Fin 5, (W i).u₁.1 < 0 ∧ (W i).u₁.2 < 0 ∧ (W i).u₂.1 < 0 ∧ (W i).u₂.2 < 0 :=
    fun i => caseB_Lgt_normals_neg (W i) pa pb (h_apex i).1 (h_apex i).2 hxa hya hxb hyb hC
      (ha i) (hb i) (h_all_gt i)
  let f : Fin 5 → VFunc := fun i =>
    toVFunc
      (-(W i).u₁.1 / (-(W i).u₁.2))
      (((W i).u₁.1 * (W i).y.1 + (W i).u₁.2 * (W i).y.2) / (-(W i).u₁.2))
      (-(W i).u₂.1 / (-(W i).u₂.2))
      (((W i).u₂.1 * (W i).y.1 + (W i).u₂.2 * (W i).y.2) / (-(W i).u₂.2))
  apply h_thm1 f
  intro m
  obtain ⟨p, hp⟩ := h_all m
  refine ⟨(p.1, -p.2), fun i => ?_⟩
  obtain ⟨_, hu12, _, hu22⟩ := hneg i
  have h1_pos : 0 < -(W i).u₁.2 := by linarith
  have h2_pos : 0 < -(W i).u₂.2 := by linarith
  have h1_ne : -(W i).u₁.2 ≠ 0 := ne_of_gt h1_pos
  have h2_ne : -(W i).u₂.2 ≠ 0 := ne_of_gt h2_pos
  have e1 : (W i).u₁.1 * (p.1 - (W i).y.1) + (W i).u₁.2 * (p.2 - (W i).y.2) =
      (-(W i).u₁.2) * (-p.2 - ((-(W i).u₁.1 / (-(W i).u₁.2)) * p.1 +
        ((W i).u₁.1 * (W i).y.1 + (W i).u₁.2 * (W i).y.2) / (-(W i).u₁.2))) := by
    have h1a : (-(W i).u₁.2) * (-(W i).u₁.1 / (-(W i).u₁.2)) = -(W i).u₁.1 := mul_div_cancel₀ _ h1_ne
    have h1b : (-(W i).u₁.2) * (((W i).u₁.1 * (W i).y.1 + (W i).u₁.2 * (W i).y.2) / (-(W i).u₁.2)) =
        (W i).u₁.1 * (W i).y.1 + (W i).u₁.2 * (W i).y.2 := mul_div_cancel₀ _ h1_ne
    calc (W i).u₁.1 * (p.1 - (W i).y.1) + (W i).u₁.2 * (p.2 - (W i).y.2)
        = (-(W i).u₁.2) * (-p.2) - (-(W i).u₁.1) * p.1 -
          ((W i).u₁.1 * (W i).y.1 + (W i).u₁.2 * (W i).y.2) := by ring
      _ = (-(W i).u₁.2) * (-p.2) -
          ((-(W i).u₁.2) * (-(W i).u₁.1 / (-(W i).u₁.2))) * p.1 -
          (-(W i).u₁.2) * (((W i).u₁.1 * (W i).y.1 + (W i).u₁.2 * (W i).y.2) / (-(W i).u₁.2)) := by
          rw [h1a, h1b]
      _ = _ := by ring
  have e2 : (W i).u₂.1 * (p.1 - (W i).y.1) + (W i).u₂.2 * (p.2 - (W i).y.2) =
      (-(W i).u₂.2) * (-p.2 - ((-(W i).u₂.1 / (-(W i).u₂.2)) * p.1 +
        ((W i).u₂.1 * (W i).y.1 + (W i).u₂.2 * (W i).y.2) / (-(W i).u₂.2))) := by
    have h2a : (-(W i).u₂.2) * (-(W i).u₂.1 / (-(W i).u₂.2)) = -(W i).u₂.1 := mul_div_cancel₀ _ h2_ne
    have h2b : (-(W i).u₂.2) * (((W i).u₂.1 * (W i).y.1 + (W i).u₂.2 * (W i).y.2) / (-(W i).u₂.2)) =
        (W i).u₂.1 * (W i).y.1 + (W i).u₂.2 * (W i).y.2 := mul_div_cancel₀ _ h2_ne
    calc (W i).u₂.1 * (p.1 - (W i).y.1) + (W i).u₂.2 * (p.2 - (W i).y.2)
        = (-(W i).u₂.2) * (-p.2) - (-(W i).u₂.1) * p.1 -
          ((W i).u₂.1 * (W i).y.1 + (W i).u₂.2 * (W i).y.2) := by ring
      _ = (-(W i).u₂.2) * (-p.2) -
          ((-(W i).u₂.2) * (-(W i).u₂.1 / (-(W i).u₂.2))) * p.1 -
          (-(W i).u₂.2) * (((W i).u₂.1 * (W i).y.1 + (W i).u₂.2 * (W i).y.2) / (-(W i).u₂.2)) := by
          rw [h2a, h2b]
      _ = _ := by ring
  have heval : (f i).eval p.1 =
      max ((-(W i).u₁.1 / (-(W i).u₁.2)) * p.1 +
          ((W i).u₁.1 * (W i).y.1 + (W i).u₁.2 * (W i).y.2) / (-(W i).u₁.2))
          ((-(W i).u₂.1 / (-(W i).u₂.2)) * p.1 +
          ((W i).u₂.1 * (W i).y.1 + (W i).u₂.2 * (W i).y.2) / (-(W i).u₂.2)) :=
    toVFunc_eval _ _ _ _ _
  have hm_i := hp i
  by_cases hmi : m i
  · simp only [hmi, ↓reduceIte] at hm_i ⊢
    rw [heval, max_lt_iff]
    obtain ⟨hm1, hm2⟩ := hm_i
    rw [e1] at hm1; rw [e2] at hm2
    exact ⟨by nlinarith, by nlinarith⟩
  · simp only [hmi, Bool.false_eq_true, ↓reduceIte] at hm_i ⊢
    rw [heval, lt_max_iff]
    rcases hm_i with hm1 | hm2
    · rw [e1] at hm1; left; nlinarith
    · rw [e2] at hm2; right; nlinarith

/-! ## General Position Perturbation (`prop:gen-pos`) -/

def normal (W : Fin 5 → OpenWedge) (ib : Fin 5 × Bool) : ℝ × ℝ :=
  if ib.2 then (W ib.1).u₁ else (W ib.1).u₂

def lineAt (W : Fin 5 → OpenWedge) (ib : Fin 5 × Bool) (p : ℝ × ℝ) : ℝ :=
  let u := normal W ib
  u.1 * (p.1 - (W ib.1).y.1) + u.2 * (p.2 - (W ib.1).y.2)

structure GeneralPosition (W : Fin 5 → OpenWedge) : Prop where
  u_nonzero : ∀ a : Fin 5 × Bool, (normal W a).1 ≠ 0 ∧ (normal W a).2 ≠ 0
  no_parallel : ∀ a b : Fin 5 × Bool, a ≠ b →
    (normal W a).1 * (normal W b).2 - (normal W a).2 * (normal W b).1 ≠ 0
  no_three_concurrent : ∀ a b c : Fin 5 × Bool, a ≠ b → a ≠ c → b ≠ c →
    ∀ p : ℝ × ℝ, ¬ (lineAt W a p = 0 ∧ lineAt W b p = 0 ∧ lineAt W c p = 0)
  no_axis_concurrent : ∀ a b : Fin 5 × Bool, a ≠ b →
    ∀ p : ℝ × ℝ, lineAt W a p = 0 → lineAt W b p = 0 → p.1 ≠ 0 ∧ p.2 ≠ 0
  not_through_origin : ∀ a : Fin 5 × Bool, lineAt W a (0, 0) ≠ 0

lemma gp_apex_not_on_line {W : Fin 5 → OpenWedge} (hGP : GeneralPosition W)
    {i j : Fin 5} (hij : i ≠ j) (b : Bool) :
    lineAt W (i, b) (W j).y ≠ 0 := by
  intro h
  apply hGP.no_three_concurrent (j, true) (j, false) (i, b)
  · simp
  · intro heq; exact hij (congrArg Prod.fst heq).symm
  · intro heq; exact hij (congrArg Prod.fst heq).symm
  · refine ⟨?_, ?_, h⟩ <;> simp [lineAt]

lemma poly_dense_box :
    ∀ (N : ℕ) (a b : Fin N → ℝ) (_ : ∀ i, a i < b i) (P : MvPolynomial (Fin N) ℝ),
    P ≠ 0 → ∃ x : Fin N → ℝ, (∀ i, x i ∈ Set.Ioo (a i) (b i)) ∧ MvPolynomial.eval x P ≠ 0
  | 0, _, _, _, P, hP => by
    refine ⟨Fin.elim0, fun i => Fin.elim0 i, ?_⟩
    have hconst : P = MvPolynomial.C (MvPolynomial.coeff 0 P) := MvPolynomial.eq_C_of_isEmpty P
    intro hev
    rw [hconst, MvPolynomial.eval_C] at hev
    apply hP
    rw [hconst, hev, map_zero]
  | N + 1, a, b, hab, P, hP => by
    let Q := MvPolynomial.finSuccEquiv ℝ N P
    have hQ : Q ≠ 0 := by
      intro h0
      exact hP ((MvPolynomial.finSuccEquiv ℝ N).injective (by simpa [Q] using h0))
    have hlc : Q.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hQ
    let a' : Fin N → ℝ := fun i => a i.succ
    let b' : Fin N → ℝ := fun i => b i.succ
    have hab' : ∀ i, a' i < b' i := fun i => hab i.succ
    obtain ⟨x', hx', hlc_ev⟩ := poly_dense_box N a' b' hab' Q.leadingCoeff hlc
    let φ : MvPolynomial (Fin N) ℝ →+* ℝ :=
      { toFun := MvPolynomial.eval x'
        map_one' := map_one _
        map_mul' := fun p₁ p₂ => map_mul _ p₁ p₂
        map_zero' := map_zero _
        map_add' := fun p₁ p₂ => map_add _ p₁ p₂ }
    let q : Polynomial ℝ := Q.map φ
    have hq_ne : q ≠ 0 := by
      intro h0
      have hlc_zero : MvPolynomial.eval x' Q.leadingCoeff = 0 := by
        have hcoeff := congrArg (fun p : Polynomial ℝ => p.coeff Q.natDegree) h0
        rw [Polynomial.coeff_map, Polynomial.coeff_zero] at hcoeff
        exact hcoeff
      exact hlc_ev hlc_zero
    have hinf : (Set.Ioo (a 0) (b 0)).Infinite := Set.Ioo_infinite (hab 0)
    obtain ⟨t, ht_mem, ht_root⟩ := hinf.exists_notMem_finset q.roots.toFinset
    have ht_eval : q.eval t ≠ 0 := by
      intro h0
      apply ht_root
      rw [Multiset.mem_toFinset, Polynomial.mem_roots hq_ne]
      exact h0
    refine ⟨Fin.cons t x', fun i => Fin.cases ht_mem hx' i, ?_⟩
    have hev : ∀ R : MvPolynomial (Fin (N + 1)) ℝ,
        MvPolynomial.eval (Fin.cons t x') R = (Polynomial.map φ (MvPolynomial.finSuccEquiv ℝ N R)).eval t := by
      intro R
      induction R using MvPolynomial.induction_on with
      | C c =>
        change MvPolynomial.eval (Fin.cons t x') (MvPolynomial.C c) =
          (Polynomial.map φ (MvPolynomial.finSuccEquiv ℝ N (algebraMap ℝ (MvPolynomial (Fin (N + 1)) ℝ) c))).eval t
        rw [AlgEquiv.commutes,
            IsScalarTower.algebraMap_apply ℝ (MvPolynomial (Fin N) ℝ) (Polynomial (MvPolynomial (Fin N) ℝ)) c,
            ← Polynomial.C_eq_algebraMap, Polynomial.map_C, Polynomial.eval_C]
        change MvPolynomial.eval (Fin.cons t x') (MvPolynomial.C c) = MvPolynomial.eval x' (MvPolynomial.C c)
        rw [MvPolynomial.eval_C, MvPolynomial.eval_C]
      | add p₁ p₂ hp₁ hp₂ => simp [map_add, hp₁, hp₂]
      | mul_X p k ih =>
        rw [map_mul, map_mul, Polynomial.map_mul, Polynomial.eval_mul, ← ih]
        congr 1
        refine Fin.cases ?_ ?_ k
        · simp [MvPolynomial.finSuccEquiv_X_zero]
        · intro j; simp [MvPolynomial.finSuccEquiv_X_succ, φ]
    rw [hev P]
    exact ht_eval

private def encVec (W : Fin 5 → OpenWedge) : Fin 30 → ℝ := fun k =>
  let i : Fin 5 := ⟨k.1 / 6, Nat.div_lt_of_lt_mul k.2⟩
  match k.1 % 6 with
  | 0 => (W i).y.1
  | 1 => (W i).y.2
  | 2 => (W i).u₁.1
  | 3 => (W i).u₁.2
  | 4 => (W i).u₂.1
  | _ => (W i).u₂.2

private def decWedge (x : Fin 30 → ℝ)
    (h_nondeg : ∀ i : Fin 5,
      0 < x ⟨6 * i.1 + 2, by omega⟩ * x ⟨6 * i.1 + 5, by omega⟩ -
          x ⟨6 * i.1 + 3, by omega⟩ * x ⟨6 * i.1 + 4, by omega⟩) :
    Fin 5 → OpenWedge := fun i =>
  { y := (x ⟨6 * i.1, by omega⟩, x ⟨6 * i.1 + 1, by omega⟩)
    u₁ := (x ⟨6 * i.1 + 2, by omega⟩, x ⟨6 * i.1 + 3, by omega⟩)
    u₂ := (x ⟨6 * i.1 + 4, by omega⟩, x ⟨6 * i.1 + 5, by omega⟩)
    h_nondeg := h_nondeg i }

private lemma encVec_idx (W : Fin 5 → OpenWedge) (i : Fin 5) :
    encVec W ⟨6 * i.1, by omega⟩ = (W i).y.1 ∧
    encVec W ⟨6 * i.1 + 1, by omega⟩ = (W i).y.2 ∧
    encVec W ⟨6 * i.1 + 2, by omega⟩ = (W i).u₁.1 ∧
    encVec W ⟨6 * i.1 + 3, by omega⟩ = (W i).u₁.2 ∧
    encVec W ⟨6 * i.1 + 4, by omega⟩ = (W i).u₂.1 ∧
    encVec W ⟨6 * i.1 + 5, by omega⟩ = (W i).u₂.2 := by
  have hi : i.1 < 5 := i.2
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  · simp [encVec]
    try
      have h1 : (6 * i.1 + 1) / 6 = i.1 := by omega
      have h2 : (6 * i.1 + 2) / 6 = i.1 := by omega
      have h3 : (6 * i.1 + 3) / 6 = i.1 := by omega
      have h4 : (6 * i.1 + 4) / 6 = i.1 := by omega
      have h5 : (6 * i.1 + 5) / 6 = i.1 := by omega
      simp [h1, h2, h3, h4, h5]

private def pY1 (i : Fin 5) : MvPolynomial (Fin 30) ℝ := MvPolynomial.X ⟨6 * i.1, by omega⟩
private def pY2 (i : Fin 5) : MvPolynomial (Fin 30) ℝ := MvPolynomial.X ⟨6 * i.1 + 1, by omega⟩
private def pU1 (a : Fin 5 × Bool) : MvPolynomial (Fin 30) ℝ :=
  if a.2 then MvPolynomial.X ⟨6 * a.1.1 + 2, by omega⟩ else MvPolynomial.X ⟨6 * a.1.1 + 4, by omega⟩
private def pU2 (a : Fin 5 × Bool) : MvPolynomial (Fin 30) ℝ :=
  if a.2 then MvPolynomial.X ⟨6 * a.1.1 + 3, by omega⟩ else MvPolynomial.X ⟨6 * a.1.1 + 5, by omega⟩
private def pC (a : Fin 5 × Bool) : MvPolynomial (Fin 30) ℝ :=
  -(pU1 a * pY1 a.1 + pU2 a * pY2 a.1)

private def pDet2 (a b : Fin 5 × Bool) : MvPolynomial (Fin 30) ℝ :=
  pU1 a * pU2 b - pU2 a * pU1 b

private def pDet3 (a b c : Fin 5 × Bool) : MvPolynomial (Fin 30) ℝ :=
  pU1 a * (pU2 b * pC c - pC b * pU2 c) -
  pU2 a * (pU1 b * pC c - pC b * pU1 c) +
  pC a * (pU1 b * pU2 c - pU2 b * pU1 c)

private def pAxisX (a b : Fin 5 × Bool) : MvPolynomial (Fin 30) ℝ :=
  pU2 a * pC b - pU2 b * pC a

private def pAxisY (a b : Fin 5 × Bool) : MvPolynomial (Fin 30) ℝ :=
  pU1 a * pC b - pU1 b * pC a

private lemma eval_decWedge (x : Fin 30 → ℝ) (h_nondeg : ∀ i : Fin 5,
      0 < x ⟨6 * i.1 + 2, by omega⟩ * x ⟨6 * i.1 + 5, by omega⟩ -
          x ⟨6 * i.1 + 3, by omega⟩ * x ⟨6 * i.1 + 4, by omega⟩) :
    let W := decWedge x h_nondeg
    (∀ a : Fin 5 × Bool,
      MvPolynomial.eval x (pU1 a) = (normal W a).1 ∧
      MvPolynomial.eval x (pU2 a) = (normal W a).2 ∧
      MvPolynomial.eval x (pC a) =
        -((normal W a).1 * (W a.1).y.1 + (normal W a).2 * (W a.1).y.2)) := by
  intro W a
  rcases a with ⟨i, ⟨⟩⟩ <;> simp [W, decWedge, normal, pU1, pU2, pC, pY1, pY2]

lemma exists_gp_perturbation
    (W : Fin 5 → OpenWedge)
    (pa pb : ℝ × ℝ)
    (h_apex : ∀ i : Fin 5, (W i).y.1 < 0 ∧ (W i).y.2 < 0)
    (hxa : 0 < pa.1) (hya : pa.2 < 0) (hxb : pb.1 < 0) (hyb : 0 < pb.2)
    (hC : pa.1 * pb.2 - pa.2 * pb.1 < 0)
    (ha : ∀ i : Fin 5, (W i).MemOpen pa) (hb : ∀ i : Fin 5, (W i).MemOpen pb)
    (h_all : ∀ m : Fin 5 → Bool, ∃ z : ℝ × ℝ, inOmega z ∧ RealizesWedgeMask W m z) :
    ∃ W' : Fin 5 → OpenWedge,
      (∀ i : Fin 5, (W' i).y.1 < 0 ∧ (W' i).y.2 < 0) ∧
      (∀ i : Fin 5, (W' i).MemOpen pa) ∧
      (∀ i : Fin 5, (W' i).MemOpen pb) ∧
      (∀ i : Fin 5, isLlt (W' i) pa pb ↔ isLlt (W i) pa pb) ∧
      (∀ i : Fin 5, isLgt (W' i) pa pb ↔ isLgt (W i) pa pb) ∧
      (∀ m : Fin 5 → Bool, ∃ z : ℝ × ℝ, inOmega z ∧ RealizesWedgeMask W' m z) ∧
      GeneralPosition W' := by
  choose zm hzm_om hzm_mask using h_all
  let x₀ := encVec W
  -- Build a neighborhood of `x₀` preserving all strict open inequalities
  let cond : (Fin 30 → ℝ) → Prop := fun x =>
    (∀ i : Fin 5,
      0 < x ⟨6 * i.1 + 2, by omega⟩ * x ⟨6 * i.1 + 5, by omega⟩ -
          x ⟨6 * i.1 + 3, by omega⟩ * x ⟨6 * i.1 + 4, by omega⟩) ∧
    (∀ i : Fin 5, x ⟨6 * i.1, by omega⟩ < 0 ∧ x ⟨6 * i.1 + 1, by omega⟩ < 0) ∧
    (∀ i : Fin 5,
      (0 < x ⟨6 * i.1 + 2, by omega⟩ * (pa.1 - x ⟨6 * i.1, by omega⟩) +
           x ⟨6 * i.1 + 3, by omega⟩ * (pa.2 - x ⟨6 * i.1 + 1, by omega⟩)) ∧
      (0 < x ⟨6 * i.1 + 4, by omega⟩ * (pa.1 - x ⟨6 * i.1, by omega⟩) +
           x ⟨6 * i.1 + 5, by omega⟩ * (pa.2 - x ⟨6 * i.1 + 1, by omega⟩))) ∧
    (∀ i : Fin 5,
      (0 < x ⟨6 * i.1 + 2, by omega⟩ * (pb.1 - x ⟨6 * i.1, by omega⟩) +
           x ⟨6 * i.1 + 3, by omega⟩ * (pb.2 - x ⟨6 * i.1 + 1, by omega⟩)) ∧
      (0 < x ⟨6 * i.1 + 4, by omega⟩ * (pb.1 - x ⟨6 * i.1, by omega⟩) +
           x ⟨6 * i.1 + 5, by omega⟩ * (pb.2 - x ⟨6 * i.1 + 1, by omega⟩))) ∧
    (∀ i : Fin 5,
      ((pb.2 - pa.2) * (W i).y.1 + (pa.1 - pb.1) * (W i).y.2 < pa.1 * pb.2 - pa.2 * pb.1 →
        (pb.2 - pa.2) * x ⟨6 * i.1, by omega⟩ + (pa.1 - pb.1) * x ⟨6 * i.1 + 1, by omega⟩ <
          pa.1 * pb.2 - pa.2 * pb.1) ∧
      (pa.1 * pb.2 - pa.2 * pb.1 < (pb.2 - pa.2) * (W i).y.1 + (pa.1 - pb.1) * (W i).y.2 →
        pa.1 * pb.2 - pa.2 * pb.1 <
          (pb.2 - pa.2) * x ⟨6 * i.1, by omega⟩ + (pa.1 - pb.1) * x ⟨6 * i.1 + 1, by omega⟩)) ∧
    (∀ (m : Fin 5 → Bool) (i : Fin 5),
      if m i then
        0 < x ⟨6 * i.1 + 2, by omega⟩ * ((zm m).1 - x ⟨6 * i.1, by omega⟩) +
            x ⟨6 * i.1 + 3, by omega⟩ * ((zm m).2 - x ⟨6 * i.1 + 1, by omega⟩) ∧
        0 < x ⟨6 * i.1 + 4, by omega⟩ * ((zm m).1 - x ⟨6 * i.1, by omega⟩) +
            x ⟨6 * i.1 + 5, by omega⟩ * ((zm m).2 - x ⟨6 * i.1 + 1, by omega⟩)
      else
        x ⟨6 * i.1 + 2, by omega⟩ * ((zm m).1 - x ⟨6 * i.1, by omega⟩) +
            x ⟨6 * i.1 + 3, by omega⟩ * ((zm m).2 - x ⟨6 * i.1 + 1, by omega⟩) < 0 ∨
        x ⟨6 * i.1 + 4, by omega⟩ * ((zm m).1 - x ⟨6 * i.1, by omega⟩) +
            x ⟨6 * i.1 + 5, by omega⟩ * ((zm m).2 - x ⟨6 * i.1 + 1, by omega⟩) < 0)
  have hopen : IsOpen {x : Fin 30 → ℝ | cond x} := by
    dsimp only [cond]
    rw [Set.setOf_and]; refine IsOpen.inter ?_ ?_
    · rw [Set.setOf_forall]
      refine isOpen_iInter_of_finite fun i => isOpen_lt continuous_const (by fun_prop)
    rw [Set.setOf_and]; refine IsOpen.inter ?_ ?_
    · rw [Set.setOf_forall]
      refine isOpen_iInter_of_finite fun i => ?_
      rw [Set.setOf_and]
      exact (isOpen_lt (by fun_prop) continuous_const).inter (isOpen_lt (by fun_prop) continuous_const)
    rw [Set.setOf_and]; refine IsOpen.inter ?_ ?_
    · rw [Set.setOf_forall]
      refine isOpen_iInter_of_finite fun i => ?_
      rw [Set.setOf_and]
      exact (isOpen_lt continuous_const (by fun_prop)).inter (isOpen_lt continuous_const (by fun_prop))
    rw [Set.setOf_and]; refine IsOpen.inter ?_ ?_
    · rw [Set.setOf_forall]
      refine isOpen_iInter_of_finite fun i => ?_
      rw [Set.setOf_and]
      exact (isOpen_lt continuous_const (by fun_prop)).inter (isOpen_lt continuous_const (by fun_prop))
    rw [Set.setOf_and]; refine IsOpen.inter ?_ ?_
    · rw [Set.setOf_forall]
      refine isOpen_iInter_of_finite fun i => ?_
      rw [Set.setOf_and]
      refine IsOpen.inter ?_ ?_
      · by_cases h : (pb.2 - pa.2) * (W i).y.1 + (pa.1 - pb.1) * (W i).y.2 < pa.1 * pb.2 - pa.2 * pb.1
        · simp [h]; exact isOpen_lt (by fun_prop) continuous_const
        · simp [h]
      · by_cases h : pa.1 * pb.2 - pa.2 * pb.1 < (pb.2 - pa.2) * (W i).y.1 + (pa.1 - pb.1) * (W i).y.2
        · simp [h]; exact isOpen_lt continuous_const (by fun_prop)
        · simp [h]
    · rw [Set.setOf_forall]
      refine isOpen_iInter_of_finite fun m => ?_
      rw [Set.setOf_forall]
      refine isOpen_iInter_of_finite fun i => ?_
      by_cases hmi : m i
      · simp only [hmi, ↓reduceIte]
        rw [Set.setOf_and]
        exact (isOpen_lt continuous_const (by fun_prop)).inter (isOpen_lt continuous_const (by fun_prop))
      · simp only [hmi, Bool.false_eq_true, ↓reduceIte]
        rw [Set.setOf_or]
        exact (isOpen_lt (by fun_prop) continuous_const).union (isOpen_lt (by fun_prop) continuous_const)
  have hx₀_cond : cond x₀ := by
    have hidx : ∀ i, encVec W ⟨6 * i.1, by omega⟩ = (W i).y.1 ∧
        encVec W ⟨6 * i.1 + 1, by omega⟩ = (W i).y.2 ∧
        encVec W ⟨6 * i.1 + 2, by omega⟩ = (W i).u₁.1 ∧
        encVec W ⟨6 * i.1 + 3, by omega⟩ = (W i).u₁.2 ∧
        encVec W ⟨6 * i.1 + 4, by omega⟩ = (W i).u₂.1 ∧
        encVec W ⟨6 * i.1 + 5, by omega⟩ = (W i).u₂.2 := fun i => encVec_idx W i
    refine ⟨fun i => ?_, fun i => ?_, fun i => ?_, fun i => ?_, fun i => ?_, fun m i => ?_⟩
    · rcases hidx i with ⟨_, _, e2, e3, e4, e5⟩
      dsimp [x₀]; rw [e2, e3, e4, e5]; exact (W i).h_nondeg
    · rcases hidx i with ⟨e0, e1, _⟩
      dsimp [x₀]; rw [e0, e1]; exact h_apex i
    · rcases hidx i with ⟨e0, e1, e2, e3, e4, e5⟩
      dsimp [x₀]; rw [e0, e1, e2, e3, e4, e5]; exact ha i
    · rcases hidx i with ⟨e0, e1, e2, e3, e4, e5⟩
      dsimp [x₀]; rw [e0, e1, e2, e3, e4, e5]; exact hb i
    · rcases hidx i with ⟨e0, e1, _⟩
      dsimp [x₀]; rw [e0, e1]; exact ⟨id, id⟩
    · rcases hidx i with ⟨e0, e1, e2, e3, e4, e5⟩
      dsimp [x₀]; rw [e0, e1, e2, e3, e4, e5]
      exact hzm_mask m i
  obtain ⟨δ, hδ_pos, hball⟩ := Metric.isOpen_iff.mp hopen x₀ hx₀_cond
  -- Build finite list of nonzero polynomials for GP
  let P1 : Fin 5 × Bool → MvPolynomial (Fin 30) ℝ := fun a => pU1 a * pU2 a * pC a
  have hP1 : ∀ a, P1 a ≠ 0 := by
    intro a h0
    let v : Fin 30 → ℝ := fun k =>
      if k.1 = 6 * a.1.1 then 1
      else if k.1 = 6 * a.1.1 + 1 then 1
      else if k.1 = 6 * a.1.1 + 2 then 1
      else if k.1 = 6 * a.1.1 + 3 then 1
      else if k.1 = 6 * a.1.1 + 4 then 1
      else if k.1 = 6 * a.1.1 + 5 then 1
      else 0
    have hev : MvPolynomial.eval v (P1 a) = -2 := by
      rcases a with ⟨i, ⟨⟩⟩ <;>
        simp [P1, pU1, pU2, pC, pY1, pY2, v] <;> norm_num
    have hzero : MvPolynomial.eval v (P1 a) = 0 := by rw [h0, map_zero]
    linarith
  let P2 : {p : (Fin 5 × Bool) × (Fin 5 × Bool) // p.1 ≠ p.2} → MvPolynomial (Fin 30) ℝ :=
    fun ⟨⟨a, b⟩, _⟩ => pDet2 a b * pAxisX a b * pAxisY a b
  have hP2 : ∀ q, P2 q ≠ 0 := by
    rintro ⟨⟨a, b⟩, hab⟩ h0
    by_cases hij : a.1 = b.1
    · -- same wedge: `a = (i, true), b = (i, false)` or vice versa
      let v : Fin 30 → ℝ := fun k =>
        if k.1 = 6 * a.1.1 then 1
        else if k.1 = 6 * a.1.1 + 1 then 1
        else if k.1 = 6 * a.1.1 + 2 then 1
        else if k.1 = 6 * a.1.1 + 3 then 0
        else if k.1 = 6 * a.1.1 + 4 then 0
        else if k.1 = 6 * a.1.1 + 5 then 1
        else 0
      -- Wait: if u1=(1,0), u2=(0,1), then pAxisX or pAxisY might vanish!
      -- Better: u1=(1, 2), u2=(3, 1), y=(1, 1) -> c1=-3, c2=-4
      -- det = 1*1 - 2*3 = -5 != 0
      -- axisX = 2*(-4) - 1*(-3) = -5 != 0
      -- axisY = 1*(-4) - 3*(-3) = 5 != 0
      let w : Fin 30 → ℝ := fun k =>
        if k.1 = 6 * a.1.1 then 1
        else if k.1 = 6 * a.1.1 + 1 then 1
        else if k.1 = 6 * a.1.1 + 2 then 1
        else if k.1 = 6 * a.1.1 + 3 then 2
        else if k.1 = 6 * a.1.1 + 4 then 3
        else if k.1 = 6 * a.1.1 + 5 then 1
        else 0
      have hne_b : a.2 ≠ b.2 := fun hb => hab (Prod.ext hij hb)
      have hev : MvPolynomial.eval w (P2 ⟨(a, b), hab⟩) ≠ 0 := by
        rcases a with ⟨i, ⟨⟩⟩ <;> rcases b with ⟨j, ⟨⟩⟩ <;> simp at hij hne_b ⊢
        · subst hij; simp [P2, pDet2, pAxisX, pAxisY, pU1, pU2, pC, pY1, pY2, w]; norm_num
        · subst hij; simp [P2, pDet2, pAxisX, pAxisY, pU1, pU2, pC, pY1, pY2, w]; norm_num
      have hzero : MvPolynomial.eval w (P2 ⟨(a, b), hab⟩) = 0 := by rw [h0, map_zero]
      exact hev hzero
    · -- distinct wedges `a.1 ≠ b.1`
      let w : Fin 30 → ℝ := fun k =>
        if k.1 / 6 = a.1.1 then
          if k.1 % 6 = 0 ∨ k.1 % 6 = 1 ∨ k.1 % 6 = 2 ∨ k.1 % 6 = 4 then 1 else 2
        else if k.1 / 6 = b.1.1 then
          if k.1 % 6 = 0 ∨ k.1 % 6 = 1 ∨ k.1 % 6 = 3 ∨ k.1 % 6 = 5 then 1 else 3
        else 0
      have ha1 : a.1.1 ≠ b.1.1 := fun h => hij (Fin.ext h)
      have ha_idx : ∀ m < 6, (6 * a.1.1 + m) / 6 = a.1.1 ∧ (6 * a.1.1 + m) % 6 = m := by
        intro m hm; omega
      have hb_idx : ∀ m < 6, (6 * b.1.1 + m) / 6 = b.1.1 ∧ (6 * b.1.1 + m) % 6 = m := by
        intro m hm; omega
      have ha_idx0 : (6 * a.1.1) / 6 = a.1.1 ∧ (6 * a.1.1) % 6 = 0 := by omega
      have hb_idx0 : (6 * b.1.1) / 6 = b.1.1 ∧ (6 * b.1.1) % 6 = 0 := by omega
      have hev : MvPolynomial.eval w (P2 ⟨(a, b), hab⟩) ≠ 0 := by
        rcases a with ⟨ia, ba⟩; rcases b with ⟨ib, bb⟩
        dsimp at ha1
        rcases ba with ⟨⟩ <;> rcases bb with ⟨⟩ <;>
        · simp [P2, pDet2, pAxisX, pAxisY, pU1, pU2, pC, pY1, pY2, w,
            ha_idx, hb_idx, ha_idx0, hb_idx0, Ne.symm ha1] <;> norm_num
      have hzero : MvPolynomial.eval w (P2 ⟨(a, b), hab⟩) = 0 := by rw [h0, map_zero]
      exact hev hzero
  -- 3 distinct wedges for `pDet3`, plus apex-not-on-line (`a.1 ≠ b.1`, `y_a` not on line `b`)
  let P3 : {t : (Fin 5 × Bool) × (Fin 5 × Bool) × (Fin 5 × Bool) //
      t.1.1 ≠ t.2.1.1 ∧ t.1.1 ≠ t.2.2.1 ∧ t.2.1.1 ≠ t.2.2.1} → MvPolynomial (Fin 30) ℝ :=
    fun ⟨⟨a, b, c⟩, _⟩ => pDet3 a b c
  have hP3 : ∀ t, P3 t ≠ 0 := by
    rintro ⟨⟨a, b, c⟩, hab, hac, hbc⟩ h0
    let w : Fin 30 → ℝ := fun k =>
      if k.1 / 6 = a.1.1 then
        if k.1 % 6 = 2 ∨ k.1 % 6 = 4 then 1 else 0
      else if k.1 / 6 = b.1.1 then
        if k.1 % 6 = 3 ∨ k.1 % 6 = 5 then 1 else 0
      else if k.1 / 6 = c.1.1 then
        if k.1 % 6 = 0 ∨ k.1 % 6 = 2 ∨ k.1 % 6 = 3 ∨ k.1 % 6 = 4 ∨ k.1 % 6 = 5 then 1 else 0
      else 0
    have hev : MvPolynomial.eval w (pDet3 a b c) = -1 := by
      have ha1 : a.1.1 ≠ b.1.1 := fun h => hab (Fin.ext h)
      have ha2 : a.1.1 ≠ c.1.1 := fun h => hac (Fin.ext h)
      have hb2 : b.1.1 ≠ c.1.1 := fun h => hbc (Fin.ext h)
      rcases a with ⟨ia, ba⟩; rcases b with ⟨ib, bb⟩; rcases c with ⟨ic, bc⟩
      dsimp at ha1 ha2 hb2
      have ha0 : (6 * ia.1) / 6 = ia.1 ∧ (6 * ia.1) % 6 = 0 := by omega
      have ha1' : (6 * ia.1 + 1) / 6 = ia.1 ∧ (6 * ia.1 + 1) % 6 = 1 := by omega
      have ha2' : (6 * ia.1 + 2) / 6 = ia.1 ∧ (6 * ia.1 + 2) % 6 = 2 := by omega
      have ha3' : (6 * ia.1 + 3) / 6 = ia.1 ∧ (6 * ia.1 + 3) % 6 = 3 := by omega
      have ha4' : (6 * ia.1 + 4) / 6 = ia.1 ∧ (6 * ia.1 + 4) % 6 = 4 := by omega
      have ha5' : (6 * ia.1 + 5) / 6 = ia.1 ∧ (6 * ia.1 + 5) % 6 = 5 := by omega
      have hb0 : (6 * ib.1) / 6 = ib.1 ∧ (6 * ib.1) % 6 = 0 := by omega
      have hb1' : (6 * ib.1 + 1) / 6 = ib.1 ∧ (6 * ib.1 + 1) % 6 = 1 := by omega
      have hb2' : (6 * ib.1 + 2) / 6 = ib.1 ∧ (6 * ib.1 + 2) % 6 = 2 := by omega
      have hb3' : (6 * ib.1 + 3) / 6 = ib.1 ∧ (6 * ib.1 + 3) % 6 = 3 := by omega
      have hb4' : (6 * ib.1 + 4) / 6 = ib.1 ∧ (6 * ib.1 + 4) % 6 = 4 := by omega
      have hb5' : (6 * ib.1 + 5) / 6 = ib.1 ∧ (6 * ib.1 + 5) % 6 = 5 := by omega
      have hc0 : (6 * ic.1) / 6 = ic.1 ∧ (6 * ic.1) % 6 = 0 := by omega
      have hc1' : (6 * ic.1 + 1) / 6 = ic.1 ∧ (6 * ic.1 + 1) % 6 = 1 := by omega
      have hc2' : (6 * ic.1 + 2) / 6 = ic.1 ∧ (6 * ic.1 + 2) % 6 = 2 := by omega
      have hc3' : (6 * ic.1 + 3) / 6 = ic.1 ∧ (6 * ic.1 + 3) % 6 = 3 := by omega
      have hc4' : (6 * ic.1 + 4) / 6 = ic.1 ∧ (6 * ic.1 + 4) % 6 = 4 := by omega
      have hc5' : (6 * ic.1 + 5) / 6 = ic.1 ∧ (6 * ic.1 + 5) % 6 = 5 := by omega
      simp only [pDet3, pU1, pU2, pC, pY1, pY2, map_add, map_sub, map_mul, map_neg, MvPolynomial.eval_X]
      rcases ba with ⟨⟩ <;> rcases bb with ⟨⟩ <;> rcases bc with ⟨⟩ <;>
        simp [w, ha0, ha1', ha2', ha3', ha4', ha5', hb0, hb1', hb2', hb3', hb4', hb5',
          hc0, hc1', hc2', hc3', hc4', hc5', Ne.symm ha1, Ne.symm ha2, Ne.symm hb2] <;> norm_num
    have hzero : MvPolynomial.eval w (pDet3 a b c) = 0 := by
      change MvPolynomial.eval w (P3 ⟨(a, b, c), hab, hac, hbc⟩) = 0
      rw [h0, map_zero]
    linarith
  let P4 : {p : Fin 5 × (Fin 5 × Bool) // p.1 ≠ p.2.1} → MvPolynomial (Fin 30) ℝ :=
    fun ⟨⟨i, b⟩, _⟩ => pU1 b * (pY1 i - pY1 b.1) + pU2 b * (pY2 i - pY2 b.1)
  have hP4 : ∀ t, P4 t ≠ 0 := by
    rintro ⟨⟨i, b⟩, hib⟩ h0
    let w : Fin 30 → ℝ := fun k =>
      if k.1 / 6 = i.1 ∧ k.1 % 6 = 0 then 1
      else if k.1 / 6 = b.1.1 ∧ (k.1 % 6 = 2 ∨ k.1 % 6 = 4) then 1
      else 0
    have hev : MvPolynomial.eval w (P4 ⟨(i, b), hib⟩) = 1 := by
      have hne : i.1 ≠ b.1.1 := fun h => hib (Fin.ext h)
      have hi0 : (6 * i.1) / 6 = i.1 ∧ (6 * i.1) % 6 = 0 := by omega
      have hb0 : (6 * b.1.1) / 6 = b.1.1 ∧ (6 * b.1.1) % 6 = 0 := by omega
      have hi1 : (6 * i.1 + 1) / 6 = i.1 ∧ (6 * i.1 + 1) % 6 = 1 := by omega
      have hb1 : (6 * b.1.1 + 1) / 6 = b.1.1 ∧ (6 * b.1.1 + 1) % 6 = 1 := by omega
      have hb2 : (6 * b.1.1 + 2) / 6 = b.1.1 ∧ (6 * b.1.1 + 2) % 6 = 2 := by omega
      have hb3 : (6 * b.1.1 + 3) / 6 = b.1.1 ∧ (6 * b.1.1 + 3) % 6 = 3 := by omega
      have hb4 : (6 * b.1.1 + 4) / 6 = b.1.1 ∧ (6 * b.1.1 + 4) % 6 = 4 := by omega
      have hb5 : (6 * b.1.1 + 5) / 6 = b.1.1 ∧ (6 * b.1.1 + 5) % 6 = 5 := by omega
      rcases b with ⟨ib, bb⟩; dsimp at hne
      rcases bb with ⟨⟩ <;>
        simp [P4, pU1, pU2, pY1, pY2, w, hne, Ne.symm hne, hi0, hb0, hi1, hb1, hb2, hb3, hb4, hb5] <;>
        norm_num
    have hzero : MvPolynomial.eval w (P4 ⟨(i, b), hib⟩) = 0 := by rw [h0, map_zero]
    linarith
  let P_all : MvPolynomial (Fin 30) ℝ :=
    (∏ a, P1 a) * (∏ q, P2 q) * (∏ t, P3 t) * (∏ s, P4 s)
  have hP_all : P_all ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero (mul_ne_zero ?_ ?_) ?_) ?_
    · exact Finset.prod_ne_zero_iff.mpr fun a _ => hP1 a
    · exact Finset.prod_ne_zero_iff.mpr fun q _ => hP2 q
    · exact Finset.prod_ne_zero_iff.mpr fun t _ => hP3 t
    · exact Finset.prod_ne_zero_iff.mpr fun s _ => hP4 s
  obtain ⟨x, hx_box, hx_poly⟩ :=
    poly_dense_box 30 (fun k => x₀ k - δ / 2) (fun k => x₀ k + δ / 2)
      (fun k => by linarith) P_all hP_all
  have hx_dist : dist x x₀ < δ := by
    rw [dist_pi_lt_iff hδ_pos]
    intro k
    have hk := hx_box k
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith [hk.1, hk.2]
  have hx_cond : cond x := hball hx_dist
  let W' := decWedge x hx_cond.1
  have hW'_eval := eval_decWedge x hx_cond.1
  have hx_prod :
      MvPolynomial.eval x (∏ a, P1 a) ≠ 0 ∧
      MvPolynomial.eval x (∏ q, P2 q) ≠ 0 ∧
      MvPolynomial.eval x (∏ t, P3 t) ≠ 0 ∧
      MvPolynomial.eval x (∏ s, P4 s) ≠ 0 := by
    dsimp only [P_all] at hx_poly
    rw [map_mul, map_mul, map_mul] at hx_poly
    exact ⟨left_ne_zero_of_mul (left_ne_zero_of_mul (left_ne_zero_of_mul hx_poly)),
           right_ne_zero_of_mul (left_ne_zero_of_mul (left_ne_zero_of_mul hx_poly)),
           right_ne_zero_of_mul (left_ne_zero_of_mul hx_poly),
           right_ne_zero_of_mul hx_poly⟩
  have hP1_ne : ∀ a, MvPolynomial.eval x (P1 a) ≠ 0 := by
    intro a h0
    apply hx_prod.1
    rw [map_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ a) h0
  have hP2_ne : ∀ q, MvPolynomial.eval x (P2 q) ≠ 0 := by
    intro q h0
    apply hx_prod.2.1
    rw [map_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ q) h0
  have hP3_ne : ∀ t, MvPolynomial.eval x (P3 t) ≠ 0 := by
    intro t h0
    apply hx_prod.2.2.1
    rw [map_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ t) h0
  have hP4_ne : ∀ s, MvPolynomial.eval x (P4 s) ≠ 0 := by
    intro s h0
    apply hx_prod.2.2.2
    rw [map_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ s) h0
  refine ⟨W', hx_cond.2.1, hx_cond.2.2.1, hx_cond.2.2.2.1, ?_, ?_, ?_, ?_⟩
  · intro i
    constructor
    · intro hlt'
      rcases caseB_dichotomy (W i) pa pb (h_apex i).1 (h_apex i).2 hxa hya hxb hyb hC (ha i) (hb i)
        with hlt | hgt
      · exact hlt
      · have hgt' := (hx_cond.2.2.2.2.1 i).2 hgt
        dsimp [isLlt, W', decWedge] at hlt'
        linarith
    · exact (hx_cond.2.2.2.2.1 i).1
  · intro i
    constructor
    · intro hgt'
      rcases caseB_dichotomy (W i) pa pb (h_apex i).1 (h_apex i).2 hxa hya hxb hyb hC (ha i) (hb i)
        with hlt | hgt
      · have hlt' := (hx_cond.2.2.2.2.1 i).1 hlt
        dsimp [isLgt, W', decWedge] at hgt'
        linarith
      · exact hgt
    · exact (hx_cond.2.2.2.2.1 i).2
  · intro m
    exact ⟨zm m, hzm_om m, hx_cond.2.2.2.2.2 m⟩
  · constructor
    · intro a
      have hp1 := hP1_ne a
      rcases hW'_eval a with ⟨e1, e2, _⟩
      simp only [P1, map_mul, e1, e2] at hp1
      exact ⟨left_ne_zero_of_mul (left_ne_zero_of_mul hp1),
             right_ne_zero_of_mul (left_ne_zero_of_mul hp1)⟩
    · intro a b hab
      have hp2 := hP2_ne ⟨(a, b), hab⟩
      rcases hW'_eval a with ⟨ea1, ea2, _⟩
      rcases hW'_eval b with ⟨eb1, eb2, _⟩
      simp only [P2, pDet2, map_mul, map_sub, ea1, ea2, eb1, eb2] at hp2
      exact left_ne_zero_of_mul (left_ne_zero_of_mul hp2)
    · intro a b c hab hac hbc p ⟨ha0, hb0, hc0⟩
      have same_wedge_eq : ∀ u v : Fin 5 × Bool, u ≠ v → u.1 = v.1 →
          lineAt W' u p = 0 → lineAt W' v p = 0 → p = (W' u.1).y := by
        intro u v huv huv1 hu0 hv0
        have hnd := (W' u.1).h_nondeg
        have huv2 : u.2 ≠ v.2 := fun h => huv (Prod.ext huv1 h)
        rcases u with ⟨iu, bu⟩; rcases v with ⟨iv, bv⟩
        dsimp at huv1 huv2; subst huv1
        rcases bu with ⟨⟩ <;> rcases bv with ⟨⟩
        · exact False.elim (huv2 rfl)
        · simp only [lineAt, normal, ite_true, ite_false, Bool.false_eq_true] at hu0 hv0
          have hdet : (W' iu).u₁.1 * (W' iu).u₂.2 - (W' iu).u₁.2 * (W' iu).u₂.1 ≠ 0 := ne_of_gt hnd
          have hx_zero : ((W' iu).u₁.1 * (W' iu).u₂.2 - (W' iu).u₁.2 * (W' iu).u₂.1) * (p.1 - (W' iu).y.1) = 0 := by
            calc ((W' iu).u₁.1 * (W' iu).u₂.2 - (W' iu).u₁.2 * (W' iu).u₂.1) * (p.1 - (W' iu).y.1)
                = (W' iu).u₂.2 * ((W' iu).u₁.1 * (p.1 - (W' iu).y.1) + (W' iu).u₁.2 * (p.2 - (W' iu).y.2)) -
                  (W' iu).u₁.2 * ((W' iu).u₂.1 * (p.1 - (W' iu).y.1) + (W' iu).u₂.2 * (p.2 - (W' iu).y.2)) := by ring
              _ = 0 := by rw [hu0, hv0]; ring
          have hy_zero : ((W' iu).u₁.1 * (W' iu).u₂.2 - (W' iu).u₁.2 * (W' iu).u₂.1) * (p.2 - (W' iu).y.2) = 0 := by
            calc ((W' iu).u₁.1 * (W' iu).u₂.2 - (W' iu).u₁.2 * (W' iu).u₂.1) * (p.2 - (W' iu).y.2)
                = -(W' iu).u₂.1 * ((W' iu).u₁.1 * (p.1 - (W' iu).y.1) + (W' iu).u₁.2 * (p.2 - (W' iu).y.2)) +
                  (W' iu).u₁.1 * ((W' iu).u₂.1 * (p.1 - (W' iu).y.1) + (W' iu).u₂.2 * (p.2 - (W' iu).y.2)) := by ring
              _ = 0 := by rw [hu0, hv0]; ring
          exact Prod.ext (sub_eq_zero.mp ((mul_eq_zero.mp hx_zero).resolve_left hdet))
                         (sub_eq_zero.mp ((mul_eq_zero.mp hy_zero).resolve_left hdet))
        · simp only [lineAt, normal, ite_true, ite_false, Bool.false_eq_true] at hu0 hv0
          have hdet : (W' iu).u₁.1 * (W' iu).u₂.2 - (W' iu).u₁.2 * (W' iu).u₂.1 ≠ 0 := ne_of_gt hnd
          have hx_zero : ((W' iu).u₁.1 * (W' iu).u₂.2 - (W' iu).u₁.2 * (W' iu).u₂.1) * (p.1 - (W' iu).y.1) = 0 := by
            calc ((W' iu).u₁.1 * (W' iu).u₂.2 - (W' iu).u₁.2 * (W' iu).u₂.1) * (p.1 - (W' iu).y.1)
                = (W' iu).u₂.2 * ((W' iu).u₁.1 * (p.1 - (W' iu).y.1) + (W' iu).u₁.2 * (p.2 - (W' iu).y.2)) -
                  (W' iu).u₁.2 * ((W' iu).u₂.1 * (p.1 - (W' iu).y.1) + (W' iu).u₂.2 * (p.2 - (W' iu).y.2)) := by ring
              _ = 0 := by rw [hv0, hu0]; ring
          have hy_zero : ((W' iu).u₁.1 * (W' iu).u₂.2 - (W' iu).u₁.2 * (W' iu).u₂.1) * (p.2 - (W' iu).y.2) = 0 := by
            calc ((W' iu).u₁.1 * (W' iu).u₂.2 - (W' iu).u₁.2 * (W' iu).u₂.1) * (p.2 - (W' iu).y.2)
                = -(W' iu).u₂.1 * ((W' iu).u₁.1 * (p.1 - (W' iu).y.1) + (W' iu).u₁.2 * (p.2 - (W' iu).y.2)) +
                  (W' iu).u₁.1 * ((W' iu).u₂.1 * (p.1 - (W' iu).y.1) + (W' iu).u₂.2 * (p.2 - (W' iu).y.2)) := by ring
              _ = 0 := by rw [hv0, hu0]; ring
          exact Prod.ext (sub_eq_zero.mp ((mul_eq_zero.mp hx_zero).resolve_left hdet))
                         (sub_eq_zero.mp ((mul_eq_zero.mp hy_zero).resolve_left hdet))
        · exact False.elim (huv2 rfl)
      by_cases h1 : a.1 = b.1
      · have hp_eq : p = (W' a.1).y := same_wedge_eq a b hab h1 ha0 hb0
        have hca : a.1 ≠ c.1 := by
          intro hca
          have hab2 : a.2 ≠ b.2 := fun h => hab (Prod.ext h1 h)
          have hac2 : a.2 ≠ c.2 := fun h => hac (Prod.ext hca h)
          have hbc2 : b.2 ≠ c.2 := fun h => hbc (Prod.ext (h1.symm.trans hca) h)
          revert hab2 hac2 hbc2
          cases a.2 <;> cases b.2 <;> cases c.2 <;> decide
        have hp4 := hP4_ne ⟨(a.1, c), hca⟩
        rcases hW'_eval c with ⟨ec1, ec2, _⟩
        simp only [P4, map_add, map_mul, map_sub, pY1, pY2, MvPolynomial.eval_X, ec1, ec2] at hp4
        apply hp4
        rw [hp_eq] at hc0
        exact hc0
      · by_cases h2 : a.1 = c.1
        · have hp_eq : p = (W' a.1).y := same_wedge_eq a c hac h2 ha0 hc0
          have hp4 := hP4_ne ⟨(a.1, b), h1⟩
          rcases hW'_eval b with ⟨eb1, eb2, _⟩
          simp only [P4, map_add, map_mul, map_sub, pY1, pY2, MvPolynomial.eval_X, eb1, eb2] at hp4
          apply hp4
          rw [hp_eq] at hb0
          exact hb0
        · by_cases h3 : b.1 = c.1
          · have hp_eq : p = (W' b.1).y := same_wedge_eq b c hbc h3 hb0 hc0
            have hba : b.1 ≠ a.1 := fun h => h1 h.symm
            have hp4 := hP4_ne ⟨(b.1, a), hba⟩
            rcases hW'_eval a with ⟨ea1, ea2, _⟩
            simp only [P4, map_add, map_mul, map_sub, pY1, pY2, MvPolynomial.eval_X, ea1, ea2] at hp4
            apply hp4
            rw [hp_eq] at ha0
            exact ha0
          · have hp3 := hP3_ne ⟨(a, b, c), h1, h2, h3⟩
            rcases hW'_eval a with ⟨ea1, ea2, ea3⟩
            rcases hW'_eval b with ⟨eb1, eb2, eb3⟩
            rcases hW'_eval c with ⟨ec1, ec2, ec3⟩
            simp only [P3, pDet3, map_add, map_sub, map_mul, ea1, ea2, ea3, eb1, eb2, eb3, ec1, ec2, ec3] at hp3
            apply hp3
            dsimp [lineAt] at ha0 hb0 hc0
            have hca : -((normal W' a).1 * (W' a.1).y.1 + (normal W' a).2 * (W' a.1).y.2) =
                -((normal W' a).1 * p.1 + (normal W' a).2 * p.2) := by linarith
            have hcb : -((normal W' b).1 * (W' b.1).y.1 + (normal W' b).2 * (W' b.1).y.2) =
                -((normal W' b).1 * p.1 + (normal W' b).2 * p.2) := by linarith
            have hcc : -((normal W' c).1 * (W' c.1).y.1 + (normal W' c).2 * (W' c.1).y.2) =
                -((normal W' c).1 * p.1 + (normal W' c).2 * p.2) := by linarith
            rw [hca, hcb, hcc]; ring
    · intro a b hab p ha0 hb0
      have hp2 := hP2_ne ⟨(a, b), hab⟩
      rcases hW'_eval a with ⟨ea1, ea2, ea3⟩
      rcases hW'_eval b with ⟨eb1, eb2, eb3⟩
      simp only [P2, pAxisX, pAxisY, map_mul, map_sub, ea1, ea2, ea3, eb1, eb2, eb3] at hp2
      have hax : (normal W' a).2 * (-((normal W' b).1 * (W' b.1).y.1 + (normal W' b).2 * (W' b.1).y.2)) -
          (normal W' b).2 * (-((normal W' a).1 * (W' a.1).y.1 + (normal W' a).2 * (W' a.1).y.2)) ≠ 0 :=
        right_ne_zero_of_mul (left_ne_zero_of_mul hp2)
      have hay : (normal W' a).1 * (-((normal W' b).1 * (W' b.1).y.1 + (normal W' b).2 * (W' b.1).y.2)) -
          (normal W' b).1 * (-((normal W' a).1 * (W' a.1).y.1 + (normal W' a).2 * (W' a.1).y.2)) ≠ 0 :=
        right_ne_zero_of_mul hp2
      dsimp [lineAt] at ha0 hb0
      constructor
      · intro hp1
        apply hax
        rw [hp1] at ha0 hb0
        linear_combination (normal W' a).2 * hb0 - (normal W' b).2 * ha0
      · intro hp2_zero
        apply hay
        rw [hp2_zero] at ha0 hb0
        linear_combination (normal W' a).1 * hb0 - (normal W' b).1 * ha0
    · intro a ha0
      have hp1 := hP1_ne a
      rcases hW'_eval a with ⟨e1, e2, e3⟩
      simp only [P1, map_mul] at hp1
      have hc : MvPolynomial.eval x (pC a) ≠ 0 := right_ne_zero_of_mul hp1
      rw [e3] at hc
      apply hc
      dsimp [lineAt] at ha0
      linarith

end CaseB
end
