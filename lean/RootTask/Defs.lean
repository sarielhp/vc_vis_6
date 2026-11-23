import Mathlib

open scoped Classical BigOperators
open Finset

noncomputable section

structure VFunc where
  a : ℝ
  b : ℝ
  c : ℝ
  d : ℝ
  hle : a ≤ c

def VFunc.eval (f : VFunc) (x : ℝ) : ℝ :=
  max (f.a * x + f.b) (f.c * x + f.d)

def RealizesVMask (f : Fin 5 → VFunc) (m : Fin 5 → Bool) (p : ℝ × ℝ) : Prop :=
  ∀ i : Fin 5, if m i then (f i).eval p.1 < p.2 else p.2 < (f i).eval p.1

structure OpenWedge where
  y : ℝ × ℝ
  u₁ : ℝ × ℝ
  u₂ : ℝ × ℝ
  h_nondeg : 0 < u₁.1 * u₂.2 - u₁.2 * u₂.1

def OpenWedge.MemOpen (W : OpenWedge) (p : ℝ × ℝ) : Prop :=
  0 < W.u₁.1 * (p.1 - W.y.1) + W.u₁.2 * (p.2 - W.y.2) ∧
  0 < W.u₂.1 * (p.1 - W.y.1) + W.u₂.2 * (p.2 - W.y.2)

def OpenWedge.MemExt (W : OpenWedge) (p : ℝ × ℝ) : Prop :=
  W.u₁.1 * (p.1 - W.y.1) + W.u₁.2 * (p.2 - W.y.2) < 0 ∨
  W.u₂.1 * (p.1 - W.y.1) + W.u₂.2 * (p.2 - W.y.2) < 0

def RealizesWedgeMask (W : Fin 5 → OpenWedge) (m : Fin 5 → Bool) (p : ℝ × ℝ) : Prop :=
  ∀ i : Fin 5, if m i then (W i).MemOpen p else (W i).MemExt p

lemma vertical_barrier_disjoint_vmask (f : Fin 5 → VFunc) (m : Fin 5 → Bool)
    (x₀ y : ℝ) (i j : Fin 5) (hi : m i = true) (hj : m j = false)
    (hbar : (f j).eval x₀ ≤ (f i).eval x₀) :
    ¬ RealizesVMask f m (x₀, y) := by
  intro hm
  have h1 : (f i).eval x₀ < y := by
    have := hm i
    simpa [hi] using this
  have h2 : y < (f j).eval x₀ := by
    have := hm j
    simpa [hj] using this
  linarith

/-- Convexity of each V-function `f.eval`. -/
lemma vfunc_convex_on_segment (f : VFunc) (x₁ x₂ t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    f.eval ((1 - t) * x₁ + t * x₂) ≤ (1 - t) * f.eval x₁ + t * f.eval x₂ := by
  unfold VFunc.eval
  have ht1' : 0 ≤ 1 - t := sub_nonneg.mpr ht1
  refine max_le ?_ ?_
  · calc
      f.a * ((1 - t) * x₁ + t * x₂) + f.b
          = (1 - t) * (f.a * x₁ + f.b) + t * (f.a * x₂ + f.b) := by ring
      _ ≤ (1 - t) * max (f.a * x₁ + f.b) (f.c * x₁ + f.d) +
            t * max (f.a * x₂ + f.b) (f.c * x₂ + f.d) :=
          add_le_add (mul_le_mul_of_nonneg_left (le_max_left _ _) ht1')
                     (mul_le_mul_of_nonneg_left (le_max_left _ _) ht0)
  · calc
      f.c * ((1 - t) * x₁ + t * x₂) + f.d
          = (1 - t) * (f.c * x₁ + f.d) + t * (f.c * x₂ + f.d) := by ring
      _ ≤ (1 - t) * max (f.a * x₁ + f.b) (f.c * x₁ + f.d) +
            t * max (f.a * x₂ + f.b) (f.c * x₂ + f.d) :=
          add_le_add (mul_le_mul_of_nonneg_left (le_max_right _ _) ht1')
                     (mul_le_mul_of_nonneg_left (le_max_right _ _) ht0)


/-! ## Part 1: Exact 3-Crossing Apex Order (`xf* < xg*`) -/

lemma three_crossings_strict_apex_order (f g : VFunc) (x₀ x₁ x₂ x₃ : ℝ)
    (hf : f.a < f.c) (hg : g.a < g.c)
    (ha : f.a < g.a) (hc : f.c < g.c)
    (hx01 : x₀ < x₁) (hx12 : x₁ < x₂) (hx23 : x₂ < x₃)
    (h0 : g.eval x₀ < f.eval x₀) (h1 : f.eval x₁ < g.eval x₁)
    (h2 : g.eval x₂ < f.eval x₂) (h3 : f.eval x₃ < g.eval x₃) :
    (f.b - f.d) / (f.c - f.a) < (g.b - g.d) / (g.c - g.a) ∧
    (f.b - f.d) / (f.c - f.a) < x₂ ∧
    x₁ < (g.b - g.d) / (g.c - g.a) := by
  unfold VFunc.eval at *
  have hfc_pos : 0 < f.c - f.a := sub_pos.mpr hf
  have hgc_pos : 0 < g.c - g.a := sub_pos.mpr hg
  have hf_x2_right : f.a * x₂ + f.b < f.c * x₂ + f.d := by
    by_contra hle2
    replace hle2 : f.c * x₂ + f.d ≤ f.a * x₂ + f.b := not_lt.mp hle2
    have hf_x2 : max (f.a * x₂ + f.b) (f.c * x₂ + f.d) = f.a * x₂ + f.b := max_eq_left hle2
    have hga_x2 : g.a * x₂ + g.b < f.a * x₂ + f.b := by
      have := le_max_left (g.a * x₂ + g.b) (g.c * x₂ + g.d); linarith
    have hle0 : f.c * x₀ + f.d ≤ f.a * x₀ + f.b := by nlinarith
    have hf_x0 : max (f.a * x₀ + f.b) (f.c * x₀ + f.d) = f.a * x₀ + f.b := max_eq_left hle0
    have hga_x0 : g.a * x₀ + g.b < f.a * x₀ + f.b := by
      have := le_max_left (g.a * x₀ + g.b) (g.c * x₀ + g.d); linarith
    rcases le_total (g.a * x₁ + g.b) (g.c * x₁ + g.d) with hg1 | hg1
    · have hg_x1 : max (g.a * x₁ + g.b) (g.c * x₁ + g.d) = g.c * x₁ + g.d := max_eq_right hg1
      have hfa_x1 : f.a * x₁ + f.b < g.c * x₁ + g.d := by
        have := le_max_left (f.a * x₁ + f.b) (f.c * x₁ + f.d); linarith
      have hgc_x2 : g.c * x₂ + g.d < f.a * x₂ + f.b := by
        have := le_max_right (g.a * x₂ + g.b) (g.c * x₂ + g.d); linarith
      nlinarith
    · have hg_x1 : max (g.a * x₁ + g.b) (g.c * x₁ + g.d) = g.a * x₁ + g.b := max_eq_left hg1
      have hfa_x1 : f.a * x₁ + f.b < g.a * x₁ + g.b := by
        have := le_max_left (f.a * x₁ + f.b) (f.c * x₁ + f.d); linarith
      nlinarith
  have hg_x1_left : g.c * x₁ + g.d < g.a * x₁ + g.b := by
    by_contra hle1
    replace hle1 : g.a * x₁ + g.b ≤ g.c * x₁ + g.d := not_lt.mp hle1
    have hg_x1 : max (g.a * x₁ + g.b) (g.c * x₁ + g.d) = g.c * x₁ + g.d := max_eq_right hle1
    have hfc_x1 : f.c * x₁ + f.d < g.c * x₁ + g.d := by
      have := le_max_right (f.a * x₁ + f.b) (f.c * x₁ + f.d); linarith
    have hle3 : g.a * x₃ + g.b ≤ g.c * x₃ + g.d := by nlinarith
    have hg_x3 : max (g.a * x₃ + g.b) (g.c * x₃ + g.d) = g.c * x₃ + g.d := max_eq_right hle3
    have hfc_x3 : f.c * x₃ + f.d < g.c * x₃ + g.d := by
      have hle_max := le_max_right (f.a * x₃ + f.b) (f.c * x₃ + f.d)
      linarith [h3, hg_x3, hle_max]
    have hfc_x2 : f.c * x₂ + f.d < g.c * x₂ + g.d := by nlinarith
    have hf_x2 : max (f.a * x₂ + f.b) (f.c * x₂ + f.d) = f.c * x₂ + f.d := max_eq_right (le_of_lt hf_x2_right)
    have hle_g2 := le_max_right (g.a * x₂ + g.b) (g.c * x₂ + g.d)
    linarith [h2, hf_x2, hle_g2]
  have hxf_lt_x2 : (f.b - f.d) / (f.c - f.a) < x₂ := by
    rw [div_lt_iff₀ hfc_pos]; linarith
  have hx1_lt_xg : x₁ < (g.b - g.d) / (g.c - g.a) := by
    rw [lt_div_iff₀ hgc_pos]; linarith
  have hxf_lt_xg : (f.b - f.d) / (f.c - f.a) < (g.b - g.d) / (g.c - g.a) := by
    by_contra hge
    replace hge : (g.b - g.d) / (g.c - g.a) ≤ (f.b - f.d) / (f.c - f.a) := not_lt.mp hge
    have hxf_eq : f.a * ((f.b - f.d) / (f.c - f.a)) + f.b = f.c * ((f.b - f.d) / (f.c - f.a)) + f.d := by
      have hne : f.c - f.a ≠ 0 := ne_of_gt hfc_pos
      field_simp [hne]; ring
    have hxg_le_xf : g.a * ((f.b - f.d) / (f.c - f.a)) + g.b ≤ g.c * ((f.b - f.d) / (f.c - f.a)) + g.d := by
      have h1 : g.b - g.d ≤ ((f.b - f.d) / (f.c - f.a)) * (g.c - g.a) := (div_le_iff₀ hgc_pos).mp hge
      linarith
    have hg_x2_right : g.a * x₂ + g.b < g.c * x₂ + g.d := by
      have h1 : (g.b - g.d) / (g.c - g.a) < x₂ := lt_of_le_of_lt hge hxf_lt_x2
      have h2' : g.b - g.d < x₂ * (g.c - g.a) := (div_lt_iff₀ hgc_pos).mp h1
      linarith
    have hgc_lt_fc_x2 : g.c * x₂ + g.d < f.c * x₂ + f.d := by
      have hg2 : max (g.a * x₂ + g.b) (g.c * x₂ + g.d) = g.c * x₂ + g.d := max_eq_right (le_of_lt hg_x2_right)
      have hf2 : max (f.a * x₂ + f.b) (f.c * x₂ + f.d) = f.c * x₂ + f.d := max_eq_right (le_of_lt hf_x2_right)
      linarith
    have hgc_lt_fc_xf : g.c * ((f.b - f.d) / (f.c - f.a)) + g.d < f.c * ((f.b - f.d) / (f.c - f.a)) + f.d := by
      nlinarith
    have hga_lt_fa_xf : g.a * ((f.b - f.d) / (f.c - f.a)) + g.b < f.a * ((f.b - f.d) / (f.c - f.a)) + f.b := by
      linarith
    have hx1_lt_xf : x₁ < (f.b - f.d) / (f.c - f.a) := lt_of_lt_of_le hx1_lt_xg hge
    have hga_lt_fa_x1 : g.a * x₁ + g.b < f.a * x₁ + f.b := by
      nlinarith
    have hg1 : max (g.a * x₁ + g.b) (g.c * x₁ + g.d) = g.a * x₁ + g.b := max_eq_left (le_of_lt hg_x1_left)
    have hf1 : f.a * x₁ + f.b ≤ max (f.a * x₁ + f.b) (f.c * x₁ + f.d) := le_max_left _ _
    linarith
  exact ⟨hxf_lt_xg, hxf_lt_x2, hx1_lt_xg⟩

/-! ## Part 2: Projective Chart Reduction (`Theorem 1(1) -> Theorem 1(2)`) -/

def toVFunc (α β γ δ : ℝ) : VFunc :=
  if h : α ≤ γ then ⟨α, β, γ, δ, h⟩
  else ⟨γ, δ, α, β, le_of_not_ge h⟩

lemma toVFunc_eval (α β γ δ x : ℝ) :
    (toVFunc α β γ δ).eval x = max (α * x + β) (γ * x + δ) := by
  unfold toVFunc VFunc.eval
  split_ifs
  · rfl
  · exact max_comm _ _

private lemma halfplane_proj_ident (u1 u2 y1 y2 p1 p2 : ℝ)
    (hc : 0 < u1 * (-y1) + u2 * (-y2)) (hp : 0 < p2) :
    let c := u1 * (-y1) + u2 * (-y2)
    u1 * (p1 - y1) + u2 * (p2 - y2) =
      (c * p2) * (1 / p2 - ((-u1 / c) * (p1 / p2) + (-u2 / c))) := by
  intro c
  have hc_ne : c ≠ 0 := ne_of_gt hc
  have hp_ne : p2 ≠ 0 := ne_of_gt hp
  field_simp [hc_ne, hp_ne]
  dsimp [c]
  ring

lemma proj_chart_wedge_iff_vfunc (W : OpenWedge) (h0 : W.MemOpen (0, 0))
    (p : ℝ × ℝ) (hp : 0 < p.2) :
    let c₁ := W.u₁.1 * (-W.y.1) + W.u₁.2 * (-W.y.2)
    let c₂ := W.u₂.1 * (-W.y.1) + W.u₂.2 * (-W.y.2)
    let f : VFunc := toVFunc (-W.u₁.1 / c₁) (-W.u₁.2 / c₁) (-W.u₂.1 / c₂) (-W.u₂.2 / c₂)
    let q : ℝ × ℝ := (p.1 / p.2, 1 / p.2)
    (W.MemOpen p ↔ f.eval q.1 < q.2) ∧ (W.MemExt p ↔ q.2 < f.eval q.1) := by
  intro c₁ c₂ f q
  have hc1 : 0 < c₁ := by simpa [c₁, OpenWedge.MemOpen] using h0.1
  have hc2 : 0 < c₂ := by simpa [c₂, OpenWedge.MemOpen] using h0.2
  have hcp1 : 0 < c₁ * p.2 := mul_pos hc1 hp
  have hcp2 : 0 < c₂ * p.2 := mul_pos hc2 hp
  have hid1 := halfplane_proj_ident W.u₁.1 W.u₁.2 W.y.1 W.y.2 p.1 p.2 hc1 hp
  have hid2 := halfplane_proj_ident W.u₂.1 W.u₂.2 W.y.1 W.y.2 p.1 p.2 hc2 hp
  have heval : f.eval q.1 = max ((-W.u₁.1 / c₁) * (p.1 / p.2) + (-W.u₁.2 / c₁))
                                ((-W.u₂.1 / c₂) * (p.1 / p.2) + (-W.u₂.2 / c₂)) :=
    toVFunc_eval _ _ _ _ _
  have h1_pos : 0 < W.u₁.1 * (p.1 - W.y.1) + W.u₁.2 * (p.2 - W.y.2) ↔
      (-W.u₁.1 / c₁) * (p.1 / p.2) + (-W.u₁.2 / c₁) < 1 / p.2 := by
    rw [hid1]
    constructor <;> intro h <;> nlinarith
  have h2_pos : 0 < W.u₂.1 * (p.1 - W.y.1) + W.u₂.2 * (p.2 - W.y.2) ↔
      (-W.u₂.1 / c₂) * (p.1 / p.2) + (-W.u₂.2 / c₂) < 1 / p.2 := by
    rw [hid2]
    constructor <;> intro h <;> nlinarith
  have h1_neg : W.u₁.1 * (p.1 - W.y.1) + W.u₁.2 * (p.2 - W.y.2) < 0 ↔
      1 / p.2 < (-W.u₁.1 / c₁) * (p.1 / p.2) + (-W.u₁.2 / c₁) := by
    rw [hid1]
    constructor <;> intro h <;> nlinarith
  have h2_neg : W.u₂.1 * (p.1 - W.y.1) + W.u₂.2 * (p.2 - W.y.2) < 0 ↔
      1 / p.2 < (-W.u₂.1 / c₂) * (p.1 / p.2) + (-W.u₂.2 / c₂) := by
    rw [hid2]
    constructor <;> intro h <;> nlinarith
  unfold OpenWedge.MemOpen OpenWedge.MemExt
  rw [heval]
  dsimp [q]
  rw [max_lt_iff, lt_max_iff, h1_pos, h2_pos, h1_neg, h2_neg]
  exact ⟨Iff.rfl, Iff.rfl⟩

lemma inter_line_of_pos_neg_in_wedges (W : Fin 5 → OpenWedge) (pm pp : ℝ × ℝ)
    (hpm : pm.2 ≤ 0) (hpp : 0 < pp.2)
    (hm : ∀ i : Fin 5, (W i).MemOpen pm)
    (hp : ∀ i : Fin 5, (W i).MemOpen pp) :
    ∃ x₀ : ℝ, ∀ i : Fin 5, (W i).MemOpen (x₀, 0) := by
  have hden : 0 < pp.2 - pm.2 := by linarith
  let t : ℝ := -pm.2 / (pp.2 - pm.2)
  have ht0 : 0 ≤ t := div_nonneg (by linarith) (le_of_lt hden)
  have ht1 : 0 < 1 - t := by
    have : 1 - t = pp.2 / (pp.2 - pm.2) := by
      dsimp [t]; field_simp [ne_of_gt hden]; ring
    rw [this]; exact div_pos hpp hden
  have hy0 : (1 - t) * pm.2 + t * pp.2 = 0 := by
    dsimp [t]; field_simp [ne_of_gt hden]; ring
  refine ⟨(1 - t) * pm.1 + t * pp.1, fun i => ?_⟩
  obtain ⟨hm1, hm2⟩ := hm i
  obtain ⟨hp1, hp2⟩ := hp i
  unfold OpenWedge.MemOpen
  constructor
  · have hlin : (W i).u₁.1 * (((1 - t) * pm.1 + t * pp.1) - (W i).y.1) +
        (W i).u₁.2 * (0 - (W i).y.2) =
        (1 - t) * ((W i).u₁.1 * (pm.1 - (W i).y.1) + (W i).u₁.2 * (pm.2 - (W i).y.2)) +
        t * ((W i).u₁.1 * (pp.1 - (W i).y.1) + (W i).u₁.2 * (pp.2 - (W i).y.2)) := by
      linear_combination -(W i).u₁.2 * hy0
    rw [hlin]; nlinarith
  · have hlin : (W i).u₂.1 * (((1 - t) * pm.1 + t * pp.1) - (W i).y.1) +
        (W i).u₂.2 * (0 - (W i).y.2) =
        (1 - t) * ((W i).u₂.1 * (pm.1 - (W i).y.1) + (W i).u₂.2 * (pm.2 - (W i).y.2)) +
        t * ((W i).u₂.1 * (pp.1 - (W i).y.1) + (W i).u₂.2 * (pp.2 - (W i).y.2)) := by
      linear_combination -(W i).u₂.2 * hy0
    rw [hlin]; nlinarith

theorem thm1_part2_upper_halfplane
    (h_thm1 : ∀ f : Fin 5 → VFunc, ¬ (∀ m : Fin 5 → Bool, ∃ q : ℝ × ℝ, RealizesVMask f m q))
    (W : Fin 5 → OpenWedge)
    (h_all_in_H : ∀ m : Fin 5 → Bool, ∃ p : ℝ × ℝ, 0 < p.2 ∧ RealizesWedgeMask W m p) :
    ¬ (∃ pm : ℝ × ℝ, pm.2 ≤ 0 ∧ ∀ i : Fin 5, (W i).MemOpen pm) := by
  rintro ⟨pm, hpm, hm⟩
  obtain ⟨pp, hpp, hpp_mask⟩ := h_all_in_H (fun _ => true)
  have hp : ∀ i : Fin 5, (W i).MemOpen pp := fun i => by simpa using hpp_mask i
  obtain ⟨x₀, hx₀⟩ := inter_line_of_pos_neg_in_wedges W pm pp hpm hpp hm hp
  let W' : Fin 5 → OpenWedge := fun i =>
    { y := ((W i).y.1 - x₀, (W i).y.2)
      u₁ := (W i).u₁
      u₂ := (W i).u₂
      h_nondeg := (W i).h_nondeg }
  have h0' : ∀ i : Fin 5, (W' i).MemOpen (0, 0) := by
    intro i
    obtain ⟨h1, h2⟩ := hx₀ i
    refine ⟨?_, ?_⟩ <;> { dsimp [W', OpenWedge.MemOpen] at *; linarith }
  let f : Fin 5 → VFunc := fun i =>
    let c₁ := (W' i).u₁.1 * (-(W' i).y.1) + (W' i).u₁.2 * (-(W' i).y.2)
    let c₂ := (W' i).u₂.1 * (-(W' i).y.1) + (W' i).u₂.2 * (-(W' i).y.2)
    toVFunc (-(W' i).u₁.1 / c₁) (-(W' i).u₁.2 / c₁) (-(W' i).u₂.1 / c₂) (-(W' i).u₂.2 / c₂)
  apply h_thm1 f
  intro m
  obtain ⟨p, hp2, hpmask⟩ := h_all_in_H m
  let p' : ℝ × ℝ := (p.1 - x₀, p.2)
  refine ⟨(p'.1 / p'.2, 1 / p'.2), fun i => ?_⟩
  have hchart := proj_chart_wedge_iff_vfunc (W' i) (h0' i) p' hp2
  have hopen_eq : (W' i).MemOpen p' ↔ (W i).MemOpen p := by
    dsimp [W', p', OpenWedge.MemOpen]
    have e1 : p.1 - x₀ - ((W i).y.1 - x₀) = p.1 - (W i).y.1 := by ring
    rw [e1]
  have hext_eq : (W' i).MemExt p' ↔ (W i).MemExt p := by
    dsimp [W', p', OpenWedge.MemExt]
    have e1 : p.1 - x₀ - ((W i).y.1 - x₀) = p.1 - (W i).y.1 := by ring
    rw [e1]
  have hm_i := hpmask i
  by_cases hmi : m i
  · simp only [hmi, ↓reduceIte] at hm_i ⊢
    exact hchart.1.mp (hopen_eq.mpr hm_i)
  · simp only [hmi, Bool.false_eq_true, ↓reduceIte] at hm_i ⊢
    exact hchart.2.mp (hext_eq.mpr hm_i)

/-! ## Part 3: Reverse Translation Reduction (`Theorem 2 -> Theorem 1(1)`) -/

theorem thm2_implies_thm1_part1
    (h_thm2 : ∀ (W : Fin 5 → OpenWedge),
      (∀ i : Fin 5, (W i).y.1 < 0 ∧ (W i).y.2 < 0) →
      (∃ pa : ℝ × ℝ, 0 < pa.1 ∧ ∀ i : Fin 5, (W i).MemOpen pa) →
      (∃ pb : ℝ × ℝ, 0 < pb.2 ∧ ∀ i : Fin 5, (W i).MemOpen pb) →
      ¬ (∀ m : Fin 5 → Bool, ∃ p : ℝ × ℝ, (p.1 < 0 ∨ p.2 < 0) ∧ RealizesWedgeMask W m p)) :
    ∀ f : Fin 5 → VFunc, ¬ (∀ m : Fin 5 → Bool, ∃ p : ℝ × ℝ, RealizesVMask f m p) := by
  intro f h_all
  choose pm hpm using h_all
  let Xmax : ℝ := 1 + ∑ m : Fin 5 → Bool, |((pm m).1)|
  have hXmax_gt : ∀ m : Fin 5 → Bool, (pm m).1 < Xmax := by
    intro m
    have h1 : (pm m).1 ≤ |(pm m).1| := le_abs_self _
    have h2 : |(pm m).1| ≤ ∑ m' : Fin 5 → Bool, |(pm m').1| :=
      Finset.single_le_sum (f := fun m' : Fin 5 → Bool => |(pm m').1|)
        (fun _ _ => abs_nonneg _) (Finset.mem_univ m)
    dsimp [Xmax]; linarith
  -- De-flatten each f_i to f'_i with strict slope inequality a'_i < c'_i
  let f' : Fin 5 → VFunc := fun i =>
    if hlt : (f i).a < (f i).c then f i
    else
      { a := (f i).a
        b := max (f i).b (f i).d
        c := (f i).a + 1
        d := max (f i).b (f i).d - Xmax - 1
        hle := by linarith }
  have hf'_lt : ∀ i : Fin 5, (f' i).a < (f' i).c := by
    intro i; dsimp [f']; split_ifs with hlt
    · exact hlt
    · dsimp; linarith
  have hf'_eval : ∀ (i : Fin 5) (m : Fin 5 → Bool), (f' i).eval (pm m).1 = (f i).eval (pm m).1 := by
    intro i m; dsimp [f']; split_ifs with hlt
    · rfl
    · have heq : (f i).c = (f i).a := le_antisymm (not_lt.mp hlt) (f i).hle
      unfold VFunc.eval; dsimp
      rw [heq]
      have hxm := hXmax_gt m
      have h1 : ((f i).a + 1) * (pm m).1 + (max (f i).b (f i).d - Xmax - 1) ≤
          (f i).a * (pm m).1 + max (f i).b (f i).d := by linarith
      rw [max_eq_left h1]
      rcases le_total (f i).b (f i).d with hbd | hbd
      · rw [max_eq_right hbd, max_eq_right (by linarith)]
      · rw [max_eq_left hbd, max_eq_left (by linarith)]
  let ξ : Fin 5 → ℝ := fun i => ((f' i).b - (f' i).d) / ((f' i).c - (f' i).a)
  let η : Fin 5 → ℝ := fun i => (f' i).a * (ξ i) + (f' i).b
  let X0 : ℝ := 1 + Xmax + ∑ i : Fin 5, |ξ i|
  let Y0 : ℝ := 1 + (∑ m : Fin 5 → Bool, |(pm m).2|) + ∑ i : Fin 5, |η i|
  have hξ_lt : ∀ i : Fin 5, ξ i < X0 := by
    intro i
    have h1 : ξ i ≤ |ξ i| := le_abs_self _
    have h2 : |ξ i| ≤ ∑ j : Fin 5, |ξ j| :=
      Finset.single_le_sum (f := fun j : Fin 5 => |ξ j|)
        (fun _ _ => abs_nonneg _) (Finset.mem_univ i)
    have h3 : 0 ≤ ∑ m : Fin 5 → Bool, |(pm m).1| :=
      Finset.sum_nonneg (fun _ _ => abs_nonneg _)
    dsimp [X0, Xmax]; linarith
  have hη_lt : ∀ i : Fin 5, η i < Y0 := by
    intro i
    have h1 : η i ≤ |η i| := le_abs_self _
    have h2 : |η i| ≤ ∑ j : Fin 5, |η j| :=
      Finset.single_le_sum (f := fun j : Fin 5 => |η j|)
        (fun _ _ => abs_nonneg _) (Finset.mem_univ i)
    have h3 : 0 ≤ ∑ m : Fin 5 → Bool, |(pm m).2| :=
      Finset.sum_nonneg (fun _ _ => abs_nonneg _)
    dsimp [Y0]; linarith
  have hpm_lt_X0 : ∀ m : Fin 5 → Bool, (pm m).1 < X0 := by
    intro m
    have h1 := hXmax_gt m
    have h2 : 0 ≤ ∑ j : Fin 5, |ξ j| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
    dsimp [X0]; linarith
  let W : Fin 5 → OpenWedge := fun i =>
    { y := (ξ i - X0, η i - Y0)
      u₁ := (-(f' i).a, 1)
      u₂ := (-(f' i).c, 1)
      h_nondeg := by have := hf'_lt i; linarith }
  have hW_eval : ∀ (i : Fin 5) (x y : ℝ),
      ((W i).MemOpen (x - X0, y - Y0) ↔ (f' i).eval x < y) ∧
      ((W i).MemExt (x - X0, y - Y0) ↔ y < (f' i).eval x) := by
    intro i x y
    have hpos : 0 < (f' i).c - (f' i).a := sub_pos.mpr (hf'_lt i)
    have hη_c : (f' i).c * (ξ i) + (f' i).d = η i := by
      dsimp [ξ, η]
      field_simp [ne_of_gt hpos]
      ring
    have hl1 : (W i).u₁.1 * ((x - X0) - (W i).y.1) + (W i).u₁.2 * ((y - Y0) - (W i).y.2) =
        y - ((f' i).a * x + (f' i).b) := by
      dsimp [W, η]; ring
    have hl2 : (W i).u₂.1 * ((x - X0) - (W i).y.1) + (W i).u₂.2 * ((y - Y0) - (W i).y.2) =
        y - ((f' i).c * x + (f' i).d) := by
      change -(f' i).c * ((x - X0) - (ξ i - X0)) + 1 * ((y - Y0) - (η i - Y0)) =
        y - ((f' i).c * x + (f' i).d)
      rw [← hη_c]
      ring
    unfold OpenWedge.MemOpen OpenWedge.MemExt VFunc.eval
    rw [hl1, hl2, max_lt_iff, lt_max_iff]
    constructor
    · constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨by linarith, by linarith⟩
    · constructor <;> rintro (h1 | h2)
      · left; linarith
      · right; linarith
      · left; linarith
      · right; linarith
  have h_apices : ∀ i : Fin 5, (W i).y.1 < 0 ∧ (W i).y.2 < 0 := by
    intro i; dsimp [W]; exact ⟨by linarith [hξ_lt i], by linarith [hη_lt i]⟩
  let xstar : ℝ := X0 + 1
  let ystar : ℝ := Y0 + 1 + ∑ i : Fin 5, |(f' i).eval xstar|
  have hpstar_open : ∀ i : Fin 5, (W i).MemOpen (xstar - X0, ystar - Y0) := by
    intro i
    rw [(hW_eval i xstar ystar).1]
    have h1 : (f' i).eval xstar ≤ |(f' i).eval xstar| := le_abs_self _
    have h2 : |(f' i).eval xstar| ≤ ∑ j : Fin 5, |(f' j).eval xstar| :=
      Finset.single_le_sum (f := fun j : Fin 5 => |(f' j).eval xstar|)
        (fun _ _ => abs_nonneg _) (Finset.mem_univ i)
    have hY0 : 0 ≤ Y0 := by
      have s1 : 0 ≤ ∑ m : Fin 5 → Bool, |(pm m).2| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
      have s2 : 0 ≤ ∑ j : Fin 5, |η j| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
      dsimp [Y0]; linarith
    dsimp [ystar]; linarith
  have hpstar_pos1 : 0 < (xstar - X0, ystar - Y0).1 := by dsimp [xstar]; linarith
  have hpstar_pos2 : 0 < (xstar - X0, ystar - Y0).2 := by
    have s : 0 ≤ ∑ j : Fin 5, |(f' j).eval xstar| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
    dsimp [ystar]; linarith
  apply h_thm2 W h_apices ⟨(xstar - X0, ystar - Y0), hpstar_pos1, hpstar_open⟩
      ⟨(xstar - X0, ystar - Y0), hpstar_pos2, hpstar_open⟩
  intro m
  refine ⟨((pm m).1 - X0, (pm m).2 - Y0), Or.inl (by linarith [hpm_lt_X0 m]), fun i => ?_⟩
  have hm_i := hpm m i
  rw [← hf'_eval i m] at hm_i
  by_cases hmi : m i
  · simp only [hmi, ↓reduceIte] at hm_i ⊢
    exact (hW_eval i (pm m).1 (pm m).2).1.mpr hm_i
  · simp only [hmi, Bool.false_eq_true, ↓reduceIte] at hm_i ⊢
    exact (hW_eval i (pm m).1 (pm m).2).2.mpr hm_i


lemma q3_ray_not_both_flanks (y d : ℝ × ℝ) (hy1 : y.1 < 0) (hy2 : y.2 < 0)
    (t₁ t₂ : ℝ) (ht1 : 0 ≤ t₁) (ht2 : 0 ≤ t₂)
    (h1x : 0 ≤ y.1 + t₁ * d.1) (h1y : y.2 + t₁ * d.2 < 0)
    (h2x : y.1 + t₂ * d.1 < 0) (h2y : 0 ≤ y.2 + t₂ * d.2) :
    False := by
  by_cases ht : t₁ < t₂ <;> by_cases hd1 : 0 < d.1 <;> by_cases hd2 : 0 < d.2 <;> nlinarith

lemma case_b_apex_not_on_line (W : OpenWedge) (pa pb : ℝ × ℝ)
    (hy1 : W.y.1 < 0) (hy2 : W.y.2 < 0)
    (hxa : 0 < pa.1) (hya : pa.2 < 0) (hxb : pb.1 < 0) (hyb : 0 < pb.2)
    (hC : pa.1 * pb.2 - pa.2 * pb.1 < 0)
    (ha : W.MemOpen pa) (hb : W.MemOpen pb) :
    (pb.2 - pa.2) * W.y.1 + (pa.1 - pb.1) * W.y.2 ≠ pa.1 * pb.2 - pa.2 * pb.1 := by
  intro heq
  rcases ha with ⟨ha1, ha2⟩
  rcases hb with ⟨hb1, hb2⟩
  have hnondeg := W.h_nondeg
  have hdet : (pa.1 - W.y.1) * (pb.2 - W.y.2) - (pa.2 - W.y.2) * (pb.1 - W.y.1) = 0 := by
    linarith
  have h1 : W.y.1 < pa.1 := by linarith
  have h2 : pb.1 < W.y.1 := by nlinarith
  by_cases hu : 0 < W.u₁.1 <;> by_cases hv : 0 < W.u₁.2 <;> nlinarith

lemma case_b_origin_in_wedge (W : OpenWedge) (pa pb : ℝ × ℝ)
    (hy1 : W.y.1 < 0) (hy2 : W.y.2 < 0)
    (hxa : 0 < pa.1) (hya : pa.2 < 0) (hxb : pb.1 < 0) (hyb : 0 < pb.2)
    (hC : pa.1 * pb.2 - pa.2 * pb.1 < 0)
    (ha : W.MemOpen pa) (hb : W.MemOpen pb)
    (h_below : (pb.2 - pa.2) * W.y.1 + (pa.1 - pb.1) * W.y.2 < pa.1 * pb.2 - pa.2 * pb.1) :
    W.MemOpen (0, 0) := by
  rcases ha with ⟨ha1, ha2⟩
  rcases hb with ⟨hb1, hb2⟩
  have hdet : 0 < (pa.1 - W.y.1) * (pb.2 - W.y.2) - (pa.2 - W.y.2) * (pb.1 - W.y.1) := by
    linarith
  have hα : 0 < (-W.y.1) * (pb.2 - W.y.2) - (-W.y.2) * (pb.1 - W.y.1) := by nlinarith
  have hβ : 0 < (pa.1 - W.y.1) * (-W.y.2) - (pa.2 - W.y.2) * (-W.y.1) := by nlinarith
  have hc1 :
      ((-W.y.1) * (pb.2 - W.y.2) - (-W.y.2) * (pb.1 - W.y.1)) *
        (W.u₁.1 * (pa.1 - W.y.1) + W.u₁.2 * (pa.2 - W.y.2)) +
      ((pa.1 - W.y.1) * (-W.y.2) - (pa.2 - W.y.2) * (-W.y.1)) *
        (W.u₁.1 * (pb.1 - W.y.1) + W.u₁.2 * (pb.2 - W.y.2)) =
      ((pa.1 - W.y.1) * (pb.2 - W.y.2) - (pa.2 - W.y.2) * (pb.1 - W.y.1)) *
        (W.u₁.1 * (0 - W.y.1) + W.u₁.2 * (0 - W.y.2)) := by ring
  have hc2 :
      ((-W.y.1) * (pb.2 - W.y.2) - (-W.y.2) * (pb.1 - W.y.1)) *
        (W.u₂.1 * (pa.1 - W.y.1) + W.u₂.2 * (pa.2 - W.y.2)) +
      ((pa.1 - W.y.1) * (-W.y.2) - (pa.2 - W.y.2) * (-W.y.1)) *
        (W.u₂.1 * (pb.1 - W.y.1) + W.u₂.2 * (pb.2 - W.y.2)) =
      ((pa.1 - W.y.1) * (pb.2 - W.y.2) - (pa.2 - W.y.2) * (pb.1 - W.y.1)) *
        (W.u₂.1 * (0 - W.y.1) + W.u₂.2 * (0 - W.y.2)) := by ring
  exact ⟨by nlinarith, by nlinarith⟩

lemma case_b_wedge_disjoint_q1 (W : OpenWedge) (pa pb q : ℝ × ℝ)
    (hy1 : W.y.1 < 0) (hy2 : W.y.2 < 0)
    (hxa : 0 < pa.1) (hya : pa.2 < 0) (hxb : pb.1 < 0) (hyb : 0 < pb.2)
    (hC : pa.1 * pb.2 - pa.2 * pb.1 < 0)
    (ha : W.MemOpen pa) (hb : W.MemOpen pb)
    (h_above : pa.1 * pb.2 - pa.2 * pb.1 < (pb.2 - pa.2) * W.y.1 + (pa.1 - pb.1) * W.y.2)
    (hq1 : 0 ≤ q.1) (hq2 : 0 ≤ q.2) :
    W.MemExt q := by
  rcases ha with ⟨ha1, ha2⟩
  rcases hb with ⟨hb1, hb2⟩
  have hdet_neg : (pa.1 - W.y.1) * (pb.2 - W.y.2) - (pa.2 - W.y.2) * (pb.1 - W.y.1) < 0 := by
    linarith
  have hva2 : pa.2 - W.y.2 < 0 := by nlinarith
  have hvb1 : pb.1 - W.y.1 < 0 := by nlinarith
  have hα : 0 < (q.1 - W.y.1) * (pb.2 - W.y.2) - (q.2 - W.y.2) * (pb.1 - W.y.1) := by nlinarith
  have hβ : 0 < (pa.1 - W.y.1) * (q.2 - W.y.2) - (pa.2 - W.y.2) * (q.1 - W.y.1) := by nlinarith
  have hc1 :
      ((q.1 - W.y.1) * (pb.2 - W.y.2) - (q.2 - W.y.2) * (pb.1 - W.y.1)) *
        (W.u₁.1 * (pa.1 - W.y.1) + W.u₁.2 * (pa.2 - W.y.2)) +
      ((pa.1 - W.y.1) * (q.2 - W.y.2) - (pa.2 - W.y.2) * (q.1 - W.y.1)) *
        (W.u₁.1 * (pb.1 - W.y.1) + W.u₁.2 * (pb.2 - W.y.2)) =
      ((pa.1 - W.y.1) * (pb.2 - W.y.2) - (pa.2 - W.y.2) * (pb.1 - W.y.1)) *
        (W.u₁.1 * (q.1 - W.y.1) + W.u₁.2 * (q.2 - W.y.2)) := by ring
  exact Or.inl (by nlinarith)

lemma case_b_exists_disjoint_wedge (W : Fin 5 → OpenWedge) (pa pb : ℝ × ℝ)
    (h_apex : ∀ i : Fin 5, (W i).y.1 < 0 ∧ (W i).y.2 < 0)
    (hxa : 0 < pa.1) (hya : pa.2 < 0) (hxb : pb.1 < 0) (hyb : 0 < pb.2)
    (hC : pa.1 * pb.2 - pa.2 * pb.1 < 0)
    (ha : ∀ i : Fin 5, (W i).MemOpen pa)
    (hb : ∀ i : Fin 5, (W i).MemOpen pb)
    (h_not_orig : ¬ ∀ i : Fin 5, (W i).MemOpen (0, 0)) :
    ∃ i : Fin 5, ∀ q : ℝ × ℝ, 0 ≤ q.1 → 0 ≤ q.2 → (W i).MemExt q := by
  push_neg at h_not_orig
  rcases h_not_orig with ⟨i, hi⟩
  refine ⟨i, fun q hq1 hq2 => ?_⟩
  have hneq := case_b_apex_not_on_line (W i) pa pb (h_apex i).1 (h_apex i).2 hxa hya hxb hyb hC (ha i) (hb i)
  rcases lt_trichotomy ((pb.2 - pa.2) * (W i).y.1 + (pa.1 - pb.1) * (W i).y.2) (pa.1 * pb.2 - pa.2 * pb.1) with hlt | heq | hgt
  · exact False.elim (hi (case_b_origin_in_wedge (W i) pa pb (h_apex i).1 (h_apex i).2 hxa hya hxb hyb hC (ha i) (hb i) hlt))
  · exact False.elim (hneq heq)
  · exact case_b_wedge_disjoint_q1 (W i) pa pb q (h_apex i).1 (h_apex i).2 hxa hya hxb hyb hC (ha i) (hb i) hgt hq1 hq2


end
