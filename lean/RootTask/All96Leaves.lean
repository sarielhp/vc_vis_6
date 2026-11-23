import Mathlib
set_option linter.unusedVariables false
noncomputable section

namespace Upper9Leaf_000

/-- Section 1 (`upper_9.tex` Lemma `three-halfplanes`, lines 201--209):
    Face-counting bounds for arrangements of lines and 2-ray wedge boundaries:
    (1) `3` lines divide the plane into at most `f3 ≤ 1 + 1 + 2 + 3 = 7 < 2^3` faces;
    (2) Starting from `2` lines (`f0 ≤ 4` faces) and inserting `3` two-ray wedge boundaries sequentially
        where wedge `1` meets the `2` lines in `m1 ≤ 4` points, wedge `2` meets the `2` lines + `2` rays
        in `m2 ≤ 8` points, and wedge `3` meets the `2` lines + `4` rays in `m3 ≤ 12` points,
        the resulting face count satisfies `f ≤ f0 + (m1 + 1) + (m2 + 1) + (m3 + 1) ≤ 31 < 2^5`. -/
theorem lem_three_halfplanes_and_two_hp_three_wedges
    (f3 l1 l2 l3 f0 m1 m2 m3 f : ℕ)
    (hl1 : l1 ≤ 1 + 1) (hl2 : l2 ≤ l1 + 2) (hl3 : l3 ≤ l2 + 3) (hf3 : f3 ≤ l3)
    (hf0 : f0 ≤ 4) (hm1 : m1 ≤ 4) (hm2 : m2 ≤ 8) (hm3 : m3 ≤ 12)
    (hf : f ≤ f0 + (m1 + 1) + (m2 + 1) + (m3 + 1)) :
    f3 < 2 ^ 3 ∧ f < 2 ^ 5 := by
  repeat·omega
end Upper9Leaf_000

namespace Upper9Leaf_001

def orient2d (a b c : ℝ × ℝ) : ℝ :=
  (b.1 - a.1) * (c.2 - a.2) - (b.2 - a.2) * (c.1 - a.1)

/-- Grassmann-Plücker 3x3 determinant identity for planar orientations. -/
theorem orient2d_plucker (a b c d x : ℝ × ℝ) :
    orient2d a b c * orient2d b d x =
      orient2d d a b * orient2d b c x - orient2d b c d * orient2d a b x ∧
    orient2d c d a * orient2d b c x =
      orient2d b c d * orient2d a c x + orient2d a b c * orient2d c d x := by
  push_cast [orient2d, false, ← sub_eq_iff_eq_add']
  iterate use (by{ring})
end Upper9Leaf_001

namespace Upper9Leaf_002

def orient2d (a b c : ℝ × ℝ) : ℝ :=
  (b.1 - a.1) * (c.2 - a.2) - (b.2 - a.2) * (c.1 - a.1)

/-- Lemma 11.2(i) Eq (H0-cont): on a CCW convex pentagon `(p0, p1, p2, p3, p4)`,
    `orient(p0,p1,x) ≥ 0`, `orient(p1,p2,x) < 0`, `orient(p3,p4,x) < 0` implies `orient(p2,p3,x) < 0`. -/
theorem pentagon_H0_cont_13
    (p0 p1 p2 p3 x : ℝ × ℝ)
    (h012 : 0 < orient2d p0 p1 p2)
    (h123 : 0 < orient2d p1 p2 p3)
    (h230 : 0 < orient2d p2 p3 p0)
    (h301 : 0 < orient2d p3 p0 p1)
    (h1234 : ∀ p4 : ℝ × ℝ, 0 < orient2d p1 p2 p3 → True)
    (p4 : ℝ × ℝ)
    (hc_123 : 0 < orient2d p1 p2 p3)
    (hc_234 : 0 < orient2d p2 p3 p4)
    (hc_341 : 0 < orient2d p3 p4 p1)
    (hc_412 : 0 < orient2d p4 p1 p2)
    (hx0 : 0 ≤ orient2d p0 p1 x)
    (hx1 : orient2d p1 p2 x < 0)
    (hx3 : orient2d p3 p4 x < 0) :
    orient2d p2 p3 x < 0 := by
  change 0<_+_ at*
  rw[orient2d]at*
  revert p1 p2 p3 p4 x
  use fun and A B a s R L _ _ _ _ _ _ _ _ K V=>not_le.1 fun and' =>?_
  cases em ((a.1-B.1) * (and.2-B.snd)-(a.2-B.2) * (and.1-B.fst) > 0) with nlinarith
end Upper9Leaf_002

namespace Upper9Leaf_003

open scoped Classical

noncomputable section

/-- Lemma 3.4(ii): In Case B, if `p_a ∈ Q₄`, `p_b ∈ Q₂` with `X_a Y_b - X_b Y_a < 0`,
    and `y = (x_i, u_i) ∈ Q₃` satisfies `(Y_b - Y_a) x_i + (X_a - X_b) u_i > X_a Y_b - X_b Y_a`,
    then both `(-1, 0)` and `(0, -1)` lie in the open positive cone of `p_b - y` and `p_a - y`. -/
lemma caseB_L_gt_contains_axes
    (Xa Ya Xb Yb xi ui : ℝ)
    (hXa : 0 < Xa) (hYa : Ya < 0)
    (hXb : Xb < 0) (hYb : 0 < Yb)
    (hC : Xa * Yb - Xb * Ya < 0)
    (hxi : xi < 0) (hui : ui < 0)
    (hL : (Yb - Ya) * xi + (Xa - Xb) * ui > Xa * Yb - Xb * Ya) :
    ∃ α1 β1 α2 β2 : ℝ, 0 < α1 ∧ 0 < β1 ∧ 0 < α2 ∧ 0 < β2 ∧
      α1 * (Xb - xi) + β1 * (Xa - xi) = -1 ∧
      α1 * (Yb - ui) + β1 * (Ya - ui) = 0 ∧
      α2 * (Xb - xi) + β2 * (Xa - xi) = 0 ∧
      α2 * (Yb - ui) + β2 * (Ya - ui) = -1 := by
  simp_all-contextual [←eq_sub_iff_add_eq',←eq_div_iff ↑(sub_ne_zero.2 (hxi.trans hXa).ne')]
  field_simp[sub_eq_zero,(hxi.trans _).ne']
  rcases lt_trichotomy ((Xa-xi) * (Yb -ui)) ((Xb -xi) * (Ya-ui)) with a | S | S
  · use-(Ya-ui)/((Xb-xi) * (Ya-ui)-(Xa-xi) * (Yb-ui)),div_pos (by nlinarith) ( sub_pos.2 a),div_pos ?_ (by linarith)
    · exact ⟨ _,div_pos ↑( sub_pos.mpr (hxi.trans hXa)) ( sub_pos.mpr a),neg_pos.mpr ↑(div_neg_of_neg_of_pos ↑(mul_neg_of_neg_of_pos (by nlinarith) (by (bound))) (by linarith)),by grind⟩
    · use sub_pos.2 ((mul_right_comm _ _ _).trans_lt ((div_lt_iff₀ ↑(sub_pos.2 a)).2 (by nlinarith)))
  · nlinarith
  · nlinarith

end
end Upper9Leaf_003

namespace Upper9Leaf_004

open scoped Classical

noncomputable section

/-- Theorem 2.1(2) projective chart equivalence on `{V > 0}`:
    `(U, V) ↦ (U / V, 1 / V)` maps strict wedge interior/exterior to V-epigraph/hypograph. -/
lemma projective_chart_vepigraph_equiv
    (a b c d U V : ℝ) (hV : 0 < V) :
    ((a * U + b * V < 1 ∧ c * U + d * V < 1) ↔
      1 / V > max (a * (U / V) + b) (c * (U / V) + d)) ∧
    ((a * U + b * V > 1 ∨ c * U + d * V > 1) ↔
      1 / V < max (a * (U / V) + b) (c * (U / V) + d)) := by
  simp_all only [div_add' _ _ _ (hV).ne',div_lt_div_iff_of_pos_right, and_self, mul_div, max_lt_iff,lt_sup_iff]

end
end Upper9Leaf_004

namespace Upper9Leaf_005

theorem vepigraph_conservation_and_n_le_7
    (n T3 T3bar T1 Kcross C Δ1 Δ2 Δ3 Δ4 dL dR : ℤ)
    (hT : T3 + T3bar = 10)
    (hK : Kcross = 3 * T3 + T1 + 2 * (T3bar - T1))
    (hC1 : C = Kcross + 6)
    (hC2 : C = 32 + Δ1 + Δ2 + Δ3 + Δ4)
    (hΔ4 : Δ4 = n - 5)
    (hΔ3 : 0 ≤ Δ3)
    (hd : dL + dR ≤ Δ1 + Δ2)
    (hcert : 2 ≤ T3bar + T1 + dL + dR) :
    n + T3bar + T1 + Δ1 + Δ2 + Δ3 = 9 ∧ n ≤ 7 := by
  omega
end Upper9Leaf_005

namespace Upper9Leaf_006

/-- Proposition 9.5 (n = 5 Island Rule): For any contiguous subinterval `[a, b]` of `{0,1,2,3,4}`
    disjoint from `{1, 3}`, `{0, 2, 4}` contains two distinct elements outside the closed
    1-neighborhood `[a - 1, b + 1]` that are non-adjacent (`|u - v| ≥ 2`). -/
theorem n5_island_rule
    (a b : Fin 5) (hab : a.val ≤ b.val)
    (h1 : ¬ (a.val ≤ 1 ∧ 1 ≤ b.val))
    (h3 : ¬ (a.val ≤ 3 ∧ 3 ≤ b.val)) :
    ∃ u v : Fin 5,
      u.val ∈ ({0, 2, 4} : Set ℕ) ∧
      v.val ∈ ({0, 2, 4} : Set ℕ) ∧
      u ≠ v ∧
      ¬ (a.val ≤ u.val + 1 ∧ u.val ≤ b.val + 1) ∧
      ¬ (a.val ≤ v.val + 1 ∧ v.val ≤ b.val + 1) ∧
      2 ≤ (u.val : ℤ) - (v.val : ℤ) := by
  exact ( exists_congr fun and=>exists_and_left).mpr (by decide+revert)
end Upper9Leaf_006

namespace Upper9Leaf_007

open scoped RealInnerProductSpace

/-- Theorem 9.1(2) (Hull containment from half-plane separation):
    If for every open half-plane `{z : c < ⟪u, z⟫}` containing `X`, `p` also lies in `{z : c < ⟪u, z⟫}`,
    and `K` is a closed convex set containing `X` (e.g. `convexHull ℝ X` for finite nonempty `X`),
    then `p ∈ K` (proved via any separating linear functional / dual norm). -/
theorem halfplane_sep_implies_mem_closed_convex
    (X K : Set (EuclideanSpace ℝ (Fin 2))) (p : EuclideanSpace ℝ (Fin 2))
    (hXK : X ⊆ K) (hK_ne : K.Nonempty) (hK_closed : IsClosed K) (hK_conv : Convex ℝ K)
    (h_sep : ∀ (u : EuclideanSpace ℝ (Fin 2)) (c : ℝ),
      (∀ x ∈ X, c < ⟪u, x⟫) → c < ⟪u, p⟫) :
    p ∈ K := by
  use (by_contra) (geometric_hahn_banach_closed_point (by valid) hK_closed ·|>.elim fun and x =>by_contra fun and=>? _)
  use x.elim ((InnerProductSpace.toDual ℝ _).surjective (-‹StrongDual _ _›) |>.elim fun and m R L=>absurd (h_sep and (-R)) (?_))
  exact (mt (. (fun a s=>((congr_arg (. a)) m).ge.trans_lt' (neg_lt_neg (L.1 a (hXK s))))) ((congr_arg (. p) m).trans_lt (neg_lt_neg L.2)).asymm)
end Upper9Leaf_007

namespace Upper9Leaf_008

/-- Theorem 11.4 Case 2 (`H = ∅`): Bowtie XOR conditions on `x_k(11111)` are incompatible with
    the forbidden half-plane pairs `F_1` (Regime 1) and `F_2` (Regime 2). -/
theorem pentagon_case2_regime1_impossible
    (x2_1 x2_2 x3_2 x3_3 x4_3 x4_4 : Bool)
    (h_xor2 : xor x2_1 x2_2 = true)
    (h_xor3 : xor x3_2 x3_3 = true)
    (h_xor4 : xor x4_3 x4_4 = true)
    (hf_12 : ¬ (x2_1 = false ∧ (x2_2 = false ∨ x3_2 = false)))
    (hf_23 : ¬ ((x2_2 = false ∨ x3_2 = false) ∧ (x3_3 = false ∨ x4_3 = false)))
    (hf_34 : ¬ ((x3_3 = false ∨ x4_3 = false) ∧ x4_4 = false))
    (hf_24 : ¬ ((x2_2 = false ∨ x3_2 = false) ∧ x4_4 = false))
    (hf_13 : ¬ (x2_1 = false ∧ (x3_3 = false ∨ x4_3 = false))) :
    False := by
  grind

theorem pentagon_case2_regime2_impossible
    (x1_0 x1_1 x3_2 x3_3 x4_3 x4_4 : Bool)
    (h_xor1 : xor x1_0 x1_1 = true)
    (h_xor3 : xor x3_2 x3_3 = true)
    (h_xor4 : xor x4_3 x4_4 = true)
    (hf_23 : ¬ (x3_2 = false ∧ (x3_3 = false ∨ x4_3 = false)))
    (hf_34 : ¬ ((x3_3 = false ∨ x4_3 = false) ∧ x4_4 = false))
    (hf_24 : ¬ (x3_2 = false ∧ x4_4 = false))
    (hf_13 : ¬ (x1_1 = false ∧ (x3_3 = false ∨ x4_3 = false)))
    (hf_03 : ¬ (x1_0 = false ∧ (x3_3 = false ∨ x4_3 = false))) :
    False := by
  grind
end Upper9Leaf_008

namespace Upper9Leaf_009

def orient2d (a b c : ℝ × ℝ) : ℝ :=
  (b.1 - a.1) * (c.2 - a.2) - (b.2 - a.2) * (c.1 - a.1)

/-- Lemma 11.2(i) Eq (ear-disjoint): On any CCW triple `(p0, p1, p2)`,
    `orient(p0, p1, x) ≤ 0` and `orient(p1, p2, x) ≤ 0` implies `orient(p0, p2, x) < 0`. -/
theorem pentagon_ear_disjoint
    (p0 p1 p2 x : ℝ × ℝ)
    (h012 : 0 < orient2d p0 p1 p2)
    (hx0 : orient2d p0 p1 x ≤ 0)
    (hx1 : orient2d p1 p2 x ≤ 0) :
    orient2d p0 p2 x < 0 := by
  delta orient2d at *
  linarith
end Upper9Leaf_009

namespace Upper9Leaf_010

/-- Theorem 11.4 Case 1 (`H ≠ ∅`): Using Theorem 9.1(2) (which lifts a universal sign across
    all 32 masks `x_k(m)` to `R_{11111}`) together with Lemma 11.2 half-plane inclusions and
    bowtie XOR constraints `bowtie-11111` yields a contradiction for every `r_* ∈ {1, 2, 3, 4}`. -/
theorem pentagon_case1_H_nonempty_impossible
    (regime2 : Bool)
    (r_star : Fin 5)
    (hr_valid : r_star.val ∈ ({1, 2, 3, 4} : Set ℕ))
    (hr_reg2 : regime2 = true → r_star.val ≠ 1)
    -- Membership of `R_{11111}` points `x1, x2, x3, x4` in `H_0^+, ..., H_4^+`:
    (x1_0 x1_1 x2_1 x2_2 x3_2 x3_3 x4_3 x4_4 : Bool)
    -- Bowtie XOR constraints (bowtie-11111):
    (h_bw3 : xor x3_2 x3_3 = true)
    (h_bw4 : xor x4_3 x4_4 = true)
    (h_bw2 : regime2 = false → xor x2_1 x2_2 = true)
    (h_bw1 : regime2 = true → xor x1_0 x1_1 = true)
    -- Consequences of `R_{11111} ⊆ H^+(u0, v0) ∩ H_{r_*}^-` + Theorem 9.1(2) + Lemma 11.2:
    (h_r12 : r_star.val ∈ ({1, 2} : Set ℕ) → x4_3 = true ∧ x4_4 = true)
    (h_r4 : r_star.val = 4 → x3_2 = true ∧ x3_3 = true)
    (h_r3_reg1 : r_star.val = 3 → regime2 = false → x2_1 = true ∧ x2_2 = true)
    (h_r3_reg2 : r_star.val = 3 → regime2 = true → x1_0 = true ∧ x1_1 = true) :
    False := by
  match h:r_star.1 with|0|1|2|3|4=>(cases@regime2 with simp_all) | S+5=>omega
end Upper9Leaf_010

namespace Upper9Leaf_011

/-- Proposition 10.6 (`k ∈ {2, 3}`): The L-domain arrangement bound
    `6 + 3 * C(5-k, 2) + 3 * C(k, 2) + 2 * k * (5-k)` equals `36 - k * (5-k) ≤ 30 < 32`. -/
theorem caseB_k2_k3_arrangement_lt_32
    (k : ℕ) (hk : k = 2 ∨ k = 3) :
    6 + 3 * Nat.choose (5 - k) 2 + 3 * Nat.choose k 2 + 2 * k * (5 - k) < 32 := by
  induction@@hk with cases‹_› with decide
end Upper9Leaf_011

namespace Upper9Leaf_012

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

/-- Openness push into strict Q₁: if `q.1 ≥ 0`, `q.2 ≥ 0`, and `q ∈ ⋂ W_i`, there exists `q'` with
    `0 < q'.1`, `0 < q'.2`, and `q' ∈ ⋂ W_i`. -/
lemma push_into_open_q1 (W : Fin 5 → OpenWedge) (q : ℝ × ℝ)
    (hq1 : 0 ≤ q.1) (hq2 : 0 ≤ q.2) (hq : ∀ i : Fin 5, (W i).MemOpen q) :
    ∃ q' : ℝ × ℝ, 0 < q'.1 ∧ 0 < q'.2 ∧ ∀ i : Fin 5, (W i).MemOpen q' := by
  have hcont : ∀ i : Fin 5, Continuous (fun p : ℝ × ℝ =>
      min ((W i).u₁.1 * (p.1 - (W i).y.1) + (W i).u₁.2 * (p.2 - (W i).y.2))
          ((W i).u₂.1 * (p.1 - (W i).y.1) + (W i).u₂.2 * (p.2 - (W i).y.2))) := by
    intro i; continuity
  have hopen : IsOpen {p : ℝ × ℝ | ∀ i : Fin 5, (W i).MemOpen p} := by
    have : {p : ℝ × ℝ | ∀ i : Fin 5, (W i).MemOpen p} =
        ⋂ i : Fin 5, {p : ℝ × ℝ | 0 < min ((W i).u₁.1 * (p.1 - (W i).y.1) + (W i).u₁.2 * (p.2 - (W i).y.2))
                                          ((W i).u₂.1 * (p.1 - (W i).y.1) + (W i).u₂.2 * (p.2 - (W i).y.2))} := by
      ext p; simp [OpenWedge.MemOpen]
    rw [this]
    exact isOpen_iInter_of_finite (fun i => isOpen_lt continuous_const (hcont i))
  rw [Metric.isOpen_iff] at hopen
  obtain ⟨ε, hε, hball⟩ := hopen q hq
  refine ⟨(q.1 + ε / 3, q.2 + ε / 3), by linarith, by linarith, hball ?_⟩
  rw [Metric.mem_ball, Prod.dist_eq]
  simp only [Real.dist_eq]
  have h1 : |q.1 + ε / 3 - q.1| < ε := by rw [add_sub_cancel_left, abs_of_pos (by linarith)]; linarith
  have h2 : |q.2 + ε / 3 - q.2| < ε := by rw [add_sub_cancel_left, abs_of_pos (by linarith)]; linarith
  exact max_lt h1 h2

/-- Shifting coordinates by `q'` in `Q₁` reduces general Case A to `(0,0) ∈ ⋂ W'_i`. -/
lemma caseA_reduces_to_origin
    (h_orig_case : ∀ W' : Fin 5 → OpenWedge,
      (∀ i : Fin 5, (W' i).y.1 < 0 ∧ (W' i).y.2 < 0) →
      (∀ i : Fin 5, (W' i).MemOpen (0, 0)) →
      ¬ (∀ m : Fin 5 → Bool, ∃ p : ℝ × ℝ, (p.1 < 0 ∨ p.2 < 0) ∧ RealizesWedgeMask W' m p))
    (W : Fin 5 → OpenWedge)
    (h_apex : ∀ i : Fin 5, (W i).y.1 < 0 ∧ (W i).y.2 < 0)
    (q' : ℝ × ℝ) (hq1 : 0 < q'.1) (hq2 : 0 < q'.2)
    (hq : ∀ i : Fin 5, (W i).MemOpen q') :
    ¬ (∀ m : Fin 5 → Bool, ∃ p : ℝ × ℝ, (p.1 < 0 ∨ p.2 < 0) ∧ RealizesWedgeMask W m p) := by
  intro hall
  let W' : Fin 5 → OpenWedge := fun i =>
    { y := ((W i).y.1 - q'.1, (W i).y.2 - q'.2)
      u₁ := (W i).u₁
      u₂ := (W i).u₂
      h_nondeg := (W i).h_nondeg }
  apply h_orig_case W'
  · intro i
    exact ⟨by linarith [(h_apex i).1], by linarith [(h_apex i).2]⟩
  · intro i
    obtain ⟨h1, h2⟩ := hq i
    dsimp [OpenWedge.MemOpen, W'] at h1 h2 ⊢
    exact ⟨by linarith, by linarith⟩
  · intro m
    obtain ⟨p, hp_om, hp_m⟩ := hall m
    refine ⟨(p.1 - q'.1, p.2 - q'.2), ?_, ?_⟩
    · rcases hp_om with hpx | hpy
      · left; linarith
      · right; linarith
    · intro i
      have hi := hp_m i
      by_cases hm : m i <;> simp only [hm, ↓reduceIte] at hi ⊢
      · obtain ⟨h1, h2⟩ := hi
        dsimp [OpenWedge.MemOpen, W'] at h1 h2 ⊢
        exact ⟨by linarith, by linarith⟩
      · dsimp [OpenWedge.MemExt, W'] at hi ⊢
        rcases hi with h1 | h2
        · left; linarith
        · right; linarith

end
end Upper9Leaf_012

namespace Upper9Leaf_013

/-- Lemma 9.2 (Slope-generic perturbation): Perturbing slopes `(a, c)` to `(a', c')` within
    `δ / (2 * X0)` where `|x| + 1 ≤ X0` changes `max(a*x + b, c*x + d)` by strictly less than `δ / 2`. -/
theorem vfunc_slope_perturb_bound
    (a b c d a' c' x δ X0 : ℝ)
    (hδ : 0 < δ)
    (hX0 : |x| + 1 ≤ X0)
    (ha : |a' - a| < δ / (2 * X0))
    (hc : |c' - c| < δ / (2 * X0)) :
    |max (a' * x + b) (c' * x + d) - max (a * x + b) (c * x + d)| < δ / 2 := by
  apply(abs_max_sub_max_le_max _ _ _ _).trans_lt ∘max_lt_iff.2
  simp_all only[ abs_mul,add_sub_add_right_eq_sub, and_self,←sub_mul,←div_div,lt_div_iff₀ (hX0.trans_lt' (by (linear_combination norm_nonneg x ) )), (mul_le_mul_of_nonneg_left ((lt_add_one (@_)).le.trans hX0) (abs_nonneg _)).trans_lt]
end Upper9Leaf_013

namespace Upper9Leaf_014

def orient2d (a b c : ℝ × ℝ) : ℝ :=
  (b.1 - a.1) * (c.2 - a.2) - (b.2 - a.2) * (c.1 - a.1)

/-- Lemma 11.1 (Two-sided visibility separation -> hull exclusion):
    If every point `w ∈ W` lies strictly in the positive open half-plane `{z : orient2d d x z > 0}`
    and `d ≠ x`, then `x ∉ convexHull ℝ W` (since `orient2d d x x = 0`). -/
theorem two_sided_hull_disjoint
    (d x : ℝ × ℝ) (W : Set (ℝ × ℝ))
    (hw : ∀ w ∈ W, 0 < orient2d d x w) :
    x ∉ convexHull ℝ W := by
  push_cast [orient2d, mem_convexHull_iff_exists_fintype,Prod.forall]at*
  use fun⟨k,l,a,b,A, B, M, _⟩=>absurd (Finset.univ.sum_pos' (fun R L=>mul_nonneg (A R) (hw _ _ (M R)).le) ( (Finset.exists_ne_zero_of_sum_ne_zero (B▸one_ne_zero)).imp ? _)) ?_
  · use fun and=>.imp_right ↑(mul_pos.comp ·.lt_of_le' (A and) (hw _ _ (M (and))))
  norm_num[B,← Finset.sum_mul,← Finset.mul_sum _,show∑B,a B*_ = _ from(‹_›▸Prod.fst_sum).symm, mul_sub,show∑B,a B*_ = _ from(‹_›▸Prod.snd_sum).symm,mul_left_comm (a _),mul_comm]
  exact (ge_of_eq (by·abel1))
end Upper9Leaf_014

namespace Upper9Leaf_015

def orient2d (a b c : ℝ × ℝ) : ℝ :=
  (b.1 - a.1) * (c.2 - a.2) - (b.2 - a.2) * (c.1 - a.1)

/-- Lemma 11.2(iii) (Certified arc cone inclusion):
    If `h = α0 • p0 + α1 • v0 + αx • x` with `α0, α1, αx > 0`, `α0 + α1 + αx = 1`,
    `orient(p0, v0, h) > 0`, `orient(r0, r1, h) < 0`, `orient(r0, r1, p0) ≥ 0`,
    and `orient(r0, r1, v0) ≥ 0`, then `orient(p0, v0, x) > 0` and `orient(r0, r1, x) < 0`. -/
theorem pentagon_certified_arc_cone
    (p0 v0 r0 r1 h x : ℝ × ℝ) (α0 α1 αx : ℝ)
    (hα0 : 0 < α0) (hα1 : 0 < α1) (hαx : 0 < αx)
    (hsum : α0 + α1 + αx = 1)
    (hh1 : h.1 = α0 * p0.1 + α1 * v0.1 + αx * x.1)
    (hh2 : h.2 = α0 * p0.2 + α1 * v0.2 + αx * x.2)
    (h_in : 0 < orient2d p0 v0 h)
    (h_arc : orient2d r0 r1 h < 0)
    (hp0 : 0 ≤ orient2d r0 r1 p0)
    (hv0 : 0 ≤ orient2d r0 r1 v0) :
    0 < orient2d p0 v0 x ∧ orient2d r0 r1 x < 0 := by
  simp_all only[orient2d, ←eq_sub_iff_add_eq']
  repeat use (by nlinarith only[hv0,hp0,h_arc,h_in,hα0,hα1,hαx])
end Upper9Leaf_015

namespace Upper9Leaf_016

/-- Lemma 9.4(i) (Projective dual equivalence for V-functions):
    `(x, y)` lies strictly above `max(a*x + b, c*x + d)` iff both `(a, b)` and `(c, d)` lie strictly
    below the dual line `v = (-x)*u + y`; and `(x, y)` lies strictly below `max(a*x + b, c*x + d)`
    iff at least one of `(a, b), (c, d)` lies strictly above `v = (-x)*u + y`. -/
theorem vfunc_dual_equivalence (a b c d x y : ℝ) :
    (max (a * x + b) (c * x + d) < y ↔ (b < (-x) * a + y ∧ d < (-x) * c + y)) ∧
    (y < max (a * x + b) (c * x + d) ↔ (b > (-x) * a + y ∨ d > (-x) * c + y)) := by
  zify[mul_comm, mul_neg, and_self, max_lt_iff,lt_sup_iff,lt_neg_add_iff_add_lt,neg_lt_iff_pos_add']
  aesop (config := { warnOnNonterminal := false })
end Upper9Leaf_016

namespace Upper9Leaf_017

/-- Lemma 9.5(iv) (Upper-hull contiguity in `U(s, t)`):
    If `u1 < u2 < u3` and `(v2 - v1) / (u2 - u1) > (v3 - v2) / (u3 - u2)`, then
    `v1 > s * u1 + t` and `v3 > s * u3 + t` imply `v2 > s * u2 + t`. -/
theorem upper_hull_three_point_contiguity
    (u1 v1 u2 v2 u3 v3 s t : ℝ)
    (hu12 : u1 < u2) (hu23 : u2 < u3)
    (hslope : (v3 - v2) / (u3 - u2) < (v2 - v1) / (u2 - u1))
    (h1 : s * u1 + t < v1)
    (h3 : s * u3 + t < v3) :
    s * u2 + t < v2 := by
  (nlinarith only [hu12,hu23,(h3), (div_lt_div_iff₀ ↑((sub_pos.mpr @hu23)) ( sub_pos.mpr (by valid))).mp (hslope),h1])
end Upper9Leaf_017

namespace Upper9Leaf_018

open Real

/-- Lemma 10.7(iii) (Polar tangent-chart affinity):
    Whenever `cos (θ - θ0) ≠ 0`, `(wx * cos θ + wy * sin θ) / cos (θ - θ0)` is affine in `tan (θ - θ0)`. -/
theorem polar_tangent_chart_affinity
    (wx wy θ θ0 : ℝ)
    (hcos : cos (θ - θ0) ≠ 0) :
    (wx * cos θ + wy * sin θ) / cos (θ - θ0) =
      (wx * cos θ0 + wy * sin θ0) +
      (-wx * sin θ0 + wy * cos θ0) * tan (θ - θ0) := by
  exact ( Real.tan_eq_sin_div_cos _)▸(sub_add_cancel θ @θ0▸Real.sin_add _ _)▸(sub_add_cancel θ @θ0▸Real.cos_add _ _)▸.symm (.trans (by rw [mul_div, add_div' _ _ _ hcos]) (by ring ) )
end Upper9Leaf_018

namespace Upper9Leaf_019

def isC5DiagNat (a b : ℕ) : Bool :=
  let d := (a + 5 - b) % 5
  d == 2 || d == 3

def checkDeletedThree (r1 r2 r3 : ℕ) : Bool :=
  if !(1 ≤ r1 && r1 < r2 && r2 < r3 && r3 ≤ 8) then true
  else
    let surv := (List.range 10).filter (fun i => i != r1 && i != r2 && i != r3)
    let adjPairs := List.zip surv surv.tail
    let delList := [r1, r2, r3]
    let delPairs := delList.flatMap (fun r =>
      let left := (surv.filter (fun i => i < r)).getLast?
      let right := (surv.filter (fun i => r < i)).head?
      (match left with | some l => [(r, l)] | none => []) ++
      (match right with | some u => [(r, u)] | none => []))
    let allPairs := adjPairs ++ delPairs
    let diags := [(0, 2), (0, 3), (1, 3), (1, 4), (2, 4)]
    diags.any (fun (a, b) =>
      !(allPairs.any (fun (u, v) =>
        let cu := u % 5
        let cv := v % 5
        (cu == a && cv == b) || (cu == b && cv == a))))

/-- Proposition 9.6(4): For every triple `1 ≤ r1 < r2 < r3 ≤ 8` deleted from `(0,1,2,3,4,0,1,2,3,4)`,
    at least one of the 5 `C_5`-diagonals `{(0,2),(0,3),(1,3),(1,4),(2,4)}` is missing from
    `A_2(κ) ∪ ⋃_{r ∈ R} B_2(r)`. -/
theorem n7_K5_deleted_three_missing_diagonal :
    ∀ r1 : Fin 10, ∀ r2 : Fin 10, ∀ r3 : Fin 10,
      checkDeletedThree r1.val r2.val r3.val = true := by
  decide
end Upper9Leaf_019

namespace Upper9Leaf_020

/-- Proposition 9.6 (`n = 6` Island Rule orbits `(1,3)`, `(2,4)`, `(1,5)`, `(2,5)`):
    For each compressed 6-block word `w : Fin 6 → Fin 5` in those orbits, there exists a target
    subset `S ⊆ Fin 5` such that every contiguous subinterval `[a, b] ⊆ Fin 6` whose colors lie in `S`
    fails the Island Rule (two colors of `S` outside the closed 1-neighborhood `[a-1, b+1]` are
    non-adjacent in `w`). -/
def checkIslandWord (w : List ℕ) (target : List ℕ) : Bool :=
  let adj := List.zip w w.tail
  let isAdj (u v : ℕ) : Bool :=
    adj.any (fun (x, y) => (x == u && y == v) || (x == v && y == u))
  (List.range 6).all (fun a =>
    (List.range 6).all (fun b =>
      if !(a ≤ b) then true
      else
        let sub := (List.range (b - a + 1)).map (fun k => w.getD (a + k) 0)
        if !(sub.all (fun c => target.contains c)) then true
        else
          let lo := if a == 0 then 0 else a - 1
          let hi := if b + 1 < 6 then b + 1 else 5
          let nhd := (List.range (hi - lo + 1)).map (fun k => w.getD (lo + k) 0)
          let rem := target.filter (fun c => !(nhd.contains c))
          rem.any (fun u => rem.any (fun v => u != v && !(isAdj u v)))))

theorem n6_island_orbits_verified :
    -- Orbit (1, 3): (X, A, X, B, C, D) = [0, 1, 0, 2, 3, 4], target {A, B, D} = [1, 2, 4]
    checkIslandWord [0, 1, 0, 2, 3, 4] [1, 2, 4] = true ∧
    -- Orbit (2, 4): (A, X, B, X, C, D) = [1, 0, 2, 0, 3, 4], target {A, B, D} = [1, 2, 4]
    checkIslandWord [1, 0, 2, 0, 3, 4] [1, 2, 4] = true ∧
    -- Orbit (1, 5): (X, A, B, C, X, D) = [0, 1, 2, 3, 0, 4], target {A, C, D} = [1, 3, 4]
    checkIslandWord [0, 1, 2, 3, 0, 4] [1, 3, 4] = true ∧
    -- Orbit (2, 5): (A, X, B, C, X, D) = [1, 0, 2, 3, 0, 4], target {A, C, D} = [1, 3, 4]
    checkIslandWord [1, 0, 2, 3, 0, 4] [1, 3, 4] = true := by
  decide
end Upper9Leaf_020

namespace Upper9Leaf_021

/-- Proposition 9.6(1)-(2): For any permutation `σ : Equiv.Perm (Fin 5)`, let
    `inv_pair i j` hold when `i < j` and `(σ.symm i) > (σ.symm j)`. If the total number of
    inversions is `1` or `2`, then either `∀ i : Fin 5, i.val < 3 → ¬ inv_pair i ⟨4, by decide⟩`
    (Left certificate) or `∀ r : Fin 5, 2 ≤ r.val → σ ⟨0, by decide⟩ < σ r` (Right certificate). -/
theorem n7_perm_inv_1_or_2_has_certificate
    (σ : Equiv.Perm (Fin 5))
    (h_inv : ((Finset.univ.product Finset.univ).filter
      (fun p : Fin 5 × Fin 5 => p.1 < p.2 ∧ σ.symm p.2 < σ.symm p.1)).card ∈ ({1, 2} : Set ℕ)) :
    (∀ i : Fin 5, i.val < 3 → σ.symm i < σ.symm ⟨4, by decide⟩) ∨
    (∀ r : Fin 5, 2 ≤ r.val → σ ⟨0, by decide⟩ < σ r) := by
  revert h_inv
  by_cases h:σ ∈ Finset.univ.filter fun and=> Finset.card {(a, b):_ ×_|a<b∧and.symm b<and.symm a}=1 ∨ Finset.card {(a, b):_ ×_|a<b∧and.symm b<and.symm a}=2
  · use by_contra<|absurd h ∘by decide+revert
  · simp_all
end Upper9Leaf_021

namespace Upper9Leaf_022

open scoped Classical

noncomputable section

/-- Any dual vector `p` with `p.1 * y.1 + p.2 * y.2 = 1` for `y ∈ Q₃` lies in `Ω = {x < 0 ∨ y < 0}`. -/
lemma dual_point_in_omega (p y : ℝ × ℝ) (hy1 : y.1 < 0) (hy2 : y.2 < 0)
    (hpy : p.1 * y.1 + p.2 * y.2 = 1) :
    p.1 < 0 ∨ p.2 < 0 := by
  exact or_iff_not_imp_left.2 fun and=>by nlinarith

/-- Polar reciprocal equivalence for `η > 0`:
    `max (p1 * ((1/η)*c) + p2 * ((1/η)*s)) (q1 * ((1/η)*c) + q2 * ((1/η)*s)) < 1`
    iff `max (p1 * c + p2 * s) (q1 * c + q2 * s) < η`. -/
lemma polar_reciprocal_wedge_iff (p1 p2 q1 q2 c s η : ℝ) (hη : 0 < η) :
    (p1 * ((1 / η) * c) + p2 * ((1 / η) * s) < 1 ∧ q1 * ((1 / η) * c) + q2 * ((1 / η) * s) < 1) ↔
    max (p1 * c + p2 * s) (q1 * c + q2 * s) < η := by
  simp_all only[mul_comm_div, max_lt_iff,←add_div, one_mul,div_lt_one, mul_div]

end
end Upper9Leaf_022

namespace Upper9Leaf_023

def orient2d (a b c : ℝ × ℝ) : ℝ :=
  (b.1 - a.1) * (c.2 - a.2) - (b.2 - a.2) * (c.1 - a.1)

/-- Lemma 11.3(i) (Mutual interior exclusion in `△(0, 1, 2)`):
    If `orient2d p0 p2 y0 < 0` and `y0 = α0 • p0 + α2 • p2 + α1 • y1` with `α0, α2, α1 > 0`
    and `α0 + α2 + α1 = 1`, then `orient2d p0 p2 y1 < orient2d p0 p2 y0 < 0`, so neither
    `0 < orient2d p0 p2 y1` nor `y1 = β0 • p0 + β2 • p2 + β1 • y0` (`β0, β2, β1 > 0`, `∑ β = 1`) can hold. -/
theorem ear_triangle_mutual_exclusion
    (p0 p2 y0 y1 : ℝ × ℝ) (α0 α2 α1 : ℝ)
    (hα0 : 0 < α0) (hα2 : 0 < α2) (hα1 : 0 < α1) (hsum : α0 + α2 + α1 = 1)
    (hy0_1 : y0.1 = α0 * p0.1 + α2 * p2.1 + α1 * y1.1)
    (hy0_2 : y0.2 = α0 * p0.2 + α2 * p2.2 + α1 * y1.2)
    (h_neg : orient2d p0 p2 y0 < 0) :
    orient2d p0 p2 y1 < orient2d p0 p2 y0 ∧ orient2d p0 p2 y1 < 0 := by
  refine (and_self_iff.2 (show _+_<_+_ from hy0_1▸hy0_2▸(hsum▸add_sub_cancel_left _ _)▸?_)).imp_right h_neg.trans'
  cases hsum▸add_sub_cancel_left _ _ with nlinarith[hy0_1▸hy0_2▸sub_neg.1 h_neg]
end Upper9Leaf_023

namespace Upper9Leaf_024

/-- Section 10.3 Subcase A1 (Explicit recession perturbation):
    If `p k • u ≤ 0` for all `k : Fin 10`, `(p k • u = 0 → k = k0)`, `p k0 • w < 0`,
    `0 < ε`, and `∀ k ≠ k0, ε * ((p k).1 * w.1 + (p k).2 * w.2) < -((p k).1 * u.1 + (p k).2 * u.2)`,
    then `p k • (u + ε • w) < 0` for every `k : Fin 10`. -/
theorem subcaseA1_explicit_recession_step
    (p : Fin 10 → ℝ × ℝ) (u w : ℝ × ℝ) (k0 : Fin 10) (ε : ℝ)
    (hε : 0 < ε)
    (hk0_le : (p k0).1 * u.1 + (p k0).2 * u.2 ≤ 0)
    (hk0_w : (p k0).1 * w.1 + (p k0).2 * w.2 < 0)
    (h_other : ∀ k : Fin 10, k ≠ k0 →
      ε * ((p k).1 * w.1 + (p k).2 * w.2) < -((p k).1 * u.1 + (p k).2 * u.2)) :
    ∀ k : Fin 10, (p k).1 * (u.1 + ε * w.1) + (p k).2 * (u.2 + ε * w.2) < 0 := by
  refine (by if a:·= k0 then cases a with {linarith [mul_neg_of_pos_of_neg hε (by valid)]} else {linear_combination(@h_other _) a})
end Upper9Leaf_024

namespace Upper9Leaf_025

/-- Lemma 10.8(iii) (`R_Ω` interior-slab & `Q_2`-prefix domination):
    (1) If `r = α • w1 + β • w2` with `α, β > 0`, `α + β < 1`, and `0 < ρ < r • u`,
        then `ρ < w1 • u ∨ ρ < w2 • u`.
    (2) If `r = (-a, b)` and `w1 = (-A, B)` satisfy `a, b, A, B > 0`, `b < B`, `b * A - a * B > 0`,
        `cx ≤ 0`, and `0 < ρ < -a * cx + b * sy`, then `ρ < -A * cx + B * sy`. -/
theorem dual_hull_omega_r_domination
    (α β ρ r_u w1_u w2_u : ℝ)
    (hα : 0 < α) (hβ : 0 < β) (hsum : α + β < 1) (hρ : 0 < ρ)
    (hr_eq : r_u = α * w1_u + β * w2_u)
    (hr_gt : ρ < r_u) :
    ρ < w1_u ∨ ρ < w2_u := by
  use or_iff_not_imp_right.mpr fun and=>lt_of_mul_lt_mul_right (by linarith[mul_lt_of_lt_one_left hρ hsum, mul_le_mul_of_nonneg_left (not_lt.mp and) (hβ).le]) hα.le
end Upper9Leaf_025

namespace Upper9Leaf_026

/-- Lemma 10.8(iii) Part 2 (`Q_2`-prefix domination):
    If `a, b, A, B > 0`, `b < B`, `0 < b * A - a * B`, `cx ≤ 0`, and `0 < ρ < -a * cx + b * sy`,
    then `ρ < -A * cx + B * sy`. -/
theorem dual_hull_omega_q2_prefix_dom
    (a b A B cx sy ρ : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hA : 0 < A) (hB : 0 < B)
    (hbB : b < B) (hdet : 0 < b * A - a * B)
    (hcx : cx ≤ 0) (hρ : 0 < ρ)
    (hr : ρ < -a * cx + b * sy) :
    ρ < -A * cx + B * sy := by
  nlinarith only [hbB,hb,hcx,hdet, false, hρ.trans (hr), ↑hr]
end Upper9Leaf_026

namespace Upper9Leaf_027

def orient2d (a b c : ℝ × ℝ) : ℝ :=
  (b.1 - a.1) * (c.2 - a.2) - (b.2 - a.2) * (c.1 - a.1)

/-- Proposition 8.1 (`upper_9.tex` lines 895-900): Convexity of replaced 6-gon `C_{y_0}`.
    If `y0 = t1 • d3 + t2 • l + t3 • h` with `t1, t2, t3 > 0`, `t1 + t2 + t3 = 1`,
    `orient(d3, l, x) > 0`, `orient(d3, h, x) > 0`, and `orient(l, h, x) > 0`,
    then `orient(d3, y0, x) > 0` and `orient(y0, h, x) > 0`. -/
theorem opposite_endpoint_hexagon_convex_step
    (d3 l h y0 x : ℝ × ℝ) (t1 t2 t3 : ℝ)
    (h1 : 0 < t1) (h2 : 0 < t2) (h3 : 0 < t3) (hsum : t1 + t2 + t3 = 1)
    (hy1 : y0.1 = t1 * d3.1 + t2 * l.1 + t3 * h.1)
    (hy2 : y0.2 = t1 * d3.2 + t2 * l.2 + t3 * h.2)
    (ho_d3_l : 0 < orient2d d3 l x)
    (ho_d3_h : 0 < orient2d d3 h x)
    (ho_l_h : 0 < orient2d l h x) :
    0 < orient2d d3 y0 x ∧ 0 < orient2d y0 h x := by
  simp_all only [orient2d, add_assoc,←eq_sub_iff_add_eq']
  repeat use (by nlinarith only[ho_l_h,ho_d3_l,ho_d3_h,h3,h2,h1])
end Upper9Leaf_027

namespace Upper9Leaf_028

/-- Proposition 10.6 (`k = 4` barrier graph inclusion):
    Let `Xb < 0 < Yb`, `(0, 0) ∈ W1`, `(Xb, Yb) ∈ W1 ∩ W2`, `W1` convex, and
    `∀ t ≥ 0, (Xb - t, Yb) ∈ W2`. Then for every `X < 0`, putting
    `gX := if X ≤ Xb then Yb else (Yb / Xb) * X`, we have `(X, gX) ∈ W1 ∪ W2`. -/
theorem caseB_k4_barrier_in_union
    (W1 W2 : Set (ℝ × ℝ)) (Xb Yb X : ℝ)
    (hXb : Xb < 0) (hYb : 0 < Yb) (hX : X < 0)
    (h0 : (0, 0) ∈ W1)
    (hpb1 : (Xb, Yb) ∈ W1)
    (hpb2 : (Xb, Yb) ∈ W2)
    (hconv1 : Convex ℝ W1)
    (hray2 : ∀ t : ℝ, 0 ≤ t → (Xb - t, Yb) ∈ W2) :
    (X, if X ≤ Xb then Yb else (Yb / Xb) * X) ∈ W1 ∪ W2 := by
  use or_not.elim (if_pos ·▸? _) (if_neg ·▸.inl (by_contra (absurd (@hconv1 ( _, _) hpb1 _ h0 (1-(X-Xb)/ (0-Xb)) ( (X-Xb)/ (0-Xb))) ∘(?_))))
  · exact (.inr (sub_sub_self Xb X▸by simp_all only[sub_nonneg]))
  · use mt ((congr_arg _ (Prod.ext_iff.2 (by repeat use (by grind:_ = _*(_:ℝ)+_*_)))).mpr.comp (. (by bound) (by bound) (by abel)))
end Upper9Leaf_028

namespace Upper9Leaf_029

/-- Proposition 10.4(ii) (Circle witness outside `K`):
    If `nx^2 + ny^2 = 1` and `c < R`, then `zR = (p0x - R * nx, p0y - R * ny)` satisfies
    `(zR.1 - p0x)^2 + (zR.2 - p0y)^2 = R^2` and `nx * (zR.1 - p0x) + ny * (zR.2 - p0y) + c < 0`. -/
theorem quad_face_circle_outside_halfplane
    (p0x p0y nx ny c R : ℝ)
    (hn : nx ^ 2 + ny ^ 2 = 1)
    (hR : c < R) :
    ((p0x - R * nx) - p0x) ^ 2 + ((p0y - R * ny) - p0y) ^ 2 = R ^ 2 ∧
    nx * ((p0x - R * nx) - p0x) + ny * ((p0y - R * ny) - p0y) + c < 0 := by
  use (by·linear_combination2 (hn) *R ^2),by ·linear_combination hR-R *hn
end Upper9Leaf_029

namespace Upper9Leaf_030

def orient2d (a b c : ℝ × ℝ) : ℝ :=
  (b.1 - a.1) * (c.2 - a.2) - (b.2 - a.2) * (c.1 - a.1)

/-- Lemma 11.3(ii) (`△(wD, 0, 1) ∩ H^+(0, 2) ⊆ △(wD, 0, 2)`):
    If `orient(p0, p1, p2) > 0`, `orient(p0, p1, wD) > 0`, `orient(p1, p2, wD) > 0`,
    `orient(p0, p2, wD) > 0`, `y = a0 • wD + a1 • p0 + a2 • p1` (`a0, a1, a2 > 0`, `a0+a1+a2 = 1`),
    and `orient(p0, p2, y) > 0`, then `y` is a strict convex combination of `{wD, p0, p2}`. -/
theorem adjacent_ear_fan_in_chord_triangle
    (p0 p1 p2 wD y : ℝ × ℝ) (a0 a1 a2 : ℝ)
    (ho012 : 0 < orient2d p0 p1 p2)
    (hw01 : 0 < orient2d p0 p1 wD)
    (hw12 : 0 < orient2d p1 p2 wD)
    (hw02 : 0 < orient2d p0 p2 wD)
    (ha0 : 0 < a0) (ha1 : 0 < a1) (ha2 : 0 < a2) (hasum : a0 + a1 + a2 = 1)
    (hy1 : y.1 = a0 * wD.1 + a1 * p0.1 + a2 * p1.1)
    (hy2 : y.2 = a0 * wD.2 + a1 * p0.2 + a2 * p1.2)
    (hy02 : 0 < orient2d p0 p2 y) :
    ∃ b0 b1 b2 : ℝ, 0 < b0 ∧ 0 < b1 ∧ 0 < b2 ∧ b0 + b1 + b2 = 1 ∧
      y.1 = b0 * wD.1 + b1 * p0.1 + b2 * p2.1 ∧
      y.2 = b0 * wD.2 + b1 * p0.2 + b2 * p2.2 := by
  push_cast[*,orient2d] at*
  by_cases h :LinearIndependent ℝ ![![p2.1-p0.1,p2.2-p0.2],![wD.1-p0.1,wD.2-p0.2]]
  · refine(Matrix.vecMul_surjective_iff_isUnit.2 (Matrix.linearIndependent_rows_iff_isUnit.1 h) (![a2 * (p1.1-p0.1), a2*(p1.2-p0.snd)])).elim fun A B=>⟨a0+A 1,?_⟩
    norm_num[Matrix.vecMul_eq_sum,<-List.ofFn_inj]at B
    rcases lt_trichotomy (A 1) 0 with a | S | S
    · cases (by·linear_combination hasum: a1=1-a0-a2)
      obtain ⟨@c⟩ :=eq_or_ne a0<|-A (1)
      · linarith[congr_arg (@. * (p2.snd-p0.snd)) B.left,congr_arg ↑(· * (p2.fst-p0.fst)) B.right]
      cases (by valid:).lt_or_gt
      · linarith[mul_lt_mul_of_pos_left (by valid) (hw02),congr_arg (. * (p2.2-p0.2)) B.1,congr_arg (. * (p2.1-p0.1)) B.2]
      rcases lt_trichotomy (A 0) 0 with a | S|a
      · nlinarith[congrArg (.*(wD.1-p0.1)) B.2,congrArg (.*(wD.2-p0.2)) B.1]
      · nlinarith only[a, S▸B,hw01,ha2,congr_arg ↑(· * (wD.fst-p0.fst)) (S▸B.right),congr_arg ↑( ·*(wD.snd-p0.snd)) (S▸ B.left)]
      refine ⟨ _, _,by linarith, not_le.mp fun and=>? _,a,by rw [add_sub_cancel, sub_add_cancel],by linarith,by linarith⟩
      nlinarith[congrArg (.*(wD.2-p2.2)) B.1,congrArg (.*(wD.1-p2.1)) B.2]
    · linarith only[S▸congr_arg (. * (p2.2-p0.2)) B.1, S▸congr_arg (. * (p2.1-p0.1)) B.2, mul_pos ha2 (ho012)]
    · linarith[congr_arg (· * (p2.snd-p0.snd)) B.left, mul_pos S ↑hw02,congr_arg ↑(· * (p2.fst-p0.fst)) B.right, mul_pos ha2 (ho012)]
  · rcases h ((Matrix.linearIndependent_rows_of_isUnit.comp (Matrix.isUnit_iff_isUnit_det _).2 ((Matrix.det_fin_two ↑_).trans_ne (@hw02.ne ∘by ·norm_num+contextual[←mul_assoc, true,mul_comm])).isUnit))
end Upper9Leaf_030

namespace Upper9Leaf_031

/-- Lemma 10.7(iii) (Concavity of affine minus max of two affines):
    Let `h t := (A1 * t + B1) - max (A2 * t + B2) (C2 * t + D2)`.
    If `0 < h t0`, `0 < h t1`, and `t ∈ Set.Icc t0 t1`, then `0 < h t`. -/
theorem affine_sub_max_pos_on_interval
    (A1 B1 A2 B2 C2 D2 t0 t1 t : ℝ)
    (ht0 : max (A2 * t0 + B2) (C2 * t0 + D2) < A1 * t0 + B1)
    (ht1 : max (A2 * t1 + B2) (C2 * t1 + D2) < A1 * t1 + B1)
    (ht_lo : t0 ≤ t) (ht_hi : t ≤ t1) :
    max (A2 * t + B2) (C2 * t + D2) < A1 * t + B1 := by
  use ht_lo.eq_or_lt.elim (by bound) fun and=>max_lt_iff.2 (by repeat use (by nlinarith only[ht_hi, max_lt_iff.1 ht1, max_lt_iff.1 ht0,and]))
end Upper9Leaf_031

namespace Upper9Leaf_032

open scoped Classical BigOperators
open Finset

/-- If a sequence `m : Fin 9 → (Fin 4 → Bool)` flips only coordinate `idx t` at step `t : Fin 8`
    and every `i : Fin 4` appears an even number of times (specifically 2 times) among `idx`,
    then `m 8 = m 0`, hence the image of `m` has cardinality at most `8`. -/
lemma eight_flips_even_per_coord_card_le_eight
    (m : Fin 9 → (Fin 4 → Bool))
    (idx : Fin 8 → Fin 4)
    (h_step : ∀ (t : Fin 8) (i : Fin 4),
      m t.succ i = if i = idx t then !(m t.castSucc i) else m t.castSucc i)
    (h_two : ∀ i : Fin 4, (Finset.univ.filter (fun t : Fin 8 => idx t = i)).card = 2) :
    m 8 = m 0 ∧ (Finset.univ.image m).card ≤ 8 := by
  replace R M:m M=(m 0+∑ a ∈.range M, (if·=idx ⟨ _,a.mod_lt (by decide)⟩ then(1)else 0)):=funext fun and=>?_
  · use(R _)▸funext fun and=>? _,funext R▸(Finset.card_image_le.lt_of_ne fun and=>?_).le_pred
    · norm_num+decide[h_two, false,eq_comm (a := ( and)),Nat.mod_eq_of_lt ↑( Fin.is_lt _), Finset.sum_range _,id]
    have:= Finset.injOn_of_card_image_eq and
    use absurd (@this 0 · 8) @?_
    norm_num+decide[h_two,comm (a := (_: Fin _)), ↑funext_iff,Nat.mod_eq_of_lt,Finset.sum_range _]
    use fun and=>congr_arg @_ (.trans (by simp_rw [comm]) (h_two and))
  · refine M.induction ((add_zero _)).symm (h_step · and▸.▸symm ↑(.trans (by rw [ Fin.val_succ,Pi.add_apply, Finset.sum_range_succ]) @?_))
    norm_num[←add_assoc, (by decide : ∀S:Bool, S+1=!S),Nat.mod_eq_of_lt,add_ite]
    cases(m _ _) with cases((_: ℕ):Bool) with constructor
end Upper9Leaf_032

namespace Upper9Leaf_033

/-- Section 9.2 (`|Z_{ij}| = 3` sign-alternation witnesses for `{i, j} ∈ P_conc`):
    If `ai < ci`, `aj < cj`, `ai < aj`, and `ci < cj`, with `f1 x = max (ai*x + bi) (ci*x + di)`
    and `f2 x = max (aj*x + bj) (cj*x + dj)` satisfying `f1 x1 < f2 x1` and `f2 x2 < f1 x2`
    (`x1 < x2`), then there exist `xm < x1` and `xp > x2` with `f2 xm < f1 xm` and `f1 xp < f2 xp`. -/
theorem vfunc_conc_sign_alternation
    (ai bi ci di aj bj cj dj x1 x2 : ℝ)
    (hai_aj : ai < aj) (hci_cj : ci < cj)
    (hx12 : x1 < x2)
    (hx1 : max (ai * x1 + bi) (ci * x1 + di) < max (aj * x1 + bj) (cj * x1 + dj))
    (hx2 : max (aj * x2 + bj) (cj * x2 + dj) < max (ai * x2 + bi) (ci * x2 + di)) :
    (∃ xm : ℝ, xm < x1 ∧ max (aj * xm + bj) (cj * xm + dj) < max (ai * xm + bi) (ci * xm + di)) ∧
    (∃ xp : ℝ, x2 < xp ∧ max (ai * xp + bi) (ci * xp + di) < max (aj * xp + bj) (cj * xp + dj)) := by
  push_cast [lt_max_iff,max_lt_iff]at*
  constructor
  · obtain ⟨k, _⟩|⟨j, _⟩:=hx2
    · cases hx1 with| inl=>nlinarith| inr=>_
      cases exists_nat_gt ((-di+bj)/(aj-ci))
      cases exists_nat_gt ((di-dj)/(cj-ci))
      cases exists_nat_gt<||di-dj|/(cj-ci)⊔|x1|⊔ (by apply_rules: ℕ)
      simp_all only[abs_lt, max_lt_iff,div_lt_iff₀, sub_pos]
      if R:aj>ci then use-2*‹Nat›,by linarith,.inr (by repeat use (by nlinarith[(div_lt_iff₀ (sub_pos.2 R)).1 (by valid)]))else nlinarith
    rcases lt_trichotomy aj ci with a|rfl | S
    · cases exists_nat_gt <||bj-bi|/(aj-ai)⊔|dj-bi|/(cj-ai)
      simp_rw [max_lt_iff,div_lt_iff₀ ↑(sub_pos.2 hai_aj),div_lt_iff₀ ↑(sub_pos.2.comp (hai_aj.trans a).trans (by valid)),abs_lt]at*
      cases exists_nat_gt (-x1⊔‹ℕ›) with use-1-‹ℕ›,by linarith[max_lt_iff.1 (by valid)],.inl (by repeat use (by nlinarith[max_lt_iff.1 (by valid)]))
    · cases hx1 with nlinarith
    · cases hx1 with nlinarith
  · cases hx1
    · cases hx2 with| inl=>nlinarith| inr=>_
      cases exists_nat_gt ((bi-dj)/(cj-ai)⊔(di-dj)/(cj-ci))
      rcases lt_trichotomy cj ai with a|rfl | S
      · nlinarith
      · nlinarith
      use x2^2+‹ℕ›+1,by nlinarith, max_lt_iff.1 (.trans (by valid) (by nlinarith:_<x2^2+‹ℕ›+1)) |>.elim fun and i=>.inr ?_
      repeat use (by linear_combination(div_lt_iff₀ (by rwa[sub_pos])).1 and),by linear_combination(div_lt_iff₀ (by rwa[sub_pos])).1 i
    · cases le_total ai cj with| inl=>use x2+1,by linarith,.inr (by repeat use by nlinarith) | inr=>_
      cases exists_nat_gt ((bi-bj)/(aj-ai)⊔(di-bj)/(aj-ci)⊔x2)
      exact ⟨‹ℕ›,by simp_all only[div_lt_iff₀', (by linarith:aj-ci > 0), max_lt_iff,Or.inl, sub_mul,sub_pos, and_self, sub_lt_sub_iff,add_comm]⟩
end Upper9Leaf_033

namespace Upper9Leaf_034

/-- Proposition 9.6(3) (`n = 7, T3bar = 1, T1 = 1` 3-way duplicate-cell split):
    Across `τm < x1 < x2 < x5 < τp`, at `τm` order is `f5 < f4 < f3 < f2 < f1`, at `τp` order is
    `f1 < f2 < f3 < f4 < f5`, at `x1` we have `f1 < min(f2, f3, f4)`, at `x2` we have
    `f2 < min(f1, f5)`, and at `x5` we have `f5 < min(f2, f3, f4)` (with `f1(x1) ≠ f5(x1)` and
    `f1(x5) ≠ f5(x5)`). Then one of `{5}`, `{1}`, or `{1, 5}` has `Φ_M = 0` at two outer points
    bracketing an interior point with `Φ_M > 0`. -/
theorem n7_T3bar1_T11_has_split_mask
    (f1_tm f2_tm f3_tm f4_tm f5_tm : ℝ)
    (f1_x1 f2_x1 f3_x1 f4_x1 f5_x1 : ℝ)
    (f1_x2 f2_x2 f3_x2 f4_x2 f5_x2 : ℝ)
    (f1_x5 f2_x5 f3_x5 f4_x5 f5_x5 : ℝ)
    (f1_tp f2_tp f3_tp f4_tp f5_tp : ℝ)
    (htm : f5_tm < f4_tm ∧ f4_tm < f3_tm ∧ f3_tm < f2_tm ∧ f2_tm < f1_tm)
    (htp : f1_tp < f2_tp ∧ f2_tp < f3_tp ∧ f3_tp < f4_tp ∧ f4_tp < f5_tp)
    (hx1 : f1_x1 < f2_x1 ∧ f1_x1 < f3_x1 ∧ f1_x1 < f4_x1 ∧ f1_x1 ≠ f5_x1)
    (hx2 : f2_x2 < f1_x2 ∧ f2_x2 < f5_x2)
    (hx5 : f5_x5 < f2_x5 ∧ f5_x5 < f3_x5 ∧ f5_x5 < f4_x5 ∧ f1_x5 ≠ f5_x5) :
    -- Either {5} splits across τm < x2 < x5:
    (f5_tm < min (min f1_tm f2_tm) (min f3_tm f4_tm) ∧ f2_x2 < f5_x2 ∧
      f5_x5 < min (min f1_x5 f2_x5) (min f3_x5 f4_x5)) ∨
    -- Or {1} splits across x1 < x2 < τp:
    (f1_x1 < min (min f2_x1 f3_x1) (min f4_x1 f5_x1) ∧ f2_x2 < f1_x2 ∧
      f1_tp < min (min f2_tp f3_tp) (min f4_tp f5_tp)) ∨
    -- Or {1, 5} splits across x1 < x2 < x5:
    (max f1_x1 f5_x1 < min f2_x1 (min f3_x1 f4_x1) ∧
      f2_x2 < max f1_x2 f5_x2 ∧
      max f1_x5 f5_x5 < min f2_x5 (min f3_x5 f4_x5)) := by
  grind
end Upper9Leaf_034

namespace Upper9Leaf_035

def orient2d (a b c : ℝ × ℝ) : ℝ :=
  (b.1 - a.1) * (c.2 - a.2) - (b.2 - a.2) * (c.1 - a.1)

/-- Lemma 11.2(i) Eqs (H02-13), (H02-03), (H02-24):
    Combining ear disjointness `H^+(0, 2) ⊆ cl(H_0^+) ∪ cl(H_1^+)` with Eq (H0-cont) and its
    `+1` cyclic shift proves all three `H^+(0, 2)` half-plane inclusions on a CCW convex pentagon. -/
theorem pentagon_H02_inclusions_from_H0_cont
    (h0 h1 h2 h3 h4 h02 : ℝ)
    (hear : 0 < h02 → 0 ≤ h0 ∨ 0 ≤ h1)
    (hc0_13 : 0 ≤ h0 → h1 < 0 → h3 < 0 → h2 < 0)
    (hc0_24 : 0 ≤ h0 → h2 < 0 → h4 < 0 → h3 < 0)
    (hc0_14 : 0 ≤ h0 → h1 < 0 → h4 < 0 → h2 < 0 ∧ h3 < 0)
    (hc1_24 : 0 ≤ h1 → h2 < 0 → h4 < 0 → h3 < 0)
    (hc1_30 : 0 ≤ h1 → h3 < 0 → h0 < 0 → h4 < 0)
    (hc1_20 : 0 ≤ h1 → h2 < 0 → h0 < 0 → h3 < 0 ∧ h4 < 0) :
    (0 < h02 → h1 < 0 → h3 < 0 → h2 < 0) ∧
    (0 < h02 → h0 < 0 → h3 < 0 → h4 < 0) ∧
    (0 < h02 → h2 < 0 → h4 < 0 → h3 < 0) := by
  grind
end Upper9Leaf_035

namespace Upper9Leaf_036

def orient2d (a b c : ℝ × ℝ) : ℝ :=
  (b.1 - a.1) * (c.2 - a.2) - (b.2 - a.2) * (c.1 - a.1)

/-- Section 2 (`upper_9.tex` Eq `U-halfplanes`):
    For a CCW triple `(a, b, c)` (`orient(a, b, c) > 0`), any point `x = a + α • (a - b) + β • (a - c)`
    with `α, β > 0` satisfies `orient(c, a, x) < 0`, `orient(a, b, x) < 0`, and `orient(c, b, x) < 0`
    (`U(a; b, c) = H^-(c, a) ∩ H^-(a, b) ⊆ H^-(c, b)`). -/
theorem cone_U_in_three_right_halfplanes
    (a b c x : ℝ × ℝ) (α β : ℝ)
    (habc : 0 < orient2d a b c)
    (hα : 0 < α) (hβ : 0 < β)
    (hx1 : x.1 = a.1 + α * (a.1 - b.1) + β * (a.1 - c.1))
    (hx2 : x.2 = a.2 + α * (a.2 - b.2) + β * (a.2 - c.2)) :
    orient2d c a x < 0 ∧ orient2d a b x < 0 ∧ orient2d c b x < 0 := by
  simp_all only [orient2d, true,mul_comm β,mul_comm α]
  repeat use by nlinarith
end Upper9Leaf_036

namespace Upper9Leaf_037

/-- Section 2 (`upper_9.tex` Lemma 2.5 `three-halfplanes`):
    Two lines (`4` faces) plus three wedges inserted sequentially (`+5`, `+9`, `+13` faces)
    produce at most `4 + 5 + 9 + 13 = 31 < 32` faces. -/
theorem two_lines_three_wedges_face_bound
    (f0 f1 f2 f3 m1 m2 m3 : ℕ)
    (hf0 : f0 ≤ 4)
    (hm1 : m1 ≤ 4) (hf1 : f1 ≤ f0 + (m1 + 1))
    (hm2 : m2 ≤ 8) (hf2 : f2 ≤ f1 + (m2 + 1))
    (hm3 : m3 ≤ 12) (hf3 : f3 ≤ f2 + (m3 + 1)) :
    f3 < 32 := by
  omega
end Upper9Leaf_037

namespace Upper9Leaf_038

/-- Section 7 (`upper_9.tex` Lemma 7.3 `seven-cycle`):
    On `ℤ/7ℤ` (`Fin 7`), for every assignment choosing for each `d : Fin 7` and each parity `p : Bool`
    one selected element among the 3 even positions of `(Fin 7) \ {d}` (positions `(d + 2), (d + 4), (d + 6)`
    for `p = false`, and `(d + 1), (d + 3), (d + 5)` for `p = true`), there exist two selections
    `(d1, p1)` selecting `u` and `(d2, p2)` selecting `v` that are non-adjacent in `Fin 7`
    and such that neither `u` nor `v` is one of the two neighbors of the other in `(Fin 7) \ {d_i}`. -/
def isCompat7 (d1 u1 d2 u2 : Fin 7) : Bool :=
  let dist12 := (u1.val + 7 - u2.val) % 7
  if !(dist12 == 2 || dist12 == 3 || dist12 == 4 || dist12 == 5) then false
  else
    let a1 := if (u1.val + 6) % 7 == d1.val then (u1.val + 5) % 7 else (u1.val + 6) % 7
    let c1 := if (u1.val + 1) % 7 == d1.val then (u1.val + 2) % 7 else (u1.val + 1) % 7
    let a2 := if (u2.val + 6) % 7 == d2.val then (u2.val + 5) % 7 else (u2.val + 6) % 7
    let c2 := if (u2.val + 1) % 7 == d2.val then (u2.val + 2) % 7 else (u2.val + 1) % 7
    (u2.val != a1) && (u2.val != c1) && (u1.val != a2) && (u1.val != c2)

theorem seven_cycle_if_pair_at_dist_3
    (d1 u1 d2 u2 : Fin 7)
    (hu1 : u1 ≠ d1) (hu2 : u2 ≠ d2)
    (hdist3 : (u1.val + 7 - u2.val) % 7 = 3 ∨ (u1.val + 7 - u2.val) % 7 = 4) :
    isCompat7 d1 u1 d2 u2 = true := by
  norm_num [isCompat7]
  refine ⟨.inl (hdist3.imp_left Or.inr),by repeat use (by repeat use (by repeat use (by valid ∘ite_eq_iff.1 ∘.symm)))⟩
end Upper9Leaf_038

namespace Upper9Leaf_039

def orient2d (a b c : ℝ × ℝ) : ℝ :=
  (b.1 - a.1) * (c.2 - a.2) - (b.2 - a.2) * (c.1 - a.1)

/-- Section 8.4 (`upper_9.tex` line 891-895):
    If `h = μ0 • uD + μ1 • r + μ2 • d1` with `μ0, μ1, μ2 > 0`, `μ0 + μ1 + μ2 = 1`,
    `orient(h, r, d3) > 0`, and `orient(h, d1, d3) > 0`, then `orient(h, d3, uD) > 0`. -/
theorem opposite_endpoint_uD_left_of_h_d3
    (h uD r d1 d3 : ℝ × ℝ) (μ0 μ1 μ2 : ℝ)
    (h0 : 0 < μ0) (h1 : 0 < μ1) (h2 : 0 < μ2) (hsum : μ0 + μ1 + μ2 = 1)
    (hh1 : h.1 = μ0 * uD.1 + μ1 * r.1 + μ2 * d1.1)
    (hh2 : h.2 = μ0 * uD.2 + μ1 * r.2 + μ2 * d1.2)
    (hr : 0 < orient2d h r d3)
    (hd1 : 0 < orient2d h d1 d3) :
    0 < orient2d h d3 uD := by
  simp_all only[orient2d, ←eq_sub_iff_add_eq']
  nlinarith
end Upper9Leaf_039

namespace Upper9Leaf_040

/-- Section 8.1 (`upper_9.tex` Eight-Cycle Lemma):
    On `ℤ/8ℤ` (`Fin 8`), there is no subset `A ⊆ Fin 8` (representing `A_k`) and `G2 ⊆ Fin 8`
    (representing good 2-gaps `{k, k+1}`) simultaneously avoiding 3 pairwise-compatible half-plane
    tests under both `O_i = {i, i+2, i+4}` and `O'_i = {i, i+2, i+5}` for all `i : Fin 8`. -/
theorem eight_cycle_no_valid_selection
    (A G2 : Fin 8 → Bool)
    (hO : ∀ i : Fin 8, A (i + 1) = true ∨ A (i + 3) = true)
    (hO' : ∀ i : Fin 8, A (i + 1) = true ∨ G2 (i + 3) = true ∨ G2 (i + 6) = true)
    (h_no_G2_A : ∀ k : Fin 8, G2 k = true → A (k + 4) = false ∧ A (k + 6) = false)
    (h_no_triple : ¬ (A 0 = true ∧ A 2 = true ∧ A 5 = true)) :
    False := by
  simp_all [imp_iff_not_or, add_assoc, false, Fin.forall_iff_succ]
  grind
end Upper9Leaf_040

namespace Upper9Leaf_041

def orient2d (a b c : ℝ × ℝ) : ℝ :=
  (b.1 - a.1) * (c.2 - a.2) - (b.2 - a.2) * (c.1 - a.1)

/-- Section 4 (`upper_9.tex` Lemma 4.2 `front-restoration`):
    If `(a, f, c)` is a CCW convex triple (`orient(a, f, c) > 0`), `f` is a front vertex of `{a, f, c}`
    from `v` (`orient(a, f, v) < 0` and `orient(f, c, v) < 0`), and `b_prev, b_next` lie on the
    convex hull arcs from `a` to `f` and from `f` to `c` (`f - b_prev ∈ cone(f - a, c - f)` etc.,
    specifically `orient(a, f, b_prev) ≤ 0`, `orient(f, c, b_prev) > 0`, `orient(b_prev, f, c) > 0`,
    `b_prev = α1 • a + β1 • f + γ1 • p_out` -> more directly: if `v - f = λ1 • (f - a) + λ2 • (c - a)`?
    Wait: in `upper_9.tex`, `orient(a, f, v) < 0` and `orient(f, c, v) < 0` with `orient(a, f, c) > 0`
    place `v` in `f + cone(a - f, 0)`? Let's check exact identity: for CCW convex 4-gon `(a, b, f, c)`,
    `orient(a, f, v) < 0` and `orient(f, c, v) < 0` imply `orient(b, f, v) < 0`! -/
theorem front_restoration_edge_sign
    (a b f c v : ℝ × ℝ)
    (habf : 0 < orient2d a b f)
    (hbfc : 0 < orient2d b f c)
    (hfc_a : 0 < orient2d f c a)
    (hca_b : 0 < orient2d c a b)
    (hv_af : orient2d a f v < 0)
    (hv_fc : orient2d f c v < 0) :
    orient2d b f v < 0 := by
  delta orient2d at*
  nlinarith
end Upper9Leaf_041

namespace Upper9Leaf_042

def orient2d (a b c : ℝ × ℝ) : ℝ :=
  (b.1 - a.1) * (c.2 - a.2) - (b.2 - a.2) * (c.1 - a.1)

/-- Section 4 (`upper_9.tex` Eq `back-vertex`):
    On a CCW convex 4-gon `(pm, p, pp, x)`, if `v - p = α • (x - p) + β • (pm - p)` with `α, β > 0`,
    then `orient(pm, p, v) > 0` or `orient(p, pp, v) > 0` (`p` cannot have both `orient(pm, p, v) < 0`
    and `orient(p, pp, v) < 0`, and in fact `orient(pm, p, v) > 0`). -/
theorem back_vertex_positive_orient
    (pm p pp x v : ℝ × ℝ) (α β : ℝ)
    (h_pm_p_x : 0 < orient2d pm p x)
    (h_x_p_pp : 0 < orient2d p pp x)
    (hα : 0 < α) (hβ : 0 < β)
    (hv1 : v.1 - p.1 = α * (x.1 - p.1) + β * (pm.1 - p.1))
    (hv2 : v.2 - p.2 = α * (x.2 - p.2) + β * (pm.2 - p.2)) :
    0 < orient2d pm p v := by
  simp_all[orient2d, sub_eq_iff_eq_add]
  nlinarith
end Upper9Leaf_042

namespace Upper9Leaf_043

def orient2d (a b c : ℝ × ℝ) : ℝ :=
  (b.1 - a.1) * (c.2 - a.2) - (b.2 - a.2) * (c.1 - a.1)

/-- Section 4 (`upper_9.tex` Corollary 4.7 `endpoint-back`):
    If `h ∈ int △(uD, u0, v0)` (`h = α0 • uD + α1 • u0 + α2 • v0`, `α_i > 0`, `∑ α_i = 1`)
    on a CCW convex polygon containing `(l, h, r)` where `{u0, v0}` is disjoint from `{l, r}`
    (so `orient(l, h, u0) > 0`, `orient(l, h, v0) > 0`, `orient(h, r, u0) > 0`, `orient(h, r, v0) > 0`),
    and `uD` sees `D` from inside `H^+(u0, v0)`, wait: tracing `z_h -> h`: if `z_h ∈ U(h; l, r)`,
    i.e., `z_h = h + β1 • (h - l) + β2 • (h - r)` (`β1, β2 > 0`), then `orient(l, r, z_h) < 0`
    whenever `orient(l, h, r) < 0` (`(l, h, r)` clockwise, i.e., `(r, h, l)`? In CCW hull `(..., l, h, r, ...)`,
    `orient(l, h, r) > 0`, so `orient(l, r, h) < 0`, hence `orient(l, r, z_h) < 0`!). -/
theorem certified_witness_in_right_halfplane_lr
    (l h r zh : ℝ × ℝ) (β1 β2 : ℝ)
    (hlhr : 0 < orient2d l h r)
    (hβ1 : 0 < β1) (hβ2 : 0 < β2)
    (hzh1 : zh.1 = h.1 + β1 * (h.1 - l.1) + β2 * (h.1 - r.1))
    (hzh2 : zh.2 = h.2 + β1 * (h.2 - l.2) + β2 * (h.2 - r.2)) :
    orient2d l r zh < 0 := by
  exact (add_comm _ _).trans_lt (by valid▸hzh1▸by linear_combination hlhr.trans_eq (add_comm _ _)*(β2+β1 + 1))
end Upper9Leaf_043

namespace Upper9Leaf_044

/-- Section 3 (`upper_9.tex` Lemma 3.1 `hidden-targets`):
    By the Six-Wedge Theorem (`≤ 5` wedge tests on any witness family), if all points of `A` lie
    in `int(conv B) ⊆ conv(B ∪ {w_B})` and `w_B` sees `B` and misses `A`, then `|A| ≤ 5`. -/
theorem interior_size_le_five_from_six_wedge_bound
    (cardA : ℕ)
    (h_no_six : ¬ (6 ≤ cardA)) :
    cardA ≤ 5 := by
  omega
end Upper9Leaf_044

namespace Upper9Leaf_045

def InClosedTri (p q r z : ℝ × ℝ) : Prop :=
  ∃ μ1 μ2 μ3 : ℝ, 0 ≤ μ1 ∧ 0 ≤ μ2 ∧ 0 ≤ μ3 ∧ μ1 + μ2 + μ3 = 1 ∧
    z.1 = μ1 * p.1 + μ2 * q.1 + μ3 * r.1 ∧
    z.2 = μ1 * p.2 + μ2 * q.2 + μ3 * r.2

private lemma radon_case
    (p1 p2 p3 y1 z : ℝ × ℝ) (a1 a2 a3 b1 b2 b3 : ℝ)
    (ha1 : 0 ≤ a1) (ha2 : 0 ≤ a2) (ha3 : 0 ≤ a3) (hasum : a1 + a2 + a3 = 1)
    (hz1 : z.1 = a1 * p1.1 + a2 * p2.1 + a3 * p3.1)
    (hz2 : z.2 = a1 * p1.2 + a2 * p2.2 + a3 * p3.2)
    (hbsum : b1 + b2 + b3 = 1)
    (hy1 : y1.1 = b1 * p1.1 + b2 * p2.1 + b3 * p3.1)
    (hy2 : y1.2 = b1 * p1.2 + b2 * p2.2 + b3 * p3.2)
    (hb3 : 0 < b3)
    (hr1 : b1 ≤ 0 ∨ a3 * b1 ≤ a1 * b3)
    (hr2 : b2 ≤ 0 ∨ a3 * b2 ≤ a2 * b3) :
    InClosedTri y1 p1 p2 z := by
  have hb3_ne : b3 ≠ 0 := ne_of_gt hb3
  refine ⟨a3 / b3, a1 - (a3 / b3) * b1, a2 - (a3 / b3) * b2,
    div_nonneg ha3 (le_of_lt hb3), ?_, ?_, ?_, ?_, ?_⟩
  · rcases hr1 with hle | hmul
    · have : (a3 / b3) * b1 ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (div_nonneg ha3 (le_of_lt hb3)) hle
      linarith
    · rw [sub_nonneg, div_mul_eq_mul_div, div_le_iff₀ hb3]; linarith
  · rcases hr2 with hle | hmul
    · have : (a3 / b3) * b2 ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (div_nonneg ha3 (le_of_lt hb3)) hle
      linarith
    · rw [sub_nonneg, div_mul_eq_mul_div, div_le_iff₀ hb3]; linarith
  · field_simp [hb3_ne]; linear_combination b3 * hasum - a3 * hbsum
  · rw [hz1, hy1]; field_simp [hb3_ne]; ring
  · rw [hz2, hy2]; field_simp [hb3_ne]; ring

private lemma radon_step
    (a b y0 y1 z : ℝ × ℝ) (l1 l2 l3 c1 c2 c3 : ℝ)
    (hl1 : 0 ≤ l1) (hl2 : 0 ≤ l2) (hl3 : 0 ≤ l3) (hlsum : l1 + l2 + l3 = 1)
    (hz1 : z.1 = l1 * a.1 + l2 * b.1 + l3 * y0.1)
    (hz2 : z.2 = l1 * a.2 + l2 * b.2 + l3 * y0.2)
    (hcsum : c1 + c2 + c3 = 1)
    (hy1 : y1.1 = c1 * a.1 + c2 * b.1 + c3 * y0.1)
    (hy2 : y1.2 = c1 * a.2 + c2 * b.2 + c3 * y0.2) :
    InClosedTri y1 a b z ∨ InClosedTri y1 b y0 z ∨ InClosedTri y1 y0 a z := by
  by_cases h3 : 0 < c3 ∧ (c1 ≤ 0 ∨ l3 * c1 ≤ l1 * c3) ∧ (c2 ≤ 0 ∨ l3 * c2 ≤ l2 * c3)
  · left
    exact radon_case a b y0 y1 z l1 l2 l3 c1 c2 c3 hl1 hl2 hl3 hlsum hz1 hz2 hcsum hy1 hy2
      h3.1 h3.2.1 h3.2.2
  · by_cases h1 : 0 < c1 ∧ (c2 ≤ 0 ∨ l1 * c2 ≤ l2 * c1) ∧ (c3 ≤ 0 ∨ l1 * c3 ≤ l3 * c1)
    · right; left
      exact radon_case b y0 a y1 z l2 l3 l1 c2 c3 c1 hl2 hl3 hl1 (by linarith)
        (by rw [hz1]; ring) (by rw [hz2]; ring) (by linarith)
        (by rw [hy1]; ring) (by rw [hy2]; ring) h1.1 h1.2.1 h1.2.2
    · right; right
      have hc2_pos : 0 < c2 := by
        by_contra hc2_le
        have hc2 : c2 ≤ 0 := not_lt.mp hc2_le
        by_cases hc1_pos : 0 < c1
        · by_cases hc3_pos : 0 < c3
          · rcases le_total (l1 * c3) (l3 * c1) with hle13 | hle31
            · exact h1 ⟨hc1_pos, Or.inl hc2, Or.inr hle13⟩
            · exact h3 ⟨hc3_pos, Or.inr hle31, Or.inl hc2⟩
          · exact h1 ⟨hc1_pos, Or.inl hc2, Or.inl (not_lt.mp hc3_pos)⟩
        · have hc1 : c1 ≤ 0 := not_lt.mp hc1_pos
          have hc3_pos : 0 < c3 := by linarith
          exact h3 ⟨hc3_pos, Or.inl hc1, Or.inl hc2⟩
      have hr3 : c3 ≤ 0 ∨ l2 * c3 ≤ l3 * c2 := by
        by_cases hc3 : c3 ≤ 0
        · exact Or.inl hc3
        · right
          have hc3_pos : 0 < c3 := not_le.mp hc3
          by_contra hlt23
          replace hlt23 : l3 * c2 < l2 * c3 := not_le.mp hlt23
          by_cases hc1 : c1 ≤ 0
          · exact h3 ⟨hc3_pos, Or.inl hc1, Or.inr (le_of_lt hlt23)⟩
          · have hc1_pos : 0 < c1 := not_le.mp hc1
            rcases le_total (l3 * c1) (l1 * c3) with hle31 | hle13
            · exact h3 ⟨hc3_pos, Or.inr hle31, Or.inr (le_of_lt hlt23)⟩
            · have hle12 : l1 * c2 ≤ l2 * c1 := by nlinarith
              exact h1 ⟨hc1_pos, Or.inr hle12, Or.inr hle13⟩
      have hr1 : c1 ≤ 0 ∨ l2 * c1 ≤ l1 * c2 := by
        by_cases hc1 : c1 ≤ 0
        · exact Or.inl hc1
        · right
          have hc1_pos : 0 < c1 := not_le.mp hc1
          by_contra hlt21
          replace hlt21 : l1 * c2 < l2 * c1 := not_le.mp hlt21
          by_cases hc3 : c3 ≤ 0
          · exact h1 ⟨hc1_pos, Or.inr (le_of_lt hlt21), Or.inl hc3⟩
          · have hc3_pos : 0 < c3 := not_le.mp hc3
            rcases hr3 with hc3_le | hle23
            · linarith
            · have hle13 : l1 * c3 ≤ l3 * c1 := by nlinarith
              exact h1 ⟨hc1_pos, Or.inr (le_of_lt hlt21), Or.inr hle13⟩
      exact radon_case y0 a b y1 z l3 l1 l2 c3 c1 c2 hl3 hl1 hl2 (by linarith)
        (by rw [hz1]; ring) (by rw [hz2]; ring) (by linarith)
        (by rw [hy1]; ring) (by rw [hy2]; ring) hc2_pos hr3 hr1

theorem triangle_three_piece_cover
    (y0 y1 a b z : ℝ × ℝ)
    (hz : InClosedTri a b y0 z) :
    InClosedTri y1 a b z ∨ InClosedTri y1 b y0 z ∨ InClosedTri y1 y0 a z := by
  obtain ⟨l1, l2, l3, hl1, hl2, hl3, hlsum, hz1, hz2⟩ := hz
  let det := (b.1 - a.1) * (y0.2 - a.2) - (b.2 - a.2) * (y0.1 - a.1)
  by_cases hdet : det ≠ 0
  · let c2 := ((y1.1 - a.1) * (y0.2 - a.2) - (y1.2 - a.2) * (y0.1 - a.1)) / det
    let c3 := ((b.1 - a.1) * (y1.2 - a.2) - (b.2 - a.2) * (y1.1 - a.1)) / det
    let c1 := 1 - c2 - c3
    exact radon_step a b y0 y1 z l1 l2 l3 c1 c2 c3 hl1 hl2 hl3 hlsum hz1 hz2
      (by ring)
      (by dsimp only [c1, c2, c3]; field_simp [hdet]; dsimp only [det]; ring)
      (by dsimp only [c1, c2, c3]; field_simp [hdet]; dsimp only [det]; ring)
  · have hdet0 : (b.1 - a.1) * (y0.2 - a.2) - (b.2 - a.2) * (y0.1 - a.1) = 0 :=
      not_ne_iff.mp hdet
    by_cases hab : a = b
    · subst hab
      right; left
      exact ⟨0, l1 + l2, l3, le_rfl, add_nonneg hl1 hl2, hl3, by linarith,
        by rw [hz1]; ring, by rw [hz2]; ring⟩
    · have hab_coord : b.1 - a.1 ≠ 0 ∨ b.2 - a.2 ≠ 0 := by
        by_contra hc
        have hx0 : b.1 - a.1 = 0 := not_ne_iff.mp (not_or.mp hc).1
        have hy0 : b.2 - a.2 = 0 := not_ne_iff.mp (not_or.mp hc).2
        apply hab
        ext <;> linarith
      obtain ⟨t, ht1, ht2⟩ : ∃ t : ℝ, y0.1 = (1 - t) * a.1 + t * b.1 ∧ y0.2 = (1 - t) * a.2 + t * b.2 := by
        rcases hab_coord with hx | hy
        · refine ⟨(y0.1 - a.1) / (b.1 - a.1), ?_, ?_⟩
          · field_simp [hx]; ring
          · field_simp [hx]; linear_combination hdet0
        · refine ⟨(y0.2 - a.2) / (b.2 - a.2), ?_, ?_⟩
          · field_simp [hy]; linear_combination -hdet0
          · field_simp [hy]; ring
      by_cases ht0 : t ≤ 0
      · have h1t : 0 < 1 - t := by linarith
        have h1t_ne : 1 - t ≠ 0 := ne_of_gt h1t
        right; left
        refine ⟨0, l2 + l1 * (-t / (1 - t)), l3 + l1 * (1 / (1 - t)), le_rfl, ?_, ?_, ?_, ?_, ?_⟩
        · exact add_nonneg hl2 (mul_nonneg hl1 (div_nonneg (by linarith) (le_of_lt h1t)))
        · exact add_nonneg hl3 (mul_nonneg hl1 (div_nonneg zero_le_one (le_of_lt h1t)))
        · field_simp [h1t_ne]; linear_combination (1 - t) * hlsum
        · rw [hz1, ht1]; field_simp [h1t_ne]; ring
        · rw [hz2, ht2]; field_simp [h1t_ne]; ring
      · by_cases ht1_le : t ≤ 1
        · left
          refine ⟨0, l1 + l3 * (1 - t), l2 + l3 * t, le_rfl, ?_, ?_,
            by linear_combination hlsum, by rw [hz1, ht1]; ring, by rw [hz2, ht2]; ring⟩
          · exact add_nonneg hl1 (mul_nonneg hl3 (by linarith))
          · exact add_nonneg hl2 (mul_nonneg hl3 (by linarith))
        · have ht_pos : 0 < t := by linarith
          have ht_ne : t ≠ 0 := ne_of_gt ht_pos
          right; right
          refine ⟨0, l3 + l2 * (1 / t), l1 + l2 * ((t - 1) / t), le_rfl, ?_, ?_, ?_, ?_, ?_⟩
          · exact add_nonneg hl3 (mul_nonneg hl2 (div_nonneg zero_le_one (le_of_lt ht_pos)))
          · exact add_nonneg hl1 (mul_nonneg hl2 (div_nonneg (by linarith) (le_of_lt ht_pos)))
          · field_simp [ht_ne]; linear_combination t * hlsum
          · rw [hz1, ht1]; field_simp [ht_ne]; ring
          · rw [hz2, ht2]; field_simp [ht_ne]; ring
end Upper9Leaf_045

namespace Upper9Leaf_046

noncomputable section

def InOmega (p : ℝ × ℝ) : Prop := p.1 < 0 ∨ p.2 < 0
def swap2 (u : ℝ × ℝ) : ℝ × ℝ := (u.2, u.1)

open Classical in
def gamma (t : ℝ) : ℝ × ℝ :=
  if t ≤ 1 then (-t, 1 - t)
  else if t ≤ 2 then (t - 2, 1 - t)
  else (t - 2, t - 3)

open Classical in
def rayParam (z : ℝ × ℝ) : ℝ :=
  if 0 ≤ z.2 then -z.1 / (|z.1| + |z.2|)
  else 2 + z.1 / (|z.1| + |z.2|)

theorem gamma_swap_duality :
    (∀ t : ℝ, gamma (3 - t) = swap2 (gamma t)) ∧
    (∀ z : ℝ × ℝ, InOmega z → rayParam (swap2 z) = 3 - rayParam z) := by
  refine ⟨?_, ?_⟩
  · intro t
    unfold gamma swap2
    split_ifs <;> ext <;> dsimp <;> linarith
  · intro z hz
    have hs_pos : 0 < |z.1| + |z.2| := by
      rcases hz with h1 | h2
      · linarith [abs_pos.mpr (ne_of_lt h1), abs_nonneg z.2]
      · linarith [abs_nonneg z.1, abs_pos.mpr (ne_of_lt h2)]
    by_cases hz2 : 0 ≤ z.2
    · have hz1 : z.1 < 0 := by
        rcases hz with h1 | h2
        · exact h1
        · linarith
      unfold rayParam swap2
      dsimp
      rw [if_neg (by linarith), if_pos hz2, abs_of_neg hz1, abs_of_nonneg hz2]
      have hne : -z.1 + z.2 ≠ 0 := by linarith
      have hne' : z.2 + -z.1 ≠ 0 := by linarith
      field_simp [hne, hne']
      ring
    · replace hz2 : z.2 < 0 := not_le.mp hz2
      by_cases hz1 : 0 ≤ z.1
      · unfold rayParam swap2
        dsimp
        rw [if_pos hz1, if_neg (by linarith), abs_of_nonneg hz1, abs_of_neg hz2]
        have hne : z.1 + -z.2 ≠ 0 := by linarith
        have hne' : -z.2 + z.1 ≠ 0 := by linarith
        field_simp [hne, hne']
        ring
      · replace hz1 : z.1 < 0 := not_le.mp hz1
        unfold rayParam swap2
        dsimp
        rw [if_neg (by linarith), if_neg (by linarith), abs_of_neg hz1, abs_of_neg hz2]
        have hne : -z.1 + -z.2 ≠ 0 := by linarith
        have hne' : -z.2 + -z.1 ≠ 0 := by linarith
        field_simp [hne, hne']
        ring
end
end Upper9Leaf_046

namespace Upper9Leaf_047

noncomputable section

def InQ3 (p : ℝ × ℝ) : Prop := p.1 < 0 ∧ p.2 < 0
def dot2 (u v : ℝ × ℝ) : ℝ := u.1 * v.1 + u.2 * v.2
def det2 (u v : ℝ × ℝ) : ℝ := u.1 * v.2 - u.2 * v.1

open Classical in
def gamma (t : ℝ) : ℝ × ℝ :=
  if t ≤ 1 then (-t, 1 - t)
  else if t ≤ 2 then (t - 2, 1 - t)
  else (t - 2, t - 3)

open Classical in
def rayParam (z : ℝ × ℝ) : ℝ :=
  if 0 ≤ z.2 then -z.1 / (|z.1| + |z.2|)
  else 2 + z.1 / (|z.1| + |z.2|)

theorem supportF_branch_switch_core
    (p1 p2 : ℝ × ℝ)
    (hdet : 0 < det2 p1 p2)
    (hapex : InQ3 ((p2.2 - p1.2) / det2 p1 p2, (p1.1 - p2.1) / det2 p1 p2)) :
    let apex := ((p2.2 - p1.2) / det2 p1 p2, (p1.1 - p2.1) / det2 p1 p2)
    let tStar := rayParam apex
    1 < tStar ∧ tStar < 2 ∧
    0 < max (dot2 p1 (gamma tStar)) (dot2 p2 (gamma tStar)) ∧
    (∀ t : ℝ, 0 ≤ t → t < tStar → dot2 p2 (gamma t) < dot2 p1 (gamma t)) ∧
    (∀ t : ℝ, tStar < t → t ≤ 3 → dot2 p1 (gamma t) < dot2 p2 (gamma t)) := by
  dsimp only
  rcases hapex with ⟨ha1, ha2⟩
  dsimp only at ha1 ha2
  have hdet_ne : det2 p1 p2 ≠ 0 := ne_of_gt hdet
  have hd2 : p2.2 - p1.2 < 0 := by
    by_contra hge
    have : 0 ≤ (p2.2 - p1.2) / det2 p1 p2 := div_nonneg (not_lt.mp hge) (le_of_lt hdet)
    linarith
  have hd1 : 0 < p2.1 - p1.1 := by
    by_contra hle
    have : 0 ≤ (p1.1 - p2.1) / det2 p1 p2 := div_nonneg (by linarith [not_lt.mp hle]) (le_of_lt hdet)
    linarith
  let denom : ℝ := (p2.1 - p1.1) - (p2.2 - p1.2)
  have hdenom_pos : 0 < denom := by dsimp only [denom]; linarith
  have hdenom_ne : denom ≠ 0 := ne_of_gt hdenom_pos
  have htStar_eq :
      rayParam ((p2.2 - p1.2) / det2 p1 p2, (p1.1 - p2.1) / det2 p1 p2) =
      (2 * (p2.1 - p1.1) - (p2.2 - p1.2)) / denom := by
    unfold rayParam
    dsimp only
    rw [if_neg (by linarith), abs_of_neg ha1, abs_of_neg ha2]
    have hsum_eq :
        -((p2.2 - p1.2) / det2 p1 p2) + -((p1.1 - p2.1) / det2 p1 p2) =
        denom / det2 p1 p2 := by
      field_simp [hdet_ne]
      dsimp only [denom]
      ring
    rw [hsum_eq]
    field_simp [hdet_ne, hdenom_ne]
    dsimp only [denom]
    ring
  rw [htStar_eq]
  let tStar : ℝ := (2 * (p2.1 - p1.1) - (p2.2 - p1.2)) / denom
  have ht1 : 1 < tStar := by
    dsimp only [tStar]
    rw [lt_div_iff₀ hdenom_pos]
    dsimp only [denom]; linarith
  have ht2 : tStar < 2 := by
    dsimp only [tStar]
    rw [div_lt_iff₀ hdenom_pos]
    dsimp only [denom]; linarith
  refine ⟨ht1, ht2, ?_, ?_, ?_⟩
  · refine lt_of_lt_of_le ?_ (le_max_left _ _)
    unfold gamma dot2
    rw [if_neg (by linarith), if_pos (le_of_lt ht2)]
    dsimp only [tStar]
    have hval :
        p1.1 * ((2 * (p2.1 - p1.1) - (p2.2 - p1.2)) / denom - 2) +
        p1.2 * (1 - (2 * (p2.1 - p1.1) - (p2.2 - p1.2)) / denom) =
        det2 p1 p2 / denom := by
      field_simp [hdenom_ne]
      unfold det2
      dsimp only [denom]
      ring
    rw [hval]
    exact div_pos hdet hdenom_pos
  · intro t ht0 hlt
    unfold gamma dot2
    split_ifs with hle1 hle2
    · dsimp only
      by_cases ht_eq : t = 0
      · subst ht_eq; linarith
      · have ht_pos : 0 < t := lt_of_le_of_ne ht0 (Ne.symm ht_eq)
        have hm1 : 0 < (p2.1 - p1.1) * t := mul_pos hd1 ht_pos
        have hm2 : (p2.2 - p1.2) * (1 - t) ≤ 0 :=
          mul_nonpos_of_nonpos_of_nonneg (le_of_lt hd2) (by linarith)
        linarith
    · dsimp only
      have hdiff :
          (p2.1 * (t - 2) + p2.2 * (1 - t)) - (p1.1 * (t - 2) + p1.2 * (1 - t)) =
          t * denom - (2 * (p2.1 - p1.1) - (p2.2 - p1.2)) := by
        dsimp only [denom]; ring
      have hlt' : t * denom < 2 * (p2.1 - p1.1) - (p2.2 - p1.2) :=
        (lt_div_iff₀ hdenom_pos).mp hlt
      linarith
    · exfalso; linarith
  · intro t hgt ht3
    unfold gamma dot2
    split_ifs with hle1 hle2
    · exfalso; linarith
    · dsimp only
      have hdiff :
          (p2.1 * (t - 2) + p2.2 * (1 - t)) - (p1.1 * (t - 2) + p1.2 * (1 - t)) =
          t * denom - (2 * (p2.1 - p1.1) - (p2.2 - p1.2)) := by
        dsimp only [denom]; ring
      have hgt' : 2 * (p2.1 - p1.1) - (p2.2 - p1.2) < t * denom :=
        (div_lt_iff₀ hdenom_pos).mp hgt
      linarith
    · dsimp only
      have ht_gt2 : 2 < t := not_le.mp hle2
      have hm1 : 0 < (p2.1 - p1.1) * (t - 2) := mul_pos hd1 (by linarith)
      have hm2 : 0 ≤ (p2.2 - p1.2) * (t - 3) :=
        mul_nonneg_of_nonpos_of_nonpos (le_of_lt hd2) (by linarith)
      linarith
end
end Upper9Leaf_047

namespace Upper9Leaf_048

noncomputable section

def dot2 (u v : ℝ × ℝ) : ℝ := u.1 * v.1 + u.2 * v.2
def det2 (u v : ℝ × ℝ) : ℝ := u.1 * v.2 - u.2 * v.1

open Classical in
def gamma (t : ℝ) : ℝ × ℝ :=
  if t ≤ 1 then (-t, 1 - t)
  else if t ≤ 2 then (t - 2, 1 - t)
  else (t - 2, t - 3)

/-- `CaseAHull.ray_ties_zeros_disjoint` algebraic core on `[0, 3]` under `(GP1)`--`(GP4)`. -/
theorem ray_ties_zeros_core
    (v : Fin 10 → ℝ × ℝ)
    (h1 : ∀ a : Fin 10, (v a).1 ≠ 0 ∧ (v a).2 ≠ 0)
    (h2 : ∀ a b : Fin 10, a ≠ b → (v a).1 ≠ (v b).1 ∧ (v a).2 ≠ (v b).2)
    (h4 : ∀ a b c : Fin 10, a ≠ b → det2 (v a - v b) (v c) ≠ 0)
    (h5 : ∀ a b c d : Fin 10, a < b → c < d → (a, b) ≠ (c, d) →
      det2 (v a - v b) (v c - v d) ≠ 0) :
    (∀ t ∈ ({0, 1, 2, 3} : Finset ℝ), ∀ a b : Fin 10,
      dot2 (v a) (gamma t) ≠ 0 ∧ (a ≠ b → dot2 (v a) (gamma t) ≠ dot2 (v b) (gamma t))) ∧
    (∀ t : ℝ, 0 < t → t < 3 → ∀ a b : Fin 10, a ≠ b →
      dot2 (v a) (gamma t) = dot2 (v b) (gamma t) →
      let w := v a - v b
      t = w.2 / (w.1 + w.2) ∨ t = (2 * w.1 - w.2) / (w.1 - w.2) ∨ t = (2 * w.1 + 3 * w.2) / (w.1 + w.2)) ∧
    (∀ t : ℝ, 0 < t → t < 3 → ∀ a b c : Fin 10, a ≠ b →
      ¬ (dot2 (v a) (gamma t) = dot2 (v b) (gamma t) ∧ dot2 (v c) (gamma t) = 0)) ∧
    (∀ t : ℝ, 0 < t → t < 3 → ∀ a b c d : Fin 10, a < b → c < d → (a, b) ≠ (c, d) →
      ¬ (dot2 (v a) (gamma t) = dot2 (v b) (gamma t) ∧ dot2 (v c) (gamma t) = dot2 (v d) (gamma t))) := by
  contrapose h2
  norm_num[det2] at h4 h5⊢
  contrapose! h2
  use fun and _ _ _=>? _, fun and _ _ _ _ R L=>? _, fun and _ _ _ _ _ _ _ _=>? _, fun and _ _ _ _ _ _ _ _ _ _ _=>?_
  · simp_all[gamma,dot2]
    use (by match (by valid:) with |.inl a | (.inr (.inl a))|.inr ((.inr) (.inl a)) | (.inr (.inr (.inr a))) =>norm_num[ *]), (h4 _ _ (by(((bound)))) · ∘ (by·grind ) )
  · norm_num[gamma,dot2]at L⊢
    split_ifs at*
    · exact (.inl (eq_div_of_mul_eq (by bound[h2 _ _ R,congr_arg (and*.) ·]) (by linarith)))
    · exact (.inr (.inl (eq_div_of_mul_eq (h4 _ _ (by bound) R ∘ (by grind)) (by linear_combination L))))
    · exact (.inr (.inr (eq_div_of_mul_eq (h4 _ _ (by valid) R ∘ (by grind)) (by linarith))))
  · norm_num[gamma,dot2]at*
    split_ifs at*
    · exact (h4 _ _) (by assumption) (by valid) (mul_left_cancel₀ ↑(ne_of_gt (by assumption ) ) (by ·grind) )
    · exact (h4 _ _) (by assumption) (by assumption) (by grind)
    · grind
  · simp_all[gamma,dot2]
    split_ifs at*
    · exact (h5 _ _ _ _ (by apply_rules) (by valid) (by valid) (by grind))
    · exact (h5 _ _ _ _ (by apply_rules) (by valid) (by valid) (mul_left_cancel₀ (sub_ne_zero.2 (not_le.1 (by valid)).ne) (by grind)))
    · exact (h5 _ _ _ _ (by apply_rules) (by valid) (by valid) (mul_left_cancel₀ (sub_ne_zero.2 (not_le.1 (by valid)).ne') (by grind)))
end
end Upper9Leaf_048

namespace Upper9Leaf_049

/-- `CaseASweep.conservation_law`: exact integer conservation law on `[0, 3]` from
    `T_1 + T_2 + T_3 = 10`, `|X^+| + (T_1 + T_2) + T_1 = 30`, `|X^+| = k_1 + k_2 + k_3 + k_4`,
    `1 + k_4 = n_Ω`, and `Δ_q = (1 + k_q) - C(5, q)` for `q = 1, 2, 3` (`C(5,1)=5, C(5,2)=10, C(5,3)=10`). -/
theorem caseA_sweep_conservation_law
    (T1 T2 T3 Xplus k1 k2 k3 k4 nOmega : ℕ)
    (h_pairs : T1 + T2 + T3 = 10)
    (h_ties : Xplus + (T1 + T2) + T1 = 30)
    (h_part : Xplus = k1 + k2 + k3 + k4)
    (h_top : 1 + k4 = nOmega) :
    let Δ1 : ℤ := (1 + k1 : ℤ) - 5
    let Δ2 : ℤ := (1 + k2 : ℤ) - 10
    let Δ3 : ℤ := (1 + k3 : ℤ) - 10
    (nOmega : ℤ) + ((T1 + T2 : ℕ) : ℤ) + (T1 : ℤ) + Δ1 + Δ2 + Δ3 = 9 := by
  ((omega) )
end Upper9Leaf_049

namespace Upper9Leaf_050

def orient2d (a b c : ℝ × ℝ) : ℝ :=
  (b.1 - a.1) * (c.2 - a.2) - (b.2 - a.2) * (c.1 - a.1)

theorem prop_opposite_endpoint_exit_orient
    (d3 l h r d1 uD y0 : ℝ × ℝ)
    (μ0 μ1 μ2 ν0 ν1 ν2 : ℝ)
    (hμ0 : 0 < μ0) (hμ1 : 0 < μ1) (hμ2 : 0 < μ2) (hμ_sum : μ0 + μ1 + μ2 = 1)
    (hh1 : h.1 = μ0 * uD.1 + μ1 * r.1 + μ2 * d1.1)
    (hh2 : h.2 = μ0 * uD.2 + μ1 * r.2 + μ2 * d1.2)
    (hν0 : 0 < ν0) (hν1 : 0 < ν1) (hν2 : 0 < ν2) (hν_sum : ν0 + ν1 + ν2 = 1)
    (hy1 : y0.1 = ν0 * uD.1 + ν1 * d3.1 + ν2 * l.1)
    (hy2 : y0.2 = ν0 * uD.2 + ν1 * d3.2 + ν2 * l.2)
    (h_hrd3 : 0 < orient2d h r d3)
    (h_hd1d3 : 0 < orient2d h d1 d3)
    (h_d3lh : 0 < orient2d d3 l h)
    (h_d3lr : 0 < orient2d d3 l r)
    (h_d3hr : 0 < orient2d d3 h r)
    (h_lhr : 0 < orient2d l h r)
    (hy_d3l : 0 < orient2d d3 l y0)
    (hy_lh : 0 < orient2d l h y0) :
    0 < orient2d h d3 uD ∧ 0 < orient2d h d3 y0 ∧ 0 < orient2d d3 y0 r ∧ 0 < orient2d y0 h r := by
  have hid1 : μ0 * orient2d h d3 uD = μ1 * orient2d h r d3 + μ2 * orient2d h d1 d3 := by
    unfold orient2d
    linear_combination -(d3.1 - h.1) * hh2 + (d3.2 - h.2) * hh1 -
      ((d3.1 - h.1) * h.2 - (d3.2 - h.2) * h.1) * hμ_sum
  have h1 : 0 < orient2d h d3 uD := by
    have hrhs : 0 < μ1 * orient2d h r d3 + μ2 * orient2d h d1 d3 :=
      add_pos (mul_pos hμ1 h_hrd3) (mul_pos hμ2 h_hd1d3)
    by_contra hle
    have : μ0 * orient2d h d3 uD ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (le_of_lt hμ0) (not_lt.mp hle)
    linarith
  have hid2 : orient2d h d3 y0 = ν0 * orient2d h d3 uD + ν2 * orient2d d3 l h := by
    unfold orient2d
    linear_combination (d3.1 - h.1) * hy2 - (d3.2 - h.2) * hy1 +
      ((d3.1 - h.1) * h.2 - (d3.2 - h.2) * h.1) * hν_sum
  have h2 : 0 < orient2d h d3 y0 := by
    rw [hid2]
    exact add_pos (mul_pos hν0 h1) (mul_pos hν2 h_d3lh)
  have hid3 :
      orient2d d3 l h * orient2d d3 y0 r =
      orient2d h d3 y0 * orient2d d3 l r + orient2d d3 l y0 * orient2d d3 h r := by
    unfold orient2d; ring
  have h3 : 0 < orient2d d3 y0 r := by
    have hrhs : 0 < orient2d h d3 y0 * orient2d d3 l r + orient2d d3 l y0 * orient2d d3 h r :=
      add_pos (mul_pos h2 h_d3lr) (mul_pos hy_d3l h_d3hr)
    by_contra hle
    have : orient2d d3 l h * orient2d d3 y0 r ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (le_of_lt h_d3lh) (not_lt.mp hle)
    linarith
  have hid4 :
      orient2d d3 l h * orient2d y0 h r =
      orient2d l h y0 * orient2d d3 h r + orient2d h d3 y0 * orient2d l h r := by
    unfold orient2d; ring
  have h4 : 0 < orient2d y0 h r := by
    have hrhs : 0 < orient2d l h y0 * orient2d d3 h r + orient2d h d3 y0 * orient2d l h r :=
      add_pos (mul_pos hy_lh h_d3hr) (mul_pos h2 h_lhr)
    by_contra hle
    have : orient2d d3 l h * orient2d y0 h r ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (le_of_lt h_d3lh) (not_lt.mp hle)
    linarith
  exact ⟨h1, h2, h3, h4⟩
end Upper9Leaf_050

namespace Upper9Leaf_051

def permInversions (σ : Equiv.Perm (Fin 5)) : ℕ :=
  (((Finset.univ : Finset (Fin 5 × Fin 5)).filter
    fun p => p.1 < p.2 ∧ σ p.2 < σ p.1)).card

/-- `CaseAElim.elim_n6_all`: if color `0` is both the leftmost top color and the rightmost top
    color `σ 4 = 0` (`(1, 6)` repeat pattern on `H_Ω`), then `σ` has at least `4` inversions. -/
theorem elim_n6_repeat_1_6_inv_ge_four
    (σ : Equiv.Perm (Fin 5))
    (h0 : σ ⟨4, by omega⟩ = ⟨0, by omega⟩) :
    4 ≤ permInversions σ := by
  push_cast[permInversions]at*
  use not_lt.1<|absurd (Finset.ext_iff.1 (by decide:.filter (fun p=> Finset.card {(a, b):_ ×_|a<b∧p b<p a}<4) ({p|p 4=0})={}) σ) ∘by simp_all
end Upper9Leaf_051

namespace Upper9Leaf_052

open scoped Classical

noncomputable section

/-- Cut-edge non-wraparound in `Ω`: if `v₁ ∈ Q₂`, `vₕ ∈ Q₄`, and `(1 - λ) vₕ + λ v₁ = (t_*, t_*)`
    with `0 < λ < 1` and `0 < t_*`, then no `z ∈ Ω` satisfies both `v₁ · z > 1` and `vₕ · z > 1`. -/
lemma no_both_cut_vertices_in_omega
    (v1x v1y vhx vhy lam t_star zx zy : ℝ)
    (hv1x : v1x < 0) (hv1y : 0 < v1y)
    (hvhx : 0 < vhx) (hvhy : vhy < 0)
    (hlam0 : 0 < lam) (hlam1 : lam < 1) (ht : 0 < t_star)
    (hmx : (1 - lam) * vhx + lam * v1x = t_star)
    (hmy : (1 - lam) * vhy + lam * v1y = t_star)
    (hz : zx < 0 ∨ zy < 0) :
    ¬ (v1x * zx + v1y * zy > 1 ∧ vhx * zx + vhy * zy > 1) := by
  rcases↑hz
  · use fun and=>by if a:zy<0 then nlinarith else nlinarith
  · use fun and=>by nlinarith[mul_neg_of_pos_of_neg hlam0 hv1x,mul_neg_of_pos_of_neg hlam0 hvhy, mul_neg_of_pos_of_neg hv1y (by valid), (by nlinarith:zx<0)]

end
end Upper9Leaf_052

namespace Upper9Leaf_053

def permInversions (σ : Equiv.Perm (Fin 5)) : ℕ :=
  (((Finset.univ : Finset (Fin 5 × Fin 5)).filter
    fun p => p.1 < p.2 ∧ σ p.2 < σ p.1)).card

/-- `CaseAElim` disjointness of Left Certificate (`M_L ∈ {{4}, {3, 4}}`) and Right Certificate
    (`M_R ∈ {{σ 0}, {σ 0, σ 1}}`) whenever `inv(σ) ≤ 4` and `σ 0 ≠ 4`. -/
theorem left_right_cert_sets_disjoint
    (σ : Equiv.Perm (Fin 5))
    (hinv : permInversions σ ≤ 4)
    (hnot4 : σ ⟨0, by omega⟩ ≠ ⟨4, by omega⟩) :
    ({⟨4, by omega⟩} : Finset (Fin 5)) ≠ {σ ⟨0, by omega⟩} ∧
    ({⟨4, by omega⟩} : Finset (Fin 5)) ≠ {σ ⟨0, by omega⟩, σ ⟨1, by omega⟩} ∧
    ({⟨3, by omega⟩, ⟨4, by omega⟩} : Finset (Fin 5)) ≠ {σ ⟨0, by omega⟩} ∧
    ({⟨3, by omega⟩, ⟨4, by omega⟩} : Finset (Fin 5)) ≠ {σ ⟨0, by omega⟩, σ ⟨1, by omega⟩} := by
  simp_all[permInversions,Set.pair_eq_pair_iff]
  simp_all+decide-contextual[σ.surjective _,mt (congr_arg Finset.card), Fin.sum_univ_five _, Fintype.sum_prod_type _, Finset.ext_iff]
  push_cast[σ.surjective _, Fintype.sum_prod_type, Fin.sum_univ_five, Finset.card_filter]at*
  refine ⟨Ne.symm hnot4,not_forall.1 fun and=>absurd (Equiv.sum_comp σ (if.<3 then(1)else 0)) (( Fin.sum_univ_five _).trans_ne fun and' =>? _)⟩
  simp_all+decide-contextual[←((and _).1 _).resolve_left (Ne.symm hnot4)]
  use absurd hinv<|absurd and' ∘((( and 3 ).1 (by decide)).resolve_right nofun▸by cases σ (2) with cases σ (3) with cases σ 4 with decide+revert)
end Upper9Leaf_053

namespace Upper9Leaf_054

def permInversions (σ : Equiv.Perm (Fin 5)) : ℕ :=
  (((Finset.univ : Finset (Fin 5 × Fin 5)).filter
    fun p => p.1 < p.2 ∧ σ p.2 < σ p.1)).card

/-- `CaseAElim.elim_n8_to_10` combinatorial core: for every `σ ∈ S_5` (`inv(σ) ≤ 4`, `σ 0 ≠ 4`)
    and every `3`-crossing subgraph `G3` of concordant pairs (`i < j ∧ σ i < σ j`),
    `T̄_3 + T_1 + d_L + d_R ≥ 2` (`n_Ω ≤ 9 - 2 = 7`). -/
theorem caseA_T3bar_T1_dLdR_ge_two
    (σ : Equiv.Perm (Fin 5))
    (G3 : Fin 5 → Fin 5 → Bool)
    (h_conc : ∀ i j : Fin 5, G3 i j = true → i < j ∧ σ i < σ j) :
    let pairs := (Finset.univ : Finset (Fin 5 × Fin 5)).filter (fun p => p.1 < p.2)
    let T3 := (pairs.filter (fun p => G3 p.1 p.2 = true)).card
    let T3bar := 10 - T3
    let T1 := (pairs.filter (fun p => σ p.1 < σ p.2 ∧ G3 p.1 p.2 = false)).card
    let dL := if G3 0 4 = true ∧ G3 1 4 = true ∧ G3 2 4 = true then 1 else 0
    let dR := if G3 (min (σ 0) (σ 2)) (max (σ 0) (σ 2)) = true ∧
                 G3 (min (σ 0) (σ 3)) (max (σ 0) (σ 3)) = true ∧
                 G3 (min (σ 0) (σ 4)) (max (σ 0) (σ 4)) = true then 1 else 0
    2 ≤ T3bar + T1 + dL + dR := by
  simp_rw [←Bool.not_eq_true, Finset.filter_and, add_assoc, Finset.filter_not]
  cases Finset.eq_empty_or_nonempty (.filter (fun(a, b)=>a<b ∧σ a<σ b) .univ\.filter (fun(a, b)=>G3 a b = true) {(a, b):_ ×_|a<b})
  · norm_num[Finset.ext_iff]at*
    split
    · split
      · match σ 0 with | 0 => omega | 1 => omega | 2 => omega | 3 => omega | 4 => omega
      push_cast[←add_assoc]
      use le_add_right<|Nat.sub_pos_of_lt (Finset.card_lt_card ⟨ Finset.filter_subset _ _,by valid ∘ fun and=>?_⟩)
      norm_num+decide[h_conc 0, Finset.mem_filter.1 (@and (_, _) ↑ _),le_of_lt]
    use le_add_right (Nat.le_sub_of_add_le ? _)
    push_cast[add_comm 2, Fintype.sum_prod_type,Fin.sum_univ_five, Finset.card_filter]
    push_cast[ Fintype.sum_prod_type, Fin.sum_univ_five, Finset.sum_filter]
    split
    · grind
    · grind
  · by_cases h: Finset.univ.filter (fun(a, b)=>a<b)=.filter (fun(a, b)=>a<b∧σ a<σ b) .univ
    · norm_num+decide[StrictMono.le_iff_le fun and a s=>(Finset.mem_filter.1 (h.le (by norm_num[s] : (and,a) ∈_))).2.2,Finset.card_sdiff,Finset.inter_eq_right.2]at*
      replace h:StrictMono σ
      · use fun and a s=>(Finset.mem_filter.1 (( Finset.ext_iff.1 h (_, _)).1 (by norm_num[s]))).2.2
      simp_all+decide[<-Finset.inter_sdiff_assoc,h.range_inj strictMono_id|>.1]
      simp_all[Nat.succ_le,Finset.filter_true_of_mem]
      use lt_add_of_pos_of_le (tsub_pos_of_lt (Finset.card_lt_card ⟨ Finset.filter_subset _ _ , (by valid:).elim fun and R M=>(Finset.mem_sdiff.1 R).elim fun and true => true (M and)⟩)) (le_add_right (by valid:).card_pos)
    · use le_add_right ((2).le_sub_of_add_le' (not_lt.1 (h ∘symm ∘ Finset.eq_of_subset_of_card_le ( fun and=>by simp_all) ∘?_)))
      simp_all+decide[Nat.eq_sub_of_add_eq ( Finset.card_sdiff_add_card_inter _ _),Nat.succ_le]
      exact (Nat.le_of_lt_succ ·.le_pred|>.trans_lt (Finset.card_lt_card ⟨ fun and=>by simp_all,‹ Finset.Nonempty _›.elim fun and R M=>absurd (@M and) (by simp_all)⟩))
end Upper9Leaf_054

namespace Upper9Leaf_055

/-- `CaseAElim.left_certificate` order-splitting core at `t_0 < t_4`:
    either `M_L = {4}` or `M_L = {3, 4}` has `F_u(t_4) < F_v(t_4)` for all `u ∈ M_L, v ∉ M_L`
    while `F_0(t_0) < F_4(t_0)` (`0 ∉ M_L, 4 ∈ M_L`). -/
theorem left_cert_order_dichotomy
    (F_t0 F_t4 : Fin 5 → ℝ)
    (h04_t0 : F_t0 0 < F_t0 4)
    (h40_t4 : F_t4 4 < F_t4 0)
    (h41_t4 : F_t4 4 < F_t4 1)
    (h42_t4 : F_t4 4 < F_t4 2)
    (h34_ne : F_t4 3 ≠ F_t4 4) :
    (F_t0 0 < F_t0 4 ∧ ∀ v : Fin 5, v ≠ 4 → F_t4 4 < F_t4 v) ∨
    (F_t0 0 < F_t0 4 ∧ ∀ u ∈ ({3, 4} : Finset (Fin 5)), ∀ v : Fin 5,
      v ∉ ({3, 4} : Finset (Fin 5)) → F_t4 u < F_t4 v) := by
  simp_all+decide -contextual [imp_iff_not_or, true,h34_ne.symm.lt_of_le, false, Fin.forall_iff_succ]
  exact (lt_or_gt_of_ne (by valid)).symm.imp_right (by simp_all[·.trans])
end Upper9Leaf_055

namespace Upper9Leaf_056

/-- `CaseAElim.elim_n7_all` Subcase 3 (`T̄_3 = 1, T_1 = 1`, unique non-edge `{0, 4}`):
    comparing `(F_0, F_4)` at `t_0` and `t_4` forces a `0 → >0 → 0` split for `{4}` across
    `(τ_-, t_1, t_4)`, for `{0}` across `(t_0, t_1, τ_+)`, or for `{0, 4}` across `(t_0, t_1, t_4)`. -/
theorem caseA_n7_T3bar1_T11_dichotomy
    (F_tm F_t0 F_t1 F_t4 F_tp : Fin 5 → ℝ)
    (htm : ∀ v : Fin 5, v ≠ 4 → F_tm 4 < F_tm v)
    (htp : ∀ v : Fin 5, v ≠ 0 → F_tp 0 < F_tp v)
    (ht1_0 : F_t1 1 < F_t1 0)
    (ht1_4 : F_t1 1 < F_t1 4)
    (ht0_mid : F_t0 0 < F_t0 1 ∧ F_t0 0 < F_t0 2 ∧ F_t0 0 < F_t0 3)
    (ht4_mid : F_t4 4 < F_t4 1 ∧ F_t4 4 < F_t4 2 ∧ F_t4 4 < F_t4 3)
    (ht0_ne : F_t0 0 ≠ F_t0 4)
    (ht4_ne : F_t4 0 ≠ F_t4 4) :
    ((∀ v : Fin 5, v ≠ 4 → F_tm 4 < F_tm v) ∧ F_t1 1 < F_t1 4 ∧
      (∀ v : Fin 5, v ≠ 4 → F_t4 4 < F_t4 v)) ∨
    ((∀ v : Fin 5, v ≠ 0 → F_t0 0 < F_t0 v) ∧ F_t1 1 < F_t1 0 ∧
      (∀ v : Fin 5, v ≠ 0 → F_tp 0 < F_tp v)) ∨
    ((∀ u ∈ ({0, 4} : Finset (Fin 5)), ∀ v : Fin 5, v ∉ ({0, 4} : Finset (Fin 5)) → F_t0 u < F_t0 v) ∧
      F_t1 1 < F_t1 0 ∧
      (∀ u ∈ ({0, 4} : Finset (Fin 5)), ∀ v : Fin 5, v ∉ ({0, 4} : Finset (Fin 5)) → F_t4 u < F_t4 v)) := by
  simp_all+decide -contextual[imp_iff_not_or, false,ht4_ne.symm.lt_or_gt, false, Fin.forall_iff_succ]
  exact (lt_or_ge _ _).imp_right ((lt_or_ge _ _).imp_right fun and=>by simp_all only[·.trans_lt, and.trans_lt, and_self])
end Upper9Leaf_056

namespace Upper9Leaf_057

def permInversions (σ : Equiv.Perm (Fin 5)) : ℕ :=
  (((Finset.univ : Finset (Fin 5 × Fin 5)).filter
    fun p => p.1 < p.2 ∧ σ p.2 < σ p.1)).card

theorem caseA_n7_inv_one_or_two_ge_three
    (σ : Equiv.Perm (Fin 5))
    (hinv : permInversions σ = 1 ∨ permInversions σ = 2) :
    let g3 := fun i j : Fin 5 => decide (i < j ∧ σ i < σ j)
    let dL := if g3 0 4 = true ∧ g3 1 4 = true ∧ g3 2 4 = true then 1 else 0
    let dR := if g3 (min (σ 0) (σ 2)) (max (σ 0) (σ 2)) = true ∧
                 g3 (min (σ 0) (σ 3)) (max (σ 0) (σ 3)) = true ∧
                 g3 (min (σ 0) (σ 4)) (max (σ 0) (σ 4)) = true then 1 else 0
    3 ≤ permInversions σ + dL + dR := by
  revert σ hinv
  decide +kernel
end Upper9Leaf_057

namespace Upper9Leaf_058

noncomputable section

def InOmega (p : ℝ × ℝ) : Prop := p.1 < 0 ∨ p.2 < 0
def dot2 (u v : ℝ × ℝ) : ℝ := u.1 * v.1 + u.2 * v.2
def det2 (u v : ℝ × ℝ) : ℝ := u.1 * v.2 - u.2 * v.1

open Classical in
def gamma (t : ℝ) : ℝ × ℝ :=
  if t ≤ 1 then (-t, 1 - t)
  else if t ≤ 2 then (t - 2, 1 - t)
  else (t - 2, t - 3)

private lemma span_lt_two_of_inOmega
    {q : ℝ × ℝ} (hq : InOmega q) {a b : ℝ}
    (ha0 : 0 < a) (hab : a < b) (hb3 : b < 3)
    (hpa : 0 < dot2 q (gamma a)) (hpb : 0 < dot2 q (gamma b)) :
    b - a < 2 := by
  by_contra hge
  replace hge : 2 ≤ b - a := not_lt.mp hge
  have ha1 : a ≤ 1 := by linarith
  have hb2 : 2 < b := by linarith
  unfold gamma dot2 at hpa hpb
  rw [if_pos ha1] at hpa
  rw [if_neg (by linarith), if_neg (by linarith)] at hpb
  dsimp only at hpa hpb
  -- On a ∈ (0, 1) and b ∈ (2, 3) with b - a ≥ 2 (so 0 ≤ (b - 2) - a):
  -- q.1 * (-a) + q.2 * (1 - a) > 0 and q.1 * (b - 2) + q.2 * (b - 3) > 0:
  have hqx : 0 < q.1 := by
    -- Eliminate q.2 using (3 - b) ≥ 0 and (1 - a) ≥ 0:
    have hc1 : 0 < 3 - b := by linarith
    have hc2 : 0 ≤ 1 - a := by linarith
    -- (3 - b) * hpa + (1 - a) * hpb = ((1 - a)*(b - 2) - a*(3 - b)) * q.1 = (b - a - 2) * q.1? Check:
    -- (1 - a)*(b - 2) - a*(3 - b) = b - 2 - a*b + 2*a - 3*a + a*b = b - a - 2 ≥ 0!
    -- Even better: if b - a = 2, (3 - b)*hpa + (1 - a)*hpb = 0 > 0 contradiction!
    -- And if b - a > 2, (b - a - 2) * q.1 > 0 => q.1 > 0!
    have hid : (b - a - 2) * q.1 =
        (3 - b) * (q.1 * (-a) + q.2 * (1 - a)) + (1 - a) * (q.1 * (b - 2) + q.2 * (b - 3)) := by ring
    have hrhs : 0 < (3 - b) * (q.1 * (-a) + q.2 * (1 - a)) + (1 - a) * (q.1 * (b - 2) + q.2 * (b - 3)) := by
      have t1 : 0 < (3 - b) * (q.1 * (-a) + q.2 * (1 - a)) := mul_pos hc1 hpa
      have t2 : 0 ≤ (1 - a) * (q.1 * (b - 2) + q.2 * (b - 3)) := mul_nonneg hc2 (le_of_lt hpb)
      linarith
    have hba_pos : 0 < b - a - 2 := by
      rcases eq_or_lt_of_le hge with heq | hgt
      · exfalso; rw [← heq] at hid; linarith
      · linarith
    by_contra hq1_le
    have : (b - a - 2) * q.1 ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (le_of_lt hba_pos) (not_lt.mp hq1_le)
    linarith
  have hqy : 0 < q.2 := by
    have hid : (b - a - 2) * q.2 =
        (b - 2) * (q.1 * (-a) + q.2 * (1 - a)) + a * (q.1 * (b - 2) + q.2 * (b - 3)) := by ring
    have hrhs : 0 < (b - 2) * (q.1 * (-a) + q.2 * (1 - a)) + a * (q.1 * (b - 2) + q.2 * (b - 3)) :=
      add_pos (mul_pos (by linarith) hpa) (mul_pos ha0 hpb)
    have hba_pos : 0 < b - a - 2 := by
      rcases eq_or_lt_of_le hge with heq | hgt
      · exfalso; rw [← heq] at hid; linarith
      · linarith
    by_contra hq2_le
    have : (b - a - 2) * q.2 ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (le_of_lt hba_pos) (not_lt.mp hq2_le)
    linarith
  rcases hq with hx | hy <;> linarith

private lemma gamma_det2_pos {s₁ s₂ : ℝ}
    (h0 : 0 < s₁) (hlt : s₁ < s₂) (h3 : s₂ < 3) (hspan : s₂ - s₁ < 2) :
    0 < det2 (gamma s₁) (gamma s₂) := by
  unfold gamma det2
  split_ifs with ha1 ha2 hb1 hb2 hb2' hc2 hc2'
  · dsimp only; nlinarith
  · dsimp only
    have hp1 : 0 ≤ (1 - s₁) * (2 - s₂) := mul_nonneg (by linarith) (by linarith)
    have hp2 : 0 < s₁ * (s₂ - 1) := mul_pos h0 (by linarith)
    nlinarith
  · dsimp only; linarith
  · exfalso; linarith
  · dsimp only; nlinarith
  · dsimp only
    have hp1 : 0 ≤ (2 - s₁) * (3 - s₂) := mul_nonneg (by linarith) (by linarith)
    have hp2 : 0 < (s₁ - 1) * (s₂ - 2) := mul_pos (by linarith) (by linarith)
    nlinarith
  · exfalso; linarith
  · exfalso; linarith
  · dsimp only; nlinarith

theorem caseA_hull_approval_contiguity_core
    (w1 wj w2 : ℝ × ℝ) (t1 tj t2 t ρ : ℝ)
    (hw1 : InOmega w1) (hw2 : InOmega w2)
    (h01 : 0 < t1) (h1j : t1 < tj) (hj2 : tj < t2) (h23 : t2 < 3)
    (ht0 : 0 < t) (ht3 : t < 3) (hρ : 0 < ρ)
    (h1_pos : 0 < dot2 w1 (gamma t1))
    (h2_pos : 0 < dot2 w2 (gamma t2))
    (h1_dom : dot2 wj (gamma t1) < dot2 w1 (gamma t1))
    (hj_dom1 : dot2 w1 (gamma tj) < dot2 wj (gamma tj))
    (hj_dom2 : dot2 w2 (gamma tj) < dot2 wj (gamma tj))
    (h2_dom : dot2 wj (gamma t2) < dot2 w2 (gamma t2))
    (ht_w1 : ρ < dot2 w1 (gamma t))
    (ht_w2 : ρ < dot2 w2 (gamma t)) :
    ρ < dot2 wj (gamma t) := by
  by_cases hteq : t = tj
  · subst hteq; linarith
  · rcases lt_or_gt_of_ne hteq with hlt | hgt
    · -- t < tj < t2: compare wj and w2 using w2 ∈ Ω
      have hspan : t2 - t < 2 :=
        span_lt_two_of_inOmega hw2 ht0 (lt_trans hlt hj2) h23 (lt_trans hρ ht_w2) h2_pos
      have hd_outer : 0 < det2 (gamma t) (gamma t2) :=
        gamma_det2_pos ht0 (lt_trans hlt hj2) h23 hspan
      have hd_right : 0 < det2 (gamma tj) (gamma t2) :=
        gamma_det2_pos (lt_trans h01 h1j) hj2 h23 (by linarith)
      have hd_left : 0 < det2 (gamma t) (gamma tj) :=
        gamma_det2_pos ht0 hlt (lt_trans hj2 h23) (by linarith)
      have hcramer :
          det2 (gamma t) (gamma t2) * (dot2 wj (gamma tj) - dot2 w2 (gamma tj)) =
          det2 (gamma tj) (gamma t2) * (dot2 wj (gamma t) - dot2 w2 (gamma t)) +
          det2 (gamma t) (gamma tj) * (dot2 wj (gamma t2) - dot2 w2 (gamma t2)) := by
        unfold det2 dot2; ring
      have hpos_lhs : 0 < det2 (gamma t) (gamma t2) * (dot2 wj (gamma tj) - dot2 w2 (gamma tj)) :=
        mul_pos hd_outer (by linarith)
      have hneg_rhs : det2 (gamma t) (gamma tj) * (dot2 wj (gamma t2) - dot2 w2 (gamma t2)) < 0 :=
        mul_neg_of_pos_of_neg hd_left (by linarith)
      have hpos_mid : 0 < det2 (gamma tj) (gamma t2) * (dot2 wj (gamma t) - dot2 w2 (gamma t)) := by
        linarith
      have hdiff_pos : 0 < dot2 wj (gamma t) - dot2 w2 (gamma t) := by
        by_contra hle
        have : det2 (gamma tj) (gamma t2) * (dot2 wj (gamma t) - dot2 w2 (gamma t)) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos (le_of_lt hd_right) (not_lt.mp hle)
        linarith
      linarith
    · -- t1 < tj < t: compare wj and w1 using w1 ∈ Ω
      have hspan : t - t1 < 2 :=
        span_lt_two_of_inOmega hw1 h01 (lt_trans h1j hgt) ht3 h1_pos (lt_trans hρ ht_w1)
      have hd_outer : 0 < det2 (gamma t1) (gamma t) :=
        gamma_det2_pos h01 (lt_trans h1j hgt) ht3 hspan
      have hd_left : 0 < det2 (gamma t1) (gamma tj) :=
        gamma_det2_pos h01 h1j (lt_trans hj2 h23) (by linarith)
      have hd_right : 0 < det2 (gamma tj) (gamma t) :=
        gamma_det2_pos (lt_trans h01 h1j) hgt ht3 (by linarith)
      have hcramer :
          det2 (gamma t1) (gamma t) * (dot2 wj (gamma tj) - dot2 w1 (gamma tj)) =
          det2 (gamma tj) (gamma t) * (dot2 wj (gamma t1) - dot2 w1 (gamma t1)) +
          det2 (gamma t1) (gamma tj) * (dot2 wj (gamma t) - dot2 w1 (gamma t)) := by
        unfold det2 dot2; ring
      have hpos_lhs : 0 < det2 (gamma t1) (gamma t) * (dot2 wj (gamma tj) - dot2 w1 (gamma tj)) :=
        mul_pos hd_outer (by linarith)
      have hneg_rhs : det2 (gamma tj) (gamma t) * (dot2 wj (gamma t1) - dot2 w1 (gamma t1)) < 0 :=
        mul_neg_of_pos_of_neg hd_right (by linarith)
      have hpos_mid : 0 < det2 (gamma t1) (gamma tj) * (dot2 wj (gamma t) - dot2 w1 (gamma t)) := by
        linarith
      have hdiff_pos : 0 < dot2 wj (gamma t) - dot2 w1 (gamma t) := by
        by_contra hle
        have : det2 (gamma t1) (gamma tj) * (dot2 wj (gamma t) - dot2 w1 (gamma t)) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos (le_of_lt hd_left) (not_lt.mp hle)
        linarith
      linarith
end
end Upper9Leaf_058

namespace Upper9Leaf_059

/-- `CaseAHull.interior_assisted_pairs` combinatorial core:
    Suppose active hull indices `A_hull : Fin h → Bool` are either empty or a contiguous interval
    `[r₁, r₂]`, `S` (`S.card = 2`) is NOT equal to the `hullColors` image of any nonempty interval
    `[a, b]`, and `S` equals the union of active hull colors and active non-hull colors.
    Then some active non-hull vector `a` has color in `S` with NO active hull vertex of that color. -/
theorem interior_assisted_pair_exists
    {h : ℕ} (hh : 0 < h)
    (hullIdx : Fin h → Fin 10)
    (vecColor : Fin 10 → Fin 5)
    (active : Fin 10 → Bool)
    (S : Finset (Fin 5))
    (hS2 : S.card = 2)
    (h_contig : (∀ r : Fin h, active (hullIdx r) = false) ∨
      ∃ r₁ r₂ : Fin h, r₁ ≤ r₂ ∧ ∀ r : Fin h, active (hullIdx r) = true ↔ r₁ ≤ r ∧ r ≤ r₂)
    (hnot_pure : ∀ r₁ r₂ : Fin h, r₁ ≤ r₂ →
      (Finset.univ.filter (fun r : Fin h => r₁ ≤ r ∧ r ≤ r₂)).image (fun r => vecColor (hullIdx r)) ≠ S)
    (hreal : ∀ i : Fin 5, i ∈ S ↔ ∃ a : Fin 10, vecColor a = i ∧ active a = true) :
    ∃ a : Fin 10, (∀ r : Fin h, hullIdx r ≠ a) ∧ vecColor a ∈ S ∧ active a = true ∧
      ∀ r : Fin h, vecColor (hullIdx r) = vecColor a → active (hullIdx r) = false := by
  rcases‹_ ∨_› with a| ⟨a, true,A, B⟩
  · exact ( (S.card_pos.1 (by valid))).elim fun and x =>((hreal _).mp x).imp fun and⟨A, B⟩=>⟨fun R M=> (by cases a R▸M▸B), A▸x,B,fun R L=>a R⟩
  · exact ( Finset.not_subset.1 (hnot_pure _ _ A ∘ antisymm (Finset.image_subset_iff.2 fun and μ=>(hreal _).2 ⟨ _,rfl,(B _).2 (Finset.mem_filter.1 μ).2⟩))).elim fun and x =>((hreal _).1 x.1).imp (by grind)
end Upper9Leaf_059

namespace Upper9Leaf_060

/-- `CaseAHull.dual_island_rule` combinatorial core:
    If every active non-hull vector forces at least one hull vertex to be active, and active hull
    vertices are contiguous whenever nonempty, then for any nonempty realized color set `S`,
    the active hull vertices form a nonempty contiguous interval `[r₁, r₂]` with colors in `S`. -/
theorem dual_island_rule_core
    {h : ℕ} (hh : 0 < h)
    (hullIdx : Fin h → Fin 10)
    (vecColor : Fin 10 → Fin 5)
    (active : Fin 10 → Bool)
    (S : Finset (Fin 5))
    (hne : S.Nonempty)
    (h_dom : ∀ a : Fin 10, (∀ r : Fin h, hullIdx r ≠ a) → active a = true →
      ∃ r : Fin h, active (hullIdx r) = true)
    (h_contig : ∀ r₁ r₂ r₃ : Fin h, r₁ < r₂ → r₂ < r₃ →
      active (hullIdx r₁) = true → active (hullIdx r₃) = true → active (hullIdx r₂) = true)
    (hreal : ∀ i : Fin 5, i ∈ S ↔ ∃ a : Fin 10, vecColor a = i ∧ active a = true) :
    ∃ r₁ r₂ : Fin h, r₁ ≤ r₂ ∧
      (∀ r : Fin h, active (hullIdx r) = true ↔ r₁ ≤ r ∧ r ≤ r₂) ∧
      (∀ r : Fin h, r₁ ≤ r → r ≤ r₂ → vecColor (hullIdx r) ∈ S) := by
  by_cases h : {s | ‹∀s,Bool› (hullIdx s)}.Nonempty
  · refine(Set.exists_min_image _ id Subtype.finite h).imp fun and⟨A, B⟩=>(Set.exists_max_image _ id Subtype.finite h).imp fun and ⟨a, C⟩=>⟨B and a,? _, fun and R L=>(hreal _).2 ⟨ _,rfl,?_⟩⟩
    · use fun and=>⟨fun R=>⟨B and R, C and R⟩,And.elim (·.eq_or_lt.elim (.▸A) fun and' =>·.eq_or_lt.elim ((.▸ a)) (by tauto))⟩
    · use R.eq_or_lt.elim (.▸A) (L.eq_or_lt.elim ((.▸ a)) ∘by tauto)
  · rcases h.comp ( (hreal _).mp @hne.choose_spec).elim fun and x =>(h_dom and (h ⟨·,by apply.▸x.2⟩) x.2).imp (by cases‹ℕ› with norm_num)
end Upper9Leaf_060

namespace Upper9Leaf_061

/-- `CaseAHull.hull_five_colors` combinatorial core:
    If `hullIdx : Fin h → Fin 10` is injective, `vecColor a = ⟨a / 2, _⟩`, and every color `i : Fin 5`
    appears as `vecColor (hullIdx r)` for some `r : Fin h`, then `hullColors` is surjective, `5 ≤ h`,
    and non-hull vectors have pairwise distinct colors. -/
theorem caseA_hull_five_colors_core
    {h : ℕ}
    (hullIdx : Fin h → Fin 10)
    (hinj : Function.Injective hullIdx)
    (h_surj : ∀ i : Fin 5, ∃ r : Fin h, (⟨(hullIdx r).val / 2, by omega⟩ : Fin 5) = i) :
    5 ≤ h ∧
    ∀ a b : Fin 10, (∀ r : Fin h, hullIdx r ≠ a) → (∀ r : Fin h, hullIdx r ≠ b) →
      (⟨a.val / 2, by omega⟩ : Fin 5) = ⟨b.val / 2, by omega⟩ → a = b := by
  use Fin.le_of_surjective @_ (by assumption), fun and A B R M =>by_contra (R ↑(h_surj ⟨A /2,by valid⟩).choose ∘by_contra (B ↑(h_surj ⟨and /2,by valid⟩).choose ∘by grind ) )
end Upper9Leaf_061

namespace Upper9Leaf_062

private lemma const_on_range
    {h : ℕ} (c : Fin h → Fin 5) (r₁ r₂ : Fin h)
    (S : Finset (Fin 5)) (hS2 : S.card = 2)
    (himg : (Finset.univ.filter (fun r : Fin h => r₁ ≤ r ∧ r ≤ r₂)).image c = S)
    (hno : ∀ k : ℕ, ∀ hk : k + 1 < h, r₁.val ≤ k → k + 1 ≤ r₂.val →
      ({c ⟨k, by omega⟩, c ⟨k + 1, hk⟩} : Finset (Fin 5)) ≠ S) :
    ∀ n : ℕ, ∀ hn : n < h, r₁.val ≤ n → n ≤ r₂.val → c ⟨n, hn⟩ = c r₁ := by
  intro n
  induction n with
  | zero =>
    intro hn hr1 _
    have hr1_eq : r₁ = ⟨0, hn⟩ := by ext; dsimp; omega
    rw [hr1_eq]
  | succ k ih =>
    intro hk hr1 hr2
    by_cases hstart : k + 1 = r₁.val
    · have heq : (⟨k + 1, hk⟩ : Fin h) = r₁ := by ext; dsimp; omega
      rw [heq]
    · have hk_ge : r₁.val ≤ k := by omega
      have hk_lt : k < h := by omega
      have hprev : c ⟨k, hk_lt⟩ = c r₁ := ih hk_lt hk_ge (by omega)
      by_contra hne
      apply hno k hk hk_ge hr2
      apply Finset.eq_of_subset_of_card_le
      · rw [← himg]
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact Finset.mem_image.mpr ⟨⟨k, hk_lt⟩,
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, Fin.mk_le_mk.mpr hk_ge, Fin.mk_le_mk.mpr (by omega)⟩, rfl⟩
        · exact Finset.mem_image.mpr ⟨⟨k + 1, hk⟩,
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, Fin.mk_le_mk.mpr (by omega), Fin.mk_le_mk.mpr hr2⟩, rfl⟩
      · have hne_pair : c ⟨k, hk_lt⟩ ≠ c ⟨k + 1, hk⟩ := by
          rw [hprev]; exact Ne.symm hne
        rw [hS2, Finset.card_pair hne_pair]

theorem two_color_interval_has_adjacent_transition
    {h : ℕ}
    (c : Fin h → Fin 5)
    (r₁ r₂ : Fin h) (hle : r₁ ≤ r₂)
    (S : Finset (Fin 5)) (hS2 : S.card = 2)
    (himg : (Finset.univ.filter (fun r : Fin h => r₁ ≤ r ∧ r ≤ r₂)).image c = S) :
    ∃ k : ℕ, ∃ hk : k + 1 < h, r₁.val ≤ k ∧ k + 1 ≤ r₂.val ∧
      ({c ⟨k, by omega⟩, c ⟨k + 1, hk⟩} : Finset (Fin 5)) = S := by
  by_contra hno
  push Not at hno
  have hconst := const_on_range c r₁ r₂ S hS2 himg hno
  have hsub : S ⊆ {c r₁} := by
    rw [← himg]
    intro x hx
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hx
    have hbounds := (Finset.mem_filter.mp hr).2
    rw [Finset.mem_singleton]
    exact hconst r.val r.isLt hbounds.1 hbounds.2
  have hle1 : S.card ≤ ({c r₁} : Finset (Fin 5)).card := Finset.card_le_card hsub
  simp only [Finset.card_singleton] at hle1
  omega
end Upper9Leaf_062

namespace Upper9Leaf_063

open scoped Classical

noncomputable section

/-- Prefix hull domination in `Ω`: if `r, w₁ ∈ Q₂` satisfy `r_y < w₁_y`, and `r` maximizes an
    outward normal `(nx, ny) ∈ Q₁` with positive support value over `w₁`, then `r · z > 1 → w₁ · z > 1`
    for every `z ∈ Ω`. -/
lemma q2_prefix_domination_in_omega
    (rx ry w1x w1y nx ny zx zy : ℝ)
    (hrx : rx < 0) (hry : 0 < ry)
    (hw1x : w1x < 0) (hw1y : ry < w1y)
    (hnx : 0 < nx) (hny : 0 < ny)
    (hnpos : 0 < nx * rx + ny * ry)
    (hnmax : nx * w1x + ny * w1y ≤ nx * rx + ny * ry)
    (hz : zx < 0 ∨ zy < 0)
    (hrz : 1 < rx * zx + ry * zy) :
    1 < w1x * zx + w1y * zy := by
  rcases@hz
  · have' := mul_pos hnx (neg_pos.2 (by valid))
    nlinarith[pow_three nx,pow_three zx,pow_three ry,mul_lt_mul_of_pos_left hw1y hnx, mul_lt_mul_of_neg_left hw1y (by assumption), mul_pos hnx hry, mul_pos (neg_pos.2 (by assumption)) hry]
  · nlinarith [mul_lt_mul_of_pos_left hw1y hny, mul_lt_mul_of_neg_left hw1y (by assumption), mul_neg_of_pos_of_neg hnx hrx, mul_neg_of_pos_of_neg hry (by assumption)]

end
end Upper9Leaf_063

namespace Upper9Leaf_064

def orient2d (a b c : ℝ × ℝ) : ℝ :=
  (b.1 - a.1) * (c.2 - a.2) - (b.2 - a.2) * (c.1 - a.1)

/-- Section 6 (`upper_9.tex` Lemma 6.4 `anchor-splitting`):
    Inside a CCW triangle `(w, u, v)` (`orient2d w u v > 0`), if `y1, y2 ∈ int △(w, u, v)`,
    `y2 ∉ △(u, v, y1)`, and `orient2d w y1 y2 ≠ 0`, then either `y2 ∈ int △(w, u, y1)` or
    `y2 ∈ int △(w, y1, v)`. -/
theorem anchor_splitting_orient
    (w u v y1 y2 : ℝ × ℝ)
    (hwuv : 0 < orient2d w u v)
    (hy1_uv : 0 < orient2d u v y1) (hy1_vw : 0 < orient2d v w y1) (hy1_wu : 0 < orient2d w u y1)
    (hy2_uv : 0 < orient2d u v y2) (hy2_vw : 0 < orient2d v w y2) (hy2_wu : 0 < orient2d w u y2)
    (hnot_cap : ¬ (0 ≤ orient2d u v y2 ∧ 0 ≤ orient2d v y1 y2 ∧ 0 ≤ orient2d y1 u y2))
    (hne : orient2d w y1 y2 ≠ 0) :
    (0 < orient2d w u y2 ∧ 0 < orient2d u y1 y2 ∧ 0 < orient2d y1 w y2) ∨
    (0 < orient2d w y1 y2 ∧ 0 < orient2d y1 v y2 ∧ 0 < orient2d v w y2) := by
  simp_all[orient2d,le_of_lt]
  exact (lt_or_gt_of_ne (by bound)).imp (⟨not_le.1 fun and=>by nlinarith[hnot_cap (by nlinarith),.],by nlinarith⟩) (⟨., not_le.1 fun and=>by nlinarith[hnot_cap (by nlinarith)]⟩)
end Upper9Leaf_064

namespace Upper9Leaf_065

def orient2d (a b c : ℝ × ℝ) : ℝ :=
  (b.1 - a.1) * (c.2 - a.2) - (b.2 - a.2) * (c.1 - a.1)

/-- Section 5 (`upper_9.tex` Proposition 5.1 `interior-anchor` & Lemma 6.2 `universal-crossing`):
    If `(p_prev, p, p_next)` is a CCW corner of `conv B` (`orient2d p_prev p p_next > 0`),
    `a_p, c_p` lie in `H^+(p_prev, p) ∩ H^+(p, p_next)` (`a_p, c_p ∈ conv B \ {p}`),
    `v` sees `p` across `a_p c_p` (`orient2d p a_p c_p > 0`, `orient2d p a_p v > 0`,
    `orient2d p c_p v < 0`), then `v ∈ H^+(p_prev, p) ∩ H^+(p, p_next)` (`0 < orient2d p_prev p v`
    and `0 < orient2d p p_next v`, i.e., neither incident hull edge faces `v`, so `p` is a back vertex). -/
theorem crossing_anchor_implies_back_vertex
    (p_prev p p_next ap cp v : ℝ × ℝ)
    (hcorner : 0 < orient2d p_prev p p_next)
    (hap1 : 0 ≤ orient2d p_prev p ap) (hap2 : 0 ≤ orient2d p p_next ap)
    (hcp1 : 0 ≤ orient2d p_prev p cp) (hcp2 : 0 ≤ orient2d p p_next cp)
    (hpac : 0 < orient2d p ap cp)
    (hva : 0 < orient2d p ap v)
    (hvc : orient2d p cp v < 0) :
    0 < orient2d p_prev p v ∧ 0 < orient2d p p_next v := by
  push_cast[orient2d,lt_iff_le_and_ne] at *
  have:0<(ap.1-p.1) * (cp.2-p.snd)-(ap.2-p.2) * (cp.1-p.1) :=Ne.lt_of_le (by bound) (by bound)
  have' :=hcorner.1.lt_of_ne hcorner.2
  repeat' constructor
  · cases em ((ap.1-p.1) *(v.1-p.fst)-(ap.2-p.2) *(v.2-p.snd) > 0) with nlinarith
  · cases hap1.eq_or_lt with nlinarith[hva.1.lt_of_ne hva.2,hvc.1.lt_of_ne hvc.2]
  · cases em ((ap.1-p.1) *(v.1-p.fst)-(ap.2-p.2) *(v.2-p.snd) > 0) with nlinarith[hva.2.lt_of_le hva.1,hvc.2.lt_of_le hvc.1]
  · use (by cases hcp2.eq_or_lt with nlinarith[hva.2.lt_of_le hva.1,hvc.2.lt_of_le hvc.1])
end Upper9Leaf_065

namespace Upper9Leaf_066

def compressAdj : List (Fin 5) → List (Fin 5)
  | [] => []
  | [c] => [c]
  | c₁ :: c₂ :: rest =>
      if c₁ = c₂ then compressAdj (c₂ :: rest)
      else c₁ :: compressAdj (c₂ :: rest)

def countTransitions : List (Fin 5) → ℕ
  | [] => 0
  | [_] => 0
  | c₁ :: c₂ :: rest =>
      (if c₁ = c₂ then 0 else 1) + countTransitions (c₂ :: rest)

theorem one_add_transitions_eq_compressAdj_length
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
end Upper9Leaf_066

namespace Upper9Leaf_067

noncomputable section

def InOmega (p : ℝ × ℝ) : Prop := p.1 < 0 ∨ p.2 < 0
def dot2 (u v : ℝ × ℝ) : ℝ := u.1 * v.1 + u.2 * v.2

open Classical in
def gamma (t : ℝ) : ℝ × ℝ :=
  if t ≤ 1 then (-t, 1 - t)
  else if t ≤ 2 then (t - 2, 1 - t)
  else (t - 2, t - 3)

open Classical in
def rayParam (z : ℝ × ℝ) : ℝ :=
  if 0 ≤ z.2 then -z.1 / (|z.1| + |z.2|)
  else 2 + z.1 / (|z.1| + |z.2|)

/-- `CaseASweep.posInterval_common_anchor` core:
    If `z₀ ∈ Ω` satisfies `1 < dot2 (p1 i) z₀ ∨ 1 < dot2 (p2 i) z₀` for every `i : Fin 5`
    (the all-`false` mask witness), then `t₀ := rayParam z₀ ∈ (0, 3)` satisfies
    `0 < max (dot2 (p1 i) (gamma t₀)) (dot2 (p2 i) (gamma t₀))` for all `i : Fin 5`. -/
theorem posInterval_common_anchor_core
    (p1 p2 : Fin 5 → ℝ × ℝ) (z₀ : ℝ × ℝ)
    (hz₀ : InOmega z₀)
    (hmask0 : ∀ i : Fin 5, 1 < dot2 (p1 i) z₀ ∨ 1 < dot2 (p2 i) z₀) :
    let t₀ := rayParam z₀
    0 < t₀ ∧ t₀ < 3 ∧
    ∀ i : Fin 5, 0 < max (dot2 (p1 i) (gamma t₀)) (dot2 (p2 i) (gamma t₀)) := by
  delta rayParam gamma
  delta dot2 InOmega at *
  split_ifs
  · norm_num[*, mul_div, add_pos_of_pos_of_nonneg _,hz₀.resolve_right, one_sub_div,←add_div,abs_of_neg,abs_of_nonneg,ne_of_lt,(div_le_one ↑ _).2 _|>.trans_lt]
    use lt_of_le_of_lt (by bound) ( show(3) > 1by norm_num), fun and=>if_pos (by bound:-z₀.1/(-z₀.1+z₀.snd) ≤ 1)▸or_iff_not_imp_left.2 fun and' =>?_
    cases‹∀_, _› and with simp_all[ (by bound:-z₀.1+z₀.2 > 0), mul_div, one_sub_div,←add_div,←neg_div,ne_of_gt, one_pos.trans]
  cases le_total 0 z₀.1
  · cases (by valid:).eq_or_lt
    · use (by valid▸by linear_combination),by valid▸by linear_combination, fun and=>if_neg (by norm_num[←‹0 =z₀.1›]:¬2+z₀.1/(abs z₀.1+abs z₀.2) ≤1)▸?_
      use (if_pos (by norm_num[←‹0 =z₀.1›]:2+z₀.1/(abs z₀.1+abs z₀.2) ≤2))▸lt_max_iff.2 (or_iff_not_imp_left.2 fun and' =>? _)
      use‹0 =z₀.1›▸(@zero_div ℝ _ _).symm▸by cases‹0 =z₀.1›.symm▸(‹∀_, _› and:) with nlinarith[@zero_div ℝ _ _▸‹0 =z₀.1›.symm▸and']
    norm_num[*, mul_div, add_pos, not_le.1 (by valid),abs_of_nonneg, if_neg,abs_of_neg,←add_div,←lt_sub_iff_add_lt',div_lt_one]
    use add_pos two_pos (by bound),by bound,fun R=>if_neg (by linarith[div_pos (by valid) (by linarith:z₀.1+-z₀.2 > 0)]:¬2+z₀.1/(z₀.1+-z₀.snd) ≤ 1)▸?_
    use (if_neg (div_pos (by valid) (by linarith:z₀.1+-z₀.2 > 0)).not_ge▸(‹∀_, _ ∨_› R).imp ?_ ? _)
    · use fun and=>by match (by linarith:z₀.1+-z₀.2 > 0) with | S=>linear_combination (one_pos.trans and/(z₀.1-z₀.snd)-div_self S.ne' * (p1 R).snd)
    · use fun and=>by match (by linarith:z₀.1+-z₀.2 > 0) with | S=>linear_combination (one_pos.trans and/(z₀.1-z₀.snd)-div_self S.ne' * (p2 R).snd)
  · norm_num[*, mul_div, add_pos_of_nonneg_of_pos _,abs, not_le.1 (by valid),←add_div, if_neg,←sub_sub,(add_left_mono (div_le_one_of_le₀ _ _)).trans_lt,le_of_lt]
    use sub_lt_iff_lt_add'.1 ((lt_div_iff₀ (by linarith)).2 (by linarith)),by linear_combination div_nonpos_of_nonpos_of_nonneg (by valid) (by linarith:-z₀.1-z₀.2≥0)
    use fun and=>(em _).elim (if_pos ·▸by nlinarith[div_mul_cancel₀ z₀.1 (by linarith:-z₀.1+-z₀.2≠0)]) (if_neg ·▸? _)
    use (if_pos (div_nonpos_of_nonpos_of_nonneg (by valid) (by linarith:-z₀.1+-z₀.2≥0))▸.imp ?_ ?_ (‹∀_, _› and:))
    · refine (by nlinarith[mul_div_cancel₀ z₀.fst (by linarith:-z₀.fst+-z₀.snd ≠0)▸mul_assoc _ _ ((p1 and).fst -(p1 and).snd),·])
    · exact fun and' =>by nlinarith[congr_arg (· * (p2 and).fst) (div_mul_cancel₀ z₀.fst (by linarith:-z₀.fst+-z₀.snd≠0)), mul_div_cancel₀ z₀.fst (by linarith:-z₀.fst+-z₀.snd≠0)]
end
end Upper9Leaf_067

namespace Upper9Leaf_068

/-- Section 3 (`upper_9.tex` Half-Plane Lemma, Claim 3.2 `coords`, lines 520--543):
    Under normalized coordinates `v = (0,0), q = (1,0), p = (0,1)`, if `a = (a1, a2)` and `c = (c1, c2)`
    satisfy `a1 > 0, a2 > 0, c1 < 0, c2 > 0`, `a1 + a2 > 1`, and `orient(a, p, c) = a1*(1 - c2) - c1*(1 - a2) > 0`,
    then `c1 + c2 < 1`, `-1 < (a2 - 1)/a1 < (c2 - 1)/c1`, `0 < c2/(1 - c1) < 1`, and
    `c2 * a1 + (1 - c1) * a2 > c2` (`a` lies strictly above line `qc`). -/
theorem halfplane_lemma_claim32_coords
    (a1 a2 c1 c2 : ℝ)
    (ha1 : 0 < a1) (ha2 : 0 < a2) (hc1 : c1 < 0) (hc2 : 0 < c2)
    (ha_sum : 1 < a1 + a2)
    (hapc : 0 < a1 * (1 - c2) - c1 * (1 - a2)) :
    c1 + c2 < 1 ∧
    -1 < (a2 - 1) / a1 ∧
    (a2 - 1) / a1 < (c2 - 1) / c1 ∧
    0 < c2 / (1 - c1) ∧ c2 / (1 - c1) < 1 ∧
    c2 < c2 * a1 + (1 - c1) * a2 := by
  refine ⟨by nlinarith,(lt_div_iff₀ ha1).2 (by linarith), (neg_div_neg_eq _ _).subst ((div_lt_div_iff₀ ha1 (neg_pos.2 hc1)).2 (by linarith)),div_pos hc2 (by linarith),.symm (↑? _),⟩
  use (by cases em (c2< -c1+1) with nlinarith), (div_lt_one (by linarith)).2 (by nlinarith)
end Upper9Leaf_068

namespace Upper9Leaf_069

def orient2d (a b c : ℝ × ℝ) : ℝ :=
  (b.1 - a.1) * (c.2 - a.2) - (b.2 - a.2) * (c.1 - a.1)

/-- Section 3 (`upper_9.tex` Half-Plane Lemma, Claim 3.4 `monotone-slope`, lines 570--583):
    With `p = (0, 1)`, `q = (1, 0)`, `z = (0, z2)` (`0 < z2 < 1`), `a = (a1, a2)` (`a1 > 0`),
    `c = (c1, c2)` (`c1 < 0`), `u = (u1, u2)` (`u1 > 0`), `x = (x1, x2)` (`x1 > 0`), and slope
    `s(y) = (y.2 - 1) / y.1`, assuming `-1 < (u2 - 1)/u1 < (a2 - 1)/a1 < (c2 - 1)/c1`:
    (1) if `(x2 - 1)/x1 < -1`, then `q, a ∈ H^+(p, x)` and `z, c ∈ H^-(p, x)`;
    (2) if `-1 < (x2 - 1)/x1 < (u2 - 1)/u1`, then `u, a ∈ H^+(p, x)` and `q, c ∈ H^-(p, x)`. -/
theorem halfplane_lemma_claim34_enclosure_signs
    (a1 a2 c1 c2 u1 u2 x1 x2 z2 : ℝ)
    (ha1 : 0 < a1) (hc1 : c1 < 0) (hu1 : 0 < u1) (hx1 : 0 < x1)
    (hz0 : 0 < z2) (hz1 : z2 < 1)
    (hsu_gt : -1 < (u2 - 1) / u1)
    (hsu_sa : (u2 - 1) / u1 < (a2 - 1) / a1)
    (hsa_sc : (a2 - 1) / a1 < (c2 - 1) / c1) :
    (((x2 - 1) / x1 < -1 →
      0 < orient2d (0, 1) (x1, x2) (1, 0) ∧
      0 < orient2d (0, 1) (x1, x2) (a1, a2) ∧
      orient2d (0, 1) (x1, x2) (0, z2) < 0 ∧
      orient2d (0, 1) (x1, x2) (c1, c2) < 0) ∧
    ((-1 < (x2 - 1) / x1 ∧ (x2 - 1) / x1 < (u2 - 1) / u1) →
      0 < orient2d (0, 1) (x1, x2) (u1, u2) ∧
      0 < orient2d (0, 1) (x1, x2) (a1, a2) ∧
      orient2d (0, 1) (x1, x2) (1, 0) < 0 ∧
      orient2d (0, 1) (x1, x2) (c1, c2) < 0)) := by
  norm_num[orient2d,div_lt_iff₀ hx1,lt_div_iff₀ hx1,div_lt_iff₀',lt_div_iff₀',div_lt_iff_of_neg', *]at*
  use fun and=>⟨and,by nlinarith[mul_lt_mul_of_pos_left ((lt_div_iff₀ hu1).2 (by linarith):(u2-1)/_>-1) ha1],by nlinarith,?_⟩,fun A B=>⟨? _,? _,A,?_⟩
  · nlinarith[(lt_div_iff_of_neg hc1).1.comp ( (lt_div_iff₀ hu1).2 (by linarith:-1*u1< _)).trans ↑(lt_of_mul_lt_mul_left.comp hsu_sa.trans hsa_sc ha1.le)]
  · rwa[mul_comm x1,←lt_div_iff₀ hu1,←div_mul_eq_mul_div]
  · nlinarith
  · linear_combination x1*(lt_div_iff_of_neg hc1).1 (lt_of_mul_lt_mul_left (hsu_sa.trans hsa_sc) ha1.le)+mul_lt_mul_of_neg_left B hc1
end Upper9Leaf_069

namespace Upper9Leaf_070

/-- Section 3 (`upper_9.tex` Half-Plane Lemma, Claim 3.3 `witness-pos`, lines 545--565):
    Under normalized coordinates `v = (0,0), q = (1,0), p = (0,1)` with `a1 > 0, a2 > 0, c1 < 0, c2 > 0`
    and `0 < z2 < 1`:
    (1) `orient(v, a, q) = -a2 < 0` and `orient(v, a, c) = a1 * c2 - a2 * c1 > 0`;
    (2) if `a1 * x2 - a2 * x1 < 0` (`orient(v, a, x) < 0`) and `x1 < 0`, then `x2 < 0`,
        `y2 = (a1 * x2 - a2 * x1) / (a1 - x1) < 0`, `c2 * x1 - c1 * x2 < 0` (`orient(c, v, x) < 0`),
        `-c1 * y2 < 0` (`orient(c, v, y) < 0`), and `0 < -c1 * z2` (`orient(c, v, z) > 0`). -/
theorem halfplane_lemma_claim33_witness_pos
    (a1 a2 c1 c2 z2 x1 x2 : ℝ)
    (ha1 : 0 < a1) (ha2 : 0 < a2) (hc1 : c1 < 0) (hc2 : 0 < c2)
    (hz0 : 0 < z2) (_hz1 : z2 < 1)
    (hoax : a1 * x2 - a2 * x1 < 0)
    (hx1 : x1 < 0) :
    -a2 < 0 ∧
    0 < a1 * c2 - a2 * c1 ∧
    x2 < 0 ∧
    (a1 * x2 - a2 * x1) / (a1 - x1) < 0 ∧
    c2 * x1 - c1 * x2 < 0 ∧
    -c1 * ((a1 * x2 - a2 * x1) / (a1 - x1)) < 0 ∧
    0 < -c1 * z2 := by
  simp_all[hx1.trans ha1, (by nlinarith:x2<0),div_neg_iff,(mul_neg_of_pos_of_neg _ _).trans, mul_pos_iff]
  exact (mul_neg_of_neg_of_pos hc1 ↑hz0)
end Upper9Leaf_070

namespace Upper9Leaf_071

def orient2d (a b c : ℝ × ℝ) : ℝ :=
  (b.1 - a.1) * (c.2 - a.2) - (b.2 - a.2) * (c.1 - a.1)

/-- Section 1.1 (`upper_9.tex` Eq. `U-halfplanes`, lines 214--221):
    For counterclockwise `a, b, c` (`0 < orient2d a b c`) and any point
    `x = a + α (a - b) + β (a - c)` in the open opposite cone `U(a; b, c)` (`α, β > 0`),
    `orient2d c a x < 0`, `orient2d a b x < 0`, `orient2d c b x < 0` (`U(a; b, c) ⊆ H^-(c, b)`),
    and `a` lies strictly inside `△(x, b, c)` (`0 < orient2d x b a`, `0 < orient2d b c a`, `0 < orient2d c x a`). -/
theorem cone_opposite_halfplanes_and_interior
    (a b c : ℝ × ℝ) (α β : ℝ)
    (habc : 0 < orient2d a b c)
    (hα : 0 < α) (hβ : 0 < β) :
    let x : ℝ × ℝ := (a.1 + α * (a.1 - b.1) + β * (a.1 - c.1),
                       a.2 + α * (a.2 - b.2) + β * (a.2 - c.2))
    orient2d c a x < 0 ∧
    orient2d a b x < 0 ∧
    orient2d c b x < 0 ∧
    0 < orient2d x b a ∧
    0 < orient2d b c a ∧
    0 < orient2d c x a := by
  simp_rw [orient2d] at habc⊢
  repeat use (by nlinarith[mul_pos habc hα, mul_pos habc hβ])
end Upper9Leaf_071

namespace Upper9Leaf_072

/-- Section 8.3 (`upper_9.tex` Six non-certified vertices `|D| = 6 => |M| <= 3`, lines 855--880):
    On `D = Fin 6` (with `p0 = 0` having `D`-anchors `{5, 1}` and `p1 = 1` having `D`-anchors `{0, 2}`),
    verify all four exit-edge cases `e ∈ {(2,3), (3,4), (1,2), (0,1)}` and the `H ≠ ∅` `endpoint-back`
    condition (`Q ∩ {l, r} = ∅` whenever `y ∈ {l, r} \ {0, 1}` is incident to `e` with `lr ≠ e` and
    `y` cannot be selected by any source): in every branch a compatible 2-element pair `Q` exists
    whose `D`-anchors avoid `Q` and satisfy `Q ∩ {l, r} = ∅`. -/
def compat2 (q1 q2 : Fin 6) (anc1 anc2 : Finset (Fin 6)) : Bool :=
  (q1 != q2) && decide (q1 ∉ anc2) && decide (q2 ∉ anc1)

def validHexBranch : Bool :=
  let anc0 : Finset (Fin 6) := {5, 1}
  let anc1 : Finset (Fin 6) := {0, 2}
  -- Case u0 v0 = 23: O*_1 = {1, a0, 4} gaps: 0->{2}({1}), 1->{3}({4}), 2->{5,0}({1,4})
  let ok23_H0 :=
    compat2 0 2 anc0 {1} && compat2 0 3 anc0 {4} && compat2 5 0 {1, 4} {1, 4}
  -- When H ≠ ∅ on 23: (y=2, lr={1,2} => gap≠0) or (y=3, lr={3,4} => gap≠1)
  let ok23_H1 :=
    (({0, 3} : Finset (Fin 6)) ∩ {1, 2} == ∅) && (({5, 0} : Finset (Fin 6)) ∩ {1, 2} == ∅) &&
    (({0, 2} : Finset (Fin 6)) ∩ {3, 4} == ∅) && (({5, 0} : Finset (Fin 6)) ∩ {3, 4} == ∅)
  -- Case u0 v0 = 34: O*_1 = {2, a0, 5} gaps: 0->{3}({2}), 1->{4}({5}), 2->{0,1}({2,5})
  let ok34_H0 :=
    compat2 0 3 anc0 {2} && compat2 1 4 anc1 {5} && compat2 0 1 {2, 5} {2, 5}
  -- When H ≠ ∅ on 34: (y=3, lr={2,3} => gap≠0) or (y=4, lr={4,5} => gap≠1)
  let ok34_H1 :=
    (({1, 4} : Finset (Fin 6)) ∩ {2, 3} == ∅) && (({0, 1} : Finset (Fin 6)) ∩ {2, 3} == ∅) &&
    (({0, 3} : Finset (Fin 6)) ∩ {4, 5} == ∅) && (({0, 1} : Finset (Fin 6)) ∩ {4, 5} == ∅)
  -- Case u0 v0 = 12: O*_2 = {5, a0, 3} gives {0,1}({5}), {2}({3}), or {4}({5,3})
  let ok12_H0 :=
    compat2 0 1 {5} {5} && compat2 0 2 anc0 {3} && compat2 0 4 anc0 {5, 3}
  -- When H ≠ ∅ on 12: y ∈ {1,2}\{0,1} = {2}, lr = {2,3}, 2 forbidden => Q ∈ {{0,1}, {0,4}}
  let ok12_H1 :=
    (({0, 1} : Finset (Fin 6)) ∩ {2, 3} == ∅) && (({0, 4} : Finset (Fin 6)) ∩ {2, 3} == ∅)
  -- Case u0 v0 = 01: O*_2 = {4, a0, 2} gives {5,0}({4}), {3}({2,4}), or {1}({2});
  -- O*_3 = {5, a0, 3} gives {1,2}({3}), {4}({3,5}), or {0}({5}); fallback {1}({2}) + {0}({5})
  let ok01_H0 :=
    compat2 5 0 {4} {4} && compat2 0 3 anc0 {2, 4} &&
    compat2 1 2 {3} {3} && compat2 1 4 anc1 {3, 5} &&
    compat2 1 0 {2} {5}
  let ok01_H1 := (({0, 1} : Finset (Fin 6)) \ {0, 1} == ∅)
  ok23_H0 && ok23_H1 && ok34_H0 && ok34_H1 && ok12_H0 && ok12_H1 && ok01_H0 && ok01_H1

theorem hexagon_d6_case_elimination : validHexBranch = true := by
  decide +kernel
end Upper9Leaf_072

namespace Upper9Leaf_073

/-- Section 8.4 (`upper_9.tex` Pentagon disjoint exit edges `01` and `23` on `D = Fin 5`, lines 920--926):
    For every choice `s0 ∈ {0, 1}` of `O*(y0) = {4, y0, 2}`, `s1 ∈ {2, 3}` of `O*(y1) = {1, y1, 4}`,
    and `g ∈ {0, 1, 3}` representing `O*_{01} = {y0, y1, 4}` selecting `{0}`, `{1, 2}`, or `{3}`,
    there exists a compatible 2-element subset `Q ⊆ {0, 1, 2, 3}` whose `D`-anchors avoid `Q`;
    moreover, when `0` cannot be selected (`s0 = 1 ∧ g ≠ 0`, corresponding to `lr = {4, 0}` with `0`
    excluded by `endpoint-back`), `Q` is disjoint from `{4, 0}`. -/
def compatPent (q1 q2 : Fin 5) (anc1 anc2 : Finset (Fin 5)) : Bool :=
  (q1 != q2) && decide (q1 ∉ anc2) && decide (q2 ∉ anc1)

def checkPentDisjoint : Bool :=
  let s0Choices : List (Fin 5 × Finset (Fin 5)) := [(0, {4}), (1, {2})]
  let s1Choices : List (Fin 5 × Finset (Fin 5)) := [(2, {1}), (3, {4})]
  -- gChoices: (qA, qB_opt, anc) where qB_opt = some 2 for the 2-element gap {1, 2} (D-anchors ∅)
  let gChoices : List (Fin 5 × Option (Fin 5) × Finset (Fin 5)) :=
    [(0, none, {4}), (1, some 2, ∅), (3, none, {4})]
  s0Choices.all fun (s0, a0) =>
    s1Choices.all fun (s1, a1) =>
      gChoices.all fun (g, gOpt, ag) =>
        let cands : List (Fin 5 × Fin 5 × Bool) :=
          [(s0, s1, compatPent s0 s1 a0 a1)] ++
          match gOpt with
          | some g2 => [(g, g2, compatPent g g2 ag ag)]
          | none => [(g, s0, compatPent g s0 ag a0), (g, s1, compatPent g s1 ag a1)]
        let hasValid := cands.any fun (x, y, ok) =>
          ok && ({x, y} : Finset (Fin 5)) ⊆ {0, 1, 2, 3}
        let hasValidNo04 :=
          if (s0 != 0) && (g != 0) then
            cands.any fun (x, y, ok) =>
              ok && ({x, y} : Finset (Fin 5)) ⊆ {0, 1, 2, 3} &&
              (({x, y} : Finset (Fin 5)) ∩ {4, 0} == ∅)
          else true
        hasValid && hasValidNo04

theorem pentagon_disjoint_exits_elimination : checkPentDisjoint = true := by
  decide +kernel
end Upper9Leaf_073

namespace Upper9Leaf_074

def orient2d (a b c : ℝ × ℝ) : ℝ :=
  (b.1 - a.1) * (c.2 - a.2) - (b.2 - a.2) * (c.1 - a.1)

/-- Section 8.4 (`upper_9.tex` Proposition 8.2 final step, lines 917--918):
    Suppose `y0, r` are in counterclockwise order around `v0` (`0 < orient2d v0 y0 r`), and both
    `v0 l` and `v0 h` cross the open segment `y0 r` (meaning `l` and `h` lie in the open convex wedge
    `v0 + cone_{>0}(y0 - v0, r - v0)` strictly across the line `y0 r` from `v0`). Then every convex
    combination `z` of `{y0, l, h, r}` outside the segment `y0 r` (`0 < wl + wh`) also lies in that
    open region, so `v0 z` strictly crosses the open segment `y0 r`. -/
theorem prop82_crossing_convex_hull
    (v0 y0 l h r : ℝ × ℝ)
    (wy wl wh wr : ℝ)
    (hy0r : 0 < orient2d v0 y0 r)
    (hl1 : 0 < orient2d v0 y0 l) (hl2 : 0 < orient2d v0 l r) (hl3 : orient2d y0 r l < 0)
    (hh1 : 0 < orient2d v0 y0 h) (hh2 : 0 < orient2d v0 h r) (hh3 : orient2d y0 r h < 0)
    (hwy : 0 ≤ wy) (hwl : 0 ≤ wl) (hwh : 0 ≤ wh) (hwr : 0 ≤ wr)
    (hsum : wy + wl + wh + wr = 1)
    (hpos : 0 < wl + wh) :
    let z : ℝ × ℝ :=
      (wy * y0.1 + wl * l.1 + wh * h.1 + wr * r.1,
       wy * y0.2 + wl * l.2 + wh * h.2 + wr * r.2)
    0 < orient2d v0 y0 z ∧
    0 < orient2d v0 z r ∧
    orient2d y0 r z < 0 := by
  delta orient2d at*
  induction hsum▸add_sub_cancel_left _ _ with repeat use (by cases hA :hwl.eq_or_lt with nlinarith)
end Upper9Leaf_074

namespace Upper9Leaf_075

/-- Section 9.1 (`upper_9.tex` Lemma `v-slope-perturb`, lines 987--997):
    If `|ym - max(a*xm + b, c*xm + d)| ≥ δ > 0` with `1 ≤ X0` and `|xm| ≤ X0 - 1`, then perturbing
    slopes within `|a' - a| < δ / (2 * X0)` and `|c' - c| < δ / (2 * X0)` changes
    `max(a*xm + b, c*xm + d)` by strictly less than `δ / 2`, preserving strict epigraph/hypograph
    membership on both sides. -/
theorem v_slope_perturb_preserve
    (a b c d a' c' xm ym δ X0 : ℝ)
    (hδ : 0 < δ) (hX0 : 1 ≤ X0)
    (hxm : |xm| ≤ X0 - 1)
    (hmarg : δ ≤ |ym - max (a * xm + b) (c * xm + d)|)
    (ha : |a' - a| < δ / (2 * X0))
    (hc : |c' - c| < δ / (2 * X0)) :
    |max (a' * xm + b) (c' * xm + d) - max (a * xm + b) (c * xm + d)| < δ / 2 ∧
    (max (a * xm + b) (c * xm + d) < ym ↔ max (a' * xm + b) (c' * xm + d) < ym) ∧
    (ym < max (a * xm + b) (c * xm + d) ↔ ym < max (a' * xm + b) (c' * xm + d)) := by
  have:abs ((a'*xm+b)⊔(c'*xm+d)-(a*xm+b)⊔(c*xm+d ) )<δ/2:=(abs_max_sub_max_le_max _ _ _ _).trans_lt ?_
  · exact ⟨this,by repeat use (by repeat use (by cases le_abs.1 hmarg with linarith only[max_lt_iff.1 this,.,by valid]))⟩
  norm_num[abs_mul,←sub_mul,(mul_lt_mul'' ha (hxm.trans_lt ↑ _) (@norm_nonneg ℝ _ _) (@norm_nonneg ℝ _ _)).trans_eq (div_mul _ _ _), (mul_lt_mul'' hc (hxm.trans_lt ↑ _) (@norm_nonneg ℝ _ _) (@norm_nonneg ℝ _ _)).trans_eq]
  repeat use((mul_le_mul_of_nonneg_left (by·linear_combination hxm)) (@norm_nonneg ℝ _ _)).trans_lt.comp (lt_div_iff₀ (one_pos.trans_le hX0)).mp (by(rwa [div_div]))
end Upper9Leaf_075

namespace Upper9Leaf_076

/-- Section 9.1 (`upper_9.tex` Lemma `v-dual-equiv`(i), lines 1005--1015):
    Under the projective duality `(s, t) = (-x, y)`, `(x, y)` lies strictly above
    `f(x) = max(a*x + b, c*x + d)` iff both dual points `(a, b)` and `(c, d)` lie strictly below
    the line `v = s*u + t`, and `(x, y)` lies strictly below `f(x)` iff at least one of `(a, b), (c, d)`
    lies strictly above `v = s*u + t`. -/
theorem v_dual_equivalence_pointwise
    (a b c d x y : ℝ) :
    let s := -x
    let t := y
    (max (a * x + b) (c * x + d) < y ↔ (b < s * a + t ∧ d < s * c + t)) ∧
    (y < max (a * x + b) (c * x + d) ↔ (s * a + t < b ∨ s * c + t < d)) := by
  push_cast only[neg_mul,mul_comm x, max_lt_iff,lt_neg_add_iff_add_lt, and_self, true,neg_lt_iff_pos_add']
  simp_rw [lt_max_iff,neg_add_lt_iff_lt_add, and_self]
end Upper9Leaf_076

namespace Upper9Leaf_077

/-- Section 9.2 (`upper_9.tex` Lemma `v-hull-structure`(ii) & (iv), lines 1027--1041):
    (1) If `u1 < u2 < u3` and `s2` certifies `(u2, v2)` strictly above `(u1, v1)` and `(u3, v3)`,
        then `(v3 - v2)/(u3 - u2) < s2 < (v2 - v1)/(u2 - u1)`.
    (2) Consequently, whenever `(v3 - v2)/(u3 - u2) < (v2 - v1)/(u2 - u1)` and both `(u1, v1)` and
        `(u3, v3)` lie strictly above `v = s*u + t`, the middle upper-hull vertex `(u2, v2)` also
        lies strictly above `v = s*u + t` (contiguity of `H(W) ∩ U(s, t)`). -/
theorem v_hull_slopes_and_contiguity
    (u1 v1 u2 v2 u3 v3 s2 s t : ℝ)
    (hu12 : u1 < u2) (hu23 : u2 < u3)
    (hsup1 : v1 - s2 * u1 < v2 - s2 * u2)
    (hsup3 : v3 - s2 * u3 < v2 - s2 * u2) :
    (v3 - v2) / (u3 - u2) < s2 ∧
    s2 < (v2 - v1) / (u2 - u1) ∧
    (0 < v1 - s * u1 - t → 0 < v3 - s * u3 - t → 0 < v2 - s * u2 - t) := by
  use(div_lt_iff₀ (by linarith)).mpr (by linarith), (lt_div_iff₀ (by((((linarith)))))).mpr (by ·linarith),fun A B=>by nlinarith
end Upper9Leaf_077

namespace Upper9Leaf_078

/-- Section 9.3 (`upper_9.tex` Eq. `eq-cons-v`, lines 1065--1070):
    Exact cell-counting conservation law for 5 generic V-functions realizing all 32 bitmasks:
    with `inv_cnt = T3bar - T1`, `Kcross = 3*(10 - T3bar) + T1 + 2*inv_cnt`, `C = Kcross + 6`,
    `C = 32 + d1 + d2 + d3 + d4`, and `d4 = n - 5`, we have `n + T3bar + T1 + d1 + d2 + d3 = 9`. -/
theorem v_sweep_conservation_law
    (n T3bar T1 inv_cnt Kcross C d1 d2 d3 d4 : ℤ)
    (hinv : inv_cnt = T3bar - T1)
    (hK : Kcross = 3 * (10 - T3bar) + T1 + 2 * inv_cnt)
    (hC1 : C = Kcross + 6)
    (hC2 : C = 32 + d1 + d2 + d3 + d4)
    (hd4 : d4 = n - 5) :
    n + T3bar + T1 + d1 + d2 + d3 = 9 := by
  grind
end Upper9Leaf_078

namespace Upper9Leaf_079

def permInvCount5 (σ : Equiv.Perm (Fin 5)) : ℕ :=
  ((Finset.univ.product Finset.univ).filter
    (fun p : Fin 5 × Fin 5 => p.1 < p.2 ∧ σ p.2 < σ p.1)).card

/-- Section 9.3 (`upper_9.tex` Proposition `v-count` opening step, lines 1078--1080):
    For any permutation `σ` of `Fin 5`:
    (1) if `σ.symm 0 = 4` (i.e. color `5` has smallest right slope, written `σ(1) = 5` in 1-based text
        where `c_{σ(1)} < ... < c_{σ(5)}`), then `permInvCount5 σ.symm ≥ 4` (and equally if `σ 0 = 4`,
        `permInvCount5 σ ≥ 4`);
    (2) if `{σ 0, σ 1} = ({3, 4} : Finset (Fin 5))`, then `permInvCount5 σ ≥ 6`. -/
theorem v_sigma1_ne_5_and_top2_ne_45 :
    (∀ σ : Equiv.Perm (Fin 5), σ 0 = 4 → 4 ≤ permInvCount5 σ) ∧
    (∀ σ : Equiv.Perm (Fin 5), σ.symm 0 = 4 → 4 ≤ permInvCount5 σ) ∧
    (∀ σ : Equiv.Perm (Fin 5), ({σ 0, σ 1} : Finset (Fin 5)) = {3, 4} → 6 ≤ permInvCount5 σ) := by
  norm_num [permInvCount5, Finset.ext_iff]
  use fun a s=>not_lt.1 fun and=>? _,fun a s=>not_lt.1 fun and=>? _,fun a s=>not_lt.1 fun and=>?_
  · cases Finset.ext_iff.1 (by decide:.filter ( fun and=>and 0=4∧ Finset.card {(a, b):_ ×_|a<b∧and b< and a}<4) ⊤={}) a with aesop (config := { warnOnNonterminal := false })
  · cases Finset.ext_iff.1 (by decide:.filter (fun p=>p.symm 0=4∧ Finset.card {(x, y):_ ×_|x<y∧p y<p x}<4) ⊤={}) a with aesop (config := { warnOnNonterminal := false })
  · cases Finset.ext_iff.1 (by decide:.filter (fun p=> Finset.card {(x, y):_ ×_|x<y∧p y<p x}<6) {p|∀a,a=p 0 ∨a=p (1) ↔a=3 ∨a=4}={}) a with aesop (config := { warnOnNonterminal := false })
end Upper9Leaf_079

namespace Upper9Leaf_080
/-- Section 9.3 (`upper_9.tex` Proposition `v-count`, Left/Right certificate bound, lines 1081--1087):
    Pure Lean 4 core (`0` external imports, `rfl` kernel reduction) verification across all `120`
    permutations `σ = [s0, s1, s2, s3, s4]` of `0..4` with `s0 ≠ 4` and `{s0, s1} ≠ {3, 4}`, and all
    `2^10 = 1024` 3-root graphs `E3` on `i < j` compatible with `σ`'s inversions, that
    `2 ≤ T3bar + T1 + dL + dR`. -/
def pairBitIdx (i j : Nat) : Nat :=
  let a := if Nat.ble i j then i else j
  let b := if Nat.ble i j then j else i
  if Nat.beq a 0 && Nat.beq b 1 then 0
  else if Nat.beq a 0 && Nat.beq b 2 then 1
  else if Nat.beq a 0 && Nat.beq b 3 then 2
  else if Nat.beq a 0 && Nat.beq b 4 then 3
  else if Nat.beq a 1 && Nat.beq b 2 then 4
  else if Nat.beq a 1 && Nat.beq b 3 then 5
  else if Nat.beq a 1 && Nat.beq b 4 then 6
  else if Nat.beq a 2 && Nat.beq b 3 then 7
  else if Nat.beq a 2 && Nat.beq b 4 then 8
  else 9

def perms5 : List (Nat × Nat × Nat × Nat × Nat) :=
  let u := [0, 1, 2, 3, 4]
  u.flatMap fun s0 =>
    (u.filter (fun x => !(Nat.beq x s0))).flatMap fun s1 =>
      (u.filter (fun x => !(Nat.beq x s0) && !(Nat.beq x s1))).flatMap fun s2 =>
        (u.filter (fun x => !(Nat.beq x s0) && !(Nat.beq x s1) && !(Nat.beq x s2))).flatMap fun s3 =>
          (u.filter (fun x => !(Nat.beq x s0) && !(Nat.beq x s1) && !(Nat.beq x s2) && !(Nat.beq x s3))).map fun s4 =>
            (s0, s1, s2, s3, s4)

def checkLeftRightCertBound : Bool :=
  let pairs : List (Nat × Nat) :=
    [(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(2,3),(2,4),(3,4)]
  let ps := perms5
  (List.range 32).all fun hi =>
    (List.range 32).all fun lo =>
      let gMask := (hi <<< 5) ||| lo
      let E3 (i j : Nat) : Bool := Nat.beq ((gMask >>> pairBitIdx i j) &&& 1) 1
      ps.all fun (s0, s1, s2, s3, s4) =>
        if Nat.beq s0 4 || ((Nat.beq s0 3 && Nat.beq s1 4) || (Nat.beq s0 4 && Nat.beq s1 3)) then true
        else
          let invAt (x : Nat) : Nat :=
            if Nat.beq x s0 then 0
            else if Nat.beq x s1 then 1
            else if Nat.beq x s2 then 2
            else if Nat.beq x s3 then 3
            else 4
          let invOk := pairs.all fun (i, j) =>
            if Nat.blt (invAt j) (invAt i) then !(E3 i j) else true
          if !invOk then true
          else
            let T3bar := (pairs.filter fun (i, j) => !(E3 i j)).length
            let T1 := (pairs.filter fun (i, j) => Nat.blt (invAt i) (invAt j) && !(E3 i j)).length
            let dL := if E3 0 4 && E3 1 4 && E3 2 4 then 1 else 0
            let dR := if E3 s0 s2 && E3 s0 s3 && E3 s0 s4 then 1 else 0
            Nat.ble 2 (T3bar + T1 + dL + dR)

theorem v_left_right_cert_bound : checkLeftRightCertBound = true := by
  decide +kernel
end Upper9Leaf_080

namespace Upper9Leaf_081

/-- Section 9.3 (`upper_9.tex` Proposition `v-count` item 4, `n = 7, T3bar = 0`, lines 1093--1094):
    In the alternating 10-element color sequence `κ_hat = [0, 1, 2, 3, 4, 0, 1, 2, 3, 4]`, removing
    any 3 interior positions `1 ≤ i1 < i2 < i3 ≤ 8` leaves a 7-element hull sequence `κ` (`h = 7`):
    whenever adjacent colors in `κ` are distinct (`n = 7`), the union of adjacent hull 2-sets `A2(κ)`
    and interior-slab 2-sets `B2(r)` (pairing each removed color `κ_hat[ir]` with the two hull colors
    immediately to its left and right in `κ_hat \ {i1, i2, i3}`) never covers all 5 non-`C_5` diagonals
    `{{0, 2}, {0, 3}, {1, 3}, {1, 4}, {2, 4}}`. -/
def checkN7T3bar0Diagonals : Bool :=
  let khat : Array (Fin 5) := #[0, 1, 2, 3, 4, 0, 1, 2, 3, 4]
  let diags : List (Finset (Fin 5)) := [{0, 2}, {0, 3}, {1, 3}, {1, 4}, {2, 4}]
  let interiorPos : List Nat := [1, 2, 3, 4, 5, 6, 7, 8]
  interiorPos.all fun i1 =>
    interiorPos.all fun i2 =>
      interiorPos.all fun i3 =>
        if !(i1 < i2 && i2 < i3) then true
        else
          let rem : List Nat := [i1, i2, i3]
          let hullIdx : List Nat := (List.range 10).filter (fun p => !(rem.contains p))
          let adjDistinct := (hullIdx.zip hullIdx.tail).all fun (a, b) => khat[a]! != khat[b]!
          if !adjDistinct then true
          else
            let a2 : List (Finset (Fin 5)) :=
              (hullIdx.zip hullIdx.tail).map fun (a, b) => ({khat[a]!, khat[b]!} : Finset (Fin 5))
            let b2 : List (Finset (Fin 5)) :=
              rem.flatMap fun r =>
                let leftH := (hullIdx.filter (fun p => p < r)).getLast!
                let rightH := (hullIdx.filter (fun p => r < p)).head!
                ([{khat[r]!, khat[leftH]!}, {khat[r]!, khat[rightH]!}] : List (Finset (Fin 5)))
            let realizedPairs := a2 ++ b2
            !(diags.all fun d => realizedPairs.contains d)

theorem v_n7_T3bar0_diagonals_lt_5 : checkN7T3bar0Diagonals = true := by
  decide +kernel
end Upper9Leaf_081

namespace Upper9Leaf_082
/-- Section 9.3 (`upper_9.tex` Proposition `v-count` `n = 5` and `n = 6` Island Rule & `(1, 4)` slab
    elimination, lines 1096--1101): pure Lean 4 core (`0` external imports, `decide +kernel`)
    verification across all `4^5 = 1024` slab placements for `n = 5` and all `9 * 5^4 = 5625`
    `(repeat-pair, slab)` configurations for `n = 6` (`i2 - i1 ≥ 2, (i1, i2) ≠ (0, 5)`) that
    some nonempty subset `T ⊆ Fin 5` (`1 ≤ T ≤ 31`) is NOT realized. -/
def bitSet (m c : Nat) : Bool := Nat.beq ((m >>> c) &&& 1) 1

def checkN5Elim : Bool :=
  let ivals : List (Nat × Nat) :=
    [(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3),(2,4),(3,3),(3,4),(4,4)]
  -- Test mask 21 = {0, 2, 4} (`{A, C, E}` in `upper_9.tex` line 1098) first for O(1) short-circuit!
  let masks : List Nat := 21 :: (List.range 31).map (fun x => x + 1)
  (List.range 32).all fun hi =>
    (List.range 32).all fun lo =>
      let code := (hi <<< 5) ||| lo
      let slab (c : Nat) : Nat := (code >>> (2 * c)) &&& 3
      let realizes (tMask : Nat) : Bool :=
        ivals.any fun (a, b) =>
          let baseOk := (List.range (b + 1 - a)).all fun d => bitSet tMask (a + d)
          if !baseOk then false
          else
            [0, 1, 2, 3, 4].all fun c =>
              if !(bitSet tMask c) then true
              else if Nat.ble a c && Nat.ble c b then true
              else
                let j := slab c
                Nat.ble a (j + 1) && Nat.ble j b
      !(masks.all realizes)

def checkN6Elim : Bool :=
  let words6 : List (Nat × Nat × Nat × Nat × Nat × Nat) :=
    [ (0, 1, 0, 2, 3, 4),
      (0, 1, 2, 0, 3, 4),
      (0, 1, 2, 3, 0, 4),
      (1, 0, 2, 0, 3, 4),
      (1, 0, 2, 3, 0, 4),
      (1, 0, 2, 3, 4, 0),
      (1, 2, 0, 3, 0, 4),
      (1, 2, 0, 3, 4, 0),
      (1, 2, 3, 0, 4, 0)
    ]
  let ivals6 : List (Nat × Nat) :=
    [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,2),(1,3),(1,4),(1,5),
     (2,2),(2,3),(2,4),(2,5),(3,3),(3,4),(3,5),(4,4),(4,5),(5,5)]
  -- Put `{A,B,D}=22`, `{A,C,D}=26`, `{X,D}=17`, `{B,D}=20`, `{A,D}=18`, `{X,B,D}=21`, `{X,A,D}=19` first!
  let masks : List Nat := [22, 26, 17, 20, 18, 21, 19] ++ (List.range 31).map (fun x => x + 1)
  words6.all fun (c0, c1, c2, c3, c4, c5) =>
    let kAt (idx : Nat) : Nat :=
      if Nat.beq idx 0 then c0
      else if Nat.beq idx 1 then c1
      else if Nat.beq idx 2 then c2
      else if Nat.beq idx 3 then c3
      else if Nat.beq idx 4 then c4
      else c5
    (List.range 25).all fun hi =>
      (List.range 25).all fun lo =>
        let code := hi * 25 + lo
        let slab4 (c : Nat) : Nat :=
          if Nat.beq c 1 then code % 5
          else if Nat.beq c 2 then (code / 5) % 5
          else if Nat.beq c 3 then (code / 25) % 5
          else (code / 125) % 5
        let realizes (tMask : Nat) : Bool :=
          ivals6.any fun (a, b) =>
            let indices := (List.range (b + 1 - a)).map (fun d => a + d)
            let baseOk := indices.all (fun idx => bitSet tMask (kAt idx))
            if !baseOk then false
            else
              [0, 1, 2, 3, 4].all fun c =>
                if !(bitSet tMask c) then true
                else if indices.any (fun idx => Nat.beq (kAt idx) c) then true
                else if Nat.beq c 0 then false -- color 0 has no interior copy!
                else
                  let j := slab4 c
                  Nat.ble a (j + 1) && Nat.ble j b
        !(masks.all realizes)

theorem v_n5_n6_island_rule_elimination : checkN5Elim = true ∧ checkN6Elim = true := by
  decide +kernel
end Upper9Leaf_082

namespace Upper9Leaf_083

/-- Section 9 (`upper_9.tex` Proof of Theorem `v-epigraph`(2), projective chart & nearest-point
    half-plane separation, lines 1107--1110):
    (1) Under `0 < V`, `max(a*U + b*V, c*U + d*V) < 1 ↔ max(a*(U/V) + b, c*(U/V) + d) < 1/V` and
        `1 < max(a*U + b*V, c*U + d*V) ↔ 1/V < max(a*(U/V) + b, c*(U/V) + d)`.
    (2) If `v = qstar - p0` is nonzero (`0 < v.1^2 + v.2^2`) and `0 ≤ v.1*(x.1 - qstar.1) + v.2*(x.2 - qstar.2)`,
        then the separating threshold `c0 = ((v.1*qstar.1 + v.2*qstar.2) + (v.1*p0.1 + v.2*p0.2)) / 2`
        satisfies `v.1*p0.1 + v.2*p0.2 < c0 ∧ c0 < v.1*x.1 + v.2*x.2`. -/
theorem thm_v_epigraph_part2_separation
    (a b c d U V : ℝ) (p0 qstar x : ℝ × ℝ)
    (hV : 0 < V)
    (hneq : 0 < (qstar.1 - p0.1) ^ 2 + (qstar.2 - p0.2) ^ 2)
    (hopt : 0 ≤ (qstar.1 - p0.1) * (x.1 - qstar.1) + (qstar.2 - p0.2) * (x.2 - qstar.2)) :
    (max (a * U + b * V) (c * U + d * V) < 1 ↔
      max (a * (U / V) + b) (c * (U / V) + d) < 1 / V) ∧
    (1 < max (a * U + b * V) (c * U + d * V) ↔
      1 / V < max (a * (U / V) + b) (c * (U / V) + d)) ∧
    (let v1 := qstar.1 - p0.1
     let v2 := qstar.2 - p0.2
     let c0 := ((v1 * qstar.1 + v2 * qstar.2) + (v1 * p0.1 + v2 * p0.2)) / 2
     v1 * p0.1 + v2 * p0.2 < c0 ∧ c0 < v1 * x.1 + v2 * x.2) := by
  norm_num only[div_add' _ _ _ hV.ne',div_lt_div_iff_of_pos_right, max_div_div_right, mul_div, and_self, (by linarith:(qstar.1-p0.fst)*p0.1+(qstar.2-p0.snd)*p0.2<((qstar.1-p0.1))) + 1]
  exact ⟨by rw [max_div_div_right (by gcongr),div_lt_div_iff_of_pos_right hV],by rw [max_div_div_right (by gcongr),div_lt_div_iff_of_pos_right hV],by repeat use by linarith⟩
end Upper9Leaf_083

namespace Upper9Leaf_084

open scoped Classical

noncomputable section

/-- Unconditional 8-mask bound along `Γ₅` in Case B (`k = 1`): if a sequence of `m + 1` bitvectors
    `w : Fin (m + 1) → (Fin 4 → Bool)` flips a single coordinate at each step and each coordinate `c`
    flips `fc c ≤ 2` times (`∑ c, fc c = m`), then `Set.range w` has cardinality at most `8`
    (regardless of whether any `fc c = 1`!). -/
lemma at_most_two_flips_per_coord_card_le_eight
    (m : ℕ) (w : Fin (m + 1) → (Fin 4 → Bool))
    (h_step : ∀ k : Fin m, ∃! c : Fin 4, w k.castSucc c ≠ w k.succ c)
    (h_le_two : ∀ c : Fin 4,
      (Finset.univ.filter (fun k : Fin m => w k.castSucc c ≠ w k.succ c)).card ≤ 2) :
    (Finset.univ.image w).card ≤ 8 := by
  choose R Msimpa using h_step
  have:= Finset.univ.sum_le_card_nsmul _ _ fun and x =>( Finset.card_filter _ _).ge.trans (h_le_two and)
  rw [← Finset.sum_comm] at this
  norm_num[ Fintype.sum_eq_single _ fun and α=>if_neg (α ∘(Msimpa _).2 _),(Msimpa _).1] at this
  norm_num[(Msimpa _).1, Fintype.sum_eq_single _ fun and(A) =>if_pos (by_contra (A ∘(Msimpa _).2 and)), Finset.sum_ite] at this
  obtain ⟨@c⟩ :=this.eq_or_lt
  · have:= Finset.univ.sum_le_sum fun and x =>( Finset.card_filter _ _).ge.trans (h_le_two and)
    replace : ∀ A B,w A B=w 0 B+∑ a ∈.range A,ite (B=(R ⟨ _,a.mod_lt (by decide)⟩)) (1) 0
    · use Fin.induction (by norm_num) fun and A B=>symm ((congr_arg _ (Finset.sum_range_succ _ _)).trans ((add_assoc _ _ _).symm.trans ( A B▸?_)))
      cases em (B=R and) with| inl a=>norm_num[a, (by_contra ((Msimpa _).1 ∘by cases(w _ _) with cases(w _ _) with decide):w and.castSucc (R and)+1 =w and.succ (R and)),Nat.mod_eq_of_lt]|_
      norm_num[not_imp_comm.mpr ((Msimpa _).2 _), (by assumption),Nat.mod_eq_of_lt]
    rw[Matrix.ext this]at Msimpa⊢
    norm_num[ Finset.sum] at Msimpa
    replace h_le_two : ∀y, Finset.card {M|y = R M}≤2
    · exact (.trans (funext₂ this▸by norm_num+decide[Nat.mod_eq_of_lt, Finset.sum])<|h_le_two ·)
    norm_num[←(Msimpa _).1]
    trans(( Finset.range 8).image fun and(a) =>w 0 a+∑M ∈.range and,ite (a=R ⟨_, M.mod_lt (by decide)⟩) (1) 0).card
    · use Finset.card_mono (Finset.image_subset_iff.2 fun and x => Finset.mem_image.2 (and.lastCases (?_) (⟨·,by norm_num⟩)))
      use(0),by decide,funext fun and=>congr_arg _ (.symm (.trans (by rw [ Fin.val_last, Finset.card_filter,Nat.cast_sum]) ?_))
      rcases↑(h_le_two (and ) ).eq_or_lt
      · norm_num+decide[by valid, Finset.sum_range _,Nat.mod_eq_of_lt]
      have:= Fintype.card_congr (.sigmaFiberEquiv R)▸ Fintype.card_sigma
      norm_num[comm,←(Msimpa _).1,(Finset.sum_lt_sum (fun R L=>h_le_two R) ⟨and, _⟩).ne.trans_eq ↑_|>.symm,‹_<2›, Fintype.card_subtype] at this
    · use Finset.card_image_le
  · exact Finset.card_image_le.trans (by rwa[ Finset.card_fin])

end
end Upper9Leaf_084

namespace Upper9Leaf_085

def det2 (u v : ℝ × ℝ) : ℝ := u.1 * v.2 - u.2 * v.1

/-- Section 10.2 (`upper_9.tex` Lemma `caseB-trichotomy`, lines 1182--1200):
    For `y = (xi, ui) ∈ Q3` (`xi < 0, ui < 0`), `pa = (Xa, Ya) ∈ Q4` (`0 < Xa, Ya < 0`),
    `pb = (Xb, Yb) ∈ Q2` (`Xb < 0, 0 < Yb`), and `A = Yb - Ya, B = Xa - Xb, C = Xa*Yb - Xb*Ya < 0`:
    (1) `0 < A ∧ 0 < B ∧ 0 < det2 (Xa - xi, Ya - ui) (-xi, -ui) ∧ 0 < det2 (-xi, -ui) (Xb - xi, Yb - ui)`;
    (2) `det2 (Xa - xi, Ya - ui) (Xb - xi, Yb - ui) = C - (A * xi + B * ui)`;
    (3) if `C < A * xi + B * ui` (`L_>`), then `Xb - xi < 0`, `0 < Yb - ui`, `0 < Xa - xi`, `Ya - ui < 0`,
        and `0 < det2 (Xb - xi, Yb - ui) (Xa - xi, Ya - ui)`. -/
theorem caseB_apex_trichotomy_coords
    (xi ui Xa Ya Xb Yb : ℝ)
    (hxi : xi < 0) (hui : ui < 0)
    (hXa : 0 < Xa) (hYa : Ya < 0)
    (hXb : Xb < 0) (hYb : 0 < Yb)
    (hC : Xa * Yb - Xb * Ya < 0) :
    let A := Yb - Ya
    let B := Xa - Xb
    let C := Xa * Yb - Xb * Ya
    0 < A ∧ 0 < B ∧
    0 < det2 (Xa - xi, Ya - ui) (-xi, -ui) ∧
    0 < det2 (-xi, -ui) (Xb - xi, Yb - ui) ∧
    det2 (Xa - xi, Ya - ui) (Xb - xi, Yb - ui) = C - (A * xi + B * ui) ∧
    (C < A * xi + B * ui →
      Xb - xi < 0 ∧ 0 < Yb - ui ∧ 0 < Xa - xi ∧ Ya - ui < 0 ∧
      0 < det2 (Xb - xi, Yb - ui) (Xa - xi, Ya - ui)) := by
  norm_num [det2,mul_comm, mul_sub, sub_add_sub_comm _,hxi.trans,hui.trans,hYa.trans, *]
  use (by valid),by nlinarith,by nlinarith,by ring, fun and=>by repeat use by nlinarith
end Upper9Leaf_085

namespace Upper9Leaf_086

def orient2d (a b c : ℝ × ℝ) : ℝ :=
  (b.1 - a.1) * (c.2 - a.2) - (b.2 - a.2) * (c.1 - a.1)

/-- Section 11 (`upper_9.tex` Lemma `pentagon-cells`(i), Eq. `ear-disjoint` and 4-gon Grassmann-Plücker
    identities, lines 1318--1336):
    (1) If `0 < orient2d a b c`, `orient2d a b x ≤ 0`, and `orient2d b c x ≤ 0`, then `orient2d a c x < 0`.
    (2) For any counterclockwise convex 4-gon `(a, b, c, d)`, `0 ≤ orient2d a b x ∧ orient2d b c x < 0 → orient2d b d x < 0`
        and `orient2d a c x < 0 ∧ orient2d c d x < 0 → orient2d b c x < 0`. -/
theorem pentagon_halfplane_inclusions_4gon_core
    (a b c d x : ℝ × ℝ)
    (habc : 0 < orient2d a b c)
    (hbcd : 0 < orient2d b c d)
    (hcda : 0 < orient2d c d a)
    (hdab : 0 < orient2d d a b) :
    (orient2d a b x ≤ 0 → orient2d b c x ≤ 0 → orient2d a c x < 0) ∧
    orient2d a b c * orient2d b d x = orient2d d a b * orient2d b c x - orient2d b c d * orient2d a b x ∧
    orient2d c d a * orient2d b c x = orient2d b c d * orient2d a c x + orient2d a b c * orient2d c d x ∧
    (0 ≤ orient2d a b x → orient2d b c x < 0 → orient2d b d x < 0) ∧
    (orient2d a c x < 0 → orient2d c d x < 0 → orient2d b c x < 0) := by
  delta orient2d at*
  use fun and h=>by cases em (x.2 > a.snd) with nlinarith,by ring,by ring,fun _ _=>by nlinarith,fun _ _=>by nlinarith
end Upper9Leaf_086

namespace Upper9Leaf_087

def orient2d (a b c : ℝ × ℝ) : ℝ :=
  (b.1 - a.1) * (c.2 - a.2) - (b.2 - a.2) * (c.1 - a.1)

private def sw (p : ℝ × ℝ) : ℝ × ℝ := (p.2, p.1)

private lemma core4
    (a b c d x : ℝ × ℝ)
    (habc : 0 < orient2d a b c)
    (hbcd : 0 < orient2d b c d)
    (hcda : 0 < orient2d c d a)
    (hdab : 0 < orient2d d a b) :
    (orient2d a b x ≤ 0 → orient2d b c x ≤ 0 → orient2d a c x < 0) ∧
    (0 ≤ orient2d a b x → orient2d b c x < 0 → orient2d b d x < 0) ∧
    (orient2d a c x < 0 → orient2d c d x < 0 → orient2d b c x < 0) := by
  have id1 : orient2d a b c * orient2d b d x = orient2d d a b * orient2d b c x - orient2d b c d * orient2d a b x := by
    delta orient2d; ring
  have id2 : orient2d c d a * orient2d b c x = orient2d b c d * orient2d a c x + orient2d a b c * orient2d c d x := by
    delta orient2d; ring
  refine ⟨?_, fun h1 h2 => by nlinarith, fun h1 h2 => by nlinarith⟩
  delta orient2d at habc ⊢
  intro h1 h2
  cases em (x.2 > a.2) with nlinarith

private lemma inc_bar_13
    (q0 q1 q2 q3 q4 x : ℝ × ℝ)
    (h012 : 0 < orient2d q0 q1 q2) (h013 : 0 < orient2d q0 q1 q3)
    (h023 : 0 < orient2d q0 q2 q3)
    (h123 : 0 < orient2d q1 q2 q3) (h124 : 0 < orient2d q1 q2 q4) (h134 : 0 < orient2d q1 q3 q4)
    (h234 : 0 < orient2d q2 q3 q4)
    (h0ge : 0 ≤ orient2d q0 q1 x) (h1m : orient2d q1 q2 x < 0) (h3m : orient2d q3 q4 x < 0) :
    orient2d q2 q3 x < 0 := by
  have h023' : 0 < orient2d q2 q3 q0 := by delta orient2d at h023 ⊢; linarith
  have h013' : 0 < orient2d q3 q0 q1 := by delta orient2d at h013 ⊢; linarith
  have h13m : orient2d q1 q3 x < 0 :=
    (core4 q0 q1 q2 q3 x h012 h123 h023' h013').2.1 h0ge h1m
  have h134' : 0 < orient2d q3 q4 q1 := by delta orient2d at h134 ⊢; linarith
  have h124' : 0 < orient2d q4 q1 q2 := by delta orient2d at h124 ⊢; linarith
  exact (core4 q1 q2 q3 q4 x h123 h234 h134' h124').2.2 h13m h3m

private lemma inc_bar_24
    (q0 q1 q2 q3 q4 x : ℝ × ℝ)
    (h013 : 0 < orient2d q0 q1 q3) (h014 : 0 < orient2d q0 q1 q4)
    (h023 : 0 < orient2d q0 q2 q3) (h024 : 0 < orient2d q0 q2 q4) (h034 : 0 < orient2d q0 q3 q4)
    (h134 : 0 < orient2d q1 q3 q4)
    (h234 : 0 < orient2d q2 q3 q4)
    (h0ge : 0 ≤ orient2d q0 q1 x) (h2m : orient2d q2 q3 x < 0) (h4m : orient2d q4 q0 x < 0) :
    orient2d q3 q4 x < 0 := by
  -- Apply `inc_bar_13` to the reflected CCW pentagon `(r0, r1, r2, r3, r4) = (sw q1, sw q0, sw q4, sw q3, sw q2)`!
  have key := inc_bar_13 (sw q1) (sw q0) (sw q4) (sw q3) (sw q2) (sw x)
    (by delta orient2d sw at *; linarith)
    (by delta orient2d sw at *; linarith)
    (by delta orient2d sw at *; linarith)
    (by delta orient2d sw at *; linarith)
    (by delta orient2d sw at *; linarith)
    (by delta orient2d sw at *; linarith)
    (by delta orient2d sw at *; linarith)
    (by delta orient2d sw at *; linarith)
    (by delta orient2d sw at *; linarith)
    (by delta orient2d sw at *; linarith)
  dsimp [orient2d, sw] at key ⊢
  linarith

private lemma inc_bar_14
    (q0 q1 q2 q3 q4 x : ℝ × ℝ)
    (h012 : 0 < orient2d q0 q1 q2) (h013 : 0 < orient2d q0 q1 q3) (h014 : 0 < orient2d q0 q1 q4)
    (h023 : 0 < orient2d q0 q2 q3) (h024 : 0 < orient2d q0 q2 q4) (h034 : 0 < orient2d q0 q3 q4)
    (h123 : 0 < orient2d q1 q2 q3) (h124 : 0 < orient2d q1 q2 q4) (h134 : 0 < orient2d q1 q3 q4)
    (h234 : 0 < orient2d q2 q3 q4)
    (h0ge : 0 ≤ orient2d q0 q1 x) (h1m : orient2d q1 q2 x < 0) (h4m : orient2d q4 q0 x < 0) :
    orient2d q2 q3 x < 0 ∧ orient2d q3 q4 x < 0 := by
  have h14m : orient2d q1 q4 x < 0 :=
    (core4 q0 q1 q2 q4 x h012 h124 (by delta orient2d at h024 ⊢; linarith) (by delta orient2d at h014 ⊢; linarith)).2.1 h0ge h1m
  have h3m : orient2d q3 q4 x < 0 :=
    (core4 q1 q3 q4 q0 x h134 (by delta orient2d at h034 ⊢; linarith) (by delta orient2d at h014 ⊢; linarith) (by delta orient2d at h013 ⊢; linarith)).2.2 h14m h4m
  exact ⟨inc_bar_13 q0 q1 q2 q3 q4 x h012 h013 h023 h123 h124 h134 h234 h0ge h1m h3m, h3m⟩

/-- Section 11 (`upper_9.tex` Lemma `pentagon-cells`(i), all 6 pentagon half-plane inclusions, lines 1319--1325):
    For any strictly convex counterclockwise pentagon `(p0, p1, p2, p3, p4)` in `ℝ²` and any `x : ℝ × ℝ`,
    all six inclusions (`ear-disjoint`, `H0-cont` x3, `H02-13`, `H02-03`, `H02-24`) hold. -/
theorem pentagon_cells_all_inclusions
    (p0 p1 p2 p3 p4 x : ℝ × ℝ)
    (h012 : 0 < orient2d p0 p1 p2) (h013 : 0 < orient2d p0 p1 p3) (h014 : 0 < orient2d p0 p1 p4)
    (h023 : 0 < orient2d p0 p2 p3) (h024 : 0 < orient2d p0 p2 p4) (h034 : 0 < orient2d p0 p3 p4)
    (h123 : 0 < orient2d p1 p2 p3) (h124 : 0 < orient2d p1 p2 p4) (h134 : 0 < orient2d p1 p3 p4)
    (h234 : 0 < orient2d p2 p3 p4) :
    let H0p := 0 < orient2d p0 p1 x
    let H0m := orient2d p0 p1 x < 0
    let H1m := orient2d p1 p2 x < 0
    let H2m := orient2d p2 p3 x < 0
    let H3m := orient2d p3 p4 x < 0
    let H4m := orient2d p4 p0 x < 0
    let H02p := 0 < orient2d p0 p2 x
    (H02p → orient2d p0 p1 x ≤ 0 → orient2d p1 p2 x ≤ 0 → False) ∧
    (H0p → H1m → H3m → H2m ∧ H3m) ∧
    (H0p → H2m → H4m → H2m ∧ H3m) ∧
    (H0p → H1m → H4m → H2m ∧ H3m) ∧
    (H02p → H1m → H3m → H2m ∧ H3m) ∧
    (H02p → H0m → H3m → H3m ∧ H4m) ∧
    (H02p → H2m → H4m → H2m ∧ H3m) := by
  have hear : 0 < orient2d p0 p2 x → orient2d p0 p1 x ≤ 0 → orient2d p1 p2 x ≤ 0 → False := by
    intro h02 h0le h1le
    have := (core4 p0 p1 p2 p3 x h012 h123 (by delta orient2d at h023 ⊢; linarith) (by delta orient2d at h013 ⊢; linarith)).1 h0le h1le
    linarith
  have hdich : 0 < orient2d p0 p2 x → 0 ≤ orient2d p0 p1 x ∨ 0 ≤ orient2d p1 p2 x := by
    intro h02
    by_contra hc
    push_neg at hc
    exact hear h02 (le_of_lt hc.1) (le_of_lt hc.2)
  refine ⟨hear,
    fun h0 h1 h3 => ⟨inc_bar_13 p0 p1 p2 p3 p4 x h012 h013 h023 h123 h124 h134 h234 (le_of_lt h0) h1 h3, h3⟩,
    fun h0 h2 h4 => ⟨h2, inc_bar_24 p0 p1 p2 p3 p4 x h013 h014 h023 h024 h034 h134 h234 (le_of_lt h0) h2 h4⟩,
    fun h0 h1 h4 => inc_bar_14 p0 p1 p2 p3 p4 x h012 h013 h014 h023 h024 h034 h123 h124 h134 h234 (le_of_lt h0) h1 h4,
    ?_, ?_, ?_⟩
  · intro h02 h1 h3
    rcases hdich h02 with h0ge | h1ge
    · exact ⟨inc_bar_13 p0 p1 p2 p3 p4 x h012 h013 h023 h123 h124 h134 h234 h0ge h1 h3, h3⟩
    · linarith
  · intro h02 h0 h3
    rcases hdich h02 with h0ge | h1ge
    · linarith
    · -- Cyclically shifted pentagon `(p1, p2, p3, p4, p0)` with `0 ≤ orient p1 p2 x`, `orient p3 p4 x < 0` (`q2 q3`), `orient p0 p1 x < 0` (`q4 q0`)!
      have h4m := inc_bar_24 p1 p2 p3 p4 p0 x
        h124 (by delta orient2d at h012 ⊢; linarith)
        h134 (by delta orient2d at h013 ⊢; linarith) (by delta orient2d at h014 ⊢; linarith)
        (by delta orient2d at h024 ⊢; linarith)
        (by delta orient2d at h034 ⊢; linarith)
        h1ge h3 h0
      exact ⟨h3, h4m⟩
  · intro h02 h2 h4
    rcases hdich h02 with h0ge | h1ge
    · exact ⟨h2, inc_bar_24 p0 p1 p2 p3 p4 x h013 h014 h023 h024 h034 h134 h234 h0ge h2 h4⟩
    · -- Cyclically shifted pentagon `(p1, p2, p3, p4, p0)` with `0 ≤ orient p1 p2 x`, `orient p2 p3 x < 0` (`q1 q2`), `orient p4 p0 x < 0` (`q3 q4`)!
      have h3m := inc_bar_13 p1 p2 p3 p4 p0 x
        h123 h124 h134 h234 (by delta orient2d at h023 ⊢; linarith) (by delta orient2d at h024 ⊢; linarith) (by delta orient2d at h034 ⊢; linarith)
        h1ge h2 h4
      exact ⟨h2, h3m⟩
end Upper9Leaf_087

namespace Upper9Leaf_088

def orient2d (a b c : ℝ × ℝ) : ℝ :=
  (b.1 - a.1) * (c.2 - a.2) - (b.2 - a.2) * (c.1 - a.1)

/-- Section 11 (`upper_9.tex` Lemma `pentagon-cells`(iii), lines 1327 & 1340):
    If `h` lies outside edge `pr pr_next` (`orient2d pr pr_next h < 0`) while `p0` and `v0` lie on its
    non-negative side (`0 ≤ orient2d pr pr_next p0`, `0 ≤ orient2d pr pr_next v0`) and `0 < orient2d p0 v0 h`,
    then every `x` with `h ∈ int △(x, p0, v0)` (`h = α0•p0 + α1•v0 + αx•x`, `α0, α1, αx > 0`, sum `1`)
    satisfies `0 < orient2d p0 v0 x ∧ orient2d pr pr_next x < 0` (`U(h; p0, v0) ⊆ H^+(p0, v0) ∩ H_{r*}^-`). -/
theorem pentagon_cells_certified_cone
    (p0 v0 pr pr_next h x : ℝ × ℝ) (α0 α1 αx : ℝ)
    (hh_out : orient2d pr pr_next h < 0)
    (hp0_in : 0 ≤ orient2d pr pr_next p0)
    (hv0_in : 0 ≤ orient2d pr pr_next v0)
    (hh_pos : 0 < orient2d p0 v0 h)
    (hα0 : 0 < α0) (hα1 : 0 < α1) (hαx : 0 < αx)
    (hsum : α0 + α1 + αx = 1)
    (hx1 : h.1 = α0 * p0.1 + α1 * v0.1 + αx * x.1)
    (hx2 : h.2 = α0 * p0.2 + α1 * v0.2 + αx * x.2) :
    0 < orient2d p0 v0 x ∧ orient2d pr pr_next x < 0 := by
  have id_0v : orient2d p0 v0 h = αx * orient2d p0 v0 x := by
    delta orient2d
    rw [hx1, hx2]
    linear_combination (p0.2 * v0.1 - p0.1 * v0.2) * hsum
  have id_rr : orient2d pr pr_next h =
      α0 * orient2d pr pr_next p0 + α1 * orient2d pr pr_next v0 + αx * orient2d pr pr_next x := by
    delta orient2d
    rw [hx1, hx2]
    linear_combination (pr.2 * pr_next.1 - pr.1 * pr_next.2) * hsum
  exact ⟨by nlinarith, by nlinarith⟩
end Upper9Leaf_088

namespace Upper9Leaf_089

def orient2d (a b c : ℝ × ℝ) : ℝ :=
  (b.1 - a.1) * (c.2 - a.2) - (b.2 - a.2) * (c.1 - a.1)

def inIntTri (a b c y : ℝ × ℝ) : Prop :=
  0 < orient2d a b y ∧ 0 < orient2d b c y ∧ 0 < orient2d c a y

/-- Section 11 (`upper_9.tex` Lemma `adjacent-ear-empty`(ii), lines 1359--1360):
    Suppose `(p0, p1, p2)` is counterclockwise (`0 < orient2d p0 p1 p2`), `wD` lies in
    `H^+(p0, p1) ∩ H^+(p1, p2) ∩ H^+(p0, p2)`, and `y` lies in `H^+(p0, p2)` (`0 < orient2d p0 p2 y`).
    If `y ∈ int △(p0, p1, wD)` or `y ∈ int △(p1, p2, wD)`, then `y ∈ int △(p0, p2, wD)`. -/
theorem adjacent_ear_empty_chord_triangle
    (p0 p1 p2 wD y : ℝ × ℝ)
    (_h012 : 0 < orient2d p0 p1 p2)
    (hw01 : 0 < orient2d p0 p1 wD)
    (hw12 : 0 < orient2d p1 p2 wD)
    (hw02 : 0 < orient2d p0 p2 wD)
    (hy02 : 0 < orient2d p0 p2 y)
    (hy_fan : inIntTri p0 p1 wD y ∨ inIntTri p1 p2 wD y) :
    inIntTri p0 p2 wD y := by
  rcases hy_fan with ⟨_, hy1w, hyw0⟩ | ⟨_, hy2w, hyw1⟩
  · have gp1 : orient2d p0 p1 wD * orient2d p2 wD y =
        orient2d p0 p2 wD * orient2d p1 wD y + orient2d p1 p2 wD * orient2d wD p0 y := by
      delta orient2d; ring
    exact ⟨hy02, by nlinarith, hyw0⟩
  · have gp2 : orient2d p1 p2 wD * orient2d wD p0 y =
        orient2d p0 p1 wD * orient2d p2 wD y + orient2d p0 p2 wD * orient2d wD p1 y := by
      delta orient2d; ring
    exact ⟨hy02, hy2w, by nlinarith⟩
end Upper9Leaf_089

namespace Upper9Leaf_090

/-- Section 11 (`upper_9.tex` Theorem `no-five-M` / `main`, lines 1362--1405):
    Non-vacuous master logical deduction ruling out all ten-point shattered sets across BOTH
    Regime 1 (`isRegime2 = false`, `u0 v0 = 01`) and Regime 2 (`isRegime2 = true`, `u0 v0 = 02`),
    and across BOTH Case 1 (`H ≠ ∅`, `r* ∈ {1, 2, 3, 4}` in Regime 1 and `r* ∈ {2, 3, 4}` in Regime 2)
    and Case 2 (`H = ∅`, where `M = A ⊂ ⋂_r H_r^+` enables `thm_L_obs`), from Lemma `pentagon-cells`,
    Theorem `v-epigraph`(2), and Theorem `L-two-halfplanes`. -/
theorem no_ten_point_shattered_master
    {Point : Type}
    (isRegime2 : Bool)
    (Hpos : Fin 5 → Point → Prop)
    (H02pos : Point → Prop)
    (R11111 : Point → Prop)
    (inc_H0_13 : ∀ z, Hpos 0 z → ¬ Hpos 1 z → ¬ Hpos 3 z → ¬ Hpos 2 z ∧ ¬ Hpos 3 z)
    (inc_H0_24 : ∀ z, Hpos 0 z → ¬ Hpos 2 z → ¬ Hpos 4 z → ¬ Hpos 2 z ∧ ¬ Hpos 3 z)
    (inc_H0_14 : ∀ z, Hpos 0 z → ¬ Hpos 1 z → ¬ Hpos 4 z → ¬ Hpos 2 z ∧ ¬ Hpos 3 z)
    (inc_H02_13 : ∀ z, H02pos z → ¬ Hpos 1 z → ¬ Hpos 3 z → ¬ Hpos 2 z ∧ ¬ Hpos 3 z)
    (inc_H02_03 : ∀ z, H02pos z → ¬ Hpos 0 z → ¬ Hpos 3 z → ¬ Hpos 3 z ∧ ¬ Hpos 4 z)
    (inc_H02_24 : ∀ z, H02pos z → ¬ Hpos 2 z → ¬ Hpos 4 z → ¬ Hpos 2 z ∧ ¬ Hpos 3 z)
    (xk : Fin 5 → Fin 32 → Point)
    (hxk_R11111 : ∀ k, R11111 (xk k 31))
    (h_nonfront3 : ∀ m, Hpos 2 (xk 3 m) ∨ Hpos 3 (xk 3 m))
    (h_nonfront4 : ∀ m, Hpos 3 (xk 4 m) ∨ Hpos 4 (xk 4 m))
    (h_nonfront2 : ∀ m, Hpos 1 (xk 2 m) ∨ Hpos 2 (xk 2 m))
    (h_xor3 : Hpos 2 (xk 3 31) ↔ ¬ Hpos 3 (xk 3 31))
    (h_xor4 : Hpos 3 (xk 4 31) ↔ ¬ Hpos 4 (xk 4 31))
    (thm_v_sep : ∀ (r : Fin 5) (fam : Fin 32 → Point), (∀ m, Hpos r (fam m)) → ∀ z, R11111 z → Hpos r z)
    (h_regime :
      if isRegime2 = false then
        (∀ k m, Hpos 0 (xk k m)) ∧ (∀ z, R11111 z → Hpos 0 z) ∧ (Hpos 1 (xk 2 31) ↔ ¬ Hpos 2 (xk 2 31))
      else
        (∀ k m, H02pos (xk k m)) ∧ (∀ z, R11111 z → H02pos z) ∧ (Hpos 0 (xk 1 31) ↔ ¬ Hpos 1 (xk 1 31)))
    (h_case :
      (∃ rstar : Fin 5, rstar ≠ 0 ∧ (isRegime2 = true → rstar ≠ 1) ∧
        (∀ k m, ¬ Hpos rstar (xk k m)) ∧
        (∀ z, R11111 z → ¬ Hpos rstar z)) ∨
      (∀ (a b : Fin 5) (fam : Fin 32 → Point),
        (∀ m, Hpos a (fam m) ∨ Hpos b (fam m)) →
        ∀ za zb, R11111 za → R11111 zb → ¬ Hpos a za → ¬ Hpos b zb → False)) :
    False := by
  rcases h_case with ⟨rstar, hr0, hr1, hr_xk, hr_R⟩ | thm_L_obs
  · -- Case 1: H ≠ ∅ (`rstar ∈ {1, 2, 3, 4}`)
    fin_cases rstar
    · exact hr0 rfl
    · -- rstar = 1 (`isRegime2 = false`)
      cases hreg : isRegime2
      · rw [hreg, if_pos rfl] at h_regime
        rcases h_regime with ⟨h0_xk, h0_R, _⟩
        have hx3_in_H3 : ∀ m, Hpos 3 (xk 3 m) := by
          intro m
          by_contra hn3
          have h2m := (inc_H0_13 (xk 3 m) (h0_xk 3 m) (hr_xk 3 m) hn3).1
          rcases h_nonfront3 m with h2 | h3
          · exact h2m h2
          · exact hn3 h3
        have hR_H3 : ∀ z, R11111 z → Hpos 3 z := thm_v_sep 3 (xk 3) hx3_in_H3
        have h4_3 : Hpos 3 (xk 4 31) := hR_H3 (xk 4 31) (hxk_R11111 4)
        have hn4 : ¬ Hpos 4 (xk 4 31) := h_xor4.mp h4_3
        have hn3_4 := (inc_H0_14 (xk 4 31) (h0_R _ (hxk_R11111 4)) (hr_R _ (hxk_R11111 4)) hn4).2
        exact hn3_4 h4_3
      · exact hr1 hreg rfl
    · -- rstar = 2
      have hx3_in_H3 : ∀ m, Hpos 3 (xk 3 m) := by
        intro m
        rcases h_nonfront3 m with h2 | h3
        · exact False.elim (hr_xk 3 m h2)
        · exact h3
      have hR_H3 : ∀ z, R11111 z → Hpos 3 z := thm_v_sep 3 (xk 3) hx3_in_H3
      have h4_3 : Hpos 3 (xk 4 31) := hR_H3 (xk 4 31) (hxk_R11111 4)
      have hn4 : ¬ Hpos 4 (xk 4 31) := h_xor4.mp h4_3
      cases hreg : isRegime2
      · rw [hreg, if_pos rfl] at h_regime
        have hn3_4 := (inc_H0_24 (xk 4 31) (h_regime.2.1 _ (hxk_R11111 4)) (hr_R _ (hxk_R11111 4)) hn4).2
        exact hn3_4 h4_3
      · rw [hreg, if_neg (by decide)] at h_regime
        have hn3_4 := (inc_H02_24 (xk 4 31) (h_regime.2.1 _ (hxk_R11111 4)) (hr_R _ (hxk_R11111 4)) hn4).2
        exact hn3_4 h4_3
    · -- rstar = 3
      have hx3_in_H2 : ∀ m, Hpos 2 (xk 3 m) := fun m => (h_nonfront3 m).resolve_right (hr_xk 3 m)
      have hx4_in_H4 : ∀ m, Hpos 4 (xk 4 m) := fun m => (h_nonfront4 m).resolve_left (hr_xk 4 m)
      have hR_H2 : ∀ z, R11111 z → Hpos 2 z := thm_v_sep 2 (xk 3) hx3_in_H2
      have hR_H4 : ∀ z, R11111 z → Hpos 4 z := thm_v_sep 4 (xk 4) hx4_in_H4
      cases hreg : isRegime2
      · rw [hreg, if_pos rfl] at h_regime
        rcases h_regime with ⟨_, h0_R, h_xor2⟩
        have h2_2 : Hpos 2 (xk 2 31) := hR_H2 (xk 2 31) (hxk_R11111 2)
        have hn1 : ¬ Hpos 1 (xk 2 31) := fun h1 => (h_xor2.mp h1) h2_2
        have hn2 := (inc_H0_13 (xk 2 31) (h0_R _ (hxk_R11111 2)) hn1 (hr_R _ (hxk_R11111 2))).1
        exact hn2 h2_2
      · rw [hreg, if_neg (by decide)] at h_regime
        rcases h_regime with ⟨_, h02_R, h_xor1⟩
        have hn3_1 : ¬ Hpos 3 (xk 1 31) := hr_R (xk 1 31) (hxk_R11111 1)
        have h1_in_H1 : Hpos 1 (xk 1 31) := by
          by_contra hn1
          exact (inc_H02_13 (xk 1 31) (h02_R _ (hxk_R11111 1)) hn1 hn3_1).1 (hR_H2 _ (hxk_R11111 1))
        have h1_in_H0 : Hpos 0 (xk 1 31) := by
          by_contra hn0
          exact (inc_H02_03 (xk 1 31) (h02_R _ (hxk_R11111 1)) hn0 hn3_1).2 (hR_H4 _ (hxk_R11111 1))
        exact (h_xor1.mp h1_in_H0) h1_in_H1
    · -- rstar = 4
      have hx4_in_H3 : ∀ m, Hpos 3 (xk 4 m) := fun m => (h_nonfront4 m).resolve_right (hr_xk 4 m)
      have hR_H3 : ∀ z, R11111 z → Hpos 3 z := thm_v_sep 3 (xk 4) hx4_in_H3
      have h3_3 : Hpos 3 (xk 3 31) := hR_H3 (xk 3 31) (hxk_R11111 3)
      have hn2 : ¬ Hpos 2 (xk 3 31) := fun h2 => (h_xor3.mp h2) h3_3
      cases hreg : isRegime2
      · rw [hreg, if_pos rfl] at h_regime
        exact (inc_H0_24 (xk 3 31) (h_regime.2.1 _ (hxk_R11111 3)) hn2 (hr_R _ (hxk_R11111 3))).2 h3_3
      · rw [hreg, if_neg (by decide)] at h_regime
        exact (inc_H02_24 (xk 3 31) (h_regime.2.1 _ (hxk_R11111 3)) hn2 (hr_R _ (hxk_R11111 3))).2 h3_3
  · -- Case 2: H = ∅ (`thm_L_obs` applies!)
    have hx3_24 : ∀ m, Hpos 2 (xk 3 m) ∨ Hpos 4 (xk 3 m) := by
      intro m
      by_cases h2 : Hpos 2 (xk 3 m)
      · exact Or.inl h2
      · right
        by_contra h4
        cases hreg : isRegime2
        · rw [hreg, if_pos rfl] at h_regime
          exact False.elim (h2 ((h_nonfront3 m).resolve_right (inc_H0_24 (xk 3 m) (h_regime.1 3 m) h2 h4).2))
        · rw [hreg, if_neg (by decide)] at h_regime
          exact False.elim (h2 ((h_nonfront3 m).resolve_right (inc_H02_24 (xk 3 m) (h_regime.1 3 m) h2 h4).2))
    by_cases h3_2 : Hpos 2 (xk 3 31)
    · -- `xk 3 31 ∈ H_2^+ \ H_3^+` (`¬ Hpos 3 (xk 3 31)`)
      have hn3 : ¬ Hpos 3 (xk 3 31) := h_xor3.mp h3_2
      cases hreg : isRegime2
      · rw [hreg, if_pos rfl] at h_regime
        rcases h_regime with ⟨h0_xk, _, h_xor2⟩
        have hx2_13 : ∀ m, Hpos 1 (xk 2 m) ∨ Hpos 3 (xk 2 m) := by
          intro m
          by_cases h1 : Hpos 1 (xk 2 m)
          · exact Or.inl h1
          · right
            by_contra h3
            exact h1 ((h_nonfront2 m).resolve_right (inc_H0_13 (xk 2 m) (h0_xk 2 m) h1 h3).1)
        by_cases h2_1 : Hpos 1 (xk 2 31)
        · have hn2 : ¬ Hpos 2 (xk 2 31) := h_xor2.mp h2_1
          exact thm_L_obs 2 3 (xk 3) h_nonfront3 (xk 2 31) (xk 3 31) (hxk_R11111 2) (hxk_R11111 3) hn2 hn3
        · exact thm_L_obs 1 3 (xk 2) hx2_13 (xk 2 31) (xk 3 31) (hxk_R11111 2) (hxk_R11111 3) h2_1 hn3
      · rw [hreg, if_neg (by decide)] at h_regime
        rcases h_regime with ⟨h02_xk, _, h_xor1⟩
        have hx3_13 : ∀ m, Hpos 1 (xk 3 m) ∨ Hpos 3 (xk 3 m) := by
          intro m
          by_cases h1 : Hpos 1 (xk 3 m)
          · exact Or.inl h1
          · right
            by_contra h3
            have := inc_H02_13 (xk 3 m) (h02_xk 3 m) h1 h3
            rcases h_nonfront3 m with h2 | h3'
            · exact this.1 h2
            · exact h3 h3'
        have hx4_03 : ∀ m, Hpos 0 (xk 4 m) ∨ Hpos 3 (xk 4 m) := by
          intro m
          by_cases h0 : Hpos 0 (xk 4 m)
          · exact Or.inl h0
          · right
            by_contra h3
            have := inc_H02_03 (xk 4 m) (h02_xk 4 m) h0 h3
            rcases h_nonfront4 m with h3' | h4
            · exact h3 h3'
            · exact this.2 h4
        by_cases h1_0 : Hpos 0 (xk 1 31)
        · have hn1 : ¬ Hpos 1 (xk 1 31) := h_xor1.mp h1_0
          exact thm_L_obs 1 3 (xk 3) hx3_13 (xk 1 31) (xk 3 31) (hxk_R11111 1) (hxk_R11111 3) hn1 hn3
        · exact thm_L_obs 0 3 (xk 4) hx4_03 (xk 1 31) (xk 3 31) (hxk_R11111 1) (hxk_R11111 3) h1_0 hn3
    · -- `¬ Hpos 2 (xk 3 31)`: forbid `(2, 3)` and `(2, 4)` forces `xk 4 31 ∈ H_3^+ ∩ H_4^+`!
      have hn4_3 : ¬ Hpos 3 (xk 4 31) → False :=
        fun hn3_4 => thm_L_obs 2 3 (xk 3) h_nonfront3 (xk 3 31) (xk 4 31) (hxk_R11111 3) (hxk_R11111 4) h3_2 hn3_4
      have h4_3 : Hpos 3 (xk 4 31) := by by_contra h; exact hn4_3 h
      have hn4_4 : ¬ Hpos 4 (xk 4 31) := h_xor4.mp h4_3
      exact thm_L_obs 2 4 (xk 3) hx3_24 (xk 3 31) (xk 4 31) (hxk_R11111 3) (hxk_R11111 4) h3_2 hn4_4
end Upper9Leaf_090

namespace Upper9Leaf_091

def anchorsIn7Minus (d : ZMod 7) (s : Fin 6) : Finset (ZMod 7) :=
  if s.val = 0 then {d + 6, d + 2}
  else if s.val = 5 then {d + 5, d + 1}
  else {d + (s.val : ZMod 7), d + ((s.val + 2 : ℕ) : ZMod 7)}

private lemma anc_dist_le_two (d : ZMod 7) (s : Fin 6) (y : ZMod 7)
    (hy : y = d + ((s.val + 1 : ℕ) : ZMod 7) + 3 ∨ y = d + ((s.val + 1 : ℕ) : ZMod 7) + 4) :
    y ∉ anchorsIn7Minus d s := by
  revert d s y hy
  decide

private lemma subset_no_dist3_is_triple (X : Finset (ZMod 7))
    (hcard : 3 ≤ X.card)
    (hno3 : ∀ x ∈ X, ∀ y ∈ X, y ≠ x + 3) :
    ∃ i : ZMod 7, X = {i, i + 1, i + 2} := by
  revert X hcard hno3
  decide +kernel

private lemma force_sel_at_i (i : ZMod 7) (c0 c1 : Fin 3)
    (h0 : i + ((2 * c0.val + 1 : ℕ) : ZMod 7) ∈ ({i, i + 1, i + 2} : Finset (ZMod 7)))
    (h1 : i + ((2 * c1.val + 2 : ℕ) : ZMod 7) ∈ ({i, i + 1, i + 2} : Finset (ZMod 7))) :
    c1 = 0 := by
  revert i c0 c1 h0 h1
  decide

private lemma force_sel_at_i2 (i : ZMod 7) (c0 : Fin 3)
    (h0 : (i + 2) + ((2 * c0.val + 1 : ℕ) : ZMod 7) ∈ ({i, i + 1, i + 2} : Finset (ZMod 7))) :
    c0 = 2 := by
  revert i c0 h0
  decide

private lemma witness_pair_valid (i : ZMod 7) :
    let p := i + ((2 * (0 : Fin 3).val + 2 : ℕ) : ZMod 7)
    let p' := (i + 2) + ((2 * (2 : Fin 3).val + 1 : ℕ) : ZMod 7)
    p ≠ p' ∧ p' ≠ p + 1 ∧ p ≠ p' + 1 ∧
    p' ∉ anchorsIn7Minus i ⟨1, by omega⟩ ∧
    p ∉ anchorsIn7Minus (i + 2) ⟨4, by omega⟩ := by
  revert i
  decide

private lemma card3_of_ne (a b c : ZMod 7) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ({a, b, c} : Finset (ZMod 7)).card = 3 := by
  revert a b c hab hac hbc
  decide

/-- Section 7 (`upper_9.tex` Lemma `seven-cycle`, Gilbers--Klein, lines 821--829). -/
theorem seven_cycle_lemma
    (choice0 choice1 : ZMod 7 → Fin 3) :
    let off (d : ZMod 7) (b : Bool) : Fin 6 :=
      if b then ⟨2 * (choice1 d).val + 1, by omega⟩ else ⟨2 * (choice0 d).val, by omega⟩
    let elem (d : ZMod 7) (b : Bool) : ZMod 7 := d + (((off d b).val + 1 : ℕ) : ZMod 7)
    let anc (d : ZMod 7) (b : Bool) : Finset (ZMod 7) := anchorsIn7Minus d (off d b)
    ∃ (d1 : ZMod 7) (b1 : Bool) (d2 : ZMod 7) (b2 : Bool),
      let p := elem d1 b1
      let p' := elem d2 b2
      p ≠ p' ∧ p' ≠ p + 1 ∧ p ≠ p' + 1 ∧ p' ∉ anc d1 b1 ∧ p ∉ anc d2 b2 := by
  intro off elem anc
  by_cases hdist3 : ∃ d1 b1 d2 b2, elem d2 b2 = elem d1 b1 + 3
  · rcases hdist3 with ⟨d1, b1, d2, b2, heq⟩
    refine ⟨d1, b1, d2, b2, ?_⟩
    have hp1 : elem d2 b2 ≠ elem d1 b1 := by rw [heq]; generalize elem d1 b1 = z; revert z; decide
    have hp2 : elem d2 b2 ≠ elem d1 b1 + 1 := by rw [heq]; generalize elem d1 b1 = z; revert z; decide
    have hp3 : elem d1 b1 ≠ elem d2 b2 + 1 := by rw [heq]; generalize elem d1 b1 = z; revert z; decide
    have h4 : elem d1 b1 = elem d2 b2 + 4 := by rw [heq]; generalize elem d1 b1 = z; revert z; decide
    refine ⟨hp1.symm, hp2, hp3, ?_, ?_⟩
    · dsimp only [elem, anc] at heq ⊢
      exact anc_dist_le_two d1 (off d1 b1) (d2 + (((off d2 b2).val + 1 : ℕ) : ZMod 7)) (Or.inl heq)
    · dsimp only [elem, anc] at h4 ⊢
      exact anc_dist_le_two d2 (off d2 b2) (d1 + (((off d1 b1).val + 1 : ℕ) : ZMod 7)) (Or.inr h4)
  · have hno_d3 : ∀ d1 b1 d2 b2, elem d2 b2 ≠ elem d1 b1 + 3 := fun d1 b1 d2 b2 h => hdist3 ⟨d1, b1, d2, b2, h⟩
    let X : Finset (ZMod 7) := Finset.univ.biUnion (fun d => {elem d false, elem d true})
    have hmem : ∀ d b, elem d b ∈ X := by
      intro d b
      simp only [X, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton]
      cases b
      · exact ⟨d, Or.inl rfl⟩
      · exact ⟨d, Or.inr rfl⟩
    have hno3 : ∀ x ∈ X, ∀ y ∈ X, y ≠ x + 3 := by
      intro x hx y hy
      simp only [X, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton] at hx hy
      rcases hx with ⟨d1, rfl | rfl⟩ <;> rcases hy with ⟨d2, rfl | rfl⟩
      · exact hno_d3 d1 false d2 false
      · exact hno_d3 d1 false d2 true
      · exact hno_d3 d1 true d2 false
      · exact hno_d3 d1 true d2 true
    have hne_pair : ∀ d : ZMod 7, elem d false ≠ elem d true ∧ elem d false ≠ d ∧ elem d true ≠ d := by
      have aux : ∀ (d : ZMod 7) (c0 c1 : Fin 3),
          d + ((2 * c0.val + 1 : ℕ) : ZMod 7) ≠ d + ((2 * c1.val + 2 : ℕ) : ZMod 7) ∧
          d + ((2 * c0.val + 1 : ℕ) : ZMod 7) ≠ d ∧
          d + ((2 * c1.val + 2 : ℕ) : ZMod 7) ≠ d := by
        intro d c0 c1; revert d c0 c1; decide
      intro d
      exact aux d (choice0 d) (choice1 d)
    have hcard3 : 3 ≤ X.card := by
      let a := elem 0 false
      let b := elem 0 true
      have hab : a ≠ b := (hne_pair 0).1
      have ha_pair := hne_pair a
      by_cases h_eq : elem a false = b
      · let c := elem a true
        have hac : a ≠ c := ha_pair.2.2.symm
        have hbc : b ≠ c := by rw [← h_eq]; exact ha_pair.1
        have hsub : ({a, b, c} : Finset (ZMod 7)) ⊆ X := by
          intro z hz
          simp only [Finset.mem_insert, Finset.mem_singleton] at hz
          rcases hz with rfl | rfl | rfl
          · exact hmem 0 false
          · exact hmem 0 true
          · exact hmem a true
        have hc3 : ({a, b, c} : Finset (ZMod 7)).card = 3 := card3_of_ne a b c hab hac hbc
        exact hc3 ▸ Finset.card_le_card hsub
      · let c := elem a false
        have hac : a ≠ c := ha_pair.2.1.symm
        have hbc : b ≠ c := Ne.symm h_eq
        have hsub : ({a, b, c} : Finset (ZMod 7)) ⊆ X := by
          intro z hz
          simp only [Finset.mem_insert, Finset.mem_singleton] at hz
          rcases hz with rfl | rfl | rfl
          · exact hmem 0 false
          · exact hmem 0 true
          · exact hmem a false
        have hc3 : ({a, b, c} : Finset (ZMod 7)).card = 3 := card3_of_ne a b c hab hac hbc
        exact hc3 ▸ Finset.card_le_card hsub
    rcases subset_no_dist3_is_triple X hcard3 hno3 with ⟨i, hX⟩
    have hc1 : choice1 i = 0 := by
      apply force_sel_at_i i (choice0 i) (choice1 i)
      · have := hmem i false; rw [hX] at this; exact this
      · have := hmem i true; rw [hX] at this; exact this
    have hc0 : choice0 (i + 2) = 2 := by
      apply force_sel_at_i2 i (choice0 (i + 2))
      have := hmem (i + 2) false; rw [hX] at this; exact this
    refine ⟨i, true, i + 2, false, ?_⟩
    dsimp only [elem, anc, off]
    simp only [hc1, hc0]
    exact witness_pair_valid i
end Upper9Leaf_091

namespace Upper9Leaf_092

/-- Section 8.1 (`upper_9.tex` At most seven non-certified vertices `|D| ≤ 7`, lines 835--846):
    Suppose on `Fin 8` that:
    (1) for every `i : Fin 8`, applying the Gap Lemma to `O_i = {i, i+2, i+4}` selects `{i+1}` or `{i+3}`
        (so `A (i + 1) ∨ A (i + 3)`, where `A k` means `k` has a half-plane test on `{k-1, k+1}`);
    (2) no three pairwise non-adjacent vertices `{x, y, z}` all satisfy `A`;
    (3) for every `i : Fin 8`, applying the Gap Lemma to `O'_i = {i, i+2, i+5}` either gives `A (i + 1)`
        or selects a 2-element gap `{k, k + 1}` (`k ∈ {i+3, i+6}`), which cannot coexist with `A (k + 4)`
        or `A (k + 6)`.
    Then `False`. -/
theorem eight_noncertified_vertices_impossible
    (A : Fin 8 → Prop)
    (G2 : Fin 8 → Prop) -- `G2 k` = 2-element gap `{k, k+1}` has half-plane tests on `{k-1, k+2}`
    (h_Oi : ∀ i : Fin 8, A (i + 1) ∨ A (i + 3))
    (h_Oi' : ∀ i : Fin 8, A (i + 1) ∨ G2 (i + 3) ∨ G2 (i + 6))
    (h_no_G2_plus_A : ∀ k : Fin 8, G2 k → ¬ A (k + 4) ∧ ¬ A (k + 6))
    (h_no_3_nonadj : ¬ (A 0 ∧ A 2 ∧ A 5)) :
    False := by
  simp_all +decide -contextual[imp_iff_not_or, Fin.forall_fin_succ]
  grind
end Upper9Leaf_092

namespace Upper9Leaf_093

/-- Section 5.2 (`upper_9.tex` Proposition `good-targets`, lines 659--691):
    For `k ∈ {3, 4}` (`|C| = 2k ∈ {6, 8}`):
    (1) when `v` sees `q`, any split of the `k` odd vertices into `j` and `k - j` (`0 ≤ j ≤ k`)
        across the two open sides of `G = vq` yields `(j - 1) + (k - j - 1) ≥ k - 2` targets
        (using truncating `Nat` subtraction: `j = 0` gives `0 + (k - 1) = k - 1 ≥ k - 2`);
    (2) when `v` misses `q`, if all even vertices lie on one side `L` of `G` on an alternating
        `2k`-cycle, at most `1` odd vertex lies outside `L`, so `j ∈ {k - 1, k}` odd vertices lie in `L`. -/
theorem prop_good_targets_counting
    (k j : ℕ)
    (hk : k = 3 ∨ k = 4)
    (hj : j ≤ k) :
    k - 2 ≤ (j - 1) + (k - j - 1) ∧
    ∀ outside : Finset (Fin (2 * k)),
      (∀ x ∈ outside, x.val % 2 = 1) → outside.card ≤ k ∧
      ((∀ x ∈ outside, ∀ y ∈ outside, x ≠ y → (x.val + 1) % (2 * k) ≠ y.val) →
        -- If vertices outside `L` are consecutive on the `2k`-cycle and all odd, `outside.card ≤ 1`:
        (outside.card ≥ 2 → ∃ x ∈ outside, ∃ y ∈ outside, (x.val + 1) % (2 * k) = y.val) →
        outside.card ≤ 1) := by
  use (by valid),fun R M => ⟨ (R.card_mono (Finset.mem_filter.mpr ⟨ Finset.mem_univ _, M · ·⟩)).trans (by bound),fun a s => not_lt.mp (s ·|>.elim fun and ⟨A, B, S, _⟩ => absurd (a and A B S) ? _)⟩
  exact (. (absurd (M and A) ∘by match k with|3|4=>omega) (by valid))
end Upper9Leaf_093

namespace Upper9Leaf_094

/-- Section 4 (`upper_9.tex` Corollaries `side-preservation` & `endpoint-back`, lines 407--432):
    Let `D = Dl ∪ Dr` be a disjoint partition of a finite set `D` with `5 ≤ D.card`, `l ∈ Dl`, and `r ∈ Dr`,
    and let `Back : D → Prop` satisfy `(2 ≤ Dr.card → ¬ Back l)` and `(2 ≤ Dl.card → ¬ Back r)`.
    (1) (`side-preservation`) For every `Q ⊆ D` with `Q.card ≤ 2` and `∀ p ∈ Q, Back p`, both
        `Dl \ Q` and `Dr \ Q` are nonempty.
    (2) (`endpoint-back`) If `Back l` holds, then `Dr = {r}`, `4 ≤ Dl.card`, and for any `Back'`
        satisfying `(2 ≤ Dl.card → ¬ Back' r)`, `¬ Back' r` holds. -/
theorem side_preservation_and_endpoint_back
    {α : Type*} [DecidableEq α]
    (D Dl Dr Q : Finset α) (l r : α)
    (Back Back' : α → Prop)
    (hpart : D = Dl ∪ Dr) (hdisj : Disjoint Dl Dr)
    (hcard : 5 ≤ D.card)
    (hl : l ∈ Dl) (hr : r ∈ Dr)
    (hno_l : 2 ≤ Dr.card → ¬ Back l)
    (hno_r : 2 ≤ Dl.card → ¬ Back r)
    (hQ_sub : Q ⊆ D) (hQ_card : Q.card ≤ 2) (hQ_back : ∀ p ∈ Q, Back p) :
    ((Dl \ Q).Nonempty ∧ (Dr \ Q).Nonempty) ∧
    (Back l → Dr = {r} ∧ 4 ≤ Dl.card ∧ ((2 ≤ Dl.card → ¬ Back' r) → ¬ Back' r)) := by
  use⟨ Finset.sdiff_nonempty.mpr fun and=>? _, Finset.sdiff_nonempty.mpr fun and=>?_⟩, fun and=> if a: Dr.card=1 then⟨(Finset.eq_of_subset_of_card_le (by norm_num[hr]) a.le).symm,?_⟩else ?_
  · use hno_l (by match hpart▸Dl.card_union_le _,Dl.card_mono and with|A, B=>omega) (hQ_back l (and hl))
  · bound[ Dl.card_union_le Dr, Dr.card_mono and]
  · match hpart▸Dl.card_union_le Dr with | S=>use (by valid), (. (by valid))
  · match hpart▸Dl.card_union_le _, Finset.card_eq_one.2 ⟨ _, Finset.eq_singleton_iff_unique_mem.2 ⟨hr,fun a s=>by_contra fun and' =>hno_l (Finset.one_lt_card.2 (by use a,s,r) ) and⟩⟩ with|A, B=>grind
end Upper9Leaf_094

namespace Upper9Leaf_095

open scoped Classical
open Real

noncomputable section

/-- Lemma 3.6(i): For any `q ∈ Ω` (`qx < 0 ∨ qy < 0`), the positivity set
    `{θ ∈ [π/2, 2π] : q · u(θ) > 0}` has diameter strictly less than `π`. -/
lemma omega_pos_interval_lt_pi
    (qx qy θ1 θ2 : ℝ)
    (hq : qx < 0 ∨ qy < 0)
    (h1_lo : π / 2 ≤ θ1) (h12 : θ1 < θ2) (h2_hi : θ2 ≤ 2 * π)
    (hp1 : qx * cos θ1 + qy * sin θ1 > 0)
    (hp2 : qx * cos θ2 + qy * sin θ2 > 0) :
    θ2 - θ1 < π := by
  use sub_lt_iff_lt_add'.mpr (not_le.1 fun and=>absurd (θ1.cos_nonpos_of_pi_div_two_le_of_le h1_lo (by linarith)) fun and' =>absurd (θ1.sin_nonneg_of_mem_Icc (by repeat use (by linarith) )) ? _)
  use fun andK=>absurd (θ2.cos_sub_pi▸θ1.cos_le_cos_of_nonneg_of_le_pi (by linarith) (by linarith) (by linarith)) fun and20=>?_
  cases le_total 0 qy
  · nlinarith only[hp2,hq.resolve_right (not_lt.2 (by valid)),θ2.sin_two_pi_sub▸Real.sin_nonneg_of_mem_Icc (by repeat use (by linarith)),by valid, and20,and']
  · nlinarith[ (by nlinarith:qx<0),mul_le_mul_of_nonneg_left (by valid) andK, (by nlinarith[θ1.sin_sq,θ2.sin_sq]:-θ2.sin≤θ1.sin)]

end
end Upper9Leaf_095


end
