import Mathlib
import RootTask.UnconditionalBridge
import RootTask.Sec7Combination

open scoped Classical BigOperators
open Finset

noncomputable section

/-!
# Section 8 Reductions & Section 11 Planar Ten-Point Elimination

This module combines:
1. Section 8 reductions:
   - `eight_cycle_impossibility` (`|D| ≤ 7`, from `leaf48`),
   - `seven_cycle_lemma` (`|D| = 7 => |M| ≤ 2`, from `leaf96`),
   - `opposite_endpoint_hexagon_convex_step` & `hexagon_d6_elimination` (`|D| = 6 => |M| ≤ 3`, from `leaf35`/`leaf78`),
   - `prop_opposite_endpoint_exit_orient` & `pentagon_disjoint_exits` (`|D| = 5` disjoint-exit elimination, from `leaf58`/`leaf79`).
2. Concrete planar Lemma 11.2 (`pentagon_halfplane_inclusions_planar`) for any strictly convex CCW pentagon
   `v : Fin 5 → ℝ × ℝ` with `OpenHalfPlane`s `H_r` and `H_02`.
3. Master elimination theorem `no_ten_point_shattered_master` (`leaf95`) and its concrete planar
   instantiation `pentagon_wedges_no_ten_shattered_planar` discharging `thm_v_sep` via
   `thm1_part2_general_halfplane` and `thm_L_obs` via `five_wedges_two_halfplanes_general`.
-/

/-! ## Section 8.1: Eight-Cycle Impossibility (`|D| ≤ 7`) -/

/-- Section 8.1 (`upper_9.tex` Eight-Cycle Lemma):
    On `ℤ/8ℤ` (`Fin 8`), there is no subset `A ⊆ Fin 8` (representing `A_k`) and `G2 ⊆ Fin 8`
    (representing good 2-gaps `{k, k+1}`) simultaneously avoiding 3 pairwise-compatible half-plane
    tests under both `O_i = {i, i+2, i+4}` and `O'_i = {i, i+2, i+5}` for all `i : Fin 8`. -/
theorem eight_cycle_impossibility
    (A G2 : Fin 8 → Bool)
    (hO : ∀ i : Fin 8, A (i + 1) = true ∨ A (i + 3) = true)
    (hO' : ∀ i : Fin 8, A (i + 1) = true ∨ G2 (i + 3) = true ∨ G2 (i + 6) = true)
    (h_no_G2_A : ∀ k : Fin 8, G2 k = true → A (k + 4) = false ∧ A (k + 6) = false)
    (h_no_triple : ¬ (A 0 = true ∧ A 2 = true ∧ A 5 = true)) :
    False := by
  simp_all [imp_iff_not_or, add_assoc, false, Fin.forall_iff_succ]
  grind

/-! ## Section 8.2: Seven-Cycle Lemma (`|D| = 7 => |M| ≤ 2`) -/

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

/-- Section 8.2 (`upper_9.tex` Lemma `seven-cycle`, Gilbers--Klein). -/
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

/-! ## Section 8.3 & 8.4: Hexagon (`|D| = 6 => |M| ≤ 3`) and Pentagon Disjoint Exits -/

/-- Proposition 8.1 (`upper_9.tex`): Convexity of replaced 6-gon `C_{y₀}`. -/
theorem opposite_endpoint_hexagon_convex_step
    (d3 l h y0 x : ℝ × ℝ) (t1 t2 t3 : ℝ)
    (h1 : 0 < t1) (h2 : 0 < t2) (h3 : 0 < t3) (hsum : t1 + t2 + t3 = 1)
    (hy1 : y0.1 = t1 * d3.1 + t2 * l.1 + t3 * h.1)
    (hy2 : y0.2 = t1 * d3.2 + t2 * l.2 + t3 * h.2)
    (ho_d3_l : 0 < orient2D d3 l x)
    (ho_d3_h : 0 < orient2D d3 h x)
    (ho_l_h : 0 < orient2D l h x) :
    0 < orient2D d3 y0 x ∧ 0 < orient2D y0 h x := by
  simp_all only [orient2D, add_assoc, ← eq_sub_iff_add_eq']
  repeat use (by nlinarith only [ho_l_h, ho_d3_l, ho_d3_h, h3, h2, h1])

def compat2 (q1 q2 : Fin 6) (anc1 anc2 : Finset (Fin 6)) : Bool :=
  (q1 != q2) && decide (q1 ∉ anc2) && decide (q2 ∉ anc1)

def validHexBranch : Bool :=
  let anc0 : Finset (Fin 6) := {5, 1}
  let anc1 : Finset (Fin 6) := {0, 2}
  let ok23_H0 :=
    compat2 0 2 anc0 {1} && compat2 0 3 anc0 {4} && compat2 5 0 {1, 4} {1, 4}
  let ok23_H1 :=
    (({0, 3} : Finset (Fin 6)) ∩ {1, 2} == ∅) && (({5, 0} : Finset (Fin 6)) ∩ {1, 2} == ∅) &&
    (({0, 2} : Finset (Fin 6)) ∩ {3, 4} == ∅) && (({5, 0} : Finset (Fin 6)) ∩ {3, 4} == ∅)
  let ok34_H0 :=
    compat2 0 3 anc0 {2} && compat2 1 4 anc1 {5} && compat2 0 1 {2, 5} {2, 5}
  let ok34_H1 :=
    (({1, 4} : Finset (Fin 6)) ∩ {2, 3} == ∅) && (({0, 1} : Finset (Fin 6)) ∩ {2, 3} == ∅) &&
    (({0, 3} : Finset (Fin 6)) ∩ {4, 5} == ∅) && (({0, 1} : Finset (Fin 6)) ∩ {4, 5} == ∅)
  let ok12_H0 :=
    compat2 0 1 {5} {5} && compat2 0 2 anc0 {3} && compat2 0 4 anc0 {5, 3}
  let ok12_H1 :=
    (({0, 1} : Finset (Fin 6)) ∩ {2, 3} == ∅) && (({0, 4} : Finset (Fin 6)) ∩ {2, 3} == ∅)
  let ok01_H0 :=
    compat2 5 0 {4} {4} && compat2 0 3 anc0 {2, 4} &&
    compat2 1 2 {3} {3} && compat2 1 4 anc1 {3, 5} &&
    compat2 1 0 {2} {5}
  let ok01_H1 := (({0, 1} : Finset (Fin 6)) \ {0, 1} == ∅)
  ok23_H0 && ok23_H1 && ok34_H0 && ok34_H1 && ok12_H0 && ok12_H1 && ok01_H0 && ok01_H1

/-- Section 8.3: Elimination of all exit-edge cases for `|D| = 6`. -/
theorem hexagon_d6_elimination : validHexBranch = true := by
  decide +kernel

/-- Proposition 8.4 (Opposite-endpoint exit orientation check). -/
theorem prop_opposite_endpoint_exit_orient
    (d3 l h r d1 uD y0 : ℝ × ℝ)
    (μ0 μ1 μ2 ν0 ν1 ν2 : ℝ)
    (hμ0 : 0 < μ0) (hμ1 : 0 < μ1) (hμ2 : 0 < μ2) (hμ_sum : μ0 + μ1 + μ2 = 1)
    (hh1 : h.1 = μ0 * uD.1 + μ1 * r.1 + μ2 * d1.1)
    (hh2 : h.2 = μ0 * uD.2 + μ1 * r.2 + μ2 * d1.2)
    (hν0 : 0 < ν0) (hν1 : 0 < ν1) (hν2 : 0 < ν2) (hν_sum : ν0 + ν1 + ν2 = 1)
    (hy1 : y0.1 = ν0 * uD.1 + ν1 * d3.1 + ν2 * l.1)
    (hy2 : y0.2 = ν0 * uD.2 + ν1 * d3.2 + ν2 * l.2)
    (h_hrd3 : 0 < orient2D h r d3)
    (h_hd1d3 : 0 < orient2D h d1 d3)
    (h_d3lh : 0 < orient2D d3 l h)
    (h_d3lr : 0 < orient2D d3 l r)
    (h_d3hr : 0 < orient2D d3 h r)
    (h_lhr : 0 < orient2D l h r)
    (hy_d3l : 0 < orient2D d3 l y0)
    (hy_lh : 0 < orient2D l h y0) :
    0 < orient2D h d3 uD ∧ 0 < orient2D h d3 y0 ∧ 0 < orient2D d3 y0 r ∧ 0 < orient2D y0 h r := by
  have hid1 : μ0 * orient2D h d3 uD = μ1 * orient2D h r d3 + μ2 * orient2D h d1 d3 := by
    unfold orient2D
    linear_combination -(d3.1 - h.1) * hh2 + (d3.2 - h.2) * hh1 -
      ((d3.1 - h.1) * h.2 - (d3.2 - h.2) * h.1) * hμ_sum
  have h1 : 0 < orient2D h d3 uD := by
    have hrhs : 0 < μ1 * orient2D h r d3 + μ2 * orient2D h d1 d3 :=
      add_pos (mul_pos hμ1 h_hrd3) (mul_pos hμ2 h_hd1d3)
    by_contra hle
    have : μ0 * orient2D h d3 uD ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (le_of_lt hμ0) (not_lt.mp hle)
    linarith
  have hid2 : orient2D h d3 y0 = ν0 * orient2D h d3 uD + ν2 * orient2D d3 l h := by
    unfold orient2D
    linear_combination (d3.1 - h.1) * hy2 - (d3.2 - h.2) * hy1 +
      ((d3.1 - h.1) * h.2 - (d3.2 - h.2) * h.1) * hν_sum
  have h2 : 0 < orient2D h d3 y0 := by
    rw [hid2]
    exact add_pos (mul_pos hν0 h1) (mul_pos hν2 h_d3lh)
  have hid3 :
      orient2D d3 l h * orient2D d3 y0 r =
      orient2D h d3 y0 * orient2D d3 l r + orient2D d3 l y0 * orient2D d3 h r := by
    unfold orient2D; ring
  have h3 : 0 < orient2D d3 y0 r := by
    have hrhs : 0 < orient2D h d3 y0 * orient2D d3 l r + orient2D d3 l y0 * orient2D d3 h r :=
      add_pos (mul_pos h2 h_d3lr) (mul_pos hy_d3l h_d3hr)
    by_contra hle
    have : orient2D d3 l h * orient2D d3 y0 r ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (le_of_lt h_d3lh) (not_lt.mp hle)
    linarith
  have hid4 :
      orient2D d3 l h * orient2D y0 h r =
      orient2D l h y0 * orient2D d3 h r + orient2D h d3 y0 * orient2D l h r := by
    unfold orient2D; ring
  have h4 : 0 < orient2D y0 h r := by
    have hrhs : 0 < orient2D l h y0 * orient2D d3 h r + orient2D h d3 y0 * orient2D l h r :=
      add_pos (mul_pos hy_lh h_d3hr) (mul_pos h2 h_lhr)
    by_contra hle
    have : orient2D d3 l h * orient2D y0 h r ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (le_of_lt h_d3lh) (not_lt.mp hle)
    linarith
  exact ⟨h1, h2, h3, h4⟩

def compatPent (q1 q2 : Fin 5) (anc1 anc2 : Finset (Fin 5)) : Bool :=
  (q1 != q2) && decide (q1 ∉ anc2) && decide (q2 ∉ anc1)

def checkPentDisjoint : Bool :=
  let s0Choices : List (Fin 5 × Finset (Fin 5)) := [(0, {4}), (1, {2})]
  let s1Choices : List (Fin 5 × Finset (Fin 5)) := [(2, {1}), (3, {4})]
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

/-- Section 8.4: Elimination of disjoint exit edges on a pentagon. -/
theorem pentagon_disjoint_exits : checkPentDisjoint = true := by
  decide +kernel

/-! ## Section 11: Concrete Planar Pentagon Half-Plane Inclusions (Lemma 11.2) -/

/-- Strictly convex counterclockwise pentagon `v : Fin 5 → ℝ × ℝ`. -/
def StrictConvexCCWPentagon (v : Fin 5 → ℝ × ℝ) : Prop :=
  ∀ i j k : Fin 5, i < j → j < k → 0 < orient2D (v i) (v j) (v k)

/-- A strictly convex CCW pentagon is a `StrictConvexCCWPoly` (in the sense of `Sec7Combination`). -/
lemma StrictConvexCCWPentagon.toPoly {v : Fin (2 + 3) → ℝ × ℝ} (hv : StrictConvexCCWPentagon v) :
    StrictConvexCCWPoly v := by
  intro i j hij1 hij2
  rcases i with ⟨iv, hi⟩
  rcases j with ⟨jv, hj⟩
  interval_cases iv <;> interval_cases jv
  · exact False.elim (hij1 rfl)
  · exact False.elim (hij2 rfl)
  · exact hv 0 1 2 (by decide) (by decide)
  · exact hv 0 1 3 (by decide) (by decide)
  · exact hv 0 1 4 (by decide) (by decide)
  · have h := hv 0 1 2 (by decide) (by decide)
    rw [orient2D_cycle, orient2D_cycle] at h; exact h
  · exact False.elim (hij1 rfl)
  · exact False.elim (hij2 rfl)
  · exact hv 1 2 3 (by decide) (by decide)
  · exact hv 1 2 4 (by decide) (by decide)
  · have h := hv 0 2 3 (by decide) (by decide)
    rw [orient2D_cycle, orient2D_cycle] at h; exact h
  · have h := hv 1 2 3 (by decide) (by decide)
    rw [orient2D_cycle, orient2D_cycle] at h; exact h
  · exact False.elim (hij1 rfl)
  · exact False.elim (hij2 rfl)
  · exact hv 2 3 4 (by decide) (by decide)
  · have h := hv 0 3 4 (by decide) (by decide)
    rw [orient2D_cycle, orient2D_cycle] at h; exact h
  · have h := hv 1 3 4 (by decide) (by decide)
    rw [orient2D_cycle, orient2D_cycle] at h; exact h
  · have h := hv 2 3 4 (by decide) (by decide)
    rw [orient2D_cycle, orient2D_cycle] at h; exact h
  · exact False.elim (hij1 rfl)
  · exact False.elim (hij2 rfl)
  · exact False.elim (hij2 rfl)
  · have h := hv 0 1 4 (by decide) (by decide)
    rw [orient2D_cycle] at h; exact h
  · have h := hv 0 2 4 (by decide) (by decide)
    rw [orient2D_cycle] at h; exact h
  · have h := hv 0 3 4 (by decide) (by decide)
    rw [orient2D_cycle] at h; exact h
  · exact False.elim (hij1 rfl)

/-- Open half-plane `H^+(a, b) = {z : orient2D a b z > 0}` to the left of directed edge `a → b`. -/
def edgeHalfPlane (a b : ℝ × ℝ) (hne : a ≠ b) : OpenHalfPlane where
  n := (-(b.2 - a.2), b.1 - a.1)
  c := (b.2 - a.2) * a.1 - (b.1 - a.1) * a.2
  hn := by
    by_contra h
    push Not at h
    apply hne
    ext <;> linarith

lemma edgeHalfPlane_memPos_iff (a b : ℝ × ℝ) (hne : a ≠ b) (z : ℝ × ℝ) :
    (edgeHalfPlane a b hne).MemPos z ↔ 0 < orient2D a b z := by
  have heq : (edgeHalfPlane a b hne).n.1 * z.1 + (edgeHalfPlane a b hne).n.2 * z.2 +
      (edgeHalfPlane a b hne).c = orient2D a b z := by
    dsimp [edgeHalfPlane, orient2D]; ring
  dsimp [OpenHalfPlane.MemPos]
  rw [heq]

lemma edgeHalfPlane_memNeg_iff (a b : ℝ × ℝ) (hne : a ≠ b) (z : ℝ × ℝ) :
    (edgeHalfPlane a b hne).MemNeg z ↔ orient2D a b z < 0 := by
  have heq : (edgeHalfPlane a b hne).n.1 * z.1 + (edgeHalfPlane a b hne).n.2 * z.2 +
      (edgeHalfPlane a b hne).c = orient2D a b z := by
    dsimp [edgeHalfPlane, orient2D]; ring
  dsimp [OpenHalfPlane.MemNeg]
  rw [heq]

lemma StrictConvexCCWPentagon.edge_ne {v : Fin 5 → ℝ × ℝ} (hv : StrictConvexCCWPentagon v)
    (r : Fin 5) : v r ≠ v (r + 1) := by
  intro heq
  rcases r with ⟨rv, hrv⟩
  interval_cases rv
  · change v 0 = v 1 at heq
    have h := hv 0 1 2 (by decide) (by decide)
    rw [heq, orient2D_self_left] at h; linarith
  · change v 1 = v 2 at heq
    have h := hv 1 2 3 (by decide) (by decide)
    rw [heq, orient2D_self_left] at h; linarith
  · change v 2 = v 3 at heq
    have h := hv 2 3 4 (by decide) (by decide)
    rw [heq, orient2D_self_left] at h; linarith
  · change v 3 = v 4 at heq
    have h := hv 0 3 4 (by decide) (by decide)
    rw [heq, orient2D_self_right] at h; linarith
  · change v 4 = v 0 at heq
    have h := hv 0 1 4 (by decide) (by decide)
    rw [heq, orient2D_self_outer] at h; linarith

lemma StrictConvexCCWPentagon.diag02_ne {v : Fin 5 → ℝ × ℝ} (hv : StrictConvexCCWPentagon v) :
    v 0 ≠ v 2 := by
  intro heq
  have h := hv 0 1 2 (by decide) (by decide)
  rw [heq, orient2D_self_outer] at h; linarith

/-- Boundary edge half-planes `H_r^+ = H^+(v r, v (r + 1))` of a strictly convex CCW pentagon. -/
def pentagonEdgeHalfPlane (v : Fin 5 → ℝ × ℝ) (hv : StrictConvexCCWPentagon v)
    (r : Fin 5) : OpenHalfPlane :=
  edgeHalfPlane (v r) (v (r + 1)) (hv.edge_ne r)

/-- Diagonal half-plane `H^+(v 0, v 2)` of a strictly convex CCW pentagon. -/
def pentagonDiag02HalfPlane (v : Fin 5 → ℝ × ℝ) (hv : StrictConvexCCWPentagon v) :
    OpenHalfPlane :=
  edgeHalfPlane (v 0) (v 2) hv.diag02_ne

private def sw (p : ℝ × ℝ) : ℝ × ℝ := (p.2, p.1)

private lemma core4_closed
    (a b c d x : ℝ × ℝ)
    (habc : 0 < orient2D a b c)
    (hbcd : 0 < orient2D b c d)
    (hcda : 0 < orient2D c d a)
    (hdab : 0 < orient2D d a b) :
    (orient2D a b x ≤ 0 → orient2D b c x ≤ 0 → orient2D a c x < 0) ∧
    (0 < orient2D a b x → orient2D b c x ≤ 0 → orient2D b d x < 0) ∧
    (orient2D a c x < 0 → orient2D c d x ≤ 0 → orient2D b c x < 0) := by
  have id1 : orient2D a b c * orient2D b d x =
      orient2D d a b * orient2D b c x - orient2D b c d * orient2D a b x := by
    delta orient2D; ring
  have id2 : orient2D c d a * orient2D b c x =
      orient2D b c d * orient2D a c x + orient2D a b c * orient2D c d x := by
    delta orient2D; ring
  refine ⟨?_, fun h1 h2 => by nlinarith, fun h1 h2 => by nlinarith⟩
  delta orient2D at habc ⊢
  intro h1 h2
  cases em (x.2 > a.2) with nlinarith

private lemma inc_bar_13_closed
    (q0 q1 q2 q3 q4 x : ℝ × ℝ)
    (h012 : 0 < orient2D q0 q1 q2) (h013 : 0 < orient2D q0 q1 q3)
    (h023 : 0 < orient2D q0 q2 q3)
    (h123 : 0 < orient2D q1 q2 q3) (h124 : 0 < orient2D q1 q2 q4) (h134 : 0 < orient2D q1 q3 q4)
    (h234 : 0 < orient2D q2 q3 q4)
    (h0pos : 0 < orient2D q0 q1 x) (h1le : orient2D q1 q2 x ≤ 0) (h3le : orient2D q3 q4 x ≤ 0) :
    orient2D q2 q3 x < 0 := by
  have h023' : 0 < orient2D q2 q3 q0 := by delta orient2D at h023 ⊢; linarith
  have h013' : 0 < orient2D q3 q0 q1 := by delta orient2D at h013 ⊢; linarith
  have h13m : orient2D q1 q3 x < 0 :=
    (core4_closed q0 q1 q2 q3 x h012 h123 h023' h013').2.1 h0pos h1le
  have h134' : 0 < orient2D q3 q4 q1 := by delta orient2D at h134 ⊢; linarith
  have h124' : 0 < orient2D q4 q1 q2 := by delta orient2D at h124 ⊢; linarith
  exact (core4_closed q1 q2 q3 q4 x h123 h234 h134' h124').2.2 h13m h3le

private lemma inc_bar_24_closed
    (q0 q1 q2 q3 q4 x : ℝ × ℝ)
    (h013 : 0 < orient2D q0 q1 q3) (h014 : 0 < orient2D q0 q1 q4)
    (h023 : 0 < orient2D q0 q2 q3) (h024 : 0 < orient2D q0 q2 q4) (h034 : 0 < orient2D q0 q3 q4)
    (h134 : 0 < orient2D q1 q3 q4)
    (h234 : 0 < orient2D q2 q3 q4)
    (h0pos : 0 < orient2D q0 q1 x) (h2le : orient2D q2 q3 x ≤ 0) (h4le : orient2D q4 q0 x ≤ 0) :
    orient2D q3 q4 x < 0 := by
  have key := inc_bar_13_closed (sw q1) (sw q0) (sw q4) (sw q3) (sw q2) (sw x)
    (by delta orient2D sw at *; linarith)
    (by delta orient2D sw at *; linarith)
    (by delta orient2D sw at *; linarith)
    (by delta orient2D sw at *; linarith)
    (by delta orient2D sw at *; linarith)
    (by delta orient2D sw at *; linarith)
    (by delta orient2D sw at *; linarith)
    (by delta orient2D sw at *; linarith)
    (by delta orient2D sw at *; linarith)
    (by delta orient2D sw at *; linarith)
  dsimp [orient2D, sw] at key ⊢
  linarith

private lemma inc_bar_14_closed
    (q0 q1 q2 q3 q4 x : ℝ × ℝ)
    (h012 : 0 < orient2D q0 q1 q2) (h013 : 0 < orient2D q0 q1 q3) (h014 : 0 < orient2D q0 q1 q4)
    (h023 : 0 < orient2D q0 q2 q3) (h024 : 0 < orient2D q0 q2 q4) (h034 : 0 < orient2D q0 q3 q4)
    (h123 : 0 < orient2D q1 q2 q3) (h124 : 0 < orient2D q1 q2 q4) (h134 : 0 < orient2D q1 q3 q4)
    (h234 : 0 < orient2D q2 q3 q4)
    (h0pos : 0 < orient2D q0 q1 x) (h1le : orient2D q1 q2 x ≤ 0) (h4le : orient2D q4 q0 x ≤ 0) :
    orient2D q2 q3 x < 0 ∧ orient2D q3 q4 x < 0 := by
  have h14m : orient2D q1 q4 x < 0 :=
    (core4_closed q0 q1 q2 q4 x h012 h124 (by delta orient2D at h024 ⊢; linarith)
      (by delta orient2D at h014 ⊢; linarith)).2.1 h0pos h1le
  have h3m : orient2D q3 q4 x < 0 :=
    (core4_closed q1 q3 q4 q0 x h134 (by delta orient2D at h034 ⊢; linarith)
      (by delta orient2D at h014 ⊢; linarith)
      (by delta orient2D at h013 ⊢; linarith)).2.2 h14m h4le
  exact ⟨inc_bar_13_closed q0 q1 q2 q3 q4 x h012 h013 h023 h123 h124 h134 h234 h0pos h1le (le_of_lt h3m), h3m⟩

/-- Lemma 11.2 (`pentagon-cells`(i)): All six concrete planar pentagon half-plane inclusions
    (plus `ear-disjoint`) stated directly in terms of `pentagonEdgeHalfPlane` and
    `pentagonDiag02HalfPlane` for any strictly convex CCW pentagon `v : Fin 5 → ℝ × ℝ`. -/
theorem pentagon_halfplane_inclusions_planar
    (v : Fin 5 → ℝ × ℝ) (hv : StrictConvexCCWPentagon v) (z : ℝ × ℝ) :
    let H := pentagonEdgeHalfPlane v hv
    let H02 := pentagonDiag02HalfPlane v hv
    (H02.MemPos z → ¬ (H 0).MemPos z → ¬ (H 1).MemPos z → False) ∧
    ((H 0).MemPos z → ¬ (H 1).MemPos z → ¬ (H 3).MemPos z → ¬ (H 2).MemPos z ∧ ¬ (H 3).MemPos z) ∧
    ((H 0).MemPos z → ¬ (H 2).MemPos z → ¬ (H 4).MemPos z → ¬ (H 2).MemPos z ∧ ¬ (H 3).MemPos z) ∧
    ((H 0).MemPos z → ¬ (H 1).MemPos z → ¬ (H 4).MemPos z → ¬ (H 2).MemPos z ∧ ¬ (H 3).MemPos z) ∧
    (H02.MemPos z → ¬ (H 1).MemPos z → ¬ (H 3).MemPos z → ¬ (H 2).MemPos z ∧ ¬ (H 3).MemPos z) ∧
    (H02.MemPos z → ¬ (H 0).MemPos z → ¬ (H 3).MemPos z → ¬ (H 3).MemPos z ∧ ¬ (H 4).MemPos z) ∧
    (H02.MemPos z → ¬ (H 2).MemPos z → ¬ (H 4).MemPos z → ¬ (H 2).MemPos z ∧ ¬ (H 3).MemPos z) := by
  intro H H02
  have h012 := hv 0 1 2 (by decide) (by decide)
  have h013 := hv 0 1 3 (by decide) (by decide)
  have h014 := hv 0 1 4 (by decide) (by decide)
  have h023 := hv 0 2 3 (by decide) (by decide)
  have h024 := hv 0 2 4 (by decide) (by decide)
  have h034 := hv 0 3 4 (by decide) (by decide)
  have h123 := hv 1 2 3 (by decide) (by decide)
  have h124 := hv 1 2 4 (by decide) (by decide)
  have h134 := hv 1 3 4 (by decide) (by decide)
  have h234 := hv 2 3 4 (by decide) (by decide)
  have hm0 : (H 0).MemPos z ↔ 0 < orient2D (v 0) (v 1) z :=
    edgeHalfPlane_memPos_iff (v 0) (v 1) (hv.edge_ne 0) z
  have hm1 : (H 1).MemPos z ↔ 0 < orient2D (v 1) (v 2) z :=
    edgeHalfPlane_memPos_iff (v 1) (v 2) (hv.edge_ne 1) z
  have hm2 : (H 2).MemPos z ↔ 0 < orient2D (v 2) (v 3) z :=
    edgeHalfPlane_memPos_iff (v 2) (v 3) (hv.edge_ne 2) z
  have hm3 : (H 3).MemPos z ↔ 0 < orient2D (v 3) (v 4) z :=
    edgeHalfPlane_memPos_iff (v 3) (v 4) (hv.edge_ne 3) z
  have hm4 : (H 4).MemPos z ↔ 0 < orient2D (v 4) (v 0) z :=
    edgeHalfPlane_memPos_iff (v 4) (v 0) (hv.edge_ne 4) z
  have hm02 : H02.MemPos z ↔ 0 < orient2D (v 0) (v 2) z :=
    edgeHalfPlane_memPos_iff (v 0) (v 2) hv.diag02_ne z
  have hear : H02.MemPos z → ¬ (H 0).MemPos z → ¬ (H 1).MemPos z → False := by
    intro h02 hn0 hn1
    rw [hm02] at h02
    rw [hm0, not_lt] at hn0
    rw [hm1, not_lt] at hn1
    have hlt := (core4_closed (v 0) (v 1) (v 2) (v 3) z h012 h123
      (by delta orient2D at h023 ⊢; linarith) (by delta orient2D at h013 ⊢; linarith)).1 hn0 hn1
    linarith
  have hdich : H02.MemPos z → (H 0).MemPos z ∨ (H 1).MemPos z := by
    intro h02
    by_contra hnot
    push Not at hnot
    exact hear h02 hnot.1 hnot.2
  refine ⟨hear, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h0 hn1 hn3
    rw [hm0] at h0; rw [hm1, not_lt] at hn1; rw [hm3, not_lt] at hn3
    have h2m := inc_bar_13_closed (v 0) (v 1) (v 2) (v 3) (v 4) z
      h012 h013 h023 h123 h124 h134 h234 h0 hn1 hn3
    exact ⟨by rw [hm2]; linarith, by rw [hm3]; linarith⟩
  · intro h0 hn2 hn4
    rw [hm0] at h0; rw [hm2, not_lt] at hn2; rw [hm4, not_lt] at hn4
    have h3m := inc_bar_24_closed (v 0) (v 1) (v 2) (v 3) (v 4) z
      h013 h014 h023 h024 h034 h134 h234 h0 hn2 hn4
    exact ⟨by rw [hm2]; linarith, by rw [hm3]; linarith⟩
  · intro h0 hn1 hn4
    rw [hm0] at h0; rw [hm1, not_lt] at hn1; rw [hm4, not_lt] at hn4
    have h23m := inc_bar_14_closed (v 0) (v 1) (v 2) (v 3) (v 4) z
      h012 h013 h014 h023 h024 h034 h123 h124 h134 h234 h0 hn1 hn4
    exact ⟨by rw [hm2]; linarith, by rw [hm3]; linarith⟩
  · intro h02 hn1 hn3
    rcases hdich h02 with h0 | h1
    · rw [hm0] at h0; rw [hm1, not_lt] at hn1; rw [hm3, not_lt] at hn3
      have h2m := inc_bar_13_closed (v 0) (v 1) (v 2) (v 3) (v 4) z
        h012 h013 h023 h123 h124 h134 h234 h0 hn1 hn3
      exact ⟨by rw [hm2]; linarith, by rw [hm3]; linarith⟩
    · exact False.elim (hn1 h1)
  · intro h02 hn0 hn3
    rcases hdich h02 with h0 | h1
    · exact False.elim (hn0 h0)
    · rw [hm1] at h1; rw [hm0, not_lt] at hn0; rw [hm3, not_lt] at hn3
      have h4m := inc_bar_24_closed (v 1) (v 2) (v 3) (v 4) (v 0) z
        h124 (by delta orient2D at h012 ⊢; linarith)
        h134 (by delta orient2D at h013 ⊢; linarith) (by delta orient2D at h014 ⊢; linarith)
        (by delta orient2D at h024 ⊢; linarith)
        (by delta orient2D at h034 ⊢; linarith)
        h1 hn3 hn0
      exact ⟨by rw [hm3]; linarith, by rw [hm4]; linarith⟩
  · intro h02 hn2 hn4
    rcases hdich h02 with h0 | h1
    · rw [hm0] at h0; rw [hm2, not_lt] at hn2; rw [hm4, not_lt] at hn4
      have h3m := inc_bar_24_closed (v 0) (v 1) (v 2) (v 3) (v 4) z
        h013 h014 h023 h024 h034 h134 h234 h0 hn2 hn4
      exact ⟨by rw [hm2]; linarith, by rw [hm3]; linarith⟩
    · rw [hm1] at h1; rw [hm2, not_lt] at hn2; rw [hm4, not_lt] at hn4
      have h3m := inc_bar_13_closed (v 1) (v 2) (v 3) (v 4) (v 0) z
        h123 h124 h134 h234
        (by delta orient2D at h023 ⊢; linarith)
        (by delta orient2D at h024 ⊢; linarith)
        (by delta orient2D at h034 ⊢; linarith)
        h1 hn2 hn4
      exact ⟨by rw [hm2]; linarith, by rw [hm3]; linarith⟩

/-! ## Master Ten-Point Shattered Set Elimination (`no_ten_point_shattered_master` & Planar Instantiation) -/

/-- Mask-carrying generalization of `no_ten_point_shattered_master`: each witness family `fam`
    passed to `thm_v_sep` or `thm_L_obs` carries the mask realization predicate `MaskPred`. -/
theorem no_ten_point_shattered_master_masked
    {Point : Type}
    (isRegime2 : Bool)
    (Hpos : Fin 5 → Point → Prop)
    (H02pos : Point → Prop)
    (R11111 : Point → Prop)
    (MaskPred : Fin 32 → Point → Prop)
    (inc_H0_13 : ∀ z, Hpos 0 z → ¬ Hpos 1 z → ¬ Hpos 3 z → ¬ Hpos 2 z ∧ ¬ Hpos 3 z)
    (inc_H0_24 : ∀ z, Hpos 0 z → ¬ Hpos 2 z → ¬ Hpos 4 z → ¬ Hpos 2 z ∧ ¬ Hpos 3 z)
    (inc_H0_14 : ∀ z, Hpos 0 z → ¬ Hpos 1 z → ¬ Hpos 4 z → ¬ Hpos 2 z ∧ ¬ Hpos 3 z)
    (inc_H02_13 : ∀ z, H02pos z → ¬ Hpos 1 z → ¬ Hpos 3 z → ¬ Hpos 2 z ∧ ¬ Hpos 3 z)
    (inc_H02_03 : ∀ z, H02pos z → ¬ Hpos 0 z → ¬ Hpos 3 z → ¬ Hpos 3 z ∧ ¬ Hpos 4 z)
    (inc_H02_24 : ∀ z, H02pos z → ¬ Hpos 2 z → ¬ Hpos 4 z → ¬ Hpos 2 z ∧ ¬ Hpos 3 z)
    (xk : Fin 5 → Fin 32 → Point)
    (hxk_R11111 : ∀ k, R11111 (xk k 31))
    (hxk_mask : ∀ k m, MaskPred m (xk k m))
    (h_nonfront3 : ∀ m, Hpos 2 (xk 3 m) ∨ Hpos 3 (xk 3 m))
    (h_nonfront4 : ∀ m, Hpos 3 (xk 4 m) ∨ Hpos 4 (xk 4 m))
    (h_nonfront2 : ∀ m, Hpos 1 (xk 2 m) ∨ Hpos 2 (xk 2 m))
    (h_xor3 : Hpos 2 (xk 3 31) ↔ ¬ Hpos 3 (xk 3 31))
    (h_xor4 : Hpos 3 (xk 4 31) ↔ ¬ Hpos 4 (xk 4 31))
    (thm_v_sep : ∀ (r : Fin 5) (fam : Fin 32 → Point),
      (∀ m, MaskPred m (fam m)) → (∀ m, Hpos r (fam m)) → ∀ z, R11111 z → Hpos r z)
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
        (∀ m, MaskPred m (fam m)) →
        (∀ m, Hpos a (fam m) ∨ Hpos b (fam m)) →
        ∀ za zb, R11111 za → R11111 zb → ¬ Hpos a za → ¬ Hpos b zb → False)) :
    False := by
  rcases h_case with ⟨rstar, hr0, hr1, hr_xk, hr_R⟩ | thm_L_obs
  · fin_cases rstar
    · exact hr0 rfl
    · cases hreg : isRegime2
      · rw [hreg, if_pos rfl] at h_regime
        rcases h_regime with ⟨h0_xk, h0_R, _⟩
        have hx3_in_H3 : ∀ m, Hpos 3 (xk 3 m) := by
          intro m
          by_contra hn3
          have h2m := (inc_H0_13 (xk 3 m) (h0_xk 3 m) (hr_xk 3 m) hn3).1
          rcases h_nonfront3 m with h2 | h3
          · exact h2m h2
          · exact hn3 h3
        have hR_H3 : ∀ z, R11111 z → Hpos 3 z := thm_v_sep 3 (xk 3) (hxk_mask 3) hx3_in_H3
        have h4_3 : Hpos 3 (xk 4 31) := hR_H3 (xk 4 31) (hxk_R11111 4)
        have hn4 : ¬ Hpos 4 (xk 4 31) := h_xor4.mp h4_3
        have hn3_4 := (inc_H0_14 (xk 4 31) (h0_R _ (hxk_R11111 4)) (hr_R _ (hxk_R11111 4)) hn4).2
        exact hn3_4 h4_3
      · exact hr1 hreg rfl
    · have hx3_in_H3 : ∀ m, Hpos 3 (xk 3 m) := by
        intro m
        rcases h_nonfront3 m with h2 | h3
        · exact False.elim (hr_xk 3 m h2)
        · exact h3
      have hR_H3 : ∀ z, R11111 z → Hpos 3 z := thm_v_sep 3 (xk 3) (hxk_mask 3) hx3_in_H3
      have h4_3 : Hpos 3 (xk 4 31) := hR_H3 (xk 4 31) (hxk_R11111 4)
      have hn4 : ¬ Hpos 4 (xk 4 31) := h_xor4.mp h4_3
      cases hreg : isRegime2
      · rw [hreg, if_pos rfl] at h_regime
        have hn3_4 := (inc_H0_24 (xk 4 31) (h_regime.2.1 _ (hxk_R11111 4)) (hr_R _ (hxk_R11111 4)) hn4).2
        exact hn3_4 h4_3
      · rw [hreg, if_neg (by decide)] at h_regime
        have hn3_4 := (inc_H02_24 (xk 4 31) (h_regime.2.1 _ (hxk_R11111 4)) (hr_R _ (hxk_R11111 4)) hn4).2
        exact hn3_4 h4_3
    · have hx3_in_H2 : ∀ m, Hpos 2 (xk 3 m) := fun m => (h_nonfront3 m).resolve_right (hr_xk 3 m)
      have hx4_in_H4 : ∀ m, Hpos 4 (xk 4 m) := fun m => (h_nonfront4 m).resolve_left (hr_xk 4 m)
      have hR_H2 : ∀ z, R11111 z → Hpos 2 z := thm_v_sep 2 (xk 3) (hxk_mask 3) hx3_in_H2
      have hR_H4 : ∀ z, R11111 z → Hpos 4 z := thm_v_sep 4 (xk 4) (hxk_mask 4) hx4_in_H4
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
    · have hx4_in_H3 : ∀ m, Hpos 3 (xk 4 m) := fun m => (h_nonfront4 m).resolve_right (hr_xk 4 m)
      have hR_H3 : ∀ z, R11111 z → Hpos 3 z := thm_v_sep 3 (xk 4) (hxk_mask 4) hx4_in_H3
      have h3_3 : Hpos 3 (xk 3 31) := hR_H3 (xk 3 31) (hxk_R11111 3)
      have hn2 : ¬ Hpos 2 (xk 3 31) := fun h2 => (h_xor3.mp h2) h3_3
      cases hreg : isRegime2
      · rw [hreg, if_pos rfl] at h_regime
        exact (inc_H0_24 (xk 3 31) (h_regime.2.1 _ (hxk_R11111 3)) hn2 (hr_R _ (hxk_R11111 3))).2 h3_3
      · rw [hreg, if_neg (by decide)] at h_regime
        exact (inc_H02_24 (xk 3 31) (h_regime.2.1 _ (hxk_R11111 3)) hn2 (hr_R _ (hxk_R11111 3))).2 h3_3
  · have hx3_24 : ∀ m, Hpos 2 (xk 3 m) ∨ Hpos 4 (xk 3 m) := by
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
    · have hn3 : ¬ Hpos 3 (xk 3 31) := h_xor3.mp h3_2
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
          exact thm_L_obs 2 3 (xk 3) (hxk_mask 3) h_nonfront3 (xk 2 31) (xk 3 31) (hxk_R11111 2) (hxk_R11111 3) hn2 hn3
        · exact thm_L_obs 1 3 (xk 2) (hxk_mask 2) hx2_13 (xk 2 31) (xk 3 31) (hxk_R11111 2) (hxk_R11111 3) h2_1 hn3
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
          exact thm_L_obs 1 3 (xk 3) (hxk_mask 3) hx3_13 (xk 1 31) (xk 3 31) (hxk_R11111 1) (hxk_R11111 3) hn1 hn3
        · exact thm_L_obs 0 3 (xk 4) (hxk_mask 4) hx4_03 (xk 1 31) (xk 3 31) (hxk_R11111 1) (hxk_R11111 3) h1_0 hn3
    · have hn4_3 : ¬ Hpos 3 (xk 4 31) → False :=
        fun hn3_4 => thm_L_obs 2 3 (xk 3) (hxk_mask 3) h_nonfront3 (xk 3 31) (xk 4 31) (hxk_R11111 3) (hxk_R11111 4) h3_2 hn3_4
      have h4_3 : Hpos 3 (xk 4 31) := by by_contra h; exact hn4_3 h
      have hn4_4 : ¬ Hpos 4 (xk 4 31) := h_xor4.mp h4_3
      exact thm_L_obs 2 4 (xk 3) (hxk_mask 3) hx3_24 (xk 3 31) (xk 4 31) (hxk_R11111 3) (hxk_R11111 4) h3_2 hn4_4

/-- Section 11 (`upper_9.tex` Theorem `no-five-M` / `main`):
    Abstract master deduction ruling out all ten-point shattered sets across BOTH Regime 1 and
    Regime 2, and across BOTH Case 1 (`H ≠ ∅`) and Case 2 (`H = ∅`). -/
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
    False :=
  no_ten_point_shattered_master_masked isRegime2 Hpos H02pos R11111 (fun _ _ => True)
    inc_H0_13 inc_H0_24 inc_H0_14 inc_H02_13 inc_H02_03 inc_H02_24
    xk hxk_R11111 (fun _ _ => trivial) h_nonfront3 h_nonfront4 h_nonfront2 h_xor3 h_xor4
    (fun r fam _ hfam z hz => thm_v_sep r fam hfam z hz) h_regime
    (h_case.imp id (fun hL a b fam _ hfam za zb hza hzb hna hnb => hL a b fam hfam za zb hza hzb hna hnb))

/-- Bitmask conversion `Fin 32 → (Fin 5 → Bool)` with `31 ↦ (fun _ => true)`. -/
def maskOfFin32 (m : Fin 32) (i : Fin 5) : Bool :=
  Nat.testBit m.val i.val

/-- Inverse bitmask conversion `(Fin 5 → Bool) → Fin 32`. -/
def fin32OfMask (b : Fin 5 → Bool) : Fin 32 :=
  ⟨(if b 0 then 1 else 0) + (if b 1 then 2 else 0) + (if b 2 then 4 else 0) +
   (if b 3 then 8 else 0) + (if b 4 then 16 else 0), by
    repeat' split_ifs <;> omega⟩

lemma maskOfFin32_31 : maskOfFin32 31 = fun _ => true := by
  ext i
  fin_cases i <;> decide

lemma maskOfFin32_fin32OfMask (b : Fin 5 → Bool) : maskOfFin32 (fin32OfMask b) = b := by
  ext i
  have aux : ∀ (b0 b1 b2 b3 b4 : Bool) (j : Fin 5),
      Nat.testBit ((if b0 then 1 else 0) + (if b1 then 2 else 0) + (if b2 then 4 else 0) +
        (if b3 then 8 else 0) + (if b4 then 16 else 0)) j.val =
      match j with | 0 => b0 | 1 => b1 | 2 => b2 | 3 => b3 | 4 => b4 := by
    decide
  have h := aux (b 0) (b 1) (b 2) (b 3) (b 4) i
  dsimp [maskOfFin32, fin32OfMask]
  rw [h]
  fin_cases i <;> rfl

/-- Openness of the common wedge intersection `R₁₁₁₁₁`: if `z ∈ R₁₁₁₁₁` and `¬ H.MemPos z`,
    we can nudge `z` slightly inside `R₁₁₁₁₁` into `H.MemNeg`. -/
private lemma exists_memNeg_in_R11111
    (W : Fin 5 → OpenWedge) (H : OpenHalfPlane)
    (z : ℝ × ℝ) (hz_open : ∀ i : Fin 5, (W i).MemOpen z) (hz_not : ¬ H.MemPos z) :
    ∃ z' : ℝ × ℝ, H.MemNeg z' ∧ ∀ i : Fin 5, (W i).MemOpen z' := by
  have hz_le : H.n.1 * z.1 + H.n.2 * z.2 + H.c ≤ 0 := not_lt.mp hz_not
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
  obtain ⟨ε, hε, hball⟩ := hopen z hz_open
  let denom : ℝ := |H.n.1| + |H.n.2| + 1
  have hdenom_pos : 0 < denom := by
    have h1 : 0 ≤ |H.n.1| := abs_nonneg _
    have h2 : 0 ≤ |H.n.2| := abs_nonneg _
    dsimp [denom]; linarith
  let δ : ℝ := ε / (2 * denom)
  have hδ_pos : 0 < δ := div_pos hε (by linarith)
  let z' : ℝ × ℝ := (z.1 - δ * H.n.1, z.2 - δ * H.n.2)
  have hz'_mem : z' ∈ Metric.ball z ε := by
    rw [Metric.mem_ball, Prod.dist_eq]
    simp only [Real.dist_eq, z']
    have h1 : |(z.1 - δ * H.n.1) - z.1| < ε := by
      have heq : (z.1 - δ * H.n.1) - z.1 = -(δ * H.n.1) := by ring
      rw [heq, abs_neg, abs_mul, abs_of_pos hδ_pos]
      have hle : |H.n.1| ≤ denom := by
        have := abs_nonneg H.n.2
        dsimp [denom]; linarith
      calc δ * |H.n.1| ≤ δ * denom := mul_le_mul_of_nonneg_left hle (le_of_lt hδ_pos)
        _ = ε / 2 := by dsimp [δ]; field_simp [ne_of_gt hdenom_pos]
        _ < ε := by linarith
    have h2 : |(z.2 - δ * H.n.2) - z.2| < ε := by
      have heq : (z.2 - δ * H.n.2) - z.2 = -(δ * H.n.2) := by ring
      rw [heq, abs_neg, abs_mul, abs_of_pos hδ_pos]
      have hle : |H.n.2| ≤ denom := by
        have := abs_nonneg H.n.1
        dsimp [denom]; linarith
      calc δ * |H.n.2| ≤ δ * denom := mul_le_mul_of_nonneg_left hle (le_of_lt hδ_pos)
        _ = ε / 2 := by dsimp [δ]; field_simp [ne_of_gt hdenom_pos]
        _ < ε := by linarith
    exact max_lt h1 h2
  refine ⟨z', ?_, hball hz'_mem⟩
  dsimp [OpenHalfPlane.MemNeg, z']
  have hs : 0 < H.n.1 ^ 2 + H.n.2 ^ 2 := by
    rcases H.hn with h1 | h2
    · exact add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero h1) (sq_nonneg _)
    · exact add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_ne_zero h2)
  have heq : H.n.1 * (z.1 - δ * H.n.1) + H.n.2 * (z.2 - δ * H.n.2) + H.c =
      (H.n.1 * z.1 + H.n.2 * z.2 + H.c) - δ * (H.n.1 ^ 2 + H.n.2 ^ 2) := by ring
  rw [heq]
  nlinarith

/-- Concrete planar instantiation of `no_ten_point_shattered_master` directly on `ℝ × ℝ`
    pentagon vertices `v : Fin 5 → ℝ × ℝ`, `OpenHalfPlane`s `pentagonEdgeHalfPlane v hv` and
    `pentagonDiag02HalfPlane v hv`, and `OpenWedge`s `W : Fin 5 → OpenWedge`, discharging:
    - all 6 half-plane inclusions via `pentagon_halfplane_inclusions_planar`,
    - `thm_v_sep` via `thm1_part2_general_halfplane h_thm1`,
    - `thm_L_obs` via `five_wedges_two_halfplanes_general h_thm1 h_caseA_orig`. -/
theorem pentagon_wedges_no_ten_shattered_planar
    (h_thm1 : ∀ f : Fin 5 → VFunc, ¬ (∀ m : Fin 5 → Bool, ∃ q : ℝ × ℝ, RealizesVMask f m q))
    (h_caseA_orig :
      (∀ f : Fin 5 → VFunc, ¬ (∀ m : Fin 5 → Bool, ∃ p : ℝ × ℝ, RealizesVMask f m p)) →
      ∀ W : Fin 5 → OpenWedge,
        (∀ i : Fin 5, (W i).y.1 < 0 ∧ (W i).y.2 < 0) →
        (∀ i : Fin 5, (W i).MemOpen (0, 0)) →
        ¬ (∀ m : Fin 5 → Bool, ∃ p : ℝ × ℝ, (p.1 < 0 ∨ p.2 < 0) ∧ RealizesWedgeMask W m p))
    (isRegime2 : Bool)
    (v : Fin 5 → ℝ × ℝ) (hv : StrictConvexCCWPentagon v)
    (W : Fin 5 → OpenWedge)
    (xk : Fin 5 → (Fin 5 → Bool) → ℝ × ℝ)
    (hxk_mask : ∀ k m, RealizesWedgeMask W m (xk k m))
    (h_nonfront3 : ∀ m, (pentagonEdgeHalfPlane v hv 2).MemPos (xk 3 m) ∨
                        (pentagonEdgeHalfPlane v hv 3).MemPos (xk 3 m))
    (h_nonfront4 : ∀ m, (pentagonEdgeHalfPlane v hv 3).MemPos (xk 4 m) ∨
                        (pentagonEdgeHalfPlane v hv 4).MemPos (xk 4 m))
    (h_nonfront2 : ∀ m, (pentagonEdgeHalfPlane v hv 1).MemPos (xk 2 m) ∨
                        (pentagonEdgeHalfPlane v hv 2).MemPos (xk 2 m))
    (h_xor3 : (pentagonEdgeHalfPlane v hv 2).MemPos (xk 3 (fun _ => true)) ↔
              ¬ (pentagonEdgeHalfPlane v hv 3).MemPos (xk 3 (fun _ => true)))
    (h_xor4 : (pentagonEdgeHalfPlane v hv 3).MemPos (xk 4 (fun _ => true)) ↔
              ¬ (pentagonEdgeHalfPlane v hv 4).MemPos (xk 4 (fun _ => true)))
    (h_regime :
      if isRegime2 = false then
        (∀ k m, (pentagonEdgeHalfPlane v hv 0).MemPos (xk k m)) ∧
        (∀ z, (∀ i : Fin 5, (W i).MemOpen z) → (pentagonEdgeHalfPlane v hv 0).MemPos z) ∧
        ((pentagonEdgeHalfPlane v hv 1).MemPos (xk 2 (fun _ => true)) ↔
          ¬ (pentagonEdgeHalfPlane v hv 2).MemPos (xk 2 (fun _ => true)))
      else
        (∀ k m, (pentagonDiag02HalfPlane v hv).MemPos (xk k m)) ∧
        (∀ z, (∀ i : Fin 5, (W i).MemOpen z) → (pentagonDiag02HalfPlane v hv).MemPos z) ∧
        ((pentagonEdgeHalfPlane v hv 0).MemPos (xk 1 (fun _ => true)) ↔
          ¬ (pentagonEdgeHalfPlane v hv 1).MemPos (xk 1 (fun _ => true))))
    (h_case :
      (∃ rstar : Fin 5, rstar ≠ 0 ∧ (isRegime2 = true → rstar ≠ 1) ∧
        (∀ k m, ¬ (pentagonEdgeHalfPlane v hv rstar).MemPos (xk k m)) ∧
        (∀ z, (∀ i : Fin 5, (W i).MemOpen z) → ¬ (pentagonEdgeHalfPlane v hv rstar).MemPos z)) ∨
      (∀ i r : Fin 5, (pentagonEdgeHalfPlane v hv r).MemPos (W i).y)) :
    False := by
  let H : Fin 5 → OpenHalfPlane := pentagonEdgeHalfPlane v hv
  let H02 : OpenHalfPlane := pentagonDiag02HalfPlane v hv
  let xk32 : Fin 5 → Fin 32 → ℝ × ℝ := fun k m => xk k (maskOfFin32 m)
  let R11111 : ℝ × ℝ → Prop := fun z => ∀ i : Fin 5, (W i).MemOpen z
  have hxk_R11111 : ∀ k, R11111 (xk32 k 31) := by
    intro k i
    dsimp [xk32]
    rw [maskOfFin32_31]
    have hi := hxk_mask k (fun _ => true) i
    simpa using hi
  have h_inc := fun z => pentagon_halfplane_inclusions_planar v hv z
  refine no_ten_point_shattered_master_masked isRegime2
    (fun r z => (H r).MemPos z) (fun z => H02.MemPos z) R11111
    (fun m p => RealizesWedgeMask W (maskOfFin32 m) p)
    (fun z => (h_inc z).2.1)
    (fun z => (h_inc z).2.2.1)
    (fun z => (h_inc z).2.2.2.1)
    (fun z => (h_inc z).2.2.2.2.1)
    (fun z => (h_inc z).2.2.2.2.2.1)
    (fun z => (h_inc z).2.2.2.2.2.2)
    xk32 hxk_R11111
    (fun k m => hxk_mask k (maskOfFin32 m))
    (fun m => h_nonfront3 (maskOfFin32 m))
    (fun m => h_nonfront4 (maskOfFin32 m))
    (fun m => h_nonfront2 (maskOfFin32 m))
    (by dsimp [xk32]; rw [maskOfFin32_31]; exact h_xor3)
    (by dsimp [xk32]; rw [maskOfFin32_31]; exact h_xor4)
    ?_ ?_ ?_
  · intro r fam hfam_mask hfam z hz
    apply thm1_part2_general_halfplane h_thm1 W (H r)
    · intro b
      refine ⟨fam (fin32OfMask b), hfam (fin32OfMask b), ?_⟩
      simpa [maskOfFin32_fin32OfMask b] using hfam_mask (fin32OfMask b)
    · exact hz
  · cases isRegime2
    · rw [if_pos rfl] at h_regime ⊢
      rcases h_regime with ⟨h0_xk, h0_R, h_xor2⟩
      refine ⟨fun k m => h0_xk k (maskOfFin32 m), h0_R, ?_⟩
      dsimp [xk32]; rw [maskOfFin32_31]; exact h_xor2
    · rw [if_neg (by decide)] at h_regime ⊢
      rcases h_regime with ⟨h02_xk, h02_R, h_xor1⟩
      refine ⟨fun k m => h02_xk k (maskOfFin32 m), h02_R, ?_⟩
      dsimp [xk32]; rw [maskOfFin32_31]; exact h_xor1
  · rcases h_case with ⟨rstar, hr0, hr1, hr_xk, hr_R⟩ | h_apices
    · left
      exact ⟨rstar, hr0, hr1, fun k m => hr_xk k (maskOfFin32 m), hr_R⟩
    · right
      intro a b fam hfam_mask hfam za zb hza hzb hna hnb
      obtain ⟨za', hza'_neg, hza'_open⟩ := exists_memNeg_in_R11111 W (H a) za hza hna
      obtain ⟨zb', hzb'_neg, hzb'_open⟩ := exists_memNeg_in_R11111 W (H b) zb hzb hnb
      apply five_wedges_two_halfplanes_general h_thm1 h_caseA_orig (H a) (H b) W
        (fun i => ⟨h_apices i a, h_apices i b⟩)
        ⟨za', hza'_neg, hza'_open⟩ ⟨zb', hzb'_neg, hzb'_open⟩
      intro m
      refine ⟨fam (fin32OfMask m), hfam (fin32OfMask m), ?_⟩
      simpa [maskOfFin32_fin32OfMask m] using hfam_mask (fin32OfMask m)

end
