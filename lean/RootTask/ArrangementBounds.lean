import Mathlib
import RootTask.Defs
import RootTask.UnconditionalBridge
import RootTask.SixWedges

open scoped Classical BigOperators
open Finset

noncomputable section

namespace ArrangementBounds

/-!
# Three Half-Planes and Two Half-Planes + Three Wedges Obstructions

Proves the two low-dimensional arrangement bounds needed for `Sec2To5Interface`:
1. `three_halfplanes_not_all_8`: Three open half-planes in `ℝ²` cannot realize all `8` strict bitmasks.
2. `two_hp_three_wedges_not_all_32`: Two open half-planes and three open convex wedges in `ℝ²`
   cannot realize all `32` strict bitmasks (via perturbation to non-parallel normals + `31 < 32`
   component-counting using `SixWedges.comps_remove_arc`).
-/

/-! ## Part 1: Three Half-Planes (`< 8` Bitmasks) -/

theorem three_halfplanes_not_all_8 (H : Fin 3 → OpenHalfPlane) :
    ¬ (∀ m : Fin 3 → Bool, ∃ p : ℝ × ℝ, ∀ i : Fin 3,
      if m i then (H i).MemPos p else (H i).MemNeg p) := by
  intro h_all
  let a : Fin 3 → ℝ := fun i => (H i).n.1
  let b : Fin 3 → ℝ := fun i => (H i).n.2
  let c : Fin 3 → ℝ := fun i => (H i).c
  let evalH : Fin 3 → ℝ × ℝ → ℝ := fun i p => a i * p.1 + b i * p.2 + c i
  let d0 : ℝ := a 1 * b 2 - a 2 * b 1
  let d1 : ℝ := a 2 * b 0 - a 0 * b 2
  let d2 : ℝ := a 0 * b 1 - a 1 * b 0
  let det3 : ℝ := d0 * c 0 + d1 * c 1 + d2 * c 2
  have hlin_id : ∀ p : ℝ × ℝ,
      d0 * evalH 0 p + d1 * evalH 1 p + d2 * evalH 2 p = det3 := by
    intro p; dsimp [d0, d1, d2, det3, evalH]; ring
  by_cases hdet : det3 ≠ 0
  · let u : Fin 3 → ℝ := ![d0 / det3, d1 / det3, d2 / det3]
    have hu_id : ∀ p : ℝ × ℝ,
        u 0 * evalH 0 p + u 1 * evalH 1 p + u 2 * evalH 2 p = 1 := by
      intro p
      have h1 := hlin_id p
      dsimp [u]
      field_simp [hdet]
      linarith
    let m : Fin 3 → Bool := fun i => decide (u i < 0)
    obtain ⟨p, hp⟩ := h_all m
    have hterm : ∀ i : Fin 3, u i * evalH i p ≤ 0 := by
      intro i
      have hi := hp i
      by_cases hui : u i < 0
      · have hmi : m i = true := decide_eq_true hui
        simp only [hmi, ↓reduceIte] at hi
        exact le_of_lt (mul_neg_of_neg_of_pos hui hi)
      · have hmi : m i = false := decide_eq_false hui
        simp only [hmi, Bool.false_eq_true, ↓reduceIte] at hi
        exact mul_nonpos_of_nonneg_of_nonpos (not_lt.mp hui) (le_of_lt hi)
    linarith [hu_id p, hterm 0, hterm 1, hterm 2]
  · have hdet0 : det3 = 0 := not_ne_iff.mp hdet
    by_cases hds : d0 ≠ 0 ∨ d1 ≠ 0 ∨ d2 ≠ 0
    · let d : Fin 3 → ℝ := ![d0, d1, d2]
      let m : Fin 3 → Bool := fun i => decide (0 < d i)
      obtain ⟨p, hp⟩ := h_all m
      have hterm_nn : ∀ i : Fin 3, 0 ≤ d i * evalH i p := by
        intro i
        have hi := hp i
        by_cases hdi : 0 < d i
        · have hmi : m i = true := decide_eq_true hdi
          simp only [hmi, ↓reduceIte] at hi
          exact le_of_lt (mul_pos hdi hi)
        · have hmi : m i = false := decide_eq_false hdi
          simp only [hmi, Bool.false_eq_true, ↓reduceIte] at hi
          exact mul_nonneg_of_nonpos_of_nonpos (not_lt.mp hdi) (le_of_lt hi)
      have hterm_pos : ∃ i : Fin 3, 0 < d i * evalH i p := by
        have hnz : ∃ i : Fin 3, d i ≠ 0 := by
          rcases hds with h | h | h
          · exact ⟨0, h⟩
          · exact ⟨1, h⟩
          · exact ⟨2, h⟩
        obtain ⟨i, hdi⟩ := hnz
        refine ⟨i, ?_⟩
        have hi := hp i
        rcases lt_or_gt_of_ne hdi with hlt | hgt
        · have hmi : m i = false := decide_eq_false (not_lt.mpr (le_of_lt hlt))
          simp only [hmi, Bool.false_eq_true, ↓reduceIte] at hi
          exact mul_pos_of_neg_of_neg hlt hi
        · have hmi : m i = true := decide_eq_true hgt
          simp only [hmi, ↓reduceIte] at hi
          exact mul_pos hgt hi
      obtain ⟨i, hi_pos⟩ := hterm_pos
      have hn0 := hterm_nn 0
      have hn1 := hterm_nn 1
      have hn2 := hterm_nn 2
      have hsum_pos : 0 < d 0 * evalH 0 p + d 1 * evalH 1 p + d 2 * evalH 2 p := by
        fin_cases i <;> (dsimp at hi_pos; linarith)
      have h0 : d 0 * evalH 0 p + d 1 * evalH 1 p + d 2 * evalH 2 p = 0 := by
        dsimp [d]; rw [hlin_id p, hdet0]
      linarith
    · push Not at hds
      have hd2 : d2 = 0 := hds.2.2
      have hcol : a 0 * b 1 - a 1 * b 0 = 0 := hd2
      obtain ⟨α0, α1, hα_nz, hα_a, hα_b⟩ :
          ∃ α0 α1 : ℝ, (α0 ≠ 0 ∨ α1 ≠ 0) ∧ α0 * a 0 + α1 * a 1 = 0 ∧ α0 * b 0 + α1 * b 1 = 0 := by
        by_cases ha0 : a 0 ≠ 0
        · refine ⟨a 1, -a 0, Or.inr (neg_ne_zero.mpr ha0), by ring, ?_⟩
          linarith [hcol]
        · have hb0 : b 0 ≠ 0 := ((H 0).hn).resolve_left ha0
          refine ⟨b 1, -b 0, Or.inr (neg_ne_zero.mpr hb0), ?_, by ring⟩
          linarith [hcol]
      let K : ℝ := α0 * c 0 + α1 * c 1
      have hconst : ∀ p : ℝ × ℝ, α0 * evalH 0 p + α1 * evalH 1 p = K := by
        intro p
        calc α0 * evalH 0 p + α1 * evalH 1 p
            = (α0 * a 0 + α1 * a 1) * p.1 + (α0 * b 0 + α1 * b 1) * p.2 + (α0 * c 0 + α1 * c 1) := by
                dsimp [evalH]; ring
          _ = K := by rw [hα_a, hα_b, zero_mul, zero_mul, zero_add, zero_add]
      by_cases hK : 0 ≤ K
      · let m : Fin 3 → Bool := ![decide (α0 < 0), decide (α1 < 0), true]
        obtain ⟨p, hp⟩ := h_all m
        have h0_neg : α0 * evalH 0 p ≤ 0 := by
          have hi := hp 0
          by_cases hα : α0 < 0
          · simp only [m, Matrix.cons_val_zero, decide_eq_true hα, ↓reduceIte] at hi
            exact le_of_lt (mul_neg_of_neg_of_pos hα hi)
          · simp only [m, Matrix.cons_val_zero, decide_eq_false hα, Bool.false_eq_true, ↓reduceIte] at hi
            exact mul_nonpos_of_nonneg_of_nonpos (not_lt.mp hα) (le_of_lt hi)
        have h1_neg : α1 * evalH 1 p ≤ 0 := by
          have hi := hp 1
          by_cases hα : α1 < 0
          · simp only [m, Matrix.cons_val_one, Matrix.cons_val_zero, decide_eq_true hα, ↓reduceIte] at hi
            exact le_of_lt (mul_neg_of_neg_of_pos hα hi)
          · simp only [m, Matrix.cons_val_one, Matrix.cons_val_zero, decide_eq_false hα, Bool.false_eq_true, ↓reduceIte] at hi
            exact mul_nonpos_of_nonneg_of_nonpos (not_lt.mp hα) (le_of_lt hi)
        have h_lt : α0 * evalH 0 p + α1 * evalH 1 p < 0 := by
          rcases hα_nz with h0nz | h1nz
          · have h0_lt : α0 * evalH 0 p < 0 := by
              have hi := hp 0
              rcases lt_or_gt_of_ne h0nz with hlt | hgt
              · simp only [m, Matrix.cons_val_zero, decide_eq_true hlt, ↓reduceIte] at hi
                exact mul_neg_of_neg_of_pos hlt hi
              · simp only [m, Matrix.cons_val_zero, decide_eq_false (not_lt.mpr (le_of_lt hgt)), Bool.false_eq_true, ↓reduceIte] at hi
                exact mul_neg_of_pos_of_neg hgt hi
            linarith
          · have h1_lt : α1 * evalH 1 p < 0 := by
              have hi := hp 1
              rcases lt_or_gt_of_ne h1nz with hlt | hgt
              · simp only [m, Matrix.cons_val_one, Matrix.cons_val_zero, decide_eq_true hlt, ↓reduceIte] at hi
                exact mul_neg_of_neg_of_pos hlt hi
              · simp only [m, Matrix.cons_val_one, Matrix.cons_val_zero, decide_eq_false (not_lt.mpr (le_of_lt hgt)), Bool.false_eq_true, ↓reduceIte] at hi
                exact mul_neg_of_pos_of_neg hgt hi
            linarith
        linarith [hconst p]
      · have hK_neg : K < 0 := not_le.mp hK
        let m : Fin 3 → Bool := ![decide (0 < α0), decide (0 < α1), true]
        obtain ⟨p, hp⟩ := h_all m
        have h0_nn : 0 ≤ α0 * evalH 0 p := by
          have hi := hp 0
          by_cases hα : 0 < α0
          · simp only [m, Matrix.cons_val_zero, decide_eq_true hα, ↓reduceIte] at hi
            exact le_of_lt (mul_pos hα hi)
          · simp only [m, Matrix.cons_val_zero, decide_eq_false hα, Bool.false_eq_true, ↓reduceIte] at hi
            exact mul_nonneg_of_nonpos_of_nonpos (not_lt.mp hα) (le_of_lt hi)
        have h1_nn : 0 ≤ α1 * evalH 1 p := by
          have hi := hp 1
          by_cases hα : 0 < α1
          · simp only [m, Matrix.cons_val_one, Matrix.cons_val_zero, decide_eq_true hα, ↓reduceIte] at hi
            exact le_of_lt (mul_pos hα hi)
          · simp only [m, Matrix.cons_val_one, Matrix.cons_val_zero, decide_eq_false hα, Bool.false_eq_true, ↓reduceIte] at hi
            exact mul_nonneg_of_nonpos_of_nonpos (not_lt.mp hα) (le_of_lt hi)
        linarith [hconst p]

/-! ## Part 2: Two Half-Planes + Three Wedges (`< 32` Bitmasks) -/

private def bdHP (h : OpenHalfPlane) : Set (ℝ × ℝ) :=
  {p | h.n.1 * p.1 + h.n.2 * p.2 + h.c = 0}

private lemma bdHP_isClosed (h : OpenHalfPlane) : IsClosed (bdHP h) :=
  isClosed_eq (by fun_prop) continuous_const

private lemma isOpen_memPos (h : OpenHalfPlane) : IsOpen {p : ℝ × ℝ | h.MemPos p} :=
  isOpen_lt continuous_const (by fun_prop)

private lemma isOpen_memNeg (h : OpenHalfPlane) : IsOpen {p : ℝ × ℝ | h.MemNeg p} :=
  isOpen_lt (by fun_prop) continuous_const

private lemma memPos_convex (h : OpenHalfPlane) : Convex ℝ {p : ℝ × ℝ | h.MemPos p} := by
  intro x hx y hy a b ha hb hab
  change 0 < h.n.1 * (a • x + b • y).1 + h.n.2 * (a • x + b • y).2 + h.c
  have hid : h.n.1 * (a • x + b • y).1 + h.n.2 * (a • x + b • y).2 + h.c =
      a * (h.n.1 * x.1 + h.n.2 * x.2 + h.c) +
      b * (h.n.1 * y.1 + h.n.2 * y.2 + h.c) := by
    simp only [Prod.smul_fst, Prod.smul_snd, Prod.fst_add, Prod.snd_add, smul_eq_mul]
    linear_combination -h.c * hab
  rw [hid]
  rcases eq_or_lt_of_le ha with rfl | ha'
  · simp only [zero_mul, zero_add] at hab ⊢; rw [hab, one_mul]; exact hy
  · have hb_nn : 0 ≤ b * (h.n.1 * y.1 + h.n.2 * y.2 + h.c) := mul_nonneg hb (le_of_lt hy)
    linarith [mul_pos ha' hx]

private lemma memNeg_convex (h : OpenHalfPlane) : Convex ℝ {p : ℝ × ℝ | h.MemNeg p} := by
  intro x hx y hy a b ha hb hab
  change h.n.1 * (a • x + b • y).1 + h.n.2 * (a • x + b • y).2 + h.c < 0
  have hid : h.n.1 * (a • x + b • y).1 + h.n.2 * (a • x + b • y).2 + h.c =
      a * (h.n.1 * x.1 + h.n.2 * x.2 + h.c) +
      b * (h.n.1 * y.1 + h.n.2 * y.2 + h.c) := by
    simp only [Prod.smul_fst, Prod.smul_snd, Prod.fst_add, Prod.snd_add, smul_eq_mul]
    linear_combination -h.c * hab
  rw [hid]
  rcases eq_or_lt_of_le ha with rfl | ha'
  · simp only [zero_mul, zero_add] at hab ⊢; rw [hab, one_mul]; exact hy
  · have hb_np : b * (h.n.1 * y.1 + h.n.2 * y.2 + h.c) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hb (le_of_lt hy)
    linarith [mul_neg_of_pos_of_neg ha' hx]

private def lineParam (h : OpenHalfPlane) (s : ℝ) : ℝ × ℝ :=
  let r2 := h.n.1 ^ 2 + h.n.2 ^ 2
  (-h.c * h.n.1 / r2 - s * h.n.2, -h.c * h.n.2 / r2 + s * h.n.1)

private lemma r2_pos (h : OpenHalfPlane) : 0 < h.n.1 ^ 2 + h.n.2 ^ 2 := by
  rcases h.hn with h1 | h2
  · exact add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero h1) (sq_nonneg _)
  · exact add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_ne_zero h2)

private lemma lineParam_continuous (h : OpenHalfPlane) : Continuous (lineParam h) := by
  unfold lineParam; fun_prop

private lemma lineParam_inv_left (h : OpenHalfPlane) (s : ℝ) :
    (-h.n.2 * (lineParam h s).1 + h.n.1 * (lineParam h s).2) / (h.n.1 ^ 2 + h.n.2 ^ 2) = s := by
  have hr2 : h.n.1 ^ 2 + h.n.2 ^ 2 ≠ 0 := ne_of_gt (r2_pos h)
  dsimp [lineParam]
  field_simp [hr2]
  ring

private lemma lineParam_injective (h : OpenHalfPlane) : Function.Injective (lineParam h) := by
  intro s₁ s₂ heq
  have h1 := lineParam_inv_left h s₁
  have h2 := lineParam_inv_left h s₂
  rw [heq] at h1
  linarith

private lemma lineParam_mem_bdHP (h : OpenHalfPlane) (s : ℝ) : lineParam h s ∈ bdHP h := by
  have hr2 : h.n.1 ^ 2 + h.n.2 ^ 2 ≠ 0 := ne_of_gt (r2_pos h)
  dsimp [bdHP, lineParam]
  field_simp [hr2]
  ring

private lemma lineParam_range (h : OpenHalfPlane) : Set.range (lineParam h) = bdHP h := by
  ext p; constructor
  · rintro ⟨s, rfl⟩; exact lineParam_mem_bdHP h s
  · intro hp
    have hr2 : h.n.1 ^ 2 + h.n.2 ^ 2 ≠ 0 := ne_of_gt (r2_pos h)
    let s := (-h.n.2 * p.1 + h.n.1 * p.2) / (h.n.1 ^ 2 + h.n.2 ^ 2)
    refine ⟨s, ?_⟩
    change h.n.1 * p.1 + h.n.2 * p.2 + h.c = 0 at hp
    ext
    · dsimp [lineParam, s]; field_simp [hr2]; linear_combination -h.n.1 * hp
    · dsimp [lineParam, s]; field_simp [hr2]; linear_combination -h.n.2 * hp

private lemma lineParam_image_isClosed (h : OpenHalfPlane) {S : Set ℝ} (hS : IsClosed S) :
    IsClosed (lineParam h '' S) := by
  let inv : ℝ × ℝ → ℝ := fun p => (-h.n.2 * p.1 + h.n.1 * p.2) / (h.n.1 ^ 2 + h.n.2 ^ 2)
  have hinv_cont : Continuous inv := by dsimp [inv]; fun_prop
  have himg : lineParam h '' S = bdHP h ∩ inv ⁻¹' S := by
    ext p; constructor
    · rintro ⟨s, hs, rfl⟩
      refine ⟨lineParam_mem_bdHP h s, ?_⟩
      change inv (lineParam h s) ∈ S
      dsimp [inv]; rw [lineParam_inv_left h s]; exact hs
    · rintro ⟨hp, hinv⟩
      rw [← lineParam_range h] at hp
      obtain ⟨s, rfl⟩ := hp
      refine ⟨s, ?_, rfl⟩
      change inv (lineParam h s) ∈ S at hinv
      dsimp [inv] at hinv; rw [lineParam_inv_left h s] at hinv; exact hinv
  rw [himg]
  exact (bdHP_isClosed h).inter (hS.preimage hinv_cont)

private lemma ball_shift_mem' {z d : ℝ × ℝ} {δ : ℝ} (hδ : 0 < δ) :
    ∃ ε > 0, (z.1 + ε * d.1, z.2 + ε * d.2) ∈ Metric.ball z δ := by
  let B := |d.1| + |d.2| + 1
  have hB : 0 < B := by positivity
  refine ⟨δ / (2 * B), by positivity, ?_⟩
  rw [Metric.mem_ball, Prod.dist_eq]
  have he : 0 < δ / (2 * B) := by positivity
  have h1 : dist (z.1 + (δ / (2 * B)) * d.1) z.1 < δ := by
    rw [Real.dist_eq, show z.1 + (δ / (2 * B)) * d.1 - z.1 = (δ / (2 * B)) * d.1 by ring,
      abs_mul, abs_of_pos he]
    have hle : |d.1| < B := by have := abs_nonneg d.2; dsimp [B]; linarith
    calc (δ / (2 * B)) * |d.1| ≤ (δ / (2 * B)) * B := mul_le_mul_of_nonneg_left (le_of_lt hle) (le_of_lt he)
      _ = δ / 2 := by field_simp [ne_of_gt hB]
      _ < δ := by linarith
  have h2 : dist (z.2 + (δ / (2 * B)) * d.2) z.2 < δ := by
    rw [Real.dist_eq, show z.2 + (δ / (2 * B)) * d.2 - z.2 = (δ / (2 * B)) * d.2 by ring,
      abs_mul, abs_of_pos he]
    have hle : |d.2| < B := by have := abs_nonneg d.1; dsimp [B]; linarith
    calc (δ / (2 * B)) * |d.2| ≤ (δ / (2 * B)) * B := mul_le_mul_of_nonneg_left (le_of_lt hle) (le_of_lt he)
      _ = δ / 2 := by field_simp [ne_of_gt hB]
      _ < δ := by linarith
  exact max_lt h1 h2

private lemma bdHP_ball_memPos_ne (h : OpenHalfPlane) {z : ℝ × ℝ} (hz : z ∈ bdHP h)
    {δ : ℝ} (hδ : 0 < δ) : (Metric.ball z δ ∩ {p | h.MemPos p}).Nonempty := by
  obtain ⟨ε, hε, hball⟩ := ball_shift_mem' (z := z) (d := h.n) hδ
  have hr2 := r2_pos h
  change h.n.1 * z.1 + h.n.2 * z.2 + h.c = 0 at hz
  have hpos : h.MemPos (z.1 + ε * h.n.1, z.2 + ε * h.n.2) := by
    change 0 < h.n.1 * (z.1 + ε * h.n.1) + h.n.2 * (z.2 + ε * h.n.2) + h.c
    have hid : h.n.1 * (z.1 + ε * h.n.1) + h.n.2 * (z.2 + ε * h.n.2) + h.c =
        (h.n.1 * z.1 + h.n.2 * z.2 + h.c) + ε * (h.n.1 ^ 2 + h.n.2 ^ 2) := by ring
    rw [hid, hz, zero_add]
    exact mul_pos hε hr2
  exact ⟨_, hball, hpos⟩

private lemma bdHP_ball_memNeg_ne (h : OpenHalfPlane) {z : ℝ × ℝ} (hz : z ∈ bdHP h)
    {δ : ℝ} (hδ : 0 < δ) : (Metric.ball z δ ∩ {p | h.MemNeg p}).Nonempty := by
  obtain ⟨ε, hε, hball⟩ := ball_shift_mem' (z := z) (d := (-h.n.1, -h.n.2)) hδ
  have hr2 := r2_pos h
  change h.n.1 * z.1 + h.n.2 * z.2 + h.c = 0 at hz
  have hneg : h.MemNeg (z.1 + ε * (-h.n.1), z.2 + ε * (-h.n.2)) := by
    change h.n.1 * (z.1 + ε * (-h.n.1)) + h.n.2 * (z.2 + ε * (-h.n.2)) + h.c < 0
    have hid : h.n.1 * (z.1 + ε * (-h.n.1)) + h.n.2 * (z.2 + ε * (-h.n.2)) + h.c =
        (h.n.1 * z.1 + h.n.2 * z.2 + h.c) - ε * (h.n.1 ^ 2 + h.n.2 ^ 2) := by ring
    rw [hid, hz, zero_sub]
    exact neg_lt_zero.mpr (mul_pos hε hr2)
  exact ⟨_, hball, hneg⟩

private lemma bdWedge_ball_memOpen_ne' (W : OpenWedge) {z : ℝ × ℝ} (hz : z ∈ SixWedges.bdWedge W)
    {δ : ℝ} (hδ : 0 < δ) : (Metric.ball z δ ∩ {p | W.MemOpen p}).Nonempty := by
  let d : ℝ × ℝ := ((SixWedges.dir1 W).1 + (SixWedges.dir2 W).1,
                     (SixWedges.dir1 W).2 + (SixWedges.dir2 W).2)
  obtain ⟨ε, hε, hball⟩ := ball_shift_mem' (z := z) (d := d) hδ
  have hcl := (SixWedges.bdWedge_iff_closure_eq_zero W z).mp hz |>.1
  have hnd := W.h_nondeg
  have ho1 : 0 < W.u₁.1 * ((z.1 + ε * d.1) - W.y.1) + W.u₁.2 * ((z.2 + ε * d.2) - W.y.2) := by
    have e : W.u₁.1 * ((z.1 + ε * d.1) - W.y.1) + W.u₁.2 * ((z.2 + ε * d.2) - W.y.2) =
        (W.u₁.1 * (z.1 - W.y.1) + W.u₁.2 * (z.2 - W.y.2)) +
        ε * (W.u₁.1 * W.u₂.2 - W.u₁.2 * W.u₂.1) := by
      dsimp [d, SixWedges.dir1, SixWedges.dir2]; ring
    rw [e]; nlinarith [hcl.1]
  have ho2 : 0 < W.u₂.1 * ((z.1 + ε * d.1) - W.y.1) + W.u₂.2 * ((z.2 + ε * d.2) - W.y.2) := by
    have e : W.u₂.1 * ((z.1 + ε * d.1) - W.y.1) + W.u₂.2 * ((z.2 + ε * d.2) - W.y.2) =
        (W.u₂.1 * (z.1 - W.y.1) + W.u₂.2 * (z.2 - W.y.2)) +
        ε * (W.u₁.1 * W.u₂.2 - W.u₁.2 * W.u₂.1) := by
      dsimp [d, SixWedges.dir1, SixWedges.dir2]; ring
    rw [e]; nlinarith [hcl.2]
  exact ⟨_, hball, ho1, ho2⟩

private lemma bdWedge_ball_memExt_ne' (W : OpenWedge) {z : ℝ × ℝ} (hz : z ∈ SixWedges.bdWedge W)
    {δ : ℝ} (hδ : 0 < δ) : (Metric.ball z δ ∩ {p | W.MemExt p}).Nonempty := by
  have hnd := W.h_nondeg
  rcases (SixWedges.bdWedge_iff_closure_eq_zero W z).mp hz |>.2 with hz1 | hz2
  · let d : ℝ × ℝ := (-(SixWedges.dir2 W).1, -(SixWedges.dir2 W).2)
    obtain ⟨ε, hε, hball⟩ := ball_shift_mem' (z := z) (d := d) hδ
    have hext : W.u₁.1 * ((z.1 + ε * d.1) - W.y.1) + W.u₁.2 * ((z.2 + ε * d.2) - W.y.2) < 0 := by
      have e : W.u₁.1 * ((z.1 + ε * d.1) - W.y.1) + W.u₁.2 * ((z.2 + ε * d.2) - W.y.2) =
          (W.u₁.1 * (z.1 - W.y.1) + W.u₁.2 * (z.2 - W.y.2)) -
          ε * (W.u₁.1 * W.u₂.2 - W.u₁.2 * W.u₂.1) := by
        dsimp [d, SixWedges.dir2]; ring
      rw [e, hz1]; nlinarith
    exact ⟨_, hball, Or.inl hext⟩
  · let d : ℝ × ℝ := (-(SixWedges.dir1 W).1, -(SixWedges.dir1 W).2)
    obtain ⟨ε, hε, hball⟩ := ball_shift_mem' (z := z) (d := d) hδ
    have hext : W.u₂.1 * ((z.1 + ε * d.1) - W.y.1) + W.u₂.2 * ((z.2 + ε * d.2) - W.y.2) < 0 := by
      have e : W.u₂.1 * ((z.1 + ε * d.1) - W.y.1) + W.u₂.2 * ((z.2 + ε * d.2) - W.y.2) =
          (W.u₂.1 * (z.1 - W.y.1) + W.u₂.2 * (z.2 - W.y.2)) -
          ε * (W.u₁.1 * W.u₂.2 - W.u₁.2 * W.u₂.1) := by
        dsimp [d, SixWedges.dir1]; ring
      rw [e, hz2]; nlinarith
    exact ⟨_, hball, Or.inr hext⟩

private lemma halfspace_lt_convex' (u y : ℝ × ℝ) :
    Convex ℝ {p : ℝ × ℝ | u.1 * (p.1 - y.1) + u.2 * (p.2 - y.2) < 0} := by
  intro p hp q hq a b ha hb hab
  change u.1 * ((a • p + b • q).1 - y.1) + u.2 * ((a • p + b • q).2 - y.2) < 0
  have e : u.1 * ((a • p + b • q).1 - y.1) + u.2 * ((a • p + b • q).2 - y.2) =
      a * (u.1 * (p.1 - y.1) + u.2 * (p.2 - y.2)) +
      b * (u.1 * (q.1 - y.1) + u.2 * (q.2 - y.2)) := by
    simp only [Prod.smul_fst, Prod.smul_snd, Prod.fst_add, Prod.snd_add, smul_eq_mul]
    linear_combination (u.1 * y.1 + u.2 * y.2) * hab
  rw [e]
  rcases eq_or_lt_of_le ha with rfl | ha'
  · simp only [zero_mul, zero_add] at hab ⊢; rw [hab, one_mul]; exact hq
  · have hb_np : b * (u.1 * (q.1 - y.1) + u.2 * (q.2 - y.2)) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hb (le_of_lt hq)
    linarith [mul_neg_of_pos_of_neg ha' hp]

private lemma seg_pairwise_disjoint' : ∀ (xs : List ℝ) {a b : ℕ}
    (ha : a < xs.length + 1) (hb : b < xs.length + 1),
    a ≠ b → Disjoint (SixWedges.seg xs ⟨a, ha⟩) (SixWedges.seg xs ⟨b, hb⟩)
  | [], a, b, ha, hb, hab => by
      simp at ha hb
      exact False.elim (hab (by omega))
  | x :: tl, 0, 0, _, _, hab => False.elim (hab rfl)
  | x :: tl, 0, b' + 1, _, _, _ => Set.disjoint_left.mpr fun s hs1 hs2 => by
      change s < x at hs1
      exact absurd (Set.mem_Ioi.mp hs2.2) (not_lt.mpr (le_of_lt hs1))
  | x :: tl, a' + 1, 0, _, _, _ => Set.disjoint_left.mpr fun s hs1 hs2 => by
      change s < x at hs2
      exact absurd (Set.mem_Ioi.mp hs1.2) (not_lt.mpr (le_of_lt hs2))
  | x :: tl, a' + 1, b' + 1, ha, hb, hab => by
      have ha' : a' < tl.length + 1 := by simp at ha; omega
      have hb' : b' < tl.length + 1 := by simp at hb; omega
      exact Set.disjoint_left.mpr fun s hs1 hs2 =>
        Set.disjoint_left.mp (seg_pairwise_disjoint' tl ha' hb' (by omega)) hs1.1 hs2.1

private lemma add_line_comps_bound (h : OpenHalfPlane) (K : Set (ℝ × ℝ)) (hK : IsClosed K)
    (hfin : (bdHP h ∩ K).Finite) :
    (SixWedges.Comps ((Set.univ : Set (ℝ × ℝ)) \ (K ∪ bdHP h))).encard ≤
      (SixWedges.Comps ((Set.univ : Set (ℝ × ℝ)) \ K)).encard + ((bdHP h ∩ K).ncard + 1 : ℕ) := by
  let U₀ : Set (ℝ × ℝ) := Set.univ \ K
  have hU₀_open : IsOpen U₀ := isOpen_univ.sdiff hK
  let P_set : Set (ℝ × ℝ) := bdHP h ∩ K
  let P_param : Set ℝ := (lineParam h) ⁻¹' P_set
  have hP_param_fin : P_param.Finite := hfin.preimage (lineParam_injective h).injOn
  let xs : List ℝ := hP_param_fin.toFinset.sort (· ≤ ·)
  have hxs_sorted : xs.SortedLT := Finset.sortedLT_sort _
  have hxs_iff : ∀ s : ℝ, s ∈ xs ↔ lineParam h s ∈ P_set := fun s => by
    simp [xs, P_param]
  let α : Fin (xs.length + 1) → Set (ℝ × ℝ) := fun i => lineParam h '' SixWedges.seg xs i
  let U_step : ℕ → Set (ℝ × ℝ) := fun m =>
    U₀ \ ⋃ (i : Fin (xs.length + 1)) (_ : i.val < m), α i
  have hU_step_open : ∀ m, IsOpen (U_step m) := by
    intro m
    let I : Finset (Fin (xs.length + 1)) := Finset.univ.filter (fun i => i.val < m)
    let S_cl : Set ℝ := ⋃ i ∈ (I : Set (Fin (xs.length + 1))), closure (SixWedges.seg xs i)
    have hS_cl : IsClosed S_cl :=
      I.finite_toSet.isClosed_biUnion fun _ _ => isClosed_closure
    let K_cl : Set (ℝ × ℝ) := lineParam h '' S_cl
    have hK_cl : IsClosed K_cl := lineParam_image_isClosed h hS_cl
    have hEq : U_step m = U₀ \ K_cl := by
      ext p; constructor
      · rintro ⟨hpU₀, hp_not⟩
        refine ⟨hpU₀, ?_⟩
        rintro ⟨s, hs, rfl⟩
        rw [Set.mem_iUnion₂] at hs
        rcases hs with ⟨i, hiI, hsi⟩
        rcases SixWedges.closure_seg_subset xs i hsi with hseg | hmem_xs
        · exact hp_not (Set.mem_iUnion₂.mpr ⟨i, (Finset.mem_filter.mp (Finset.mem_coe.mp hiI)).2,
            ⟨s, hseg, rfl⟩⟩)
        · exact hpU₀.2 ((hxs_iff s).mp hmem_xs).2
      · rintro ⟨hpU₀, hp_not⟩
        refine ⟨hpU₀, fun hmem => hp_not ?_⟩
        rw [Set.mem_iUnion₂] at hmem
        rcases hmem with ⟨i, him, ⟨s, hsi, rfl⟩⟩
        refine ⟨s, Set.mem_iUnion₂.mpr ⟨i, ?_, subset_closure hsi⟩, rfl⟩
        exact Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ i, him⟩)
    rw [hEq]
    exact hU₀_open.sdiff hK_cl
  have h_step : ∀ m : ℕ, m ≤ xs.length + 1 →
      (SixWedges.Comps (U_step m)).encard ≤ (SixWedges.Comps U₀).encard + (m : ℕ∞) := by
    intro m
    induction m with
    | zero =>
      intro _
      have heq : U_step 0 = U₀ := by ext p; simp [U_step]
      rw [heq]; simp
    | succ m ih =>
      intro hm
      have hm' : m < xs.length + 1 := hm
      let i : Fin (xs.length + 1) := ⟨m, hm'⟩
      have h_split : U_step (m + 1) = U_step m \ α i := by
        ext p; constructor
        · rintro ⟨hpU₀, hp_not⟩
          refine ⟨⟨hpU₀, fun hmem => hp_not ?_⟩, fun hmem => hp_not ?_⟩
          · rw [Set.mem_iUnion₂] at hmem ⊢
            rcases hmem with ⟨j, hj, hpj⟩
            exact ⟨j, Nat.lt_succ_of_lt hj, hpj⟩
          · exact Set.mem_iUnion₂.mpr ⟨i, Nat.lt_succ_self m, hmem⟩
        · rintro ⟨⟨hpU₀, hp_not⟩, hp_ni⟩
          refine ⟨hpU₀, fun hmem => ?_⟩
          rw [Set.mem_iUnion₂] at hmem
          rcases hmem with ⟨j, hj, hpj⟩
          rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj' | hj'
          · exact hp_not (Set.mem_iUnion₂.mpr ⟨j, hj', hpj⟩)
          · have hji : j = i := Fin.ext hj'
            rw [hji] at hpj
            exact hp_ni hpj
      have hi_sub : α i ⊆ U_step m := by
        rintro p ⟨s, hs, rfl⟩
        refine ⟨⟨trivial, fun hU => ?_⟩, fun hprev => ?_⟩
        · have hP : lineParam h s ∈ P_set := ⟨lineParam_mem_bdHP h s, hU⟩
          exact SixWedges.seg_disjoint_list xs hxs_sorted i hs ((hxs_iff s).mpr hP)
        · rw [Set.mem_iUnion₂] at hprev
          rcases hprev with ⟨j, hj, ⟨s', hs', heq⟩⟩
          have hij : j ≠ i := fun h0 => by rw [h0] at hj; exact Nat.lt_irrefl m hj
          have hs_eq : s' = s := lineParam_injective h heq
          subst hs_eq
          exact Set.disjoint_left.mp
            (seg_pairwise_disjoint' xs (hj.trans hm') hm' (fun h0 => hij (Fin.ext h0))) hs' hs
      -- Apply SixWedges.comps_remove_arc to α i ⊆ U_step m
      have hα_ne : (α i).Nonempty := (SixWedges.seg_nonempty xs hxs_sorted i).image _
      have hα_conn : IsPreconnected (α i) :=
        (SixWedges.seg_isPreconnected xs i).image (lineParam h) (lineParam_continuous h).continuousOn
      have hUi_open : IsOpen (U_step m \ α i) := h_split ▸ hU_step_open (m + 1)
      let K_other : Set (ℝ × ℝ) := lineParam h '' (SixWedges.seg xs i)ᶜ
      have hK_other : IsClosed K_other := lineParam_image_isClosed h (SixWedges.seg_isOpen xs i).isClosed_compl
      let V : Set (ℝ × ℝ) := U_step m ∩ K_otherᶜ
      have hV_open : IsOpen V := (hU_step_open m).inter hK_other.isOpen_compl
      have hz_mem_V : ∀ z ∈ α i, z ∈ V := by
        rintro z ⟨s, hs, rfl⟩
        refine ⟨hi_sub ⟨s, hs, rfl⟩, ?_⟩
        rintro ⟨s', hs', heq⟩
        rw [lineParam_injective h heq] at hs'
        exact hs' hs
      let r : (ℝ × ℝ) → ℝ := fun z =>
        if hz : z ∈ α i then (Metric.isOpen_iff.mp hV_open z (hz_mem_V z hz)).choose else 1
      have hr_pos : ∀ z ∈ α i, 0 < r z := fun z hz => by
        dsimp [r]; rw [dif_pos hz]
        exact (Metric.isOpen_iff.mp hV_open z (hz_mem_V z hz)).choose_spec.1
      have hball_V : ∀ z ∈ α i, Metric.ball z (r z) ⊆ V := fun z hz => by
        dsimp [r]; rw [dif_pos hz]
        exact (Metric.isOpen_iff.mp hV_open z (hz_mem_V z hz)).choose_spec.2
      have hball_sub : ∀ z ∈ α i, Metric.ball z (r z) ⊆ U_step m := fun z hz =>
        (hball_V z hz).trans Set.inter_subset_left
      let BL : (ℝ × ℝ) → Set (ℝ × ℝ) := fun z => Metric.ball z (r z) ∩ {p | h.MemPos p}
      let BR : (ℝ × ℝ) → Set (ℝ × ℝ) := fun z => Metric.ball z (r z) ∩ {p | h.MemNeg p}
      have hball_split : ∀ z ∈ α i, Metric.ball z (r z) \ α i = BL z ∪ BR z := by
        intro z hz
        ext p; constructor
        · rintro ⟨hp_ball, hp_nα⟩
          have hpV := hball_V z hz hp_ball
          have hp_nbd : p ∉ bdHP h := by
            intro hp_bd
            rw [← lineParam_range h] at hp_bd
            obtain ⟨s', rfl⟩ := hp_bd
            by_cases hs' : s' ∈ SixWedges.seg xs i
            · exact hp_nα ⟨s', hs', rfl⟩
            · exact hpV.2 ⟨s', hs', rfl⟩
          change h.n.1 * p.1 + h.n.2 * p.2 + h.c ≠ 0 at hp_nbd
          rcases lt_or_gt_of_ne hp_nbd with hlt | hgt
          · right; exact ⟨hp_ball, hlt⟩
          · left; exact ⟨hp_ball, hgt⟩
        · rintro (⟨hp_ball, hp_pos⟩ | ⟨hp_ball, hp_neg⟩)
          · refine ⟨hp_ball, fun hpα => ?_⟩
            obtain ⟨s', _, rfl⟩ := hpα
            have hbd := lineParam_mem_bdHP h s'
            change h.n.1 * _ + h.n.2 * _ + h.c = 0 at hbd
            change 0 < h.n.1 * _ + h.n.2 * _ + h.c at hp_pos
            linarith
          · refine ⟨hp_ball, fun hpα => ?_⟩
            obtain ⟨s', _, rfl⟩ := hpα
            have hbd := lineParam_mem_bdHP h s'
            change h.n.1 * _ + h.n.2 * _ + h.c = 0 at hbd
            change h.n.1 * _ + h.n.2 * _ + h.c < 0 at hp_neg
            linarith
      have hBL_ne : ∀ z ∈ α i, (BL z).Nonempty := fun z hz => by
        obtain ⟨s, _, rfl⟩ := hz
        exact bdHP_ball_memPos_ne h (lineParam_mem_bdHP h s) (hr_pos _ ⟨s, ‹_›, rfl⟩)
      have hBL_conn : ∀ z ∈ α i, IsPreconnected (BL z) := fun z _ =>
        ((convex_ball z (r z)).inter (memPos_convex h)).isPreconnected
      have hBR_ne : ∀ z ∈ α i, (BR z).Nonempty := fun z hz => by
        obtain ⟨s, _, rfl⟩ := hz
        exact bdHP_ball_memNeg_ne h (lineParam_mem_bdHP h s) (hr_pos _ ⟨s, ‹_›, rfl⟩)
      have hBR_conn : ∀ z ∈ α i, IsPreconnected (BR z) := fun z _ =>
        ((convex_ball z (r z)).inter (memNeg_convex h)).isPreconnected
      have h_ball_inter : ∀ z ∈ α i, ∀ z' ∈ α i, z' ∈ Metric.ball z (r z) →
          ∃ δ > 0, Metric.ball z' δ ⊆ Metric.ball z (r z) ∩ Metric.ball z' (r z') := by
        intro z _ z' hz' hz'b
        let δ := min (r z - dist z' z) (r z')
        have hδ : 0 < δ := lt_min (sub_pos.mpr (Metric.mem_ball.mp hz'b)) (hr_pos z' hz')
        refine ⟨δ, hδ, fun p hp => ⟨?_, ?_⟩⟩
        · rw [Metric.mem_ball] at hp ⊢
          have hd1 : dist p z' < r z - dist z' z := lt_of_lt_of_le hp (min_le_left _ _)
          linarith [dist_triangle p z' z]
        · exact Metric.mem_ball.mpr (lt_of_lt_of_le (Metric.mem_ball.mp hp) (min_le_right _ _))
      have hBL_ov : ∀ z ∈ α i, ∀ z' ∈ α i, z' ∈ Metric.ball z (r z) → (BL z ∩ BL z').Nonempty := by
        intro z hz z' hz' hz'b
        obtain ⟨δ, hδ, hsub_ball⟩ := h_ball_inter z hz z' hz' hz'b
        obtain ⟨s', _, rfl⟩ := hz'
        obtain ⟨p, hp_ball, hp_pos⟩ := bdHP_ball_memPos_ne h (lineParam_mem_bdHP h s') hδ
        exact ⟨p, ⟨(hsub_ball hp_ball).1, hp_pos⟩, ⟨(hsub_ball hp_ball).2, hp_pos⟩⟩
      have hBR_ov : ∀ z ∈ α i, ∀ z' ∈ α i, z' ∈ Metric.ball z (r z) → (BR z ∩ BR z').Nonempty := by
        intro z hz z' hz' hz'b
        obtain ⟨δ, hδ, hsub_ball⟩ := h_ball_inter z hz z' hz' hz'b
        obtain ⟨s', _, rfl⟩ := hz'
        obtain ⟨p, hp_ball, hp_neg⟩ := bdHP_ball_memNeg_ne h (lineParam_mem_bdHP h s') hδ
        exact ⟨p, ⟨(hsub_ball hp_ball).1, hp_neg⟩, ⟨(hsub_ball hp_ball).2, hp_neg⟩⟩
      have h_inc : (SixWedges.Comps (U_step (m + 1))).encard ≤ (SixWedges.Comps (U_step m)).encard + 1 := by
        rw [h_split]
        exact SixWedges.comps_remove_arc (hU_step_open m) hi_sub hα_ne hα_conn hUi_open r BL BR
          hr_pos hball_sub hball_split hBL_ne hBL_conn hBR_ne hBR_conn hBL_ov hBR_ov
      calc (SixWedges.Comps (U_step (m + 1))).encard
          ≤ (SixWedges.Comps (U_step m)).encard + 1 := h_inc
        _ ≤ ((SixWedges.Comps U₀).encard + (m : ℕ∞)) + 1 := add_le_add (ih (Nat.le_of_lt hm')) le_rfl
        _ = (SixWedges.Comps U₀).encard + ((m + 1 : ℕ) : ℕ∞) := by
            rw [Nat.cast_add, Nat.cast_one, add_assoc]
  have h_final_eq : (Set.univ : Set (ℝ × ℝ)) \ (K ∪ bdHP h) = U_step (xs.length + 1) := by
    ext p; constructor
    · rintro ⟨hp_om, hp_not⟩
      refine ⟨⟨hp_om, fun hKmem => hp_not (Or.inl hKmem)⟩, fun hmem => ?_⟩
      rw [Set.mem_iUnion₂] at hmem
      rcases hmem with ⟨_, _, ⟨s, _, rfl⟩⟩
      exact hp_not (Or.inr (lineParam_mem_bdHP h s))
    · rintro ⟨⟨hp_om, hp_notK⟩, hp_not_seg⟩
      refine ⟨hp_om, fun hmem => ?_⟩
      rcases hmem with hKmem | hbd
      · exact hp_notK hKmem
      · rw [← lineParam_range h] at hbd
        obtain ⟨s, rfl⟩ := hbd
        have hs_nxs : s ∉ xs := fun hmem => hp_notK ((hxs_iff s).mp hmem).2
        have hmem_seg := SixWedges.compl_list_subset_iUnion_seg xs hs_nxs
        rw [Set.mem_iUnion] at hmem_seg
        obtain ⟨i, hsi⟩ := hmem_seg
        exact hp_not_seg (Set.mem_iUnion₂.mpr ⟨i, i.isLt, ⟨s, hsi, rfl⟩⟩)
  have h_len_bound : xs.length ≤ P_set.ncard := by
    have h1 : xs.length = hP_param_fin.toFinset.card := Finset.length_sort (· ≤ ·)
    have h2 : (hP_param_fin.toFinset.card : ℕ) = P_param.ncard :=
      (Set.ncard_eq_toFinset_card P_param hP_param_fin).symm
    have h3 : P_param.ncard ≤ P_set.ncard := by
      have himg : lineParam h '' P_param ⊆ P_set := Set.image_preimage_subset _ _
      rw [← Set.ncard_image_of_injective P_param (lineParam_injective h)]
      exact Set.ncard_le_ncard himg hfin
    omega
  rw [h_final_eq]
  have h_fin := h_step (xs.length + 1) le_rfl
  calc (SixWedges.Comps (U_step (xs.length + 1))).encard
      ≤ (SixWedges.Comps U₀).encard + ((xs.length + 1 : ℕ) : ℕ∞) := h_fin
    _ ≤ (SixWedges.Comps U₀).encard + ((P_set.ncard + 1 : ℕ) : ℕ∞) :=
        add_le_add le_rfl (Nat.cast_le.mpr (by omega))

private lemma add_wedge_comps_bound (W : OpenWedge) (K : Set (ℝ × ℝ)) (hK : IsClosed K)
    (hfin : (SixWedges.bdWedge W ∩ K).Finite) :
    (SixWedges.Comps ((Set.univ : Set (ℝ × ℝ)) \ (K ∪ SixWedges.bdWedge W))).encard ≤
      (SixWedges.Comps ((Set.univ : Set (ℝ × ℝ)) \ K)).encard +
        ((SixWedges.bdWedge W ∩ K).ncard + 1 : ℕ) := by
  let U₀ : Set (ℝ × ℝ) := Set.univ \ K
  have hU₀_open : IsOpen U₀ := isOpen_univ.sdiff hK
  let P_set : Set (ℝ × ℝ) := SixWedges.bdWedge W ∩ K
  let P_param : Set ℝ := (SixWedges.gammaParam W) ⁻¹' P_set
  have hP_param_fin : P_param.Finite := hfin.preimage (SixWedges.gammaParam_injective W).injOn
  let xs : List ℝ := hP_param_fin.toFinset.sort (· ≤ ·)
  have hxs_sorted : xs.SortedLT := Finset.sortedLT_sort _
  have hxs_iff : ∀ s : ℝ, s ∈ xs ↔ SixWedges.gammaParam W s ∈ P_set := fun s => by
    simp [xs, P_param]
  let α : Fin (xs.length + 1) → Set (ℝ × ℝ) := fun i => SixWedges.gammaParam W '' SixWedges.seg xs i
  let U_step : ℕ → Set (ℝ × ℝ) := fun m =>
    U₀ \ ⋃ (i : Fin (xs.length + 1)) (_ : i.val < m), α i
  have hU_step_open : ∀ m, IsOpen (U_step m) := by
    intro m
    let I : Finset (Fin (xs.length + 1)) := Finset.univ.filter (fun i => i.val < m)
    let S_cl : Set ℝ := ⋃ i ∈ (I : Set (Fin (xs.length + 1))), closure (SixWedges.seg xs i)
    have hS_cl : IsClosed S_cl :=
      I.finite_toSet.isClosed_biUnion fun _ _ => isClosed_closure
    let K_cl : Set (ℝ × ℝ) := SixWedges.gammaParam W '' S_cl
    have hK_cl : IsClosed K_cl := SixWedges.gammaParam_image_isClosed W hS_cl
    have hEq : U_step m = U₀ \ K_cl := by
      ext p; constructor
      · rintro ⟨hpU₀, hp_not⟩
        refine ⟨hpU₀, ?_⟩
        rintro ⟨s, hs, rfl⟩
        rw [Set.mem_iUnion₂] at hs
        rcases hs with ⟨i, hiI, hsi⟩
        rcases SixWedges.closure_seg_subset xs i hsi with hseg | hmem_xs
        · exact hp_not (Set.mem_iUnion₂.mpr ⟨i, (Finset.mem_filter.mp (Finset.mem_coe.mp hiI)).2,
            ⟨s, hseg, rfl⟩⟩)
        · exact hpU₀.2 ((hxs_iff s).mp hmem_xs).2
      · rintro ⟨hpU₀, hp_not⟩
        refine ⟨hpU₀, fun hmem => hp_not ?_⟩
        rw [Set.mem_iUnion₂] at hmem
        rcases hmem with ⟨i, him, ⟨s, hsi, rfl⟩⟩
        refine ⟨s, Set.mem_iUnion₂.mpr ⟨i, ?_, subset_closure hsi⟩, rfl⟩
        exact Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ i, him⟩)
    rw [hEq]
    exact hU₀_open.sdiff hK_cl
  have h_step : ∀ m : ℕ, m ≤ xs.length + 1 →
      (SixWedges.Comps (U_step m)).encard ≤ (SixWedges.Comps U₀).encard + (m : ℕ∞) := by
    intro m
    induction m with
    | zero =>
      intro _
      have heq : U_step 0 = U₀ := by ext p; simp [U_step]
      rw [heq]; simp
    | succ m ih =>
      intro hm
      have hm' : m < xs.length + 1 := hm
      let i : Fin (xs.length + 1) := ⟨m, hm'⟩
      have h_split : U_step (m + 1) = U_step m \ α i := by
        ext p; constructor
        · rintro ⟨hpU₀, hp_not⟩
          refine ⟨⟨hpU₀, fun hmem => hp_not ?_⟩, fun hmem => hp_not ?_⟩
          · rw [Set.mem_iUnion₂] at hmem ⊢
            rcases hmem with ⟨j, hj, hpj⟩
            exact ⟨j, Nat.lt_succ_of_lt hj, hpj⟩
          · exact Set.mem_iUnion₂.mpr ⟨i, Nat.lt_succ_self m, hmem⟩
        · rintro ⟨⟨hpU₀, hp_not⟩, hp_ni⟩
          refine ⟨hpU₀, fun hmem => ?_⟩
          rw [Set.mem_iUnion₂] at hmem
          rcases hmem with ⟨j, hj, hpj⟩
          rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj' | hj'
          · exact hp_not (Set.mem_iUnion₂.mpr ⟨j, hj', hpj⟩)
          · have hji : j = i := Fin.ext hj'
            rw [hji] at hpj
            exact hp_ni hpj
      have hi_sub : α i ⊆ U_step m := by
        rintro p ⟨s, hs, rfl⟩
        refine ⟨⟨trivial, fun hU => ?_⟩, fun hprev => ?_⟩
        · have hP : SixWedges.gammaParam W s ∈ P_set := ⟨SixWedges.gammaParam_mem_bdWedge W s, hU⟩
          exact SixWedges.seg_disjoint_list xs hxs_sorted i hs ((hxs_iff s).mpr hP)
        · rw [Set.mem_iUnion₂] at hprev
          rcases hprev with ⟨j, hj, ⟨s', hs', heq⟩⟩
          have hij : j ≠ i := fun h0 => by rw [h0] at hj; exact Nat.lt_irrefl m hj
          have hs_eq : s' = s := SixWedges.gammaParam_injective W heq
          subst hs_eq
          exact Set.disjoint_left.mp
            (seg_pairwise_disjoint' xs (hj.trans hm') hm' (fun h0 => hij (Fin.ext h0))) hs' hs
      have hα_ne : (α i).Nonempty := (SixWedges.seg_nonempty xs hxs_sorted i).image _
      have hα_conn : IsPreconnected (α i) :=
        (SixWedges.seg_isPreconnected xs i).image (SixWedges.gammaParam W)
          (SixWedges.gammaParam_continuous W).continuousOn
      have hUi_open : IsOpen (U_step m \ α i) := h_split ▸ hU_step_open (m + 1)
      let K_other : Set (ℝ × ℝ) := SixWedges.gammaParam W '' (SixWedges.seg xs i)ᶜ
      have hK_closed : IsClosed K_other :=
        SixWedges.gammaParam_image_isClosed W (SixWedges.seg_isOpen xs i).isClosed_compl
      let V : (ℝ × ℝ) → Set (ℝ × ℝ) := fun z =>
        if z = W.y then U_step m ∩ K_otherᶜ
        else if W.u₁.1 * (z.1 - W.y.1) + W.u₁.2 * (z.2 - W.y.2) = 0 then
          U_step m ∩ K_otherᶜ ∩ {p | 0 < W.u₂.1 * (p.1 - W.y.1) + W.u₂.2 * (p.2 - W.y.2)}
        else
          U_step m ∩ K_otherᶜ ∩ {p | 0 < W.u₁.1 * (p.1 - W.y.1) + W.u₁.2 * (p.2 - W.y.2)}
      have hV_open : ∀ z, IsOpen (V z) := by
        intro z; dsimp [V]
        split_ifs
        · exact (hU_step_open m).inter hK_closed.isOpen_compl
        · refine ((hU_step_open m).inter hK_closed.isOpen_compl).inter (isOpen_lt continuous_const ?_)
          fun_prop
        · refine ((hU_step_open m).inter hK_closed.isOpen_compl).inter (isOpen_lt continuous_const ?_)
          fun_prop
      have hz_mem_V : ∀ z ∈ α i, z ∈ V z := by
        rintro z ⟨s, hs, rfl⟩
        have hzU : SixWedges.gammaParam W s ∈ U_step m := hi_sub ⟨s, hs, rfl⟩
        have hzG : SixWedges.gammaParam W s ∈ SixWedges.bdWedge W := SixWedges.gammaParam_mem_bdWedge W s
        have hzK : SixWedges.gammaParam W s ∉ K_other := by
          rintro ⟨s', hs', heq⟩
          rw [SixWedges.gammaParam_injective W heq] at hs'
          exact hs' hs
        dsimp [V]
        split_ifs with hzy hz1
        · exact ⟨hzU, hzK⟩
        · refine ⟨⟨hzU, hzK⟩, ?_⟩
          have hcl := (SixWedges.bdWedge_iff_closure_eq_zero W _).mp hzG |>.1
          refine lt_of_le_of_ne hcl.2 fun hz2 => hzy ?_
          have hnd := ne_of_gt W.h_nondeg
          have e1 : (SixWedges.gammaParam W s).1 - W.y.1 = 0 := by
            have hmul : ((SixWedges.gammaParam W s).1 - W.y.1) *
                (W.u₁.1 * W.u₂.2 - W.u₁.2 * W.u₂.1) = 0 := by
              linear_combination W.u₂.2 * hz1 - W.u₁.2 * hz2.symm
            exact (mul_eq_zero.mp hmul).resolve_right hnd
          have e2 : (SixWedges.gammaParam W s).2 - W.y.2 = 0 := by
            have hmul : ((SixWedges.gammaParam W s).2 - W.y.2) *
                (W.u₁.1 * W.u₂.2 - W.u₁.2 * W.u₂.1) = 0 := by
              linear_combination -W.u₂.1 * hz1 + W.u₁.1 * hz2.symm
            exact (mul_eq_zero.mp hmul).resolve_right hnd
          ext <;> linarith
        · refine ⟨⟨hzU, hzK⟩, ?_⟩
          have hcl := (SixWedges.bdWedge_iff_closure_eq_zero W _).mp hzG |>.1
          exact lt_of_le_of_ne hcl.1 (Ne.symm hz1)
      let r : (ℝ × ℝ) → ℝ := fun z =>
        if hz : z ∈ α i then (Metric.isOpen_iff.mp (hV_open z) z (hz_mem_V z hz)).choose else 1
      have hr_pos : ∀ z ∈ α i, 0 < r z := fun z hz => by
        dsimp [r]; rw [dif_pos hz]
        exact (Metric.isOpen_iff.mp (hV_open z) z (hz_mem_V z hz)).choose_spec.1
      have hball_V : ∀ z ∈ α i, Metric.ball z (r z) ⊆ V z := fun z hz => by
        dsimp [r]; rw [dif_pos hz]
        exact (Metric.isOpen_iff.mp (hV_open z) z (hz_mem_V z hz)).choose_spec.2
      have hV_sub_UK : ∀ z, V z ⊆ U_step m ∩ K_otherᶜ := by
        intro z; dsimp [V]; split_ifs <;>
          [exact Set.Subset.rfl; exact Set.inter_subset_left; exact Set.inter_subset_left]
      have hball_sub : ∀ z ∈ α i, Metric.ball z (r z) ⊆ U_step m := fun z hz =>
        (hball_V z hz).trans ((hV_sub_UK z).trans Set.inter_subset_left)
      let BL : (ℝ × ℝ) → Set (ℝ × ℝ) := fun z => Metric.ball z (r z) ∩ {p | W.MemOpen p}
      let BR : (ℝ × ℝ) → Set (ℝ × ℝ) := fun z => Metric.ball z (r z) ∩ {p | W.MemExt p}
      have hball_split : ∀ z ∈ α i, Metric.ball z (r z) \ α i = BL z ∪ BR z := by
        intro z hz
        ext p; constructor
        · rintro ⟨hp_ball, hp_nα⟩
          have hpUK := hV_sub_UK z (hball_V z hz hp_ball)
          have hp_nbd : p ∉ SixWedges.bdWedge W := by
            intro hp_bd
            rw [← SixWedges.gammaParam_range W] at hp_bd
            obtain ⟨s', rfl⟩ := hp_bd
            by_cases hs' : s' ∈ SixWedges.seg xs i
            · exact hp_nα ⟨s', hs', rfl⟩
            · exact hpUK.2 ⟨s', hs', rfl⟩
          dsimp [SixWedges.bdWedge] at hp_nbd
          push Not at hp_nbd
          by_cases ho : W.MemOpen p
          · left; exact ⟨hp_ball, ho⟩
          · right; exact ⟨hp_ball, hp_nbd ho⟩
        · rintro (⟨hp_ball, ho⟩ | ⟨hp_ball, he⟩)
          · refine ⟨hp_ball, fun hpα => ?_⟩
            obtain ⟨s', _, rfl⟩ := hpα
            exact (SixWedges.gammaParam_mem_bdWedge W s').1 ho
          · refine ⟨hp_ball, fun hpα => ?_⟩
            obtain ⟨s', _, rfl⟩ := hpα
            exact (SixWedges.gammaParam_mem_bdWedge W s').2 he
      have hBL_ne : ∀ z ∈ α i, (BL z).Nonempty := fun z hz => by
        obtain ⟨s, _, rfl⟩ := hz
        exact bdWedge_ball_memOpen_ne' W (SixWedges.gammaParam_mem_bdWedge W s) (hr_pos _ ⟨s, ‹_›, rfl⟩)
      have hBL_conn : ∀ z ∈ α i, IsPreconnected (BL z) := fun z _ =>
        ((convex_ball z (r z)).inter (SixWedges.memOpen_convex W)).isPreconnected
      have hBR_ne : ∀ z ∈ α i, (BR z).Nonempty := fun z hz => by
        obtain ⟨s, _, rfl⟩ := hz
        exact bdWedge_ball_memExt_ne' W (SixWedges.gammaParam_mem_bdWedge W s) (hr_pos _ ⟨s, ‹_›, rfl⟩)
      have hBR_conn : ∀ z ∈ α i, IsPreconnected (BR z) := by
        intro z hz
        dsimp [BR]
        by_cases hzy : z = W.y
        · let S1 : Set (ℝ × ℝ) := Metric.ball z (r z) ∩
            {p | W.u₁.1 * (p.1 - W.y.1) + W.u₁.2 * (p.2 - W.y.2) < 0}
          let S2 : Set (ℝ × ℝ) := Metric.ball z (r z) ∩
            {p | W.u₂.1 * (p.1 - W.y.1) + W.u₂.2 * (p.2 - W.y.2) < 0}
          have heq : Metric.ball z (r z) ∩ {p | W.MemExt p} = S1 ∪ S2 := by
            ext p; simp [S1, S2, OpenWedge.MemExt, and_or_left]
          rw [heq]
          have hc1 : IsPreconnected S1 :=
            ((convex_ball z (r z)).inter (halfspace_lt_convex' W.u₁ W.y)).isPreconnected
          have hc2 : IsPreconnected S2 :=
            ((convex_ball z (r z)).inter (halfspace_lt_convex' W.u₂ W.y)).isPreconnected
          let d_neg : ℝ × ℝ := (-(SixWedges.dir1 W).1 - (SixWedges.dir2 W).1,
                                -(SixWedges.dir1 W).2 - (SixWedges.dir2 W).2)
          obtain ⟨ε, hε, hball⟩ := ball_shift_mem' (z := z) (d := d_neg) (hr_pos z hz)
          have hnd := W.h_nondeg
          have ho1 : W.u₁.1 * ((z.1 + ε * d_neg.1) - W.y.1) +
              W.u₁.2 * ((z.2 + ε * d_neg.2) - W.y.2) < 0 := by
            rw [hzy]
            have e : W.u₁.1 * ((W.y.1 + ε * d_neg.1) - W.y.1) +
                W.u₁.2 * ((W.y.2 + ε * d_neg.2) - W.y.2) =
                -ε * (W.u₁.1 * W.u₂.2 - W.u₁.2 * W.u₂.1) := by
              dsimp [d_neg, SixWedges.dir1, SixWedges.dir2]; ring
            rw [e]; nlinarith
          have ho2 : W.u₂.1 * ((z.1 + ε * d_neg.1) - W.y.1) +
              W.u₂.2 * ((z.2 + ε * d_neg.2) - W.y.2) < 0 := by
            rw [hzy]
            have e : W.u₂.1 * ((W.y.1 + ε * d_neg.1) - W.y.1) +
                W.u₂.2 * ((W.y.2 + ε * d_neg.2) - W.y.2) =
                -ε * (W.u₁.1 * W.u₂.2 - W.u₁.2 * W.u₂.1) := by
              dsimp [d_neg, SixWedges.dir1, SixWedges.dir2]; ring
            rw [e]; nlinarith
          exact hc1.union' ⟨(z.1 + ε * d_neg.1, z.2 + ε * d_neg.2), ⟨hball, ho1⟩, ⟨hball, ho2⟩⟩ hc2
        · by_cases hz1 : W.u₁.1 * (z.1 - W.y.1) + W.u₁.2 * (z.2 - W.y.2) = 0
          · have hsubV : Metric.ball z (r z) ⊆ {p | 0 < W.u₂.1 * (p.1 - W.y.1) + W.u₂.2 * (p.2 - W.y.2)} := by
              intro p hp
              have hpV := hball_V z hz hp
              dsimp [V] at hpV
              rw [if_neg hzy, if_pos hz1] at hpV
              exact hpV.2
            have heq : Metric.ball z (r z) ∩ {p | W.MemExt p} =
                Metric.ball z (r z) ∩ {p | W.u₁.1 * (p.1 - W.y.1) + W.u₁.2 * (p.2 - W.y.2) < 0} := by
              ext p; constructor
              · rintro ⟨hp, hp1 | hp2⟩
                · exact ⟨hp, hp1⟩
                · exfalso; have hp_pos := hsubV hp
                  change 0 < W.u₂.1 * (p.1 - W.y.1) + W.u₂.2 * (p.2 - W.y.2) at hp_pos; linarith
              · rintro ⟨hp, hp1⟩; exact ⟨hp, Or.inl hp1⟩
            rw [heq]
            exact ((convex_ball z (r z)).inter (halfspace_lt_convex' W.u₁ W.y)).isPreconnected
          · have hsubV : Metric.ball z (r z) ⊆ {p | 0 < W.u₁.1 * (p.1 - W.y.1) + W.u₁.2 * (p.2 - W.y.2)} := by
              intro p hp
              have hpV := hball_V z hz hp
              dsimp [V] at hpV
              rw [if_neg hzy, if_neg hz1] at hpV
              exact hpV.2
            have heq : Metric.ball z (r z) ∩ {p | W.MemExt p} =
                Metric.ball z (r z) ∩ {p | W.u₂.1 * (p.1 - W.y.1) + W.u₂.2 * (p.2 - W.y.2) < 0} := by
              ext p; constructor
              · rintro ⟨hp, hp1 | hp2⟩
                · exfalso; have hp_pos := hsubV hp
                  change 0 < W.u₁.1 * (p.1 - W.y.1) + W.u₁.2 * (p.2 - W.y.2) at hp_pos; linarith
                · exact ⟨hp, hp2⟩
              · rintro ⟨hp, hp2⟩; exact ⟨hp, Or.inr hp2⟩
            rw [heq]
            exact ((convex_ball z (r z)).inter (halfspace_lt_convex' W.u₂ W.y)).isPreconnected
      have h_ball_inter : ∀ z ∈ α i, ∀ z' ∈ α i, z' ∈ Metric.ball z (r z) →
          ∃ δ > 0, Metric.ball z' δ ⊆ Metric.ball z (r z) ∩ Metric.ball z' (r z') := by
        intro z _ z' hz' hz'b
        let δ := min (r z - dist z' z) (r z')
        have hδ : 0 < δ := lt_min (sub_pos.mpr (Metric.mem_ball.mp hz'b)) (hr_pos z' hz')
        refine ⟨δ, hδ, fun p hp => ⟨?_, ?_⟩⟩
        · rw [Metric.mem_ball] at hp ⊢
          have hd1 : dist p z' < r z - dist z' z := lt_of_lt_of_le hp (min_le_left _ _)
          linarith [dist_triangle p z' z]
        · exact Metric.mem_ball.mpr (lt_of_lt_of_le (Metric.mem_ball.mp hp) (min_le_right _ _))
      have hBL_ov : ∀ z ∈ α i, ∀ z' ∈ α i, z' ∈ Metric.ball z (r z) → (BL z ∩ BL z').Nonempty := by
        intro z hz z' hz' hz'b
        obtain ⟨δ, hδ, hsub_ball⟩ := h_ball_inter z hz z' hz' hz'b
        obtain ⟨s', _, rfl⟩ := hz'
        obtain ⟨p, hp_ball, hp_om⟩ := bdWedge_ball_memOpen_ne' W (SixWedges.gammaParam_mem_bdWedge W s') hδ
        exact ⟨p, ⟨(hsub_ball hp_ball).1, hp_om⟩, ⟨(hsub_ball hp_ball).2, hp_om⟩⟩
      have hBR_ov : ∀ z ∈ α i, ∀ z' ∈ α i, z' ∈ Metric.ball z (r z) → (BR z ∩ BR z').Nonempty := by
        intro z hz z' hz' hz'b
        obtain ⟨δ, hδ, hsub_ball⟩ := h_ball_inter z hz z' hz' hz'b
        obtain ⟨s', _, rfl⟩ := hz'
        obtain ⟨p, hp_ball, hp_ext⟩ := bdWedge_ball_memExt_ne' W (SixWedges.gammaParam_mem_bdWedge W s') hδ
        exact ⟨p, ⟨(hsub_ball hp_ball).1, hp_ext⟩, ⟨(hsub_ball hp_ball).2, hp_ext⟩⟩
      have h_inc : (SixWedges.Comps (U_step (m + 1))).encard ≤ (SixWedges.Comps (U_step m)).encard + 1 := by
        rw [h_split]
        exact SixWedges.comps_remove_arc (hU_step_open m) hi_sub hα_ne hα_conn hUi_open r BL BR
          hr_pos hball_sub hball_split hBL_ne hBL_conn hBR_ne hBR_conn hBL_ov hBR_ov
      calc (SixWedges.Comps (U_step (m + 1))).encard
          ≤ (SixWedges.Comps (U_step m)).encard + 1 := h_inc
        _ ≤ ((SixWedges.Comps U₀).encard + (m : ℕ∞)) + 1 := add_le_add (ih (Nat.le_of_lt hm')) le_rfl
        _ = (SixWedges.Comps U₀).encard + ((m + 1 : ℕ) : ℕ∞) := by
            rw [Nat.cast_add, Nat.cast_one, add_assoc]
  have h_final_eq : (Set.univ : Set (ℝ × ℝ)) \ (K ∪ SixWedges.bdWedge W) = U_step (xs.length + 1) := by
    ext p; constructor
    · rintro ⟨hp_om, hp_not⟩
      refine ⟨⟨hp_om, fun hKmem => hp_not (Or.inl hKmem)⟩, fun hmem => ?_⟩
      rw [Set.mem_iUnion₂] at hmem
      rcases hmem with ⟨_, _, ⟨s, _, rfl⟩⟩
      exact hp_not (Or.inr (SixWedges.gammaParam_mem_bdWedge W s))
    · rintro ⟨⟨hp_om, hp_notK⟩, hp_not_seg⟩
      refine ⟨hp_om, fun hmem => ?_⟩
      rcases hmem with hKmem | hbd
      · exact hp_notK hKmem
      · rw [← SixWedges.gammaParam_range W] at hbd
        obtain ⟨s, rfl⟩ := hbd
        have hs_nxs : s ∉ xs := fun hmem => hp_notK ((hxs_iff s).mp hmem).2
        have hmem_seg := SixWedges.compl_list_subset_iUnion_seg xs hs_nxs
        rw [Set.mem_iUnion] at hmem_seg
        obtain ⟨i, hsi⟩ := hmem_seg
        exact hp_not_seg (Set.mem_iUnion₂.mpr ⟨i, i.isLt, ⟨s, hsi, rfl⟩⟩)
  have h_len_bound : xs.length ≤ P_set.ncard := by
    have h1 : xs.length = hP_param_fin.toFinset.card := Finset.length_sort (· ≤ ·)
    have h2 : (hP_param_fin.toFinset.card : ℕ) = P_param.ncard :=
      (Set.ncard_eq_toFinset_card P_param hP_param_fin).symm
    have h3 : P_param.ncard ≤ P_set.ncard := by
      have himg : SixWedges.gammaParam W '' P_param ⊆ P_set := Set.image_preimage_subset _ _
      rw [← Set.ncard_image_of_injective P_param (SixWedges.gammaParam_injective W)]
      exact Set.ncard_le_ncard himg hfin
    omega
  rw [h_final_eq]
  have h_fin := h_step (xs.length + 1) le_rfl
  calc (SixWedges.Comps (U_step (xs.length + 1))).encard
      ≤ (SixWedges.Comps U₀).encard + ((xs.length + 1 : ℕ) : ℕ∞) := h_fin
    _ ≤ (SixWedges.Comps U₀).encard + ((P_set.ncard + 1 : ℕ) : ℕ∞) :=
        add_le_add le_rfl (Nat.cast_le.mpr (by omega))

private def norm8 (H : Fin 2 → OpenHalfPlane) (R : Fin 3 → OpenWedge) : Fin 8 → ℝ × ℝ
  | 0 => (H 0).n
  | 1 => (H 1).n
  | 2 => (R 0).u₁
  | 3 => (R 0).u₂
  | 4 => (R 1).u₁
  | 5 => (R 1).u₂
  | 6 => (R 2).u₁
  | 7 => (R 2).u₂

private def GP23 (H : Fin 2 → OpenHalfPlane) (R : Fin 3 → OpenWedge) : Prop :=
  ∀ i j : Fin 8, i ≠ j → SixWedges.det2 (norm8 H R i) (norm8 H R j) ≠ 0

private lemma exists_gp23_perturbation (H : Fin 2 → OpenHalfPlane) (R : Fin 3 → OpenWedge)
    (h_all : ∀ (mH : Fin 2 → Bool) (mW : Fin 3 → Bool), ∃ p : ℝ × ℝ,
      (∀ i : Fin 2, if mH i then (H i).MemPos p else (H i).MemNeg p) ∧
      (∀ j : Fin 3, if mW j then (R j).MemOpen p else (R j).MemExt p)) :
    ∃ (H' : Fin 2 → OpenHalfPlane) (R' : Fin 3 → OpenWedge), GP23 H' R' ∧
      ∀ (mH : Fin 2 → Bool) (mW : Fin 3 → Bool), ∃ p : ℝ × ℝ,
        (∀ i : Fin 2, if mH i then (H' i).MemPos p else (H' i).MemNeg p) ∧
        (∀ j : Fin 3, if mW j then (R' j).MemOpen p else (R' j).MemExt p) := by
  let zm : (Fin 2 → Bool) → (Fin 3 → Bool) → ℝ × ℝ := fun mH mW => (h_all mH mW).choose
  have hzm : ∀ mH mW,
      (∀ i : Fin 2, if mH i then (H i).MemPos (zm mH mW) else (H i).MemNeg (zm mH mW)) ∧
      (∀ j : Fin 3, if mW j then (R j).MemOpen (zm mH mW) else (R j).MemExt (zm mH mW)) :=
    fun mH mW => (h_all mH mW).choose_spec
  -- Encode (H 0, H 1, R 0, R 1, R 2) into Fin 24 → ℝ:
  -- 0..2: H0 (n.1, n.2, c); 3..5: H1 (n.1, n.2, c);
  -- 6 + 6*j .. 6 + 6*j + 5: R j (y.1, y.2, u1.1, u1.2, u2.1, u2.2)
  let x₀ : Fin 24 → ℝ := ![
    (H 0).n.1, (H 0).n.2, (H 0).c,
    (H 1).n.1, (H 1).n.2, (H 1).c,
    (R 0).y.1, (R 0).y.2, (R 0).u₁.1, (R 0).u₁.2, (R 0).u₂.1, (R 0).u₂.2,
    (R 1).y.1, (R 1).y.2, (R 1).u₁.1, (R 1).u₁.2, (R 1).u₂.1, (R 1).u₂.2,
    (R 2).y.1, (R 2).y.2, (R 2).u₁.1, (R 2).u₁.2, (R 2).u₂.1, (R 2).u₂.2
  ]
  let n1Idx : Fin 8 → Fin 24 := ![0, 3, 8, 10, 14, 16, 20, 22]
  let n2Idx : Fin 8 → Fin 24 := ![1, 4, 9, 11, 15, 17, 21, 23]
  let cond : (Fin 24 → ℝ) → Prop := fun x =>
    (∀ i : Fin 2, x ⟨3 * i.1, by omega⟩ ≠ 0 ∨ x ⟨3 * i.1 + 1, by omega⟩ ≠ 0) ∧
    (∀ j : Fin 3,
      0 < x ⟨6 + 6 * j.1 + 2, by omega⟩ * x ⟨6 + 6 * j.1 + 5, by omega⟩ -
          x ⟨6 + 6 * j.1 + 3, by omega⟩ * x ⟨6 + 6 * j.1 + 4, by omega⟩) ∧
    (∀ (mH : Fin 2 → Bool) (mW : Fin 3 → Bool),
      (∀ i : Fin 2,
        if mH i then
          0 < x ⟨3 * i.1, by omega⟩ * (zm mH mW).1 +
              x ⟨3 * i.1 + 1, by omega⟩ * (zm mH mW).2 + x ⟨3 * i.1 + 2, by omega⟩
        else
          x ⟨3 * i.1, by omega⟩ * (zm mH mW).1 +
              x ⟨3 * i.1 + 1, by omega⟩ * (zm mH mW).2 + x ⟨3 * i.1 + 2, by omega⟩ < 0) ∧
      (∀ j : Fin 3,
        if mW j then
          0 < x ⟨6 + 6 * j.1 + 2, by omega⟩ * ((zm mH mW).1 - x ⟨6 + 6 * j.1, by omega⟩) +
              x ⟨6 + 6 * j.1 + 3, by omega⟩ * ((zm mH mW).2 - x ⟨6 + 6 * j.1 + 1, by omega⟩) ∧
          0 < x ⟨6 + 6 * j.1 + 4, by omega⟩ * ((zm mH mW).1 - x ⟨6 + 6 * j.1, by omega⟩) +
              x ⟨6 + 6 * j.1 + 5, by omega⟩ * ((zm mH mW).2 - x ⟨6 + 6 * j.1 + 1, by omega⟩)
        else
          x ⟨6 + 6 * j.1 + 2, by omega⟩ * ((zm mH mW).1 - x ⟨6 + 6 * j.1, by omega⟩) +
              x ⟨6 + 6 * j.1 + 3, by omega⟩ * ((zm mH mW).2 - x ⟨6 + 6 * j.1 + 1, by omega⟩) < 0 ∨
          x ⟨6 + 6 * j.1 + 4, by omega⟩ * ((zm mH mW).1 - x ⟨6 + 6 * j.1, by omega⟩) +
              x ⟨6 + 6 * j.1 + 5, by omega⟩ * ((zm mH mW).2 - x ⟨6 + 6 * j.1 + 1, by omega⟩) < 0))
  have hopen : IsOpen {x : Fin 24 → ℝ | cond x} := by
    dsimp only [cond]
    rw [Set.setOf_and, Set.setOf_and]
    refine IsOpen.inter ?_ (IsOpen.inter ?_ ?_)
    · rw [Set.setOf_forall]
      refine isOpen_iInter_of_finite fun i => ?_
      rw [Set.setOf_or]
      exact (isOpen_ne_fun (by fun_prop) continuous_const).union
        (isOpen_ne_fun (by fun_prop) continuous_const)
    · rw [Set.setOf_forall]
      exact isOpen_iInter_of_finite fun j => isOpen_lt continuous_const (by fun_prop)
    · rw [Set.setOf_forall]
      refine isOpen_iInter_of_finite fun mH => ?_
      rw [Set.setOf_forall]
      refine isOpen_iInter_of_finite fun mW => ?_
      rw [Set.setOf_and]
      refine IsOpen.inter ?_ ?_
      · rw [Set.setOf_forall]
        refine isOpen_iInter_of_finite fun i => ?_
        by_cases hmi : mH i
        · simp only [hmi, ↓reduceIte]; exact isOpen_lt continuous_const (by fun_prop)
        · simp only [hmi, Bool.false_eq_true, ↓reduceIte]; exact isOpen_lt (by fun_prop) continuous_const
      · rw [Set.setOf_forall]
        refine isOpen_iInter_of_finite fun j => ?_
        by_cases hmj : mW j
        · simp only [hmj, ↓reduceIte]; rw [Set.setOf_and]
          exact (isOpen_lt continuous_const (by fun_prop)).inter (isOpen_lt continuous_const (by fun_prop))
        · simp only [hmj, Bool.false_eq_true, ↓reduceIte]; rw [Set.setOf_or]
          exact (isOpen_lt (by fun_prop) continuous_const).union (isOpen_lt (by fun_prop) continuous_const)
  have hx₀_cond : cond x₀ := by
    refine ⟨fun i => ?_, fun j => ?_, fun mH mW => ⟨fun i => ?_, fun j => ?_⟩⟩
    · fin_cases i
      · simpa [x₀] using (H 0).hn
      · simpa [x₀] using (H 1).hn
    · fin_cases j
      · simpa [x₀] using (R 0).h_nondeg
      · simpa [x₀] using (R 1).h_nondeg
      · simpa [x₀] using (R 2).h_nondeg
    · have hi := (hzm mH mW).1 i
      fin_cases i
      · by_cases hm : mH 0 <;> simp [hm, x₀, OpenHalfPlane.MemPos, OpenHalfPlane.MemNeg] at hi ⊢ <;> exact hi
      · by_cases hm : mH 1 <;> simp [hm, x₀, OpenHalfPlane.MemPos, OpenHalfPlane.MemNeg] at hi ⊢ <;> exact hi
    · have hj := (hzm mH mW).2 j
      fin_cases j
      · by_cases hm : mW 0 <;> simp [hm, x₀, OpenWedge.MemOpen, OpenWedge.MemExt] at hj ⊢ <;> exact hj
      · by_cases hm : mW 1 <;> simp [hm, x₀, OpenWedge.MemOpen, OpenWedge.MemExt] at hj ⊢ <;> exact hj
      · by_cases hm : mW 2 <;> simp [hm, x₀, OpenWedge.MemOpen, OpenWedge.MemExt] at hj ⊢ <;> exact hj
  obtain ⟨δ, hδ_pos, hball⟩ := Metric.isOpen_iff.mp hopen x₀ hx₀_cond
  let pDet : Fin 8 → Fin 8 → MvPolynomial (Fin 24) ℝ := fun i j =>
    MvPolynomial.X (n1Idx i) * MvPolynomial.X (n2Idx j) -
      MvPolynomial.X (n2Idx i) * MvPolynomial.X (n1Idx j)
  have hn_disj : ∀ a b : Fin 8, n1Idx a ≠ n2Idx b := by decide
  have hn1_inj : ∀ a b : Fin 8, a ≠ b → n1Idx a ≠ n1Idx b := by decide
  have hn2_inj : ∀ a b : Fin 8, a ≠ b → n2Idx a ≠ n2Idx b := by decide
  have hpDet_ne : ∀ i j : Fin 8, i ≠ j → pDet i j ≠ 0 := by
    intro i j hij h0
    let w : Fin 24 → ℝ := fun k => if k = n1Idx i ∨ k = n2Idx j then 1 else 0
    have h2i : w (n2Idx i) = 0 := if_neg (fun h => by rcases h with h | h; exact hn_disj i i h.symm; exact hn2_inj i j hij h)
    have h1j : w (n1Idx j) = 0 := if_neg (fun h => by rcases h with h | h; exact hn1_inj j i hij.symm h; exact hn_disj j j h)
    have hev : MvPolynomial.eval w (pDet i j) = 1 := by
      simp only [pDet, map_sub, map_mul, MvPolynomial.eval_X]
      have h1i : w (n1Idx i) = 1 := if_pos (Or.inl rfl)
      have h2j : w (n2Idx j) = 1 := if_pos (Or.inr rfl)
      rw [h1i, h2j, h2i, h1j]
      ring
    have hzero : MvPolynomial.eval w (pDet i j) = 0 := by rw [h0, map_zero]
    linarith
  let P_all : MvPolynomial (Fin 24) ℝ :=
    ∏ i : Fin 8, ∏ j ∈ Finset.univ.filter (fun j : Fin 8 => i < j), pDet i j
  have hP_all : P_all ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i _ =>
      Finset.prod_ne_zero_iff.mpr fun j hj => hpDet_ne i j (ne_of_lt (Finset.mem_filter.mp hj).2)
  obtain ⟨x, hx_box, hx_poly⟩ :=
    SixWedges.poly_dense_box 24 (fun k => x₀ k - δ / 2) (fun k => x₀ k + δ / 2)
      (fun k => by linarith) P_all hP_all
  have hx_dist : dist x x₀ < δ := by
    rw [dist_pi_lt_iff hδ_pos]
    intro k
    have hk := hx_box k
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith [hk.1, hk.2]
  have hx_cond : cond x := hball hx_dist
  let H' : Fin 2 → OpenHalfPlane := fun i =>
    { n := (x ⟨3 * i.1, by omega⟩, x ⟨3 * i.1 + 1, by omega⟩)
      c := x ⟨3 * i.1 + 2, by omega⟩
      hn := hx_cond.1 i }
  let R' : Fin 3 → OpenWedge := fun j =>
    { y := (x ⟨6 + 6 * j.1, by omega⟩, x ⟨6 + 6 * j.1 + 1, by omega⟩)
      u₁ := (x ⟨6 + 6 * j.1 + 2, by omega⟩, x ⟨6 + 6 * j.1 + 3, by omega⟩)
      u₂ := (x ⟨6 + 6 * j.1 + 4, by omega⟩, x ⟨6 + 6 * j.1 + 5, by omega⟩)
      h_nondeg := hx_cond.2.1 j }
  have hpDet_lt_ne : ∀ i j : Fin 8, i < j → MvPolynomial.eval x (pDet i j) ≠ 0 := by
    intro i j hij h0
    apply hx_poly
    dsimp only [P_all]
    rw [map_prod]
    refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
    rw [map_prod]
    exact Finset.prod_eq_zero (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hij⟩) h0
  have hnorm_eq : ∀ i : Fin 8, norm8 H' R' i = (x (n1Idx i), x (n2Idx i)) := by
    intro i; fin_cases i <;> rfl
  have hgp : GP23 H' R' := by
    intro i j hij
    dsimp [SixWedges.det2]
    rw [hnorm_eq i, hnorm_eq j]
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · have hne := hpDet_lt_ne i j hlt
      simpa only [pDet, map_sub, map_mul, MvPolynomial.eval_X] using hne
    · have hne := hpDet_lt_ne j i hgt
      simp only [pDet, map_sub, map_mul, MvPolynomial.eval_X] at hne
      intro heq; apply hne; linarith
  refine ⟨H', R', hgp, fun mH mW => ⟨zm mH mW, fun i => ?_, fun j => ?_⟩⟩
  · have hi := (hx_cond.2.2 mH mW).1 i
    by_cases hm : mH i
    · simp only [hm, ↓reduceIte] at hi ⊢; exact hi
    · simp only [hm, Bool.false_eq_true, ↓reduceIte] at hi ⊢; exact hi
  · have hj := (hx_cond.2.2 mH mW).2 j
    by_cases hm : mW j
    · simp only [hm, ↓reduceIte] at hj ⊢; exact hj
    · simp only [hm, Bool.false_eq_true, ↓reduceIte] at hj ⊢; exact hj

private lemma two_lines_inter_le_one (a1 a2 c1 b1 b2 c2 : ℝ) (hdet : a1 * b2 - a2 * b1 ≠ 0) :
    ∃ p₀ : ℝ × ℝ, ∀ p : ℝ × ℝ, a1 * p.1 + a2 * p.2 + c1 = 0 → b1 * p.1 + b2 * p.2 + c2 = 0 → p = p₀ := by
  let det := a1 * b2 - a2 * b1
  refine ⟨((-b2 * c1 + a2 * c2) / det, (b1 * c1 - a1 * c2) / det), fun p hp1 hp2 => ?_⟩
  have hx : det * p.1 = -b2 * c1 + a2 * c2 := by
    dsimp [det]; linear_combination b2 * hp1 - a2 * hp2
  have hy : det * p.2 = b1 * c1 - a1 * c2 := by
    dsimp [det]; linear_combination -b1 * hp1 + a1 * hp2
  ext
  · exact (eq_div_iff hdet).mpr (by rw [mul_comm]; exact hx)
  · exact (eq_div_iff hdet).mpr (by rw [mul_comm]; exact hy)

private lemma bdHP_inter_bdHP_le_one {h₁ h₂ : OpenHalfPlane}
    (hdet : SixWedges.det2 h₁.n h₂.n ≠ 0) :
    (bdHP h₁ ∩ bdHP h₂).Finite ∧ (bdHP h₁ ∩ bdHP h₂).ncard ≤ 1 := by
  obtain ⟨p₀, hp₀⟩ := two_lines_inter_le_one h₁.n.1 h₁.n.2 h₁.c h₂.n.1 h₂.n.2 h₂.c hdet
  have hsub : bdHP h₁ ∩ bdHP h₂ ⊆ ({p₀} : Set (ℝ × ℝ)) := fun p ⟨hp1, hp2⟩ => by
    rw [Set.mem_singleton_iff]
    exact hp₀ p hp1 hp2
  refine ⟨(Set.finite_singleton p₀).subset hsub, ?_⟩
  calc (bdHP h₁ ∩ bdHP h₂).ncard ≤ ({p₀} : Set (ℝ × ℝ)).ncard :=
        Set.ncard_le_ncard hsub (Set.finite_singleton p₀)
    _ = 1 := Set.ncard_singleton p₀

private lemma bdWedge_inter_bdHP_le_two {W : OpenWedge} {h : OpenHalfPlane}
    (hdet1 : SixWedges.det2 W.u₁ h.n ≠ 0) (hdet2 : SixWedges.det2 W.u₂ h.n ≠ 0) :
    (SixWedges.bdWedge W ∩ bdHP h).Finite ∧ (SixWedges.bdWedge W ∩ bdHP h).ncard ≤ 2 := by
  obtain ⟨p₁, hp₁⟩ := two_lines_inter_le_one W.u₁.1 W.u₁.2 (-(W.u₁.1 * W.y.1 + W.u₁.2 * W.y.2))
    h.n.1 h.n.2 h.c hdet1
  obtain ⟨p₂, hp₂⟩ := two_lines_inter_le_one W.u₂.1 W.u₂.2 (-(W.u₂.1 * W.y.1 + W.u₂.2 * W.y.2))
    h.n.1 h.n.2 h.c hdet2
  let S2 : Finset (ℝ × ℝ) := {p₁, p₂}
  have hsub : SixWedges.bdWedge W ∩ bdHP h ⊆ (S2 : Set (ℝ × ℝ)) := by
    rintro p ⟨hpW, hph⟩
    obtain ⟨_, h_eq⟩ := (SixWedges.bdWedge_iff_closure_eq_zero W p).mp hpW
    rcases h_eq with hw1 | hw2
    · have := hp₁ p (by linear_combination hw1) hph
      simp [S2, this]
    · have := hp₂ p (by linear_combination hw2) hph
      simp [S2, this]
  refine ⟨S2.finite_toSet.subset hsub, ?_⟩
  calc (SixWedges.bdWedge W ∩ bdHP h).ncard ≤ (S2 : Set (ℝ × ℝ)).ncard :=
        Set.ncard_le_ncard hsub S2.finite_toSet
    _ = S2.card := Set.ncard_coe_finset S2
    _ ≤ 2 := Finset.card_le_two

private lemma bdWedge_inter_bdWedge_le_four {W₁ W₂ : OpenWedge}
    (h11 : SixWedges.det2 W₁.u₁ W₂.u₁ ≠ 0) (h12 : SixWedges.det2 W₁.u₁ W₂.u₂ ≠ 0)
    (h21 : SixWedges.det2 W₁.u₂ W₂.u₁ ≠ 0) (h22 : SixWedges.det2 W₁.u₂ W₂.u₂ ≠ 0) :
    (SixWedges.bdWedge W₁ ∩ SixWedges.bdWedge W₂).Finite ∧
      (SixWedges.bdWedge W₁ ∩ SixWedges.bdWedge W₂).ncard ≤ 4 := by
  obtain ⟨p11, hp11⟩ := two_lines_inter_le_one W₁.u₁.1 W₁.u₁.2 (-(W₁.u₁.1 * W₁.y.1 + W₁.u₁.2 * W₁.y.2))
    W₂.u₁.1 W₂.u₁.2 (-(W₂.u₁.1 * W₂.y.1 + W₂.u₁.2 * W₂.y.2)) h11
  obtain ⟨p12, hp12⟩ := two_lines_inter_le_one W₁.u₁.1 W₁.u₁.2 (-(W₁.u₁.1 * W₁.y.1 + W₁.u₁.2 * W₁.y.2))
    W₂.u₂.1 W₂.u₂.2 (-(W₂.u₂.1 * W₂.y.1 + W₂.u₂.2 * W₂.y.2)) h12
  obtain ⟨p21, hp21⟩ := two_lines_inter_le_one W₁.u₂.1 W₁.u₂.2 (-(W₁.u₂.1 * W₁.y.1 + W₁.u₂.2 * W₁.y.2))
    W₂.u₁.1 W₂.u₁.2 (-(W₂.u₁.1 * W₂.y.1 + W₂.u₁.2 * W₂.y.2)) h21
  obtain ⟨p22, hp22⟩ := two_lines_inter_le_one W₁.u₂.1 W₁.u₂.2 (-(W₁.u₂.1 * W₁.y.1 + W₁.u₂.2 * W₁.y.2))
    W₂.u₂.1 W₂.u₂.2 (-(W₂.u₂.1 * W₂.y.1 + W₂.u₂.2 * W₂.y.2)) h22
  let S4 : Finset (ℝ × ℝ) := {p11, p12, p21, p22}
  have hsub : SixWedges.bdWedge W₁ ∩ SixWedges.bdWedge W₂ ⊆ (S4 : Set (ℝ × ℝ)) := by
    rintro p ⟨hW1, hW2⟩
    obtain ⟨_, h1⟩ := (SixWedges.bdWedge_iff_closure_eq_zero W₁ p).mp hW1
    obtain ⟨_, h2⟩ := (SixWedges.bdWedge_iff_closure_eq_zero W₂ p).mp hW2
    rcases h1 with hw1 | hw1 <;> rcases h2 with hw2 | hw2
    · have := hp11 p (by linear_combination hw1) (by linear_combination hw2); simp [S4, this]
    · have := hp12 p (by linear_combination hw1) (by linear_combination hw2); simp [S4, this]
    · have := hp21 p (by linear_combination hw1) (by linear_combination hw2); simp [S4, this]
    · have := hp22 p (by linear_combination hw1) (by linear_combination hw2); simp [S4, this]
  refine ⟨S4.finite_toSet.subset hsub, ?_⟩
  calc (SixWedges.bdWedge W₁ ∩ SixWedges.bdWedge W₂).ncard ≤ (S4 : Set (ℝ × ℝ)).ncard :=
        Set.ncard_le_ncard hsub S4.finite_toSet
    _ = S4.card := Set.ncard_coe_finset S4
    _ ≤ 4 := (Finset.card_insert_le _ _).trans (Nat.succ_le_succ
        ((Finset.card_insert_le _ _).trans (Nat.succ_le_succ
          ((Finset.card_insert_le _ _).trans (Nat.succ_le_succ (by simp))))))

private lemma comp_ne_of_sep_halfplane {U : Set (ℝ × ℝ)} {h : OpenHalfPlane}
    (hdisj : ∀ p ∈ bdHP h, p ∉ U) {p₁ p₂ : ℝ × ℝ} (hp₁ : p₁ ∈ U) (hp₂ : p₂ ∈ U)
    (hsep : (h.MemPos p₁ ∧ h.MemNeg p₂) ∨ (h.MemNeg p₁ ∧ h.MemPos p₂)) :
    connectedComponentIn U p₁ ≠ connectedComponentIn U p₂ := by
  intro heq
  let C : Set (ℝ × ℝ) := connectedComponentIn U p₁
  have hC_conn : IsPreconnected C := isPreconnected_connectedComponentIn
  have hp1C : p₁ ∈ C := mem_connectedComponentIn hp₁
  have hp2C : p₂ ∈ C := by dsimp [C]; rw [heq]; exact mem_connectedComponentIn hp₂
  have hC_sub : C ⊆ {q | h.MemPos q} ∪ {q | h.MemNeg q} := by
    intro q hq
    have hqU : q ∈ U := connectedComponentIn_subset U p₁ hq
    have hq_nbd : q ∉ bdHP h := fun hbd => hdisj q hbd hqU
    change h.n.1 * q.1 + h.n.2 * q.2 + h.c ≠ 0 at hq_nbd
    rcases lt_or_gt_of_ne hq_nbd with hlt | hgt
    · exact Or.inr hlt
    · exact Or.inl hgt
  have h_empty : (C ∩ ({q | h.MemPos q} ∩ {q | h.MemNeg q})).Nonempty → False := by
    rintro ⟨q, _, hpos, hneg⟩
    change 0 < h.n.1 * q.1 + h.n.2 * q.2 + h.c at hpos
    change h.n.1 * q.1 + h.n.2 * q.2 + h.c < 0 at hneg
    linarith
  rcases hC_conn {q | h.MemPos q} {q | h.MemNeg q} (isOpen_memPos h) (isOpen_memNeg h) hC_sub
      (by rcases hsep with ⟨h1, _⟩ | ⟨_, h2⟩; exacts [⟨p₁, hp1C, h1⟩, ⟨p₂, hp2C, h2⟩])
      (by rcases hsep with ⟨_, h2⟩ | ⟨h1, _⟩; exacts [⟨p₂, hp2C, h2⟩, ⟨p₁, hp1C, h1⟩]) with
    ⟨q, hqC, hqpos, hqneg⟩
  exact h_empty ⟨q, hqC, hqpos, hqneg⟩

theorem two_hp_three_wedges_not_all_32 (H : Fin 2 → OpenHalfPlane) (R : Fin 3 → OpenWedge) :
    ¬ (∀ (mH : Fin 2 → Bool) (mW : Fin 3 → Bool), ∃ p : ℝ × ℝ,
      (∀ i : Fin 2, if mH i then (H i).MemPos p else (H i).MemNeg p) ∧
      (∀ j : Fin 3, if mW j then (R j).MemOpen p else (R j).MemExt p)) := by
  intro h_all
  obtain ⟨H', R', hgp, h_all'⟩ := exists_gp23_perturbation H R h_all
  choose pm hpm using h_all'
  let K1 : Set (ℝ × ℝ) := bdHP (H' 0)
  let K2 : Set (ℝ × ℝ) := K1 ∪ bdHP (H' 1)
  let K3 : Set (ℝ × ℝ) := K2 ∪ SixWedges.bdWedge (R' 0)
  let K4 : Set (ℝ × ℝ) := K3 ∪ SixWedges.bdWedge (R' 1)
  let K5 : Set (ℝ × ℝ) := K4 ∪ SixWedges.bdWedge (R' 2)
  have hK1_cl : IsClosed K1 := bdHP_isClosed (H' 0)
  have hK2_cl : IsClosed K2 := hK1_cl.union (bdHP_isClosed (H' 1))
  have hK3_cl : IsClosed K3 := hK2_cl.union (SixWedges.bdWedge_isClosed (R' 0))
  have hK4_cl : IsClosed K4 := hK3_cl.union (SixWedges.bdWedge_isClosed (R' 1))
  -- Intersection bounds
  have h10 := bdHP_inter_bdHP_le_one (hgp 1 0 (by decide))
  have h2_0 := bdWedge_inter_bdHP_le_two (hgp 2 0 (by decide)) (hgp 3 0 (by decide))
  have h2_1 := bdWedge_inter_bdHP_le_two (hgp 2 1 (by decide)) (hgp 3 1 (by decide))
  have h3_0 := bdWedge_inter_bdHP_le_two (hgp 4 0 (by decide)) (hgp 5 0 (by decide))
  have h3_1 := bdWedge_inter_bdHP_le_two (hgp 4 1 (by decide)) (hgp 5 1 (by decide))
  have h3_2 := bdWedge_inter_bdWedge_le_four (hgp 4 2 (by decide)) (hgp 4 3 (by decide))
    (hgp 5 2 (by decide)) (hgp 5 3 (by decide))
  have h4_0 := bdWedge_inter_bdHP_le_two (hgp 6 0 (by decide)) (hgp 7 0 (by decide))
  have h4_1 := bdWedge_inter_bdHP_le_two (hgp 6 1 (by decide)) (hgp 7 1 (by decide))
  have h4_2 := bdWedge_inter_bdWedge_le_four (hgp 6 2 (by decide)) (hgp 6 3 (by decide))
    (hgp 7 2 (by decide)) (hgp 7 3 (by decide))
  have h4_3 := bdWedge_inter_bdWedge_le_four (hgp 6 4 (by decide)) (hgp 6 5 (by decide))
    (hgp 7 4 (by decide)) (hgp 7 5 (by decide))
  -- Step 1: univ \ K1 ≤ 2
  have h_b1 : (SixWedges.Comps ((Set.univ : Set (ℝ × ℝ)) \ K1)).encard ≤ 2 := by
    have h0 := add_line_comps_bound (H' 0) ∅ isClosed_empty (by simp)
    simp only [Set.empty_union, Set.sdiff_empty, Set.inter_empty, Set.ncard_empty, zero_add] at h0
    rw [SixWedges.comps_univ_card] at h0
    exact h0.trans (by norm_num)
  -- Step 2: univ \ K2 ≤ 4
  have h_b2 : (SixWedges.Comps ((Set.univ : Set (ℝ × ℝ)) \ K2)).encard ≤ 4 := by
    have h1 := add_line_comps_bound (H' 1) K1 hK1_cl h10.1
    have hnc : (bdHP (H' 1) ∩ K1).ncard ≤ 1 := h10.2
    calc (SixWedges.Comps ((Set.univ : Set (ℝ × ℝ)) \ K2)).encard
        ≤ (SixWedges.Comps ((Set.univ : Set (ℝ × ℝ)) \ K1)).encard +
            ((bdHP (H' 1) ∩ K1).ncard + 1 : ℕ) := h1
      _ ≤ 2 + ((1 + 1 : ℕ) : ℕ∞) := add_le_add h_b1 (Nat.cast_le.mpr (by omega))
      _ = 4 := by norm_num
  -- Step 3: univ \ K3 ≤ 9
  have h_b3 : (SixWedges.Comps ((Set.univ : Set (ℝ × ℝ)) \ K3)).encard ≤ 9 := by
    have heq : SixWedges.bdWedge (R' 0) ∩ K2 =
        (SixWedges.bdWedge (R' 0) ∩ bdHP (H' 0)) ∪ (SixWedges.bdWedge (R' 0) ∩ bdHP (H' 1)) := by
      ext p; simp [K2, K1, Set.inter_union_distrib_left]
    have hfin : (SixWedges.bdWedge (R' 0) ∩ K2).Finite := heq ▸ (h2_0.1.union h2_1.1)
    have hnc : (SixWedges.bdWedge (R' 0) ∩ K2).ncard ≤ 4 := by
      rw [heq]
      have ha := h2_0.2; have hb := h2_1.2
      exact (Set.ncard_union_le _ _).trans (by omega)
    have h2 := add_wedge_comps_bound (R' 0) K2 hK2_cl hfin
    calc (SixWedges.Comps ((Set.univ : Set (ℝ × ℝ)) \ K3)).encard
        ≤ (SixWedges.Comps ((Set.univ : Set (ℝ × ℝ)) \ K2)).encard +
            ((SixWedges.bdWedge (R' 0) ∩ K2).ncard + 1 : ℕ) := h2
      _ ≤ 4 + ((4 + 1 : ℕ) : ℕ∞) := add_le_add h_b2 (Nat.cast_le.mpr (by omega))
      _ = 9 := by norm_num
  -- Step 4: univ \ K4 ≤ 18
  have h_b4 : (SixWedges.Comps ((Set.univ : Set (ℝ × ℝ)) \ K4)).encard ≤ 18 := by
    have heq : SixWedges.bdWedge (R' 1) ∩ K3 =
        ((SixWedges.bdWedge (R' 1) ∩ bdHP (H' 0)) ∪ (SixWedges.bdWedge (R' 1) ∩ bdHP (H' 1))) ∪
          (SixWedges.bdWedge (R' 1) ∩ SixWedges.bdWedge (R' 0)) := by
      ext p; simp [K3, K2, K1, Set.inter_union_distrib_left, union_assoc]
    have hfin : (SixWedges.bdWedge (R' 1) ∩ K3).Finite :=
      heq ▸ ((h3_0.1.union h3_1.1).union h3_2.1)
    have hnc : (SixWedges.bdWedge (R' 1) ∩ K3).ncard ≤ 8 := by
      rw [heq]
      have ha := h3_0.2; have hb := h3_1.2; have hc := h3_2.2
      have h12 := Set.ncard_union_le (SixWedges.bdWedge (R' 1) ∩ bdHP (H' 0))
        (SixWedges.bdWedge (R' 1) ∩ bdHP (H' 1))
      have h123 := Set.ncard_union_le
        ((SixWedges.bdWedge (R' 1) ∩ bdHP (H' 0)) ∪ (SixWedges.bdWedge (R' 1) ∩ bdHP (H' 1)))
        (SixWedges.bdWedge (R' 1) ∩ SixWedges.bdWedge (R' 0))
      omega
    have h3 := add_wedge_comps_bound (R' 1) K3 hK3_cl hfin
    calc (SixWedges.Comps ((Set.univ : Set (ℝ × ℝ)) \ K4)).encard
        ≤ (SixWedges.Comps ((Set.univ : Set (ℝ × ℝ)) \ K3)).encard +
            ((SixWedges.bdWedge (R' 1) ∩ K3).ncard + 1 : ℕ) := h3
      _ ≤ 9 + ((8 + 1 : ℕ) : ℕ∞) := add_le_add h_b3 (Nat.cast_le.mpr (by omega))
      _ = 18 := by norm_num
  -- Step 5: univ \ K5 ≤ 31
  have h_b5 : (SixWedges.Comps ((Set.univ : Set (ℝ × ℝ)) \ K5)).encard ≤ 31 := by
    have heq : SixWedges.bdWedge (R' 2) ∩ K4 =
        (((SixWedges.bdWedge (R' 2) ∩ bdHP (H' 0)) ∪ (SixWedges.bdWedge (R' 2) ∩ bdHP (H' 1))) ∪
          (SixWedges.bdWedge (R' 2) ∩ SixWedges.bdWedge (R' 0))) ∪
            (SixWedges.bdWedge (R' 2) ∩ SixWedges.bdWedge (R' 1)) := by
      ext p; simp [K4, K3, K2, K1, Set.inter_union_distrib_left, union_assoc]
    have hfin : (SixWedges.bdWedge (R' 2) ∩ K4).Finite :=
      heq ▸ (((h4_0.1.union h4_1.1).union h4_2.1).union h4_3.1)
    have hnc : (SixWedges.bdWedge (R' 2) ∩ K4).ncard ≤ 12 := by
      rw [heq]
      have ha := h4_0.2; have hb := h4_1.2; have hc := h4_2.2; have hd := h4_3.2
      have h12 := Set.ncard_union_le (SixWedges.bdWedge (R' 2) ∩ bdHP (H' 0))
        (SixWedges.bdWedge (R' 2) ∩ bdHP (H' 1))
      have h123 := Set.ncard_union_le
        ((SixWedges.bdWedge (R' 2) ∩ bdHP (H' 0)) ∪ (SixWedges.bdWedge (R' 2) ∩ bdHP (H' 1)))
        (SixWedges.bdWedge (R' 2) ∩ SixWedges.bdWedge (R' 0))
      have h1234 := Set.ncard_union_le
        (((SixWedges.bdWedge (R' 2) ∩ bdHP (H' 0)) ∪ (SixWedges.bdWedge (R' 2) ∩ bdHP (H' 1))) ∪
          (SixWedges.bdWedge (R' 2) ∩ SixWedges.bdWedge (R' 0)))
        (SixWedges.bdWedge (R' 2) ∩ SixWedges.bdWedge (R' 1))
      omega
    have h4 := add_wedge_comps_bound (R' 2) K4 hK4_cl hfin
    calc (SixWedges.Comps ((Set.univ : Set (ℝ × ℝ)) \ K5)).encard
        ≤ (SixWedges.Comps ((Set.univ : Set (ℝ × ℝ)) \ K4)).encard +
            ((SixWedges.bdWedge (R' 2) ∩ K4).ncard + 1 : ℕ) := h4
      _ ≤ 18 + ((12 + 1 : ℕ) : ℕ∞) := add_le_add h_b4 (Nat.cast_le.mpr (by omega))
      _ = 31 := by norm_num
  -- All 32 points lie in distinct connected components of U := univ \ K5
  let U : Set (ℝ × ℝ) := Set.univ \ K5
  have hpm_mem : ∀ m : (Fin 2 → Bool) × (Fin 3 → Bool), pm m.1 m.2 ∈ U := fun m => by
    refine ⟨trivial, fun hK => ?_⟩
    rcases hK with (((h0 | h1) | r0) | r1) | r2
    · have hi := (hpm m.1 m.2).1 0
      change (H' 0).n.1 * _ + (H' 0).n.2 * _ + (H' 0).c = 0 at h0
      cases hm : m.1 0 <;> simp [hm, OpenHalfPlane.MemPos, OpenHalfPlane.MemNeg] at hi <;> linarith
    · have hi := (hpm m.1 m.2).1 1
      change (H' 1).n.1 * _ + (H' 1).n.2 * _ + (H' 1).c = 0 at h1
      cases hm : m.1 1 <;> simp [hm, OpenHalfPlane.MemPos, OpenHalfPlane.MemNeg] at hi <;> linarith
    · have hj := (hpm m.1 m.2).2 0
      cases hm : m.2 0 <;> simp [hm] at hj
      · exact r0.2 hj
      · exact r0.1 hj
    · have hj := (hpm m.1 m.2).2 1
      cases hm : m.2 1 <;> simp [hm] at hj
      · exact r1.2 hj
      · exact r1.1 hj
    · have hj := (hpm m.1 m.2).2 2
      cases hm : m.2 2 <;> simp [hm] at hj
      · exact r2.2 hj
      · exact r2.1 hj
  let f : ((Fin 2 → Bool) × (Fin 3 → Bool)) → Set (ℝ × ℝ) := fun m =>
    connectedComponentIn U (pm m.1 m.2)
  have hf_inj : Function.Injective f := by
    intro m₁ m₂ heq
    by_contra hne
    have hdiff : (∃ i : Fin 2, m₁.1 i ≠ m₂.1 i) ∨ (∃ j : Fin 3, m₁.2 j ≠ m₂.2 j) := by
      by_contra hnot; push Not at hnot
      exact hne (Prod.ext (funext hnot.1) (funext hnot.2))
    rcases hdiff with ⟨i, hi⟩ | ⟨j, hj⟩
    · have hdisj : ∀ p ∈ bdHP (H' i), p ∉ U := fun p hp hpU => hpU.2 (by
        fin_cases i
        · exact Or.inl (Or.inl (Or.inl (Or.inl hp)))
        · exact Or.inl (Or.inl (Or.inl (Or.inr hp))))
      have h1 := (hpm m₁.1 m₁.2).1 i
      have h2 := (hpm m₂.1 m₂.2).1 i
      apply comp_ne_of_sep_halfplane hdisj (hpm_mem m₁) (hpm_mem m₂) _ heq
      cases hm1 : m₁.1 i <;> cases hm2 : m₂.1 i
      · exact False.elim (hi (hm1.trans hm2.symm))
      · simp only [hm1, Bool.false_eq_true, ↓reduceIte] at h1
        simp only [hm2, ↓reduceIte] at h2
        exact Or.inr ⟨h1, h2⟩
      · simp only [hm1, ↓reduceIte] at h1
        simp only [hm2, Bool.false_eq_true, ↓reduceIte] at h2
        exact Or.inl ⟨h1, h2⟩
      · exact False.elim (hi (hm1.trans hm2.symm))
    · have hdisj : ∀ p ∈ SixWedges.bdWedge (R' j), p ∉ U := fun p hp hpU => hpU.2 (by
        fin_cases j
        · exact Or.inl (Or.inl (Or.inr hp))
        · exact Or.inl (Or.inr hp)
        · exact Or.inr hp)
      have h1 := (hpm m₁.1 m₁.2).2 j
      have h2 := (hpm m₂.1 m₂.2).2 j
      apply SixWedges.comp_ne_of_sep_any_wedge hdisj (hpm_mem m₁) (hpm_mem m₂) _ heq
      cases hm1 : m₁.2 j <;> cases hm2 : m₂.2 j
      · exact False.elim (hj (hm1.trans hm2.symm))
      · simp only [hm1, Bool.false_eq_true, ↓reduceIte] at h1
        simp only [hm2, ↓reduceIte] at h2
        exact Or.inr ⟨h1, h2⟩
      · simp only [hm1, ↓reduceIte] at h1
        simp only [hm2, Bool.false_eq_true, ↓reduceIte] at h2
        exact Or.inl ⟨h1, h2⟩
      · exact False.elim (hj (hm1.trans hm2.symm))
  have hf_sub : Set.range f ⊆ SixWedges.Comps U := by
    rintro _ ⟨m, rfl⟩; exact ⟨pm m.1 m.2, hpm_mem m, rfl⟩
  have h32 : (32 : ℕ∞) ≤ (SixWedges.Comps U).encard := by
    calc (32 : ℕ∞)
        = (Fintype.card ((Fin 2 → Bool) × (Fin 3 → Bool)) : ℕ∞) := by norm_num [Fintype.card_prod, Fintype.card_fun]
      _ = (Set.univ : Set ((Fin 2 → Bool) × (Fin 3 → Bool))).encard := by
          rw [Set.encard_univ, ENat.card_eq_coe_fintype_card]
      _ = (f '' Set.univ).encard := (hf_inj.injOn.encard_image).symm
      _ = (Set.range f).encard := by rw [Set.image_univ]
      _ ≤ (SixWedges.Comps U).encard := Set.encard_le_encard hf_sub
  have h32_le_31 : (32 : ℕ∞) ≤ 31 := h32.trans h_b5
  have hnat : (32 : ℕ) ≤ 31 := Nat.cast_le.mp h32_le_31
  omega

end ArrangementBounds

end
