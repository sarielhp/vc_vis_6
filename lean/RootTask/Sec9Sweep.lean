import Mathlib
import RootTask.Defs
import RootTask.Sec9Perturb
import RootTask.Sec9Dual

open scoped Classical BigOperators
open Finset

noncomputable section

namespace Sec9

/-- Bundled generic V-function system obtained from `exists_generic_v_system`. -/
structure GenericVSystem where
  f : Fin 5 → VFunc
  ac : ∀ i : Fin 5, (f i).a < (f i).c
  a_mono : StrictMono (fun i : Fin 5 => (f i).a)
  slopes_inj : Function.Injective (fun k : Fin 5 × Bool => (dualPt f k).1)
  noncol : ∀ p q r : Fin 5 × Bool, p ≠ q → q ≠ r → p ≠ r →
    ((dualPt f q).1 - (dualPt f p).1) * ((dualPt f r).2 - (dualPt f p).2) -
    ((dualPt f q).2 - (dualPt f p).2) * ((dualPt f r).1 - (dualPt f p).1) ≠ 0
  dual : ∀ S : Finset (Fin 5), ∃ s t : ℝ, DualRealizes f S s t
  realizes : ∀ m : Fin 5 → Bool, ∃ p : ℝ × ℝ, RealizesVMask f m p
  gpa_kinks : ∀ i j : Fin 5, i ≠ j → kink f i ≠ kink f j
  gpa_vals : ∀ i j : Fin 5, i ≠ j → (f i).eval (kink f i) ≠ (f j).eval (kink f i)
  gpb_disj : ∀ i j k l : Fin 5, i < j → k < l → (i, j) ≠ (k, l) → ∀ x : ℝ,
    ¬ ((f i).eval x = (f j).eval x ∧ (f k).eval x = (f l).eval x)
  gpb_kink : ∀ i j m : Fin 5, i < j → (f i).eval (kink f m) ≠ (f j).eval (kink f m)

lemma continuous_eval_vfunc (g : VFunc) : Continuous g.eval := by
  unfold VFunc.eval
  exact Continuous.max ((continuous_const.mul continuous_id).add continuous_const)
    ((continuous_const.mul continuous_id).add continuous_const)

lemma VFunc.eval_left (g : VFunc) (h : g.a < g.c) {x : ℝ} (hx : x ≤ (g.b - g.d) / (g.c - g.a)) :
    g.eval x = g.a * x + g.b := by
  unfold VFunc.eval
  apply max_eq_left
  have hpos : 0 < g.c - g.a := sub_pos.mpr h
  have h1 : x * (g.c - g.a) ≤ g.b - g.d := (le_div_iff₀ hpos).mp hx
  linarith

lemma VFunc.eval_right (g : VFunc) (h : g.a < g.c) {x : ℝ} (hx : (g.b - g.d) / (g.c - g.a) ≤ x) :
    g.eval x = g.c * x + g.d := by
  unfold VFunc.eval
  apply max_eq_right
  have hpos : 0 < g.c - g.a := sub_pos.mpr h
  have h1 : g.b - g.d ≤ x * (g.c - g.a) := (div_le_iff₀ hpos).mp hx
  linarith

lemma VFunc.eval_branch_le (g : VFunc) (x : ℝ) :
    g.a * x + g.b ≤ g.eval x ∧ g.c * x + g.d ≤ g.eval x :=
  ⟨le_max_left _ _, le_max_right _ _⟩

/-- Candidate crossing points of `f i` and `f j` (`i < j`). -/
def candPts (f : Fin 5 → VFunc) (i j : Fin 5) : Finset ℝ :=
  (Finset.univ : Finset (Bool × Bool)).image (fun p =>
    ((dualPt f (j, p.2)).2 - (dualPt f (i, p.1)).2) /
    ((dualPt f (i, p.1)).1 - (dualPt f (j, p.2)).1))

/-- Finite set of crossing abscissae `Z_{ij} = {x | f_i(x) = f_j(x)}` for `i < j`. -/
def Z_set (f : Fin 5 → VFunc) (i j : Fin 5) : Finset ℝ :=
  (candPts f i j).filter (fun x => (f i).eval x = (f j).eval x)

lemma mem_Z_set (G : GenericVSystem) {i j : Fin 5} (hij : i < j) (x : ℝ) :
    x ∈ Z_set G.f i j ↔ (G.f i).eval x = (G.f j).eval x := by
  constructor
  · intro hx; exact (Finset.mem_filter.mp hx).2
  · intro heq
    refine Finset.mem_filter.mpr ⟨?_, heq⟩
    have branch : ∀ c : Fin 5, ∃ b : Bool,
        (G.f c).eval x = (dualPt G.f (c, b)).1 * x + (dualPt G.f (c, b)).2 := by
      intro c; unfold VFunc.eval
      rcases le_total ((G.f c).a * x + (G.f c).b) ((G.f c).c * x + (G.f c).d) with h | h
      · rw [max_eq_right h]; exact ⟨true, rfl⟩
      · rw [max_eq_left h]; exact ⟨false, rfl⟩
    obtain ⟨b1, hb1⟩ := branch i
    obtain ⟨b2, hb2⟩ := branch j
    refine Finset.mem_image.mpr ⟨(b1, b2), Finset.mem_univ _, ?_⟩
    have hne_pt : (i, b1) ≠ (j, b2) := fun h => (ne_of_lt hij) (congrArg Prod.fst h)
    have hne_s : (dualPt G.f (i, b1)).1 - (dualPt G.f (j, b2)).1 ≠ 0 :=
      sub_ne_zero.mpr (fun h => hne_pt (G.slopes_inj h))
    rw [div_eq_iff hne_s]
    linarith

lemma Z_set_inv_spec (G : GenericVSystem) {i j : Fin 5} (hij : i < j)
    (hinv : (G.f j).c < (G.f i).c) :
    (Z_set G.f i j).card = 2 ∧ (G.f i).eval (kink G.f i) < (G.f j).eval (kink G.f i) := by
  have ha_lt : (G.f i).a < (G.f j).a := G.a_mono hij
  have hai_lt_cj : (G.f i).a < (G.f j).c := lt_trans ha_lt (G.ac j)
  have haj_lt_ci : (G.f j).a < (G.f i).c := lt_trans (G.ac j) hinv
  have hdec : ∀ x₁ x₂ : ℝ, x₁ < x₂ → x₂ ≤ kink G.f i →
      (G.f i).eval x₂ - (G.f j).eval x₂ < (G.f i).eval x₁ - (G.f j).eval x₁ := by
    intro x₁ x₂ h12 hx2
    have hx1 : x₁ ≤ kink G.f i := le_trans (le_of_lt h12) hx2
    rw [VFunc.eval_left (G.f i) (G.ac i) hx1, VFunc.eval_left (G.f i) (G.ac i) hx2]
    unfold VFunc.eval
    rcases le_total ((G.f j).a * x₁ + (G.f j).b) ((G.f j).c * x₁ + (G.f j).d) with h | h
    · rw [max_eq_right h]
      have hle := le_max_right ((G.f j).a * x₂ + (G.f j).b) ((G.f j).c * x₂ + (G.f j).d)
      nlinarith
    · rw [max_eq_left h]
      have hle := le_max_left ((G.f j).a * x₂ + (G.f j).b) ((G.f j).c * x₂ + (G.f j).d)
      nlinarith
  have hinc : ∀ x₁ x₂ : ℝ, kink G.f i ≤ x₁ → x₁ < x₂ →
      (G.f i).eval x₁ - (G.f j).eval x₁ < (G.f i).eval x₂ - (G.f j).eval x₂ := by
    intro x₁ x₂ hx1 h12
    have hx2 : kink G.f i ≤ x₂ := le_trans hx1 (le_of_lt h12)
    rw [VFunc.eval_right (G.f i) (G.ac i) hx1, VFunc.eval_right (G.f i) (G.ac i) hx2]
    unfold VFunc.eval
    rcases le_total ((G.f j).a * x₂ + (G.f j).b) ((G.f j).c * x₂ + (G.f j).d) with h | h
    · rw [max_eq_right h]
      have hle := le_max_right ((G.f j).a * x₁ + (G.f j).b) ((G.f j).c * x₁ + (G.f j).d)
      nlinarith
    · rw [max_eq_left h]
      have hle := le_max_left ((G.f j).a * x₁ + (G.f j).b) ((G.f j).c * x₁ + (G.f j).d)
      nlinarith
  have hkink_lt : (G.f i).eval (kink G.f i) < (G.f j).eval (kink G.f i) := by
    rcases lt_or_gt_of_ne (G.gpa_vals i j (ne_of_lt hij)) with hlt | hgt
    · exact hlt
    · exfalso
      let m : Fin 5 → Bool := fun k => decide (k = i)
      obtain ⟨⟨x, y⟩, hm⟩ := G.realizes m
      have hmi : (G.f i).eval x < y := by simpa [m] using hm i
      have hmj : y < (G.f j).eval x := by simpa [m, ne_of_gt hij] using hm j
      have hle : (G.f j).eval x < (G.f i).eval x := by
        rcases lt_trichotomy x (kink G.f i) with hx | rfl | hx
        · have := hdec x (kink G.f i) hx le_rfl; linarith
        · exact hgt
        · have := hinc (kink G.f i) x le_rfl hx; linarith
      linarith
  -- Find `M_neg < kink f i` and `kink f i < M_pos` where `f j < f i`
  have hex_neg : ∃ xL : ℝ, xL < kink G.f i ∧ (G.f j).eval xL < (G.f i).eval xL := by
    let num : ℝ := max ((G.f j).b - (G.f i).b) ((G.f j).d - (G.f i).b)
    let den : ℝ := min ((G.f j).a - (G.f i).a) ((G.f j).c - (G.f i).a)
    have hden_pos : 0 < den := lt_min (sub_pos.mpr ha_lt) (sub_pos.mpr hai_lt_cj)
    let xL : ℝ := min (kink G.f i - 1) (-|num| / den - 1)
    have hxL_lt : xL < kink G.f i := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    refine ⟨xL, hxL_lt, ?_⟩
    rw [VFunc.eval_left (G.f i) (G.ac i) (le_of_lt hxL_lt)]
    have hxL_bound : xL ≤ -|num| / den - 1 := min_le_right _ _
    have hxL_nonpos : xL < 0 := by
      have h0 : 0 ≤ |num| / den := div_nonneg (abs_nonneg _) (le_of_lt hden_pos)
      rw [neg_div] at hxL_bound
      linarith [hxL_bound]
    have hmul1 : xL * ((G.f j).a - (G.f i).a) ≤ xL * den :=
      mul_le_mul_of_nonpos_left (min_le_left _ _) (le_of_lt hxL_nonpos)
    have hmul2 : xL * ((G.f j).c - (G.f i).c + ((G.f i).c - (G.f i).a)) ≤ xL * den := by
      have : (G.f j).c - (G.f i).c + ((G.f i).c - (G.f i).a) = (G.f j).c - (G.f i).a := by ring
      rw [this]
      exact mul_le_mul_of_nonpos_left (min_le_right _ _) (le_of_lt hxL_nonpos)
    have hxd : xL * den ≤ -|num| - den := by
      have h1 := mul_le_mul_of_nonneg_right hxL_bound (le_of_lt hden_pos)
      have h2 : (-|num| / den - 1) * den = -|num| - den := by field_simp [ne_of_gt hden_pos]
      linarith
    have hb1 : (G.f j).b - (G.f i).b ≤ |num| := le_trans (le_max_left _ _) (le_abs_self _)
    have hb2 : (G.f j).d - (G.f i).b ≤ |num| := le_trans (le_max_right _ _) (le_abs_self _)
    unfold VFunc.eval
    rw [max_lt_iff]
    exact ⟨by nlinarith, by nlinarith⟩
  have hex_pos : ∃ xR : ℝ, kink G.f i < xR ∧ (G.f j).eval xR < (G.f i).eval xR := by
    let num : ℝ := max ((G.f j).b - (G.f i).d) ((G.f j).d - (G.f i).d)
    let den : ℝ := min ((G.f i).c - (G.f j).a) ((G.f i).c - (G.f j).c)
    have hden_pos : 0 < den := lt_min (sub_pos.mpr haj_lt_ci) (sub_pos.mpr hinv)
    let xR : ℝ := max (kink G.f i + 1) (|num| / den + 1)
    have hxR_gt : kink G.f i < xR := lt_of_lt_of_le (by linarith) (le_max_left _ _)
    refine ⟨xR, hxR_gt, ?_⟩
    rw [VFunc.eval_right (G.f i) (G.ac i) (le_of_lt hxR_gt)]
    have hxR_bound : |num| / den + 1 ≤ xR := le_max_right _ _
    have hxR_pos : 0 < xR := by
      have : 0 ≤ |num| / den := div_nonneg (abs_nonneg _) (le_of_lt hden_pos)
      linarith
    have hmul1 : xR * den ≤ xR * ((G.f i).c - (G.f j).a) :=
      mul_le_mul_of_nonneg_left (min_le_left _ _) (le_of_lt hxR_pos)
    have hmul2 : xR * den ≤ xR * ((G.f i).c - (G.f j).c) :=
      mul_le_mul_of_nonneg_left (min_le_right _ _) (le_of_lt hxR_pos)
    have hxd : |num| + den ≤ xR * den := by
      have h1 := mul_le_mul_of_nonneg_right hxR_bound (le_of_lt hden_pos)
      have h2 : (|num| / den + 1) * den = |num| + den := by field_simp [ne_of_gt hden_pos]
      linarith
    have hb1 : (G.f j).b - (G.f i).d ≤ |num| := le_trans (le_max_left _ _) (le_abs_self _)
    have hb2 : (G.f j).d - (G.f i).d ≤ |num| := le_trans (le_max_right _ _) (le_abs_self _)
    unfold VFunc.eval
    rw [max_lt_iff]
    exact ⟨by nlinarith, by nlinarith⟩
  obtain ⟨xL, hxL_lt, hxL_val⟩ := hex_neg
  obtain ⟨xR, hxR_gt, hxR_val⟩ := hex_pos
  let diff (x : ℝ) : ℝ := (G.f i).eval x - (G.f j).eval x
  have hcont : Continuous diff := (continuous_eval_vfunc (G.f i)).sub (continuous_eval_vfunc (G.f j))
  have h0_mem : (0 : ℝ) ∈ Set.Icc (diff (kink G.f i)) (diff xL) :=
    ⟨by dsimp [diff]; linarith, by dsimp [diff]; linarith⟩
  obtain ⟨rL, hrL_mem, hrL_zero⟩ := intermediate_value_Icc' (le_of_lt hxL_lt) hcont.continuousOn h0_mem
  have hrL_lt : rL < kink G.f i := by
    refine lt_of_le_of_ne hrL_mem.2 (fun heq => ?_)
    rw [heq] at hrL_zero
    dsimp [diff] at hrL_zero
    linarith
  have h0_mem2 : (0 : ℝ) ∈ Set.Icc (diff (kink G.f i)) (diff xR) :=
    ⟨by dsimp [diff]; linarith, by dsimp [diff]; linarith⟩
  obtain ⟨rR, hrR_mem, hrR_zero⟩ := intermediate_value_Icc (le_of_lt hxR_gt) hcont.continuousOn h0_mem2
  have hrR_gt : kink G.f i < rR := by
    refine lt_of_le_of_ne hrR_mem.1 (fun heq => ?_)
    rw [← heq] at hrR_zero
    dsimp [diff] at hrR_zero
    linarith
  have hZ_eq : Z_set G.f i j = {rL, rR} := by
    apply Finset.ext
    intro x
    rw [mem_Z_set G hij, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · intro heq
      rcases lt_trichotomy x (kink G.f i) with hx | rfl | hx
      · left
        by_contra hne
        rcases lt_or_gt_of_ne hne with hlt | hgt
        · have := hdec x rL hlt (le_of_lt hrL_lt)
          dsimp [diff] at hrL_zero
          linarith
        · have := hdec rL x hgt (le_of_lt hx)
          dsimp [diff] at hrL_zero
          linarith
      · exfalso; linarith
      · right
        by_contra hne
        rcases lt_or_gt_of_ne hne with hlt | hgt
        · have := hinc x rR (le_of_lt hx) hlt
          dsimp [diff] at hrR_zero
          linarith
        · have := hinc rR x (le_of_lt hrR_gt) hgt
          dsimp [diff] at hrR_zero
          linarith
    · rintro (rfl | rfl)
      · dsimp [diff] at hrL_zero; linarith
      · dsimp [diff] at hrR_zero; linarith
  refine ⟨?_, hkink_lt⟩
  rw [hZ_eq, Finset.card_pair (ne_of_lt (lt_trans hrL_lt hrR_gt))]

lemma Z_set_conc_spec (G : GenericVSystem) {i j : Fin 5} (hij : i < j)
    (hconc : (G.f i).c < (G.f j).c) :
    ((Z_set G.f i j).card = 1 ∨ (Z_set G.f i j).card = 3) ∧
    ((Z_set G.f i j).card = 3 ↔
      kink G.f i < kink G.f j ∧
      (G.f i).eval (kink G.f i) < (G.f j).eval (kink G.f i) ∧
      (G.f j).eval (kink G.f j) < (G.f i).eval (kink G.f j)) := by
  have ha_lt : (G.f i).a < (G.f j).a := G.a_mono hij
  let diff (x : ℝ) : ℝ := (G.f i).eval x - (G.f j).eval x
  have hcont : Continuous diff := (continuous_eval_vfunc (G.f i)).sub (continuous_eval_vfunc (G.f j))
  let xL : ℝ := min (kink G.f i) (kink G.f j)
  let xR : ℝ := max (kink G.f i) (kink G.f j)
  have hxLR : xL < xR := by
    have hne := G.gpa_kinks i j (ne_of_lt hij)
    dsimp [xL, xR]
    rcases lt_or_gt_of_ne hne with h | h
    · rw [min_eq_left (le_of_lt h), max_eq_right (le_of_lt h)]; exact h
    · rw [min_eq_right (le_of_lt h), max_eq_left (le_of_lt h)]; exact h
  have hdiff_left : ∀ x₁ x₂ : ℝ, x₁ < x₂ → x₂ ≤ xL → diff x₂ < diff x₁ := by
    intro x₁ x₂ h12 hx2
    have h1i : x₁ ≤ kink G.f i := le_trans (le_of_lt h12) (le_trans hx2 (min_le_left _ _))
    have h2i : x₂ ≤ kink G.f i := le_trans hx2 (min_le_left _ _)
    have h1j : x₁ ≤ kink G.f j := le_trans (le_of_lt h12) (le_trans hx2 (min_le_right _ _))
    have h2j : x₂ ≤ kink G.f j := le_trans hx2 (min_le_right _ _)
    dsimp [diff]
    rw [VFunc.eval_left (G.f i) (G.ac i) h1i, VFunc.eval_left (G.f i) (G.ac i) h2i,
        VFunc.eval_left (G.f j) (G.ac j) h1j, VFunc.eval_left (G.f j) (G.ac j) h2j]
    nlinarith
  have hdiff_right : ∀ x₁ x₂ : ℝ, xR ≤ x₁ → x₁ < x₂ → diff x₂ < diff x₁ := by
    intro x₁ x₂ hx1 h12
    have h1i : kink G.f i ≤ x₁ := le_trans (le_max_left _ _) hx1
    have h2i : kink G.f i ≤ x₂ := le_trans h1i (le_of_lt h12)
    have h1j : kink G.f j ≤ x₁ := le_trans (le_max_right _ _) hx1
    have h2j : kink G.f j ≤ x₂ := le_trans h1j (le_of_lt h12)
    dsimp [diff]
    rw [VFunc.eval_right (G.f i) (G.ac i) h1i, VFunc.eval_right (G.f i) (G.ac i) h2i,
        VFunc.eval_right (G.f j) (G.ac j) h1j, VFunc.eval_right (G.f j) (G.ac j) h2j]
    nlinarith
  have hdiff_mid_mono : (∀ x₁ x₂ : ℝ, xL ≤ x₁ → x₁ < x₂ → x₂ ≤ xR → diff x₁ < diff x₂) ∨
      (∀ x₁ x₂ : ℝ, xL ≤ x₁ → x₁ < x₂ → x₂ ≤ xR → diff x₂ < diff x₁) := by
    rcases lt_or_gt_of_ne (G.gpa_kinks i j (ne_of_lt hij)) with hij_k | hji_k
    · have hxL_eq : xL = kink G.f i := min_eq_left (le_of_lt hij_k)
      have hxR_eq : xR = kink G.f j := max_eq_right (le_of_lt hij_k)
      have hne_slope : (G.f i).c ≠ (G.f j).a := fun h => by
        have := G.slopes_inj (a₁ := (i, true)) (a₂ := (j, false)) h
        exact (ne_of_lt hij) (congrArg Prod.fst this)
      rcases lt_or_gt_of_ne hne_slope with hsl | hsl
      · right; intro x₁ x₂ hx1 h12 hx2
        rw [hxL_eq] at hx1; rw [hxR_eq] at hx2
        dsimp [diff]
        rw [VFunc.eval_right (G.f i) (G.ac i) hx1,
            VFunc.eval_right (G.f i) (G.ac i) (le_trans hx1 (le_of_lt h12)),
            VFunc.eval_left (G.f j) (G.ac j) (le_trans (le_of_lt h12) hx2),
            VFunc.eval_left (G.f j) (G.ac j) hx2]
        nlinarith
      · left; intro x₁ x₂ hx1 h12 hx2
        rw [hxL_eq] at hx1; rw [hxR_eq] at hx2
        dsimp [diff]
        rw [VFunc.eval_right (G.f i) (G.ac i) hx1,
            VFunc.eval_right (G.f i) (G.ac i) (le_trans hx1 (le_of_lt h12)),
            VFunc.eval_left (G.f j) (G.ac j) (le_trans (le_of_lt h12) hx2),
            VFunc.eval_left (G.f j) (G.ac j) hx2]
        nlinarith
    · have hxL_eq : xL = kink G.f j := min_eq_right (le_of_lt hji_k)
      have hxR_eq : xR = kink G.f i := max_eq_left (le_of_lt hji_k)
      have hsl : (G.f i).a < (G.f j).c := lt_trans ha_lt (G.ac j)
      right; intro x₁ x₂ hx1 h12 hx2
      rw [hxL_eq] at hx1; rw [hxR_eq] at hx2
      dsimp [diff]
      rw [VFunc.eval_left (G.f i) (G.ac i) (le_trans (le_of_lt h12) hx2),
          VFunc.eval_left (G.f i) (G.ac i) hx2,
          VFunc.eval_right (G.f j) (G.ac j) hx1,
          VFunc.eval_right (G.f j) (G.ac j) (le_trans hx1 (le_of_lt h12))]
      nlinarith
  -- Find `M_neg < xL` with `diff M_neg > 0` and `xR < M_pos` with `diff M_pos < 0`
  have hex_neg : ∃ M_neg : ℝ, M_neg < xL ∧ 0 < diff M_neg := by
    let x := min (xL - 1) (-|(G.f j).b - (G.f i).b| / ((G.f j).a - (G.f i).a) - 1)
    have hx_lt : x < xL := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    refine ⟨x, hx_lt, ?_⟩
    have hxi : x ≤ kink G.f i := le_trans (le_of_lt hx_lt) (min_le_left _ _)
    have hxj : x ≤ kink G.f j := le_trans (le_of_lt hx_lt) (min_le_right _ _)
    dsimp [diff]
    rw [VFunc.eval_left (G.f i) (G.ac i) hxi, VFunc.eval_left (G.f j) (G.ac j) hxj]
    have hden : 0 < (G.f j).a - (G.f i).a := sub_pos.mpr ha_lt
    have hx_b : x ≤ -|(G.f j).b - (G.f i).b| / ((G.f j).a - (G.f i).a) - 1 := min_le_right _ _
    have hmul : x * ((G.f j).a - (G.f i).a) ≤ -|(G.f j).b - (G.f i).b| - ((G.f j).a - (G.f i).a) := by
      have h1 := mul_le_mul_of_nonneg_right hx_b (le_of_lt hden)
      have h2 : (-|(G.f j).b - (G.f i).b| / ((G.f j).a - (G.f i).a) - 1) * ((G.f j).a - (G.f i).a) =
          -|(G.f j).b - (G.f i).b| - ((G.f j).a - (G.f i).a) := by field_simp [ne_of_gt hden]
      linarith
    have hb : (G.f j).b - (G.f i).b ≤ |(G.f j).b - (G.f i).b| := le_abs_self _
    linarith
  have hex_pos : ∃ M_pos : ℝ, xR < M_pos ∧ diff M_pos < 0 := by
    let x := max (xR + 1) (|(G.f i).d - (G.f j).d| / ((G.f j).c - (G.f i).c) + 1)
    have hx_gt : xR < x := lt_of_lt_of_le (by linarith) (le_max_left _ _)
    refine ⟨x, hx_gt, ?_⟩
    have hxi : kink G.f i ≤ x := le_trans (le_max_left _ _) (le_of_lt hx_gt)
    have hxj : kink G.f j ≤ x := le_trans (le_max_right _ _) (le_of_lt hx_gt)
    dsimp [diff]
    rw [VFunc.eval_right (G.f i) (G.ac i) hxi, VFunc.eval_right (G.f j) (G.ac j) hxj]
    have hden : 0 < (G.f j).c - (G.f i).c := sub_pos.mpr hconc
    have hx_b : |(G.f i).d - (G.f j).d| / ((G.f j).c - (G.f i).c) + 1 ≤ x := le_max_right _ _
    have hmul : |(G.f i).d - (G.f j).d| + ((G.f j).c - (G.f i).c) ≤ x * ((G.f j).c - (G.f i).c) := by
      have h1 := mul_le_mul_of_nonneg_right hx_b (le_of_lt hden)
      have h2 : (|(G.f i).d - (G.f j).d| / ((G.f j).c - (G.f i).c) + 1) * ((G.f j).c - (G.f i).c) =
          |(G.f i).d - (G.f j).d| + ((G.f j).c - (G.f i).c) := by field_simp [ne_of_gt hden]
      linarith
    have hd : (G.f i).d - (G.f j).d ≤ |(G.f i).d - (G.f j).d| := le_abs_self _
    linarith
  obtain ⟨M_neg, hMneg_lt, hMneg_val⟩ := hex_neg
  obtain ⟨M_pos, hMpos_gt, hMpos_val⟩ := hex_pos
  have hxL_ne : diff xL ≠ 0 := by
    dsimp [xL]; cases le_total (kink G.f i) (kink G.f j) with
    | inl h => rw [min_eq_left h]; exact sub_ne_zero.mpr (G.gpb_kink i j i hij)
    | inr h => rw [min_eq_right h]; exact sub_ne_zero.mpr (G.gpb_kink i j j hij)
  have hxR_ne : diff xR ≠ 0 := by
    dsimp [xR]; cases le_total (kink G.f i) (kink G.f j) with
    | inl h => rw [max_eq_right h]; exact sub_ne_zero.mpr (G.gpb_kink i j j hij)
    | inr h => rw [max_eq_left h]; exact sub_ne_zero.mpr (G.gpb_kink i j i hij)
  -- Partition `Z_set G.f i j` into `Iio xL`, `Ioo xL xR`, `Ioi xR`
  have hsub_union : Z_set G.f i j =
      (Z_set G.f i j).filter (· < xL) ∪
      (Z_set G.f i j).filter (fun x => xL < x ∧ x < xR) ∪
      (Z_set G.f i j).filter (xR < ·) := by
    apply Finset.ext; intro x
    simp only [Finset.mem_union, Finset.mem_filter]
    constructor
    · intro hx
      have heq : diff x = 0 := sub_eq_zero.mpr ((mem_Z_set G hij x).mp hx)
      have hneL : x ≠ xL := fun h => hxL_ne (h ▸ heq)
      have hneR : x ≠ xR := fun h => hxR_ne (h ▸ heq)
      rcases lt_or_gt_of_ne hneL with h1 | h1
      · left; left; exact ⟨hx, h1⟩
      · rcases lt_or_gt_of_ne hneR with h2 | h2
        · left; right; exact ⟨hx, h1, h2⟩
        · right; exact ⟨hx, h2⟩
    · rintro ((⟨hx, _⟩ | ⟨hx, _⟩) | ⟨hx, _⟩) <;> exact hx
  have h_left_card : ((Z_set G.f i j).filter (· < xL)).card = if diff xL < 0 then 1 else 0 := by
    by_cases hneg : diff xL < 0
    · rw [if_pos hneg]
      have h0 : (0 : ℝ) ∈ Set.Icc (diff xL) (diff M_neg) := ⟨le_of_lt hneg, le_of_lt hMneg_val⟩
      obtain ⟨r, hr_mem, hr_zero⟩ := intermediate_value_Icc' (le_of_lt hMneg_lt) hcont.continuousOn h0
      have hr_lt : r < xL := lt_of_le_of_ne hr_mem.2 (fun h => hxL_ne (h ▸ hr_zero))
      have hsing : (Z_set G.f i j).filter (· < xL) = {r} := by
        apply Finset.ext; intro x
        rw [Finset.mem_filter, Finset.mem_singleton, mem_Z_set G hij]
        constructor
        · rintro ⟨heq, hx⟩
          by_contra hne
          rcases lt_or_gt_of_ne hne with hlt | hgt
          · have := hdiff_left x r hlt (le_of_lt hr_lt); dsimp [diff] at hr_zero; linarith
          · have := hdiff_left r x hgt (le_of_lt hx); dsimp [diff] at hr_zero; linarith
        · rintro rfl; exact ⟨sub_eq_zero.mp hr_zero, hr_lt⟩
      rw [hsing, Finset.card_singleton]
    · rw [if_neg hneg]
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro x hx hlt
      have heq : diff x = 0 := sub_eq_zero.mpr ((mem_Z_set G hij x).mp hx)
      have hgt : 0 < diff xL := lt_of_le_of_ne (not_lt.mp hneg) hxL_ne.symm
      have := hdiff_left x xL hlt le_rfl
      linarith
  have h_right_card : ((Z_set G.f i j).filter (xR < ·)).card = if 0 < diff xR then 1 else 0 := by
    by_cases hpos : 0 < diff xR
    · rw [if_pos hpos]
      have h0 : (0 : ℝ) ∈ Set.Icc (diff M_pos) (diff xR) := ⟨le_of_lt hMpos_val, le_of_lt hpos⟩
      obtain ⟨r, hr_mem, hr_zero⟩ := intermediate_value_Icc' (le_of_lt hMpos_gt) hcont.continuousOn h0
      have hr_gt : xR < r := lt_of_le_of_ne hr_mem.1 (fun h => hxR_ne (h ▸ hr_zero))
      have hsing : (Z_set G.f i j).filter (xR < ·) = {r} := by
        apply Finset.ext; intro x
        rw [Finset.mem_filter, Finset.mem_singleton, mem_Z_set G hij]
        constructor
        · rintro ⟨heq, hx⟩
          by_contra hne
          rcases lt_or_gt_of_ne hne with hlt | hgt
          · have := hdiff_right x r (le_of_lt hx) hlt; dsimp [diff] at hr_zero; linarith
          · have := hdiff_right r x (le_of_lt hr_gt) hgt; dsimp [diff] at hr_zero; linarith
        · rintro rfl; exact ⟨sub_eq_zero.mp hr_zero, hr_gt⟩
      rw [hsing, Finset.card_singleton]
    · rw [if_neg hpos]
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro x hx hgt
      have heq : diff x = 0 := sub_eq_zero.mpr ((mem_Z_set G hij x).mp hx)
      have hlt : diff xR < 0 := lt_of_le_of_ne (not_lt.mp hpos) hxR_ne
      have := hdiff_right xR x le_rfl hgt
      linarith
  have h_mid_card : ((Z_set G.f i j).filter (fun x => xL < x ∧ x < xR)).card =
      if (diff xL < 0 ∧ 0 < diff xR) ∨ (0 < diff xL ∧ diff xR < 0) then 1 else 0 := by
    split_ifs with hcond
    · rcases hcond with ⟨hL, hR⟩ | ⟨hL, hR⟩
      · have h0 : (0 : ℝ) ∈ Set.Icc (diff xL) (diff xR) := ⟨le_of_lt hL, le_of_lt hR⟩
        obtain ⟨r, hr_mem, hr_zero⟩ := intermediate_value_Icc (le_of_lt hxLR) hcont.continuousOn h0
        have hr_lt : xL < r := lt_of_le_of_ne hr_mem.1 (fun h => hxL_ne (h ▸ hr_zero))
        have hr_gt : r < xR := lt_of_le_of_ne hr_mem.2 (fun h => hxR_ne (h ▸ hr_zero))
        have hsing : (Z_set G.f i j).filter (fun x => xL < x ∧ x < xR) = {r} := by
          apply Finset.ext; intro x
          rw [Finset.mem_filter, Finset.mem_singleton, mem_Z_set G hij]
          constructor
          · rintro ⟨heq, hx1, hx2⟩
            by_contra hne
            rcases hdiff_mid_mono with hm | hm
            · rcases lt_or_gt_of_ne hne with hlt | hgt
              · have := hm x r (le_of_lt hx1) hlt (le_of_lt hr_gt); dsimp [diff] at hr_zero; linarith
              · have := hm r x (le_of_lt hr_lt) hgt (le_of_lt hx2); dsimp [diff] at hr_zero; linarith
            · exfalso; have := hm xL xR le_rfl hxLR le_rfl; linarith
          · rintro rfl; exact ⟨sub_eq_zero.mp hr_zero, hr_lt, hr_gt⟩
        rw [hsing, Finset.card_singleton]
      · have h0 : (0 : ℝ) ∈ Set.Icc (diff xR) (diff xL) := ⟨le_of_lt hR, le_of_lt hL⟩
        obtain ⟨r, hr_mem, hr_zero⟩ := intermediate_value_Icc' (le_of_lt hxLR) hcont.continuousOn h0
        have hr_lt : xL < r := lt_of_le_of_ne hr_mem.1 (fun h => hxL_ne (h ▸ hr_zero))
        have hr_gt : r < xR := lt_of_le_of_ne hr_mem.2 (fun h => hxR_ne (h ▸ hr_zero))
        have hsing : (Z_set G.f i j).filter (fun x => xL < x ∧ x < xR) = {r} := by
          apply Finset.ext; intro x
          rw [Finset.mem_filter, Finset.mem_singleton, mem_Z_set G hij]
          constructor
          · rintro ⟨heq, hx1, hx2⟩
            by_contra hne
            rcases hdiff_mid_mono with hm | hm
            · exfalso; have := hm xL xR le_rfl hxLR le_rfl; linarith
            · rcases lt_or_gt_of_ne hne with hlt | hgt
              · have := hm x r (le_of_lt hx1) hlt (le_of_lt hr_gt); dsimp [diff] at hr_zero; linarith
              · have := hm r x (le_of_lt hr_lt) hgt (le_of_lt hx2); dsimp [diff] at hr_zero; linarith
          · rintro rfl; exact ⟨sub_eq_zero.mp hr_zero, hr_lt, hr_gt⟩
        rw [hsing, Finset.card_singleton]
    · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro x hx ⟨hx1, hx2⟩
      have heq : diff x = 0 := sub_eq_zero.mpr ((mem_Z_set G hij x).mp hx)
      rcases hdiff_mid_mono with hm | hm
      · have h1 := hm xL x le_rfl hx1 (le_of_lt hx2)
        have h2 := hm x xR (le_of_lt hx1) hx2 le_rfl
        apply hcond; left; exact ⟨by linarith, by linarith⟩
      · have h1 := hm xL x le_rfl hx1 (le_of_lt hx2)
        have h2 := hm x xR (le_of_lt hx1) hx2 le_rfl
        apply hcond; right; exact ⟨by linarith, by linarith⟩
  have hdisj1 : Disjoint ((Z_set G.f i j).filter (· < xL))
      ((Z_set G.f i j).filter (fun x => xL < x ∧ x < xR)) := by
    rw [Finset.disjoint_left]; intro x h1 h2
    have h1' := (Finset.mem_filter.mp h1).2
    have h2' := (Finset.mem_filter.mp h2).2
    linarith
  have hdisj2 : Disjoint ((Z_set G.f i j).filter (· < xL) ∪
      (Z_set G.f i j).filter (fun x => xL < x ∧ x < xR))
      ((Z_set G.f i j).filter (xR < ·)) := by
    rw [Finset.disjoint_left]; intro x h1 h2
    have h2' := (Finset.mem_filter.mp h2).2
    rcases Finset.mem_union.mp h1 with h1a | h1b
    · have h1' := (Finset.mem_filter.mp h1a).2; linarith
    · have h1' := (Finset.mem_filter.mp h1b).2; linarith
  have hcard_sum : (Z_set G.f i j).card =
      (if diff xL < 0 then 1 else 0) +
      (if (diff xL < 0 ∧ 0 < diff xR) ∨ (0 < diff xL ∧ diff xR < 0) then 1 else 0) +
      (if 0 < diff xR then 1 else 0) := by
    rw [hsub_union, Finset.card_union_of_disjoint hdisj2, Finset.card_union_of_disjoint hdisj1,
        h_left_card, h_mid_card, h_right_card]
  have hsigns : (diff xL < 0 ∨ 0 < diff xL) ∧ (0 < diff xR ∨ diff xR < 0) :=
    ⟨lt_or_gt_of_ne hxL_ne, (lt_or_gt_of_ne hxR_ne).symm⟩
  constructor
  · rcases hsigns with ⟨hL | hL, hR | hR⟩ <;> rw [hcard_sum]
    · right; simp [hL, hR]
    · left; simp [hL, hR, lt_asymm hL, lt_asymm hR]
    · left; simp [hL, hR, lt_asymm hL, lt_asymm hR]
    · left; simp [hL, hR, lt_asymm hL, lt_asymm hR]
  · constructor
    · intro h3
      have hLR_signs : diff xL < 0 ∧ 0 < diff xR := by
        rcases hsigns with ⟨hL | hL, hR | hR⟩
        · exact ⟨hL, hR⟩
        · exfalso; rw [hcard_sum] at h3; simp [hL, hR, lt_asymm hL, lt_asymm hR] at h3
        · exfalso; rw [hcard_sum] at h3; simp [hL, hR, lt_asymm hL, lt_asymm hR] at h3
        · exfalso; rw [hcard_sum] at h3; simp [hL, hR, lt_asymm hL, lt_asymm hR] at h3
      have hk_ord : kink G.f i < kink G.f j := by
        rcases lt_or_gt_of_ne (G.gpa_kinks i j (ne_of_lt hij)) with hij_k | hji_k
        · exact hij_k
        · exfalso
          have hxL_eq : xL = kink G.f j := min_eq_right (le_of_lt hji_k)
          have hxR_eq : xR = kink G.f i := max_eq_left (le_of_lt hji_k)
          have hsl : (G.f i).a < (G.f j).c := lt_trans ha_lt (G.ac j)
          have hle : diff xR < diff xL := by
            dsimp [diff]; rw [hxL_eq, hxR_eq]
            rw [eval_kink G.f i (G.ac i),
                VFunc.eval_left (G.f i) (G.ac i) (le_of_lt hji_k),
                VFunc.eval_right (G.f j) (G.ac j) (le_of_lt hji_k),
                eval_kink G.f j (G.ac j)]
            have hki_eq := kink_eq G.f i (G.ac i)
            have hkj_eq := kink_eq G.f j (G.ac j)
            nlinarith
          linarith [hLR_signs.1, hLR_signs.2]
      have hxL_eq : xL = kink G.f i := min_eq_left (le_of_lt hk_ord)
      have hxR_eq : xR = kink G.f j := max_eq_right (le_of_lt hk_ord)
      rw [hxL_eq] at hLR_signs; rw [hxR_eq] at hLR_signs
      exact ⟨hk_ord, sub_neg.mp hLR_signs.1, sub_pos.mp hLR_signs.2⟩
    · rintro ⟨hk_ord, h1, h2⟩
      have hxL_eq : xL = kink G.f i := min_eq_left (le_of_lt hk_ord)
      have hxR_eq : xR = kink G.f j := max_eq_right (le_of_lt hk_ord)
      have hL : diff xL < 0 := by rw [hxL_eq]; dsimp [diff]; linarith
      have hR : 0 < diff xR := by rw [hxR_eq]; dsimp [diff]; linarith
      rw [hcard_sum]; simp [hL, hR]

/-- All unordered pairs `(i, j)` with `i < j`. -/
def pair5 : Finset (Fin 5 × Fin 5) :=
  Finset.univ.filter (fun p : Fin 5 × Fin 5 => p.1 < p.2)

lemma pair5_card : pair5.card = 10 := by decide

def P_inv (f : Fin 5 → VFunc) : Finset (Fin 5 × Fin 5) :=
  pair5.filter (fun p => (f p.2).c < (f p.1).c)

def P_conc (f : Fin 5 → VFunc) : Finset (Fin 5 × Fin 5) :=
  pair5.filter (fun p => (f p.1).c < (f p.2).c)

def E_G3 (G : GenericVSystem) : Finset (Fin 5 × Fin 5) :=
  pair5.filter (fun p => (Z_set G.f p.1 p.2).card = 3)

def T3 (G : GenericVSystem) : ℕ := (E_G3 G).card
def T3bar (G : GenericVSystem) : ℕ := 10 - T3 G
def T1 (G : GenericVSystem) : ℕ := (pair5.filter (fun p => (G.f p.1).c < (G.f p.2).c ∧ (Z_set G.f p.1 p.2).card = 1)).card

def X_cross (f : Fin 5 → VFunc) : Finset ℝ :=
  pair5.biUnion (fun p => Z_set f p.1 p.2)

lemma X_cross_card (G : GenericVSystem) :
    (X_cross G.f).card = 3 * T3 G + T1 G + 2 * (T3bar G - T1 G) := by
  have hdisj : ∀ p ∈ pair5, ∀ q ∈ pair5, p ≠ q → Disjoint (Z_set G.f p.1 p.2) (Z_set G.f q.1 q.2) := by
    rintro ⟨i, j⟩ hp ⟨k, l⟩ hq hne
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    have hij : i < j := (Finset.mem_filter.mp hp).2
    have hkl : k < l := (Finset.mem_filter.mp hq).2
    rw [mem_Z_set G hij] at hx1
    rw [mem_Z_set G hkl] at hx2
    exact G.gpb_disj i j k l hij hkl hne x ⟨hx1, hx2⟩
  have hsum : (X_cross G.f).card = ∑ p ∈ pair5, (Z_set G.f p.1 p.2).card :=
    Finset.card_biUnion hdisj
  have hT3_le : T3 G ≤ 10 := by
    calc T3 G ≤ pair5.card := Finset.card_filter_le _ _
      _ = 10 := pair5_card
  have hconc_part : ∀ p ∈ pair5, (G.f p.1).c < (G.f p.2).c ∨ (G.f p.2).c < (G.f p.1).c := by
    intro ⟨i, j⟩ hp
    have hij : i < j := (Finset.mem_filter.mp hp).2
    have hne : (G.f i).c ≠ (G.f j).c := fun h => by
      have := G.slopes_inj (a₁ := (i, true)) (a₂ := (j, true)) h
      exact (ne_of_lt hij) (congrArg Prod.fst this)
    exact lt_or_gt_of_ne hne
  -- Count each pair by `(Z_set).card ∈ {1, 2, 3}`
  let S3 := pair5.filter (fun p => (Z_set G.f p.1 p.2).card = 3)
  let S1 := pair5.filter (fun p => (G.f p.1).c < (G.f p.2).c ∧ (Z_set G.f p.1 p.2).card = 1)
  let S2 := pair5.filter (fun p => (G.f p.2).c < (G.f p.1).c)
  have hpart : ∀ p ∈ pair5, p ∈ S3 ∨ p ∈ S1 ∨ p ∈ S2 := by
    intro ⟨i, j⟩ hp
    have hij : i < j := (Finset.mem_filter.mp hp).2
    rcases hconc_part (i, j) hp with hc | hi
    · rcases (Z_set_conc_spec G hij hc).1 with h1 | h3
      · right; left; exact Finset.mem_filter.mpr ⟨hp, hc, h1⟩
      · left; exact Finset.mem_filter.mpr ⟨hp, h3⟩
    · right; right; exact Finset.mem_filter.mpr ⟨hp, hi⟩
  have h12 : Disjoint S3 S1 := by
    rw [Finset.disjoint_left]; intro p h3 h1
    have := (Finset.mem_filter.mp h3).2
    have := (Finset.mem_filter.mp h1).2.2
    omega
  have h13 : Disjoint (S3 ∪ S1) S2 := by
    rw [Finset.disjoint_left]; intro p h31 h2
    have hij : p.1 < p.2 := (Finset.mem_filter.mp (Finset.mem_filter.mp h2).1).2
    have hi : (G.f p.2).c < (G.f p.1).c := (Finset.mem_filter.mp h2).2
    rcases Finset.mem_union.mp h31 with h3 | h1
    · have h3' := (Finset.mem_filter.mp h3).2
      have h2' := (Z_set_inv_spec G hij hi).1
      omega
    · have h1' := (Finset.mem_filter.mp h1).2.1
      linarith
  have hpair_eq : pair5 = S3 ∪ S1 ∪ S2 := by
    apply Finset.ext; intro p; constructor
    · intro hp; rcases hpart p hp with h | h | h
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ h)
      · exact Finset.mem_union_left _ (Finset.mem_union_right _ h)
      · exact Finset.mem_union_right _ h
    · intro hp; rcases Finset.mem_union.mp hp with h | h
      · rcases Finset.mem_union.mp h with h | h <;> exact (Finset.mem_filter.mp h).1
      · exact (Finset.mem_filter.mp h).1
  have hcard_total : 10 = S3.card + S1.card + S2.card := by
    calc 10 = pair5.card := pair5_card.symm
      _ = (S3 ∪ S1 ∪ S2).card := by rw [hpair_eq]
      _ = S3.card + S1.card + S2.card := by
          rw [Finset.card_union_of_disjoint h13, Finset.card_union_of_disjoint h12]
  have hS3 : S3.card = T3 G := rfl
  have hS1 : S1.card = T1 G := rfl
  have hS2 : S2.card = T3bar G - T1 G := by dsimp [T3bar]; omega
  rw [hsum, hpair_eq, Finset.sum_union h13, Finset.sum_union h12]
  have hs3 : ∑ p ∈ S3, (Z_set G.f p.1 p.2).card = 3 * S3.card := by
    rw [Finset.sum_congr rfl (fun p hp => (Finset.mem_filter.mp hp).2), Finset.sum_const, smul_eq_mul, mul_comm]
  have hs1 : ∑ p ∈ S1, (Z_set G.f p.1 p.2).card = S1.card := by
    rw [Finset.sum_congr rfl (fun p hp => (Finset.mem_filter.mp hp).2.2), Finset.sum_const, smul_eq_mul, mul_one]
  have hs2 : ∑ p ∈ S2, (Z_set G.f p.1 p.2).card = 2 * S2.card := by
    have h2 : ∀ p ∈ S2, (Z_set G.f p.1 p.2).card = 2 := by
      intro p hp
      have hp' := Finset.mem_filter.mp hp
      have hij := (Finset.mem_filter.mp hp'.1).2
      exact (Z_set_inv_spec G hij hp'.2).1
    rw [Finset.sum_congr rfl h2, Finset.sum_const, smul_eq_mul, mul_comm]
  rw [hs3, hs1, hs2, hS3, hS1, hS2]

/-- `T_1 ≤ T3bar` because `S1` is disjoint from `S3`. -/
lemma T1_le_T3bar (G : GenericVSystem) : T1 G ≤ T3bar G := by
  let S3 := E_G3 G
  let S1 := pair5.filter (fun p => (G.f p.1).c < (G.f p.2).c ∧ (Z_set G.f p.1 p.2).card = 1)
  have hdisj : Disjoint S3 S1 := by
    rw [Finset.disjoint_left]; intro p h3 h1
    have := (Finset.mem_filter.mp h3).2
    have := (Finset.mem_filter.mp h1).2.2
    omega
  have hsub : S3 ∪ S1 ⊆ pair5 := Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdisj, pair5_card] at hcard
  dsimp [S3, S1] at hcard
  dsimp [T3bar, T3, T1]
  omega

/-- Sweeping 1D intervals between `X_cross` and proving the exact conservation law
    `H.n + T3bar G + T1 G + Δ1 + Δ2 + Δ3 = 9` along with the duplicate-cell split criterion. -/
def maskOf (M : Finset (Fin 5)) : Fin 5 → Bool :=
  fun i => decide (i ∈ M)

def Φ (f : Fin 5 → VFunc) (M : Finset (Fin 5)) (x : ℝ) : Prop :=
  ∀ u ∈ M, ∀ v ∉ M, (f u).eval x < (f v).eval x

structure SweepData (G : GenericVSystem) (H : HullData G.f) where
  Δ1 : ℕ
  Δ2 : ℕ
  Δ3 : ℕ
  h_cons : (H.n : ℤ) + (T3bar G : ℤ) + (T1 G : ℤ) + (Δ1 : ℤ) + (Δ2 : ℤ) + (Δ3 : ℤ) = 9
  h_split_cert : ∀ (M : Finset (Fin 5)) (τ₁ τ₂ τ₃ : ℝ),
    M.card = 1 ∨ M.card = 2 →
    τ₁ < τ₂ → τ₂ < τ₃ →
    τ₁ ∉ X_cross G.f → τ₂ ∉ X_cross G.f → τ₃ ∉ X_cross G.f →
    Φ G.f M τ₁ → ¬ Φ G.f M τ₂ → Φ G.f M τ₃ →
    1 ≤ if M.card = 1 then Δ1 else Δ2
  h_two_split_cert : ∀ (M₁ M₂ : Finset (Fin 5)) (τ₁ τ₂ τ₃ τ₁' τ₂' τ₃' : ℝ),
    (M₁.card = 1 ∨ M₁.card = 2) → (M₂.card = 1 ∨ M₂.card = 2) → M₁ ≠ M₂ →
    τ₁ < τ₂ → τ₂ < τ₃ →
    τ₁ ∉ X_cross G.f → τ₂ ∉ X_cross G.f → τ₃ ∉ X_cross G.f →
    Φ G.f M₁ τ₁ → ¬ Φ G.f M₁ τ₂ → Φ G.f M₁ τ₃ →
    τ₁' < τ₂' → τ₂' < τ₃' →
    τ₁' ∉ X_cross G.f → τ₂' ∉ X_cross G.f → τ₃' ∉ X_cross G.f →
    Φ G.f M₂ τ₁' → ¬ Φ G.f M₂ τ₂' → Φ G.f M₂ τ₃' →
    2 ≤ Δ1 + Δ2

/-- Bottom `q` elements of an injective function `v : Fin 5 → ℝ`. -/
def bottomK (v : Fin 5 → ℝ) (q : ℕ) : Finset (Fin 5) :=
  Finset.univ.filter (fun i : Fin 5 => (Finset.univ.filter (fun j : Fin 5 => v j < v i)).card < q)

lemma rank_strictMono {v : Fin 5 → ℝ} (i j : Fin 5) (hij : v i < v j) :
    (Finset.univ.filter (fun k : Fin 5 => v k < v i)).card <
    (Finset.univ.filter (fun k : Fin 5 => v k < v j)).card := by
  refine Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩)
  · intro k hk
    rw [Finset.mem_filter] at hk ⊢
    exact ⟨Finset.mem_univ _, lt_trans hk.2 hij⟩
  · intro heq
    have hi : i ∈ Finset.univ.filter (fun k : Fin 5 => v k < v j) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hij⟩
    rw [← heq, Finset.mem_filter] at hi
    exact lt_irrefl _ hi.2

lemma bottomK_card {v : Fin 5 → ℝ} (hv : Function.Injective v) (q : ℕ) (hq : q ≤ 5) :
    (bottomK v q).card = q := by
  let rk : Fin 5 → Fin 5 := fun i =>
    ⟨(Finset.univ.filter (fun j : Fin 5 => v j < v i)).card, by
      have hsub : Finset.univ.filter (fun j : Fin 5 => v j < v i) ⊆ Finset.univ.erase i := by
        intro j hj
        rw [Finset.mem_filter] at hj
        exact Finset.mem_erase.mpr ⟨fun heq => lt_irrefl _ (heq ▸ hj.2), Finset.mem_univ _⟩
      have hc := Finset.card_le_card hsub
      rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_fin] at hc
      omega⟩
  have hrk_inj : Function.Injective rk := by
    intro i j heq
    by_contra hne
    rcases lt_or_gt_of_ne (fun h => hne (hv h)) with hlt | hgt
    · have := rank_strictMono i j hlt
      have hval := congrArg Fin.val heq
      dsimp [rk] at hval; omega
    · have := rank_strictMono j i hgt
      have hval := congrArg Fin.val heq
      dsimp [rk] at hval; omega
  have hrk_bij : Function.Bijective rk :=
    (Fintype.bijective_iff_injective_and_card rk).mpr ⟨hrk_inj, by simp⟩
  let e := Equiv.ofBijective rk hrk_bij
  have himg : (bottomK v q).image e = Finset.univ.filter (fun k : Fin 5 => k.val < q) := by
    apply Finset.ext; intro k; rw [Finset.mem_image, Finset.mem_filter]
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact ⟨Finset.mem_univ _, (Finset.mem_filter.mp hi).2⟩
    · rintro ⟨_, hk⟩
      refine ⟨e.symm k, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, e.apply_symm_apply k⟩
      change (e (e.symm k)).val < q
      rwa [e.apply_symm_apply]
  rw [← Finset.card_image_of_injective (bottomK v q) e.injective, himg]
  have hfin : (Finset.univ.filter (fun k : Fin 5 => k.val < q)) =
      (Finset.range q).attach.image (fun x => ⟨x.1, lt_of_lt_of_le (Finset.mem_range.mp x.2) hq⟩) := by
    apply Finset.ext; intro k; rw [Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨_, hk⟩
      exact ⟨⟨k.val, Finset.mem_range.mpr hk⟩, Finset.mem_attach _ _, Fin.ext rfl⟩
    · rintro ⟨⟨x, hx⟩, _, rfl⟩
      exact ⟨Finset.mem_univ _, Finset.mem_range.mp hx⟩
  rw [hfin, Finset.card_image_of_injective _ (fun a b h => Subtype.ext (congrArg Fin.val h)),
      Finset.card_attach, Finset.card_range]

lemma bottomK_eq_iff {v : Fin 5 → ℝ} (hv : Function.Injective v) (q : ℕ) (hq : q ≤ 5)
    (M : Finset (Fin 5)) :
    bottomK v q = M ↔ M.card = q ∧ ∀ u ∈ M, ∀ w ∉ M, v u < v w := by
  constructor
  · rintro rfl
    refine ⟨bottomK_card hv q hq, fun u hu w hw => ?_⟩
    have hu' := (Finset.mem_filter.mp hu).2
    have hw' : q ≤ (Finset.univ.filter (fun j : Fin 5 => v j < v w)).card :=
      not_lt.mp (fun hlt => hw (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt⟩))
    by_contra hle
    rcases eq_or_lt_of_le (not_lt.mp hle) with heq | hlt
    · exact hw (hv heq ▸ hu)
    · have := rank_strictMono w u hlt
      omega
  · rintro ⟨hcard, hord⟩
    by_cases hq0 : q = 0
    · subst hq0
      have hM : M = ∅ := Finset.card_eq_zero.mp hcard
      have hB : bottomK v 0 = ∅ := Finset.card_eq_zero.mp (bottomK_card hv 0 hq)
      rw [hM, hB]
    · symm
      refine Finset.eq_of_subset_of_card_le (fun u hu => ?_) (by rw [bottomK_card hv q hq, hcard])
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      have hsub : Finset.univ.filter (fun j : Fin 5 => v j < v u) ⊆ M.erase u := by
        intro j hj
        have hjlt := (Finset.mem_filter.mp hj).2
        refine Finset.mem_erase.mpr ⟨fun heq => lt_irrefl _ (heq ▸ hjlt), ?_⟩
        by_contra hjnot
        have := hord u hu j hjnot
        linarith
      have hc := Finset.card_le_card hsub
      rw [Finset.card_erase_of_mem hu, hcard] at hc
      omega

/-- Combinatorial run-counting identity on any finite sequence `sSeq : Fin (K + 1) → α`. -/
def seqRuns {K : ℕ} {α : Type*} [DecidableEq α] (sSeq : Fin (K + 1) → α) (m : α) : ℕ :=
  (if sSeq 0 = m then 1 else 0) +
  (Finset.univ.filter (fun r : Fin K => sSeq ⟨r.val, by omega⟩ ≠ m ∧ sSeq ⟨r.val + 1, by omega⟩ = m)).card

lemma seqRuns_ge_one {K : ℕ} {α : Type*} [DecidableEq α] (sSeq : Fin (K + 1) → α) (m : α)
    (hex : ∃ r : Fin (K + 1), sSeq r = m) : 1 ≤ seqRuns sSeq m := by
  let S := Finset.univ.filter (fun r : Fin (K + 1) => sSeq r = m)
  have hSne : S.Nonempty := by
    rcases hex with ⟨r, hr⟩; exact ⟨r, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hr⟩⟩
  let r0 := S.min' hSne
  have hr0_eq : sSeq r0 = m := (Finset.mem_filter.mp (Finset.min'_mem S hSne)).2
  by_cases h0 : r0.val = 0
  · have hr00 : r0 = 0 := Fin.ext h0
    rw [hr00] at hr0_eq
    unfold seqRuns; rw [if_pos hr0_eq]; omega
  · let r' : Fin K := ⟨r0.val - 1, by omega⟩
    have hr'_ne : sSeq ⟨r'.val, by omega⟩ ≠ m := by
      intro heq
      have hmem : (⟨r'.val, by omega⟩ : Fin (K + 1)) ∈ S :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, heq⟩
      have hle := Finset.min'_le S _ hmem
      have hle' : r0.val ≤ r'.val := hle
      dsimp [r'] at hle'; omega
    have hr'_succ : sSeq ⟨r'.val + 1, by omega⟩ = m := by
      have heq : (⟨r'.val + 1, by omega⟩ : Fin (K + 1)) = r0 := Fin.ext (by dsimp [r']; omega)
      rwa [heq]
    have hmem_filt : r' ∈ Finset.univ.filter (fun r : Fin K =>
        sSeq ⟨r.val, by omega⟩ ≠ m ∧ sSeq ⟨r.val + 1, by omega⟩ = m) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hr'_ne, hr'_succ⟩
    have hpos : 1 ≤ (Finset.univ.filter (fun r : Fin K =>
        sSeq ⟨r.val, by omega⟩ ≠ m ∧ sSeq ⟨r.val + 1, by omega⟩ = m)).card :=
      Finset.card_pos.mpr ⟨r', hmem_filt⟩
    unfold seqRuns; omega

lemma seqRuns_ge_two {K : ℕ} {α : Type*} [DecidableEq α] (sSeq : Fin (K + 1) → α) (m : α)
    {r₁ r₂ r₃ : Fin (K + 1)} (h12 : r₁ < r₂) (h23 : r₂ < r₃)
    (hs1 : sSeq r₁ = m) (hs2 : sSeq r₂ ≠ m) (hs3 : sSeq r₃ = m) :
    2 ≤ seqRuns sSeq m := by
  let S1 := Finset.univ.filter (fun r : Fin (K + 1) => r ≤ r₁ ∧ sSeq r = m)
  have hS1 : S1.Nonempty := ⟨r₁, Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_rfl, hs1⟩⟩
  let a := S1.min' hS1
  have ha_mem := (Finset.mem_filter.mp (Finset.min'_mem S1 hS1)).2
  let S2 := Finset.univ.filter (fun r : Fin (K + 1) => r₂ < r ∧ r ≤ r₃ ∧ sSeq r = m)
  have hS2 : S2.Nonempty := ⟨r₃, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h23, le_rfl, hs3⟩⟩
  let b := S2.min' hS2
  have hb_mem := (Finset.mem_filter.mp (Finset.min'_mem S2 hS2)).2
  have hb_gt : r₂.val < b.val := hb_mem.1
  have hb_pos : 0 < b.val := by omega
  let b' : Fin K := ⟨b.val - 1, by omega⟩
  have hb'_ne : sSeq ⟨b'.val, by omega⟩ ≠ m := by
    intro heq
    have hb'_eq : (⟨b'.val, by omega⟩ : Fin (K + 1)) = r₂ ∨ r₂ < (⟨b'.val, by omega⟩ : Fin (K + 1)) := by
      have : r₂.val ≤ b'.val := by dsimp [b']; omega
      rcases eq_or_lt_of_le this with h | h
      · left; exact Fin.ext h.symm
      · right; exact h
    rcases hb'_eq with h | h
    · rw [h] at heq; exact hs2 heq
    · have hmem : (⟨b'.val, by omega⟩ : Fin (K + 1)) ∈ S2 :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, h, by change b'.val ≤ r₃.val; dsimp [b']; omega, heq⟩
      have hle := Finset.min'_le S2 _ hmem
      change b.val ≤ b'.val at hle; dsimp [b'] at hle; omega
  have hb'_succ : sSeq ⟨b'.val + 1, by omega⟩ = m := by
    have heq : (⟨b'.val + 1, by omega⟩ : Fin (K + 1)) = b := Fin.ext (by dsimp [b']; omega)
    rw [heq]; exact hb_mem.2.2
  let T := Finset.univ.filter (fun r : Fin K => sSeq ⟨r.val, by omega⟩ ≠ m ∧ sSeq ⟨r.val + 1, by omega⟩ = m)
  have hb'_T : b' ∈ T := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb'_ne, hb'_succ⟩
  by_cases ha0 : a.val = 0
  · have ha00 : a = 0 := Fin.ext ha0
    have h0eq : sSeq 0 = m := ha00 ▸ ha_mem.2
    have hTpos : 1 ≤ T.card := Finset.card_pos.mpr ⟨b', hb'_T⟩
    unfold seqRuns; rw [if_pos h0eq]
    change 2 ≤ 1 + T.card; omega
  · let a' : Fin K := ⟨a.val - 1, by omega⟩
    have ha'_ne : sSeq ⟨a'.val, by omega⟩ ≠ m := by
      intro heq
      have hmem : (⟨a'.val, by omega⟩ : Fin (K + 1)) ∈ S1 :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, by change a'.val ≤ r₁.val; dsimp [a']; omega, heq⟩
      have hle := Finset.min'_le S1 _ hmem
      change a.val ≤ a'.val at hle; dsimp [a'] at hle; omega
    have ha'_succ : sSeq ⟨a'.val + 1, by omega⟩ = m := by
      have heq : (⟨a'.val + 1, by omega⟩ : Fin (K + 1)) = a := Fin.ext (by dsimp [a']; omega)
      rw [heq]; exact ha_mem.2
    have ha'_T : a' ∈ T := Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha'_ne, ha'_succ⟩
    have ha'_ne_b' : a' ≠ b' := by
      intro heq
      have hval := congrArg Fin.val heq
      dsimp [a', b'] at hval
      have : a.val ≤ r₁.val := ha_mem.1
      have : r₁.val < r₂.val := h12
      omega
    have hT2 : 2 ≤ T.card := by
      have hsub : ({a', b'} : Finset (Fin K)) ⊆ T := by
        intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl <;> assumption
      have hc := Finset.card_le_card hsub
      rwa [Finset.card_pair ha'_ne_b'] at hc
    unfold seqRuns
    change 2 ≤ _ + T.card; omega

lemma sum_seqRuns_eq {K : ℕ} {α : Type*} [DecidableEq α] (sSeq : Fin (K + 1) → α)
    (B : Finset α) (hB : ∀ r : Fin (K + 1), sSeq r ∈ B) :
    ∑ m ∈ B, seqRuns sSeq m =
      1 + (Finset.univ.filter (fun r : Fin K => sSeq ⟨r.val, by omega⟩ ≠ sSeq ⟨r.val + 1, by omega⟩)).card := by
  unfold seqRuns
  rw [Finset.sum_add_distrib]
  have h1 : ∑ m ∈ B, (if sSeq 0 = m then 1 else 0) = 1 := by
    rw [Finset.sum_ite_eq, if_pos (hB 0)]
  have h2 : ∑ m ∈ B, (Finset.univ.filter (fun r : Fin K =>
      sSeq ⟨r.val, by omega⟩ ≠ m ∧ sSeq ⟨r.val + 1, by omega⟩ = m)).card =
      (Finset.univ.filter (fun r : Fin K => sSeq ⟨r.val, by omega⟩ ≠ sSeq ⟨r.val + 1, by omega⟩)).card := by
    simp only [Finset.card_filter]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun r _ => ?_)
    by_cases hne : sSeq ⟨r.val, by omega⟩ ≠ sSeq ⟨r.val + 1, by omega⟩
    · rw [if_pos hne]
      have h_eq : ∑ x ∈ B, (if sSeq ⟨r.val, by omega⟩ ≠ x ∧ sSeq ⟨r.val + 1, by omega⟩ = x then 1 else 0) =
          ∑ x ∈ B, (if sSeq ⟨r.val + 1, by omega⟩ = x then 1 else 0) := by
        refine Finset.sum_congr rfl (fun x _ => ?_)
        by_cases hx : sSeq ⟨r.val + 1, by omega⟩ = x
        · subst hx; simp [hne]
        · simp [hx]
      rw [h_eq, Finset.sum_ite_eq, if_pos (hB ⟨r.val + 1, by omega⟩)]
    · rw [if_neg hne]
      refine Finset.sum_eq_zero (fun x _ => ?_)
      have heq : sSeq ⟨r.val, by omega⟩ = sSeq ⟨r.val + 1, by omega⟩ := not_ne_iff.mp hne
      simp [heq]
  rw [h1, h2]

private lemma xCross_card_pos (G : GenericVSystem) : 0 < (X_cross G.f).card := by
  have hK_eq := X_cross_card G
  have hT3_le : T3 G ≤ 10 := by
    calc T3 G ≤ pair5.card := Finset.card_filter_le _ _
      _ = 10 := pair5_card
  have hT1_le : T1 G ≤ T3bar G := T1_le_T3bar G
  have hT3bar_eq : T3bar G = 10 - T3 G := rfl
  omega

private noncomputable def sweepXi (G : GenericVSystem) : Fin (X_cross G.f).card ↪o ℝ :=
  (X_cross G.f).orderEmbOfFin rfl

private noncomputable def sweepTau (G : GenericVSystem) (r : Fin ((X_cross G.f).card + 1)) : ℝ :=
  if hK : (X_cross G.f).card = 0 then 0
  else if hr0 : r.val = 0 then sweepXi G ⟨0, Nat.pos_of_ne_zero hK⟩ - 1
  else if hrK : r.val = (X_cross G.f).card then
    sweepXi G ⟨(X_cross G.f).card - 1, Nat.sub_lt (Nat.pos_of_ne_zero hK) Nat.one_pos⟩ + 1
  else (sweepXi G ⟨r.val - 1, by omega⟩ + sweepXi G ⟨r.val, by omega⟩) / 2

private lemma sweepTau_lt_xi (G : GenericVSystem) (r : Fin (X_cross G.f).card) :
    sweepTau G ⟨r.val, by omega⟩ < sweepXi G r := by
  have hK : (X_cross G.f).card ≠ 0 := Nat.ne_of_gt (xCross_card_pos G)
  dsimp [sweepTau]
  split_ifs with hK0 hr0 hrK
  · exact absurd hK0 hK
  · have h0 : (⟨0, Nat.pos_of_ne_zero hK0⟩ : Fin (X_cross G.f).card) = r := by ext; exact hr0.symm
    rw [h0]; linarith
  · exfalso; omega
  · have hlt := (sweepXi G).strictMono
      (show (⟨r.val - 1, by omega⟩ : Fin (X_cross G.f).card) < r by change r.val - 1 < r.val; omega)
    linarith

private lemma xi_lt_sweepTau (G : GenericVSystem) (r : Fin (X_cross G.f).card) :
    sweepXi G r < sweepTau G ⟨r.val + 1, by omega⟩ := by
  have hK : (X_cross G.f).card ≠ 0 := Nat.ne_of_gt (xCross_card_pos G)
  dsimp [sweepTau]
  split_ifs with hK0 hrK
  · exact absurd hK0 hK
  · have hlast :
        (⟨(X_cross G.f).card - 1, Nat.sub_lt (Nat.pos_of_ne_zero hK0) Nat.one_pos⟩ :
          Fin (X_cross G.f).card) = r := by
      ext; dsimp; omega
    rw [hlast]; linarith
  · have hlt := (sweepXi G).strictMono
      (show r < (⟨r.val + 1, by omega⟩ : Fin (X_cross G.f).card) by change r.val < r.val + 1; omega)
    linarith

private lemma sweepTau_step (G : GenericVSystem) (m : ℕ) (hm : m < (X_cross G.f).card) :
    sweepTau G ⟨m, by omega⟩ < sweepTau G ⟨m + 1, by omega⟩ :=
  lt_trans (sweepTau_lt_xi G ⟨m, hm⟩) (xi_lt_sweepTau G ⟨m, hm⟩)

private lemma sweepTau_strictMono (G : GenericVSystem) : StrictMono (sweepTau G) := by
  intro a b hab
  have ha := a.isLt; have hb := b.isLt
  have h_ind : ∀ d m : ℕ, (hmd : m + d ≤ (X_cross G.f).card) → (hd : 1 ≤ d) →
      sweepTau G ⟨m, by omega⟩ < sweepTau G ⟨m + d, by omega⟩ := by
    intro d; induction d with
    | zero => intro _ _ hd; omega
    | succ d ih =>
      intro m hmd _
      by_cases hd0 : d = 0
      · subst hd0; exact sweepTau_step G m (by omega)
      · exact lt_trans (ih m (by omega) (by omega)) (sweepTau_step G (m + d) (by omega))
  have hres := h_ind (b.val - a.val) a.val (by omega) (by change a.val < b.val at hab; omega)
  have haeq : (⟨a.val, by omega⟩ : Fin ((X_cross G.f).card + 1)) = a := rfl
  have hbeq : (⟨a.val + (b.val - a.val), by omega⟩ : Fin ((X_cross G.f).card + 1)) = b := by
    ext; dsimp; change a.val < b.val at hab; omega
  rwa [haeq, hbeq] at hres

private lemma sweepTau_not_mem (G : GenericVSystem) (r : Fin ((X_cross G.f).card + 1)) :
    sweepTau G r ∉ X_cross G.f := by
  intro hmem
  have hrange : sweepTau G r ∈ Set.range (sweepXi G) := by
    simpa [sweepXi, Finset.range_orderEmbOfFin] using hmem
  rcases hrange with ⟨k, hk⟩
  rcases lt_trichotomy r.val k.val with hlt | heq | hgt
  · have h1 := sweepTau_lt_xi G ⟨r.val, by omega⟩
    have h2 : sweepXi G ⟨r.val, by omega⟩ < sweepXi G k := (sweepXi G).strictMono hlt
    linarith
  · have h1 := sweepTau_lt_xi G k
    have hreq : (⟨k.val, by omega⟩ : Fin ((X_cross G.f).card + 1)) = r := by ext; exact heq.symm
    rw [hreq] at h1
    linarith
  · by_cases h_eq : r.val = k.val + 1
    · have h1 := xi_lt_sweepTau G k
      have hreq : (⟨k.val + 1, by omega⟩ : Fin ((X_cross G.f).card + 1)) = r := by ext; exact h_eq.symm
      rw [hreq] at h1
      linarith
    · have h1 := xi_lt_sweepTau G k
      have h2 : sweepTau G ⟨k.val + 1, by omega⟩ < sweepXi G ⟨k.val + 1, by omega⟩ :=
        sweepTau_lt_xi G ⟨k.val + 1, by omega⟩
      have h3 : sweepXi G ⟨k.val + 1, by omega⟩ ≤ sweepXi G ⟨r.val - 1, by omega⟩ := by
        by_cases heq2 : k.val + 1 = r.val - 1
        · have : (⟨k.val + 1, by omega⟩ : Fin (X_cross G.f).card) = ⟨r.val - 1, by omega⟩ := by
            ext; exact heq2
          rw [this]
        · exact le_of_lt ((sweepXi G).strictMono (by change k.val + 1 < r.val - 1; omega))
      have h4 : sweepXi G ⟨r.val - 1, by omega⟩ < sweepTau G r := by
        have := xi_lt_sweepTau G ⟨r.val - 1, by omega⟩
        have hreq : (⟨r.val - 1 + 1, by omega⟩ : Fin ((X_cross G.f).card + 1)) = r := by
          ext; dsimp; omega
        rwa [hreq] at this
      linarith

private lemma locate_avoiding_X (G : GenericVSystem) (x : ℝ) (hx : x ∉ X_cross G.f) :
    ∃ r : Fin ((X_cross G.f).card + 1),
      (∀ k : Fin (X_cross G.f).card, k.val < r.val → sweepXi G k < x) ∧
      (∀ k : Fin (X_cross G.f).card, r.val ≤ k.val → x < sweepXi G k) := by
  let S_lt := (Finset.univ : Finset (Fin (X_cross G.f).card)).filter (fun k => sweepXi G k < x)
  by_cases hS : S_lt.Nonempty
  · let km := S_lt.max' hS
    have hkm_mem := (Finset.mem_filter.mp (Finset.max'_mem S_lt hS)).2
    refine ⟨⟨km.val + 1, by omega⟩, ?_, ?_⟩
    · intro k hk
      have hle : k ≤ km := by change k.val ≤ km.val; dsimp at hk; omega
      exact lt_of_le_of_lt ((sweepXi G).monotone hle) hkm_mem
    · intro k hk
      have hk' : km.val < k.val := by dsimp at hk; omega
      have hnot : k ∉ S_lt := fun hm => by
        have hle := Finset.le_max' S_lt k hm
        change k.val ≤ km.val at hle
        omega
      have hle : x ≤ sweepXi G k :=
        not_lt.mp (fun hlt => hnot (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt⟩))
      refine lt_of_le_of_ne hle (fun heq => hx ?_)
      rw [heq]
      exact Finset.orderEmbOfFin_mem (X_cross G.f) rfl k
  · rw [Finset.not_nonempty_iff_eq_empty] at hS
    refine ⟨⟨0, Nat.zero_lt_succ _⟩, fun k hk => False.elim (Nat.not_lt_zero _ hk), fun k _ => ?_⟩
    have hnot : k ∉ S_lt := by rw [hS]; exact Finset.notMem_empty _
    have hle : x ≤ sweepXi G k :=
      not_lt.mp (fun hlt => hnot (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt⟩))
    refine lt_of_le_of_ne hle (fun heq => hx ?_)
    rw [heq]
    exact Finset.orderEmbOfFin_mem (X_cross G.f) rfl k

private lemma same_interval_lt_iff (G : GenericVSystem)
    (x : ℝ) (r : Fin ((X_cross G.f).card + 1))
    (hx_gt : ∀ k : Fin (X_cross G.f).card, k.val < r.val → sweepXi G k < x)
    (hx_lt : ∀ k : Fin (X_cross G.f).card, r.val ≤ k.val → x < sweepXi G k)
    (i j : Fin 5) :
    (G.f i).eval x < (G.f j).eval x ↔ (G.f i).eval (sweepTau G r) < (G.f j).eval (sweepTau G r) := by
  have hτ_gt : ∀ k : Fin (X_cross G.f).card, k.val < r.val → sweepXi G k < sweepTau G r := by
    intro k hk
    have h1 : sweepXi G k < sweepTau G ⟨k.val + 1, by omega⟩ := xi_lt_sweepTau G k
    have h2 : sweepTau G ⟨k.val + 1, by omega⟩ ≤ sweepTau G r :=
      (sweepTau_strictMono G).monotone (by change k.val + 1 ≤ r.val; exact hk)
    linarith
  have hτ_lt : ∀ k : Fin (X_cross G.f).card, r.val ≤ k.val → sweepTau G r < sweepXi G k := by
    intro k hk
    have h1 : sweepTau G ⟨k.val, by omega⟩ < sweepXi G k := sweepTau_lt_xi G k
    have h2 : sweepTau G r ≤ sweepTau G ⟨k.val, by omega⟩ :=
      (sweepTau_strictMono G).monotone (by change r.val ≤ k.val; exact hk)
    linarith
  by_cases hij_ne : i = j
  · subst hij_ne; simp
  · have hno_root : ∀ z ∈ Set.uIcc x (sweepTau G r), (G.f i).eval z ≠ (G.f j).eval z := by
      intro z hz heq
      have hzX : z ∈ X_cross G.f := by
        rcases lt_or_gt_of_ne hij_ne with hij | hji
        · exact Finset.mem_biUnion.mpr ⟨(i, j), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hij⟩,
            (mem_Z_set G hij z).mpr heq⟩
        · exact Finset.mem_biUnion.mpr ⟨(j, i), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hji⟩,
            (mem_Z_set G hji z).mpr heq.symm⟩
      have hrange : z ∈ Set.range (sweepXi G) := by
        simpa [sweepXi, Finset.range_orderEmbOfFin] using hzX
      rcases hrange with ⟨k, rfl⟩
      rcases lt_or_ge k.val r.val with hk | hk
      · have h1 := hx_gt k hk; have h2 := hτ_gt k hk
        rcases Set.mem_uIcc.mp hz with ⟨_, _⟩ | ⟨_, _⟩ <;> linarith
      · have h1 := hx_lt k hk; have h2 := hτ_lt k hk
        rcases Set.mem_uIcc.mp hz with ⟨_, _⟩ | ⟨_, _⟩ <;> linarith
    let diff (z : ℝ) : ℝ := (G.f i).eval z - (G.f j).eval z
    have hcont : Continuous diff := (continuous_eval_vfunc (G.f i)).sub (continuous_eval_vfunc (G.f j))
    constructor <;> intro hlt
    · by_contra hnot
      have hle : (G.f j).eval (sweepTau G r) ≤ (G.f i).eval (sweepTau G r) := not_lt.mp hnot
      have h0 : (0 : ℝ) ∈ Set.Icc (diff x) (diff (sweepTau G r)) :=
        ⟨by dsimp [diff]; linarith, by dsimp [diff]; linarith⟩
      obtain ⟨z, hz_mem, hz_zero⟩ := intermediate_value_uIcc hcont.continuousOn
        (Set.mem_uIcc.mpr (Or.inl h0))
      exact hno_root z hz_mem (sub_eq_zero.mp hz_zero)
    · by_contra hnot
      have hle : (G.f j).eval x ≤ (G.f i).eval x := not_lt.mp hnot
      have h0 : (0 : ℝ) ∈ Set.Icc (diff (sweepTau G r)) (diff x) :=
        ⟨by dsimp [diff]; linarith, by dsimp [diff]; linarith⟩
      obtain ⟨z, hz_mem, hz_zero⟩ := intermediate_value_uIcc hcont.continuousOn
        (Set.mem_uIcc.mpr (Or.inr h0))
      exact hno_root z hz_mem (sub_eq_zero.mp hz_zero)

private lemma distinct_eval_of_not_mem (G : GenericVSystem) (x : ℝ) (hx : x ∉ X_cross G.f) :
    Function.Injective (fun i : Fin 5 => (G.f i).eval x) := by
  intro i j heq
  by_contra hne
  apply hx
  rcases lt_or_gt_of_ne hne with hij | hji
  · exact Finset.mem_biUnion.mpr ⟨(i, j), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hij⟩,
      (mem_Z_set G hij x).mpr heq⟩
  · exact Finset.mem_biUnion.mpr ⟨(j, i), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hji⟩,
      (mem_Z_set G hji x).mpr heq.symm⟩

private noncomputable def sweepSSeq (G : GenericVSystem) (q : ℕ)
    (r : Fin ((X_cross G.f).card + 1)) : Finset (Fin 5) :=
  bottomK (fun i => (G.f i).eval (sweepTau G r)) q

private lemma sweep_xi_unique_pair (G : GenericVSystem) (r : Fin (X_cross G.f).card) :
    ∃ i₀ j₀ : Fin 5, i₀ < j₀ ∧
      (G.f i₀).eval (sweepXi G r) = (G.f j₀).eval (sweepXi G r) ∧
      (∀ k l : Fin 5, k < l → (G.f k).eval (sweepXi G r) = (G.f l).eval (sweepXi G r) →
        (k, l) = (i₀, j₀)) := by
  have hr_mem : sweepXi G r ∈ X_cross G.f := Finset.orderEmbOfFin_mem (X_cross G.f) rfl r
  rcases Finset.mem_biUnion.mp hr_mem with ⟨⟨i₀, j₀⟩, hp, hz⟩
  have hij : i₀ < j₀ := (Finset.mem_filter.mp hp).2
  refine ⟨i₀, j₀, hij, (mem_Z_set G hij (sweepXi G r)).mp hz, fun k l hkl heq => ?_⟩
  by_contra hne
  exact G.gpb_disj k l i₀ j₀ hkl hij hne (sweepXi G r) ⟨heq, (mem_Z_set G hij (sweepXi G r)).mp hz⟩

set_option maxHeartbeats 400000 in
private lemma sweep_unique_jump (G : GenericVSystem) (r : Fin (X_cross G.f).card) :
    ∃ q₀ : ℕ, 1 ≤ q₀ ∧ q₀ ≤ 4 ∧
      (∀ q : ℕ, q ≤ 5 → q ≠ q₀ →
        sweepSSeq G q ⟨r.val, by omega⟩ = sweepSSeq G q ⟨r.val + 1, by omega⟩) ∧
      sweepSSeq G q₀ ⟨r.val, by omega⟩ ≠ sweepSSeq G q₀ ⟨r.val + 1, by omega⟩ ∧
      (q₀ = 4 ↔ ∃ i j : Fin 5, i < j ∧
        (G.f i).eval (sweepXi G r) = (G.f j).eval (sweepXi G r) ∧
        (G.f i).eval (sweepXi G r) = F_top G.f (sweepXi G r)) := by
  let ξ := sweepXi G
  let τ := sweepTau G
  obtain ⟨i₀, j₀, hij, heq, hunique⟩ := sweep_xi_unique_pair G r
  let v₀ := (G.f i₀).eval (ξ r)
  have h_other_ne : ∀ k : Fin 5, k ≠ i₀ → k ≠ j₀ → (G.f k).eval (ξ r) ≠ v₀ := by
    intro k hki hkj heqk
    rcases lt_or_gt_of_ne hki with hlt | hgt
    · have := hunique k i₀ hlt heqk; exact (ne_of_lt hij) (congrArg Prod.snd this)
    · have := hunique i₀ k hgt heqk.symm; exact hkj (congrArg Prod.snd this)
  have h_keep_sign : ∀ (k : Fin 5) (r' : Fin ((X_cross G.f).card + 1)),
      (r'.val = r.val ∨ r'.val = r.val + 1) → k ≠ i₀ → k ≠ j₀ →
      ((G.f k).eval (ξ r) < v₀ → (G.f k).eval (τ r') < (G.f i₀).eval (τ r') ∧
        (G.f k).eval (τ r') < (G.f j₀).eval (τ r')) ∧
      (v₀ < (G.f k).eval (ξ r) → (G.f i₀).eval (τ r') < (G.f k).eval (τ r') ∧
        (G.f j₀).eval (τ r') < (G.f k).eval (τ r')) := by
    intro k r' hr' hki hkj
    have hno_root_pair : ∀ m : Fin 5, m ≠ k → (m = i₀ ∨ m = j₀) →
        ∀ z ∈ Set.uIcc (ξ r) (τ r'), (G.f k).eval z ≠ (G.f m).eval z := by
      intro m hmk hm z hz heqz
      have hzX : z ∈ X_cross G.f := by
        rcases lt_or_gt_of_ne hmk with h1 | h2
        · exact Finset.mem_biUnion.mpr ⟨(m, k), Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1⟩,
            (mem_Z_set G h1 z).mpr heqz.symm⟩
        · exact Finset.mem_biUnion.mpr ⟨(k, m), Finset.mem_filter.mpr ⟨Finset.mem_univ _, h2⟩,
            (mem_Z_set G h2 z).mpr heqz⟩
      have hrange : z ∈ Set.range ξ := by simpa [ξ, sweepXi, Finset.range_orderEmbOfFin] using hzX
      rcases hrange with ⟨k', rfl⟩
      by_cases hk'r : k' = r
      · subst hk'r
        rcases hm with rfl | rfl
        · exact h_other_ne k hki hkj heqz
        · exact h_other_ne k hki hkj (by linarith)
      · have hlt_or_gt := lt_or_gt_of_ne hk'r
        rcases hr' with h_eq | h_eq
        · have hτ : τ r' < ξ r := by
            have hreq : r' = ⟨r.val, by omega⟩ := Fin.ext h_eq
            rw [hreq]; exact sweepTau_lt_xi G r
          rcases Set.mem_uIcc.mp hz with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · linarith
          · rcases hlt_or_gt with hlt | hgt
            · have h1' : ξ k' < τ ⟨k'.val + 1, by omega⟩ := xi_lt_sweepTau G k'
              have h2' : τ ⟨k'.val + 1, by omega⟩ ≤ τ r' :=
                (sweepTau_strictMono G).monotone (by change k'.val + 1 ≤ r'.val; have : k'.val < r.val := hlt; omega)
              linarith
            · have : ξ r < ξ k' := ξ.strictMono hgt
              linarith
        · have hτ : ξ r < τ r' := by
            have hreq : r' = ⟨r.val + 1, by omega⟩ := Fin.ext h_eq
            rw [hreq]; exact xi_lt_sweepTau G r
          rcases Set.mem_uIcc.mp hz with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · rcases hlt_or_gt with hlt | hgt
            · have : ξ k' < ξ r := ξ.strictMono hlt
              linarith
            · have h1' : τ ⟨k'.val, by omega⟩ < ξ k' := sweepTau_lt_xi G k'
              have h2' : τ r' ≤ τ ⟨k'.val, by omega⟩ :=
                (sweepTau_strictMono G).monotone (by change r'.val ≤ k'.val; have : r.val < k'.val := hgt; omega)
              linarith
          · linarith
    have ivt_lt : ∀ m : Fin 5, m ≠ k → (m = i₀ ∨ m = j₀) →
        (G.f k).eval (ξ r) < (G.f m).eval (ξ r) → (G.f k).eval (τ r') < (G.f m).eval (τ r') := by
      intro m hmk hm hlt
      by_contra hnot
      have hle : (G.f m).eval (τ r') ≤ (G.f k).eval (τ r') := not_lt.mp hnot
      let diff (z : ℝ) := (G.f k).eval z - (G.f m).eval z
      have hcont : Continuous diff := (continuous_eval_vfunc (G.f k)).sub (continuous_eval_vfunc (G.f m))
      have h0 : (0 : ℝ) ∈ Set.Icc (diff (ξ r)) (diff (τ r')) :=
        ⟨by dsimp [diff]; linarith, by dsimp [diff]; linarith⟩
      obtain ⟨z, hz_mem, hz_zero⟩ := intermediate_value_uIcc hcont.continuousOn (Set.mem_uIcc.mpr (Or.inl h0))
      exact hno_root_pair m hmk hm z hz_mem (sub_eq_zero.mp hz_zero)
    have ivt_gt : ∀ m : Fin 5, m ≠ k → (m = i₀ ∨ m = j₀) →
        (G.f m).eval (ξ r) < (G.f k).eval (ξ r) → (G.f m).eval (τ r') < (G.f k).eval (τ r') := by
      intro m hmk hm hgt
      by_contra hnot
      have hle : (G.f k).eval (τ r') ≤ (G.f m).eval (τ r') := not_lt.mp hnot
      let diff (z : ℝ) := (G.f k).eval z - (G.f m).eval z
      have hcont : Continuous diff := (continuous_eval_vfunc (G.f k)).sub (continuous_eval_vfunc (G.f m))
      have h0 : (0 : ℝ) ∈ Set.Icc (diff (τ r')) (diff (ξ r)) :=
        ⟨by dsimp [diff]; linarith, by dsimp [diff]; linarith⟩
      obtain ⟨z, hz_mem, hz_zero⟩ := intermediate_value_uIcc hcont.continuousOn (Set.mem_uIcc.mpr (Or.inr h0))
      exact hno_root_pair m hmk hm z hz_mem (sub_eq_zero.mp hz_zero)
    exact ⟨fun hlt => ⟨ivt_lt i₀ hki.symm (Or.inl rfl) hlt,
                       ivt_lt j₀ hkj.symm (Or.inr rfl) (by linarith)⟩,
           fun hgt => ⟨ivt_gt i₀ hki.symm (Or.inl rfl) hgt,
                       ivt_gt j₀ hkj.symm (Or.inr rfl) (by linarith)⟩⟩
  have hij_swap : ((G.f i₀).eval (τ ⟨r.val, by omega⟩) < (G.f j₀).eval (τ ⟨r.val, by omega⟩) ∧
                   (G.f j₀).eval (τ ⟨r.val + 1, by omega⟩) < (G.f i₀).eval (τ ⟨r.val + 1, by omega⟩)) ∨
                  ((G.f j₀).eval (τ ⟨r.val, by omega⟩) < (G.f i₀).eval (τ ⟨r.val, by omega⟩) ∧
                   (G.f i₀).eval (τ ⟨r.val + 1, by omega⟩) < (G.f j₀).eval (τ ⟨r.val + 1, by omega⟩)) := by
    have hki_ne : ξ r ≠ kink G.f i₀ := fun h => G.gpb_kink i₀ j₀ i₀ hij (by rw [← h]; exact heq)
    have hkj_ne : ξ r ≠ kink G.f j₀ := fun h => G.gpb_kink i₀ j₀ j₀ hij (by rw [← h]; exact heq)
    let δ_loc : ℝ := min (min |ξ r - kink G.f i₀| |ξ r - kink G.f j₀|)
      (min (ξ r - τ ⟨r.val, by omega⟩) (τ ⟨r.val + 1, by omega⟩ - ξ r)) / 2
    have hδ_loc : 0 < δ_loc := by
      have h1 : 0 < |ξ r - kink G.f i₀| := abs_pos.mpr (sub_ne_zero.mpr hki_ne)
      have h2 : 0 < |ξ r - kink G.f j₀| := abs_pos.mpr (sub_ne_zero.mpr hkj_ne)
      have h3 : 0 < ξ r - τ ⟨r.val, by omega⟩ := sub_pos.mpr (sweepTau_lt_xi G r)
      have h4 : 0 < τ ⟨r.val + 1, by omega⟩ - ξ r := sub_pos.mpr (xi_lt_sweepTau G r)
      exact div_pos (lt_min (lt_min h1 h2) (lt_min h3 h4)) zero_lt_two
    have h_no_other_root : ∀ z ∈ Set.Icc (τ ⟨r.val, by omega⟩) (τ ⟨r.val + 1, by omega⟩),
        z ≠ ξ r → (G.f i₀).eval z ≠ (G.f j₀).eval z := by
      intro z hz hzne heqz
      have hzX : z ∈ X_cross G.f :=
        Finset.mem_biUnion.mpr ⟨(i₀, j₀), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hij⟩,
          (mem_Z_set G hij z).mpr heqz⟩
      have hrange : z ∈ Set.range ξ := by simpa [ξ, sweepXi, Finset.range_orderEmbOfFin] using hzX
      rcases hrange with ⟨k', rfl⟩
      have hkne : k' ≠ r := fun h => hzne (congrArg ξ h)
      rcases lt_or_gt_of_ne hkne with hlt | hgt
      · have h1' : ξ k' < τ ⟨k'.val + 1, by omega⟩ := xi_lt_sweepTau G k'
        have h2' : τ ⟨k'.val + 1, by omega⟩ ≤ τ ⟨r.val, by omega⟩ :=
          (sweepTau_strictMono G).monotone (by change k'.val + 1 ≤ r.val; exact hlt)
        linarith [hz.1]
      · have h1' : τ ⟨k'.val, by omega⟩ < ξ k' := sweepTau_lt_xi G k'
        have h2' : τ ⟨r.val + 1, by omega⟩ ≤ τ ⟨k'.val, by omega⟩ :=
          (sweepTau_strictMono G).monotone (by change r.val + 1 ≤ k'.val; exact hgt)
        linarith [hz.2]
    let zL := ξ r - δ_loc
    let zR := ξ r + δ_loc
    have hz_bounds : τ ⟨r.val, by omega⟩ < zL ∧ zL < ξ r ∧ ξ r < zR ∧ zR < τ ⟨r.val + 1, by omega⟩ := by
      have h3 : δ_loc < ξ r - τ ⟨r.val, by omega⟩ := by
        have hle := le_trans (min_le_right (min |ξ r - kink G.f i₀| |ξ r - kink G.f j₀|)
          (min (ξ r - τ ⟨r.val, by omega⟩) (τ ⟨r.val + 1, by omega⟩ - ξ r))) (min_le_left _ _)
        have h30 : 0 < ξ r - τ ⟨r.val, by omega⟩ := sub_pos.mpr (sweepTau_lt_xi G r)
        have hδ_le : δ_loc ≤ (ξ r - τ ⟨r.val, by omega⟩) / 2 := by
          dsimp [δ_loc]; exact div_le_div_of_nonneg_right hle (by norm_num)
        linarith
      have h4 : δ_loc < τ ⟨r.val + 1, by omega⟩ - ξ r := by
        have hle := le_trans (min_le_right (min |ξ r - kink G.f i₀| |ξ r - kink G.f j₀|)
          (min (ξ r - τ ⟨r.val, by omega⟩) (τ ⟨r.val + 1, by omega⟩ - ξ r))) (min_le_right _ _)
        have h40 : 0 < τ ⟨r.val + 1, by omega⟩ - ξ r := sub_pos.mpr (xi_lt_sweepTau G r)
        have hδ_le : δ_loc ≤ (τ ⟨r.val + 1, by omega⟩ - ξ r) / 2 := by
          dsimp [δ_loc]; exact div_le_div_of_nonneg_right hle (by norm_num)
        linarith
      dsimp [zL, zR]
      exact ⟨by linarith, by linarith [hδ_loc], by linarith [hδ_loc], by linarith⟩
    have h_same_side : ∀ (c : Fin 5) (hc : c = i₀ ∨ c = j₀),
        ∃ b : Bool, (G.f c).eval (ξ r) = (dualPt G.f (c, b)).1 * (ξ r) + (dualPt G.f (c, b)).2 ∧
          (G.f c).eval zL = (dualPt G.f (c, b)).1 * zL + (dualPt G.f (c, b)).2 ∧
          (G.f c).eval zR = (dualPt G.f (c, b)).1 * zR + (dualPt G.f (c, b)).2 := by
      intro c hc
      have hne_c : ξ r ≠ kink G.f c := by rcases hc with rfl | rfl <;> assumption
      have hδc : δ_loc < |ξ r - kink G.f c| := by
        have h1 := min_le_left (min |ξ r - kink G.f i₀| |ξ r - kink G.f j₀|)
          (min (ξ r - τ ⟨r.val, by omega⟩) (τ ⟨r.val + 1, by omega⟩ - ξ r))
        have hle : min |ξ r - kink G.f i₀| |ξ r - kink G.f j₀| ≤ |ξ r - kink G.f c| := by
          rcases hc with rfl | rfl
          · exact min_le_left _ _
          · exact min_le_right _ _
        have hpos : 0 < |ξ r - kink G.f c| := abs_pos.mpr (sub_ne_zero.mpr hne_c)
        have hδ_le : δ_loc ≤ |ξ r - kink G.f c| / 2 := by
          dsimp [δ_loc]; exact div_le_div_of_nonneg_right (le_trans h1 hle) (by norm_num)
        linarith
      have hk_def : kink G.f c = ((G.f c).b - (G.f c).d) / ((G.f c).c - (G.f c).a) := rfl
      rcases lt_or_gt_of_ne hne_c with hlt | hgt
      · have h_abs : |ξ r - kink G.f c| = -(ξ r - kink G.f c) := abs_of_neg (sub_neg.mpr hlt)
        refine ⟨false,
          VFunc.eval_left (G.f c) (G.ac c) (by rw [← hk_def]; linarith),
          VFunc.eval_left (G.f c) (G.ac c) (by rw [← hk_def]; dsimp [zL]; linarith),
          VFunc.eval_left (G.f c) (G.ac c) (by rw [← hk_def]; dsimp [zR]; linarith)⟩
      · have h_abs : |ξ r - kink G.f c| = ξ r - kink G.f c := abs_of_pos (sub_pos.mpr hgt)
        refine ⟨true,
          VFunc.eval_right (G.f c) (G.ac c) (by rw [← hk_def]; linarith),
          VFunc.eval_right (G.f c) (G.ac c) (by rw [← hk_def]; dsimp [zL]; linarith),
          VFunc.eval_right (G.f c) (G.ac c) (by rw [← hk_def]; dsimp [zR]; linarith)⟩
    obtain ⟨bi, hbi0, hbiL, hbiR⟩ := h_same_side i₀ (Or.inl rfl)
    obtain ⟨bj, hbj0, hbjL, hbjR⟩ := h_same_side j₀ (Or.inr rfl)
    have hsl_ne : (dualPt G.f (i₀, bi)).1 ≠ (dualPt G.f (j₀, bj)).1 :=
      fun h => (ne_of_lt hij) (congrArg Prod.fst (G.slopes_inj h))
    have transport : ∀ a b : ℝ, τ ⟨r.val, by omega⟩ ≤ a → a ≤ b → b ≤ τ ⟨r.val + 1, by omega⟩ →
        (∀ z ∈ Set.Icc a b, z ≠ ξ r) →
        ((G.f i₀).eval a < (G.f j₀).eval a ↔ (G.f i₀).eval b < (G.f j₀).eval b) := by
      intro a b ha_lo hab hb_hi hne
      let diff (z : ℝ) : ℝ := (G.f i₀).eval z - (G.f j₀).eval z
      have hcont : Continuous diff := (continuous_eval_vfunc (G.f i₀)).sub (continuous_eval_vfunc (G.f j₀))
      have hno : ∀ z ∈ Set.Icc a b, diff z ≠ 0 := fun z hz heq =>
        h_no_other_root z ⟨le_trans ha_lo hz.1, le_trans hz.2 hb_hi⟩ (hne z hz) (sub_eq_zero.mp heq)
      constructor <;> intro hlt
      · by_contra hnot
        have hle : (G.f j₀).eval b ≤ (G.f i₀).eval b := not_lt.mp hnot
        have h0 : (0 : ℝ) ∈ Set.Icc (diff a) (diff b) := ⟨by dsimp [diff]; linarith, by dsimp [diff]; linarith⟩
        obtain ⟨z, hz, hzero⟩ := intermediate_value_Icc hab hcont.continuousOn h0
        exact hno z hz hzero
      · by_contra hnot
        have hle : (G.f j₀).eval a ≤ (G.f i₀).eval a := not_lt.mp hnot
        have h0 : (0 : ℝ) ∈ Set.Icc (diff b) (diff a) := ⟨by dsimp [diff]; linarith, by dsimp [diff]; linarith⟩
        obtain ⟨z, hz, hzero⟩ := intermediate_value_Icc' hab hcont.continuousOn h0
        exact hno z hz hzero
    have htL : (G.f i₀).eval (τ ⟨r.val, by omega⟩) < (G.f j₀).eval (τ ⟨r.val, by omega⟩) ↔
        (G.f i₀).eval zL < (G.f j₀).eval zL :=
      transport _ _ le_rfl (le_of_lt hz_bounds.1)
        (le_of_lt (lt_trans hz_bounds.2.1 (lt_trans hz_bounds.2.2.1 hz_bounds.2.2.2)))
        (fun z hz hzx => by linarith [hz.2, hz_bounds.2.1])
    have htL' : (G.f j₀).eval (τ ⟨r.val, by omega⟩) < (G.f i₀).eval (τ ⟨r.val, by omega⟩) ↔
        (G.f j₀).eval zL < (G.f i₀).eval zL := by
      have hne_τ : (G.f i₀).eval (τ ⟨r.val, by omega⟩) ≠ (G.f j₀).eval (τ ⟨r.val, by omega⟩) :=
        fun h => h_no_other_root _ ⟨le_rfl, le_of_lt (lt_trans (sweepTau_lt_xi G r) (xi_lt_sweepTau G r))⟩
          (ne_of_lt (sweepTau_lt_xi G r)) h
      have hne_zL : (G.f i₀).eval zL ≠ (G.f j₀).eval zL :=
        fun h => h_no_other_root _ ⟨le_of_lt hz_bounds.1,
          le_of_lt (lt_trans hz_bounds.2.1 (lt_trans hz_bounds.2.2.1 hz_bounds.2.2.2))⟩
          (ne_of_lt hz_bounds.2.1) h
      constructor <;> intro h
      · exact lt_of_le_of_ne (not_lt.mp (fun hlt => lt_asymm h (htL.mpr hlt))) hne_zL.symm
      · exact lt_of_le_of_ne (not_lt.mp (fun hlt => lt_asymm h (htL.mp hlt))) hne_τ.symm
    have htR : (G.f i₀).eval zR < (G.f j₀).eval zR ↔
        (G.f i₀).eval (τ ⟨r.val + 1, by omega⟩) < (G.f j₀).eval (τ ⟨r.val + 1, by omega⟩) :=
      transport _ _ (le_of_lt (lt_trans hz_bounds.1 (lt_trans hz_bounds.2.1 hz_bounds.2.2.1)))
        (le_of_lt hz_bounds.2.2.2) le_rfl (fun z hz hzx => by linarith [hz.1, hz_bounds.2.2.1])
    have htR' : (G.f j₀).eval zR < (G.f i₀).eval zR ↔
        (G.f j₀).eval (τ ⟨r.val + 1, by omega⟩) < (G.f i₀).eval (τ ⟨r.val + 1, by omega⟩) := by
      have hne_τ : (G.f i₀).eval (τ ⟨r.val + 1, by omega⟩) ≠ (G.f j₀).eval (τ ⟨r.val + 1, by omega⟩) :=
        fun h => h_no_other_root _ ⟨le_of_lt (lt_trans (sweepTau_lt_xi G r) (xi_lt_sweepTau G r)), le_rfl⟩
          (ne_of_gt (xi_lt_sweepTau G r)) h
      have hne_zR : (G.f i₀).eval zR ≠ (G.f j₀).eval zR :=
        fun h => h_no_other_root _ ⟨le_of_lt (lt_trans hz_bounds.1 (lt_trans hz_bounds.2.1 hz_bounds.2.2.1)),
          le_of_lt hz_bounds.2.2.2⟩ (ne_of_gt hz_bounds.2.2.1) h
      constructor <;> intro h
      · exact lt_of_le_of_ne (not_lt.mp (fun hlt => lt_asymm h (htR.mpr hlt))) hne_τ.symm
      · exact lt_of_le_of_ne (not_lt.mp (fun hlt => lt_asymm h (htR.mp hlt))) hne_zR.symm
    have heq_lin : (dualPt G.f (i₀, bi)).1 * ξ r + (dualPt G.f (i₀, bi)).2 =
        (dualPt G.f (j₀, bj)).1 * ξ r + (dualPt G.f (j₀, bj)).2 := by linarith
    rcases lt_or_gt_of_ne hsl_ne with h_sl | h_sl
    · right
      have hdiff_pos : 0 < ((dualPt G.f (j₀, bj)).1 - (dualPt G.f (i₀, bi)).1) * δ_loc :=
        mul_pos (sub_pos.mpr h_sl) hδ_loc
      have hL : (G.f j₀).eval zL < (G.f i₀).eval zL := by
        rw [hbiL, hbjL]
        have h_id : (dualPt G.f (i₀, bi)).1 * zL + (dualPt G.f (i₀, bi)).2 -
            ((dualPt G.f (j₀, bj)).1 * zL + (dualPt G.f (j₀, bj)).2) =
            ((dualPt G.f (i₀, bi)).1 * ξ r + (dualPt G.f (i₀, bi)).2 -
              ((dualPt G.f (j₀, bj)).1 * ξ r + (dualPt G.f (j₀, bj)).2)) +
            ((dualPt G.f (j₀, bj)).1 - (dualPt G.f (i₀, bi)).1) * δ_loc := by
          dsimp [zL]; ring
        linarith
      have hR : (G.f i₀).eval zR < (G.f j₀).eval zR := by
        rw [hbiR, hbjR]
        have h_id : (dualPt G.f (j₀, bj)).1 * zR + (dualPt G.f (j₀, bj)).2 -
            ((dualPt G.f (i₀, bi)).1 * zR + (dualPt G.f (i₀, bi)).2) =
            ((dualPt G.f (j₀, bj)).1 * ξ r + (dualPt G.f (j₀, bj)).2 -
              ((dualPt G.f (i₀, bi)).1 * ξ r + (dualPt G.f (i₀, bi)).2)) +
            ((dualPt G.f (j₀, bj)).1 - (dualPt G.f (i₀, bi)).1) * δ_loc := by
          dsimp [zR]; ring
        linarith
      exact ⟨htL'.mpr hL, htR.mp hR⟩
    · left
      have hdiff_pos : 0 < ((dualPt G.f (i₀, bi)).1 - (dualPt G.f (j₀, bj)).1) * δ_loc :=
        mul_pos (sub_pos.mpr h_sl) hδ_loc
      have hL : (G.f i₀).eval zL < (G.f j₀).eval zL := by
        rw [hbiL, hbjL]
        have h_id : (dualPt G.f (j₀, bj)).1 * zL + (dualPt G.f (j₀, bj)).2 -
            ((dualPt G.f (i₀, bi)).1 * zL + (dualPt G.f (i₀, bi)).2) =
            ((dualPt G.f (j₀, bj)).1 * ξ r + (dualPt G.f (j₀, bj)).2 -
              ((dualPt G.f (i₀, bi)).1 * ξ r + (dualPt G.f (i₀, bi)).2)) +
            ((dualPt G.f (i₀, bi)).1 - (dualPt G.f (j₀, bj)).1) * δ_loc := by
          dsimp [zL]; ring
        linarith
      have hR : (G.f j₀).eval zR < (G.f i₀).eval zR := by
        rw [hbiR, hbjR]
        have h_id : (dualPt G.f (i₀, bi)).1 * zR + (dualPt G.f (i₀, bi)).2 -
            ((dualPt G.f (j₀, bj)).1 * zR + (dualPt G.f (j₀, bj)).2) =
            ((dualPt G.f (i₀, bi)).1 * ξ r + (dualPt G.f (i₀, bi)).2 -
              ((dualPt G.f (j₀, bj)).1 * ξ r + (dualPt G.f (j₀, bj)).2)) +
            ((dualPt G.f (i₀, bi)).1 - (dualPt G.f (j₀, bj)).1) * δ_loc := by
          dsimp [zR]; ring
        linarith
      exact ⟨htL.mpr hL, htR'.mp hR⟩
  have h_rk_eq : ∀ q : ℕ, q ≤ 5 →
      (Finset.univ.filter (fun k : Fin 5 => (G.f k).eval (ξ r) < v₀)).card + 1 ≠ q →
      sweepSSeq G q ⟨r.val, by omega⟩ = sweepSSeq G q ⟨r.val + 1, by omega⟩ := by
    intro q hq hne_rk
    let rk_set := Finset.univ.filter (fun k : Fin 5 => (G.f k).eval (ξ r) < v₀)
    have hi_not_rk : i₀ ∉ rk_set := by simp [rk_set, v₀]
    have hj_not_rk : j₀ ∉ rk_set := by
      simp only [rk_set, Finset.mem_filter, Finset.mem_univ, true_and]
      dsimp [v₀, ξ]; rw [heq]; exact lt_irrefl _
    have hrk_le : rk_set.card ≤ 3 := by
      have hsub : rk_set ⊆ (Finset.univ.erase i₀).erase j₀ := by
        intro k hk
        refine Finset.mem_erase.mpr ⟨fun h => by rw [h] at hk; exact hj_not_rk hk,
          Finset.mem_erase.mpr ⟨fun h => by rw [h] at hk; exact hi_not_rk hk, Finset.mem_univ _⟩⟩
      have hc := Finset.card_le_card hsub
      rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨ne_of_gt hij, Finset.mem_univ _⟩),
          Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_fin] at hc
      exact hc
    have h_set_eq_outside : ∀ k : Fin 5, k ≠ i₀ → k ≠ j₀ →
        Finset.univ.filter (fun m : Fin 5 => (G.f m).eval (τ ⟨r.val, by omega⟩) < (G.f k).eval (τ ⟨r.val, by omega⟩)) =
        Finset.univ.filter (fun m : Fin 5 => (G.f m).eval (τ ⟨r.val + 1, by omega⟩) < (G.f k).eval (τ ⟨r.val + 1, by omega⟩)) := by
      intro k hki hkj
      apply Finset.ext; intro m
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      by_cases hmk : m = k
      · subst m; simp
      · by_cases hmi : m = i₀
        · subst m
          rcases lt_or_gt_of_ne (h_other_ne k hki hkj) with h1 | h2
          · have ha := (h_keep_sign k ⟨r.val, by omega⟩ (Or.inl rfl) hki hkj).1 h1
            have hb := (h_keep_sign k ⟨r.val + 1, by omega⟩ (Or.inr rfl) hki hkj).1 h1
            constructor <;> intro h <;> linarith
          · have ha := (h_keep_sign k ⟨r.val, by omega⟩ (Or.inl rfl) hki hkj).2 h2
            have hb := (h_keep_sign k ⟨r.val + 1, by omega⟩ (Or.inr rfl) hki hkj).2 h2
            constructor <;> intro h <;> linarith
        · by_cases hmj : m = j₀
          · subst m
            rcases lt_or_gt_of_ne (h_other_ne k hki hkj) with h1 | h2
            · have ha := (h_keep_sign k ⟨r.val, by omega⟩ (Or.inl rfl) hki hkj).1 h1
              have hb := (h_keep_sign k ⟨r.val + 1, by omega⟩ (Or.inr rfl) hki hkj).1 h1
              constructor <;> intro h <;> linarith
            · have ha := (h_keep_sign k ⟨r.val, by omega⟩ (Or.inl rfl) hki hkj).2 h2
              have hb := (h_keep_sign k ⟨r.val + 1, by omega⟩ (Or.inr rfl) hki hkj).2 h2
              constructor <;> intro h <;> linarith
          · have hne_mk : (G.f m).eval (ξ r) ≠ (G.f k).eval (ξ r) := by
              intro heq_mk
              rcases lt_or_gt_of_ne hmk with h1 | h2
              · have := hunique m k h1 heq_mk; exact hmi (congrArg Prod.fst this)
              · have := hunique k m h2 heq_mk.symm; exact hki (congrArg Prod.fst this)
            have hno_mk : ∀ z ∈ Set.Icc (τ ⟨r.val, by omega⟩) (τ ⟨r.val + 1, by omega⟩),
                (G.f m).eval z ≠ (G.f k).eval z := by
              intro z hz heqz
              have hzX : z ∈ X_cross G.f := by
                rcases lt_or_gt_of_ne hmk with h1 | h2
                · exact Finset.mem_biUnion.mpr ⟨(m, k), Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1⟩, (mem_Z_set G h1 z).mpr heqz⟩
                · exact Finset.mem_biUnion.mpr ⟨(k, m), Finset.mem_filter.mpr ⟨Finset.mem_univ _, h2⟩, (mem_Z_set G h2 z).mpr heqz.symm⟩
              have hrange : z ∈ Set.range ξ := by simpa [ξ, sweepXi, Finset.range_orderEmbOfFin] using hzX
              rcases hrange with ⟨k', rfl⟩
              by_cases hk'r : k' = r
              · subst hk'r; exact hne_mk heqz
              · rcases lt_or_gt_of_ne hk'r with hlt | hgt
                · have h1' : ξ k' < τ ⟨k'.val + 1, by omega⟩ := xi_lt_sweepTau G k'
                  have h2' : τ ⟨k'.val + 1, by omega⟩ ≤ τ ⟨r.val, by omega⟩ :=
                    (sweepTau_strictMono G).monotone (by change k'.val + 1 ≤ r.val; exact hlt)
                  linarith [hz.1]
                · have h1' : τ ⟨k'.val, by omega⟩ < ξ k' := sweepTau_lt_xi G k'
                  have h2' : τ ⟨r.val + 1, by omega⟩ ≤ τ ⟨k'.val, by omega⟩ :=
                    (sweepTau_strictMono G).monotone (by change r.val + 1 ≤ k'.val; exact hgt)
                  linarith [hz.2]
            let diff (z : ℝ) := (G.f m).eval z - (G.f k).eval z
            have hcont : Continuous diff := (continuous_eval_vfunc (G.f m)).sub (continuous_eval_vfunc (G.f k))
            have h12 : τ ⟨r.val, by omega⟩ ≤ τ ⟨r.val + 1, by omega⟩ :=
              le_of_lt (lt_trans (sweepTau_lt_xi G r) (xi_lt_sweepTau G r))
            constructor <;> intro hlt
            · by_contra hnot
              have hle := not_lt.mp hnot
              have h0 : (0 : ℝ) ∈ Set.Icc (diff (τ ⟨r.val, by omega⟩)) (diff (τ ⟨r.val + 1, by omega⟩)) :=
                ⟨by dsimp [diff]; linarith, by dsimp [diff]; linarith⟩
              obtain ⟨z, hz, hzero⟩ := intermediate_value_Icc h12 hcont.continuousOn h0
              exact hno_mk z hz (sub_eq_zero.mp hzero)
            · by_contra hnot
              have hle := not_lt.mp hnot
              have h0 : (0 : ℝ) ∈ Set.Icc (diff (τ ⟨r.val + 1, by omega⟩)) (diff (τ ⟨r.val, by omega⟩)) :=
                ⟨by dsimp [diff]; linarith, by dsimp [diff]; linarith⟩
              obtain ⟨z, hz, hzero⟩ := intermediate_value_Icc' h12 hcont.continuousOn h0
              exact hno_mk z hz (sub_eq_zero.mp hzero)
    rcases lt_or_gt_of_ne hne_rk with h_gt | h_lt
    · change rk_set.card + 1 < q at h_gt
      have h_same_mem : ∀ k : Fin 5, k ∈ sweepSSeq G q ⟨r.val, by omega⟩ ↔ k ∈ sweepSSeq G q ⟨r.val + 1, by omega⟩ := by
        intro k
        by_cases hki : k = i₀
        · subst k
          have hcard_lt : ∀ (r' : Fin ((X_cross G.f).card + 1)), (r'.val = r.val ∨ r'.val = r.val + 1) →
              (Finset.univ.filter (fun m : Fin 5 => (G.f m).eval (τ r') < (G.f i₀).eval (τ r'))).card ≤ rk_set.card + 1 := by
            intro r' hr'
            have hsub : Finset.univ.filter (fun m : Fin 5 => (G.f m).eval (τ r') < (G.f i₀).eval (τ r')) ⊆ insert j₀ rk_set := by
              intro m hm
              have hm' := (Finset.mem_filter.mp hm).2
              by_cases hmj : m = j₀
              · subst m; exact Finset.mem_insert_self _ _
              · by_cases hmi : m = i₀
                · subst m; exact False.elim (lt_irrefl _ hm')
                · refine Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩)
                  rcases lt_or_gt_of_ne (h_other_ne m hmi hmj) with h1 | h2
                  · exact h1
                  · have := (h_keep_sign m r' hr' hmi hmj).2 h2
                    linarith
            calc (Finset.univ.filter (fun m : Fin 5 => (G.f m).eval (τ r') < (G.f i₀).eval (τ r'))).card
                ≤ (insert j₀ rk_set).card := Finset.card_le_card hsub
              _ ≤ rk_set.card + 1 := Finset.card_insert_le _ _
          simp only [sweepSSeq, bottomK, Finset.mem_filter, Finset.mem_univ, true_and]
          constructor <;> intro _
          · exact lt_of_le_of_lt (hcard_lt ⟨r.val + 1, by omega⟩ (Or.inr rfl)) (by omega)
          · exact lt_of_le_of_lt (hcard_lt ⟨r.val, by omega⟩ (Or.inl rfl)) (by omega)
        · by_cases hkj : k = j₀
          · subst k
            have hcard_lt : ∀ (r' : Fin ((X_cross G.f).card + 1)), (r'.val = r.val ∨ r'.val = r.val + 1) →
                (Finset.univ.filter (fun m : Fin 5 => (G.f m).eval (τ r') < (G.f j₀).eval (τ r'))).card ≤ rk_set.card + 1 := by
              intro r' hr'
              have hsub : Finset.univ.filter (fun m : Fin 5 => (G.f m).eval (τ r') < (G.f j₀).eval (τ r')) ⊆ insert i₀ rk_set := by
                intro m hm
                have hm' := (Finset.mem_filter.mp hm).2
                by_cases hmi : m = i₀
                · subst m; exact Finset.mem_insert_self _ _
                · by_cases hmj : m = j₀
                  · subst m; exact False.elim (lt_irrefl _ hm')
                  · refine Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩)
                    rcases lt_or_gt_of_ne (h_other_ne m hmi hmj) with h1 | h2
                    · exact h1
                    · have := (h_keep_sign m r' hr' hmi hmj).2 h2
                      linarith
              calc (Finset.univ.filter (fun m : Fin 5 => (G.f m).eval (τ r') < (G.f j₀).eval (τ r'))).card
                  ≤ (insert i₀ rk_set).card := Finset.card_le_card hsub
                _ ≤ rk_set.card + 1 := Finset.card_insert_le _ _
            simp only [sweepSSeq, bottomK, Finset.mem_filter, Finset.mem_univ, true_and]
            constructor <;> intro _
            · exact lt_of_le_of_lt (hcard_lt ⟨r.val + 1, by omega⟩ (Or.inr rfl)) (by omega)
            · exact lt_of_le_of_lt (hcard_lt ⟨r.val, by omega⟩ (Or.inl rfl)) (by omega)
          · simp only [sweepSSeq, bottomK, Finset.mem_filter, Finset.mem_univ, true_and]
            dsimp [τ] at h_set_eq_outside
            rw [h_set_eq_outside k hki hkj]
      exact Finset.ext h_same_mem
    · change q < rk_set.card + 1 at h_lt
      have h_same_mem : ∀ k : Fin 5, k ∈ sweepSSeq G q ⟨r.val, by omega⟩ ↔ k ∈ sweepSSeq G q ⟨r.val + 1, by omega⟩ := by
        intro k
        by_cases hki : k = i₀
        · subst k
          have hcard_ge : ∀ (r' : Fin ((X_cross G.f).card + 1)), (r'.val = r.val ∨ r'.val = r.val + 1) →
              rk_set.card ≤ (Finset.univ.filter (fun m : Fin 5 => (G.f m).eval (τ r') < (G.f i₀).eval (τ r'))).card := by
            intro r' hr'
            refine Finset.card_le_card (fun m hm => ?_)
            have hm' := (Finset.mem_filter.mp hm).2
            have hmi : m ≠ i₀ := fun h => by rw [h] at hm; exact hi_not_rk hm
            have hmj : m ≠ j₀ := fun h => by rw [h] at hm; exact hj_not_rk hm
            exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (h_keep_sign m r' hr' hmi hmj).1 hm' |>.1⟩
          simp only [sweepSSeq, bottomK, Finset.mem_filter, Finset.mem_univ, true_and]
          constructor <;> intro hlt
          · exfalso; exact absurd (lt_of_le_of_lt (hcard_ge ⟨r.val, by omega⟩ (Or.inl rfl)) hlt) (by omega)
          · exfalso; exact absurd (lt_of_le_of_lt (hcard_ge ⟨r.val + 1, by omega⟩ (Or.inr rfl)) hlt) (by omega)
        · by_cases hkj : k = j₀
          · subst k
            have hcard_ge : ∀ (r' : Fin ((X_cross G.f).card + 1)), (r'.val = r.val ∨ r'.val = r.val + 1) →
                rk_set.card ≤ (Finset.univ.filter (fun m : Fin 5 => (G.f m).eval (τ r') < (G.f j₀).eval (τ r'))).card := by
              intro r' hr'
              refine Finset.card_le_card (fun m hm => ?_)
              have hm' := (Finset.mem_filter.mp hm).2
              have hmi : m ≠ i₀ := fun h => by rw [h] at hm; exact hi_not_rk hm
              have hmj : m ≠ j₀ := fun h => by rw [h] at hm; exact hj_not_rk hm
              exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (h_keep_sign m r' hr' hmi hmj).1 hm' |>.2⟩
            simp only [sweepSSeq, bottomK, Finset.mem_filter, Finset.mem_univ, true_and]
            constructor <;> intro hlt
            · exfalso; exact absurd (lt_of_le_of_lt (hcard_ge ⟨r.val, by omega⟩ (Or.inl rfl)) hlt) (by omega)
            · exfalso; exact absurd (lt_of_le_of_lt (hcard_ge ⟨r.val + 1, by omega⟩ (Or.inr rfl)) hlt) (by omega)
          · simp only [sweepSSeq, bottomK, Finset.mem_filter, Finset.mem_univ, true_and]
            dsimp [τ] at h_set_eq_outside
            rw [h_set_eq_outside k hki hkj]
      exact Finset.ext h_same_mem
  let rk_top_set := Finset.univ.filter (fun k : Fin 5 => (G.f k).eval (ξ r) < v₀)
  have hrk_top_le : rk_top_set.card ≤ 3 := by
    have hsub : rk_top_set ⊆ (Finset.univ.erase i₀).erase j₀ := by
      intro k hk; have hk' := (Finset.mem_filter.mp hk).2
      refine Finset.mem_erase.mpr ⟨fun h => by rw [h] at hk'; dsimp [v₀, ξ] at hk'; rw [heq] at hk'; exact lt_irrefl _ hk',
        Finset.mem_erase.mpr ⟨fun h => by rw [h] at hk'; exact lt_irrefl _ hk', Finset.mem_univ _⟩⟩
    have hc := Finset.card_le_card hsub
    rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨ne_of_gt hij, Finset.mem_univ _⟩),
        Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_fin] at hc
    exact hc
  let q₀ : ℕ := rk_top_set.card + 1
  refine ⟨q₀, by omega, by omega, fun q hq hne => h_rk_eq q hq hne.symm, ?_, ?_⟩
  · have h_below_pair : ∀ (r' : Fin ((X_cross G.f).card + 1)) (hr' : r'.val = r.val ∨ r'.val = r.val + 1)
        (a b : Fin 5), (a = i₀ ∧ b = j₀ ∨ a = j₀ ∧ b = i₀) →
        (G.f a).eval (τ r') < (G.f b).eval (τ r') →
        (a ∈ sweepSSeq G q₀ r' ∧ b ∉ sweepSSeq G q₀ r') := by
      intro r' hr' a b hab hlt
      have hsub_a : Finset.univ.filter (fun m : Fin 5 => (G.f m).eval (τ r') < (G.f a).eval (τ r')) ⊆ rk_top_set := by
        intro m hm; have hm' := (Finset.mem_filter.mp hm).2
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
        by_cases hma : m = a
        · subst m; exact False.elim (lt_irrefl _ hm')
        · by_cases hmb : m = b
          · subst m; exact False.elim (lt_asymm hlt hm')
          · have hmi : m ≠ i₀ := fun h => by rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> contradiction
            have hmj : m ≠ j₀ := fun h => by rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> contradiction
            rcases lt_or_gt_of_ne (h_other_ne m hmi hmj) with h1 | h2
            · exact h1
            · have hs := (h_keep_sign m r' hr' hmi hmj).2 h2
              rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
              · linarith [hs.1]
              · linarith [hs.2]
      have hc_a : (Finset.univ.filter (fun m : Fin 5 => (G.f m).eval (τ r') < (G.f a).eval (τ r'))).card < q₀ := by
        have := Finset.card_le_card hsub_a
        dsimp [q₀]; omega
      have hsub_b : insert a rk_top_set ⊆ Finset.univ.filter (fun m : Fin 5 => (G.f m).eval (τ r') < (G.f b).eval (τ r')) := by
        intro m hm
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
        rcases Finset.mem_insert.mp hm with hma | hm_rk
        · rw [hma]; exact hlt
        · have hm' := (Finset.mem_filter.mp hm_rk).2
          have hmi : m ≠ i₀ := fun h => by rw [h] at hm'; exact lt_irrefl _ hm'
          have hmj : m ≠ j₀ := fun h => by rw [h] at hm'; dsimp [v₀, ξ] at hm'; rw [heq] at hm'; exact lt_irrefl _ hm'
          have hs := (h_keep_sign m r' hr' hmi hmj).1 hm'
          rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact hs.2
          · exact hs.1
      have ha_not_rk : a ∉ rk_top_set := by
        simp only [rk_top_set, Finset.mem_filter, Finset.mem_univ, true_and]
        dsimp [v₀, ξ]
        rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact lt_irrefl _
        · rw [heq]; exact lt_irrefl _
      have hc_b : q₀ ≤ (Finset.univ.filter (fun m : Fin 5 => (G.f m).eval (τ r') < (G.f b).eval (τ r'))).card := by
        have := Finset.card_le_card hsub_b
        rw [Finset.card_insert_of_notMem ha_not_rk] at this
        dsimp [q₀]; exact this
      exact ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc_a⟩,
             fun hb => absurd (Finset.mem_filter.mp hb).2 (not_lt.mpr hc_b)⟩
    intro heq_s
    rcases hij_swap with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have hi1 := (h_below_pair _ (Or.inl rfl) i₀ j₀ (Or.inl ⟨rfl, rfl⟩) h1).1
      have hi2 := (h_below_pair _ (Or.inr rfl) j₀ i₀ (Or.inr ⟨rfl, rfl⟩) h2).2
      rw [heq_s] at hi1; exact hi2 hi1
    · have hj1 := (h_below_pair _ (Or.inl rfl) j₀ i₀ (Or.inr ⟨rfl, rfl⟩) h1).1
      have hj2 := (h_below_pair _ (Or.inr rfl) i₀ j₀ (Or.inl ⟨rfl, rfl⟩) h2).2
      rw [heq_s] at hj1; exact hj2 hj1
  · constructor
    · intro hq4
      have hrk3 : rk_top_set.card = 3 := by dsimp [q₀] at hq4; omega
      have hall_eq : rk_top_set = (Finset.univ.erase i₀).erase j₀ := by
        apply Finset.eq_of_subset_of_card_le
        · intro k hk; have hk' := (Finset.mem_filter.mp hk).2
          refine Finset.mem_erase.mpr ⟨fun h => by rw [h] at hk'; dsimp [v₀, ξ] at hk'; rw [heq] at hk'; exact lt_irrefl _ hk',
            Finset.mem_erase.mpr ⟨fun h => by rw [h] at hk'; exact lt_irrefl _ hk', Finset.mem_univ _⟩⟩
        · rw [hrk3, Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨ne_of_gt hij, Finset.mem_univ _⟩),
              Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_fin]
      have htop : v₀ = F_top G.f (ξ r) := by
        rw [F_top]
        refine le_antisymm (Finset.le_sup' (fun k => (G.f k).eval (ξ r)) (Finset.mem_univ i₀)) ?_
        rw [Finset.sup'_le_iff]; intro k _
        by_cases hki : k = i₀
        · subst k; exact le_rfl
        · by_cases hkj : k = j₀
          · subst k; exact le_of_eq heq.symm
          · have hk_mem : k ∈ (Finset.univ.erase i₀).erase j₀ :=
              Finset.mem_erase.mpr ⟨hkj, Finset.mem_erase.mpr ⟨hki, Finset.mem_univ _⟩⟩
            rw [← hall_eq] at hk_mem
            exact le_of_lt (Finset.mem_filter.mp hk_mem).2
      exact ⟨i₀, j₀, hij, heq, htop⟩
    · rintro ⟨i', j', hij', heq', htop⟩
      have heq_pair := hunique i' j' hij' heq'
      have hi' : i' = i₀ := congrArg Prod.fst heq_pair
      have hj' : j' = j₀ := congrArg Prod.snd heq_pair
      subst i'; subst j'
      have hsub : (Finset.univ.erase i₀).erase j₀ ⊆ rk_top_set := by
        intro k hk
        have hkj : k ≠ j₀ := (Finset.mem_erase.mp hk).1
        have hki : k ≠ i₀ := (Finset.mem_erase.mp (Finset.mem_erase.mp hk).2).1
        have hle : (G.f k).eval (ξ r) ≤ v₀ := by
          dsimp [v₀, ξ]; rw [htop, F_top]; exact Finset.le_sup' (fun m => (G.f m).eval (sweepXi G r)) (Finset.mem_univ k)
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, lt_of_le_of_ne hle (h_other_ne k hki hkj)⟩
      have hc := Finset.card_le_card hsub
      rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨ne_of_gt hij, Finset.mem_univ _⟩),
          Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_fin] at hc
      dsimp [q₀]; omega

private def B_masks (q : ℕ) : Finset (Finset (Fin 5)) :=
  Finset.univ.filter (fun M : Finset (Fin 5) => M.card = q)

private lemma B_masks_card_1 : (B_masks 1).card = 5 := by decide
private lemma B_masks_card_2 : (B_masks 2).card = 10 := by decide
private lemma B_masks_card_3 : (B_masks 3).card = 10 := by decide

private noncomputable def sweepDeltaQ (G : GenericVSystem) (q : ℕ) : ℕ :=
  ∑ M ∈ B_masks q, (seqRuns (sweepSSeq G q) M - 1)

private lemma sweepDeltaQ_le_self (G : GenericVSystem) (q : ℕ) (M : Finset (Fin 5))
    (hM : M.card = q) :
    seqRuns (sweepSSeq G q) M - 1 ≤ sweepDeltaQ G q := by
  dsimp [sweepDeltaQ]
  exact Finset.single_le_sum (f := fun x => seqRuns (sweepSSeq G q) x - 1)
    (fun _ _ => Nat.zero_le _) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hM⟩)

private lemma sweepDeltaQ_pair_le (G : GenericVSystem) (q : ℕ) (M₁ M₂ : Finset (Fin 5))
    (hne : M₁ ≠ M₂) (hM1 : M₁.card = q) (hM2 : M₂.card = q) :
    (seqRuns (sweepSSeq G q) M₁ - 1) + (seqRuns (sweepSSeq G q) M₂ - 1) ≤ sweepDeltaQ G q := by
  have hpair : ({M₁, M₂} : Finset (Finset (Fin 5))) ⊆ B_masks q := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hM1⟩
    · rw [Finset.mem_singleton.mp hx]
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hM2⟩
  dsimp [sweepDeltaQ]
  have hs := Finset.sum_le_sum_of_subset_of_nonneg hpair
    (f := fun x => seqRuns (sweepSSeq G q) x - 1) (fun _ _ _ => Nat.zero_le _)
  rwa [Finset.sum_pair hne] at hs

private lemma sweep_get_ge2 (G : GenericVSystem)
    (M : Finset (Fin 5)) (a b c : ℝ) (hMc : M.card = 1 ∨ M.card = 2)
    (hab : a < b) (hbc : b < c)
    (haX : a ∉ X_cross G.f) (hbX : b ∉ X_cross G.f) (hcX : c ∉ X_cross G.f)
    (hPa : Φ G.f M a) (hPb : ¬ Φ G.f M b) (hPc : Φ G.f M c) :
    2 ≤ seqRuns (sweepSSeq G M.card) M := by
  have hq : M.card ≤ 5 := by rcases hMc with h | h <;> omega
  obtain ⟨ra, hra_gt, hra_lt⟩ := locate_avoiding_X G a haX
  obtain ⟨rb, hrb_gt, hrb_lt⟩ := locate_avoiding_X G b hbX
  obtain ⟨rc, hrc_gt, hrc_lt⟩ := locate_avoiding_X G c hcX
  have hsSeq_eq_iff : ∀ (r : Fin ((X_cross G.f).card + 1)),
      sweepSSeq G M.card r = M ↔ M.card = M.card ∧ Φ G.f M (sweepTau G r) :=
    fun r => bottomK_eq_iff (distinct_eval_of_not_mem G (sweepTau G r) (sweepTau_not_mem G r)) M.card hq M
  have hrab : ra < rb := by
    by_contra hle; have hrba := not_lt.mp hle
    rcases eq_or_lt_of_le hrba with rfl | hlt
    · exact hPb (fun u hu v hv => (same_interval_lt_iff G b rb hrb_gt hrb_lt u v).mpr
        ((same_interval_lt_iff G a rb hra_gt hra_lt u v).mp (hPa u hu v hv)))
    · have hxa := hra_gt ⟨rb.val, by omega⟩ hlt
      have hxb := hrb_lt ⟨rb.val, by omega⟩ le_rfl
      linarith
  have hrbc : rb < rc := by
    by_contra hle; have hrcb := not_lt.mp hle
    rcases eq_or_lt_of_le hrcb with rfl | hlt
    · exact hPb (fun u hu v hv => (same_interval_lt_iff G b rc hrb_gt hrb_lt u v).mpr
        ((same_interval_lt_iff G c rc hrc_gt hrc_lt u v).mp (hPc u hu v hv)))
    · have hxa := hrb_gt ⟨rc.val, by omega⟩ hlt
      have hxb := hrc_lt ⟨rc.val, by omega⟩ le_rfl
      linarith
  exact seqRuns_ge_two (sweepSSeq G M.card) M hrab hrbc
    ((hsSeq_eq_iff ra).mpr ⟨rfl, fun u hu v hv => (same_interval_lt_iff G a ra hra_gt hra_lt u v).mp (hPa u hu v hv)⟩)
    (fun heq => hPb (fun u hu v hv => (same_interval_lt_iff G b rb hrb_gt hrb_lt u v).mpr
      (((hsSeq_eq_iff rb).mp heq).2 u hu v hv)))
    ((hsSeq_eq_iff rc).mpr ⟨rfl, fun u hu v hv => (same_interval_lt_iff G c rc hrc_gt hrc_lt u v).mp (hPc u hu v hv)⟩)

theorem build_sweepData (G : GenericVSystem) (H : HullData G.f) :
    Nonempty (SweepData G H) := by
  let K : ℕ := (X_cross G.f).card
  have hK_eq : K = 3 * T3 G + T1 G + 2 * (T3bar G - T1 G) := X_cross_card G
  have hT3bar_eq : T3bar G = 10 - T3 G := rfl
  have hT3_le : T3 G ≤ 10 := by
    calc T3 G ≤ pair5.card := Finset.card_filter_le _ _
      _ = 10 := pair5_card
  have hT1_le : T1 G ≤ T3bar G := T1_le_T3bar G
  have hK_pos : 0 < K := xCross_card_pos G
  let ξ : Fin K ↪o ℝ := sweepXi G
  let τ : Fin (K + 1) → ℝ := sweepTau G
  have hτ_not_X : ∀ r : Fin (K + 1), τ r ∉ X_cross G.f := sweepTau_not_mem G
  have h_locate := locate_avoiding_X G
  have h_same_interval := same_interval_lt_iff G
  have h_distinct_at := distinct_eval_of_not_mem G
  let sSeq : ℕ → Fin (K + 1) → Finset (Fin 5) := sweepSSeq G
  let B : ℕ → Finset (Finset (Fin 5)) := B_masks
  have hsSeq_mem : ∀ (q : ℕ) (hq : q ≤ 5) (r : Fin (K + 1)), sSeq q r ∈ B q := by
    intro q hq r
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, bottomK_card (h_distinct_at (τ r) (hτ_not_X r)) q hq⟩
  have hsSeq_eq_iff : ∀ (q : ℕ) (hq : q ≤ 5) (r : Fin (K + 1)) (M : Finset (Fin 5)),
      sSeq q r = M ↔ M.card = q ∧ Φ G.f M (τ r) :=
    fun q hq r M => bottomK_eq_iff (h_distinct_at (τ r) (hτ_not_X r)) q hq M
  have hsSeq_realized : ∀ (q : ℕ) (hq : q ≤ 5) (M : Finset (Fin 5)),
      M ∈ B q → ∃ r : Fin (K + 1), sSeq q r = M := by
    intro q hq M hM
    have hMcard : M.card = q := (Finset.mem_filter.mp hM).2
    obtain ⟨⟨x₀, y₀⟩, hm⟩ := G.realizes (maskOf M)
    let marg : Finset (Fin 5) := Finset.univ
    let δ : ℝ := marg.inf' ⟨0, Finset.mem_univ _⟩ (fun i => |y₀ - (G.f i).eval x₀|)
    have hδ_pos : 0 < δ := by
      rw [Finset.lt_inf'_iff]; intro i _
      have hi := hm i
      by_cases hiM : i ∈ M
      · simp only [maskOf, hiM, decide_true, ↓reduceIte] at hi
        exact abs_pos.mpr (by linarith)
      · simp only [maskOf, hiM, decide_false, Bool.false_eq_true, ↓reduceIte] at hi
        exact abs_pos.mpr (by linarith)
    let L : ℝ := 1 + marg.sup' ⟨0, Finset.mem_univ _⟩ (fun i => max |(G.f i).a| |(G.f i).c|)
    have hL_pos : 0 < L := by
      have h0 : 0 ≤ marg.sup' ⟨0, Finset.mem_univ _⟩ (fun i => max |(G.f i).a| |(G.f i).c|) :=
        le_trans (le_max_of_le_left (abs_nonneg (G.f 0).a))
          (Finset.le_sup' (fun i : Fin 5 => max |(G.f i).a| |(G.f i).c|) (Finset.mem_univ (0 : Fin 5)))
      dsimp [L]; linarith
    let ε : ℝ := δ / (2 * L)
    have hε_pos : 0 < ε := div_pos hδ_pos (by linarith)
    obtain ⟨x, hx_lo, hx_hi, hx_not⟩ := exists_mem_Ioo_avoiding (x₀ - ε) (x₀ + ε) (by linarith) (X_cross G.f)
    have hΦx : Φ G.f M x := by
      have hclose : ∀ i : Fin 5, |(G.f i).eval x - (G.f i).eval x₀| < δ / 2 := by
        intro i
        have hlip : |(G.f i).eval x - (G.f i).eval x₀| ≤ max |(G.f i).a| |(G.f i).c| * |x - x₀| := by
          unfold VFunc.eval
          refine (abs_max_sub_max_le_max _ _ _ _).trans ?_
          rw [max_le_iff]
          have e1 : (G.f i).a * x + (G.f i).b - ((G.f i).a * x₀ + (G.f i).b) = (G.f i).a * (x - x₀) := by ring
          have e2 : (G.f i).c * x + (G.f i).d - ((G.f i).c * x₀ + (G.f i).d) = (G.f i).c * (x - x₀) := by ring
          rw [e1, e2, abs_mul, abs_mul]
          exact ⟨mul_le_mul_of_nonneg_right (le_max_left _ _) (abs_nonneg _),
                 mul_le_mul_of_nonneg_right (le_max_right _ _) (abs_nonneg _)⟩
        have hmax_lt : max |(G.f i).a| |(G.f i).c| < L := by
          have := Finset.le_sup' (fun j : Fin 5 => max |(G.f j).a| |(G.f j).c|) (Finset.mem_univ i)
          dsimp [L]; linarith
        have hdx : |x - x₀| < ε := abs_lt.mpr ⟨by linarith, by linarith⟩
        calc |(G.f i).eval x - (G.f i).eval x₀|
            ≤ max |(G.f i).a| |(G.f i).c| * |x - x₀| := hlip
          _ ≤ L * |x - x₀| := mul_le_mul_of_nonneg_right (le_of_lt hmax_lt) (abs_nonneg _)
          _ < L * ε := mul_lt_mul_of_pos_left hdx hL_pos
          _ = δ / 2 := by dsimp [ε]; field_simp [ne_of_gt hL_pos]
      intro u hu v hv
      have hu_m := hm u; simp only [maskOf, hu, decide_true, ↓reduceIte] at hu_m
      have hv_m := hm v; simp only [maskOf, hv, decide_false, Bool.false_eq_true, ↓reduceIte] at hv_m
      have hdu : δ ≤ |y₀ - (G.f u).eval x₀| := Finset.inf'_le _ (Finset.mem_univ u)
      have hdv : δ ≤ |y₀ - (G.f v).eval x₀| := Finset.inf'_le _ (Finset.mem_univ v)
      have hcu := abs_lt.mp (hclose u)
      have hcv := abs_lt.mp (hclose v)
      have h1 : (G.f u).eval x < y₀ := by
        rw [abs_of_pos (by linarith)] at hdu; linarith
      have h2 : y₀ < (G.f v).eval x := by
        rw [abs_of_neg (by linarith)] at hdv; linarith
      linarith
    obtain ⟨r, hr_gt, hr_lt⟩ := h_locate x hx_not
    refine ⟨r, (hsSeq_eq_iff q hq r M).mpr ⟨hMcard, fun u hu v hv => ?_⟩⟩
    exact (h_same_interval x r hr_gt hr_lt u v).mp (hΦx u hu v hv)
  have h_unique_jump := sweep_unique_jump G
  -- Define jump counts `k q` for `q = 1, 2, 3, 4`
  let kJump (q : ℕ) : ℕ :=
    (Finset.univ.filter (fun r : Fin K => sSeq q ⟨r.val, by omega⟩ ≠ sSeq q ⟨r.val + 1, by omega⟩)).card
  have hkJump_sum : kJump 1 + kJump 2 + kJump 3 + kJump 4 = K := by
    have hsum : ∑ q ∈ ({1, 2, 3, 4} : Finset ℕ), kJump q =
        ∑ r : Fin K, ∑ q ∈ ({1, 2, 3, 4} : Finset ℕ),
          (if sSeq q ⟨r.val, by omega⟩ ≠ sSeq q ⟨r.val + 1, by omega⟩ then 1 else 0) := by
      simp only [kJump, Finset.card_filter]
      exact Finset.sum_comm
    have hrhs : ∀ r : Fin K, ∑ q ∈ ({1, 2, 3, 4} : Finset ℕ),
        (if sSeq q ⟨r.val, by omega⟩ ≠ sSeq q ⟨r.val + 1, by omega⟩ then 1 else 0) = 1 := by
      intro r
      obtain ⟨q₀, hq1, hq4, huniq, hjmp, _⟩ := h_unique_jump r
      have h_eq : ∑ q ∈ ({1, 2, 3, 4} : Finset ℕ),
          (if sSeq q ⟨r.val, by omega⟩ ≠ sSeq q ⟨r.val + 1, by omega⟩ then 1 else 0) =
          ∑ q ∈ ({1, 2, 3, 4} : Finset ℕ), (if q₀ = q then 1 else 0) := by
        refine Finset.sum_congr rfl (fun q hqm => ?_)
        have hq5 : q ≤ 5 := by
          simp only [Finset.mem_insert, Finset.mem_singleton] at hqm
          rcases hqm with rfl | rfl | rfl | rfl <;> omega
        by_cases hqq : q₀ = q
        · subst hqq; dsimp [sSeq]; rw [if_pos hjmp]; simp
        · have := huniq q hq5 (Ne.symm hqq)
          dsimp [sSeq]; rw [if_neg (not_not.mpr this), if_neg hqq]
      rw [h_eq, Finset.sum_ite_eq]
      have hqmem : q₀ ∈ ({1, 2, 3, 4} : Finset ℕ) := by
        simp only [Finset.mem_insert, Finset.mem_singleton]; omega
      simp [hqmem]
    rw [Finset.sum_congr rfl (fun r _ => hrhs r)] at hsum
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one] at hsum
    have h4 : ∑ q ∈ ({1, 2, 3, 4} : Finset ℕ), kJump q = kJump 1 + kJump 2 + kJump 3 + kJump 4 := by
      simp [Finset.sum_insert, Finset.sum_singleton]; ring
    linarith
  -- Compute `kJump 4 = H.n - 1` via `T4.image ξ = B_set.image (fun b => -H.μ b)`
  have hk4_eq : kJump 4 = H.n - 1 := by
    let T4 := Finset.univ.filter (fun r : Fin K =>
      ∃ i j : Fin 5, i < j ∧ (G.f i).eval (ξ r) = (G.f j).eval (ξ r) ∧
        (G.f i).eval (ξ r) = F_top G.f (ξ r))
    have hT4_eq : Finset.univ.filter (fun r : Fin K =>
        sSeq 4 ⟨r.val, by omega⟩ ≠ sSeq 4 ⟨r.val + 1, by omega⟩) = T4 := by
      apply Finset.ext; intro r
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, T4]
      obtain ⟨q₀, hq1, hq4, huniq, hjmp, htop_iff⟩ := h_unique_jump r
      rw [← htop_iff]
      constructor
      · intro hne; by_contra hqne; exact hne (huniq 4 (by omega) (Ne.symm hqne))
      · intro h4; rwa [← h4]
    let B_set := Finset.univ.filter (fun b : Fin (H.h - 1) =>
      (H.q ⟨b.val, by have := H.hh_ge; omega⟩).1 ≠
      (H.q ⟨b.val + 1, by have := H.hh_ge; omega⟩).1)
    have himg : T4.image ξ = B_set.image (fun b => -H.μ b) := by
      apply Finset.ext; intro x; simp only [Finset.mem_image]
      constructor
      · rintro ⟨r, htop, rfl⟩
        have htop' := (Finset.mem_filter.mp htop).2
        obtain ⟨b, hb_col, hxb⟩ := (top_crossings_eq_block_boundaries H (ξ r)).mp htop'
        exact ⟨b, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb_col⟩, hxb.symm⟩
      · rintro ⟨b, hb_mem, rfl⟩
        have hb_col := (Finset.mem_filter.mp hb_mem).2
        obtain ⟨i, j, hij, heq, htop⟩ := (top_crossings_eq_block_boundaries H (-H.μ b)).mpr ⟨b, hb_col, rfl⟩
        have hx_X : -H.μ b ∈ X_cross G.f :=
          Finset.mem_biUnion.mpr ⟨(i, j), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hij⟩,
            (mem_Z_set G hij (-H.μ b)).mpr heq⟩
        have hrange : -H.μ b ∈ Set.range ξ := by simpa [ξ, sweepXi, Finset.range_orderEmbOfFin] using hx_X
        rcases hrange with ⟨r, hr⟩
        refine ⟨r, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, hr⟩
        rw [hr]; exact ⟨i, j, hij, heq, htop⟩
    have hμ_neg_inj : Function.Injective (fun b : Fin (H.h - 1) => -H.μ b) :=
      fun b₁ b₂ h => H.hμ_anti.injective (neg_inj.mp h)
    have hcard_eq : T4.card = B_set.card := by
      rw [← Finset.card_image_of_injective T4 ξ.injective, himg,
          Finset.card_image_of_injective B_set hμ_neg_inj]
    have hn_eq : H.n = 1 + B_set.card := rfl
    dsimp [kJump]; rw [hT4_eq, hcard_eq]; omega
  -- Define excess cell counts `Δq q` for `q = 1, 2, 3`
  let Δq : ℕ → ℕ := sweepDeltaQ G
  have hΔq_id : ∀ q : ℕ, 1 ≤ q → q ≤ 3 → (B q).card + Δq q = 1 + kJump q := by
    intro q hq1 hq3
    have hrun_ge : ∀ M ∈ B q, 1 ≤ seqRuns (sSeq q) M := fun M hM =>
      seqRuns_ge_one (sSeq q) M (hsSeq_realized q (by omega) M hM)
    have hadd : (B q).card + Δq q = ∑ M ∈ B q, seqRuns (sSeq q) M := by
      dsimp [Δq, sweepDeltaQ, B, sSeq]
      rw [Finset.card_eq_sum_ones, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun M hM => ?_)
      have hge := hrun_ge M hM
      dsimp [sSeq] at hge
      omega
    rw [hadd, sum_seqRuns_eq (sSeq q) (B q) (hsSeq_mem q (by omega))]
  have hB1 : (B 1).card = 5 := B_masks_card_1
  have hB2 : (B 2).card = 10 := B_masks_card_2
  have hB3 : (B 3).card = 10 := B_masks_card_3
  have h1 := hΔq_id 1 (by omega) (by omega)
  have h2 := hΔq_id 2 (by omega) (by omega)
  have h3 := hΔq_id 3 (by omega) (by omega)
  have hn_pos : 1 ≤ H.n := by dsimp [HullData.n]; omega
  have h_cons_int : (H.n : ℤ) + (T3bar G : ℤ) + (T1 G : ℤ) + (Δq 1 : ℤ) + (Δq 2 : ℤ) + (Δq 3 : ℤ) = 9 := by
    omega
  refine ⟨⟨Δq 1, Δq 2, Δq 3, h_cons_int, ?_, ?_⟩⟩
  · intro M τ₁ τ₂ τ₃ hMcard h12 h23 hτ1X hτ2X hτ3X hΦ1 hΦ2 hΦ3
    have hruns2 : 2 ≤ seqRuns (sweepSSeq G M.card) M :=
      sweep_get_ge2 G M τ₁ τ₂ τ₃ hMcard h12 h23 hτ1X hτ2X hτ3X hΦ1 hΦ2 hΦ3
    have hle_sum : seqRuns (sweepSSeq G M.card) M - 1 ≤ sweepDeltaQ G M.card :=
      sweepDeltaQ_le_self G M.card M rfl
    rcases hMcard with hc1 | hc2
    · rw [hc1] at hruns2 hle_sum ⊢; simp only [↓reduceIte]; dsimp [Δq]; omega
    · rw [hc2] at hruns2 hle_sum ⊢; simp only [show (2 : ℕ) ≠ 1 by omega, ↓reduceIte]; dsimp [Δq]; omega
  · intro M₁ M₂ τ₁ τ₂ τ₃ τ₁' τ₂' τ₃' hM1 hM2 hne h12 h23 hτ1X hτ2X hτ3X hΦ1 hΦ2 hΦ3
      h12' h23' hτ1'X hτ2'X hτ3'X hΦ1' hΦ2' hΦ3'
    have hr1 := sweep_get_ge2 G M₁ τ₁ τ₂ τ₃ hM1 h12 h23 hτ1X hτ2X hτ3X hΦ1 hΦ2 hΦ3
    have hr2 := sweep_get_ge2 G M₂ τ₁' τ₂' τ₃' hM2 h12' h23' hτ1'X hτ2'X hτ3'X hΦ1' hΦ2' hΦ3'
    rcases hM1 with hc1 | hc1 <;> rcases hM2 with hc2 | hc2
    · rw [hc1] at hr1; rw [hc2] at hr2
      have hs := sweepDeltaQ_pair_le G 1 M₁ M₂ hne hc1 hc2
      dsimp [Δq]; omega
    · rw [hc1] at hr1; rw [hc2] at hr2
      have hs1 := sweepDeltaQ_le_self G 1 M₁ hc1
      have hs2 := sweepDeltaQ_le_self G 2 M₂ hc2
      dsimp [Δq]; omega
    · rw [hc1] at hr1; rw [hc2] at hr2
      have hs1 := sweepDeltaQ_le_self G 2 M₁ hc1
      have hs2 := sweepDeltaQ_le_self G 1 M₂ hc2
      dsimp [Δq]; omega
    · rw [hc1] at hr1; rw [hc2] at hr2
      have hs := sweepDeltaQ_pair_le G 2 M₁ M₂ hne hc1 hc2
      dsimp [Δq]; omega

end Sec9

end
