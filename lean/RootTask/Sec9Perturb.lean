import Mathlib
import RootTask.Defs

open scoped Classical BigOperators
open Finset

noncomputable section

namespace Sec9

/-- A point in the projective dual plane indexed by `(i, b) : Fin 5 × Bool`,
    where `false` corresponds to `(a_i, b_i)` and `true` to `(c_i, d_i)`. -/
def dualPt (f : Fin 5 → VFunc) (k : Fin 5 × Bool) : ℝ × ℝ :=
  if k.2 then ((f k.1).c, (f k.1).d) else ((f k.1).a, (f k.1).b)

@[simp] lemma dualPt_false (f : Fin 5 → VFunc) (i : Fin 5) :
    dualPt f (i, false) = ((f i).a, (f i).b) := rfl

@[simp] lemma dualPt_true (f : Fin 5 → VFunc) (i : Fin 5) :
    dualPt f (i, true) = ((f i).c, (f i).d) := rfl

/-- The kink abscissa `x_i^* = (b_i - d_i) / (c_i - a_i)` of `f i`. -/
def kink (f : Fin 5 → VFunc) (i : Fin 5) : ℝ :=
  ((f i).b - (f i).d) / ((f i).c - (f i).a)

lemma kink_eq (f : Fin 5 → VFunc) (i : Fin 5) (h : (f i).a < (f i).c) :
    (f i).a * kink f i + (f i).b = (f i).c * kink f i + (f i).d := by
  have hne : (f i).c - (f i).a ≠ 0 := sub_ne_zero.mpr (ne_of_gt h)
  unfold kink
  field_simp [hne]
  ring

lemma eval_kink (f : Fin 5 → VFunc) (i : Fin 5) (h : (f i).a < (f i).c) :
    (f i).eval (kink f i) = (f i).a * kink f i + (f i).b := by
  unfold VFunc.eval
  rw [← kink_eq f i h, max_self]

/-- Dual realization of a subset `S ⊆ Fin 5` by a line `v = s * u + t` disjoint from all 10 dual points. -/
def DualRealizes (f : Fin 5 → VFunc) (S : Finset (Fin 5)) (s t : ℝ) : Prop :=
  (∀ k : Fin 5 × Bool, (dualPt f k).2 ≠ s * (dualPt f k).1 + t) ∧
  (∀ i : Fin 5, i ∈ S ↔ ∃ b : Bool, s * (dualPt f (i, b)).1 + t < (dualPt f (i, b)).2)

lemma dualRealizes_iff_realizesVMask (f : Fin 5 → VFunc) (S : Finset (Fin 5)) (x y : ℝ)
    (hdisj : ∀ k : Fin 5 × Bool, (dualPt f k).2 ≠ (-x) * (dualPt f k).1 + y) :
    DualRealizes f S (-x) y ↔ RealizesVMask f (fun i => decide (i ∉ S)) (x, y) := by
  constructor
  · intro ⟨_, hS⟩ i
    by_cases hi : i ∈ S
    · simp only [hi, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte]
      obtain ⟨b, hb⟩ := (hS i).mp hi
      unfold VFunc.eval
      rw [lt_max_iff]
      cases b
      · left; simp only [dualPt_false] at hb; linarith
      · right; simp only [dualPt_true] at hb; linarith
    · simp only [hi, not_false_eq_true, decide_true, ↓reduceIte]
      have hnot : ¬ ∃ b : Bool, (-x) * (dualPt f (i, b)).1 + y < (dualPt f (i, b)).2 :=
        fun hex => hi ((hS i).mpr hex)
      have h0 : (dualPt f (i, false)).2 < (-x) * (dualPt f (i, false)).1 + y := by
        have hle : (dualPt f (i, false)).2 ≤ (-x) * (dualPt f (i, false)).1 + y :=
          not_lt.mp (fun h => hnot ⟨false, h⟩)
        exact lt_of_le_of_ne hle (hdisj (i, false))
      have h1 : (dualPt f (i, true)).2 < (-x) * (dualPt f (i, true)).1 + y := by
        have hle : (dualPt f (i, true)).2 ≤ (-x) * (dualPt f (i, true)).1 + y :=
          not_lt.mp (fun h => hnot ⟨true, h⟩)
        exact lt_of_le_of_ne hle (hdisj (i, true))
      simp only [dualPt_false] at h0
      simp only [dualPt_true] at h1
      unfold VFunc.eval
      rw [max_lt_iff]
      exact ⟨by linarith, by linarith⟩
  · intro hm
    refine ⟨hdisj, fun i => ?_⟩
    have hmi := hm i
    by_cases hi : i ∈ S
    · simp only [hi, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte] at hmi
      refine ⟨fun _ => ?_, fun _ => hi⟩
      unfold VFunc.eval at hmi
      rw [lt_max_iff] at hmi
      rcases hmi with h | h
      · exact ⟨false, by simp only [dualPt_false]; linarith⟩
      · exact ⟨true, by simp only [dualPt_true]; linarith⟩
    · simp only [hi, not_false_eq_true, decide_true, ↓reduceIte] at hmi
      refine ⟨fun h => False.elim (hi h), ?_⟩
      rintro ⟨b, hb⟩
      unfold VFunc.eval at hmi
      rw [max_lt_iff] at hmi
      cases b
      · simp only [dualPt_false] at hb; linarith
      · simp only [dualPt_true] at hb; linarith

/-- Elementary witness in `(l, r)` avoiding a finite set `S` (no `Set.Infinite` needed). -/
lemma exists_mem_Ioo_avoiding (l r : ℝ) (hlr : l < r) (S : Finset ℝ) :
    ∃ x : ℝ, l < x ∧ x < r ∧ x ∉ S := by
  let S' := S.filter (fun x => l < x ∧ x < r)
  by_cases hne : S'.Nonempty
  · let m := S'.min' hne
    have hm_mem : m ∈ S' := Finset.min'_mem S' hne
    have hm_bounds := (Finset.mem_filter.mp hm_mem).2
    refine ⟨(l + m) / 2, by linarith, by linarith, fun hx => ?_⟩
    have hx' : (l + m) / 2 ∈ S' := Finset.mem_filter.mpr ⟨hx, by linarith, by linarith⟩
    have hle : m ≤ (l + m) / 2 := Finset.min'_le S' _ hx'
    linarith
  · rw [Finset.not_nonempty_iff_eq_empty] at hne
    refine ⟨(l + r) / 2, by linarith, by linarith, fun hx => ?_⟩
    have hx' : (l + r) / 2 ∈ S' := Finset.mem_filter.mpr ⟨hx, by linarith, by linarith⟩
    rw [hne] at hx'
    exact Finset.notMem_empty _ hx'

/-- From `leaf81_v_slope_perturb_preserve.proved.lean`, adapted cleanly without `valid`. -/
lemma slope_perturb_preserve
    (a b c d a' c' xm ym δ X0 : ℝ)
    (hδ : 0 < δ) (hX0 : 1 ≤ X0)
    (hxm : |xm| ≤ X0 - 1)
    (hmarg : δ ≤ |ym - max (a * xm + b) (c * xm + d)|)
    (ha : |a' - a| < δ / (2 * X0))
    (hc : |c' - c| < δ / (2 * X0)) :
    |max (a' * xm + b) (c' * xm + d) - max (a * xm + b) (c * xm + d)| < δ / 2 ∧
    (max (a * xm + b) (c * xm + d) < ym ↔ max (a' * xm + b) (c' * xm + d) < ym) ∧
    (ym < max (a * xm + b) (c * xm + d) ↔ ym < max (a' * xm + b) (c' * xm + d)) := by
  have hX0_pos : 0 < X0 := by linarith
  have hdiff_lt : |max (a' * xm + b) (c' * xm + d) - max (a * xm + b) (c * xm + d)| < δ / 2 := by
    refine (abs_max_sub_max_le_max _ _ _ _).trans_lt ?_
    rw [max_lt_iff]
    have hxm_lt : |xm| < X0 := by linarith
    have h1 : |(a' * xm + b) - (a * xm + b)| < δ / 2 := by
      have eq1 : (a' * xm + b) - (a * xm + b) = (a' - a) * xm := by ring
      rw [eq1, abs_mul]
      calc |a' - a| * |xm|
          ≤ |a' - a| * X0 := mul_le_mul_of_nonneg_left (le_of_lt hxm_lt) (abs_nonneg _)
        _ < (δ / (2 * X0)) * X0 := mul_lt_mul_of_pos_right ha hX0_pos
        _ = δ / 2 := by field_simp [ne_of_gt hX0_pos]
    have h2 : |(c' * xm + d) - (c * xm + d)| < δ / 2 := by
      have eq2 : (c' * xm + d) - (c * xm + d) = (c' - c) * xm := by ring
      rw [eq2, abs_mul]
      calc |c' - c| * |xm|
          ≤ |c' - c| * X0 := mul_le_mul_of_nonneg_left (le_of_lt hxm_lt) (abs_nonneg _)
        _ < (δ / (2 * X0)) * X0 := mul_lt_mul_of_pos_right hc hX0_pos
        _ = δ / 2 := by field_simp [ne_of_gt hX0_pos]
    exact ⟨h1, h2⟩
  refine ⟨hdiff_lt, ?_, ?_⟩
  · have hbounds := abs_lt.mp hdiff_lt
    rcases le_abs.mp hmarg with hpos | hneg
    · constructor <;> intro h <;> linarith
    · constructor <;> intro h <;> linarith
  · have hbounds := abs_lt.mp hdiff_lt
    rcases le_abs.mp hmarg with hpos | hneg
    · constructor <;> intro h <;> linarith
    · constructor <;> intro h <;> linarith

/-- Perturbing slopes `(a_i, c_i)` to make all 10 slopes pairwise distinct with `a_i < c_i`,
    while preserving realization of all 32 bitmasks. -/
lemma perturb_slopes_distinct (f₀ : Fin 5 → VFunc)
    (h_all : ∀ m : Fin 5 → Bool, ∃ p : ℝ × ℝ, RealizesVMask f₀ m p) :
    ∃ f₁ : Fin 5 → VFunc,
      (∀ i : Fin 5, (f₁ i).a < (f₁ i).c) ∧
      Function.Injective (fun k : Fin 5 × Bool => (dualPt f₁ k).1) ∧
      (∀ m : Fin 5 → Bool, ∃ p : ℝ × ℝ, RealizesVMask f₁ m p) := by
  choose pm hpm using h_all
  let pairs : Finset ((Fin 5 → Bool) × Fin 5) := Finset.univ
  have hpairs_ne : pairs.Nonempty := ⟨(fun _ => true, 0), Finset.mem_univ _⟩
  let margin : (Fin 5 → Bool) × Fin 5 → ℝ := fun q => |(pm q.1).2 - (f₀ q.2).eval (pm q.1).1|
  let δ : ℝ := pairs.inf' hpairs_ne margin
  have hδ_pos : 0 < δ := by
    rw [Finset.lt_inf'_iff]
    intro q _
    have hm := hpm q.1 q.2
    cases hqb : q.1 q.2 <;> simp only [hqb, Bool.false_eq_true, ↓reduceIte] at hm
    · exact abs_pos.mpr (by linarith)
    · exact abs_pos.mpr (by linarith)
  let X0 : ℝ := 1 + ∑ m : Fin 5 → Bool, |(pm m).1|
  have hX0_ge : 1 ≤ X0 := by
    have hs : 0 ≤ ∑ m : Fin 5 → Bool, |(pm m).1| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
    dsimp [X0]; linarith
  have hxm_le : ∀ m : Fin 5 → Bool, |(pm m).1| ≤ X0 - 1 := by
    intro m
    have h1 : |(pm m).1| ≤ ∑ m' : Fin 5 → Bool, |(pm m').1| :=
      Finset.single_le_sum (f := fun m' : Fin 5 → Bool => |(pm m').1|)
        (fun _ _ => abs_nonneg _) (Finset.mem_univ m)
    dsimp [X0]; linarith
  let step : ℝ := δ / (2 * X0)
  have hstep_pos : 0 < step := div_pos hδ_pos (by linarith)
  let lo : Fin 10 → ℝ := fun k =>
    if k.val % 2 = 0 then (f₀ ⟨k.val / 2, by omega⟩).a - step else (f₀ ⟨k.val / 2, by omega⟩).c
  let hi : Fin 10 → ℝ := fun k =>
    if k.val % 2 = 0 then (f₀ ⟨k.val / 2, by omega⟩).a else (f₀ ⟨k.val / 2, by omega⟩).c + step
  have hlohi : ∀ k : Fin 10, lo k < hi k := by
    intro k; dsimp [lo, hi]; split_ifs <;> linarith
  have hex_seq : ∀ (n : ℕ) (hn : n ≤ 10),
      ∃ g : Fin n → ℝ,
        (∀ j : Fin n, lo ⟨j.val, by omega⟩ < g j ∧ g j < hi ⟨j.val, by omega⟩) ∧
        Function.Injective g := by
    intro n
    induction n with
    | zero =>
      intro _
      refine ⟨Fin.elim0, fun j => Fin.elim0 j, fun j => Fin.elim0 j⟩
    | succ n ih =>
      intro hn
      obtain ⟨g', hg'_bounds, hg'_inj⟩ := ih (Nat.le_of_succ_le hn)
      let used : Finset ℝ := Finset.univ.image g'
      have hlt : lo ⟨n, hn⟩ < hi ⟨n, hn⟩ := hlohi ⟨n, hn⟩
      obtain ⟨xn, hxn_lo, hxn_hi, hxn_not⟩ := exists_mem_Ioo_avoiding _ _ hlt used
      refine ⟨Fin.snoc g' xn, ?_, ?_⟩
      · intro j
        refine Fin.lastCases ?_ ?_ j
        · simpa [Fin.snoc_last] using ⟨hxn_lo, hxn_hi⟩
        · intro j'
          simpa [Fin.snoc_castSucc] using hg'_bounds j'
      · intro j₁ j₂ heq
        revert heq
        refine Fin.lastCases ?_ ?_ j₁ <;> refine Fin.lastCases ?_ ?_ j₂
        · intro _; rfl
        · intro j₂' heq
          exfalso; apply hxn_not
          rw [Fin.snoc_last, Fin.snoc_castSucc] at heq
          rw [heq]
          exact Finset.mem_image_of_mem g' (Finset.mem_univ j₂')
        · intro j₁' heq
          exfalso; apply hxn_not
          rw [Fin.snoc_castSucc, Fin.snoc_last] at heq
          rw [← heq]
          exact Finset.mem_image_of_mem g' (Finset.mem_univ j₁')
        · intro j₁' j₂' heq
          rw [Fin.snoc_castSucc, Fin.snoc_castSucc] at heq
          exact congrArg Fin.castSucc (hg'_inj heq)
  obtain ⟨s₁₀, hs₁₀_bounds, hs₁₀_inj⟩ := hex_seq 10 (le_refl 10)
  let a' : Fin 5 → ℝ := fun i => s₁₀ ⟨2 * i.val, by omega⟩
  let c' : Fin 5 → ℝ := fun i => s₁₀ ⟨2 * i.val + 1, by omega⟩
  have ha'_bounds : ∀ i : Fin 5, (f₀ i).a - step < a' i ∧ a' i < (f₀ i).a := by
    intro i
    have hb := hs₁₀_bounds ⟨2 * i.val, by omega⟩
    dsimp [lo, hi] at hb
    have hmod : (2 * i.val) % 2 = 0 := by omega
    have hidx : (⟨(2 * i.val) / 2, by omega⟩ : Fin 5) = i := Fin.ext (by simp)
    simp only [hmod, ↓reduceIte, hidx] at hb
    exact hb
  have hc'_bounds : ∀ i : Fin 5, (f₀ i).c < c' i ∧ c' i < (f₀ i).c + step := by
    intro i
    have hb := hs₁₀_bounds ⟨2 * i.val + 1, by omega⟩
    dsimp [lo, hi] at hb
    have hmod : (2 * i.val + 1) % 2 ≠ 0 := by omega
    have hidx : (⟨(2 * i.val + 1) / 2, by omega⟩ : Fin 5) = i := Fin.ext (by simp; omega)
    simp only [hmod, ↓reduceIte, hidx] at hb
    exact hb
  have ha_lt_c : ∀ i : Fin 5, a' i < c' i := by
    intro i
    have h1 := (ha'_bounds i).2
    have h2 := (hc'_bounds i).1
    have hle := (f₀ i).hle
    linarith
  let f₁ : Fin 5 → VFunc := fun i =>
    { a := a' i, b := (f₀ i).b, c := c' i, d := (f₀ i).d, hle := le_of_lt (ha_lt_c i) }
  refine ⟨f₁, ha_lt_c, ?_, ?_⟩
  · rintro ⟨i₁, b₁⟩ ⟨i₂, b₂⟩ heq
    let idx : Fin 5 × Bool → Fin 10 := fun k =>
      if k.2 then ⟨2 * k.1.val + 1, by omega⟩ else ⟨2 * k.1.val, by omega⟩
    have hidx_inj : Function.Injective idx := by decide
    have hpt : ∀ k, (dualPt f₁ k).1 = s₁₀ (idx k) := by
      rintro ⟨i, b⟩; cases b <;> simp [dualPt, f₁, a', c', idx]
    dsimp only at heq
    rw [hpt (i₁, b₁), hpt (i₂, b₂)] at heq
    exact hidx_inj (hs₁₀_inj heq)
  · intro m
    refine ⟨pm m, fun i => ?_⟩
    have hmarg_i : δ ≤ |(pm m).2 - (f₀ i).eval (pm m).1| :=
      Finset.inf'_le margin (Finset.mem_univ (m, i))
    have ha_dist : |a' i - (f₀ i).a| < δ / (2 * X0) := by
      rw [abs_lt]; constructor <;> linarith [(ha'_bounds i).1, (ha'_bounds i).2]
    have hc_dist : |c' i - (f₀ i).c| < δ / (2 * X0) := by
      rw [abs_lt]; constructor <;> linarith [(hc'_bounds i).1, (hc'_bounds i).2]
    have hpres := slope_perturb_preserve (f₀ i).a (f₀ i).b (f₀ i).c (f₀ i).d (a' i) (c' i)
      (pm m).1 (pm m).2 δ X0 hδ_pos hX0_ge (hxm_le m) hmarg_i ha_dist hc_dist
    have hmi := hpm m i
    unfold VFunc.eval at hmi ⊢
    dsimp [f₁]
    by_cases hmb : m i
    · simp only [hmb, ↓reduceIte] at hmi ⊢
      exact hpres.2.1.mp hmi
    · simp only [hmb, Bool.false_eq_true, ↓reduceIte] at hmi ⊢
      exact hpres.2.2.mp hmi

/-- Avoiding finitely many nonzero affine hyperplanes `∑ j, α j * w j = γ` inside any open box in `ℝ^n`. -/
lemma avoid_hyperplanes :
    ∀ (n : ℕ) (l r : Fin n → ℝ) (_ : ∀ j, l j < r j)
      (H : Finset ((Fin n → ℝ) × ℝ)) (_ : ∀ p ∈ H, p.1 ≠ 0),
      ∃ w : Fin n → ℝ, (∀ j, l j < w j ∧ w j < r j) ∧
        ∀ p ∈ H, (∑ j : Fin n, p.1 j * w j) ≠ p.2 := by
  intro n
  induction n with
  | zero =>
    intro l r _ H hH
    refine ⟨Fin.elim0, fun j => Fin.elim0 j, fun p hp => ?_⟩
    exfalso
    apply hH p hp
    ext j
    exact Fin.elim0 j
  | succ n ih =>
    intro l r hlr H hH
    let H_last := H.filter (fun p => p.1 (Fin.last n) ≠ 0)
    let H_rest := H.filter (fun p => p.1 (Fin.last n) = 0)
    let proj : ((Fin (n + 1) → ℝ) × ℝ) → ((Fin n → ℝ) × ℝ) :=
      fun p => (fun j => p.1 j.castSucc, p.2)
    let H' : Finset ((Fin n → ℝ) × ℝ) := H_rest.image proj
    have hH' : ∀ p' ∈ H', p'.1 ≠ 0 := by
      intro p' hp'
      rcases Finset.mem_image.mp hp' with ⟨p, hp, rfl⟩
      have hp_rest := (Finset.mem_filter.mp hp)
      have hne := hH p hp_rest.1
      intro hzero
      apply hne
      ext j
      refine Fin.lastCases ?_ ?_ j
      · exact hp_rest.2
      · intro j'
        have := congrFun hzero j'
        simpa [proj] using this
    obtain ⟨w', hw'_bounds, hw'_avoid⟩ :=
      ih (fun j => l j.castSucc) (fun j => r j.castSucc) (fun j => hlr j.castSucc) H' hH'
    let forb : ((Fin (n + 1) → ℝ) × ℝ) → ℝ :=
      fun p => (p.2 - ∑ j : Fin n, p.1 j.castSucc * w' j) / p.1 (Fin.last n)
    obtain ⟨wn, hwn_lo, hwn_hi, hwn_not⟩ :=
      exists_mem_Ioo_avoiding (l (Fin.last n)) (r (Fin.last n)) (hlr (Fin.last n)) (H_last.image forb)
    refine ⟨Fin.snoc w' wn, ?_, ?_⟩
    · intro j
      refine Fin.lastCases ?_ ?_ j
      · simpa [Fin.snoc_last] using ⟨hwn_lo, hwn_hi⟩
      · intro j'
        simpa [Fin.snoc_castSucc] using hw'_bounds j'
    · intro p hp
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.snoc_castSucc, Fin.snoc_last]
      by_cases hlast : p.1 (Fin.last n) = 0
      · have hp' : proj p ∈ H' :=
          Finset.mem_image_of_mem proj (Finset.mem_filter.mpr ⟨hp, hlast⟩)
        have hne := hw'_avoid (proj p) hp'
        simpa [proj, hlast] using hne
      · intro heq
        apply hwn_not
        refine Finset.mem_image.mpr ⟨p, Finset.mem_filter.mpr ⟨hp, hlast⟩, ?_⟩
        dsimp [forb]
        field_simp [hlast]
        linarith

/-- Encoding `Fin 5 × Bool ≃ Fin 10`. -/
def kToFin10 (k : Fin 5 × Bool) : Fin 10 :=
  if k.2 then ⟨2 * k.1.val + 1, by omega⟩ else ⟨2 * k.1.val, by omega⟩

lemma kToFin10_inj : Function.Injective kToFin10 := by
  decide

lemma kToFin10_bij : Function.Bijective kToFin10 :=
  (Fintype.bijective_iff_injective_and_card kToFin10).mpr ⟨kToFin10_inj, by decide⟩

def kEquivFin10 : (Fin 5 × Bool) ≃ Fin 10 :=
  Equiv.ofBijective kToFin10 kToFin10_bij

/-- Constructing a linear constraint `(α : Fin 10 → ℝ, 0)` from a coefficient function on `Fin 5 × Bool`. -/
def mkPlane (c : Fin 5 × Bool → ℝ) : (Fin 10 → ℝ) × ℝ :=
  (fun j => c (kEquivFin10.symm j), 0)

lemma mkPlane_eval (c : Fin 5 × Bool → ℝ) (w : Fin 10 → ℝ) :
    (∑ j : Fin 10, (mkPlane c).1 j * w j) =
      ∑ k : Fin 5 × Bool, c k * w (kToFin10 k) := by
  dsimp [mkPlane]
  rw [← Equiv.sum_comp kEquivFin10]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  change c (kEquivFin10.symm (kEquivFin10 k)) * w (kEquivFin10 k) = c k * w (kToFin10 k)
  rw [kEquivFin10.symm_apply_apply]
  rfl

lemma mkPlane_ne_zero (c : Fin 5 × Bool → ℝ) (k₀ : Fin 5 × Bool) (hk₀ : c k₀ ≠ 0) :
    (mkPlane c).1 ≠ 0 := by
  intro hzero
  apply hk₀
  have h := congrFun hzero (kToFin10 k₀)
  change c (kEquivFin10.symm (kEquivFin10 k₀)) = 0 at h
  rwa [kEquivFin10.symm_apply_apply] at h

/-- Relabel `Fin 5` so that `a_0 < a_1 < a_2 < a_3 < a_4`. -/
lemma sort_vfuncs_a (f₁ : Fin 5 → VFunc)
    (hf₁_ac : ∀ i : Fin 5, (f₁ i).a < (f₁ i).c)
    (hf₁_inj : Function.Injective (fun k : Fin 5 × Bool => (dualPt f₁ k).1))
    (h_all₁ : ∀ m : Fin 5 → Bool, ∃ p : ℝ × ℝ, RealizesVMask f₁ m p) :
    ∃ f₂ : Fin 5 → VFunc,
      (∀ i : Fin 5, (f₂ i).a < (f₂ i).c) ∧
      StrictMono (fun i : Fin 5 => (f₂ i).a) ∧
      Function.Injective (fun k : Fin 5 × Bool => (dualPt f₂ k).1) ∧
      (∀ m : Fin 5 → Bool, ∃ p : ℝ × ℝ, RealizesVMask f₂ m p) := by
  have ha₁_inj : Function.Injective (fun i : Fin 5 => (f₁ i).a) := by
    intro i j hij
    have := hf₁_inj (a₁ := (i, false)) (a₂ := (j, false)) hij
    exact (Prod.ext_iff.mp this).1
  let A_set : Finset ℝ := Finset.univ.image (fun i : Fin 5 => (f₁ i).a)
  have hcard : A_set.card = 5 := by
    rw [Finset.card_image_of_injective _ ha₁_inj, Finset.card_fin]
  let emb := A_set.orderEmbOfFin hcard
  have hmem : ∀ r : Fin 5, ∃ i : Fin 5, (f₁ i).a = emb r := by
    intro r
    have hr := Finset.orderEmbOfFin_mem A_set hcard r
    rcases Finset.mem_image.mp hr with ⟨i, _, hi⟩
    exact ⟨i, hi⟩
  choose τ_fn hτ_fn using hmem
  have hτ_inj : Function.Injective τ_fn := by
    intro r₁ r₂ heq
    have h1 : emb r₁ = emb r₂ := by rw [← hτ_fn r₁, ← hτ_fn r₂, heq]
    exact emb.injective h1
  let τ : Equiv.Perm (Fin 5) := Equiv.ofBijective τ_fn
    ((Fintype.bijective_iff_injective_and_card τ_fn).mpr ⟨hτ_inj, by simp⟩)
  let f₂ : Fin 5 → VFunc := fun i => f₁ (τ i)
  refine ⟨f₂, fun i => hf₁_ac (τ i), ?_, ?_, ?_⟩
  · intro i j hij
    change (f₁ (τ_fn i)).a < (f₁ (τ_fn j)).a
    rw [hτ_fn i, hτ_fn j]
    exact emb.strictMono hij
  · rintro ⟨i₁, b₁⟩ ⟨i₂, b₂⟩ heq
    have : (dualPt f₁ (τ i₁, b₁)).1 = (dualPt f₁ (τ i₂, b₂)).1 := by
      cases b₁ <;> cases b₂ <;> simpa [dualPt, f₂] using heq
    have hprod := hf₁_inj this
    rcases Prod.ext_iff.mp hprod with ⟨hi, hb⟩
    exact Prod.ext (τ.injective hi) hb
  · intro m
    obtain ⟨p, hp⟩ := h_all₁ (fun i => m (τ.symm i))
    refine ⟨p, fun i => ?_⟩
    simpa [f₂] using hp (τ i)

/-- Build strict dual witnesses `DualRealizes f₂ S s t` for all 32 subsets `S : Finset (Fin 5)`. -/
lemma build_strict_dual_witnesses (f₂ : Fin 5 → VFunc)
    (h_all₂ : ∀ m : Fin 5 → Bool, ∃ p : ℝ × ℝ, RealizesVMask f₂ m p) :
    ∀ S : Finset (Fin 5), ∃ s t : ℝ, DualRealizes f₂ S s t := by
  intro S
  obtain ⟨⟨x, y⟩, hm⟩ := h_all₂ (fun i => decide (i ∉ S))
  let s₀ : ℝ := -x
  let t₀ : ℝ := y
  let U₀ : Finset (Fin 5 × Bool) :=
    Finset.univ.filter (fun k => s₀ * (dualPt f₂ k).1 + t₀ < (dualPt f₂ k).2)
  have h_shift : ∃ t : ℝ, (∀ k : Fin 5 × Bool, (dualPt f₂ k).2 ≠ s₀ * (dualPt f₂ k).1 + t) ∧
      (∀ k : Fin 5 × Bool, s₀ * (dualPt f₂ k).1 + t < (dualPt f₂ k).2 ↔ k ∈ U₀) := by
    by_cases hU : U₀.Nonempty
    · let gap : ℝ := U₀.inf' hU (fun k => (dualPt f₂ k).2 - (s₀ * (dualPt f₂ k).1 + t₀))
      have hgap_pos : 0 < gap := by
        rw [Finset.lt_inf'_iff]
        intro k hk
        have hk' := (Finset.mem_filter.mp hk).2
        linarith
      refine ⟨t₀ + gap / 2, ?_, ?_⟩
      · intro k
        by_cases hk : k ∈ U₀
        · have hk_le : gap ≤ (dualPt f₂ k).2 - (s₀ * (dualPt f₂ k).1 + t₀) :=
            Finset.inf'_le _ hk
          linarith
        · have hk' : (dualPt f₂ k).2 ≤ s₀ * (dualPt f₂ k).1 + t₀ :=
            not_lt.mp (fun hlt => hk (Finset.mem_filter.mpr ⟨Finset.mem_univ k, hlt⟩))
          linarith
      · intro k
        constructor <;> intro hk
        · by_contra hnot
          have hk' : (dualPt f₂ k).2 ≤ s₀ * (dualPt f₂ k).1 + t₀ :=
            not_lt.mp (fun hlt => hnot (Finset.mem_filter.mpr ⟨Finset.mem_univ k, hlt⟩))
          linarith
        · have hk_le : gap ≤ (dualPt f₂ k).2 - (s₀ * (dualPt f₂ k).1 + t₀) :=
            Finset.inf'_le _ hk
          linarith
    · rw [Finset.not_nonempty_iff_eq_empty] at hU
      refine ⟨t₀ + 1, ?_, ?_⟩
      · intro k
        have hk' : (dualPt f₂ k).2 ≤ s₀ * (dualPt f₂ k).1 + t₀ := by
          by_contra hlt
          have : k ∈ U₀ := Finset.mem_filter.mpr ⟨Finset.mem_univ k, not_le.mp hlt⟩
          rw [hU] at this
          exact Finset.notMem_empty _ this
        linarith
      · intro k
        rw [hU]
        simp only [Finset.notMem_empty, iff_false, not_lt]
        have hk' : (dualPt f₂ k).2 ≤ s₀ * (dualPt f₂ k).1 + t₀ := by
          by_contra hlt
          have : k ∈ U₀ := Finset.mem_filter.mpr ⟨Finset.mem_univ k, not_le.mp hlt⟩
          rw [hU] at this
          exact Finset.notMem_empty _ this
        linarith
  obtain ⟨t, ht_disj, ht_U⟩ := h_shift
  refine ⟨s₀, t, ht_disj, fun i => ?_⟩
  by_cases hi : i ∈ S
  · refine ⟨fun _ => ?_, fun _ => hi⟩
    have hmi := hm i
    simp only [hi, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte] at hmi
    unfold VFunc.eval at hmi
    rw [lt_max_iff] at hmi
    rcases hmi with hlt | hlt
    · refine ⟨false, (ht_U (i, false)).mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩)⟩
      simp only [dualPt_false]; dsimp [s₀, t₀]; linarith
    · refine ⟨true, (ht_U (i, true)).mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩)⟩
      simp only [dualPt_true]; dsimp [s₀, t₀]; linarith
  · refine ⟨fun h => False.elim (hi h), ?_⟩
    rintro ⟨b, hb⟩
    have hmemU := (Finset.mem_filter.mp ((ht_U (i, b)).mp hb)).2
    have hmi := hm i
    simp only [hi, not_false_eq_true, decide_true, ↓reduceIte] at hmi
    unfold VFunc.eval at hmi
    rw [max_lt_iff] at hmi
    cases b
    · simp only [dualPt_false] at hmemU; dsimp [s₀, t₀] at hmemU; linarith
    · simp only [dualPt_true] at hmemU; dsimp [s₀, t₀] at hmemU; linarith

private def planeCol (s : Fin 5 × Bool → ℝ) (p q r : Fin 5 × Bool) : (Fin 10 → ℝ) × ℝ :=
  mkPlane (fun k =>
    (if k = p then s q - s r else 0) +
    (if k = q then s r - s p else 0) +
    (if k = r then s p - s q else 0))

private def planeKinkEq (s : Fin 5 × Bool → ℝ) (i j : Fin 5) : (Fin 10 → ℝ) × ℝ :=
  mkPlane (fun k =>
    (if k = (i, true) then s (j, false) - s (j, true) else 0) +
    (if k = (i, false) then -(s (j, false) - s (j, true)) else 0) +
    (if k = (j, true) then -(s (i, false) - s (i, true)) else 0) +
    (if k = (j, false) then s (i, false) - s (i, true) else 0))

private def planeGpaVal (s : Fin 5 × Bool → ℝ) (i j : Fin 5) (b : Bool) : (Fin 10 → ℝ) × ℝ :=
  mkPlane (fun k =>
    (if k = (i, true) then s (i, false) - s (j, b) else 0) +
    (if k = (i, false) then (s (i, false) - s (i, true)) - (s (i, false) - s (j, b)) else 0) +
    (if k = (j, b) then -(s (i, false) - s (i, true)) else 0))

private def planeQuad (s : Fin 5 × Bool → ℝ) (p1 p2 p3 p4 : Fin 5 × Bool) : (Fin 10 → ℝ) × ℝ :=
  mkPlane (fun k =>
    (if k = p2 then s p3 - s p4 else 0) +
    (if k = p1 then -(s p3 - s p4) else 0) +
    (if k = p4 then -(s p1 - s p2) else 0) +
    (if k = p3 then s p1 - s p2 else 0))

private def quadGood (p1 p2 p3 p4 : Fin 5 × Bool) : Bool :=
  decide (p1 ≠ p2 ∧ p3 ≠ p4 ∧
    (p1.1 ≠ p3.1 ∧ p1.1 ≠ p4.1 ∨ p2.1 ≠ p3.1 ∧ p2.1 ≠ p4.1 ∨
     p3.1 ≠ p1.1 ∧ p3.1 ≠ p2.1 ∨ p4.1 ≠ p1.1 ∧ p4.1 ≠ p2.1))

private def gpHyperplanes (s : Fin 5 × Bool → ℝ) : Finset ((Fin 10 → ℝ) × ℝ) :=
  let H_col := ((Finset.univ : Finset ((Fin 5 × Bool) × (Fin 5 × Bool) × (Fin 5 × Bool))).filter
    (fun ⟨p, q, r⟩ => p ≠ q ∧ q ≠ r ∧ p ≠ r)).image (fun ⟨p, q, r⟩ => planeCol s p q r)
  let H_kink := ((Finset.univ : Finset (Fin 5 × Fin 5)).filter
    (fun ⟨i, j⟩ => i ≠ j)).image (fun ⟨i, j⟩ => planeKinkEq s i j)
  let H_gpa := ((Finset.univ : Finset (Fin 5 × Fin 5 × Bool)).filter
    (fun ⟨i, j, _⟩ => i ≠ j)).image (fun ⟨i, j, b⟩ => planeGpaVal s i j b)
  let H_gpb := ((Finset.univ : Finset ((Fin 5 × Bool) × (Fin 5 × Bool) × (Fin 5 × Bool) × (Fin 5 × Bool))).filter
    (fun ⟨p1, p2, p3, p4⟩ => quadGood p1 p2 p3 p4 = true)).image
      (fun ⟨p1, p2, p3, p4⟩ => planeQuad s p1 p2 p3 p4)
  H_col ∪ H_kink ∪ H_gpa ∪ H_gpb

private lemma gpHyperplanes_nonzero (s : Fin 5 × Bool → ℝ) (hs_inj : Function.Injective s) :
    ∀ hp ∈ gpHyperplanes s, hp.1 ≠ 0 := by
  intro hp hmem
  unfold gpHyperplanes at hmem
  simp only [Finset.mem_union] at hmem
  rcases hmem with ((hmem | hmem) | hmem) | hmem
  · rcases Finset.mem_image.mp hmem with ⟨⟨p, q, r⟩, hfilt, rfl⟩
    obtain ⟨hpq, hqr, hpr⟩ := (Finset.mem_filter.mp hfilt).2
    refine mkPlane_ne_zero _ p ?_
    simp only [planeCol, hpq, hpr, ↓reduceIte, add_zero]
    exact sub_ne_zero.mpr (fun h => hqr (hs_inj h))
  · rcases Finset.mem_image.mp hmem with ⟨⟨i, j⟩, hfilt, rfl⟩
    have hij : i ≠ j := (Finset.mem_filter.mp hfilt).2
    refine mkPlane_ne_zero _ (i, true) ?_
    have h1 : (i, true) ≠ (i, false) := fun h => Bool.false_ne_true (congrArg Prod.snd h).symm
    have h2 : (i, true) ≠ (j, true) := fun h => hij (congrArg Prod.fst h)
    have h3 : (i, true) ≠ (j, false) := fun h => hij (congrArg Prod.fst h)
    simp only [planeKinkEq, h1, h2, h3, ↓reduceIte, add_zero]
    exact sub_ne_zero.mpr (fun h => Bool.false_ne_true (congrArg Prod.snd (hs_inj h)))
  · rcases Finset.mem_image.mp hmem with ⟨⟨i, j, b⟩, hfilt, rfl⟩
    have hij : i ≠ j := (Finset.mem_filter.mp hfilt).2
    refine mkPlane_ne_zero _ (j, b) ?_
    have h1 : (j, b) ≠ (i, true) := fun h => hij (congrArg Prod.fst h).symm
    have h2 : (j, b) ≠ (i, false) := fun h => hij (congrArg Prod.fst h).symm
    simp only [planeGpaVal, h1, h2, ↓reduceIte, zero_add]
    exact neg_ne_zero.mpr (sub_ne_zero.mpr (fun h => Bool.false_ne_true (congrArg Prod.snd (hs_inj h))))
  · rcases Finset.mem_image.mp hmem with ⟨⟨p1, p2, p3, p4⟩, hfilt, rfl⟩
    have hq := (Finset.mem_filter.mp hfilt).2
    simp only [quadGood, decide_eq_true_eq] at hq
    obtain ⟨hp12, hp34, hdisj⟩ := hq
    rcases hdisj with ⟨h13, h14⟩ | ⟨h23, h24⟩ | ⟨h31, h32⟩ | ⟨h41, h42⟩
    · refine mkPlane_ne_zero _ p1 ?_
      have h13' : p1 ≠ p3 := fun h => h13 (congrArg Prod.fst h)
      have h14' : p1 ≠ p4 := fun h => h14 (congrArg Prod.fst h)
      simp only [planeQuad, hp12, h13', h14', ↓reduceIte, zero_add, add_zero]
      exact neg_ne_zero.mpr (sub_ne_zero.mpr (fun h => hp34 (hs_inj h)))
    · refine mkPlane_ne_zero _ p2 ?_
      have h23' : p2 ≠ p3 := fun h => h23 (congrArg Prod.fst h)
      have h24' : p2 ≠ p4 := fun h => h24 (congrArg Prod.fst h)
      simp only [planeQuad, hp12.symm, h23', h24', ↓reduceIte, add_zero]
      exact sub_ne_zero.mpr (fun h => hp34 (hs_inj h))
    · refine mkPlane_ne_zero _ p3 ?_
      have h31' : p3 ≠ p1 := fun h => h31 (congrArg Prod.fst h)
      have h32' : p3 ≠ p2 := fun h => h32 (congrArg Prod.fst h)
      simp only [planeQuad, h31', h32', hp34, ↓reduceIte, zero_add]
      exact sub_ne_zero.mpr (fun h => hp12 (hs_inj h))
    · refine mkPlane_ne_zero _ p4 ?_
      have h41' : p4 ≠ p1 := fun h => h41 (congrArg Prod.fst h)
      have h42' : p4 ≠ p2 := fun h => h42 (congrArg Prod.fst h)
      simp only [planeQuad, h41', h42', hp34.symm, ↓reduceIte, zero_add, add_zero]
      exact neg_ne_zero.mpr (sub_ne_zero.mpr (fun h => hp12 (hs_inj h)))

private lemma planeCol_mem (s : Fin 5 × Bool → ℝ) (p q r : Fin 5 × Bool)
    (hpq : p ≠ q) (hqr : q ≠ r) (hpr : p ≠ r) :
    planeCol s p q r ∈ gpHyperplanes s := by
  unfold gpHyperplanes
  refine Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ ?_))
  exact Finset.mem_image.mpr ⟨(p, q, r), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpq, hqr, hpr⟩, rfl⟩

private lemma planeKinkEq_mem (s : Fin 5 × Bool → ℝ) (i j : Fin 5) (hij : i ≠ j) :
    planeKinkEq s i j ∈ gpHyperplanes s := by
  unfold gpHyperplanes
  refine Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ ?_))
  exact Finset.mem_image.mpr ⟨(i, j), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hij⟩, rfl⟩

private lemma planeGpaVal_mem (s : Fin 5 × Bool → ℝ) (i j : Fin 5) (b : Bool) (hij : i ≠ j) :
    planeGpaVal s i j b ∈ gpHyperplanes s := by
  unfold gpHyperplanes
  refine Finset.mem_union_left _ (Finset.mem_union_right _ ?_)
  exact Finset.mem_image.mpr ⟨(i, j, b), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hij⟩, rfl⟩

private lemma planeQuad_mem (s : Fin 5 × Bool → ℝ) (p1 p2 p3 p4 : Fin 5 × Bool)
    (hq : quadGood p1 p2 p3 p4 = true) :
    planeQuad s p1 p2 p3 p4 ∈ gpHyperplanes s := by
  unfold gpHyperplanes
  refine Finset.mem_union_right _ ?_
  exact Finset.mem_image.mpr ⟨(p1, p2, p3, p4), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hq⟩, rfl⟩

/-- Perturbing intercepts `(b_i, d_i)` of `f₂` inside an `ε`-box to achieve full general position
    (non-collinearity, GP-A, GP-B) while preserving all 32 strict dual witnesses. -/
lemma perturb_intercepts_gp (f₂ : Fin 5 → VFunc)
    (hf₂_ac : ∀ i : Fin 5, (f₂ i).a < (f₂ i).c)
    (hf₂_mono : StrictMono (fun i : Fin 5 => (f₂ i).a))
    (hf₂_inj : Function.Injective (fun k : Fin 5 × Bool => (dualPt f₂ k).1))
    (h_dual₂ : ∀ S : Finset (Fin 5), ∃ s t : ℝ, DualRealizes f₂ S s t) :
    ∃ f : Fin 5 → VFunc,
      (∀ i : Fin 5, (f i).a < (f i).c) ∧
      StrictMono (fun i : Fin 5 => (f i).a) ∧
      Function.Injective (fun k : Fin 5 × Bool => (dualPt f k).1) ∧
      (∀ p q r : Fin 5 × Bool, p ≠ q → q ≠ r → p ≠ r →
        ((dualPt f q).1 - (dualPt f p).1) * ((dualPt f r).2 - (dualPt f p).2) -
        ((dualPt f q).2 - (dualPt f p).2) * ((dualPt f r).1 - (dualPt f p).1) ≠ 0) ∧
      (∀ S : Finset (Fin 5), ∃ s t : ℝ, DualRealizes f S s t) ∧
      (∀ m : Fin 5 → Bool, ∃ p : ℝ × ℝ, RealizesVMask f m p) ∧
      (∀ i j : Fin 5, i ≠ j → kink f i ≠ kink f j) ∧
      (∀ i j : Fin 5, i ≠ j → (f i).eval (kink f i) ≠ (f j).eval (kink f i)) ∧
      (∀ i j k l : Fin 5, i < j → k < l → (i, j) ≠ (k, l) → ∀ x : ℝ,
        ¬ ((f i).eval x = (f j).eval x ∧ (f k).eval x = (f l).eval x)) ∧
      (∀ i j m : Fin 5, i < j → (f i).eval (kink f m) ≠ (f j).eval (kink f m)) := by
  choose sw tw h_dual_w using h_dual₂
  let witnessPairs : Finset (Finset (Fin 5) × (Fin 5 × Bool)) := Finset.univ
  have hwP_ne : witnessPairs.Nonempty := ⟨(∅, (0, false)), Finset.mem_univ _⟩
  let wMargin : Finset (Fin 5) × (Fin 5 × Bool) → ℝ :=
    fun p => |(dualPt f₂ p.2).2 - (sw p.1 * (dualPt f₂ p.2).1 + tw p.1)|
  let ε : ℝ := witnessPairs.inf' hwP_ne wMargin
  have hε_pos : 0 < ε := by
    rw [Finset.lt_inf'_iff]
    intro p _
    exact abs_pos.mpr (sub_ne_zero.mpr ((h_dual_w p.1).1 p.2))
  let s : Fin 5 × Bool → ℝ := fun k => (dualPt f₂ k).1
  let w₀ : Fin 10 → ℝ := fun j => (dualPt f₂ (kEquivFin10.symm j)).2
  obtain ⟨w, hw_box, hw_avoid⟩ :=
    avoid_hyperplanes 10 (fun j => w₀ j - ε) (fun j => w₀ j + ε)
      (fun j => by linarith) (gpHyperplanes s) (gpHyperplanes_nonzero s hf₂_inj)
  let f : Fin 5 → VFunc := fun i =>
    { a := (f₂ i).a
      b := w (kToFin10 (i, false))
      c := (f₂ i).c
      d := w (kToFin10 (i, true))
      hle := (f₂ i).hle }
  have hpt_u : ∀ k : Fin 5 × Bool, (dualPt f k).1 = s k := by
    rintro ⟨i, b⟩; cases b <;> simp [dualPt, f, s]
  have hpt_v : ∀ k : Fin 5 × Bool, (dualPt f k).2 = w (kToFin10 k) := by
    rintro ⟨i, b⟩; cases b <;> simp [dualPt, f]
  have hpt_close : ∀ k : Fin 5 × Bool, |(dualPt f k).2 - (dualPt f₂ k).2| < ε := by
    intro k
    rw [hpt_v]
    have hb := hw_box (kToFin10 k)
    have h0 : w₀ (kToFin10 k) = (dualPt f₂ k).2 := by
      dsimp [w₀]; change (dualPt f₂ (kEquivFin10.symm (kEquivFin10 k))).2 = _
      rw [kEquivFin10.symm_apply_apply]
    rw [h0] at hb
    rw [abs_lt]; constructor <;> linarith [hb.1, hb.2]
  have h_fac : ∀ i : Fin 5, (f i).a < (f i).c := hf₂_ac
  have h_mono : StrictMono (fun i : Fin 5 => (f i).a) := hf₂_mono
  have h_inj : Function.Injective (fun k : Fin 5 × Bool => (dualPt f k).1) := by
    intro k₁ k₂ heq; dsimp at heq; rw [hpt_u k₁, hpt_u k₂] at heq; exact hf₂_inj heq
  have h_noncol : ∀ p q r : Fin 5 × Bool, p ≠ q → q ≠ r → p ≠ r →
      ((dualPt f q).1 - (dualPt f p).1) * ((dualPt f r).2 - (dualPt f p).2) -
      ((dualPt f q).2 - (dualPt f p).2) * ((dualPt f r).1 - (dualPt f p).1) ≠ 0 := by
    intro p q r hpq hqr hpr
    have hne := hw_avoid _ (planeCol_mem s p q r hpq hqr hpr)
    dsimp [planeCol] at hne
    rw [mkPlane_eval] at hne
    have hsum : (∑ k : Fin 5 × Bool,
        ((if k = p then s q - s r else 0) +
         (if k = q then s r - s p else 0) +
         (if k = r then s p - s q else 0)) * w (kToFin10 k)) =
        (s q - s r) * w (kToFin10 p) + (s r - s p) * w (kToFin10 q) +
        (s p - s q) * w (kToFin10 r) := by
      simp only [add_mul, Finset.sum_add_distrib, ite_mul, zero_mul,
        Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
    rw [hsum] at hne
    change (s q - s r) * w (kToFin10 p) + (s r - s p) * w (kToFin10 q) +
      (s p - s q) * w (kToFin10 r) ≠ 0 at hne
    rw [hpt_u p, hpt_u q, hpt_u r, hpt_v p, hpt_v q, hpt_v r]
    intro heq
    apply hne
    linarith
  have h_dual : ∀ S : Finset (Fin 5), ∃ s' t' : ℝ, DualRealizes f S s' t' := by
    intro S
    refine ⟨sw S, tw S, ?_, ?_⟩
    · intro k
      have hm : ε ≤ |(dualPt f₂ k).2 - (sw S * (dualPt f₂ k).1 + tw S)| :=
        Finset.inf'_le wMargin (Finset.mem_univ (S, k))
      have hc := abs_lt.mp (hpt_close k)
      rw [hpt_u]
      dsimp [s]
      rcases le_abs.mp hm with hpos | hneg <;> intro heq <;> linarith
    · intro i
      rw [(h_dual_w S).2 i]
      refine exists_congr (fun b => ?_)
      have hm : ε ≤ |(dualPt f₂ (i, b)).2 - (sw S * (dualPt f₂ (i, b)).1 + tw S)| :=
        Finset.inf'_le wMargin (Finset.mem_univ (S, (i, b)))
      have hc := abs_lt.mp (hpt_close (i, b))
      rw [hpt_u]
      dsimp [s]
      rcases le_abs.mp hm with hpos | hneg
      · constructor <;> intro h <;> linarith
      · constructor <;> intro h <;> linarith
  have h_realizes : ∀ m : Fin 5 → Bool, ∃ p : ℝ × ℝ, RealizesVMask f m p := by
    intro m
    let S : Finset (Fin 5) := Finset.univ.filter (fun i => m i = false)
    obtain ⟨s', t', hdisj, hS⟩ := h_dual S
    refine ⟨(-s', t'), ?_⟩
    have heqv := (dualRealizes_iff_realizesVMask f S (-s') t' (by simpa using hdisj)).mp
      (by simpa using ⟨hdisj, hS⟩)
    intro i
    have hi := heqv i
    by_cases hmi : m i
    · have hiS : i ∉ S := by simp [S, hmi]
      simpa [hmi, hiS] using hi
    · have hmif : m i = false := Bool.eq_false_iff.mpr hmi
      have hiS : i ∈ S := by simp [S, hmif]
      simpa [hmif, hiS] using hi
  have h_gpa_kinks : ∀ i j : Fin 5, i ≠ j → kink f i ≠ kink f j := by
    intro i j hij heq
    have hne := hw_avoid _ (planeKinkEq_mem s i j hij)
    dsimp [planeKinkEq] at hne
    rw [mkPlane_eval] at hne
    have hsum : (∑ k : Fin 5 × Bool,
        ((if k = (i, true) then s (j, false) - s (j, true) else 0) +
         (if k = (i, false) then -(s (j, false) - s (j, true)) else 0) +
         (if k = (j, true) then -(s (i, false) - s (i, true)) else 0) +
         (if k = (j, false) then s (i, false) - s (i, true) else 0)) * w (kToFin10 k)) =
        (s (j, false) - s (j, true)) * (w (kToFin10 (i, true)) - w (kToFin10 (i, false))) -
        (s (i, false) - s (i, true)) * (w (kToFin10 (j, true)) - w (kToFin10 (j, false))) := by
      simp only [add_mul, Finset.sum_add_distrib, ite_mul, zero_mul,
        Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
      ring
    rw [hsum] at hne
    change (s (j, false) - s (j, true)) * (w (kToFin10 (i, true)) - w (kToFin10 (i, false))) -
      (s (i, false) - s (i, true)) * (w (kToFin10 (j, true)) - w (kToFin10 (j, false))) ≠ 0 at hne
    apply hne
    dsimp [kink] at heq
    have hci : (f i).c - (f i).a ≠ 0 := sub_ne_zero.mpr (ne_of_gt (h_fac i))
    have hcj : (f j).c - (f j).a ≠ 0 := sub_ne_zero.mpr (ne_of_gt (h_fac j))
    rw [div_eq_div_iff hci hcj] at heq
    have hsif : s (i, false) = (f i).a := by simp [s, dualPt, f]
    have hsit : s (i, true) = (f i).c := by simp [s, dualPt, f]
    have hsjf : s (j, false) = (f j).a := by simp [s, dualPt, f]
    have hsjt : s (j, true) = (f j).c := by simp [s, dualPt, f]
    have hwif : w (kToFin10 (i, false)) = (f i).b := rfl
    have hwit : w (kToFin10 (i, true)) = (f i).d := rfl
    have hwjf : w (kToFin10 (j, false)) = (f j).b := rfl
    have hwjt : w (kToFin10 (j, true)) = (f j).d := rfl
    rw [hsif, hsit, hsjf, hsjt, hwif, hwit, hwjf, hwjt]
    linarith
  have eval_eq_branch : ∀ (i : Fin 5) (x : ℝ),
      ∃ b : Bool, (f i).eval x = (dualPt f (i, b)).1 * x + (dualPt f (i, b)).2 := by
    intro i x
    unfold VFunc.eval
    rcases le_total ((f i).a * x + (f i).b) ((f i).c * x + (f i).d) with h | h
    · rw [max_eq_right h]; exact ⟨true, rfl⟩
    · rw [max_eq_left h]; exact ⟨false, rfl⟩
  have h_gpa_vals : ∀ i j : Fin 5, i ≠ j → (f i).eval (kink f i) ≠ (f j).eval (kink f i) := by
    intro i j hij heq
    rw [eval_kink f i (h_fac i)] at heq
    obtain ⟨b, hb⟩ := eval_eq_branch j (kink f i)
    rw [hb] at heq
    have hne := hw_avoid _ (planeGpaVal_mem s i j b hij)
    dsimp [planeGpaVal] at hne
    rw [mkPlane_eval] at hne
    have hsum : (∑ k : Fin 5 × Bool,
        ((if k = (i, true) then s (i, false) - s (j, b) else 0) +
         (if k = (i, false) then (s (i, false) - s (i, true)) - (s (i, false) - s (j, b)) else 0) +
         (if k = (j, b) then -(s (i, false) - s (i, true)) else 0)) * w (kToFin10 k)) =
        (s (i, false) - s (j, b)) * w (kToFin10 (i, true)) +
        ((s (i, false) - s (i, true)) - (s (i, false) - s (j, b))) * w (kToFin10 (i, false)) -
        (s (i, false) - s (i, true)) * w (kToFin10 (j, b)) := by
      simp only [add_mul, Finset.sum_add_distrib, ite_mul, zero_mul,
        Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
      ring
    rw [hsum] at hne
    change (s (i, false) - s (j, b)) * w (kToFin10 (i, true)) +
      ((s (i, false) - s (i, true)) - (s (i, false) - s (j, b))) * w (kToFin10 (i, false)) -
      (s (i, false) - s (i, true)) * w (kToFin10 (j, b)) ≠ 0 at hne
    apply hne
    have hci : (f i).c - (f i).a ≠ 0 := sub_ne_zero.mpr (ne_of_gt (h_fac i))
    have hb' : ((f i).a - (dualPt f (j, b)).1) * ((f i).b - (f i).d) +
        ((f i).c - (f i).a) * (f i).b - ((f i).c - (f i).a) * (dualPt f (j, b)).2 = 0 := by
      have hmul := congrArg (fun z => ((f i).c - (f i).a) * z) heq
      dsimp [kink] at hmul
      field_simp [hci] at hmul
      linarith
    rw [← hpt_u (i, false), ← hpt_u (i, true), ← hpt_u (j, b)]
    rw [← hpt_v (i, false), ← hpt_v (i, true), ← hpt_v (j, b)]
    simp only [dualPt_false, dualPt_true] at hb' ⊢
    linarith
  have h_quad_eq : ∀ (p1 p2 p3 p4 : Fin 5 × Bool) (x : ℝ),
      p1 ≠ p2 → p3 ≠ p4 →
      (p1.1 ≠ p3.1 ∧ p1.1 ≠ p4.1 ∨ p2.1 ≠ p3.1 ∧ p2.1 ≠ p4.1 ∨
       p3.1 ≠ p1.1 ∧ p3.1 ≠ p2.1 ∨ p4.1 ≠ p1.1 ∧ p4.1 ≠ p2.1) →
      (dualPt f p1).1 * x + (dualPt f p1).2 = (dualPt f p2).1 * x + (dualPt f p2).2 →
      (dualPt f p3).1 * x + (dualPt f p3).2 = (dualPt f p4).1 * x + (dualPt f p4).2 →
      False := by
    intro p1 p2 p3 p4 x hp12 hp34 hdisj heq1 heq2
    have hq : quadGood p1 p2 p3 p4 = true := by
      simp [quadGood, hp12, hp34, hdisj]
    have hne := hw_avoid _ (planeQuad_mem s p1 p2 p3 p4 hq)
    dsimp [planeQuad] at hne
    rw [mkPlane_eval] at hne
    have hsum : (∑ k : Fin 5 × Bool,
        ((if k = p2 then s p3 - s p4 else 0) +
         (if k = p1 then -(s p3 - s p4) else 0) +
         (if k = p4 then -(s p1 - s p2) else 0) +
         (if k = p3 then s p1 - s p2 else 0)) * w (kToFin10 k)) =
        (s p3 - s p4) * (w (kToFin10 p2) - w (kToFin10 p1)) -
        (s p1 - s p2) * (w (kToFin10 p4) - w (kToFin10 p3)) := by
      simp only [add_mul, Finset.sum_add_distrib, ite_mul, zero_mul,
        Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
      ring
    rw [hsum] at hne
    change (s p3 - s p4) * (w (kToFin10 p2) - w (kToFin10 p1)) -
      (s p1 - s p2) * (w (kToFin10 p4) - w (kToFin10 p3)) ≠ 0 at hne
    apply hne
    have h1 : (s p1 - s p2) * x = w (kToFin10 p2) - w (kToFin10 p1) := by
      rw [← hpt_u p1, ← hpt_u p2, ← hpt_v p1, ← hpt_v p2]; linarith
    have h2 : (s p3 - s p4) * x = w (kToFin10 p4) - w (kToFin10 p3) := by
      rw [← hpt_u p3, ← hpt_u p4, ← hpt_v p3, ← hpt_v p4]; linarith
    calc (s p3 - s p4) * (w (kToFin10 p2) - w (kToFin10 p1)) -
         (s p1 - s p2) * (w (kToFin10 p4) - w (kToFin10 p3))
        = (s p3 - s p4) * ((s p1 - s p2) * x) - (s p1 - s p2) * ((s p3 - s p4) * x) := by rw [h1, h2]
      _ = 0 := by ring
  have h_gpb_disj : ∀ i j k l : Fin 5, i < j → k < l → (i, j) ≠ (k, l) → ∀ x : ℝ,
      ¬ ((f i).eval x = (f j).eval x ∧ (f k).eval x = (f l).eval x) := by
    intro i j k l hij hkl hne x ⟨h1, h2⟩
    obtain ⟨b1, hb1⟩ := eval_eq_branch i x
    obtain ⟨b2, hb2⟩ := eval_eq_branch j x
    obtain ⟨b3, hb3⟩ := eval_eq_branch k x
    obtain ⟨b4, hb4⟩ := eval_eq_branch l x
    have hdisj : (i ≠ k ∧ i ≠ l) ∨ (j ≠ k ∧ j ≠ l) ∨ (k ≠ i ∧ k ≠ j) ∨ (l ≠ i ∧ l ≠ j) := by
      by_contra hnot
      push Not at hnot
      have h1' : i = k ∨ i = l := by tauto
      have h2' : j = k ∨ j = l := by tauto
      rcases h1' with rfl | rfl <;> rcases h2' with rfl | rfl
      · exact lt_irrefl _ hij
      · exact hne rfl
      · exact lt_asymm hij hkl
      · exact lt_irrefl _ hij
    exact h_quad_eq (i, b1) (j, b2) (k, b3) (l, b4) x
      (fun h => (ne_of_lt hij) (congrArg Prod.fst h))
      (fun h => (ne_of_lt hkl) (congrArg Prod.fst h))
      hdisj (by linarith) (by linarith)
  have h_gpb_kink : ∀ i j m : Fin 5, i < j → (f i).eval (kink f m) ≠ (f j).eval (kink f m) := by
    intro i j m hij heq
    by_cases hmi : m = i
    · rw [hmi] at heq; exact h_gpa_vals i j (ne_of_lt hij) heq
    · by_cases hmj : m = j
      · rw [hmj] at heq; exact h_gpa_vals j i (ne_of_gt hij) heq.symm
      · obtain ⟨b1, hb1⟩ := eval_eq_branch i (kink f m)
        obtain ⟨b2, hb2⟩ := eval_eq_branch j (kink f m)
        have hkm : (dualPt f (m, false)).1 * kink f m + (dualPt f (m, false)).2 =
            (dualPt f (m, true)).1 * kink f m + (dualPt f (m, true)).2 :=
          kink_eq f m (h_fac m)
        exact h_quad_eq (i, b1) (j, b2) (m, false) (m, true) (kink f m)
          (fun h => (ne_of_lt hij) (congrArg Prod.fst h))
          (fun h => Bool.false_ne_true (congrArg Prod.snd h))
          (Or.inr (Or.inr (Or.inl ⟨hmi, hmj⟩)))
          (by linarith) hkm
  exact ⟨f, h_fac, h_mono, h_inj, h_noncol, h_dual, h_realizes, h_gpa_kinks, h_gpa_vals, h_gpb_disj, h_gpb_kink⟩

/-- Main perturbation theorem for Section 9: chains slope perturbation, `a`-sorting, and
    intercept general-position perturbation. -/
theorem exists_generic_v_system (f₀ : Fin 5 → VFunc)
    (h_all₀ : ∀ m : Fin 5 → Bool, ∃ p : ℝ × ℝ, RealizesVMask f₀ m p) :
    ∃ f : Fin 5 → VFunc,
      (∀ i : Fin 5, (f i).a < (f i).c) ∧
      StrictMono (fun i : Fin 5 => (f i).a) ∧
      Function.Injective (fun k : Fin 5 × Bool => (dualPt f k).1) ∧
      (∀ p q r : Fin 5 × Bool, p ≠ q → q ≠ r → p ≠ r →
        ((dualPt f q).1 - (dualPt f p).1) * ((dualPt f r).2 - (dualPt f p).2) -
        ((dualPt f q).2 - (dualPt f p).2) * ((dualPt f r).1 - (dualPt f p).1) ≠ 0) ∧
      (∀ S : Finset (Fin 5), ∃ s t : ℝ, DualRealizes f S s t) ∧
      (∀ m : Fin 5 → Bool, ∃ p : ℝ × ℝ, RealizesVMask f m p) ∧
      (∀ i j : Fin 5, i ≠ j → kink f i ≠ kink f j) ∧
      (∀ i j : Fin 5, i ≠ j → (f i).eval (kink f i) ≠ (f j).eval (kink f i)) ∧
      (∀ i j k l : Fin 5, i < j → k < l → (i, j) ≠ (k, l) → ∀ x : ℝ,
        ¬ ((f i).eval x = (f j).eval x ∧ (f k).eval x = (f l).eval x)) ∧
      (∀ i j m : Fin 5, i < j → (f i).eval (kink f m) ≠ (f j).eval (kink f m)) := by
  obtain ⟨f₁, hf₁_ac, hf₁_inj, h_all₁⟩ := perturb_slopes_distinct f₀ h_all₀
  obtain ⟨f₂, hf₂_ac, hf₂_mono, hf₂_inj, h_all₂⟩ := sort_vfuncs_a f₁ hf₁_ac hf₁_inj h_all₁
  exact perturb_intercepts_gp f₂ hf₂_ac hf₂_mono hf₂_inj (build_strict_dual_witnesses f₂ h_all₂)

end Sec9

end
