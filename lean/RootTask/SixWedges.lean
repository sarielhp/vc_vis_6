import Mathlib
import RootTask.Defs

open scoped Classical BigOperators
open Finset

noncomputable section

namespace SixWedges

/-! # Theorem 2.3 (`six-wedges`, Isler et al. 2004 / Gilbers & Klein Theorem 2)

Six open convex wedges in `ℝ²` cannot realize all `64` strict bitmasks.
-/

/-! ## Part 1: Basic Geometry, Lines, Rays, and General-Position Perturbation -/

def det2 (u v : ℝ × ℝ) : ℝ := u.1 * v.2 - u.2 * v.1

def dot2 (u v : ℝ × ℝ) : ℝ := u.1 * v.1 + u.2 * v.2

def normal (W : Fin 6 → OpenWedge) (a : Fin 6 × Bool) : ℝ × ℝ :=
  if a.2 then (W a.1).u₁ else (W a.1).u₂

def lineAt (W : Fin 6 → OpenWedge) (a : Fin 6 × Bool) (p : ℝ × ℝ) : ℝ :=
  (normal W a).1 * (p.1 - (W a.1).y.1) + (normal W a).2 * (p.2 - (W a.1).y.2)

def dir1 (W : OpenWedge) : ℝ × ℝ := (-W.u₁.2, W.u₁.1)

def dir2 (W : OpenWedge) : ℝ × ℝ := (W.u₂.2, -W.u₂.1)

def ray1 (W : OpenWedge) (t : ℝ) : ℝ × ℝ :=
  (W.y.1 + t * (dir1 W).1, W.y.2 + t * (dir1 W).2)

def ray2 (W : OpenWedge) (t : ℝ) : ℝ × ℝ :=
  (W.y.1 + t * (dir2 W).1, W.y.2 + t * (dir2 W).2)

def bdWedge (W : OpenWedge) : Set (ℝ × ℝ) :=
  {p | ¬ W.MemOpen p ∧ ¬ W.MemExt p}

def Realizes6 (W : Fin 6 → OpenWedge) (m : Fin 6 → Bool) (p : ℝ × ℝ) : Prop :=
  ∀ i : Fin 6, if m i then (W i).MemOpen p else (W i).MemExt p

structure GP6 (W : Fin 6 → OpenWedge) : Prop where
  no_parallel : ∀ a b : Fin 6 × Bool, a ≠ b →
    det2 (normal W a) (normal W b) ≠ 0
  apex_not_on_line : ∀ i j : Fin 6, i ≠ j → ∀ b : Bool,
    lineAt W (j, b) (W i).y ≠ 0

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

lemma bdWedge_isClosed (W : OpenWedge) : IsClosed (bdWedge W) := by
  change IsClosed ({p : ℝ × ℝ | W.MemOpen p}ᶜ ∩ {p : ℝ × ℝ | W.MemExt p}ᶜ)
  exact (isOpen_memOpen W).isClosed_compl.inter (isOpen_memExt W).isClosed_compl

lemma memOpen_memExt_disjoint (W : OpenWedge) (p : ℝ × ℝ) :
    ¬ (W.MemOpen p ∧ W.MemExt p) := by
  rintro ⟨⟨h1, h2⟩, h3 | h4⟩ <;> linarith

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

private lemma halfspace_lt_convex (u y : ℝ × ℝ) :
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

private def encVec6 (W : Fin 6 → OpenWedge) : Fin 36 → ℝ := fun k =>
  let i : Fin 6 := ⟨k.1 / 6, Nat.div_lt_of_lt_mul k.2⟩
  match k.1 % 6 with
  | 0 => (W i).y.1
  | 1 => (W i).y.2
  | 2 => (W i).u₁.1
  | 3 => (W i).u₁.2
  | 4 => (W i).u₂.1
  | _ => (W i).u₂.2

private def decWedge6 (x : Fin 36 → ℝ)
    (h_nondeg : ∀ i : Fin 6,
      0 < x ⟨6 * i.1 + 2, by omega⟩ * x ⟨6 * i.1 + 5, by omega⟩ -
          x ⟨6 * i.1 + 3, by omega⟩ * x ⟨6 * i.1 + 4, by omega⟩) :
    Fin 6 → OpenWedge := fun i =>
  { y := (x ⟨6 * i.1, by omega⟩, x ⟨6 * i.1 + 1, by omega⟩)
    u₁ := (x ⟨6 * i.1 + 2, by omega⟩, x ⟨6 * i.1 + 3, by omega⟩)
    u₂ := (x ⟨6 * i.1 + 4, by omega⟩, x ⟨6 * i.1 + 5, by omega⟩)
    h_nondeg := h_nondeg i }

private lemma encVec6_idx (W : Fin 6 → OpenWedge) (i : Fin 6) :
    encVec6 W ⟨6 * i.1, by omega⟩ = (W i).y.1 ∧
    encVec6 W ⟨6 * i.1 + 1, by omega⟩ = (W i).y.2 ∧
    encVec6 W ⟨6 * i.1 + 2, by omega⟩ = (W i).u₁.1 ∧
    encVec6 W ⟨6 * i.1 + 3, by omega⟩ = (W i).u₁.2 ∧
    encVec6 W ⟨6 * i.1 + 4, by omega⟩ = (W i).u₂.1 ∧
    encVec6 W ⟨6 * i.1 + 5, by omega⟩ = (W i).u₂.2 := by
  have hi : i.1 < 6 := i.2
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  · simp [encVec6]
    try
      have h1 : (6 * i.1 + 1) / 6 = i.1 := by omega
      have h2 : (6 * i.1 + 2) / 6 = i.1 := by omega
      have h3 : (6 * i.1 + 3) / 6 = i.1 := by omega
      have h4 : (6 * i.1 + 4) / 6 = i.1 := by omega
      have h5 : (6 * i.1 + 5) / 6 = i.1 := by omega
      simp [h1, h2, h3, h4, h5]

private def pY1 (i : Fin 6) : MvPolynomial (Fin 36) ℝ := MvPolynomial.X ⟨6 * i.1, by omega⟩
private def pY2 (i : Fin 6) : MvPolynomial (Fin 36) ℝ := MvPolynomial.X ⟨6 * i.1 + 1, by omega⟩
private def pU1 (a : Fin 6 × Bool) : MvPolynomial (Fin 36) ℝ :=
  if a.2 then MvPolynomial.X ⟨6 * a.1.1 + 2, by omega⟩ else MvPolynomial.X ⟨6 * a.1.1 + 4, by omega⟩
private def pU2 (a : Fin 6 × Bool) : MvPolynomial (Fin 36) ℝ :=
  if a.2 then MvPolynomial.X ⟨6 * a.1.1 + 3, by omega⟩ else MvPolynomial.X ⟨6 * a.1.1 + 5, by omega⟩

private def pDet2 (a b : Fin 6 × Bool) : MvPolynomial (Fin 36) ℝ :=
  pU1 a * pU2 b - pU2 a * pU1 b

private lemma eval_decWedge6 (x : Fin 36 → ℝ)
    (h_nondeg : ∀ i : Fin 6,
      0 < x ⟨6 * i.1 + 2, by omega⟩ * x ⟨6 * i.1 + 5, by omega⟩ -
          x ⟨6 * i.1 + 3, by omega⟩ * x ⟨6 * i.1 + 4, by omega⟩) :
    let W := decWedge6 x h_nondeg
    (∀ i : Fin 6,
      MvPolynomial.eval x (pY1 i) = (W i).y.1 ∧
      MvPolynomial.eval x (pY2 i) = (W i).y.2) ∧
    (∀ a : Fin 6 × Bool,
      MvPolynomial.eval x (pU1 a) = (normal W a).1 ∧
      MvPolynomial.eval x (pU2 a) = (normal W a).2) := by
  intro W
  refine ⟨fun i => by simp [W, decWedge6, pY1, pY2], fun a => ?_⟩
  rcases a with ⟨i, ⟨⟩⟩ <;> simp [W, decWedge6, normal, pU1, pU2]

lemma exists_gp6_perturbation (W : Fin 6 → OpenWedge)
    (h_all : ∀ m : Fin 6 → Bool, ∃ p : ℝ × ℝ, Realizes6 W m p) :
    ∃ W' : Fin 6 → OpenWedge, GP6 W' ∧ ∀ m : Fin 6 → Bool, ∃ p : ℝ × ℝ, Realizes6 W' m p := by
  choose zm hzm using h_all
  let x₀ := encVec6 W
  let cond : (Fin 36 → ℝ) → Prop := fun x =>
    (∀ i : Fin 6,
      0 < x ⟨6 * i.1 + 2, by omega⟩ * x ⟨6 * i.1 + 5, by omega⟩ -
          x ⟨6 * i.1 + 3, by omega⟩ * x ⟨6 * i.1 + 4, by omega⟩) ∧
    (∀ (m : Fin 6 → Bool) (i : Fin 6),
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
  have hopen : IsOpen {x : Fin 36 → ℝ | cond x} := by
    dsimp only [cond]
    rw [Set.setOf_and]
    refine IsOpen.inter ?_ ?_
    · rw [Set.setOf_forall]
      refine isOpen_iInter_of_finite fun i => isOpen_lt continuous_const (by fun_prop)
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
    refine ⟨fun i => ?_, fun m i => ?_⟩
    · rcases encVec6_idx W i with ⟨_, _, e2, e3, e4, e5⟩
      dsimp [x₀]; rw [e2, e3, e4, e5]; exact (W i).h_nondeg
    · rcases encVec6_idx W i with ⟨e0, e1, e2, e3, e4, e5⟩
      dsimp [x₀]; rw [e0, e1, e2, e3, e4, e5]; exact hzm m i
  obtain ⟨δ, hδ_pos, hball⟩ := Metric.isOpen_iff.mp hopen x₀ hx₀_cond
  let P2 : {p : (Fin 6 × Bool) × (Fin 6 × Bool) // p.1 ≠ p.2} → MvPolynomial (Fin 36) ℝ :=
    fun ⟨⟨a, b⟩, _⟩ => pDet2 a b
  have hP2 : ∀ q, P2 q ≠ 0 := by
    rintro ⟨⟨a, b⟩, hab⟩ h0
    by_cases hij : a.1 = b.1
    · let w : Fin 36 → ℝ := fun k =>
        if k.1 = 6 * a.1.1 + 2 then 1
        else if k.1 = 6 * a.1.1 + 3 then 2
        else if k.1 = 6 * a.1.1 + 4 then 3
        else if k.1 = 6 * a.1.1 + 5 then 1
        else 0
      have hne_b : a.2 ≠ b.2 := fun hb => hab (Prod.ext hij hb)
      have hev : MvPolynomial.eval w (P2 ⟨(a, b), hab⟩) ≠ 0 := by
        rcases a with ⟨i, ⟨⟩⟩ <;> rcases b with ⟨j, ⟨⟩⟩ <;> simp at hij hne_b ⊢
        · subst hij; simp [P2, pDet2, pU1, pU2, w]; norm_num
        · subst hij; simp [P2, pDet2, pU1, pU2, w]; norm_num
      have hzero : MvPolynomial.eval w (P2 ⟨(a, b), hab⟩) = 0 := by rw [h0, map_zero]
      exact hev hzero
    · let w : Fin 36 → ℝ := fun k =>
        if k.1 / 6 = a.1.1 then
          if k.1 % 6 = 2 ∨ k.1 % 6 = 4 then 1 else 2
        else if k.1 / 6 = b.1.1 then
          if k.1 % 6 = 3 ∨ k.1 % 6 = 5 then 1 else 3
        else 0
      have ha1 : a.1.1 ≠ b.1.1 := fun h => hij (Fin.ext h)
      have ha_idx : ∀ m < 6, (6 * a.1.1 + m) / 6 = a.1.1 ∧ (6 * a.1.1 + m) % 6 = m := by
        intro m hm; omega
      have hb_idx : ∀ m < 6, (6 * b.1.1 + m) / 6 = b.1.1 ∧ (6 * b.1.1 + m) % 6 = m := by
        intro m hm; omega
      have hev : MvPolynomial.eval w (P2 ⟨(a, b), hab⟩) ≠ 0 := by
        rcases a with ⟨ia, ba⟩; rcases b with ⟨ib, bb⟩
        dsimp at ha1
        rcases ba with ⟨⟩ <;> rcases bb with ⟨⟩ <;>
          (simp [P2, pDet2, pU1, pU2, w, ha_idx, hb_idx, Ne.symm ha1]; norm_num)
      have hzero : MvPolynomial.eval w (P2 ⟨(a, b), hab⟩) = 0 := by rw [h0, map_zero]
      exact hev hzero
  let P4 : {p : Fin 6 × (Fin 6 × Bool) // p.1 ≠ p.2.1} → MvPolynomial (Fin 36) ℝ :=
    fun ⟨⟨i, b⟩, _⟩ => pU1 b * (pY1 i - pY1 b.1) + pU2 b * (pY2 i - pY2 b.1)
  have hP4 : ∀ t, P4 t ≠ 0 := by
    rintro ⟨⟨i, b⟩, hib⟩ h0
    let w : Fin 36 → ℝ := fun k =>
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
        simp [P4, pU1, pU2, pY1, pY2, w, hne, Ne.symm hne, hi0, hb0, hi1, hb1, hb2, hb3, hb4, hb5]
    have hzero : MvPolynomial.eval w (P4 ⟨(i, b), hib⟩) = 0 := by rw [h0, map_zero]
    linarith
  let P_all : MvPolynomial (Fin 36) ℝ := (∏ q, P2 q) * (∏ s, P4 s)
  have hP_all : P_all ≠ 0 := by
    refine mul_ne_zero ?_ ?_
    · exact Finset.prod_ne_zero_iff.mpr fun q _ => hP2 q
    · exact Finset.prod_ne_zero_iff.mpr fun s _ => hP4 s
  obtain ⟨x, hx_box, hx_poly⟩ :=
    poly_dense_box 36 (fun k => x₀ k - δ / 2) (fun k => x₀ k + δ / 2)
      (fun k => by linarith) P_all hP_all
  have hx_dist : dist x x₀ < δ := by
    rw [dist_pi_lt_iff hδ_pos]
    intro k
    have hk := hx_box k
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith [hk.1, hk.2]
  have hx_cond : cond x := hball hx_dist
  let W' := decWedge6 x hx_cond.1
  have hW'_eval := eval_decWedge6 x hx_cond.1
  have hx_prod : MvPolynomial.eval x (∏ q, P2 q) ≠ 0 ∧ MvPolynomial.eval x (∏ s, P4 s) ≠ 0 := by
    dsimp only [P_all] at hx_poly
    rw [map_mul] at hx_poly
    exact ⟨left_ne_zero_of_mul hx_poly, right_ne_zero_of_mul hx_poly⟩
  have hP2_ne : ∀ q, MvPolynomial.eval x (P2 q) ≠ 0 := fun q h0 => by
    apply hx_prod.1; rw [map_prod]; exact Finset.prod_eq_zero (Finset.mem_univ q) h0
  have hP4_ne : ∀ s, MvPolynomial.eval x (P4 s) ≠ 0 := fun s h0 => by
    apply hx_prod.2; rw [map_prod]; exact Finset.prod_eq_zero (Finset.mem_univ s) h0
  refine ⟨W', ⟨?_, ?_⟩, fun m => ⟨zm m, hx_cond.2 m⟩⟩
  · intro a b hab
    have hp2 := hP2_ne ⟨(a, b), hab⟩
    rcases hW'_eval.2 a with ⟨ea1, ea2⟩
    rcases hW'_eval.2 b with ⟨eb1, eb2⟩
    simp only [P2, pDet2, map_sub, map_mul, ea1, ea2, eb1, eb2] at hp2
    exact hp2
  · intro i j hij b
    have hp4 := hP4_ne ⟨(i, (j, b)), hij⟩
    rcases hW'_eval.1 i with ⟨yi1, yi2⟩
    rcases hW'_eval.1 j with ⟨yj1, yj2⟩
    rcases hW'_eval.2 (j, b) with ⟨ub1, ub2⟩
    simp only [P4, map_add, map_sub, map_mul, yi1, yi2, yj1, yj2, ub1, ub2] at hp4
    exact hp4

/-! ## Part 2: `ℝ²` Wedge Arrangement Face Bound (`arr_comps_bound_univ`) -/

lemma bdWedge_iff_closure_eq_zero (W : OpenWedge) (p : ℝ × ℝ) :
    p ∈ bdWedge W ↔
      (0 ≤ W.u₁.1 * (p.1 - W.y.1) + W.u₁.2 * (p.2 - W.y.2) ∧
       0 ≤ W.u₂.1 * (p.1 - W.y.1) + W.u₂.2 * (p.2 - W.y.2)) ∧
      (W.u₁.1 * (p.1 - W.y.1) + W.u₁.2 * (p.2 - W.y.2) = 0 ∨
       W.u₂.1 * (p.1 - W.y.1) + W.u₂.2 * (p.2 - W.y.2) = 0) := by
  constructor
  · rintro ⟨hno, hne⟩
    dsimp [OpenWedge.MemOpen, OpenWedge.MemExt] at hno hne
    push Not at hne
    refine ⟨hne, ?_⟩
    by_contra hboth
    push Not at hboth
    exact hno ⟨lt_of_le_of_ne hne.1 hboth.1.symm, lt_of_le_of_ne hne.2 hboth.2.symm⟩
  · rintro ⟨⟨h1, h2⟩, h1z | h2z⟩
    · refine ⟨fun ⟨ho1, _⟩ => by linarith, ?_⟩
      rintro (he1 | he2) <;> linarith
    · refine ⟨fun ⟨_, ho2⟩ => by linarith, ?_⟩
      rintro (he1 | he2) <;> linarith

lemma dir1_ne_zero (W : OpenWedge) : dir1 W ≠ (0, 0) := by
  intro h
  have h1 : -W.u₁.2 = 0 := congrArg Prod.fst h
  have h2 : W.u₁.1 = 0 := congrArg Prod.snd h
  have hnd := W.h_nondeg
  have h1' : W.u₁.2 = 0 := by linarith
  rw [h1', h2] at hnd
  linarith

lemma dir2_ne_zero (W : OpenWedge) : dir2 W ≠ (0, 0) := by
  intro h
  have h1 : W.u₂.2 = 0 := congrArg Prod.fst h
  have h2 : -W.u₂.1 = 0 := congrArg Prod.snd h
  have hnd := W.h_nondeg
  have h2' : W.u₂.1 = 0 := by linarith
  rw [h1, h2'] at hnd
  linarith

lemma ray1_injective (W : OpenWedge) : Function.Injective (ray1 W) := by
  intro t₁ t₂ heq
  have hne := dir1_ne_zero W
  have hfx : t₁ * (dir1 W).1 = t₂ * (dir1 W).1 := by
    have := congrArg Prod.fst heq; dsimp [ray1] at this; linarith
  have hfy : t₁ * (dir1 W).2 = t₂ * (dir1 W).2 := by
    have := congrArg Prod.snd heq; dsimp [ray1] at this; linarith
  by_cases hx : (dir1 W).1 = 0
  · have hy : (dir1 W).2 ≠ 0 := fun hy => hne (Prod.ext hx hy)
    exact mul_right_cancel₀ hy hfy
  · exact mul_right_cancel₀ hx hfx

lemma ray2_injective (W : OpenWedge) : Function.Injective (ray2 W) := by
  intro t₁ t₂ heq
  have hne := dir2_ne_zero W
  have hfx : t₁ * (dir2 W).1 = t₂ * (dir2 W).1 := by
    have := congrArg Prod.fst heq; dsimp [ray2] at this; linarith
  have hfy : t₁ * (dir2 W).2 = t₂ * (dir2 W).2 := by
    have := congrArg Prod.snd heq; dsimp [ray2] at this; linarith
  by_cases hx : (dir2 W).1 = 0
  · have hy : (dir2 W).2 ≠ 0 := fun hy => hne (Prod.ext hx hy)
    exact mul_right_cancel₀ hy hfy
  · exact mul_right_cancel₀ hx hfx

lemma ray1_isClosedEmbedding (W : OpenWedge) : Topology.IsClosedEmbedding (ray1 W) := by
  have hne := dir1_ne_zero W
  let inv : ℝ × ℝ → ℝ := fun p =>
    if (dir1 W).1 ≠ 0 then (p.1 - W.y.1) / (dir1 W).1 else (p.2 - W.y.2) / (dir1 W).2
  have hcont_ray : Continuous (ray1 W) := by unfold ray1; fun_prop
  have hcont_inv : Continuous inv := by
    unfold inv; split_ifs <;> fun_prop
  have hleft : Function.LeftInverse inv (ray1 W) := by
    intro t
    dsimp [inv, ray1]
    by_cases hx : (dir1 W).1 = 0
    · rw [if_neg (not_not.mpr hx)]
      have hy : (dir1 W).2 ≠ 0 := fun hy => hne (Prod.ext hx hy)
      field_simp [hy]; ring
    · rw [if_pos hx]
      field_simp [hx]; ring
  have hclosed_range : IsClosed (Set.range (ray1 W)) := by
    rw [show Set.range (ray1 W) = {p : ℝ × ℝ | ray1 W (inv p) = p} from by
      ext p; constructor
      · rintro ⟨t, rfl⟩; change ray1 W (inv (ray1 W t)) = ray1 W t; rw [hleft t]
      · intro hp; exact ⟨inv p, hp⟩]
    exact isClosed_eq (hcont_ray.comp hcont_inv) continuous_id
  exact Topology.IsClosedEmbedding.of_continuous_injective_isClosedMap hcont_ray (ray1_injective W)
    (fun s hs => by
      have himg : ray1 W '' s = Set.range (ray1 W) ∩ inv ⁻¹' s := by
        ext p; constructor
        · rintro ⟨t, ht, rfl⟩; exact ⟨⟨t, rfl⟩, by simpa [hleft t] using ht⟩
        · rintro ⟨⟨t, rfl⟩, ht⟩; exact ⟨t, by simpa [hleft t] using ht, rfl⟩
      rw [himg]
      exact hclosed_range.inter (hs.preimage hcont_inv))

lemma ray2_isClosedEmbedding (W : OpenWedge) : Topology.IsClosedEmbedding (ray2 W) := by
  have hne := dir2_ne_zero W
  let inv : ℝ × ℝ → ℝ := fun p =>
    if (dir2 W).1 ≠ 0 then (p.1 - W.y.1) / (dir2 W).1 else (p.2 - W.y.2) / (dir2 W).2
  have hcont_ray : Continuous (ray2 W) := by unfold ray2; fun_prop
  have hcont_inv : Continuous inv := by
    unfold inv; split_ifs <;> fun_prop
  have hleft : Function.LeftInverse inv (ray2 W) := by
    intro t
    dsimp [inv, ray2]
    by_cases hx : (dir2 W).1 = 0
    · rw [if_neg (not_not.mpr hx)]
      have hy : (dir2 W).2 ≠ 0 := fun hy => hne (Prod.ext hx hy)
      field_simp [hy]; ring
    · rw [if_pos hx]
      field_simp [hx]; ring
  have hclosed_range : IsClosed (Set.range (ray2 W)) := by
    rw [show Set.range (ray2 W) = {p : ℝ × ℝ | ray2 W (inv p) = p} from by
      ext p; constructor
      · rintro ⟨t, rfl⟩; change ray2 W (inv (ray2 W t)) = ray2 W t; rw [hleft t]
      · intro hp; exact ⟨inv p, hp⟩]
    exact isClosed_eq (hcont_ray.comp hcont_inv) continuous_id
  exact Topology.IsClosedEmbedding.of_continuous_injective_isClosedMap hcont_ray (ray2_injective W)
    (fun s hs => by
      have himg : ray2 W '' s = Set.range (ray2 W) ∩ inv ⁻¹' s := by
        ext p; constructor
        · rintro ⟨t, ht, rfl⟩; exact ⟨⟨t, rfl⟩, by simpa [hleft t] using ht⟩
        · rintro ⟨⟨t, rfl⟩, ht⟩; exact ⟨t, by simpa [hleft t] using ht, rfl⟩
      rw [himg]
      exact hclosed_range.inter (hs.preimage hcont_inv))

lemma ray1_mem_bdWedge (W : OpenWedge) {t : ℝ} (ht : 0 ≤ t) : ray1 W t ∈ bdWedge W := by
  have hnd := W.h_nondeg
  have hl1 : W.u₁.1 * ((ray1 W t).1 - W.y.1) + W.u₁.2 * ((ray1 W t).2 - W.y.2) = 0 := by
    dsimp [ray1, dir1]; ring
  have hl2 : W.u₂.1 * ((ray1 W t).1 - W.y.1) + W.u₂.2 * ((ray1 W t).2 - W.y.2) =
      t * (W.u₁.1 * W.u₂.2 - W.u₁.2 * W.u₂.1) := by
    dsimp [ray1, dir1]; ring
  have hnn : 0 ≤ t * (W.u₁.1 * W.u₂.2 - W.u₁.2 * W.u₂.1) := mul_nonneg ht (le_of_lt hnd)
  refine ⟨?_, ?_⟩
  · rintro ⟨h1, _⟩; linarith
  · rintro (h1 | h2) <;> linarith

lemma ray2_mem_bdWedge (W : OpenWedge) {t : ℝ} (ht : 0 ≤ t) : ray2 W t ∈ bdWedge W := by
  have hnd := W.h_nondeg
  have hl1 : W.u₁.1 * ((ray2 W t).1 - W.y.1) + W.u₁.2 * ((ray2 W t).2 - W.y.2) =
      t * (W.u₁.1 * W.u₂.2 - W.u₁.2 * W.u₂.1) := by
    dsimp [ray2, dir2]; ring
  have hl2 : W.u₂.1 * ((ray2 W t).1 - W.y.1) + W.u₂.2 * ((ray2 W t).2 - W.y.2) = 0 := by
    dsimp [ray2, dir2]; ring
  have hnn : 0 ≤ t * (W.u₁.1 * W.u₂.2 - W.u₁.2 * W.u₂.1) := mul_nonneg ht (le_of_lt hnd)
  refine ⟨?_, ?_⟩
  · rintro ⟨_, h2⟩; linarith
  · rintro (h1 | h2) <;> linarith

lemma bdWedge_iff_rays (W : OpenWedge) (p : ℝ × ℝ) :
    p ∈ bdWedge W ↔ (∃ t ≥ 0, p = ray1 W t) ∨ (∃ t ≥ 0, p = ray2 W t) := by
  constructor
  · rintro ⟨hno, hne⟩
    dsimp [OpenWedge.MemOpen, OpenWedge.MemExt] at hno hne
    push Not at hne
    have h1_nn : 0 ≤ W.u₁.1 * (p.1 - W.y.1) + W.u₁.2 * (p.2 - W.y.2) := hne.1
    have h2_nn : 0 ≤ W.u₂.1 * (p.1 - W.y.1) + W.u₂.2 * (p.2 - W.y.2) := hne.2
    have hnd := W.h_nondeg
    have hnd_ne : W.u₁.1 * W.u₂.2 - W.u₁.2 * W.u₂.1 ≠ 0 := ne_of_gt hnd
    have h_or : W.u₁.1 * (p.1 - W.y.1) + W.u₁.2 * (p.2 - W.y.2) = 0 ∨
        W.u₂.1 * (p.1 - W.y.1) + W.u₂.2 * (p.2 - W.y.2) = 0 := by
      by_contra hboth
      push Not at hboth
      exact hno ⟨lt_of_le_of_ne h1_nn hboth.1.symm, lt_of_le_of_ne h2_nn hboth.2.symm⟩
    rcases h_or with h1z | h2z
    · left
      let t := (W.u₂.1 * (p.1 - W.y.1) + W.u₂.2 * (p.2 - W.y.2)) /
        (W.u₁.1 * W.u₂.2 - W.u₁.2 * W.u₂.1)
      refine ⟨t, div_nonneg h2_nn (le_of_lt hnd), ?_⟩
      ext
      · dsimp [ray1, dir1, t]
        have hx : (p.1 - W.y.1) * (W.u₁.1 * W.u₂.2 - W.u₁.2 * W.u₂.1) =
            (W.u₂.1 * (p.1 - W.y.1) + W.u₂.2 * (p.2 - W.y.2)) * (-W.u₁.2) := by
          linear_combination W.u₂.2 * h1z
        calc p.1 = W.y.1 + (p.1 - W.y.1) := by ring
          _ = W.y.1 + ((p.1 - W.y.1) * (W.u₁.1 * W.u₂.2 - W.u₁.2 * W.u₂.1)) /
                (W.u₁.1 * W.u₂.2 - W.u₁.2 * W.u₂.1) := by rw [mul_div_cancel_right₀ _ hnd_ne]
          _ = W.y.1 + (W.u₂.1 * (p.1 - W.y.1) + W.u₂.2 * (p.2 - W.y.2)) /
                (W.u₁.1 * W.u₂.2 - W.u₁.2 * W.u₂.1) * -W.u₁.2 := by rw [hx]; ring
      · dsimp [ray1, dir1, t]
        have hy : (p.2 - W.y.2) * (W.u₁.1 * W.u₂.2 - W.u₁.2 * W.u₂.1) =
            (W.u₂.1 * (p.1 - W.y.1) + W.u₂.2 * (p.2 - W.y.2)) * W.u₁.1 := by
          linear_combination -W.u₂.1 * h1z
        calc p.2 = W.y.2 + (p.2 - W.y.2) := by ring
          _ = W.y.2 + ((p.2 - W.y.2) * (W.u₁.1 * W.u₂.2 - W.u₁.2 * W.u₂.1)) /
                (W.u₁.1 * W.u₂.2 - W.u₁.2 * W.u₂.1) := by rw [mul_div_cancel_right₀ _ hnd_ne]
          _ = W.y.2 + (W.u₂.1 * (p.1 - W.y.1) + W.u₂.2 * (p.2 - W.y.2)) /
                (W.u₁.1 * W.u₂.2 - W.u₁.2 * W.u₂.1) * W.u₁.1 := by rw [hy]; ring
    · right
      let t := (W.u₁.1 * (p.1 - W.y.1) + W.u₁.2 * (p.2 - W.y.2)) /
        (W.u₁.1 * W.u₂.2 - W.u₁.2 * W.u₂.1)
      refine ⟨t, div_nonneg h1_nn (le_of_lt hnd), ?_⟩
      ext
      · dsimp [ray2, dir2, t]
        have hx : (p.1 - W.y.1) * (W.u₁.1 * W.u₂.2 - W.u₁.2 * W.u₂.1) =
            (W.u₁.1 * (p.1 - W.y.1) + W.u₁.2 * (p.2 - W.y.2)) * W.u₂.2 := by
          linear_combination -W.u₁.2 * h2z
        calc p.1 = W.y.1 + (p.1 - W.y.1) := by ring
          _ = W.y.1 + ((p.1 - W.y.1) * (W.u₁.1 * W.u₂.2 - W.u₁.2 * W.u₂.1)) /
                (W.u₁.1 * W.u₂.2 - W.u₁.2 * W.u₂.1) := by rw [mul_div_cancel_right₀ _ hnd_ne]
          _ = W.y.1 + (W.u₁.1 * (p.1 - W.y.1) + W.u₁.2 * (p.2 - W.y.2)) /
                (W.u₁.1 * W.u₂.2 - W.u₁.2 * W.u₂.1) * W.u₂.2 := by rw [hx]; ring
      · dsimp [ray2, dir2, t]
        have hy : (p.2 - W.y.2) * (W.u₁.1 * W.u₂.2 - W.u₁.2 * W.u₂.1) =
            (W.u₁.1 * (p.1 - W.y.1) + W.u₁.2 * (p.2 - W.y.2)) * (-W.u₂.1) := by
          linear_combination W.u₁.1 * h2z
        calc p.2 = W.y.2 + (p.2 - W.y.2) := by ring
          _ = W.y.2 + ((p.2 - W.y.2) * (W.u₁.1 * W.u₂.2 - W.u₁.2 * W.u₂.1)) /
                (W.u₁.1 * W.u₂.2 - W.u₁.2 * W.u₂.1) := by rw [mul_div_cancel_right₀ _ hnd_ne]
          _ = W.y.2 + (W.u₁.1 * (p.1 - W.y.1) + W.u₁.2 * (p.2 - W.y.2)) /
                (W.u₁.1 * W.u₂.2 - W.u₁.2 * W.u₂.1) * -W.u₂.1 := by rw [hy]; ring
  · rintro (⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩)
    · exact ray1_mem_bdWedge W ht
    · exact ray2_mem_bdWedge W ht

lemma ray1_eq_ray2 (W : OpenWedge) {t₁ t₂ : ℝ} (heq : ray1 W t₁ = ray2 W t₂) :
    t₁ = 0 ∧ t₂ = 0 := by
  have hnd := ne_of_gt W.h_nondeg
  have hx : t₁ * (-W.u₁.2) = t₂ * W.u₂.2 := by
    have := congrArg Prod.fst heq; dsimp [ray1, ray2, dir1, dir2] at this; linarith
  have hy : t₁ * W.u₁.1 = t₂ * (-W.u₂.1) := by
    have := congrArg Prod.snd heq; dsimp [ray1, ray2, dir1, dir2] at this; linarith
  have h1 : t₁ * (W.u₁.1 * W.u₂.2 - W.u₁.2 * W.u₂.1) = 0 := by
    calc t₁ * (W.u₁.1 * W.u₂.2 - W.u₁.2 * W.u₂.1)
        = (t₁ * W.u₁.1) * W.u₂.2 + (t₁ * (-W.u₁.2)) * W.u₂.1 := by ring
      _ = (t₂ * (-W.u₂.1)) * W.u₂.2 + (t₂ * W.u₂.2) * W.u₂.1 := by rw [hx, hy]
      _ = 0 := by ring
  have h2 : t₂ * (W.u₁.1 * W.u₂.2 - W.u₁.2 * W.u₂.1) = 0 := by
    calc t₂ * (W.u₁.1 * W.u₂.2 - W.u₁.2 * W.u₂.1)
        = W.u₁.1 * (t₂ * W.u₂.2) + W.u₁.2 * (t₂ * (-W.u₂.1)) := by ring
      _ = W.u₁.1 * (t₁ * (-W.u₁.2)) + W.u₁.2 * (t₁ * W.u₁.1) := by rw [← hx, ← hy]
      _ = 0 := by ring
  exact ⟨(mul_eq_zero.mp h1).resolve_right hnd, (mul_eq_zero.mp h2).resolve_right hnd⟩

def gammaParam (W : OpenWedge) (s : ℝ) : ℝ × ℝ :=
  if s ≤ 0 then ray1 W (-s) else ray2 W s

lemma gammaParam_zero (W : OpenWedge) : gammaParam W 0 = W.y := by
  simp [gammaParam, ray1]

lemma gammaParam_continuous (W : OpenWedge) : Continuous (gammaParam W) := by
  let f1 : ℝ → ℝ × ℝ := fun s => ray1 W (-s)
  let f2 : ℝ → ℝ × ℝ := fun s => ray2 W s
  have hf1 : Continuous f1 := (by unfold ray1; fun_prop : Continuous (ray1 W)).comp continuous_neg
  have hf2 : Continuous f2 := by dsimp [f2]; unfold ray2; fun_prop
  rw [← continuousOn_univ, show (Set.univ : Set ℝ) = Set.Iic 0 ∪ Set.Ici 0 from
    (Set.Iic_union_Ici).symm]
  refine ContinuousOn.union_of_isClosed ?_ ?_ isClosed_Iic isClosed_Ici
  · exact hf1.continuousOn.congr fun s hs => by simp [gammaParam, Set.mem_Iic.mp hs, f1]
  · exact hf2.continuousOn.congr fun s hs => by
      by_cases hs0 : s ≤ 0
      · have hs' : s = 0 := le_antisymm hs0 hs
        subst hs'
        simp [gammaParam, ray1, ray2, f2]
      · simp [gammaParam, hs0, f2]

lemma gammaParam_injective (W : OpenWedge) : Function.Injective (gammaParam W) := by
  intro a b hab
  unfold gammaParam at hab
  split_ifs at hab with ha hb hb
  · have := ray1_injective W hab; linarith
  · obtain ⟨h1, h2⟩ := ray1_eq_ray2 W hab; linarith
  · obtain ⟨h1, h2⟩ := ray1_eq_ray2 W hab.symm; linarith
  · exact ray2_injective W hab

lemma gammaParam_mem_bdWedge (W : OpenWedge) (s : ℝ) : gammaParam W s ∈ bdWedge W := by
  unfold gammaParam
  split_ifs with hs
  · exact ray1_mem_bdWedge W (by linarith)
  · exact ray2_mem_bdWedge W (by linarith)

lemma gammaParam_range (W : OpenWedge) : Set.range (gammaParam W) = bdWedge W := by
  ext p; constructor
  · rintro ⟨s, rfl⟩; exact gammaParam_mem_bdWedge W s
  · intro hp
    rcases (bdWedge_iff_rays W p).mp hp with ⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩
    · exact ⟨-t, by simp [gammaParam, ht]⟩
    · by_cases ht0 : t = 0
      · subst ht0; exact ⟨0, by simp [gammaParam, ray1, ray2]⟩
      · exact ⟨t, by simp [gammaParam, not_le.mpr (lt_of_le_of_ne ht (Ne.symm ht0))]⟩

lemma gammaParam_image_isClosed (W : OpenWedge) {S : Set ℝ} (hS : IsClosed S) :
    IsClosed (gammaParam W '' S) := by
  have himg : gammaParam W '' S =
      ray1 W '' ((- ·) '' (S ∩ Set.Iic 0)) ∪ ray2 W '' (S ∩ Set.Ici 0) := by
    ext p; constructor
    · rintro ⟨s, hs, rfl⟩
      unfold gammaParam
      split_ifs with hs0
      · left; exact ⟨-s, ⟨s, ⟨hs, hs0⟩, rfl⟩, rfl⟩
      · right; exact ⟨s, ⟨hs, le_of_not_ge hs0⟩, rfl⟩
    · rintro (⟨t, ⟨s, ⟨hs, hs0⟩, rfl⟩, rfl⟩ | ⟨s, ⟨hs, hs0⟩, rfl⟩)
      · exact ⟨s, hs, by simp [gammaParam, Set.mem_Iic.mp hs0]⟩
      · by_cases hsz : s = 0
        · subst hsz; exact ⟨0, hs, by simp [gammaParam, ray1, ray2]⟩
        · exact ⟨s, hs, by simp [gammaParam, not_le.mpr (lt_of_le_of_ne hs0 (Ne.symm hsz))]⟩
  rw [himg]
  have h1 : IsClosed ((- ·) '' (S ∩ Set.Iic 0)) :=
    (Homeomorph.neg ℝ).isClosed_image.mpr (hS.inter isClosed_Iic)
  have h2 : IsClosed (S ∩ Set.Ici 0) := hS.inter isClosed_Ici
  exact ((ray1_isClosedEmbedding W).isClosedMap _ h1).union
        ((ray2_isClosedEmbedding W).isClosedMap _ h2)

def Comps (U : Set (ℝ × ℝ)) : Set (Set (ℝ × ℝ)) :=
  {C | ∃ x ∈ U, C = connectedComponentIn U x}

lemma comps_univ_card : (Comps (Set.univ : Set (ℝ × ℝ))).encard = 1 := by
  have heq : Comps (Set.univ : Set (ℝ × ℝ)) = {Set.univ} := by
    ext C; constructor
    · rintro ⟨x, hx, rfl⟩
      exact isPreconnected_univ.connectedComponentIn hx
    · intro hC
      rw [Set.mem_singleton_iff.mp hC]
      exact ⟨(0, 0), trivial, (isPreconnected_univ.connectedComponentIn trivial).symm⟩
  rw [heq, Set.encard_singleton]

private lemma union_balls_preconnected
    {α : Set (ℝ × ℝ)} (hα_conn : IsPreconnected α)
    (r : ℝ × ℝ → ℝ) (B : (ℝ × ℝ) → Set (ℝ × ℝ))
    (hr_pos : ∀ z ∈ α, 0 < r z)
    (hB_conn : ∀ z ∈ α, IsPreconnected (B z))
    (hB_ov : ∀ z ∈ α, ∀ z' ∈ α, z' ∈ Metric.ball z (r z) → (B z ∩ B z').Nonempty) :
    IsPreconnected (⋃ z ∈ α, B z) := by
  intro S T hS hT hsub hS_ne hT_ne
  by_contra hnot_inter
  rw [Set.not_nonempty_iff_eq_empty] at hnot_inter
  have hB_choice : ∀ z ∈ α, B z ⊆ S ∨ B z ⊆ T := by
    intro z hz
    have hBz_sub : B z ⊆ S ∪ T := (Set.subset_biUnion_of_mem (u := fun z => B z) hz).trans hsub
    by_cases hBS : B z ⊆ S
    · exact Or.inl hBS
    · right
      by_contra hBT
      obtain ⟨pT, hpT_B, hpT_S⟩ := Set.not_subset.mp hBS
      have hpT_T : pT ∈ T := (hBz_sub hpT_B).resolve_left hpT_S
      obtain ⟨pS, hpS_B, hpS_T⟩ := Set.not_subset.mp hBT
      have hpS_S : pS ∈ S := (hBz_sub hpS_B).resolve_right hpS_T
      obtain ⟨w, hwB, hwS, hwT⟩ := hB_conn z hz S T hS hT hBz_sub ⟨pS, hpS_B, hpS_S⟩ ⟨pT, hpT_B, hpT_T⟩
      have hwU : w ∈ ⋃ z' ∈ α, B z' := Set.mem_biUnion hz hwB
      exact (Set.eq_empty_iff_forall_notMem.mp hnot_inter w) ⟨hwU, hwS, hwT⟩
  let αS : Set (ℝ × ℝ) := {z ∈ α | B z ⊆ S}
  let αT : Set (ℝ × ℝ) := {z ∈ α | B z ⊆ T}
  let OS : Set (ℝ × ℝ) := ⋃ z ∈ αS, Metric.ball z (r z)
  let OT : Set (ℝ × ℝ) := ⋃ z ∈ αT, Metric.ball z (r z)
  have hOS : IsOpen OS := isOpen_biUnion fun z _ => Metric.isOpen_ball
  have hOT : IsOpen OT := isOpen_biUnion fun z _ => Metric.isOpen_ball
  have hα_sub : α ⊆ OS ∪ OT := by
    intro z hz
    rcases hB_choice z hz with hBS | hBT
    · left; exact Set.mem_biUnion ⟨hz, hBS⟩ (Metric.mem_ball_self (hr_pos z hz))
    · right; exact Set.mem_biUnion ⟨hz, hBT⟩ (Metric.mem_ball_self (hr_pos z hz))
  have hα_S_ne : (α ∩ OS).Nonempty := by
    obtain ⟨w, hwU, hwS⟩ := hS_ne
    rw [Set.mem_iUnion₂] at hwU
    rcases hwU with ⟨z, hz, hwB⟩
    rcases hB_choice z hz with hBS | hBT
    · exact ⟨z, hz, Set.mem_biUnion ⟨hz, hBS⟩ (Metric.mem_ball_self (hr_pos z hz))⟩
    · exact False.elim ((Set.eq_empty_iff_forall_notMem.mp hnot_inter w)
        ⟨Set.mem_biUnion hz hwB, hwS, hBT hwB⟩)
  have hα_T_ne : (α ∩ OT).Nonempty := by
    obtain ⟨w, hwU, hwT⟩ := hT_ne
    rw [Set.mem_iUnion₂] at hwU
    rcases hwU with ⟨z, hz, hwB⟩
    rcases hB_choice z hz with hBS | hBT
    · exact False.elim ((Set.eq_empty_iff_forall_notMem.mp hnot_inter w)
        ⟨Set.mem_biUnion hz hwB, hBS hwB, hwT⟩)
    · exact ⟨z, hz, Set.mem_biUnion ⟨hz, hBT⟩ (Metric.mem_ball_self (hr_pos z hz))⟩
  obtain ⟨w, hw, hwS, hwT⟩ := hα_conn OS OT hOS hOT hα_sub hα_S_ne hα_T_ne
  rw [Set.mem_iUnion₂] at hwS hwT
  rcases hwS with ⟨zS, ⟨hzS, hBS⟩, hwbS⟩
  rcases hwT with ⟨zT, ⟨hzT, hBT⟩, hwbT⟩
  obtain ⟨pS, hpS1, hpS2⟩ := hB_ov zS hzS w hw hwbS
  obtain ⟨pT, hpT1, hpT2⟩ := hB_ov zT hzT w hw hwbT
  rcases hB_choice w hw with hwS' | hwT'
  · exact (Set.eq_empty_iff_forall_notMem.mp hnot_inter pT)
      ⟨Set.mem_biUnion hzT hpT1, hwS' hpT2, hBT hpT1⟩
  · exact (Set.eq_empty_iff_forall_notMem.mp hnot_inter pS)
      ⟨Set.mem_biUnion hzS hpS1, hBS hpS1, hwT' hpS2⟩

lemma comps_remove_arc
    {U α : Set (ℝ × ℝ)} (_hU : IsOpen U) (hα_sub : α ⊆ U)
    (hα_ne : α.Nonempty) (hα_conn : IsPreconnected α) (hUα_open : IsOpen (U \ α))
    (r : ℝ × ℝ → ℝ) (BL BR : (ℝ × ℝ) → Set (ℝ × ℝ))
    (hr_pos : ∀ z ∈ α, 0 < r z)
    (hball_sub : ∀ z ∈ α, Metric.ball z (r z) ⊆ U)
    (hball_split : ∀ z ∈ α, Metric.ball z (r z) \ α = BL z ∪ BR z)
    (hBL_ne : ∀ z ∈ α, (BL z).Nonempty)
    (hBL_conn : ∀ z ∈ α, IsPreconnected (BL z))
    (hBR_ne : ∀ z ∈ α, (BR z).Nonempty)
    (hBR_conn : ∀ z ∈ α, IsPreconnected (BR z))
    (hBL_ov : ∀ z ∈ α, ∀ z' ∈ α, z' ∈ Metric.ball z (r z) → (BL z ∩ BL z').Nonempty)
    (hBR_ov : ∀ z ∈ α, ∀ z' ∈ α, z' ∈ Metric.ball z (r z) → (BR z ∩ BR z').Nonempty) :
    (Comps (U \ α)).encard ≤ (Comps U).encard + 1 := by
  obtain ⟨z₀, hz₀⟩ := hα_ne
  let F : Set (ℝ × ℝ) := connectedComponentIn U z₀
  have hF_mem : F ∈ Comps U := ⟨z₀, hα_sub hz₀, rfl⟩
  have hF_conn : IsPreconnected F := isPreconnected_connectedComponentIn
  have hα_sub_F : α ⊆ F := hα_conn.subset_connectedComponentIn hz₀ hα_sub
  let UL : Set (ℝ × ℝ) := ⋃ z ∈ α, BL z
  let UR : Set (ℝ × ℝ) := ⋃ z ∈ α, BR z
  have hBL_sub : ∀ z ∈ α, BL z ⊆ U \ α := fun z hz p hp => by
    have hmem : p ∈ Metric.ball z (r z) \ α := by rw [hball_split z hz]; exact Or.inl hp
    exact ⟨hball_sub z hz hmem.1, hmem.2⟩
  have hBR_sub : ∀ z ∈ α, BR z ⊆ U \ α := fun z hz p hp => by
    have hmem : p ∈ Metric.ball z (r z) \ α := by rw [hball_split z hz]; exact Or.inr hp
    exact ⟨hball_sub z hz hmem.1, hmem.2⟩
  have hUL_sub : UL ⊆ U \ α := Set.iUnion₂_subset hBL_sub
  have hUR_sub : UR ⊆ U \ α := Set.iUnion₂_subset hBR_sub
  have hUL_conn : IsPreconnected UL :=
    union_balls_preconnected hα_conn r BL hr_pos hBL_conn hBL_ov
  have hUR_conn : IsPreconnected UR :=
    union_balls_preconnected hα_conn r BR hr_pos hBR_conn hBR_ov
  obtain ⟨uL, huL⟩ := hBL_ne z₀ hz₀
  obtain ⟨uR, huR⟩ := hBR_ne z₀ hz₀
  have huL_mem : uL ∈ UL := Set.mem_biUnion hz₀ huL
  have huR_mem : uR ∈ UR := Set.mem_biUnion hz₀ huR
  let CL : Set (ℝ × ℝ) := connectedComponentIn (U \ α) uL
  let CR : Set (ℝ × ℝ) := connectedComponentIn (U \ α) uR
  have hsub : Comps (U \ α) ⊆ insert CL (insert CR (Comps U \ {F})) := by
    have comp_eq_of_mem : ∀ {S : Set (ℝ × ℝ)} {a b p : ℝ × ℝ},
        p ∈ connectedComponentIn S a → p ∈ connectedComponentIn S b →
        connectedComponentIn S a = connectedComponentIn S b := fun hpa hpb =>
      (connectedComponentIn_eq hpa).trans (connectedComponentIn_eq hpb).symm
    rintro C ⟨x, hx, rfl⟩
    by_cases hxF : x ∈ F
    · have hmeet : (connectedComponentIn (U \ α) x ∩ (UL ∪ UR)).Nonempty := by
        by_contra hno
        rw [Set.not_nonempty_iff_eq_empty] at hno
        let A : Set (ℝ × ℝ) := connectedComponentIn (U \ α) x
        let B : Set (ℝ × ℝ) :=
          (⋃ y ∈ (U \ α) \ A, connectedComponentIn (U \ α) y) ∪
          (⋃ z ∈ α, Metric.ball z (r z))
        have hA_open : IsOpen A := hUα_open.connectedComponentIn
        have hB_open : IsOpen B :=
          (isOpen_biUnion fun _ _ => hUα_open.connectedComponentIn).union
            (isOpen_biUnion fun _ _ => Metric.isOpen_ball)
        have hF_sub : F ⊆ A ∪ B := by
          intro p hpF
          by_cases hpα : p ∈ α
          · right; right; exact Set.mem_biUnion hpα (Metric.mem_ball_self (hr_pos p hpα))
          · have hpU : p ∈ U \ α := ⟨connectedComponentIn_subset U z₀ hpF, hpα⟩
            by_cases hpA : p ∈ A
            · left; exact hpA
            · right; left; exact Set.mem_biUnion ⟨hpU, hpA⟩ (mem_connectedComponentIn hpU)
        have hF_disj : F ∩ (A ∩ B) = ∅ := by
          rw [Set.eq_empty_iff_forall_notMem]
          rintro p ⟨_, hpA, hpB1 | hpB2⟩
          · rw [Set.mem_iUnion₂] at hpB1
            rcases hpB1 with ⟨y, ⟨hy, hyA⟩, hpy⟩
            have heq : A = connectedComponentIn (U \ α) y := comp_eq_of_mem hpA hpy
            rw [heq] at hyA
            exact hyA (mem_connectedComponentIn hy)
          · rw [Set.mem_iUnion₂] at hpB2
            rcases hpB2 with ⟨z, hz, hpb⟩
            have hp_not : p ∉ α := (connectedComponentIn_subset (U \ α) x hpA).2
            have hp_split : p ∈ BL z ∪ BR z := by
              rw [← hball_split z hz]; exact ⟨hpb, hp_not⟩
            have hp_U : p ∈ UL ∪ UR := by
              rcases hp_split with h1 | h2
              · left; exact Set.mem_biUnion hz h1
              · right; exact Set.mem_biUnion hz h2
            exact (Set.eq_empty_iff_forall_notMem.mp hno p) ⟨hpA, hp_U⟩
        obtain ⟨w, hwF, hwA, hwB⟩ := hF_conn A B hA_open hB_open hF_sub
          ⟨x, hxF, mem_connectedComponentIn hx⟩
          ⟨z₀, hα_sub_F hz₀, Or.inr (Set.mem_biUnion hz₀ (Metric.mem_ball_self (hr_pos z₀ hz₀)))⟩
        exact (Set.eq_empty_iff_forall_notMem.mp hF_disj w) ⟨hwF, hwA, hwB⟩
      obtain ⟨w, hwC, hwL | hwR⟩ := hmeet
      · left
        have hw_mem : w ∈ U \ α := hUL_sub hwL
        have h1 : connectedComponentIn (U \ α) x = connectedComponentIn (U \ α) w :=
          comp_eq_of_mem hwC (mem_connectedComponentIn hw_mem)
        have h2 : connectedComponentIn (U \ α) w = CL := by
          have hsub1 : UL ⊆ connectedComponentIn (U \ α) uL :=
            hUL_conn.subset_connectedComponentIn huL_mem hUL_sub
          exact comp_eq_of_mem (mem_connectedComponentIn hw_mem) (hsub1 hwL)
        exact h1.trans h2
      · right; left
        have hw_mem : w ∈ U \ α := hUR_sub hwR
        have h1 : connectedComponentIn (U \ α) x = connectedComponentIn (U \ α) w :=
          comp_eq_of_mem hwC (mem_connectedComponentIn hw_mem)
        have h2 : connectedComponentIn (U \ α) w = CR := by
          have hsub1 : UR ⊆ connectedComponentIn (U \ α) uR :=
            hUR_conn.subset_connectedComponentIn huR_mem hUR_sub
          exact comp_eq_of_mem (mem_connectedComponentIn hw_mem) (hsub1 hwR)
        exact h1.trans h2
    · right; right
      let F' := connectedComponentIn U x
      have hxU : x ∈ U := hx.1
      have hF'_mem : F' ∈ Comps U := ⟨x, hxU, rfl⟩
      have hF'_ne : F' ≠ F := fun heq => hxF (by rw [← heq]; exact mem_connectedComponentIn hxU)
      have hF'_disj : Disjoint F' F := by
        rw [Set.disjoint_left]; intro p hp1 hp2; exact hF'_ne (comp_eq_of_mem hp1 hp2)
      have hF'_sub : F' ⊆ U \ α := fun p hp =>
        ⟨connectedComponentIn_subset U x hp, fun hpα =>
          Set.disjoint_left.mp hF'_disj hp (hα_sub_F hpα)⟩
      have hC_eq : connectedComponentIn (U \ α) x = F' := by
        apply Set.Subset.antisymm
        · exact connectedComponentIn_mono x Set.sdiff_subset
        · exact isPreconnected_connectedComponentIn.subset_connectedComponentIn
            (mem_connectedComponentIn hxU) hF'_sub
      rw [hC_eq]; exact ⟨hF'_mem, hF'_ne⟩
  calc (Comps (U \ α)).encard
      ≤ (insert CL (insert CR (Comps U \ {F}))).encard := Set.encard_le_encard hsub
    _ ≤ (insert CR (Comps U \ {F})).encard + 1 := Set.encard_insert_le _ _
    _ ≤ ((Comps U \ {F}).encard + 1) + 1 := add_le_add (Set.encard_insert_le _ _) le_rfl
    _ = (Comps U).encard + 1 := by
        rw [add_assoc, add_comm 1 1, ← add_assoc, Set.encard_sdiff_singleton_add_one hF_mem]

def seg : (xs : List ℝ) → Fin (xs.length + 1) → Set ℝ
  | [], _ => Set.univ
  | a :: _, ⟨0, _⟩ => Set.Iio a
  | a :: tl, ⟨k + 1, hk⟩ => seg tl ⟨k, by simp at hk; omega⟩ ∩ Set.Ioi a

lemma seg_isOpen : ∀ (xs : List ℝ) (i : Fin (xs.length + 1)), IsOpen (seg xs i)
  | [], _ => isOpen_univ
  | _ :: _, ⟨0, _⟩ => isOpen_Iio
  | _ :: tl, ⟨k + 1, hk⟩ => (seg_isOpen tl ⟨k, by simp at hk; omega⟩).inter isOpen_Ioi

lemma seg_convex : ∀ (xs : List ℝ) (i : Fin (xs.length + 1)), Convex ℝ (seg xs i)
  | [], _ => convex_univ
  | _ :: _, ⟨0, _⟩ => convex_Iio _
  | a :: tl, ⟨k + 1, hk⟩ => (seg_convex tl ⟨k, by simp at hk; omega⟩).inter (convex_Ioi a)

lemma seg_isPreconnected (xs : List ℝ) (i : Fin (xs.length + 1)) : IsPreconnected (seg xs i) :=
  (seg_convex xs i).isPreconnected

lemma seg_nonempty : ∀ (xs : List ℝ), xs.SortedLT → ∀ (i : Fin (xs.length + 1)), (seg xs i).Nonempty
  | [], _, _ => ⟨0, trivial⟩
  | a :: _, _, ⟨0, _⟩ => ⟨a - 1, by simp [seg]⟩
  | a :: [], _, ⟨1, _⟩ => ⟨a + 1, by simp [seg]⟩
  | a :: b :: tl', hsort, ⟨1, _⟩ => by
    have hab : a < b := hsort (Fin.mk_lt_mk.mpr Nat.zero_lt_one :
      (⟨0, by simp⟩ : Fin (a :: b :: tl').length) < ⟨1, by simp⟩)
    exact ⟨(a + b) / 2, by simp [seg]; constructor <;> linarith⟩
  | a :: b :: tl', hsort, ⟨k + 2, hk⟩ => by
    have hab : a < b := hsort (Fin.mk_lt_mk.mpr Nat.zero_lt_one :
      (⟨0, by simp⟩ : Fin (a :: b :: tl').length) < ⟨1, by simp⟩)
    have htl : (b :: tl').SortedLT := fun i j hij => hsort (Fin.succ_lt_succ_iff.mpr hij)
    obtain ⟨w, hw⟩ := seg_nonempty (b :: tl') htl ⟨k + 1, by dsimp [List.length] at hk ⊢; omega⟩
    exact ⟨w, hw, hab.trans hw.2⟩

lemma seg_disjoint_list : ∀ (xs : List ℝ), xs.SortedLT →
    ∀ (i : Fin (xs.length + 1)), seg xs i ⊆ {s : ℝ | s ∉ xs}
  | [], _, _, _, _, hmem => by simp at hmem
  | a :: tl, hsort, ⟨0, _⟩, s, hs, hmem => by
    change s < a at hs
    rcases List.mem_cons.mp hmem with rfl | htl
    · exact lt_irrefl _ hs
    · obtain ⟨j, hj⟩ := List.mem_iff_get.mp htl
      have has : a < s := by
        rw [← hj]
        exact hsort (Fin.mk_lt_mk.mpr (Nat.zero_lt_succ j.val) :
          (⟨0, by simp⟩ : Fin (a :: tl).length) < ⟨j.val + 1, by simp⟩)
      linarith
  | a :: tl, hsort, ⟨k + 1, hk⟩, s, hs, hmem => by
    have htl_sort : tl.SortedLT := fun i j hij => hsort (Fin.succ_lt_succ_iff.mpr hij)
    rcases List.mem_cons.mp hmem with rfl | htl
    · exact lt_irrefl s (Set.mem_Ioi.mp hs.2)
    · exact seg_disjoint_list tl htl_sort ⟨k, by dsimp [List.length] at hk ⊢; omega⟩ hs.1 htl

lemma compl_list_subset_iUnion_seg : ∀ (xs : List ℝ),
    {s : ℝ | s ∉ xs} ⊆ ⋃ i : Fin (xs.length + 1), seg xs i
  | [], s, _ => Set.mem_iUnion.mpr ⟨0, trivial⟩
  | a :: tl, s, hs => by
    have hne : s ≠ a := fun h => hs (h ▸ List.mem_cons_self)
    have htl : s ∉ tl := fun h => hs (List.mem_cons_of_mem _ h)
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact Set.mem_iUnion.mpr ⟨0, hlt⟩
    · have hmem := compl_list_subset_iUnion_seg tl htl
      rw [Set.mem_iUnion] at hmem
      obtain ⟨k, hk⟩ := hmem
      exact Set.mem_iUnion.mpr ⟨k.succ, hk, hgt⟩

lemma closure_seg_subset : ∀ (xs : List ℝ) (i : Fin (xs.length + 1)),
    closure (seg xs i) ⊆ seg xs i ∪ {s : ℝ | s ∈ xs}
  | [], _, s, _ => Or.inl trivial
  | a :: _, ⟨0, _⟩, s, hs => by
    have hs' : s ≤ a := by simpa [seg] using hs
    rcases lt_or_eq_of_le hs' with h | rfl
    · exact Or.inl h
    · exact Or.inr List.mem_cons_self
  | a :: tl, ⟨k + 1, hk⟩, s, hs => by
    have h1 : s ∈ closure (seg tl ⟨k, by simp at hk; omega⟩) :=
      closure_mono Set.inter_subset_left hs
    have h2 : a ≤ s := by
      have := closure_mono Set.inter_subset_right hs
      simpa using this
    rcases lt_or_eq_of_le h2 with ha_lt | rfl
    · rcases closure_seg_subset tl ⟨k, by simp at hk; omega⟩ h1 with hseg | htl
      · exact Or.inl ⟨hseg, ha_lt⟩
      · exact Or.inr (List.mem_cons_of_mem _ htl)
    · exact Or.inr List.mem_cons_self

private lemma seg_pairwise_disjoint : ∀ (xs : List ℝ) {i j : Fin (xs.length + 1)},
    i ≠ j → Disjoint (seg xs i) (seg xs j)
  | [], ⟨0, _⟩, ⟨0, _⟩, hij => False.elim (hij rfl)
  | a :: tl, ⟨0, _⟩, ⟨0, _⟩, hij => False.elim (hij rfl)
  | a :: tl, ⟨0, _⟩, ⟨k + 1, _⟩, _ => Set.disjoint_left.mpr fun s hs1 hs2 => by
      change s < a at hs1; exact absurd (Set.mem_Ioi.mp hs2.2) (not_lt.mpr (le_of_lt hs1))
  | a :: tl, ⟨k + 1, _⟩, ⟨0, _⟩, _ => Set.disjoint_left.mpr fun s hs1 hs2 => by
      change s < a at hs2; exact absurd (Set.mem_Ioi.mp hs1.2) (not_lt.mpr (le_of_lt hs2))
  | a :: tl, ⟨k + 1, hk⟩, ⟨m + 1, hm⟩, hij => by
      have hkm : (⟨k, by simp at hk; omega⟩ : Fin (tl.length + 1)) ≠
          ⟨m, by simp at hm; omega⟩ := by
        intro h
        apply hij
        exact Fin.ext (congrArg (· + 1) (congrArg Fin.val h))
      exact Set.disjoint_left.mpr fun s hs1 hs2 =>
        Set.disjoint_left.mp (seg_pairwise_disjoint tl hkm) hs1.1 hs2.1

private lemma biUnion_ncard_le_sum {ι : Type*} (S : Finset ι) (f : ι → Set (ℝ × ℝ))
    (hf : ∀ i ∈ S, (f i).Finite) :
    (⋃ i ∈ S, f i).ncard ≤ ∑ i ∈ S, (f i).ncard := by
  induction S using Finset.induction with
  | empty => simp
  | @insert i S' hiS ih =>
    have hf' : ∀ j ∈ S', (f j).Finite := fun j hj => hf j (Finset.mem_insert_of_mem hj)
    have h_eq : (⋃ j ∈ insert i S', f j) = f i ∪ (⋃ j ∈ S', f j) := by
      ext x; simp [Finset.mem_insert]
    rw [h_eq, Finset.sum_insert hiS]
    exact (Set.ncard_union_le _ _).trans (add_le_add le_rfl (ih hf'))

private lemma ball_shift_mem {z d : ℝ × ℝ} {δ : ℝ} (hδ : 0 < δ) :
    ∃ ε > 0, (z.1 + ε * d.1, z.2 + ε * d.2) ∈ Metric.ball z δ := by
  let B := |d.1| + |d.2| + 1
  have hB : 0 < B := by positivity
  refine ⟨δ / (2 * B), by positivity, ?_⟩
  rw [Metric.mem_ball, Prod.dist_eq]
  have he : 0 < δ / (2 * B) := by positivity
  have h1 : dist (z.1 + (δ / (2 * B)) * d.1) z.1 < δ := by
    rw [Real.dist_eq, show z.1 + (δ / (2 * B)) * d.1 - z.1 = (δ / (2 * B)) * d.1 by ring,
      abs_mul, abs_of_pos he]
    have hle : |d.1| < B := by dsimp [B]; linarith [abs_nonneg d.2]
    calc (δ / (2 * B)) * |d.1| ≤ (δ / (2 * B)) * B :=
          mul_le_mul_of_nonneg_left (le_of_lt hle) (le_of_lt he)
      _ = δ / 2 := by field_simp [ne_of_gt hB]
      _ < δ := by linarith
  have h2 : dist (z.2 + (δ / (2 * B)) * d.2) z.2 < δ := by
    rw [Real.dist_eq, show z.2 + (δ / (2 * B)) * d.2 - z.2 = (δ / (2 * B)) * d.2 by ring,
      abs_mul, abs_of_pos he]
    have hle : |d.2| < B := by dsimp [B]; linarith [abs_nonneg d.1]
    calc (δ / (2 * B)) * |d.2| ≤ (δ / (2 * B)) * B :=
          mul_le_mul_of_nonneg_left (le_of_lt hle) (le_of_lt he)
      _ = δ / 2 := by field_simp [ne_of_gt hB]
      _ < δ := by linarith
  exact max_lt h1 h2

private lemma bdWedge_ball_memOpen_ne (Wk : OpenWedge) {z : ℝ × ℝ} (hz : z ∈ bdWedge Wk)
    {δ : ℝ} (hδ : 0 < δ) :
    (Metric.ball z δ ∩ {p | Wk.MemOpen p}).Nonempty := by
  let d : ℝ × ℝ := ((dir1 Wk).1 + (dir2 Wk).1, (dir1 Wk).2 + (dir2 Wk).2)
  obtain ⟨ε, hε, hball⟩ := ball_shift_mem (z := z) (d := d) hδ
  have hcl := (bdWedge_iff_closure_eq_zero Wk z).mp hz |>.1
  have hnd := Wk.h_nondeg
  have ho1 : 0 < Wk.u₁.1 * ((z.1 + ε * d.1) - Wk.y.1) +
      Wk.u₁.2 * ((z.2 + ε * d.2) - Wk.y.2) := by
    have e : Wk.u₁.1 * ((z.1 + ε * d.1) - Wk.y.1) + Wk.u₁.2 * ((z.2 + ε * d.2) - Wk.y.2) =
        (Wk.u₁.1 * (z.1 - Wk.y.1) + Wk.u₁.2 * (z.2 - Wk.y.2)) +
        ε * (Wk.u₁.1 * Wk.u₂.2 - Wk.u₁.2 * Wk.u₂.1) := by
      dsimp [d, dir1, dir2]; ring
    rw [e]; nlinarith [hcl.1]
  have ho2 : 0 < Wk.u₂.1 * ((z.1 + ε * d.1) - Wk.y.1) +
      Wk.u₂.2 * ((z.2 + ε * d.2) - Wk.y.2) := by
    have e : Wk.u₂.1 * ((z.1 + ε * d.1) - Wk.y.1) + Wk.u₂.2 * ((z.2 + ε * d.2) - Wk.y.2) =
        (Wk.u₂.1 * (z.1 - Wk.y.1) + Wk.u₂.2 * (z.2 - Wk.y.2)) +
        ε * (Wk.u₁.1 * Wk.u₂.2 - Wk.u₁.2 * Wk.u₂.1) := by
      dsimp [d, dir1, dir2]; ring
    rw [e]; nlinarith [hcl.2]
  exact ⟨(z.1 + ε * d.1, z.2 + ε * d.2), hball, ho1, ho2⟩

private lemma bdWedge_ball_memExt_ne (Wk : OpenWedge) {z : ℝ × ℝ} (hz : z ∈ bdWedge Wk)
    {δ : ℝ} (hδ : 0 < δ) :
    (Metric.ball z δ ∩ {p | Wk.MemExt p}).Nonempty := by
  have hnd := Wk.h_nondeg
  rcases (bdWedge_iff_closure_eq_zero Wk z).mp hz |>.2 with hz1 | hz2
  · let d : ℝ × ℝ := (-(dir2 Wk).1, -(dir2 Wk).2)
    obtain ⟨ε, hε, hball⟩ := ball_shift_mem (z := z) (d := d) hδ
    have hext : Wk.u₁.1 * ((z.1 + ε * d.1) - Wk.y.1) +
        Wk.u₁.2 * ((z.2 + ε * d.2) - Wk.y.2) < 0 := by
      have e : Wk.u₁.1 * ((z.1 + ε * d.1) - Wk.y.1) + Wk.u₁.2 * ((z.2 + ε * d.2) - Wk.y.2) =
          (Wk.u₁.1 * (z.1 - Wk.y.1) + Wk.u₁.2 * (z.2 - Wk.y.2)) -
          ε * (Wk.u₁.1 * Wk.u₂.2 - Wk.u₁.2 * Wk.u₂.1) := by
        dsimp [d, dir2]; ring
      rw [e, hz1]; nlinarith
    exact ⟨(z.1 + ε * d.1, z.2 + ε * d.2), hball, Or.inl hext⟩
  · let d : ℝ × ℝ := (-(dir1 Wk).1, -(dir1 Wk).2)
    obtain ⟨ε, hε, hball⟩ := ball_shift_mem (z := z) (d := d) hδ
    have hext : Wk.u₂.1 * ((z.1 + ε * d.1) - Wk.y.1) +
        Wk.u₂.2 * ((z.2 + ε * d.2) - Wk.y.2) < 0 := by
      have e : Wk.u₂.1 * ((z.1 + ε * d.1) - Wk.y.1) + Wk.u₂.2 * ((z.2 + ε * d.2) - Wk.y.2) =
          (Wk.u₂.1 * (z.1 - Wk.y.1) + Wk.u₂.2 * (z.2 - Wk.y.2)) -
          ε * (Wk.u₁.1 * Wk.u₂.2 - Wk.u₁.2 * Wk.u₂.1) := by
        dsimp [d, dir1]; ring
      rw [e, hz2]; nlinarith
    exact ⟨(z.1 + ε * d.1, z.2 + ε * d.2), hball, Or.inr hext⟩

private lemma remove_seg_arc_comps
    (Wk : OpenWedge)
    (U : Set (ℝ × ℝ)) (hU_open : IsOpen U)
    (xs : List ℝ) (hxs_sorted : xs.SortedLT)
    (i : Fin (xs.length + 1))
    (hi_sub : gammaParam Wk '' seg xs i ⊆ U)
    (hUi_open : IsOpen (U \ (gammaParam Wk '' seg xs i))) :
    (Comps (U \ (gammaParam Wk '' seg xs i))).encard ≤ (Comps U).encard + 1 := by
  let α : Set (ℝ × ℝ) := gammaParam Wk '' seg xs i
  have hα_ne : α.Nonempty := (seg_nonempty xs hxs_sorted i).image _
  have hα_conn : IsPreconnected α :=
    (seg_isPreconnected xs i).image (gammaParam Wk) (gammaParam_continuous Wk).continuousOn
  let K_other : Set (ℝ × ℝ) := gammaParam Wk '' (seg xs i)ᶜ
  have hK_closed : IsClosed K_other :=
    gammaParam_image_isClosed Wk (seg_isOpen xs i).isClosed_compl
  let V : (ℝ × ℝ) → Set (ℝ × ℝ) := fun z =>
    if z = Wk.y then U ∩ K_otherᶜ
    else if Wk.u₁.1 * (z.1 - Wk.y.1) + Wk.u₁.2 * (z.2 - Wk.y.2) = 0 then
      U ∩ K_otherᶜ ∩ {p | 0 < Wk.u₂.1 * (p.1 - Wk.y.1) + Wk.u₂.2 * (p.2 - Wk.y.2)}
    else
      U ∩ K_otherᶜ ∩ {p | 0 < Wk.u₁.1 * (p.1 - Wk.y.1) + Wk.u₁.2 * (p.2 - Wk.y.2)}
  have hV_open : ∀ z, IsOpen (V z) := by
    intro z; dsimp [V]
    split_ifs
    · exact hU_open.inter hK_closed.isOpen_compl
    · refine (hU_open.inter hK_closed.isOpen_compl).inter (isOpen_lt continuous_const ?_)
      fun_prop
    · refine (hU_open.inter hK_closed.isOpen_compl).inter (isOpen_lt continuous_const ?_)
      fun_prop
  have hz_mem_V : ∀ z ∈ α, z ∈ V z := by
    rintro z ⟨s, hs, rfl⟩
    have hzU : gammaParam Wk s ∈ U := hi_sub ⟨s, hs, rfl⟩
    have hzG : gammaParam Wk s ∈ bdWedge Wk := gammaParam_mem_bdWedge Wk s
    have hzK : gammaParam Wk s ∉ K_other := by
      rintro ⟨s', hs', heq⟩
      rw [gammaParam_injective Wk heq] at hs'
      exact hs' hs
    dsimp [V]
    split_ifs with hzy hz1
    · exact ⟨hzU, hzK⟩
    · refine ⟨⟨hzU, hzK⟩, ?_⟩
      have hcl := (bdWedge_iff_closure_eq_zero Wk _).mp hzG |>.1
      refine lt_of_le_of_ne hcl.2 fun hz2 => hzy ?_
      have hnd := ne_of_gt Wk.h_nondeg
      have e1 : (gammaParam Wk s).1 - Wk.y.1 = 0 := by
        have hmul : ((gammaParam Wk s).1 - Wk.y.1) * (Wk.u₁.1 * Wk.u₂.2 - Wk.u₁.2 * Wk.u₂.1) = 0 := by
          linear_combination Wk.u₂.2 * hz1 - Wk.u₁.2 * hz2.symm
        exact (mul_eq_zero.mp hmul).resolve_right hnd
      have e2 : (gammaParam Wk s).2 - Wk.y.2 = 0 := by
        have hmul : ((gammaParam Wk s).2 - Wk.y.2) * (Wk.u₁.1 * Wk.u₂.2 - Wk.u₁.2 * Wk.u₂.1) = 0 := by
          linear_combination -Wk.u₂.1 * hz1 + Wk.u₁.1 * hz2.symm
        exact (mul_eq_zero.mp hmul).resolve_right hnd
      ext <;> linarith
    · refine ⟨⟨hzU, hzK⟩, ?_⟩
      have hcl := (bdWedge_iff_closure_eq_zero Wk _).mp hzG |>.1
      exact lt_of_le_of_ne hcl.1 (Ne.symm hz1)
  let r : (ℝ × ℝ) → ℝ := fun z =>
    if hz : z ∈ α then (Metric.isOpen_iff.mp (hV_open z) z (hz_mem_V z hz)).choose else 1
  have hr_pos : ∀ z ∈ α, 0 < r z := fun z hz => by
    dsimp [r]; rw [dif_pos hz]
    exact (Metric.isOpen_iff.mp (hV_open z) z (hz_mem_V z hz)).choose_spec.1
  have hball_V : ∀ z ∈ α, Metric.ball z (r z) ⊆ V z := fun z hz => by
    dsimp [r]; rw [dif_pos hz]
    exact (Metric.isOpen_iff.mp (hV_open z) z (hz_mem_V z hz)).choose_spec.2
  have hV_sub_UK : ∀ z, V z ⊆ U ∩ K_otherᶜ := by
    intro z; dsimp [V]; split_ifs <;> [exact Set.Subset.rfl; exact Set.inter_subset_left; exact Set.inter_subset_left]
  have hball_sub : ∀ z ∈ α, Metric.ball z (r z) ⊆ U := fun z hz =>
    (hball_V z hz).trans ((hV_sub_UK z).trans Set.inter_subset_left)
  let BL : (ℝ × ℝ) → Set (ℝ × ℝ) := fun z => Metric.ball z (r z) ∩ {p | Wk.MemOpen p}
  let BR : (ℝ × ℝ) → Set (ℝ × ℝ) := fun z => Metric.ball z (r z) ∩ {p | Wk.MemExt p}
  have hball_split : ∀ z ∈ α, Metric.ball z (r z) \ α = BL z ∪ BR z := by
    intro z hz
    ext p; constructor
    · rintro ⟨hp_ball, hp_nα⟩
      have hpUK := hV_sub_UK z (hball_V z hz hp_ball)
      have hp_nbd : p ∉ bdWedge Wk := by
        intro hp_bd
        rw [← gammaParam_range Wk] at hp_bd
        obtain ⟨s', rfl⟩ := hp_bd
        by_cases hs' : s' ∈ seg xs i
        · exact hp_nα ⟨s', hs', rfl⟩
        · exact hpUK.2 ⟨s', hs', rfl⟩
      dsimp [bdWedge] at hp_nbd
      push Not at hp_nbd
      by_cases ho : Wk.MemOpen p
      · left; exact ⟨hp_ball, ho⟩
      · right; exact ⟨hp_ball, hp_nbd ho⟩
    · rintro (⟨hp_ball, ho⟩ | ⟨hp_ball, he⟩)
      · refine ⟨hp_ball, fun hpα => ?_⟩
        obtain ⟨s', _, rfl⟩ := hpα
        exact (gammaParam_mem_bdWedge Wk s').1 ho
      · refine ⟨hp_ball, fun hpα => ?_⟩
        obtain ⟨s', _, rfl⟩ := hpα
        exact (gammaParam_mem_bdWedge Wk s').2 he
  have hBL_ne : ∀ z ∈ α, (BL z).Nonempty := fun z hz => by
    obtain ⟨s, _, rfl⟩ := hz
    exact bdWedge_ball_memOpen_ne Wk (gammaParam_mem_bdWedge Wk s) (hr_pos _ ⟨s, ‹_›, rfl⟩)
  have hBL_conn : ∀ z ∈ α, IsPreconnected (BL z) := fun z _ =>
    ((convex_ball z (r z)).inter (memOpen_convex Wk)).isPreconnected
  have hBR_ne : ∀ z ∈ α, (BR z).Nonempty := fun z hz => by
    obtain ⟨s, _, rfl⟩ := hz
    exact bdWedge_ball_memExt_ne Wk (gammaParam_mem_bdWedge Wk s) (hr_pos _ ⟨s, ‹_›, rfl⟩)
  have hBR_conn : ∀ z ∈ α, IsPreconnected (BR z) := by
    intro z hz
    dsimp [BR]
    by_cases hzy : z = Wk.y
    · let S1 : Set (ℝ × ℝ) := Metric.ball z (r z) ∩
        {p | Wk.u₁.1 * (p.1 - Wk.y.1) + Wk.u₁.2 * (p.2 - Wk.y.2) < 0}
      let S2 : Set (ℝ × ℝ) := Metric.ball z (r z) ∩
        {p | Wk.u₂.1 * (p.1 - Wk.y.1) + Wk.u₂.2 * (p.2 - Wk.y.2) < 0}
      have heq : Metric.ball z (r z) ∩ {p | Wk.MemExt p} = S1 ∪ S2 := by
        ext p; simp [S1, S2, OpenWedge.MemExt, and_or_left]
      rw [heq]
      have hc1 : IsPreconnected S1 :=
        ((convex_ball z (r z)).inter (halfspace_lt_convex Wk.u₁ Wk.y)).isPreconnected
      have hc2 : IsPreconnected S2 :=
        ((convex_ball z (r z)).inter (halfspace_lt_convex Wk.u₂ Wk.y)).isPreconnected
      let d_neg : ℝ × ℝ := (-(dir1 Wk).1 - (dir2 Wk).1, -(dir1 Wk).2 - (dir2 Wk).2)
      obtain ⟨ε, hε, hball⟩ := ball_shift_mem (z := z) (d := d_neg) (hr_pos z hz)
      have hnd := Wk.h_nondeg
      have ho1 : Wk.u₁.1 * ((z.1 + ε * d_neg.1) - Wk.y.1) +
          Wk.u₁.2 * ((z.2 + ε * d_neg.2) - Wk.y.2) < 0 := by
        rw [hzy]
        have e : Wk.u₁.1 * ((Wk.y.1 + ε * d_neg.1) - Wk.y.1) +
            Wk.u₁.2 * ((Wk.y.2 + ε * d_neg.2) - Wk.y.2) =
            -ε * (Wk.u₁.1 * Wk.u₂.2 - Wk.u₁.2 * Wk.u₂.1) := by
          dsimp [d_neg, dir1, dir2]; ring
        rw [e]; nlinarith
      have ho2 : Wk.u₂.1 * ((z.1 + ε * d_neg.1) - Wk.y.1) +
          Wk.u₂.2 * ((z.2 + ε * d_neg.2) - Wk.y.2) < 0 := by
        rw [hzy]
        have e : Wk.u₂.1 * ((Wk.y.1 + ε * d_neg.1) - Wk.y.1) +
            Wk.u₂.2 * ((Wk.y.2 + ε * d_neg.2) - Wk.y.2) =
            -ε * (Wk.u₁.1 * Wk.u₂.2 - Wk.u₁.2 * Wk.u₂.1) := by
          dsimp [d_neg, dir1, dir2]; ring
        rw [e]; nlinarith
      exact hc1.union' ⟨(z.1 + ε * d_neg.1, z.2 + ε * d_neg.2), ⟨hball, ho1⟩, ⟨hball, ho2⟩⟩ hc2
    · by_cases hz1 : Wk.u₁.1 * (z.1 - Wk.y.1) + Wk.u₁.2 * (z.2 - Wk.y.2) = 0
      · have hsubV : Metric.ball z (r z) ⊆ {p | 0 < Wk.u₂.1 * (p.1 - Wk.y.1) + Wk.u₂.2 * (p.2 - Wk.y.2)} := by
          intro p hp
          have hpV := hball_V z hz hp
          dsimp [V] at hpV
          rw [if_neg hzy, if_pos hz1] at hpV
          exact hpV.2
        have heq : Metric.ball z (r z) ∩ {p | Wk.MemExt p} =
            Metric.ball z (r z) ∩ {p | Wk.u₁.1 * (p.1 - Wk.y.1) + Wk.u₁.2 * (p.2 - Wk.y.2) < 0} := by
          ext p; constructor
          · rintro ⟨hp, hp1 | hp2⟩
            · exact ⟨hp, hp1⟩
            · exfalso; have hp_pos : 0 < Wk.u₂.1 * (p.1 - Wk.y.1) + Wk.u₂.2 * (p.2 - Wk.y.2) := hsubV hp
              linarith
          · rintro ⟨hp, hp1⟩; exact ⟨hp, Or.inl hp1⟩
        rw [heq]
        exact ((convex_ball z (r z)).inter (halfspace_lt_convex Wk.u₁ Wk.y)).isPreconnected
      · have hsubV : Metric.ball z (r z) ⊆ {p | 0 < Wk.u₁.1 * (p.1 - Wk.y.1) + Wk.u₁.2 * (p.2 - Wk.y.2)} := by
          intro p hp
          have hpV := hball_V z hz hp
          dsimp [V] at hpV
          rw [if_neg hzy, if_neg hz1] at hpV
          exact hpV.2
        have heq : Metric.ball z (r z) ∩ {p | Wk.MemExt p} =
            Metric.ball z (r z) ∩ {p | Wk.u₂.1 * (p.1 - Wk.y.1) + Wk.u₂.2 * (p.2 - Wk.y.2) < 0} := by
          ext p; constructor
          · rintro ⟨hp, hp1 | hp2⟩
            · exfalso; have hp_pos : 0 < Wk.u₁.1 * (p.1 - Wk.y.1) + Wk.u₁.2 * (p.2 - Wk.y.2) := hsubV hp
              linarith
            · exact ⟨hp, hp2⟩
          · rintro ⟨hp, hp2⟩; exact ⟨hp, Or.inr hp2⟩
        rw [heq]
        exact ((convex_ball z (r z)).inter (halfspace_lt_convex Wk.u₂ Wk.y)).isPreconnected
  have h_ball_inter : ∀ z ∈ α, ∀ z' ∈ α, z' ∈ Metric.ball z (r z) →
      ∃ δ > 0, Metric.ball z' δ ⊆ Metric.ball z (r z) ∩ Metric.ball z' (r z') := by
    intro z _ z' hz' hz'b
    let δ := min (r z - dist z' z) (r z')
    have hδ : 0 < δ := lt_min (sub_pos.mpr (Metric.mem_ball.mp hz'b)) (hr_pos z' hz')
    refine ⟨δ, hδ, fun p hp => ⟨?_, ?_⟩⟩
    · rw [Metric.mem_ball] at hp ⊢
      have hd1 : dist p z' < r z - dist z' z := lt_of_lt_of_le hp (min_le_left _ _)
      linarith [dist_triangle p z' z]
    · exact Metric.mem_ball.mpr (lt_of_lt_of_le (Metric.mem_ball.mp hp) (min_le_right _ _))
  have hBL_ov : ∀ z ∈ α, ∀ z' ∈ α, z' ∈ Metric.ball z (r z) → (BL z ∩ BL z').Nonempty := by
    intro z hz z' hz' hz'b
    obtain ⟨δ, hδ, hsub_ball⟩ := h_ball_inter z hz z' hz' hz'b
    obtain ⟨s', _, rfl⟩ := hz'
    obtain ⟨p, hp_ball, hp_om⟩ := bdWedge_ball_memOpen_ne Wk (gammaParam_mem_bdWedge Wk s') hδ
    exact ⟨p, ⟨(hsub_ball hp_ball).1, hp_om⟩, ⟨(hsub_ball hp_ball).2, hp_om⟩⟩
  have hBR_ov : ∀ z ∈ α, ∀ z' ∈ α, z' ∈ Metric.ball z (r z) → (BR z ∩ BR z').Nonempty := by
    intro z hz z' hz' hz'b
    obtain ⟨δ, hδ, hsub_ball⟩ := h_ball_inter z hz z' hz' hz'b
    obtain ⟨s', _, rfl⟩ := hz'
    obtain ⟨p, hp_ball, hp_ext⟩ := bdWedge_ball_memExt_ne Wk (gammaParam_mem_bdWedge Wk s') hδ
    exact ⟨p, ⟨(hsub_ball hp_ball).1, hp_ext⟩, ⟨(hsub_ball hp_ball).2, hp_ext⟩⟩
  exact comps_remove_arc hU_open hi_sub hα_ne hα_conn hUi_open r BL BR
    hr_pos hball_sub hball_split hBL_ne hBL_conn hBR_ne hBR_conn hBL_ov hBR_ov

lemma inter_card_le_four {W : Fin 6 → OpenWedge} (hGP : GP6 W)
    {i j : Fin 6} (hij : i ≠ j) :
    (bdWedge (W i) ∩ bdWedge (W j)).Finite ∧ (bdWedge (W i) ∩ bdWedge (W j)).ncard ≤ 4 := by
  have huniq : ∀ (bi bj : Bool), ∃ p₀ : ℝ × ℝ,
      lineAt W (i, bi) p₀ = 0 ∧ lineAt W (j, bj) p₀ = 0 ∧
      (∀ p : ℝ × ℝ, lineAt W (i, bi) p = 0 → lineAt W (j, bj) p = 0 → p = p₀) := by
    intro bi bj
    have hne : (i, bi) ≠ (j, bj) := fun h => hij (congrArg Prod.fst h)
    have hdet := hGP.no_parallel (i, bi) (j, bj) hne
    let a1 := (normal W (i, bi)).1; let a2 := (normal W (i, bi)).2
    let b1 := (normal W (j, bj)).1; let b2 := (normal W (j, bj)).2
    let ca := a1 * (W i).y.1 + a2 * (W i).y.2
    let cb := b1 * (W j).y.1 + b2 * (W j).y.2
    let det := a1 * b2 - a2 * b1
    have hdet' : det ≠ 0 := hdet
    refine ⟨((b2 * ca - a2 * cb) / det, (-b1 * ca + a1 * cb) / det), ?_, ?_, fun p hp1 hp2 => ?_⟩
    · dsimp [lineAt]
      change a1 * ((b2 * ca - a2 * cb) / det - (W i).y.1) +
             a2 * ((-b1 * ca + a1 * cb) / det - (W i).y.2) = 0
      field_simp [hdet']; dsimp [det, ca, cb]; ring
    · dsimp [lineAt]
      change b1 * ((b2 * ca - a2 * cb) / det - (W j).y.1) +
             b2 * ((-b1 * ca + a1 * cb) / det - (W j).y.2) = 0
      field_simp [hdet']; dsimp [det, ca, cb]; ring
    · dsimp [lineAt] at hp1 hp2
      have h1 : det * p.1 = b2 * ca - a2 * cb := by
        change (a1 * b2 - a2 * b1) * p.1 = b2 * (a1 * (W i).y.1 + a2 * (W i).y.2) -
          a2 * (b1 * (W j).y.1 + b2 * (W j).y.2)
        linear_combination b2 * hp1 - a2 * hp2
      have h2 : det * p.2 = -b1 * ca + a1 * cb := by
        change (a1 * b2 - a2 * b1) * p.2 = -b1 * (a1 * (W i).y.1 + a2 * (W i).y.2) +
          a1 * (b1 * (W j).y.1 + b2 * (W j).y.2)
        linear_combination -b1 * hp1 + a1 * hp2
      ext
      · exact (eq_div_iff hdet').mpr (by rw [mul_comm]; exact h1)
      · exact (eq_div_iff hdet').mpr (by rw [mul_comm]; exact h2)
  let pt (bi bj : Bool) : ℝ × ℝ := (huniq bi bj).choose
  have hpt : ∀ bi bj p, lineAt W (i, bi) p = 0 → lineAt W (j, bj) p = 0 → p = pt bi bj :=
    fun bi bj => (huniq bi bj).choose_spec.2.2
  let S4 : Finset (ℝ × ℝ) := {pt true true, pt true false, pt false true, pt false false}
  have hsub : bdWedge (W i) ∩ bdWedge (W j) ⊆ (S4 : Set (ℝ × ℝ)) := by
    rintro p ⟨hi, hj⟩
    obtain ⟨_, hi_eq⟩ := (bdWedge_iff_closure_eq_zero (W i) p).mp hi
    obtain ⟨_, hj_eq⟩ := (bdWedge_iff_closure_eq_zero (W j) p).mp hj
    rcases hi_eq with hi1 | hi2 <;> rcases hj_eq with hj1 | hj2
    · have := hpt true true p (by simpa [lineAt, normal] using hi1) (by simpa [lineAt, normal] using hj1)
      simp [S4, this]
    · have := hpt true false p (by simpa [lineAt, normal] using hi1) (by simpa [lineAt, normal] using hj2)
      simp [S4, this]
    · have := hpt false true p (by simpa [lineAt, normal] using hi2) (by simpa [lineAt, normal] using hj1)
      simp [S4, this]
    · have := hpt false false p (by simpa [lineAt, normal] using hi2) (by simpa [lineAt, normal] using hj2)
      simp [S4, this]
  refine ⟨S4.finite_toSet.subset hsub, ?_⟩
  calc (bdWedge (W i) ∩ bdWedge (W j)).ncard
      ≤ (S4 : Set (ℝ × ℝ)).ncard := Set.ncard_le_ncard hsub S4.finite_toSet
    _ = S4.card := Set.ncard_coe_finset S4
    _ ≤ 4 := by
        dsimp [S4]
        exact (Finset.card_insert_le _ _).trans (Nat.succ_le_succ
          ((Finset.card_insert_le _ _).trans (Nat.succ_le_succ
            ((Finset.card_insert_le _ _).trans (Nat.succ_le_succ (by simp))))))

lemma add_wedge_comps_bound_univ {W : Fin 6 → OpenWedge} (hGP : GP6 W)
    (S : Finset (Fin 6)) (k : Fin 6) (hkS : k ∉ S) :
    (Comps ((Set.univ : Set (ℝ × ℝ)) \ ⋃ j ∈ insert k S, bdWedge (W j))).encard ≤
    (Comps ((Set.univ : Set (ℝ × ℝ)) \ ⋃ j ∈ S, bdWedge (W j))).encard +
      1 + ∑ j ∈ S, ((bdWedge (W k) ∩ bdWedge (W j)).ncard : ℕ∞) := by
  let U₀ : Set (ℝ × ℝ) := Set.univ \ ⋃ j ∈ S, bdWedge (W j)
  have hU₀_open : IsOpen U₀ :=
    isOpen_univ.sdiff (S.finite_toSet.isClosed_biUnion fun j _ => bdWedge_isClosed (W j))
  let P_set : Set (ℝ × ℝ) := ⋃ j ∈ S, (bdWedge (W k) ∩ bdWedge (W j))
  have hP_fin : P_set.Finite :=
    S.finite_toSet.biUnion fun j hj => (inter_card_le_four hGP (ne_of_mem_of_not_mem hj hkS).symm).1
  let P_param : Set ℝ := (gammaParam (W k)) ⁻¹' P_set
  have hP_param_fin : P_param.Finite := hP_fin.preimage (gammaParam_injective (W k)).injOn
  let xs : List ℝ := hP_param_fin.toFinset.sort (· ≤ ·)
  have hxs_sorted : xs.SortedLT := Finset.sortedLT_sort _
  have hxs_iff : ∀ s : ℝ, s ∈ xs ↔ gammaParam (W k) s ∈ P_set := fun s => by
    simp [xs, P_param]
  let α : Fin (xs.length + 1) → Set (ℝ × ℝ) := fun i => gammaParam (W k) '' seg xs i
  let U_step : ℕ → Set (ℝ × ℝ) := fun m =>
    U₀ \ ⋃ (i : Fin (xs.length + 1)) (_ : i.val < m), α i
  have hU_step_open : ∀ m, IsOpen (U_step m) := by
    intro m
    let I : Finset (Fin (xs.length + 1)) := Finset.univ.filter (fun i => i.val < m)
    let S_cl : Set ℝ := ⋃ i ∈ (I : Set (Fin (xs.length + 1))), closure (seg xs i)
    have hS_cl : IsClosed S_cl :=
      I.finite_toSet.isClosed_biUnion fun _ _ => isClosed_closure
    let K_cl : Set (ℝ × ℝ) := gammaParam (W k) '' S_cl
    have hK_cl : IsClosed K_cl := gammaParam_image_isClosed (W k) hS_cl
    have hEq : U_step m = U₀ \ K_cl := by
      ext p; constructor
      · rintro ⟨hpU₀, hp_not⟩
        refine ⟨hpU₀, ?_⟩
        rintro ⟨s, hs, rfl⟩
        rw [Set.mem_iUnion₂] at hs
        rcases hs with ⟨i, hiI, hsi⟩
        rcases closure_seg_subset xs i hsi with hseg | hmem_xs
        · exact hp_not (Set.mem_iUnion₂.mpr ⟨i, (Finset.mem_filter.mp (Finset.mem_coe.mp hiI)).2,
            ⟨s, hseg, rfl⟩⟩)
        · have hP := (hxs_iff s).mp hmem_xs
          rw [Set.mem_iUnion₂] at hP
          rcases hP with ⟨j, hjS, _, hjG⟩
          exact hpU₀.2 (Set.mem_iUnion₂.mpr ⟨j, hjS, hjG⟩)
      · rintro ⟨hpU₀, hp_not⟩
        refine ⟨hpU₀, fun hmem => hp_not ?_⟩
        rw [Set.mem_iUnion₂] at hmem
        rcases hmem with ⟨i, him, ⟨s, hsi, rfl⟩⟩
        refine ⟨s, Set.mem_iUnion₂.mpr ⟨i, ?_, subset_closure hsi⟩, rfl⟩
        exact Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ i, him⟩)
    rw [hEq]
    exact hU₀_open.sdiff hK_cl
  have h_step : ∀ m : ℕ, m ≤ xs.length + 1 →
      (Comps (U_step m)).encard ≤ (Comps U₀).encard + (m : ℕ∞) := by
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
          refine ⟨⟨hpU₀, fun h => hp_not ?_⟩, fun h => hp_not ?_⟩
          · rw [Set.mem_iUnion₂] at h ⊢
            rcases h with ⟨j, hj, hpj⟩
            exact ⟨j, Nat.lt_succ_of_lt hj, hpj⟩
          · exact Set.mem_iUnion₂.mpr ⟨i, Nat.lt_succ_self m, h⟩
        · rintro ⟨⟨hpU₀, hp_not⟩, hp_ni⟩
          refine ⟨hpU₀, fun h => ?_⟩
          rw [Set.mem_iUnion₂] at h
          rcases h with ⟨j, hj, hpj⟩
          rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj' | hj'
          · exact hp_not (Set.mem_iUnion₂.mpr ⟨j, hj', hpj⟩)
          · have hji : j = i := Fin.ext hj'
            rw [hji] at hpj
            exact hp_ni hpj
      have hi_sub : α i ⊆ U_step m := by
        rintro p ⟨s, hs, rfl⟩
        refine ⟨⟨trivial, fun hU => ?_⟩, fun hprev => ?_⟩
        · rw [Set.mem_iUnion₂] at hU
          rcases hU with ⟨j, hjS, hjG⟩
          have hP : gammaParam (W k) s ∈ P_set :=
            Set.mem_iUnion₂.mpr ⟨j, hjS, gammaParam_mem_bdWedge (W k) s, hjG⟩
          exact seg_disjoint_list xs hxs_sorted i hs ((hxs_iff s).mpr hP)
        · rw [Set.mem_iUnion₂] at hprev
          rcases hprev with ⟨j, hj, ⟨s', hs', heq⟩⟩
          have hij : j ≠ i := fun h => by rw [h] at hj; exact Nat.lt_irrefl m hj
          have hs_eq : s' = s := gammaParam_injective (W k) heq
          rw [hs_eq] at hs'
          exact Set.disjoint_left.mp (seg_pairwise_disjoint xs hij) hs' hs
      have h_inc : (Comps (U_step (m + 1))).encard ≤ (Comps (U_step m)).encard + 1 := by
        rw [h_split]
        exact remove_seg_arc_comps (W k) (U_step m) (hU_step_open m)
          xs hxs_sorted i hi_sub (h_split ▸ hU_step_open (m + 1))
      calc (Comps (U_step (m + 1))).encard
          ≤ (Comps (U_step m)).encard + 1 := h_inc
        _ ≤ ((Comps U₀).encard + (m : ℕ∞)) + 1 := add_le_add (ih (Nat.le_of_lt hm')) le_rfl
        _ = (Comps U₀).encard + ((m + 1 : ℕ) : ℕ∞) := by
            rw [Nat.cast_add, Nat.cast_one, add_assoc]
  have h_final_eq : (Set.univ : Set (ℝ × ℝ)) \ ⋃ j ∈ insert k S, bdWedge (W j) =
      U_step (xs.length + 1) := by
    ext p; constructor
    · rintro ⟨hp_om, hp_not⟩
      refine ⟨⟨hp_om, fun h => hp_not ?_⟩, fun h => hp_not ?_⟩
      · rw [Set.mem_iUnion₂] at h ⊢
        rcases h with ⟨j, hj, hpj⟩
        exact ⟨j, Finset.mem_insert_of_mem hj, hpj⟩
      · rw [Set.mem_iUnion₂] at h
        rcases h with ⟨i, _, ⟨s, _, rfl⟩⟩
        exact Set.mem_iUnion₂.mpr ⟨k, Finset.mem_insert_self k S, gammaParam_mem_bdWedge (W k) s⟩
    · rintro ⟨⟨hp_om, hp_notS⟩, hp_not_seg⟩
      refine ⟨hp_om, fun h => ?_⟩
      rw [Set.mem_iUnion₂] at h
      rcases h with ⟨j, hj, hpj⟩
      rcases Finset.mem_insert.mp hj with hjk | hjS
      · rw [hjk, ← gammaParam_range (W k)] at hpj
        obtain ⟨s, rfl⟩ := hpj
        have hs_nxs : s ∉ xs := by
          intro hmem
          have hP := (hxs_iff s).mp hmem
          rw [Set.mem_iUnion₂] at hP
          rcases hP with ⟨j', hj', _, hjG⟩
          exact hp_notS (Set.mem_iUnion₂.mpr ⟨j', hj', hjG⟩)
        have hmem_seg := compl_list_subset_iUnion_seg xs hs_nxs
        rw [Set.mem_iUnion] at hmem_seg
        obtain ⟨i, hsi⟩ := hmem_seg
        exact hp_not_seg (Set.mem_iUnion₂.mpr ⟨i, i.isLt, ⟨s, hsi, rfl⟩⟩)
      · exact hp_notS (Set.mem_iUnion₂.mpr ⟨j, hjS, hpj⟩)
  have h_len_bound : xs.length ≤ ∑ j ∈ S, (bdWedge (W k) ∩ bdWedge (W j)).ncard := by
    have h1 : xs.length = hP_param_fin.toFinset.card := Finset.length_sort (· ≤ ·)
    have h2 : (hP_param_fin.toFinset.card : ℕ) = P_param.ncard :=
      (Set.ncard_eq_toFinset_card P_param hP_param_fin).symm
    have h3 : P_param.ncard ≤ P_set.ncard := by
      have himg : gammaParam (W k) '' P_param ⊆ P_set := Set.image_preimage_subset _ _
      rw [← Set.ncard_image_of_injective P_param (gammaParam_injective (W k))]
      exact Set.ncard_le_ncard himg hP_fin
    have h4 : P_set.ncard ≤ ∑ j ∈ S, (bdWedge (W k) ∩ bdWedge (W j)).ncard :=
      biUnion_ncard_le_sum S (fun j => bdWedge (W k) ∩ bdWedge (W j))
        fun j hj => (inter_card_le_four hGP (ne_of_mem_of_not_mem hj hkS).symm).1
    omega
  rw [h_final_eq]
  have h_fin := h_step (xs.length + 1) le_rfl
  have h_enat : ((xs.length + 1 : ℕ) : ℕ∞) ≤
      1 + ∑ j ∈ S, ((bdWedge (W k) ∩ bdWedge (W j)).ncard : ℕ∞) := by
    have h_sum_coe : (∑ j ∈ S, ((bdWedge (W k) ∩ bdWedge (W j)).ncard : ℕ∞)) =
        ((∑ j ∈ S, (bdWedge (W k) ∩ bdWedge (W j)).ncard : ℕ) : ℕ∞) := by
      push_cast; rfl
    rw [h_sum_coe, add_comm (1 : ℕ∞)]
    calc ((xs.length + 1 : ℕ) : ℕ∞)
        ≤ (((∑ j ∈ S, (bdWedge (W k) ∩ bdWedge (W j)).ncard) + 1 : ℕ) : ℕ∞) :=
          Nat.cast_le.mpr (by omega)
      _ = ((∑ j ∈ S, (bdWedge (W k) ∩ bdWedge (W j)).ncard : ℕ) : ℕ∞) + 1 := by
          push_cast; rfl
  calc (Comps (U_step (xs.length + 1))).encard
      ≤ (Comps U₀).encard + ((xs.length + 1 : ℕ) : ℕ∞) := h_fin
    _ ≤ (Comps U₀).encard + (1 + ∑ j ∈ S, ((bdWedge (W k) ∩ bdWedge (W j)).ncard : ℕ∞)) :=
        add_le_add le_rfl h_enat
    _ = (Comps U₀).encard + 1 + ∑ j ∈ S, ((bdWedge (W k) ∩ bdWedge (W j)).ncard : ℕ∞) := by
        rw [add_assoc]

lemma arr_comps_bound_univ {W : Fin 6 → OpenWedge} (hGP : GP6 W) (S : Finset (Fin 6)) :
    (Comps ((Set.univ : Set (ℝ × ℝ)) \ ⋃ j ∈ S, bdWedge (W j))).encard ≤
    1 + (S.card : ℕ∞) +
      ∑ i ∈ S, ∑ j ∈ S with i < j, ((bdWedge (W i) ∩ bdWedge (W j)).ncard : ℕ∞) := by
  induction S using Finset.induction with
  | empty =>
    simp only [Finset.notMem_empty, Set.iUnion_of_empty, Set.iUnion_empty, Set.sdiff_empty,
      Finset.card_empty, CharP.cast_eq_zero, add_zero, Finset.sum_empty]
    exact comps_univ_card.le
  | @insert k S' hkS ih =>
    have h_add := add_wedge_comps_bound_univ hGP S' k hkS
    have h_sum_eq : ∑ i ∈ insert k S', ∑ j ∈ insert k S' with i < j,
          ((bdWedge (W i) ∩ bdWedge (W j)).ncard : ℕ∞) =
        (∑ i ∈ S', ∑ j ∈ S' with i < j, ((bdWedge (W i) ∩ bdWedge (W j)).ncard : ℕ∞)) +
          ∑ j ∈ S', ((bdWedge (W k) ∩ bdWedge (W j)).ncard : ℕ∞) := by
      have h_in : ∀ i ∈ S', (∑ j ∈ (insert k S').filter (i < ·),
            ((bdWedge (W i) ∩ bdWedge (W j)).ncard : ℕ∞)) =
          (∑ j ∈ S'.filter (i < ·), ((bdWedge (W i) ∩ bdWedge (W j)).ncard : ℕ∞)) +
          (if i < k then ((bdWedge (W i) ∩ bdWedge (W k)).ncard : ℕ∞) else 0) := by
        intro i _
        rw [Finset.filter_insert]
        split_ifs with hik
        · rw [Finset.sum_insert (fun h => hkS (Finset.mem_filter.mp h).1), add_comm]
        · rw [add_zero]
      rw [Finset.sum_insert hkS]
      have h_k : (∑ j ∈ (insert k S').filter (k < ·), ((bdWedge (W k) ∩ bdWedge (W j)).ncard : ℕ∞)) =
          ∑ j ∈ S', if k < j then ((bdWedge (W k) ∩ bdWedge (W j)).ncard : ℕ∞) else 0 := by
        rw [Finset.filter_insert, if_neg (lt_irrefl k), Finset.sum_filter]
      have h_S : (∑ i ∈ S', ∑ j ∈ (insert k S').filter (i < ·),
            ((bdWedge (W i) ∩ bdWedge (W j)).ncard : ℕ∞)) =
          (∑ i ∈ S', ∑ j ∈ S'.filter (i < ·), ((bdWedge (W i) ∩ bdWedge (W j)).ncard : ℕ∞)) +
          ∑ i ∈ S', if i < k then ((bdWedge (W i) ∩ bdWedge (W k)).ncard : ℕ∞) else 0 := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl h_in
      rw [h_k, h_S]
      have h_pair : (∑ j ∈ S', if k < j then ((bdWedge (W k) ∩ bdWedge (W j)).ncard : ℕ∞) else 0) +
          (∑ i ∈ S', if i < k then ((bdWedge (W i) ∩ bdWedge (W k)).ncard : ℕ∞) else 0) =
          ∑ j ∈ S', ((bdWedge (W k) ∩ bdWedge (W j)).ncard : ℕ∞) := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun j hj => ?_
        have hne : j ≠ k := ne_of_mem_of_not_mem hj hkS
        rcases lt_or_gt_of_ne hne with hjk | hkj
        · rw [if_neg (not_lt.mpr (le_of_lt hjk)), if_pos hjk, zero_add, Set.inter_comm]
        · rw [if_pos hkj, if_neg (not_lt.mpr (le_of_lt hkj)), add_zero]
      rw [← add_assoc, add_comm (∑ j ∈ S', if k < j then _ else _), add_assoc, h_pair]
    calc (Comps ((Set.univ : Set (ℝ × ℝ)) \ ⋃ j ∈ insert k S', bdWedge (W j))).encard
        ≤ (Comps ((Set.univ : Set (ℝ × ℝ)) \ ⋃ j ∈ S', bdWedge (W j))).encard +
            1 + ∑ j ∈ S', ((bdWedge (W k) ∩ bdWedge (W j)).ncard : ℕ∞) := h_add
      _ ≤ (1 + (S'.card : ℕ∞) +
            ∑ i ∈ S', ∑ j ∈ S' with i < j, ((bdWedge (W i) ∩ bdWedge (W j)).ncard : ℕ∞)) +
            1 + ∑ j ∈ S', ((bdWedge (W k) ∩ bdWedge (W j)).ncard : ℕ∞) :=
          add_le_add (add_le_add ih le_rfl) le_rfl
      _ = 1 + ((insert k S').card : ℕ∞) +
            ∑ i ∈ insert k S', ∑ j ∈ insert k S' with i < j,
              ((bdWedge (W i) ∩ bdWedge (W j)).ncard : ℕ∞) := by
          rw [Finset.card_insert_of_notMem hkS, Nat.cast_add, Nat.cast_one, h_sum_eq]
          simp only [add_assoc, add_left_comm]

/-! ## Part 3: Four Crossings Imply Disjoint Cones and Ray-Pair Intersection -/

lemma quad_four_inter_rays_univ {W : Fin 6 → OpenWedge} (hGP : GP6 W)
    {i j : Fin 6} (hij : i ≠ j)
    (h4 : ¬ (bdWedge (W i) ∩ bdWedge (W j)).ncard ≤ 3) :
    ∀ bi bj : Bool, ∃ ti > 0, ∃ tj > 0,
      (if bi then ray1 (W i) ti else ray2 (W i) ti) =
      (if bj then ray1 (W j) tj else ray2 (W j) tj) := by
  have huniq : ∀ (bi bj : Bool), ∃ p₀ : ℝ × ℝ,
      lineAt W (i, bi) p₀ = 0 ∧ lineAt W (j, bj) p₀ = 0 ∧
      (∀ p : ℝ × ℝ, lineAt W (i, bi) p = 0 → lineAt W (j, bj) p = 0 → p = p₀) := by
    intro bi bj
    have hne : (i, bi) ≠ (j, bj) := fun h => hij (congrArg Prod.fst h)
    have hdet := hGP.no_parallel (i, bi) (j, bj) hne
    let a1 := (normal W (i, bi)).1; let a2 := (normal W (i, bi)).2
    let b1 := (normal W (j, bj)).1; let b2 := (normal W (j, bj)).2
    let ca := a1 * (W i).y.1 + a2 * (W i).y.2
    let cb := b1 * (W j).y.1 + b2 * (W j).y.2
    let det := a1 * b2 - a2 * b1
    have hdet' : det ≠ 0 := hdet
    refine ⟨((b2 * ca - a2 * cb) / det, (-b1 * ca + a1 * cb) / det), ?_, ?_, fun p hp1 hp2 => ?_⟩
    · dsimp [lineAt]
      change a1 * ((b2 * ca - a2 * cb) / det - (W i).y.1) +
             a2 * ((-b1 * ca + a1 * cb) / det - (W i).y.2) = 0
      field_simp [hdet']; dsimp [det, ca, cb]; ring
    · dsimp [lineAt]
      change b1 * ((b2 * ca - a2 * cb) / det - (W j).y.1) +
             b2 * ((-b1 * ca + a1 * cb) / det - (W j).y.2) = 0
      field_simp [hdet']; dsimp [det, ca, cb]; ring
    · dsimp [lineAt] at hp1 hp2
      have h1 : det * p.1 = b2 * ca - a2 * cb := by
        change (a1 * b2 - a2 * b1) * p.1 = b2 * (a1 * (W i).y.1 + a2 * (W i).y.2) -
          a2 * (b1 * (W j).y.1 + b2 * (W j).y.2)
        linear_combination b2 * hp1 - a2 * hp2
      have h2 : det * p.2 = -b1 * ca + a1 * cb := by
        change (a1 * b2 - a2 * b1) * p.2 = -b1 * (a1 * (W i).y.1 + a2 * (W i).y.2) +
          a1 * (b1 * (W j).y.1 + b2 * (W j).y.2)
        linear_combination -b1 * hp1 + a1 * hp2
      ext
      · exact (eq_div_iff hdet').mpr (by rw [mul_comm]; exact h1)
      · exact (eq_div_iff hdet').mpr (by rw [mul_comm]; exact h2)
  let pt (bi bj : Bool) : ℝ × ℝ := (huniq bi bj).choose
  have hpt1 : ∀ bi bj, lineAt W (i, bi) (pt bi bj) = 0 := fun bi bj => (huniq bi bj).choose_spec.1
  have hpt2 : ∀ bi bj, lineAt W (j, bj) (pt bi bj) = 0 := fun bi bj => (huniq bi bj).choose_spec.2.1
  have hpt : ∀ bi bj p, lineAt W (i, bi) p = 0 → lineAt W (j, bj) p = 0 → p = pt bi bj :=
    fun bi bj => (huniq bi bj).choose_spec.2.2
  let S4 : Finset (ℝ × ℝ) := {pt true true, pt true false, pt false true, pt false false}
  have hsub : bdWedge (W i) ∩ bdWedge (W j) ⊆ (S4 : Set (ℝ × ℝ)) := by
    rintro p ⟨hi, hj⟩
    obtain ⟨_, hi_eq⟩ := (bdWedge_iff_closure_eq_zero (W i) p).mp hi
    obtain ⟨_, hj_eq⟩ := (bdWedge_iff_closure_eq_zero (W j) p).mp hj
    rcases hi_eq with hi1 | hi2 <;> rcases hj_eq with hj1 | hj2
    · have := hpt true true p (by simpa [lineAt, normal] using hi1) (by simpa [lineAt, normal] using hj1)
      simp [S4, this]
    · have := hpt true false p (by simpa [lineAt, normal] using hi1) (by simpa [lineAt, normal] using hj2)
      simp [S4, this]
    · have := hpt false true p (by simpa [lineAt, normal] using hi2) (by simpa [lineAt, normal] using hj1)
      simp [S4, this]
    · have := hpt false false p (by simpa [lineAt, normal] using hi2) (by simpa [lineAt, normal] using hj2)
      simp [S4, this]
  have hmem_all : ∀ bi bj : Bool, pt bi bj ∈ bdWedge (W i) ∩ bdWedge (W j) := by
    intro bi bj
    by_contra hnot
    let S3 : Finset (ℝ × ℝ) := S4.erase (pt bi bj)
    have hsub3 : bdWedge (W i) ∩ bdWedge (W j) ⊆ (S3 : Set (ℝ × ℝ)) := by
      intro p hp
      exact Finset.mem_coe.mpr (Finset.mem_erase.mpr ⟨fun heq => hnot (heq ▸ hp), hsub hp⟩)
    have hpt_mem : pt bi bj ∈ S4 := by cases bi <;> cases bj <;> simp [S4]
    have hcard4 : S4.card ≤ 4 := by
      dsimp [S4]
      exact (Finset.card_insert_le _ _).trans (Nat.succ_le_succ
        ((Finset.card_insert_le _ _).trans (Nat.succ_le_succ
          ((Finset.card_insert_le _ _).trans (Nat.succ_le_succ (by simp))))))
    have hcard3 : S3.card ≤ 3 := by
      have hcard_eq := Finset.card_erase_add_one hpt_mem
      change S3.card + 1 = S4.card at hcard_eq
      omega
    have hle3 : (bdWedge (W i) ∩ bdWedge (W j)).ncard ≤ 3 := by
      calc (bdWedge (W i) ∩ bdWedge (W j)).ncard
          ≤ (S3 : Set (ℝ × ℝ)).ncard := Set.ncard_le_ncard hsub3 S3.finite_toSet
        _ = S3.card := Set.ncard_coe_finset S3
        _ ≤ 3 := hcard3
    exact h4 hle3
  intro bi bj
  obtain ⟨hi_bd, hj_bd⟩ := hmem_all bi bj
  have hi_neq : pt bi bj ≠ (W i).y := by
    intro heq
    obtain ⟨_, hj_eq⟩ := (bdWedge_iff_closure_eq_zero (W j) (pt bi bj)).mp hj_bd
    rw [heq] at hj_eq
    rcases hj_eq with h1 | h2
    · exact hGP.apex_not_on_line i j hij true (by simpa [lineAt, normal] using h1)
    · exact hGP.apex_not_on_line i j hij false (by simpa [lineAt, normal] using h2)
  have hj_neq : pt bi bj ≠ (W j).y := by
    intro heq
    obtain ⟨_, hi_eq⟩ := (bdWedge_iff_closure_eq_zero (W i) (pt bi bj)).mp hi_bd
    rw [heq] at hi_eq
    rcases hi_eq with h1 | h2
    · exact hGP.apex_not_on_line j i hij.symm true (by simpa [lineAt, normal] using h1)
    · exact hGP.apex_not_on_line j i hij.symm false (by simpa [lineAt, normal] using h2)
  have hi_ray : ∃ ti > 0, pt bi bj = if bi then ray1 (W i) ti else ray2 (W i) ti := by
    have hnd := (W i).h_nondeg
    rcases (bdWedge_iff_rays (W i) (pt bi bj)).mp hi_bd with ⟨t, ht, hpt_eq⟩ | ⟨t, ht, hpt_eq⟩
    · have ht_pos : 0 < t := lt_of_le_of_ne ht fun ht0 => by
        apply hi_neq; rw [hpt_eq, ← ht0]; simp [ray1]
      cases bi with
      | true => exact ⟨t, ht_pos, hpt_eq⟩
      | false =>
        have hfalse := hpt1 false bj
        rw [hpt_eq] at hfalse
        have hval : lineAt W (i, false) (ray1 (W i) t) =
            t * ((W i).u₁.1 * (W i).u₂.2 - (W i).u₁.2 * (W i).u₂.1) := by
          dsimp [lineAt, normal, ray1, dir1]; ring
        rw [hval] at hfalse
        have hmul : 0 < t * ((W i).u₁.1 * (W i).u₂.2 - (W i).u₁.2 * (W i).u₂.1) := mul_pos ht_pos hnd
        linarith
    · have ht_pos : 0 < t := lt_of_le_of_ne ht fun ht0 => by
        apply hi_neq; rw [hpt_eq, ← ht0]; simp [ray2]
      cases bi with
      | true =>
        have htrue := hpt1 true bj
        rw [hpt_eq] at htrue
        have hval : lineAt W (i, true) (ray2 (W i) t) =
            t * ((W i).u₁.1 * (W i).u₂.2 - (W i).u₁.2 * (W i).u₂.1) := by
          dsimp [lineAt, normal, ray2, dir2]; ring
        rw [hval] at htrue
        have hmul : 0 < t * ((W i).u₁.1 * (W i).u₂.2 - (W i).u₁.2 * (W i).u₂.1) := mul_pos ht_pos hnd
        linarith
      | false => exact ⟨t, ht_pos, hpt_eq⟩
  have hj_ray : ∃ tj > 0, pt bi bj = if bj then ray1 (W j) tj else ray2 (W j) tj := by
    have hnd := (W j).h_nondeg
    rcases (bdWedge_iff_rays (W j) (pt bi bj)).mp hj_bd with ⟨t, ht, hpt_eq⟩ | ⟨t, ht, hpt_eq⟩
    · have ht_pos : 0 < t := lt_of_le_of_ne ht fun ht0 => by
        apply hj_neq; rw [hpt_eq, ← ht0]; simp [ray1]
      cases bj with
      | true => exact ⟨t, ht_pos, hpt_eq⟩
      | false =>
        have hfalse := hpt2 bi false
        rw [hpt_eq] at hfalse
        have hval : lineAt W (j, false) (ray1 (W j) t) =
            t * ((W j).u₁.1 * (W j).u₂.2 - (W j).u₁.2 * (W j).u₂.1) := by
          dsimp [lineAt, normal, ray1, dir1]; ring
        rw [hval] at hfalse
        have hmul : 0 < t * ((W j).u₁.1 * (W j).u₂.2 - (W j).u₁.2 * (W j).u₂.1) := mul_pos ht_pos hnd
        linarith
    · have ht_pos : 0 < t := lt_of_le_of_ne ht fun ht0 => by
        apply hj_neq; rw [hpt_eq, ← ht0]; simp [ray2]
      cases bj with
      | true =>
        have htrue := hpt2 bi true
        rw [hpt_eq] at htrue
        have hval : lineAt W (j, true) (ray2 (W j) t) =
            t * ((W j).u₁.1 * (W j).u₂.2 - (W j).u₁.2 * (W j).u₂.1) := by
          dsimp [lineAt, normal, ray2, dir2]; ring
        rw [hval] at htrue
        have hmul : 0 < t * ((W j).u₁.1 * (W j).u₂.2 - (W j).u₁.2 * (W j).u₂.1) := mul_pos ht_pos hnd
        linarith
      | false => exact ⟨t, ht_pos, hpt_eq⟩
  obtain ⟨ti, hti, heqi⟩ := hi_ray
  obtain ⟨tj, htj, heqj⟩ := hj_ray
  exact ⟨ti, hti, tj, htj, heqi.symm.trans heqj⟩

def closureConeMem (W : OpenWedge) (d : ℝ × ℝ) : Prop :=
  0 ≤ W.u₁.1 * d.1 + W.u₁.2 * d.2 ∧ 0 ≤ W.u₂.1 * d.1 + W.u₂.2 * d.2

private lemma closureConeMem_coords (W : OpenWedge) (d : ℝ × ℝ) (hd : closureConeMem W d) :
    ∃ c1 c2 : ℝ, 0 ≤ c1 ∧ 0 ≤ c2 ∧
      d.1 = c1 * (dir1 W).1 + c2 * (dir2 W).1 ∧
      d.2 = c1 * (dir1 W).2 + c2 * (dir2 W).2 := by
  have hnd := W.h_nondeg
  let Δ := W.u₁.1 * W.u₂.2 - W.u₁.2 * W.u₂.1
  have hΔ : Δ ≠ 0 := ne_of_gt hnd
  let c1 := (W.u₂.1 * d.1 + W.u₂.2 * d.2) / Δ
  let c2 := (W.u₁.1 * d.1 + W.u₁.2 * d.2) / Δ
  refine ⟨c1, c2, div_nonneg hd.2 (le_of_lt hnd), div_nonneg hd.1 (le_of_lt hnd), ?_, ?_⟩
  · dsimp [c1, c2, dir1, dir2]; field_simp [hΔ]; dsimp [Δ]; ring
  · dsimp [c1, c2, dir1, dir2]; field_simp [hΔ]; dsimp [Δ]; ring

private lemma quad_four_ray_slopes_univ (Wi Wj : OpenWedge)
    (hrays : ∀ bi bj : Bool, ∃ ti > 0, ∃ tj > 0,
      (if bi then ray1 Wi ti else ray2 Wi ti) =
      (if bj then ray1 Wj tj else ray2 Wj tj)) :
    let s11 := Wj.u₁.1 * (dir1 Wi).1 + Wj.u₁.2 * (dir1 Wi).2
    let s12 := Wj.u₂.1 * (dir1 Wi).1 + Wj.u₂.2 * (dir1 Wi).2
    let s21 := Wj.u₁.1 * (dir2 Wi).1 + Wj.u₁.2 * (dir2 Wi).2
    let s22 := Wj.u₂.1 * (dir2 Wi).1 + Wj.u₂.2 * (dir2 Wi).2
    ((0 < s11 ∧ s12 < 0 ∧ 0 < s21 ∧ s22 < 0) ∨
     (s11 < 0 ∧ 0 < s12 ∧ s21 < 0 ∧ 0 < s22)) := by
  intro s11 s12 s21 s22
  let a1 := Wj.u₁.1 * (Wi.y.1 - Wj.y.1) + Wj.u₁.2 * (Wi.y.2 - Wj.y.2)
  let a2 := Wj.u₂.1 * (Wi.y.1 - Wj.y.1) + Wj.u₂.2 * (Wi.y.2 - Wj.y.2)
  obtain ⟨t11, ht11, tj11, htj11, heq11⟩ := hrays true true
  obtain ⟨t12, ht12, tj12, htj12, heq12⟩ := hrays true false
  obtain ⟨t21, ht21, tj21, htj21, heq21⟩ := hrays false true
  obtain ⟨t22, ht22, tj22, htj22, heq22⟩ := hrays false false
  simp only [ite_true, ite_false, Bool.false_eq_true] at heq11 heq12 heq21 heq22
  have hndj := Wj.h_nondeg
  have e_l1_r1 : ∀ t, Wj.u₁.1 * ((ray1 Wi t).1 - Wj.y.1) + Wj.u₁.2 * ((ray1 Wi t).2 - Wj.y.2) = a1 + t * s11 := by
    intro t; dsimp [a1, s11, ray1]; ring
  have e_l2_r1 : ∀ t, Wj.u₂.1 * ((ray1 Wi t).1 - Wj.y.1) + Wj.u₂.2 * ((ray1 Wi t).2 - Wj.y.2) = a2 + t * s12 := by
    intro t; dsimp [a2, s12, ray1]; ring
  have e_l1_r2 : ∀ t, Wj.u₁.1 * ((ray2 Wi t).1 - Wj.y.1) + Wj.u₁.2 * ((ray2 Wi t).2 - Wj.y.2) = a1 + t * s21 := by
    intro t; dsimp [a1, s21, ray2]; ring
  have e_l2_r2 : ∀ t, Wj.u₂.1 * ((ray2 Wi t).1 - Wj.y.1) + Wj.u₂.2 * ((ray2 Wi t).2 - Wj.y.2) = a2 + t * s22 := by
    intro t; dsimp [a2, s22, ray2]; ring
  have z11 : a1 + t11 * s11 = 0 := by rw [← e_l1_r1, heq11]; dsimp [ray1, dir1]; ring
  have p11 : 0 < a2 + t11 * s12 := by
    rw [← e_l2_r1, heq11]
    have : Wj.u₂.1 * ((ray1 Wj tj11).1 - Wj.y.1) + Wj.u₂.2 * ((ray1 Wj tj11).2 - Wj.y.2) =
        tj11 * (Wj.u₁.1 * Wj.u₂.2 - Wj.u₁.2 * Wj.u₂.1) := by dsimp [ray1, dir1]; ring
    rw [this]; exact mul_pos htj11 hndj
  have z12 : a2 + t12 * s12 = 0 := by rw [← e_l2_r1, heq12]; dsimp [ray2, dir2]; ring
  have p12 : 0 < a1 + t12 * s11 := by
    rw [← e_l1_r1, heq12]
    have : Wj.u₁.1 * ((ray2 Wj tj12).1 - Wj.y.1) + Wj.u₁.2 * ((ray2 Wj tj12).2 - Wj.y.2) =
        tj12 * (Wj.u₁.1 * Wj.u₂.2 - Wj.u₁.2 * Wj.u₂.1) := by dsimp [ray2, dir2]; ring
    rw [this]; exact mul_pos htj12 hndj
  have z21 : a1 + t21 * s21 = 0 := by rw [← e_l1_r2, heq21]; dsimp [ray1, dir1]; ring
  have p21 : 0 < a2 + t21 * s22 := by
    rw [← e_l2_r2, heq21]
    have : Wj.u₂.1 * ((ray1 Wj tj21).1 - Wj.y.1) + Wj.u₂.2 * ((ray1 Wj tj21).2 - Wj.y.2) =
        tj21 * (Wj.u₁.1 * Wj.u₂.2 - Wj.u₁.2 * Wj.u₂.1) := by dsimp [ray1, dir1]; ring
    rw [this]; exact mul_pos htj21 hndj
  have z22 : a2 + t22 * s22 = 0 := by rw [← e_l2_r2, heq22]; dsimp [ray2, dir2]; ring
  have p22 : 0 < a1 + t22 * s21 := by
    rw [← e_l1_r2, heq22]
    have : Wj.u₁.1 * ((ray2 Wj tj22).1 - Wj.y.1) + Wj.u₁.2 * ((ray2 Wj tj22).2 - Wj.y.2) =
        tj22 * (Wj.u₁.1 * Wj.u₂.2 - Wj.u₁.2 * Wj.u₂.1) := by dsimp [ray2, dir2]; ring
    rw [this]; exact mul_pos htj22 hndj
  have hs11_ne : s11 ≠ 0 := by intro h0; rw [h0, mul_zero, add_zero] at z11 p12; linarith
  have hs12_ne : s12 ≠ 0 := by intro h0; rw [h0, mul_zero, add_zero] at z12 p11; linarith
  have hs21_ne : s21 ≠ 0 := by intro h0; rw [h0, mul_zero, add_zero] at z21 p22; linarith
  have hs22_ne : s22 ≠ 0 := by intro h0; rw [h0, mul_zero, add_zero] at z22 p21; linarith
  rcases lt_or_gt_of_ne hs11_ne with hs11 | hs11
  · right
    have ha1 : 0 < a1 := by
      have : 0 < -(t11 * s11) := neg_pos.mpr (mul_neg_of_pos_of_neg ht11 hs11)
      linarith
    have hs21 : s21 < 0 := by
      by_contra hge
      have : 0 ≤ t21 * s21 := mul_nonneg (le_of_lt ht21) (not_lt.mp hge)
      linarith
    have hlt_t : t12 < t11 := by
      have hsub : 0 < (t12 - t11) * s11 := by linarith
      by_contra hge
      have : (t12 - t11) * s11 ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by linarith) (le_of_lt hs11)
      linarith
    have hs12 : 0 < s12 := by
      have hsub : 0 < (t11 - t12) * s12 := by linarith
      by_contra hle
      have : (t11 - t12) * s12 ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by linarith) (not_lt.mp hle)
      linarith
    have ha2 : a2 < 0 := by
      have : 0 < t12 * s12 := mul_pos ht12 hs12
      linarith
    have hs22 : 0 < s22 := by
      by_contra hle
      have : t22 * s22 ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (le_of_lt ht22) (not_lt.mp hle)
      linarith
    exact ⟨hs11, hs12, hs21, hs22⟩
  · left
    have ha1 : a1 < 0 := by
      have : 0 < t11 * s11 := mul_pos ht11 hs11
      linarith
    have hs21 : 0 < s21 := by
      by_contra hle
      have : t21 * s21 ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (le_of_lt ht21) (not_lt.mp hle)
      linarith
    have hlt_t : t11 < t12 := by
      have hsub : 0 < (t12 - t11) * s11 := by linarith
      by_contra hle
      have : (t12 - t11) * s11 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) (le_of_lt hs11)
      linarith
    have hs12 : s12 < 0 := by
      have hsub : 0 < (t11 - t12) * s12 := by linarith
      by_contra hge
      have : (t11 - t12) * s12 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) (not_lt.mp hge)
      linarith
    have ha2 : 0 < a2 := by
      have : 0 < -(t12 * s12) := neg_pos.mpr (mul_neg_of_pos_of_neg ht12 hs12)
      linarith
    have hs22 : s22 < 0 := by
      by_contra hge
      have : 0 ≤ t22 * s22 := mul_nonneg (le_of_lt ht22) (not_lt.mp hge)
      linarith
    exact ⟨hs11, hs12, hs21, hs22⟩

lemma quad_four_disjoint_cones {W : Fin 6 → OpenWedge} (hGP : GP6 W)
    {i j : Fin 6} (hij : i ≠ j)
    (h4 : ¬ (bdWedge (W i) ∩ bdWedge (W j)).ncard ≤ 3)
    {d : ℝ × ℝ} (hd_ne : d ≠ (0, 0)) :
    ¬ (closureConeMem (W i) d ∧ closureConeMem (W j) d) := by
  rintro ⟨hdi, hdj⟩
  obtain ⟨c1, c2, hc1, hc2, hd1, hd2⟩ := closureConeMem_coords (W i) d hdi
  have hnot00 : ¬ (c1 = 0 ∧ c2 = 0) := by
    rintro ⟨rfl, rfl⟩
    apply hd_ne; ext <;> simp [hd1, hd2]
  have hrays := quad_four_inter_rays_univ hGP hij h4
  rcases quad_four_ray_slopes_univ (W i) (W j) hrays with
      ⟨hs11, hs12, hs21, hs22⟩ | ⟨hs11, hs12, hs21, hs22⟩
  · have hlin : (W j).u₂.1 * d.1 + (W j).u₂.2 * d.2 =
        c1 * ((W j).u₂.1 * (dir1 (W i)).1 + (W j).u₂.2 * (dir1 (W i)).2) +
        c2 * ((W j).u₂.1 * (dir2 (W i)).1 + (W j).u₂.2 * (dir2 (W i)).2) := by
      rw [hd1, hd2]; ring
    have hlt0 : (W j).u₂.1 * d.1 + (W j).u₂.2 * d.2 < 0 := by
      rw [hlin]
      rcases eq_or_lt_of_le hc1 with rfl | hc1p
      · have hc2p : 0 < c2 := lt_of_le_of_ne hc2 (fun h => hnot00 ⟨rfl, h.symm⟩)
        nlinarith
      · have h2np : c2 * ((W j).u₂.1 * (dir2 (W i)).1 + (W j).u₂.2 * (dir2 (W i)).2) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos hc2 (le_of_lt hs22)
        nlinarith
    linarith [hdj.2]
  · have hlin : (W j).u₁.1 * d.1 + (W j).u₁.2 * d.2 =
        c1 * ((W j).u₁.1 * (dir1 (W i)).1 + (W j).u₁.2 * (dir1 (W i)).2) +
        c2 * ((W j).u₁.1 * (dir2 (W i)).1 + (W j).u₁.2 * (dir2 (W i)).2) := by
      rw [hd1, hd2]; ring
    have hlt0 : (W j).u₁.1 * d.1 + (W j).u₁.2 * d.2 < 0 := by
      rw [hlin]
      rcases eq_or_lt_of_le hc1 with rfl | hc1p
      · have hc2p : 0 < c2 := lt_of_le_of_ne hc2 (fun h => hnot00 ⟨rfl, h.symm⟩)
        nlinarith
      · have h2np : c2 * ((W j).u₁.1 * (dir2 (W i)).1 + (W j).u₁.2 * (dir2 (W i)).2) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos hc2 (le_of_lt hs21)
        nlinarith
    linarith [hdj.1]

/-! ## Part 4: Angles, Minimal-Cover Gap Rotation, Interval Components, and Main Theorem -/

def coneMem (W : OpenWedge) (d : ℝ × ℝ) : Prop :=
  0 < W.u₁.1 * d.1 + W.u₁.2 * d.2 ∧ 0 < W.u₂.1 * d.1 + W.u₂.2 * d.2

def extConeMem (W : OpenWedge) (d : ℝ × ℝ) : Prop :=
  W.u₁.1 * d.1 + W.u₁.2 * d.2 < 0 ∨ W.u₂.1 * d.1 + W.u₂.2 * d.2 < 0

def uvec (φ : ℝ) : ℝ × ℝ := (Real.cos φ, Real.sin φ)

def toC (v : ℝ × ℝ) : ℂ := ⟨v.1, v.2⟩

def ang02 (v : ℝ × ℝ) : ℝ :=
  let θ := (toC v).arg
  if θ < 0 then θ + 2 * Real.pi else θ

def onArc (W : OpenWedge) (φ : ℝ) : Prop := closureConeMem W (uvec φ)

lemma uvec_ne_zero (φ : ℝ) : uvec φ ≠ (0, 0) := by
  intro h
  have h1 : Real.cos φ = 0 := congrArg Prod.fst h
  have h2 : Real.sin φ = 0 := congrArg Prod.snd h
  have hsq := Real.cos_sq_add_sin_sq φ
  rw [h1, h2] at hsq
  norm_num at hsq

lemma ang02_nonneg (v : ℝ × ℝ) : 0 ≤ ang02 v := by
  dsimp [ang02]
  split_ifs with h
  · have hmem := Complex.arg_mem_Ioc (toC v)
    linarith [hmem.1]
  · exact not_lt.mp h

lemma ang02_lt_two_pi (v : ℝ × ℝ) : ang02 v < 2 * Real.pi := by
  dsimp [ang02]
  have hmem := Complex.arg_mem_Ioc (toC v)
  split_ifs with h
  · linarith
  · linarith [hmem.2, Real.pi_pos]

lemma eq_norm_smul_uvec {v : ℝ × ℝ} (hv : v ≠ (0, 0)) :
    ∃ r > 0, v.1 = r * Real.cos (ang02 v) ∧ v.2 = r * Real.sin (ang02 v) := by
  let z : ℂ := toC v
  have hz : z ≠ 0 := by
    intro h0; apply hv; ext <;> [exact congrArg Complex.re h0; exact congrArg Complex.im h0]
  have hr : 0 < ‖z‖ := norm_pos_iff.mpr hz
  refine ⟨‖z‖, hr, ?_, ?_⟩
  · have hcos : Real.cos z.arg = z.re / ‖z‖ := Complex.cos_arg hz
    have hcos' : Real.cos (ang02 v) = Real.cos z.arg := by
      dsimp [ang02]; split_ifs
      · exact Real.cos_add_two_pi z.arg
      · rfl
    rw [hcos', hcos]
    dsimp [z, toC]
    exact (mul_div_cancel₀ v.1 (ne_of_gt hr)).symm
  · have hsin : Real.sin z.arg = z.im / ‖z‖ := Complex.sin_arg z
    have hsin' : Real.sin (ang02 v) = Real.sin z.arg := by
      dsimp [ang02]; split_ifs
      · exact Real.sin_add_two_pi z.arg
      · rfl
    rw [hsin', hsin]
    dsimp [z, toC]
    exact (mul_div_cancel₀ v.2 (ne_of_gt hr)).symm

private lemma sin_pos_iff_of_Ico_two_pi {x : ℝ} (hx0 : 0 ≤ x) (hx2 : x < 2 * Real.pi) :
    0 < Real.sin x ↔ 0 < x ∧ x < Real.pi := by
  constructor
  · intro hs
    have hx_ne : x ≠ 0 := by rintro rfl; simp at hs
    refine ⟨lt_of_le_of_ne hx0 hx_ne.symm, ?_⟩
    by_contra hge
    replace hge : Real.pi ≤ x := not_lt.mp hge
    have h1 : 0 ≤ x - Real.pi := by linarith
    have h2 : x - Real.pi ≤ Real.pi := by linarith
    have hs_nonpos : Real.sin x ≤ 0 := by
      have : Real.sin x = -Real.sin (x - Real.pi) := by
        have := Real.sin_sub_pi x; linarith
      rw [this]
      exact neg_nonpos.mpr (Real.sin_nonneg_of_nonneg_of_le_pi h1 h2)
    linarith
  · rintro ⟨h1, h2⟩
    exact Real.sin_pos_of_pos_of_lt_pi h1 h2

private lemma sin_nonneg_iff_of_Ioo_pi {y : ℝ} (hy1 : -Real.pi < y) (hy2 : y < Real.pi) :
    0 ≤ Real.sin y ↔ 0 ≤ y := by
  constructor
  · intro hs
    by_contra hlt
    replace hlt : y < 0 := not_le.mp hlt
    have hpos : 0 < Real.sin (-y) := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
    rw [Real.sin_neg] at hpos
    linarith
  · intro hy0
    exact Real.sin_nonneg_of_nonneg_of_le_pi hy0 (le_of_lt hy2)

private lemma sin_nonneg_iff_of_Ico_two_pi {x : ℝ} (hx0 : 0 ≤ x) (hx2 : x < 2 * Real.pi) :
    0 ≤ Real.sin x ↔ x ≤ Real.pi := by
  constructor
  · intro hs
    by_contra hlt
    replace hlt : Real.pi < x := not_le.mp hlt
    have hpos : 0 < Real.sin (x - Real.pi) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
    have : Real.sin x = -Real.sin (x - Real.pi) := by
      have := Real.sin_sub_pi x; linarith
    linarith
  · intro hxp
    exact Real.sin_nonneg_of_nonneg_of_le_pi hx0 hxp

lemma onArc_isClosed (W : OpenWedge) : IsClosed {φ : ℝ | onArc W φ} := by
  have f1 : Continuous fun φ : ℝ => W.u₁.1 * Real.cos φ + W.u₁.2 * Real.sin φ := by fun_prop
  have f2 : Continuous fun φ : ℝ => W.u₂.1 * Real.cos φ + W.u₂.2 * Real.sin φ := by fun_prop
  exact (isClosed_le continuous_const f1).inter (isClosed_le continuous_const f2)

lemma onArc_periodic (W : OpenWedge) (φ : ℝ) (k : ℤ) :
    onArc W (φ + k * (2 * Real.pi)) ↔ onArc W φ := by
  have hc : Real.cos (φ + k * (2 * Real.pi)) = Real.cos φ := by
    simpa [mul_comm] using Real.cos_add_int_mul_two_pi φ k
  have hs : Real.sin (φ + k * (2 * Real.pi)) = Real.sin φ := by
    simpa [mul_comm] using Real.sin_add_int_mul_two_pi φ k
  simp [onArc, closureConeMem, uvec, hc, hs]

private lemma wedge_dot_uvec_sin (W : OpenWedge) :
    ∃ r₁ > 0, ∃ r₂ > 0,
      let a := ang02 (dir2 W)
      let b := ang02 (dir1 W)
      (∀ φ, W.u₁.1 * Real.cos φ + W.u₁.2 * Real.sin φ = r₁ * Real.sin (b - φ)) ∧
      (∀ φ, W.u₂.1 * Real.cos φ + W.u₂.2 * Real.sin φ = r₂ * Real.sin (φ - a)) := by
  obtain ⟨r₁, hr₁, h1x, h1y⟩ := eq_norm_smul_uvec (dir1_ne_zero W)
  obtain ⟨r₂, hr₂, h2x, h2y⟩ := eq_norm_smul_uvec (dir2_ne_zero W)
  refine ⟨r₁, hr₁, r₂, hr₂, fun φ => ?_, fun φ => ?_⟩
  · have hu1 : W.u₁.1 = r₁ * Real.sin (ang02 (dir1 W)) := by
      have : (dir1 W).2 = W.u₁.1 := rfl
      rw [← this, h1y]
    have hu2 : W.u₁.2 = -(r₁ * Real.cos (ang02 (dir1 W))) := by
      have : (dir1 W).1 = -W.u₁.2 := rfl
      linarith [h1x]
    rw [hu1, hu2, Real.sin_sub]
    ring
  · have hu1 : W.u₂.1 = -(r₂ * Real.sin (ang02 (dir2 W))) := by
      have : (dir2 W).2 = -W.u₂.1 := rfl
      linarith [h2y]
    have hu2 : W.u₂.2 = r₂ * Real.cos (ang02 (dir2 W)) := by
      have : (dir2 W).1 = W.u₂.2 := rfl
      rw [← this, h2x]
    rw [hu1, hu2, Real.sin_sub]
    ring

lemma onArc_span_lt_pi (W : OpenWedge) :
    let a := ang02 (dir2 W)
    let b := ang02 (dir1 W)
    let b' := if a ≤ b then b else b + 2 * Real.pi
    0 < b' - a ∧ b' - a < Real.pi := by
  intro a b b'
  obtain ⟨r₁, hr₁, r₂, hr₂, hdot1, _⟩ := wedge_dot_uvec_sin W
  have hdet : 0 < W.u₁.1 * (dir2 W).1 + W.u₁.2 * (dir2 W).2 := by
    have e : W.u₁.1 * (dir2 W).1 + W.u₁.2 * (dir2 W).2 =
        W.u₁.1 * W.u₂.2 - W.u₁.2 * W.u₂.1 := by dsimp [dir2]; ring
    rw [e]; exact W.h_nondeg
  obtain ⟨r₂', hr₂', h2x, h2y⟩ := eq_norm_smul_uvec (dir2_ne_zero W)
  have hval := hdot1 a
  have hmul : r₂' * (W.u₁.1 * Real.cos a + W.u₁.2 * Real.sin a) =
      W.u₁.1 * (dir2 W).1 + W.u₁.2 * (dir2 W).2 := by
    rw [h2x, h2y]; ring
  have hsin_b_a : 0 < Real.sin (b - a) := by
    have hpos : 0 < r₁ * Real.sin (b - a) := by
      rw [← hval]
      have : 0 < r₂' * (W.u₁.1 * Real.cos a + W.u₁.2 * Real.sin a) := hmul ▸ hdet
      exact pos_of_mul_pos_right this (le_of_lt hr₂')
    exact pos_of_mul_pos_right hpos (le_of_lt hr₁)
  have hsin_b'_a : 0 < Real.sin (b' - a) := by
    dsimp [b']
    split_ifs
    · exact hsin_b_a
    · rw [show b + 2 * Real.pi - a = (b - a) + 2 * Real.pi by ring, Real.sin_add_two_pi]
      exact hsin_b_a
  have h0 : 0 ≤ b' - a := by
    dsimp [b']
    split_ifs with h
    · linarith
    · linarith [ang02_lt_two_pi (dir2 W), ang02_nonneg (dir1 W)]
  have h2 : b' - a < 2 * Real.pi := by
    dsimp [b']
    split_ifs with h
    · linarith [ang02_nonneg (dir2 W), ang02_lt_two_pi (dir1 W)]
    · linarith
  exact (sin_pos_iff_of_Ico_two_pi h0 h2).mp hsin_b'_a

lemma onArc_iff_Icc (W : OpenWedge) (φ : ℝ) :
    let a := ang02 (dir2 W)
    let b := ang02 (dir1 W)
    let b' := if a ≤ b then b else b + 2 * Real.pi
    onArc W φ ↔ ∃ k : ℤ, φ ∈ Set.Icc (a + k * (2 * Real.pi)) (b' + k * (2 * Real.pi)) := by
  intro a b b'
  obtain ⟨r₁, hr₁, r₂, hr₂, hdot1, hdot2⟩ := wedge_dot_uvec_sin W
  obtain ⟨hspan_pos, hspan_lt⟩ := onArc_span_lt_pi W
  have hsin_eq : ∀ ψ, Real.sin (b' - ψ) = Real.sin (b - ψ) := by
    intro ψ
    dsimp [b']
    split_ifs
    · rfl
    · rw [show b + 2 * Real.pi - ψ = (b - ψ) + 2 * Real.pi by ring, Real.sin_add_two_pi]
  have hiff_base : ∀ ψ, a ≤ ψ → ψ < a + 2 * Real.pi →
      (onArc W ψ ↔ ψ ∈ Set.Icc a b') := by
    intro ψ hψ1 hψ2
    have h1 : 0 ≤ Real.sin (ψ - a) ↔ ψ - a ≤ Real.pi :=
      sin_nonneg_iff_of_Ico_two_pi (by linarith) (by linarith)
    constructor
    · rintro ⟨hu1, hu2⟩
      have hs2 : 0 ≤ Real.sin (ψ - a) := by
        have : r₂ * Real.sin (ψ - a) ≥ 0 := by rw [← hdot2 ψ]; exact hu2
        exact nonneg_of_mul_nonneg_right this hr₂
      have hle_pi : ψ - a ≤ Real.pi := h1.mp hs2
      have hb_hi : b' - ψ < Real.pi := by linarith
      have hb_lo : -Real.pi < b' - ψ := by linarith
      have hs1 : 0 ≤ Real.sin (b' - ψ) := by
        have : r₁ * Real.sin (b' - ψ) ≥ 0 := by rw [hsin_eq, ← hdot1 ψ]; exact hu1
        exact nonneg_of_mul_nonneg_right this hr₁
      have h0_le : 0 ≤ b' - ψ := (sin_nonneg_iff_of_Ioo_pi hb_lo hb_hi).mp hs1
      exact ⟨hψ1, by linarith⟩
    · rintro ⟨_, hψb⟩
      have hle_pi : ψ - a ≤ Real.pi := by linarith
      have hs2 : 0 ≤ Real.sin (ψ - a) := h1.mpr hle_pi
      have hs1 : 0 ≤ Real.sin (b' - ψ) :=
        Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
      refine ⟨?_, ?_⟩
      · dsimp [onArc, closureConeMem, uvec]
        rw [hdot1 ψ, ← hsin_eq ψ]; exact mul_nonneg (le_of_lt hr₁) hs1
      · dsimp [onArc, closureConeMem, uvec]
        rw [hdot2 ψ]; exact mul_nonneg (le_of_lt hr₂) hs2
  constructor
  · intro hφ
    let k : ℤ := ⌊(φ - a) / (2 * Real.pi)⌋
    let ψ : ℝ := φ - k * (2 * Real.pi)
    have h2pi : 0 < 2 * Real.pi := by linarith [Real.pi_pos]
    have hk_le : (k : ℝ) * (2 * Real.pi) ≤ φ - a := by
      have := Int.floor_le ((φ - a) / (2 * Real.pi))
      exact (le_div_iff₀ h2pi).mp this
    have hk_lt : φ - a < ((k : ℝ) + 1) * (2 * Real.pi) := by
      have := Int.lt_floor_add_one ((φ - a) / (2 * Real.pi))
      exact (div_lt_iff₀ h2pi).mp this
    have hψ1 : a ≤ ψ := by dsimp [ψ]; linarith
    have hψ2 : ψ < a + 2 * Real.pi := by dsimp [ψ]; linarith
    have hψ_arc : onArc W ψ := by
      have hper := (onArc_periodic W ψ k).mp
      have heq : ψ + k * (2 * Real.pi) = φ := by dsimp [ψ]; ring
      rw [heq] at hper
      exact hper hφ
    obtain ⟨ha_le, hb_le⟩ := (hiff_base ψ hψ1 hψ2).mp hψ_arc
    refine ⟨k, by dsimp [ψ] at ha_le; linarith, by dsimp [ψ] at hb_le; linarith⟩
  · rintro ⟨k, hk1, hk2⟩
    let ψ : ℝ := φ - k * (2 * Real.pi)
    have hψ_mem : ψ ∈ Set.Icc a b' := ⟨by dsimp [ψ]; linarith, by dsimp [ψ]; linarith⟩
    have hψ2 : ψ < a + 2 * Real.pi := by linarith [Real.pi_pos]
    have hψ_arc : onArc W ψ := (hiff_base ψ hψ_mem.1 hψ2).mpr hψ_mem
    have heq : ψ + k * (2 * Real.pi) = φ := by dsimp [ψ]; ring
    rw [← heq]
    exact (onArc_periodic W ψ k).mpr hψ_arc

lemma onArc_endpoints_mem (W : OpenWedge) :
    onArc W (ang02 (dir2 W)) ∧
    onArc W (if ang02 (dir2 W) ≤ ang02 (dir1 W) then ang02 (dir1 W) else ang02 (dir1 W) + 2 * Real.pi) := by
  have hiff := onArc_iff_Icc W
  obtain ⟨hpos, _⟩ := onArc_span_lt_pi W
  constructor
  · refine (hiff (ang02 (dir2 W))).mpr ⟨0, ?_⟩
    simp only [Int.cast_zero, zero_mul, add_zero, Set.mem_Icc]
    exact ⟨le_rfl, by linarith⟩
  · refine (hiff _).mpr ⟨0, ?_⟩
    simp only [Int.cast_zero, zero_mul, add_zero, Set.mem_Icc]
    exact ⟨by linarith, le_rfl⟩

lemma onArc_subset_of_endpoints (W₁ W₂ : OpenWedge)
    (h1 : onArc W₂ (ang02 (dir2 W₁)))
    (h2 : onArc W₂ (if ang02 (dir2 W₁) ≤ ang02 (dir1 W₁) then ang02 (dir1 W₁) else ang02 (dir1 W₁) + 2 * Real.pi)) :
    ∀ φ : ℝ, onArc W₁ φ → onArc W₂ φ := by
  let a₁ := ang02 (dir2 W₁)
  let b₁' := if a₁ ≤ ang02 (dir1 W₁) then ang02 (dir1 W₁) else ang02 (dir1 W₁) + 2 * Real.pi
  let a₂ := ang02 (dir2 W₂)
  let b₂' := if a₂ ≤ ang02 (dir1 W₂) then ang02 (dir1 W₂) else ang02 (dir1 W₂) + 2 * Real.pi
  obtain ⟨hspan1_pos, hspan1_lt⟩ := onArc_span_lt_pi W₁
  obtain ⟨hspan2_pos, hspan2_lt⟩ := onArc_span_lt_pi W₂
  obtain ⟨k, hk1, hk2⟩ := (onArc_iff_Icc W₂ a₁).mp h1
  obtain ⟨m, hm1, hm2⟩ := (onArc_iff_Icc W₂ b₁').mp h2
  have hkm : k = m := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hk1_le : (k + 1 : ℤ) ≤ m := hlt
      have hreal : ((k : ℝ) + 1) ≤ (m : ℝ) := by exact_mod_cast hk1_le
      have hpi : 0 < Real.pi := Real.pi_pos
      have hdiff : b₁' - a₁ ≥ 2 * Real.pi - (b₂' - a₂) := by nlinarith
      linarith
    · have hm1_le : (m + 1 : ℤ) ≤ k := hgt
      have hreal : ((m : ℝ) + 1) ≤ (k : ℝ) := by exact_mod_cast hm1_le
      have hpi : 0 < Real.pi := Real.pi_pos
      have hdiff : b₁' - a₁ ≤ -2 * Real.pi + (b₂' - a₂) := by nlinarith
      linarith
  subst hkm
  intro φ hφ
  obtain ⟨r, hr1, hr2⟩ := (onArc_iff_Icc W₁ φ).mp hφ
  refine (onArc_iff_Icc W₂ φ).mpr ⟨k + r, ?_, ?_⟩
  · push_cast; linarith
  · push_cast; linarith

def ovW (W : Fin 6 → OpenWedge) (i j : Fin 6) : Prop :=
  ∃ φ : ℝ, onArc (W i) φ ∧ onArc (W j) φ

lemma exists_uncovered_angle (W : Fin 6 → OpenWedge)
    (h_edge_le : (Finset.univ.filter (fun p : Fin 6 × Fin 6 => p.1 < p.2 ∧ ovW W p.1 p.2)).card ≤ 3) :
    ∃ θ₀ : ℝ, ∀ i : Fin 6, ¬ onArc (W i) θ₀ := by
  by_contra hcov
  push Not at hcov
  let covers := Finset.univ.filter (fun T : Finset (Fin 6) => ∀ θ : ℝ, ∃ i ∈ T, onArc (W i) θ)
  have huniv : Finset.univ ∈ covers :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun θ => let ⟨i, hi⟩ := hcov θ; ⟨i, Finset.mem_univ _, hi⟩⟩
  obtain ⟨T, hT_mem, hT_min⟩ := Finset.exists_min_image covers Finset.card ⟨Finset.univ, huniv⟩
  have hT_cov : ∀ θ : ℝ, ∃ i ∈ T, onArc (W i) θ := (Finset.mem_filter.mp hT_mem).2
  have h_deg2 : ∀ i ∈ T, ∃ j₁ ∈ T.erase i, ∃ j₂ ∈ T.erase i, j₁ ≠ j₂ ∧ ovW W i j₁ ∧ ovW W i j₂ := by
    intro i hiT
    let a := ang02 (dir2 (W i))
    let b' := if a ≤ ang02 (dir1 (W i)) then ang02 (dir1 (W i)) else ang02 (dir1 (W i)) + 2 * Real.pi
    have h_cover_pt : ∀ θ₀ : ℝ, (∀ ε > 0, ∃ θ ∈ Set.Ioo (θ₀ - ε) (θ₀ + ε), ¬ onArc (W i) θ) →
        ∃ j ∈ T.erase i, onArc (W j) θ₀ := by
      intro θ₀ hnot
      by_contra hnone
      push Not at hnone
      let K : Set ℝ := ⋃ j ∈ (T.erase i : Set (Fin 6)), {θ : ℝ | onArc (W j) θ}
      have hK_closed : IsClosed K :=
        (T.erase i).finite_toSet.isClosed_biUnion fun j _ => onArc_isClosed (W j)
      have hθ₀_nK : θ₀ ∉ K := by
        intro hmem; rw [Set.mem_iUnion₂] at hmem
        obtain ⟨j, hj, hjθ⟩ := hmem
        exact hnone j hj hjθ
      obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hK_closed.isOpen_compl θ₀ hθ₀_nK
      obtain ⟨θ, hθ_Ioo, hθ_no⟩ := hnot ε hε
      have hθ_ball : θ ∈ Metric.ball θ₀ ε := by
        rw [Metric.mem_ball, Real.dist_eq, abs_lt]
        exact ⟨by linarith [hθ_Ioo.1], by linarith [hθ_Ioo.2]⟩
      have hθ_nK : θ ∉ K := hball hθ_ball
      obtain ⟨j, hjT, hjθ⟩ := hT_cov θ
      have hji : j ≠ i := fun heq => hθ_no (heq ▸ hjθ)
      exact hθ_nK (Set.mem_iUnion₂.mpr ⟨j, Finset.mem_erase.mpr ⟨hji, hjT⟩, hjθ⟩)
    obtain ⟨hspan_pos, hspan_lt⟩ := onArc_span_lt_pi (W i)
    have ha_cov : ∃ j₁ ∈ T.erase i, onArc (W j₁) a := by
      apply h_cover_pt a
      intro ε hε
      let δ := min (ε / 2) (Real.pi / 2)
      have hδ : 0 < δ := lt_min (by linarith) (by linarith [Real.pi_pos])
      refine ⟨a - δ, ⟨by linarith [min_le_left (ε / 2) (Real.pi / 2)], by linarith⟩, ?_⟩
      intro hon
      obtain ⟨k, hk1, hk2⟩ := (onArc_iff_Icc (W i) (a - δ)).mp hon
      have h2pi : 0 < 2 * Real.pi := by linarith [Real.pi_pos]
      have hlt_k : k ≤ -1 := by
        by_contra hge
        have hk0 : (0 : ℤ) ≤ k := by omega
        have hk0' : (0 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk0
        nlinarith
      have hle_r : (k : ℝ) ≤ -1 := by exact_mod_cast hlt_k
      have : a - δ ≤ b' + k * (2 * Real.pi) := hk2
      have h1 : b' + k * (2 * Real.pi) ≤ b' - 2 * Real.pi := by nlinarith
      linarith [min_le_right (ε / 2) (Real.pi / 2)]
    have hb_cov : ∃ j₂ ∈ T.erase i, onArc (W j₂) b' := by
      apply h_cover_pt b'
      intro ε hε
      let δ := min (ε / 2) (Real.pi / 2)
      have hδ : 0 < δ := lt_min (by linarith) (by linarith [Real.pi_pos])
      refine ⟨b' + δ, ⟨by linarith, by linarith [min_le_left (ε / 2) (Real.pi / 2)]⟩, ?_⟩
      intro hon
      obtain ⟨k, hk1, hk2⟩ := (onArc_iff_Icc (W i) (b' + δ)).mp hon
      have h2pi : 0 < 2 * Real.pi := by linarith [Real.pi_pos]
      have hge_k : 1 ≤ k := by
        by_contra hlt
        have hk0 : k ≤ 0 := by omega
        have hk0' : (k : ℝ) ≤ 0 := by exact_mod_cast hk0
        have : b' + k * (2 * Real.pi) ≤ b' := by nlinarith
        linarith
      have hge_r : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hge_k
      have : a + k * (2 * Real.pi) ≤ b' + δ := hk1
      have h1 : a + 2 * Real.pi ≤ a + k * (2 * Real.pi) := by nlinarith
      linarith [min_le_right (ε / 2) (Real.pi / 2)]
    obtain ⟨j₁, hj₁, hja⟩ := ha_cov
    obtain ⟨j₂, hj₂, hjb⟩ := hb_cov
    have hne : j₁ ≠ j₂ := by
      rintro rfl
      have hsub := onArc_subset_of_endpoints (W i) (W j₁) hja hjb
      have hmem_erase : T.erase i ∈ covers := by
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun θ => ?_⟩
        obtain ⟨r, hrT, hrθ⟩ := hT_cov θ
        by_cases hri : r = i
        · subst hri; exact ⟨j₁, hj₁, hsub θ hrθ⟩
        · exact ⟨r, Finset.mem_erase.mpr ⟨hri, hrT⟩, hrθ⟩
      have hle := hT_min (T.erase i) hmem_erase
      have hcard := Finset.card_erase_lt_of_mem hiT
      omega
    obtain ⟨ha_mem, hb_mem⟩ := onArc_endpoints_mem (W i)
    exact ⟨j₁, hj₁, j₂, hj₂, hne, ⟨a, ha_mem, hja⟩, ⟨b', hb_mem, hjb⟩⟩
  let E_ov := Finset.univ.filter (fun p : Fin 6 × Fin 6 => p.1 < p.2 ∧ ovW W p.1 p.2)
  let E_in := E_ov.filter (fun p => p.1 ∈ T ∧ p.2 ∈ T)
  let E_out := E_ov.filter (fun p => (p.1 ∈ T ∧ p.2 ∉ T) ∨ (p.1 ∉ T ∧ p.2 ∈ T))
  have hE_disj : Disjoint E_in E_out := by
    rw [Finset.disjoint_left]
    rintro p hp1 hp2
    have h1 := (Finset.mem_filter.mp hp1).2
    rcases (Finset.mem_filter.mp hp2).2 with ⟨_, h⟩ | ⟨h, _⟩ <;> tauto
  have hE_sub : E_in ∪ E_out ⊆ E_ov := Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  have hE_in_card : T.card ≤ E_in.card := by
    let dirIn := T.biUnion (fun i => (T.erase i).filter (fun j => ovW W i j) |>.map
      ⟨fun j => (i, j), fun a b hab => congrArg Prod.snd hab⟩)
    have hdir_card : 2 * T.card ≤ dirIn.card := by
      have hdisj : (T : Set (Fin 6)).PairwiseDisjoint
          (fun i => ((T.erase i).filter (fun j => ovW W i j)).map
            ⟨fun j => (i, j), fun a b hab => congrArg Prod.snd hab⟩) := by
        intro x _ y _ hxy
        dsimp [Function.onFun]
        rw [Finset.disjoint_left]
        intro p hp1 hp2
        simp only [Finset.mem_map, Finset.mem_filter, Function.Embedding.coeFn_mk] at hp1 hp2
        rcases hp1 with ⟨a, _, rfl⟩
        rcases hp2 with ⟨b, _, heq⟩
        exact hxy (congrArg Prod.fst heq).symm
      rw [Finset.card_biUnion hdisj]
      calc 2 * T.card = ∑ _i ∈ T, 2 := by simp [mul_comm]
        _ ≤ ∑ i ∈ T, (((T.erase i).filter (fun j => ovW W i j)).map
              ⟨fun j => (i, j), fun a b hab => congrArg Prod.snd hab⟩).card := by
            refine Finset.sum_le_sum fun i hi => ?_
            rw [Finset.card_map]
            obtain ⟨j₁, hj₁, j₂, hj₂, hne, hov1, hov2⟩ := h_deg2 i hi
            have h12 : ({j₁, j₂} : Finset (Fin 6)) ⊆ (T.erase i).filter (fun j => ovW W i j) := by
              intro j hj
              rcases Finset.mem_insert.mp hj with rfl | hj'
              · exact Finset.mem_filter.mpr ⟨hj₁, hov1⟩
              · rw [Finset.mem_singleton.mp hj']; exact Finset.mem_filter.mpr ⟨hj₂, hov2⟩
            calc 2 = ({j₁, j₂} : Finset (Fin 6)).card := (Finset.card_pair hne).symm
              _ ≤ ((T.erase i).filter (fun j => ovW W i j)).card := Finset.card_le_card h12
    have hf_sub : dirIn ⊆ E_in.image id ∪ E_in.image Prod.swap := by
      rintro ⟨i, j⟩ hij
      simp only [dirIn, Finset.mem_biUnion, Finset.mem_map, Finset.mem_filter,
        Function.Embedding.coeFn_mk, Prod.mk.injEq] at hij
      rcases hij with ⟨i', hi'T, j', ⟨hj'er, hov⟩, rfl, rfl⟩
      have hji : j' ≠ i' := (Finset.mem_erase.mp hj'er).1
      have hj'T : j' ∈ T := (Finset.mem_erase.mp hj'er).2
      rcases lt_or_gt_of_ne hji with hlt | hgt
      · refine Finset.mem_union.mpr (Or.inr (Finset.mem_image.mpr ⟨(j', i'), ?_, rfl⟩))
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt, by obtain ⟨φ, h1, h2⟩ := hov; exact ⟨φ, h2, h1⟩⟩,
           hj'T, hi'T⟩
      · refine Finset.mem_union.mpr (Or.inl (Finset.mem_image.mpr ⟨(i', j'), ?_, rfl⟩))
        exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hgt, hov⟩, hi'T, hj'T⟩
    have hle2 : dirIn.card ≤ 2 * E_in.card := by
      calc dirIn.card ≤ (E_in.image id ∪ E_in.image Prod.swap).card := Finset.card_le_card hf_sub
        _ ≤ (E_in.image id).card + (E_in.image Prod.swap).card := Finset.card_union_le _ _
        _ ≤ E_in.card + E_in.card := add_le_add Finset.card_image_le Finset.card_image_le
        _ = 2 * E_in.card := by ring
    omega
  have hE_out_card : (Finset.univ \ T).card ≤ E_out.card := by
    have hmap : ∀ r ∈ Finset.univ \ T, ∃ p ∈ E_out, p.1 = r ∨ p.2 = r := by
      intro r hr
      have hrT : r ∉ T := (Finset.mem_sdiff.mp hr).2
      let a := ang02 (dir2 (W r))
      obtain ⟨i, hiT, hia⟩ := hT_cov a
      have hri : r ≠ i := fun h => hrT (h ▸ hiT)
      have hov : ovW W r i := ⟨a, (onArc_endpoints_mem (W r)).1, hia⟩
      rcases lt_or_gt_of_ne hri with hlt | hgt
      · refine ⟨(r, i), Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt, hov⟩,
          Or.inr ⟨hrT, hiT⟩⟩, Or.inl rfl⟩
      · refine ⟨(i, r), Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hgt,
          by obtain ⟨φ, h1, h2⟩ := hov; exact ⟨φ, h2, h1⟩⟩, Or.inl ⟨hiT, hrT⟩⟩, Or.inr rfl⟩
    let g : Fin 6 → Fin 6 × Fin 6 := fun r =>
      if hr : r ∈ Finset.univ \ T then (hmap r hr).choose else (0, 0)
    have hg_mem : ∀ r ∈ Finset.univ \ T, g r ∈ E_out := fun r hr => by
      dsimp [g]; rw [dif_pos hr]; exact (hmap r hr).choose_spec.1
    have hg_inj : Set.InjOn g (Finset.univ \ T : Finset (Fin 6)) := by
      intro r₁ hr₁ r₂ hr₂ heq
      have h1 := (hmap r₁ hr₁).choose_spec
      have h2 := (hmap r₂ hr₂).choose_spec
      have hp : (hmap r₁ (Finset.mem_coe.mp hr₁)).choose =
          (hmap r₂ (Finset.mem_coe.mp hr₂)).choose := by
        dsimp [g] at heq
        rw [dif_pos (Finset.mem_coe.mp hr₁), dif_pos (Finset.mem_coe.mp hr₂)] at heq
        exact heq
      have hr₁_nT : r₁ ∉ T := (Finset.mem_sdiff.mp (Finset.mem_coe.mp hr₁)).2
      have hr₂_nT : r₂ ∉ T := (Finset.mem_sdiff.mp (Finset.mem_coe.mp hr₂)).2
      rw [hp] at h1
      rcases h1.2 with h1l | h1r <;> rcases h2.2 with h2l | h2r
      · exact h1l.symm.trans h2l
      · exfalso
        have hp_out := (Finset.mem_filter.mp h2.1).2
        rcases hp_out with ⟨hfst, _⟩ | ⟨_, hsnd⟩
        · rw [h1l] at hfst; exact hr₁_nT hfst
        · rw [h2r] at hsnd; exact hr₂_nT hsnd
      · exfalso
        have hp_out := (Finset.mem_filter.mp h2.1).2
        rcases hp_out with ⟨hfst, _⟩ | ⟨_, hsnd⟩
        · rw [h2l] at hfst; exact hr₂_nT hfst
        · rw [h1r] at hsnd; exact hr₁_nT hsnd
      · exact h1r.symm.trans h2r
    calc (Finset.univ \ T).card
        = ((Finset.univ \ T).image g).card := (Finset.card_image_of_injOn hg_inj).symm
      _ ≤ E_out.card := Finset.card_le_card (Finset.image_subset_iff.mpr hg_mem)
  have hdisjT : Disjoint T (Finset.univ \ T) :=
    Finset.disjoint_left.mpr fun _ hx hy => (Finset.mem_sdiff.mp hy).2 hx
  have h6 : T.card + (Finset.univ \ T).card = 6 := by
    rw [← Finset.card_union_of_disjoint hdisjT,
      Finset.union_sdiff_of_subset (Finset.subset_univ T), Finset.card_univ, Fintype.card_fin]
  have hE_tot : (E_in ∪ E_out).card = E_in.card + E_out.card := Finset.card_union_of_disjoint hE_disj
  have hE_le : E_in.card + E_out.card ≤ E_ov.card := by
    rw [← hE_tot]; exact Finset.card_le_card hE_sub
  have hE_ov_le : E_ov.card ≤ 3 := h_edge_le
  omega

def rotPt (c s : ℝ) (p : ℝ × ℝ) : ℝ × ℝ :=
  (c * p.1 + s * p.2, -s * p.1 + c * p.2)

lemma rotPt_injective (c s : ℝ) (hcs : c ^ 2 + s ^ 2 = 1) : Function.Injective (rotPt c s) := by
  intro p q hpq
  have hx : c * p.1 + s * p.2 = c * q.1 + s * q.2 := congrArg Prod.fst hpq
  have hy : -s * p.1 + c * p.2 = -s * q.1 + c * q.2 := congrArg Prod.snd hpq
  ext
  · linear_combination (c * hx - s * hy) - (p.1 - q.1) * hcs
  · linear_combination (s * hx + c * hy) - (p.2 - q.2) * hcs

def rotWedge (c s : ℝ) (hcs : c ^ 2 + s ^ 2 = 1) (W : OpenWedge) : OpenWedge where
  y := rotPt c s W.y
  u₁ := rotPt c s W.u₁
  u₂ := rotPt c s W.u₂
  h_nondeg := by
    have hdet : (rotPt c s W.u₁).1 * (rotPt c s W.u₂).2 - (rotPt c s W.u₁).2 * (rotPt c s W.u₂).1 =
        (c ^ 2 + s ^ 2) * (W.u₁.1 * W.u₂.2 - W.u₁.2 * W.u₂.1) := by
      dsimp [rotPt]; ring
    rw [hdet, hcs, one_mul]
    exact W.h_nondeg

lemma rotWedge_memOpen (c s : ℝ) (hcs : c ^ 2 + s ^ 2 = 1) (W : OpenWedge) (p : ℝ × ℝ) :
    (rotWedge c s hcs W).MemOpen (rotPt c s p) ↔ W.MemOpen p := by
  have hdot : ∀ u y : ℝ × ℝ,
      (rotPt c s u).1 * ((rotPt c s p).1 - (rotPt c s y).1) +
      (rotPt c s u).2 * ((rotPt c s p).2 - (rotPt c s y).2) =
        (c ^ 2 + s ^ 2) * (u.1 * (p.1 - y.1) + u.2 * (p.2 - y.2)) := by
    intro u y; dsimp [rotPt]; ring
  dsimp [OpenWedge.MemOpen, rotWedge]
  rw [hdot W.u₁ W.y, hdot W.u₂ W.y, hcs, one_mul, one_mul]

lemma rotWedge_memExt (c s : ℝ) (hcs : c ^ 2 + s ^ 2 = 1) (W : OpenWedge) (p : ℝ × ℝ) :
    (rotWedge c s hcs W).MemExt (rotPt c s p) ↔ W.MemExt p := by
  have hdot : ∀ u y : ℝ × ℝ,
      (rotPt c s u).1 * ((rotPt c s p).1 - (rotPt c s y).1) +
      (rotPt c s u).2 * ((rotPt c s p).2 - (rotPt c s y).2) =
        (c ^ 2 + s ^ 2) * (u.1 * (p.1 - y.1) + u.2 * (p.2 - y.2)) := by
    intro u y; dsimp [rotPt]; ring
  dsimp [OpenWedge.MemExt, rotWedge]
  rw [hdot W.u₁ W.y, hdot W.u₂ W.y, hcs, one_mul, one_mul]

lemma rotWedge_bdWedge (c s : ℝ) (hcs : c ^ 2 + s ^ 2 = 1) (W : OpenWedge) (p : ℝ × ℝ) :
    rotPt c s p ∈ bdWedge (rotWedge c s hcs W) ↔ p ∈ bdWedge W := by
  simp [bdWedge, rotWedge_memOpen, rotWedge_memExt]

lemma rotWedge_gp6 (c s : ℝ) (hcs : c ^ 2 + s ^ 2 = 1) {W : Fin 6 → OpenWedge} (hGP : GP6 W) :
    GP6 (fun i => rotWedge c s hcs (W i)) := by
  constructor
  · intro a b hab
    have hnorm : ∀ x, normal (fun i => rotWedge c s hcs (W i)) x = rotPt c s (normal W x) := by
      rintro ⟨i, ⟨⟩⟩ <;> rfl
    rw [hnorm a, hnorm b]
    have hdet : det2 (rotPt c s (normal W a)) (rotPt c s (normal W b)) =
        (c ^ 2 + s ^ 2) * det2 (normal W a) (normal W b) := by
      dsimp [det2, rotPt]; ring
    rw [hdet, hcs, one_mul]
    exact hGP.no_parallel a b hab
  · intro i j hij b
    have hline : lineAt (fun k => rotWedge c s hcs (W k)) (j, b) (rotWedge c s hcs (W i)).y =
        (c ^ 2 + s ^ 2) * lineAt W (j, b) (W i).y := by
      cases b <;> dsimp [lineAt, normal, rotWedge, rotPt] <;> ring
    rw [hline, hcs, one_mul]
    exact hGP.apex_not_on_line i j hij b

lemma rotWedge_inter_ncard (c s : ℝ) (hcs : c ^ 2 + s ^ 2 = 1) (W₁ W₂ : OpenWedge) :
    (bdWedge (rotWedge c s hcs W₁) ∩ bdWedge (rotWedge c s hcs W₂)).ncard =
    (bdWedge W₁ ∩ bdWedge W₂).ncard := by
  have himg : rotPt c s '' (bdWedge W₁ ∩ bdWedge W₂) =
      bdWedge (rotWedge c s hcs W₁) ∩ bdWedge (rotWedge c s hcs W₂) := by
    ext q; constructor
    · rintro ⟨p, ⟨h1, h2⟩, rfl⟩
      exact ⟨(rotWedge_bdWedge c s hcs W₁ p).mpr h1, (rotWedge_bdWedge c s hcs W₂ p).mpr h2⟩
    · rintro ⟨h1, h2⟩
      let p : ℝ × ℝ := (c * q.1 - s * q.2, s * q.1 + c * q.2)
      have hpq : rotPt c s p = q := by
        ext <;> [dsimp [rotPt, p]; dsimp [rotPt, p]]
        · linear_combination q.1 * hcs
        · linear_combination q.2 * hcs
      refine ⟨p, ?_, hpq⟩
      rw [← hpq] at h1 h2
      exact ⟨(rotWedge_bdWedge c s hcs W₁ p).mp h1, (rotWedge_bdWedge c s hcs W₂ p).mp h2⟩
  rw [← himg]
  exact Set.ncard_image_of_injective _ (rotPt_injective c s hcs)

lemma rot_zero_uncovered (W : OpenWedge) (θ₀ : ℝ) (hno : ¬ onArc W θ₀) :
    let c := Real.cos θ₀
    let s := Real.sin θ₀
    let hcs : c ^ 2 + s ^ 2 = 1 := Real.cos_sq_add_sin_sq θ₀
    let W' := rotWedge c s hcs W
    ¬ onArc W' 0 ∧
    0 < ang02 (dir2 W') ∧ ang02 (dir2 W') < ang02 (dir1 W') ∧
    ang02 (dir1 W') < 2 * Real.pi ∧ ang02 (dir1 W') - ang02 (dir2 W') < Real.pi := by
  intro c s hcs W'
  have hdot : ∀ u : ℝ × ℝ,
      (rotPt c s u).1 * (uvec 0).1 + (rotPt c s u).2 * (uvec 0).2 =
        u.1 * (uvec θ₀).1 + u.2 * (uvec θ₀).2 := by
    intro u; dsimp [rotPt, uvec, c, s]; rw [Real.cos_zero, Real.sin_zero]; ring
  have hzero : ¬ onArc W' 0 := by
    intro h0
    apply hno
    dsimp [onArc, closureConeMem, W', rotWedge] at h0 ⊢
    rw [hdot W.u₁, hdot W.u₂] at h0
    exact h0
  let a := ang02 (dir2 W')
  let b := ang02 (dir1 W')
  have ha_ne : a ≠ 0 := by
    rintro ha0
    apply hzero
    rw [← ha0]
    exact (onArc_endpoints_mem W').1
  have ha_pos : 0 < a := lt_of_le_of_ne (ang02_nonneg _) ha_ne.symm
  have hle : a ≤ b := by
    by_contra hlt
    replace hlt : b < a := not_le.mp hlt
    apply hzero
    refine (onArc_iff_Icc W' 0).mpr ⟨-1, ?_, ?_⟩
    · have h2pi := ang02_lt_two_pi (dir2 W'); push_cast; linarith
    · have hb_nn : 0 ≤ ang02 (dir1 W') := ang02_nonneg (dir1 W')
      have hif : (if a ≤ b then b else b + 2 * Real.pi) = b + 2 * Real.pi := if_neg (not_le.mpr hlt)
      change (0 : ℝ) ≤ (if a ≤ b then b else b + 2 * Real.pi) + (-1 : ℤ) * (2 * Real.pi)
      rw [hif]; push_cast; dsimp [b]; linarith
  have hlt_ab : a < b := by
    rcases eq_or_lt_of_le hle with hab | hlt
    · exfalso
      have hspan := onArc_span_lt_pi W'
      have hif : (if a ≤ b then b else b + 2 * Real.pi) = b := if_pos hle
      dsimp [a, b] at hspan hif hab
      rw [hif, hab] at hspan
      linarith [hspan.1]
    · exact hlt
  have hspan := onArc_span_lt_pi W'
  have hif : (if a ≤ b then b else b + 2 * Real.pi) = b := if_pos hle
  dsimp [a, b] at hspan hif
  rw [hif] at hspan
  exact ⟨hzero, ha_pos, hlt_ab, ang02_lt_two_pi (dir1 W'), hspan.2⟩

private def setoidOfRel (R : Fin 6 → Fin 6 → Prop) : Setoid (Fin 6) where
  r := Relation.EqvGen R
  iseqv := ⟨Relation.EqvGen.refl, fun h => Relation.EqvGen.symm _ _ h,
    fun h1 h2 => Relation.EqvGen.trans _ _ _ h1 h2⟩

private lemma six_le_quotCard_add_card :
    ∀ (E : Finset (Fin 6 × Fin 6)),
      6 ≤ (Finset.univ.image (Quotient.mk (setoidOfRel (fun i j => (i, j) ∈ E ∨ (j, i) ∈ E)))).card +
          E.card := by
  intro E
  induction E using Finset.induction with
  | empty =>
    have heq : Relation.EqvGen (fun i j : Fin 6 => (i, j) ∈ (∅ : Finset _) ∨ (j, i) ∈ (∅ : Finset _)) = Eq := by
      ext i j; constructor
      · intro h
        induction h with
        | rel _ _ h => simp at h
        | refl => rfl
        | symm _ _ _ ih => exact ih.symm
        | trans _ _ _ _ _ ih1 ih2 => exact ih1.trans ih2
      · rintro rfl; exact Relation.EqvGen.refl _
    have hinj : Function.Injective (Quotient.mk (setoidOfRel (fun i j : Fin 6 => (i, j) ∈ (∅ : Finset _) ∨ (j, i) ∈ (∅ : Finset _)))) := by
      intro a b hab
      have := Quotient.exact hab
      change Relation.EqvGen _ a b at this
      rw [heq] at this
      exact this
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin, Finset.card_empty]
  | @insert e E' he ih =>
    rcases e with ⟨u, v⟩
    let R' := fun i j : Fin 6 => (i, j) ∈ E' ∨ (j, i) ∈ E'
    let R := fun i j : Fin 6 => (i, j) ∈ insert (u, v) E' ∨ (j, i) ∈ insert (u, v) E'
    let S' := setoidOfRel R'
    let S := setoidOfRel R
    let Q' := Finset.univ.image (Quotient.mk S')
    let Q := Finset.univ.image (Quotient.mk S)
    have h_rel : ∀ x y : Fin 6, Relation.EqvGen R' x y → Relation.EqvGen R x y := by
      intro x y h
      induction h with
      | rel a b hab =>
        apply Relation.EqvGen.rel
        rcases hab with h1 | h2
        · left; exact Finset.mem_insert_of_mem h1
        · right; exact Finset.mem_insert_of_mem h2
      | refl => exact Relation.EqvGen.refl _
      | symm _ _ _ ih' => exact Relation.EqvGen.symm _ _ ih'
      | trans _ _ _ _ _ ih1 ih2 => exact Relation.EqvGen.trans _ _ _ ih1 ih2
    have h_char : ∀ x y : Fin 6, Relation.EqvGen R x y →
        Relation.EqvGen R' x y ∨
        (Relation.EqvGen R' x u ∧ Relation.EqvGen R' v y) ∨
        (Relation.EqvGen R' x v ∧ Relation.EqvGen R' u y) := by
      intro x y h
      induction h with
      | rel a b hab =>
        rcases hab with h1 | h2
        · rcases Finset.mem_insert.mp h1 with heq | hmem
          · obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
            right; left; exact ⟨Relation.EqvGen.refl _, Relation.EqvGen.refl _⟩
          · left; exact Relation.EqvGen.rel _ _ (Or.inl hmem)
        · rcases Finset.mem_insert.mp h2 with heq | hmem
          · obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
            right; right; exact ⟨Relation.EqvGen.refl _, Relation.EqvGen.refl _⟩
          · left; exact Relation.EqvGen.rel _ _ (Or.inr hmem)
      | refl => left; exact Relation.EqvGen.refl _
      | symm a b _ ih' =>
        rcases ih' with h | ⟨h1, h2⟩ | ⟨h1, h2⟩
        · left; exact Relation.EqvGen.symm _ _ h
        · right; right; exact ⟨Relation.EqvGen.symm _ _ h2, Relation.EqvGen.symm _ _ h1⟩
        · right; left; exact ⟨Relation.EqvGen.symm _ _ h2, Relation.EqvGen.symm _ _ h1⟩
      | trans a b c _ _ ih1 ih2 =>
        rcases ih1 with h1 | ⟨ha, hb⟩ | ⟨ha, hb⟩ <;> rcases ih2 with h2 | ⟨hb', hc⟩ | ⟨hb', hc⟩
        · left; exact Relation.EqvGen.trans _ _ _ h1 h2
        · right; left; exact ⟨Relation.EqvGen.trans _ _ _ h1 hb', hc⟩
        · right; right; exact ⟨Relation.EqvGen.trans _ _ _ h1 hb', hc⟩
        · right; left; exact ⟨ha, Relation.EqvGen.trans _ _ _ hb h2⟩
        · right; left; exact ⟨ha, hc⟩
        · left; exact Relation.EqvGen.trans _ _ _ ha hc
        · right; right; exact ⟨ha, Relation.EqvGen.trans _ _ _ hb h2⟩
        · left; exact Relation.EqvGen.trans _ _ _ ha hc
        · right; right; exact ⟨ha, hc⟩
    let qu := Quotient.mk S' u
    let f : Quotient S' → Quotient S :=
      Quotient.lift (Quotient.mk S) fun a b hab => Quotient.sound (h_rel a b hab)
    have hf_inj : Set.InjOn f (Q'.erase qu : Set (Quotient S')) := by
      intro x hx y hy hxy
      obtain ⟨hx_ne, hxQ⟩ := Finset.mem_erase.mp hx
      obtain ⟨hy_ne, hyQ⟩ := Finset.mem_erase.mp hy
      obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hxQ
      obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp hyQ
      have hR : Relation.EqvGen R a b := Quotient.exact hxy
      rcases h_char a b hR with hR' | ⟨hau, _⟩ | ⟨_, hub⟩
      · exact Quotient.sound hR'
      · exfalso; exact hx_ne (Quotient.sound hau)
      · exfalso; exact hy_ne (Quotient.sound (Relation.EqvGen.symm _ _ hub))
    have hsub_img : (Q'.erase qu).image f ⊆ Q := by
      intro z hz
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hz
      obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp (Finset.mem_erase.mp hq).2
      exact Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩
    have hcard_q : Q'.card ≤ Q.card + 1 := by
      have h1 : (Q'.erase qu).card ≤ Q.card := by
        rw [← Finset.card_image_of_injOn hf_inj]
        exact Finset.card_le_card hsub_img
      have hqu : qu ∈ Q' := Finset.mem_image.mpr ⟨u, Finset.mem_univ _, rfl⟩
      have h2 := Finset.card_erase_add_one hqu
      omega
    rw [Finset.card_insert_of_notMem he]
    change 6 ≤ Q.card + (E'.card + 1)
    change 6 ≤ Q'.card + E'.card at ih
    omega

private lemma separating_wedge_ordered {W : Fin 6 → OpenWedge} (hGP : GP6 W)
    {A B : Fin 6} (hAB : A ≠ B)
    (h4 : ¬ (bdWedge (W A) ∩ bdWedge (W B)).ncard ≤ 3)
    (haA0 : 0 < ang02 (dir2 (W A))) (hAB_ord : ang02 (dir1 (W A)) < ang02 (dir2 (W B)))
    (hbB2 : ang02 (dir1 (W B)) < 2 * Real.pi)
    (hA_lt : ang02 (dir2 (W A)) < ang02 (dir1 (W A)))
    (_hA_pi : ang02 (dir1 (W A)) - ang02 (dir2 (W A)) < Real.pi)
    (hB_lt : ang02 (dir2 (W B)) < ang02 (dir1 (W B)))
    (_hB_pi : ang02 (dir1 (W B)) - ang02 (dir2 (W B)) < Real.pi)
    {φ₁ φ₂ : ℝ} (_hφ₁0 : 0 < φ₁) (hφ₂2 : φ₂ < 2 * Real.pi)
    (h_in : φ₁ ∈ Set.Ioo (ang02 (dir1 (W A))) (ang02 (dir2 (W B))))
    (h_out : φ₂ ∈ Set.Ioo 0 (ang02 (dir2 (W A))) ∨ φ₂ ∈ Set.Ioo (ang02 (dir1 (W B))) (2 * Real.pi)) :
    ∃ V : OpenWedge, bdWedge V ⊆ bdWedge (W A) ∪ bdWedge (W B) ∧
      ((coneMem V (uvec φ₁) ∧ extConeMem V (uvec φ₂)) ∨
       (extConeMem V (uvec φ₁) ∧ coneMem V (uvec φ₂))) := by
  let aA := ang02 (dir2 (W A)); let bA := ang02 (dir1 (W A))
  let aB := ang02 (dir2 (W B)); let bB := ang02 (dir1 (W B))
  have hrays := quad_four_inter_rays_univ hGP hAB h4
  have hG1_ne_pi : aB - bA ≠ Real.pi := by
    intro hpi
    obtain ⟨rA, _, hAx, hAy⟩ := eq_norm_smul_uvec (dir1_ne_zero (W A))
    obtain ⟨rB, _, hBx, hBy⟩ := eq_norm_smul_uvec (dir2_ne_zero (W B))
    have hdet0 : det2 (dir1 (W A)) (dir2 (W B)) = 0 := by
      have e : det2 (dir1 (W A)) (dir2 (W B)) = rA * rB * Real.sin (aB - bA) := by
        dsimp [det2]; rw [hAx, hAy, hBx, hBy, Real.sin_sub]; ring
      rw [e, hpi, Real.sin_pi, mul_zero]
    have hdet_norm : det2 (normal W (A, true)) (normal W (B, false)) =
        -det2 (dir1 (W A)) (dir2 (W B)) := by
      simp only [det2, normal, ite_true, ite_false, Bool.false_eq_true, dir1, dir2]; ring
    exact hGP.no_parallel (A, true) (B, false) (fun h => hAB (congrArg Prod.fst h))
      (by rw [hdet_norm, hdet0, neg_zero])
  have hG2_ne_pi : aA + 2 * Real.pi - bB ≠ Real.pi := by
    intro hpi
    obtain ⟨rB, _, hBx, hBy⟩ := eq_norm_smul_uvec (dir1_ne_zero (W B))
    obtain ⟨rA, _, hAx, hAy⟩ := eq_norm_smul_uvec (dir2_ne_zero (W A))
    have hdet0 : det2 (dir1 (W B)) (dir2 (W A)) = 0 := by
      have e : det2 (dir1 (W B)) (dir2 (W A)) = rB * rA * Real.sin (aA + 2 * Real.pi - bB) := by
        have hs : Real.sin (aA + 2 * Real.pi - bB) = Real.sin (aA - bB) := by
          rw [show aA + 2 * Real.pi - bB = (aA - bB) + 2 * Real.pi by ring, Real.sin_add_two_pi]
        dsimp [det2]; rw [hBx, hBy, hAx, hAy, hs, Real.sin_sub]; ring
      rw [e, hpi, Real.sin_pi, mul_zero]
    have hdet_norm : det2 (normal W (B, true)) (normal W (A, false)) =
        -det2 (dir1 (W B)) (dir2 (W A)) := by
      simp only [det2, normal, ite_true, ite_false, Bool.false_eq_true, dir1, dir2]; ring
    exact hGP.no_parallel (B, true) (A, false) (fun h => hAB (congrArg Prod.fst h).symm)
      (by rw [hdet_norm, hdet0, neg_zero])
  obtain ⟨r1A, hr1A, r2A, hr2A, hdot1A, hdot2A⟩ := wedge_dot_uvec_sin (W A)
  obtain ⟨r1B, hr1B, r2B, hr2B, hdot1B, hdot2B⟩ := wedge_dot_uvec_sin (W B)
  rcases lt_or_gt_of_ne hG1_ne_pi with hG1_lt | hG1_gt
  · obtain ⟨tA, htA, tB, htB, heq⟩ := hrays true false
    simp only [ite_true] at heq
    let V : OpenWedge :=
      { y := ray1 (W A) tA
        u₁ := (-(W B).u₂.1, -(W B).u₂.2)
        u₂ := (-(W A).u₁.1, -(W A).u₁.2)
        h_nondeg := by
          have hs : 0 < Real.sin (aB - bA) :=
            Real.sin_pos_of_pos_of_lt_pi (by linarith) hG1_lt
          obtain ⟨rA, hrA, hAx, hAy⟩ := eq_norm_smul_uvec (dir1_ne_zero (W A))
          obtain ⟨rB, hrB, hBx, hBy⟩ := eq_norm_smul_uvec (dir2_ne_zero (W B))
          have e1 : (-(W B).u₂.1) * (-(W A).u₁.2) - (-(W B).u₂.2) * (-(W A).u₁.1) =
              det2 (dir1 (W A)) (dir2 (W B)) := by dsimp [det2, dir1, dir2]; ring
          have e2 : det2 (dir1 (W A)) (dir2 (W B)) = rA * rB * Real.sin (aB - bA) := by
            dsimp [det2]; rw [hAx, hAy, hBx, hBy, Real.sin_sub]; ring
          rw [e1, e2]; exact mul_pos (mul_pos hrA hrB) hs }
    refine ⟨V, ?_, Or.inl ⟨?_, ?_⟩⟩
    · intro p hp
      rcases (bdWedge_iff_rays V p).mp hp with ⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩
      · right
        have hray : ray1 V t = ray2 (W B) (tB + t) := by
          have hx := congrArg Prod.fst heq
          have hy := congrArg Prod.snd heq
          ext
          · dsimp [ray1, dir1, V] at *; rw [hx]; dsimp [ray2, dir2]; ring
          · dsimp [ray1, dir1, V] at *; rw [hy]; dsimp [ray2, dir2]; ring
        rw [hray]; exact ray2_mem_bdWedge (W B) (by linarith)
      · left
        have hray : ray2 V t = ray1 (W A) (tA + t) := by
          ext <;> dsimp [ray1, ray2, dir1, dir2, V] <;> ring
        rw [hray]; exact ray1_mem_bdWedge (W A) (by linarith)
    · constructor
      · have h1 : V.u₁.1 * (uvec φ₁).1 + V.u₁.2 * (uvec φ₁).2 = r2B * Real.sin (aB - φ₁) := by
          have := hdot2B φ₁
          dsimp [V, uvec]; rw [Real.sin_sub] at this ⊢; linarith
        rw [h1]
        exact mul_pos hr2B (Real.sin_pos_of_pos_of_lt_pi (by linarith [h_in.2]) (by linarith [h_in.1]))
      · have h2 : V.u₂.1 * (uvec φ₁).1 + V.u₂.2 * (uvec φ₁).2 = r1A * Real.sin (φ₁ - bA) := by
          have := hdot1A φ₁
          dsimp [V, uvec]; rw [Real.sin_sub] at this ⊢; linarith
        rw [h2]
        exact mul_pos hr1A (Real.sin_pos_of_pos_of_lt_pi (by linarith [h_in.1]) (by linarith [h_in.2]))
    · have h1 : V.u₁.1 * (uvec φ₂).1 + V.u₁.2 * (uvec φ₂).2 = r2B * Real.sin (aB - φ₂) := by
        have := hdot2B φ₂
        dsimp [V, uvec]; rw [Real.sin_sub] at this ⊢; linarith
      have h2 : V.u₂.1 * (uvec φ₂).1 + V.u₂.2 * (uvec φ₂).2 = r1A * Real.sin (φ₂ - bA) := by
        have := hdot1A φ₂
        dsimp [V, uvec]; rw [Real.sin_sub] at this ⊢; linarith
      dsimp [extConeMem]; rw [h1, h2]
      rcases h_out with ⟨hφ₂0, hφ₂A⟩ | ⟨hφ₂B, hφ₂2'⟩
      · by_cases hlt : bA - φ₂ < Real.pi
        · right
          have hs : 0 < Real.sin (bA - φ₂) :=
            Real.sin_pos_of_pos_of_lt_pi (by linarith) hlt
          have hneg : Real.sin (φ₂ - bA) < 0 := by
            rw [show φ₂ - bA = -(bA - φ₂) by ring, Real.sin_neg]; linarith
          exact mul_neg_of_pos_of_neg hr1A hneg
        · left
          replace hlt : Real.pi ≤ bA - φ₂ := not_lt.mp hlt
          have hs : 0 < Real.sin (aB - φ₂ - Real.pi) :=
            Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
          have hneg : Real.sin (aB - φ₂) < 0 := by
            have := Real.sin_sub_pi (aB - φ₂); linarith
          exact mul_neg_of_pos_of_neg hr2B hneg
      · by_cases hlt : φ₂ - aB < Real.pi
        · left
          have hs : 0 < Real.sin (φ₂ - aB) :=
            Real.sin_pos_of_pos_of_lt_pi (by linarith) hlt
          have hneg : Real.sin (aB - φ₂) < 0 := by
            rw [show aB - φ₂ = -(φ₂ - aB) by ring, Real.sin_neg]; linarith
          exact mul_neg_of_pos_of_neg hr2B hneg
        · right
          replace hlt : Real.pi ≤ φ₂ - aB := not_lt.mp hlt
          have hs : 0 < Real.sin (φ₂ - bA - Real.pi) :=
            Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
          have hneg : Real.sin (φ₂ - bA) < 0 := by
            have := Real.sin_sub_pi (φ₂ - bA); linarith
          exact mul_neg_of_pos_of_neg hr1A hneg
  · have hG2_lt : aA + 2 * Real.pi - bB < Real.pi := by linarith
    have hG2_pos : 0 < aA + 2 * Real.pi - bB := by linarith
    obtain ⟨tA, htA, tB, htB, heq⟩ := hrays false true
    simp only [ite_true, ite_false, Bool.false_eq_true] at heq
    let V : OpenWedge :=
      { y := ray2 (W A) tA
        u₁ := (-(W A).u₂.1, -(W A).u₂.2)
        u₂ := (-(W B).u₁.1, -(W B).u₁.2)
        h_nondeg := by
          have hs : 0 < Real.sin (aA + 2 * Real.pi - bB) :=
            Real.sin_pos_of_pos_of_lt_pi hG2_pos hG2_lt
          obtain ⟨rB, hrB, hBx, hBy⟩ := eq_norm_smul_uvec (dir1_ne_zero (W B))
          obtain ⟨rA, hrA, hAx, hAy⟩ := eq_norm_smul_uvec (dir2_ne_zero (W A))
          have e1 : (-(W A).u₂.1) * (-(W B).u₁.2) - (-(W A).u₂.2) * (-(W B).u₁.1) =
              det2 (dir1 (W B)) (dir2 (W A)) := by dsimp [det2, dir1, dir2]; ring
          have e2 : det2 (dir1 (W B)) (dir2 (W A)) = rB * rA * Real.sin (aA + 2 * Real.pi - bB) := by
            have hs' : Real.sin (aA + 2 * Real.pi - bB) = Real.sin (aA - bB) := by
              rw [show aA + 2 * Real.pi - bB = (aA - bB) + 2 * Real.pi by ring, Real.sin_add_two_pi]
            dsimp [det2]; rw [hBx, hBy, hAx, hAy, hs', Real.sin_sub]; ring
          rw [e1, e2]; exact mul_pos (mul_pos hrB hrA) hs }
    refine ⟨V, ?_, Or.inr ⟨?_, ?_⟩⟩
    · intro p hp
      rcases (bdWedge_iff_rays V p).mp hp with ⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩
      · left
        have hray : ray1 V t = ray2 (W A) (tA + t) := by
          ext <;> dsimp [ray1, ray2, dir1, dir2, V] <;> ring
        rw [hray]; exact ray2_mem_bdWedge (W A) (by linarith)
      · right
        have hray : ray2 V t = ray1 (W B) (tB + t) := by
          have hx := congrArg Prod.fst heq
          have hy := congrArg Prod.snd heq
          ext
          · dsimp [ray2, dir2, V] at *; rw [hx]; dsimp [ray1, dir1]; ring
          · dsimp [ray2, dir2, V] at *; rw [hy]; dsimp [ray1, dir1]; ring
        rw [hray]; exact ray1_mem_bdWedge (W B) (by linarith)
    · have h1 : V.u₁.1 * (uvec φ₁).1 + V.u₁.2 * (uvec φ₁).2 = r2A * Real.sin (aA - φ₁) := by
        have := hdot2A φ₁
        dsimp [V, uvec]; rw [Real.sin_sub] at this ⊢; linarith
      have h2 : V.u₂.1 * (uvec φ₁).1 + V.u₂.2 * (uvec φ₁).2 = r1B * Real.sin (φ₁ - bB) := by
        have := hdot1B φ₁
        dsimp [V, uvec]; rw [Real.sin_sub] at this ⊢; linarith
      dsimp [extConeMem]; rw [h1, h2]
      by_cases hlt : φ₁ - aA < Real.pi
      · left
        have hs : 0 < Real.sin (φ₁ - aA) := Real.sin_pos_of_pos_of_lt_pi (by linarith [h_in.1]) hlt
        have hneg : Real.sin (aA - φ₁) < 0 := by
          rw [show aA - φ₁ = -(φ₁ - aA) by ring, Real.sin_neg]; linarith
        exact mul_neg_of_pos_of_neg hr2A hneg
      · right
        replace hlt : Real.pi ≤ φ₁ - aA := not_lt.mp hlt
        have hs : 0 < Real.sin (bB - φ₁) :=
          Real.sin_pos_of_pos_of_lt_pi (by linarith [h_in.2]) (by linarith)
        have hneg : Real.sin (φ₁ - bB) < 0 := by
          rw [show φ₁ - bB = -(bB - φ₁) by ring, Real.sin_neg]; linarith
        exact mul_neg_of_pos_of_neg hr1B hneg
    · have h1 : V.u₁.1 * (uvec φ₂).1 + V.u₁.2 * (uvec φ₂).2 = r2A * Real.sin (aA - φ₂) := by
        have := hdot2A φ₂
        dsimp [V, uvec]; rw [Real.sin_sub] at this ⊢; linarith
      have h2 : V.u₂.1 * (uvec φ₂).1 + V.u₂.2 * (uvec φ₂).2 = r1B * Real.sin (φ₂ - bB) := by
        have := hdot1B φ₂
        dsimp [V, uvec]; rw [Real.sin_sub] at this ⊢; linarith
      constructor
      · rw [h1]
        rcases h_out with ⟨hφ₂0, hφ₂A⟩ | ⟨hφ₂B, hφ₂2'⟩
        · exact mul_pos hr2A (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [hG2_lt]))
        · have hs1 : 0 < Real.sin (aA - φ₂) := by
            have : Real.sin (aA - φ₂) = Real.sin (aA + 2 * Real.pi - φ₂) := by
              rw [show aA + 2 * Real.pi - φ₂ = (aA - φ₂) + 2 * Real.pi by ring, Real.sin_add_two_pi]
            rw [this]
            exact Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
          exact mul_pos hr2A hs1
      · rw [h2]
        rcases h_out with ⟨hφ₂0, hφ₂A⟩ | ⟨hφ₂B, hφ₂2'⟩
        · have hs2 : 0 < Real.sin (φ₂ - bB) := by
            have : Real.sin (φ₂ - bB) = Real.sin (φ₂ + 2 * Real.pi - bB) := by
              rw [show φ₂ + 2 * Real.pi - bB = (φ₂ - bB) + 2 * Real.pi by ring, Real.sin_add_two_pi]
            rw [this]
            exact Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
          exact mul_pos hr1B hs2
        · exact mul_pos hr1B (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith))

lemma separating_wedge_for_pair {W : Fin 6 → OpenWedge} (hGP : GP6 W)
    (h_int : ∀ r : Fin 6, 0 < ang02 (dir2 (W r)) ∧ ang02 (dir2 (W r)) < ang02 (dir1 (W r)) ∧
      ang02 (dir1 (W r)) < 2 * Real.pi ∧ ang02 (dir1 (W r)) - ang02 (dir2 (W r)) < Real.pi)
    {i j : Fin 6} (hij : i ≠ j)
    (h4 : ¬ (bdWedge (W i) ∩ bdWedge (W j)).ncard ≤ 3)
    {φ₁ φ₂ : ℝ} (hφ₁0 : 0 < φ₁) (hφ₁₂ : φ₁ < φ₂) (hφ₂2 : φ₂ < 2 * Real.pi)
    (hi_in : φ₁ < ang02 (dir2 (W i)) ∧ ang02 (dir1 (W i)) < φ₂)
    (hj_out : ang02 (dir1 (W j)) < φ₁ ∨ φ₂ < ang02 (dir2 (W j))) :
    ∃ V : OpenWedge, bdWedge V ⊆ bdWedge (W i) ∪ bdWedge (W j) ∧
      ((coneMem V (uvec φ₁) ∧ extConeMem V (uvec φ₂)) ∨
       (extConeMem V (uvec φ₁) ∧ coneMem V (uvec φ₂))) := by
  rcases hj_out with hj_lo | hj_hi
  · obtain ⟨V, hsub, hsep⟩ := separating_wedge_ordered hGP hij.symm
      (by rwa [Set.inter_comm])
      (h_int j).1 (by linarith [hj_lo, hi_in.1]) (h_int i).2.2.1
      (h_int j).2.1 (h_int j).2.2.2 (h_int i).2.1 (h_int i).2.2.2
      hφ₁0 hφ₂2 ⟨hj_lo, hi_in.1⟩ (Or.inr ⟨hi_in.2, hφ₂2⟩)
    exact ⟨V, hsub.trans (by rw [Set.union_comm]), hsep⟩
  · obtain ⟨V, hsub, hsep⟩ := separating_wedge_ordered hGP hij h4
      (h_int i).1 (by linarith [hi_in.2, hj_hi]) (h_int j).2.2.1
      (h_int i).2.1 (h_int i).2.2.2 (h_int j).2.1 (h_int j).2.2.2
      (hφ₁0.trans hφ₁₂) (hφ₁₂.trans hφ₂2) ⟨hi_in.2, hj_hi⟩ (Or.inl ⟨hφ₁0, hi_in.1⟩)
    refine ⟨V, hsub, ?_⟩
    rcases hsep with ⟨hc, he⟩ | ⟨he, hc⟩
    · exact Or.inr ⟨he, hc⟩
    · exact Or.inl ⟨hc, he⟩

lemma large_scale_memOpen (V : OpenWedge) {d : ℝ × ℝ} (hd : coneMem V d) :
    ∃ T₀ : ℝ, ∀ t ≥ T₀, V.MemOpen (t * d.1, t * d.2) := by
  let a₁ := V.u₁.1 * d.1 + V.u₁.2 * d.2
  let a₂ := V.u₂.1 * d.1 + V.u₂.2 * d.2
  let b₁ := V.u₁.1 * V.y.1 + V.u₁.2 * V.y.2
  let b₂ := V.u₂.1 * V.y.1 + V.u₂.2 * V.y.2
  have ha₁ : 0 < a₁ := hd.1
  have ha₂ : 0 < a₂ := hd.2
  refine ⟨max (b₁ / a₁) (b₂ / a₂) + 1, fun t ht => ?_⟩
  have ht1 : b₁ / a₁ < t := lt_of_le_of_lt (le_max_left _ _) (by linarith)
  have ht2 : b₂ / a₂ < t := lt_of_le_of_lt (le_max_right _ _) (by linarith)
  have h1 : b₁ < t * a₁ := (div_lt_iff₀ ha₁).mp ht1
  have h2 : b₂ < t * a₂ := (div_lt_iff₀ ha₂).mp ht2
  constructor
  · have e : V.u₁.1 * (t * d.1 - V.y.1) + V.u₁.2 * (t * d.2 - V.y.2) = t * a₁ - b₁ := by
      dsimp [a₁, b₁]; ring
    linarith
  · have e : V.u₂.1 * (t * d.1 - V.y.1) + V.u₂.2 * (t * d.2 - V.y.2) = t * a₂ - b₂ := by
      dsimp [a₂, b₂]; ring
    linarith

lemma large_scale_memExt (V : OpenWedge) {d : ℝ × ℝ} (hd : extConeMem V d) :
    ∃ T₀ : ℝ, ∀ t ≥ T₀, V.MemExt (t * d.1, t * d.2) := by
  rcases hd with h1 | h2
  · let a := V.u₁.1 * d.1 + V.u₁.2 * d.2
    let b := V.u₁.1 * V.y.1 + V.u₁.2 * V.y.2
    have ha : 0 < -a := neg_pos.mpr h1
    refine ⟨(-b) / (-a) + 1, fun t ht => ?_⟩
    have hmul : -b < t * (-a) := (div_lt_iff₀ ha).mp (by linarith)
    left
    have e : V.u₁.1 * (t * d.1 - V.y.1) + V.u₁.2 * (t * d.2 - V.y.2) = -(t * (-a) - (-b)) := by
      dsimp [a, b]; ring
    linarith
  · let a := V.u₂.1 * d.1 + V.u₂.2 * d.2
    let b := V.u₂.1 * V.y.1 + V.u₂.2 * V.y.2
    have ha : 0 < -a := neg_pos.mpr h2
    refine ⟨(-b) / (-a) + 1, fun t ht => ?_⟩
    have hmul : -b < t * (-a) := (div_lt_iff₀ ha).mp (by linarith)
    right
    have e : V.u₂.1 * (t * d.1 - V.y.1) + V.u₂.2 * (t * d.2 - V.y.2) = -(t * (-a) - (-b)) := by
      dsimp [a, b]; ring
    linarith

lemma extConeMem_of_not_onArc (W : OpenWedge) (φ : ℝ) (hno : ¬ onArc W φ) :
    extConeMem W (uvec φ) := by
  dsimp [onArc, closureConeMem] at hno
  rw [not_and_or] at hno
  rcases hno with h1 | h2
  · exact Or.inl (lt_of_not_ge h1)
  · exact Or.inr (lt_of_not_ge h2)

lemma comp_ne_of_sep_any_wedge {U : Set (ℝ × ℝ)} {V : OpenWedge}
    (hV_sub : bdWedge V ⊆ Uᶜ) {p₁ p₂ : ℝ × ℝ}
    (hp₁ : p₁ ∈ U) (hp₂ : p₂ ∈ U)
    (hsep : (V.MemOpen p₁ ∧ V.MemExt p₂) ∨ (V.MemExt p₁ ∧ V.MemOpen p₂)) :
    connectedComponentIn U p₁ ≠ connectedComponentIn U p₂ := by
  intro heq
  have hp₂_in : p₂ ∈ connectedComponentIn U p₁ := by rw [heq]; exact mem_connectedComponentIn hp₂
  have hp₁_in : p₁ ∈ connectedComponentIn U p₁ := mem_connectedComponentIn hp₁
  have hsub : connectedComponentIn U p₁ ⊆ {p | V.MemOpen p} ∪ {p | V.MemExt p} := by
    intro p hp
    have hpU : p ∈ U := connectedComponentIn_subset U p₁ hp
    have hp_nbd : p ∉ bdWedge V := fun hbd => hV_sub hbd hpU
    dsimp [bdWedge] at hp_nbd
    push Not at hp_nbd
    by_cases ho : V.MemOpen p
    · left; exact ho
    · right; exact hp_nbd ho
  have hdisj : Disjoint {p | V.MemOpen p} {p | V.MemExt p} := by
    rw [Set.disjoint_left]
    exact fun p ho he => memOpen_memExt_disjoint V p ⟨ho, he⟩
  rcases isPreconnected_connectedComponentIn.subset_or_subset
      (isOpen_memOpen V) (isOpen_memExt V) hdisj hsub with hO | hE
  · rcases hsep with ⟨_, he₂⟩ | ⟨he₁, _⟩
    · exact memOpen_memExt_disjoint V p₂ ⟨hO hp₂_in, he₂⟩
    · exact memOpen_memExt_disjoint V p₁ ⟨hO hp₁_in, he₁⟩
  · rcases hsep with ⟨ho₁, _⟩ | ⟨_, ho₂⟩
    · exact memOpen_memExt_disjoint V p₁ ⟨ho₁, hE hp₁_in⟩
    · exact memOpen_memExt_disjoint V p₂ ⟨ho₂, hE hp₂_in⟩

lemma comp_ne_of_sep_wedge_univ {W : Fin 6 → OpenWedge} {j : Fin 6} {p₁ p₂ : ℝ × ℝ}
    (hp₁ : p₁ ∈ (Set.univ : Set (ℝ × ℝ)) \ ⋃ i : Fin 6, bdWedge (W i))
    (hp₂ : p₂ ∈ (Set.univ : Set (ℝ × ℝ)) \ ⋃ i : Fin 6, bdWedge (W i))
    (hsep : ((W j).MemOpen p₁ ∧ (W j).MemExt p₂) ∨ ((W j).MemExt p₁ ∧ (W j).MemOpen p₂)) :
    connectedComponentIn ((Set.univ : Set (ℝ × ℝ)) \ ⋃ i : Fin 6, bdWedge (W i)) p₁ ≠
    connectedComponentIn ((Set.univ : Set (ℝ × ℝ)) \ ⋃ i : Fin 6, bdWedge (W i)) p₂ := by
  apply comp_ne_of_sep_any_wedge _ hp₁ hp₂ hsep
  intro p hp hpU
  exact hpU.2 (Set.mem_iUnion.mpr ⟨j, hp⟩)

private lemma six_wedges_gp_contradiction (W : Fin 6 → OpenWedge) (hGP : GP6 W)
    (h_all : ∀ m : Fin 6 → Bool, ∃ p : ℝ × ℝ, Realizes6 W m p) : False := by
  choose pm hpm using h_all
  let badPairs : Finset (Fin 6 × Fin 6) :=
    Finset.univ.filter (fun p : Fin 6 × Fin 6 =>
      p.1 < p.2 ∧ (bdWedge (W p.1) ∩ bdWedge (W p.2)).ncard ≤ 3)
  let U : Set (ℝ × ℝ) := Set.univ \ ⋃ i : Fin 6, bdWedge (W i)
  have hpm_mem : ∀ m : Fin 6 → Bool, pm m ∈ U := fun m => by
    refine ⟨trivial, fun h => ?_⟩
    rw [Set.mem_iUnion] at h
    obtain ⟨i, hi⟩ := h
    have hm := hpm m i
    by_cases hmi : m i
    · simp only [hmi, ↓reduceIte] at hm; exact hi.1 hm
    · simp only [hmi, Bool.false_eq_true, ↓reduceIte] at hm; exact hi.2 hm
  have hU_bound : (Comps U).encard ≤ (67 - badPairs.card : ℕ∞) := by
    have h_arr := arr_comps_bound_univ hGP Finset.univ
    have hU_eq : U = (Set.univ : Set (ℝ × ℝ)) \ ⋃ j ∈ (Finset.univ : Finset (Fin 6)), bdWedge (W j) := by
      ext p; simp [U]
    rw [← hU_eq] at h_arr
    let ordPairs : Finset (Fin 6 × Fin 6) := Finset.univ.filter (fun p : Fin 6 × Fin 6 => p.1 < p.2)
    have hord_card : ordPairs.card = 15 := by decide
    have hbad_sub : badPairs ⊆ ordPairs := fun p hp => by
      have hp' := (Finset.mem_filter.mp hp).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ p, hp'.1⟩
    have hsum_eq :
        (∑ i : Fin 6, ∑ j : Fin 6 with i < j, (bdWedge (W i) ∩ bdWedge (W j)).ncard) =
        ∑ p ∈ ordPairs, (bdWedge (W p.1) ∩ bdWedge (W p.2)).ncard := by
      have h1 : (∑ i : Fin 6, ∑ j : Fin 6 with i < j, (bdWedge (W i) ∩ bdWedge (W j)).ncard) =
          ∑ i : Fin 6, ∑ j : Fin 6,
            (if i < j then (bdWedge (W i) ∩ bdWedge (W j)).ncard else 0) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_filter]
      rw [h1, ← Fintype.sum_prod_type']
      rw [Finset.sum_filter]
    have hsum_nat :
        (∑ p ∈ ordPairs, (bdWedge (W p.1) ∩ bdWedge (W p.2)).ncard) ≤ 60 - badPairs.card := by
      have hsplit := Finset.sum_sdiff hbad_sub (f := fun p : Fin 6 × Fin 6 =>
        (bdWedge (W p.1) ∩ bdWedge (W p.2)).ncard)
      have hbad_le : (∑ p ∈ badPairs, (bdWedge (W p.1) ∩ bdWedge (W p.2)).ncard) ≤
          3 * badPairs.card := by
        calc (∑ p ∈ badPairs, (bdWedge (W p.1) ∩ bdWedge (W p.2)).ncard)
            ≤ ∑ _p ∈ badPairs, 3 := Finset.sum_le_sum fun p hp => (Finset.mem_filter.mp hp).2.2
          _ = 3 * badPairs.card := by simp [mul_comm]
      have hgood_le : (∑ p ∈ ordPairs \ badPairs, (bdWedge (W p.1) ∩ bdWedge (W p.2)).ncard) ≤
          4 * (ordPairs \ badPairs).card := by
        calc (∑ p ∈ ordPairs \ badPairs, (bdWedge (W p.1) ∩ bdWedge (W p.2)).ncard)
            ≤ ∑ _p ∈ ordPairs \ badPairs, 4 := Finset.sum_le_sum fun p hp => by
              have hlt : p.1 < p.2 := (Finset.mem_filter.mp (Finset.mem_sdiff.mp hp).1).2
              exact (inter_card_le_four hGP (ne_of_lt hlt)).2
          _ = 4 * (ordPairs \ badPairs).card := by simp [mul_comm]
      have hdisj_bad : Disjoint (ordPairs \ badPairs) badPairs :=
        Finset.disjoint_left.mpr fun _ h1 h2 => (Finset.mem_sdiff.mp h1).2 h2
      have hcard_sdiff : (ordPairs \ badPairs).card + badPairs.card = 15 := by
        rw [← Finset.card_union_of_disjoint hdisj_bad,
          Finset.sdiff_union_of_subset hbad_sub, hord_card]
      omega
    have h_enat : (Comps U).encard ≤ ((67 - badPairs.card : ℕ) : ℕ∞) := by
      have h1 : (1 + ((Finset.univ : Finset (Fin 6)).card : ℕ∞) +
          ∑ i ∈ (Finset.univ : Finset (Fin 6)),
            ∑ j ∈ (Finset.univ : Finset (Fin 6)) with i < j,
              ((bdWedge (W i) ∩ bdWedge (W j)).ncard : ℕ∞)) =
          ((7 + ∑ p ∈ ordPairs, (bdWedge (W p.1) ∩ bdWedge (W p.2)).ncard : ℕ) : ℕ∞) := by
        rw [← hsum_eq]
        simp only [Finset.card_univ, Fintype.card_fin]
        push_cast
        ring
      rw [h1] at h_arr
      have h_le67 : 7 + ∑ p ∈ ordPairs, (bdWedge (W p.1) ∩ bdWedge (W p.2)).ncard ≤ 67 - badPairs.card := by
        have hbad15 : badPairs.card ≤ 15 := by
          calc badPairs.card ≤ ordPairs.card := Finset.card_le_card hbad_sub
            _ = 15 := hord_card
        omega
      exact h_arr.trans (Nat.cast_le.mpr h_le67)
    simpa using h_enat
  have h_all_inj : ∀ m₁ m₂ : Fin 6 → Bool, m₁ ≠ m₂ →
      connectedComponentIn U (pm m₁) ≠ connectedComponentIn U (pm m₂) := by
    intro m₁ m₂ hne
    have hdiff : ∃ j : Fin 6, m₁ j ≠ m₂ j := by
      by_contra hnot; push Not at hnot; exact hne (funext hnot)
    obtain ⟨j, hj⟩ := hdiff
    refine comp_ne_of_sep_wedge_univ (j := j) (hpm_mem m₁) (hpm_mem m₂) ?_
    have h1 := hpm m₁ j
    have h2 := hpm m₂ j
    cases hm1 : m₁ j <;> cases hm2 : m₂ j
    · exact False.elim (hj (hm1.trans hm2.symm))
    · simp only [hm1, Bool.false_eq_true, ↓reduceIte] at h1
      simp only [hm2, ↓reduceIte] at h2
      exact Or.inr ⟨h1, h2⟩
    · simp only [hm1, ↓reduceIte] at h1
      simp only [hm2, Bool.false_eq_true, ↓reduceIte] at h2
      exact Or.inl ⟨h1, h2⟩
    · exact False.elim (hj (hm1.trans hm2.symm))
  by_cases hk4 : 4 ≤ badPairs.card
  · let f : (Fin 6 → Bool) → Set (ℝ × ℝ) := fun m => connectedComponentIn U (pm m)
    have hf_inj : Function.Injective f := fun a b hab => by
      by_contra hne; exact h_all_inj a b hne hab
    have hf_sub : Set.range f ⊆ Comps U := by
      rintro _ ⟨m, rfl⟩; exact ⟨pm m, hpm_mem m, rfl⟩
    have h64 : (64 : ℕ∞) ≤ (Comps U).encard := by
      calc (64 : ℕ∞)
          = (Fintype.card (Fin 6 → Bool) : ℕ∞) := by norm_num [Fintype.card_fun]
        _ = (Set.univ : Set (Fin 6 → Bool)).encard := by
            rw [Set.encard_univ, ENat.card_eq_coe_fintype_card]
        _ = (f '' Set.univ).encard := (hf_inj.injOn.encard_image).symm
        _ = (Set.range f).encard := by rw [Set.image_univ]
        _ ≤ (Comps U).encard := Set.encard_le_encard hf_sub
    have hle : (64 : ℕ∞) ≤ ((67 - badPairs.card : ℕ) : ℕ∞) := by
      have := h64.trans hU_bound
      simpa using this
    have hnat : 64 ≤ 67 - badPairs.card := Nat.cast_le.mp hle
    omega
  · have hk_le3 : badPairs.card ≤ 3 := by omega
    have hov_sub : Finset.univ.filter (fun p : Fin 6 × Fin 6 => p.1 < p.2 ∧ ovW W p.1 p.2) ⊆
        badPairs := by
      intro p hp
      obtain ⟨hlt, φ, hφ1, hφ2⟩ := (Finset.mem_filter.mp hp).2
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ p, hlt, ?_⟩
      by_contra h4
      exact quad_four_disjoint_cones hGP (ne_of_lt hlt) h4 (uvec_ne_zero φ) ⟨hφ1, hφ2⟩
    have hov_le3 : (Finset.univ.filter (fun p : Fin 6 × Fin 6 => p.1 < p.2 ∧ ovW W p.1 p.2)).card ≤ 3 :=
      (Finset.card_le_card hov_sub).trans hk_le3
    obtain ⟨θ₀, hθ₀⟩ := exists_uncovered_angle W hov_le3
    let c := Real.cos θ₀
    let s := Real.sin θ₀
    have hcs : c ^ 2 + s ^ 2 = 1 := Real.cos_sq_add_sin_sq θ₀
    let W' : Fin 6 → OpenWedge := fun i => rotWedge c s hcs (W i)
    have hGP' : GP6 W' := rotWedge_gp6 c s hcs hGP
    have h_int : ∀ r : Fin 6, 0 < ang02 (dir2 (W' r)) ∧ ang02 (dir2 (W' r)) < ang02 (dir1 (W' r)) ∧
        ang02 (dir1 (W' r)) < 2 * Real.pi ∧ ang02 (dir1 (W' r)) - ang02 (dir2 (W' r)) < Real.pi := by
      intro r
      obtain ⟨_, h1, h2, h3, h4⟩ := rot_zero_uncovered (W r) θ₀ (hθ₀ r)
      exact ⟨h1, h2, h3, h4⟩
    have h_all' : ∀ m : Fin 6 → Bool, ∃ p : ℝ × ℝ, Realizes6 W' m p := by
      intro m
      refine ⟨rotPt c s (pm m), fun i => ?_⟩
      have hm := hpm m i
      by_cases hmi : m i
      · simp only [hmi, ↓reduceIte] at hm ⊢
        exact (rotWedge_memOpen c s hcs (W i) (pm m)).mpr hm
      · simp only [hmi, Bool.false_eq_true, ↓reduceIte] at hm ⊢
        exact (rotWedge_memExt c s hcs (W i) (pm m)).mpr hm
    choose pm' hpm' using h_all'
    let badPairs' : Finset (Fin 6 × Fin 6) :=
      Finset.univ.filter (fun p : Fin 6 × Fin 6 =>
        p.1 < p.2 ∧ (bdWedge (W' p.1) ∩ bdWedge (W' p.2)).ncard ≤ 3)
    have hbad_eq : badPairs' = badPairs := by
      ext p; simp [badPairs', badPairs, W', rotWedge_inter_ncard]
    let a : Fin 6 → ℝ := fun r => ang02 (dir2 (W' r))
    let b : Fin 6 → ℝ := fun r => ang02 (dir1 (W' r))
    let ov_idx : Fin 6 → Fin 6 → Prop := fun i j => max (a i) (a j) ≤ min (b i) (b j)
    let E_ov : Finset (Fin 6 × Fin 6) :=
      Finset.univ.filter (fun p : Fin 6 × Fin 6 => p.1 < p.2 ∧ ov_idx p.1 p.2)
    have hE_ov_sub : E_ov ⊆ badPairs' := by
      intro p hp
      obtain ⟨hlt, hov⟩ := (Finset.mem_filter.mp hp).2
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ p, hlt, ?_⟩
      by_contra h4
      let φ := max (a p.1) (a p.2)
      have hφ1 : onArc (W' p.1) φ := by
        have hif : (if a p.1 ≤ b p.1 then b p.1 else b p.1 + 2 * Real.pi) = b p.1 :=
          if_pos (le_of_lt (h_int p.1).2.1)
        refine (onArc_iff_Icc (W' p.1) φ).mpr ⟨0, ?_, ?_⟩
        · simp; exact le_max_left _ _
        · simp only [Int.cast_zero, zero_mul, add_zero]; rw [hif]
          exact hov.trans (min_le_left _ _)
      have hφ2 : onArc (W' p.2) φ := by
        have hif : (if a p.2 ≤ b p.2 then b p.2 else b p.2 + 2 * Real.pi) = b p.2 :=
          if_pos (le_of_lt (h_int p.2).2.1)
        refine (onArc_iff_Icc (W' p.2) φ).mpr ⟨0, ?_, ?_⟩
        · simp; exact le_max_right _ _
        · simp only [Int.cast_zero, zero_mul, add_zero]; rw [hif]
          exact hov.trans (min_le_right _ _)
      exact quad_four_disjoint_cones hGP' (ne_of_lt hlt) h4 (uvec_ne_zero φ) ⟨hφ1, hφ2⟩
    let R_ov : Fin 6 → Fin 6 → Prop := fun i j => (i, j) ∈ E_ov ∨ (j, i) ∈ E_ov
    let S_ov : Setoid (Fin 6) := setoidOfRel R_ov
    let Q := Quotient S_ov
    let C_cls : Finset Q := Finset.univ.image (Quotient.mk S_ov)
    have h6_le : 6 ≤ C_cls.card + badPairs.card := by
      have h1 := six_le_quotCard_add_card E_ov
      have h2 : E_ov.card ≤ badPairs.card := by
        rw [← hbad_eq]; exact Finset.card_le_card hE_ov_sub
      change 6 ≤ C_cls.card + E_ov.card at h1
      omega
    let K : Q → Finset (Fin 6) := fun q =>
      Finset.univ.filter (fun i => Quotient.mk S_ov i = q)
    have hK_ne : ∀ q ∈ C_cls, (K q).Nonempty := fun q hq => by
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hq
      exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩⟩
    let L : Q → ℝ := fun q => if hq : q ∈ C_cls then (K q).inf' (hK_ne q hq) a else 0
    let R : Q → ℝ := fun q => if hq : q ∈ C_cls then (K q).sup' (hK_ne q hq) b else 0
    have hL_le_R : ∀ q ∈ C_cls, L q < R q := fun q hq => by
      obtain ⟨i, hi⟩ := hK_ne q hq
      have hLi : L q ≤ a i := by dsimp [L]; rw [dif_pos hq]; exact Finset.inf'_le a hi
      have hiR : b i ≤ R q := by dsimp [R]; rw [dif_pos hq]; exact Finset.le_sup' b hi
      linarith [(h_int i).2.1]
    have hL_pos : ∀ q ∈ C_cls, 0 < L q := fun q hq => by
      dsimp [L]; rw [dif_pos hq]
      rw [Finset.lt_inf'_iff]
      intro i _; exact (h_int i).1
    have hR_lt : ∀ q ∈ C_cls, R q < 2 * Real.pi := fun q hq => by
      dsimp [R]; rw [dif_pos hq]
      rw [Finset.sup'_lt_iff]
      intro i _; exact (h_int i).2.2.1
    have h_cover_Icc : ∀ q ∈ C_cls, ∀ x ∈ Set.Icc (L q) (R q),
        ∃ i ∈ K q, x ∈ Set.Icc (a i) (b i) := by
      intro q hq x hx
      by_contra hnone
      push Not at hnone
      let KL := (K q).filter (fun i => b i < x)
      let KR := (K q).filter (fun i => x < a i)
      have hpart : ∀ i ∈ K q, i ∈ KL ∨ i ∈ KR := by
        intro i hi
        have hnot := hnone i hi
        rw [Set.mem_Icc, not_and_or, not_le, not_le] at hnot
        rcases hnot with h1 | h2
        · right; exact Finset.mem_filter.mpr ⟨hi, h1⟩
        · left; exact Finset.mem_filter.mpr ⟨hi, h2⟩
      have hKL_ne : KL.Nonempty := by
        have hx1 : L q ≤ x := hx.1
        dsimp [L] at hx1
        rw [dif_pos hq] at hx1
        obtain ⟨i₀, hi₀, hai₀⟩ := Finset.exists_mem_eq_inf' (hK_ne q hq) a
        rw [hai₀] at hx1
        rcases hpart i₀ hi₀ with h | h
        · exact ⟨i₀, h⟩
        · exfalso; have := (Finset.mem_filter.mp h).2; linarith
      have hKR_ne : KR.Nonempty := by
        have hx2 : x ≤ R q := hx.2
        dsimp [R] at hx2
        rw [dif_pos hq] at hx2
        obtain ⟨i₁, hi₁, hbi₁⟩ := Finset.exists_mem_eq_sup' (hK_ne q hq) b
        rw [hbi₁] at hx2
        rcases hpart i₁ hi₁ with h | h
        · exfalso; have := (Finset.mem_filter.mp h).2; linarith
        · exact ⟨i₁, h⟩
      obtain ⟨i₀, hi₀⟩ := hKL_ne
      obtain ⟨i₁, hi₁⟩ := hKR_ne
      have heqv : Relation.EqvGen R_ov i₀ i₁ := by
        have h0 : Quotient.mk S_ov i₀ = q :=
          (Finset.mem_filter.mp (Finset.mem_filter.mp hi₀).1).2
        have h1 : Quotient.mk S_ov i₁ = q :=
          (Finset.mem_filter.mp (Finset.mem_filter.mp hi₁).1).2
        exact Quotient.exact (h0.trans h1.symm)
      have h_no_cross : ∀ u v : Fin 6, Relation.EqvGen R_ov u v → u ∈ K q →
          (u ∈ KL ↔ v ∈ KL) := by
        intro u v huv
        induction huv with
        | rel x y hxy =>
          intro hxK
          have hyK : y ∈ K q := by
            have hx_eq : Quotient.mk S_ov x = q := (Finset.mem_filter.mp hxK).2
            refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
            rw [← hx_eq]
            exact Quotient.sound (Relation.EqvGen.symm _ _ (Relation.EqvGen.rel x y hxy))
          have hov : ov_idx x y := by
            rcases hxy with h | h
            · exact (Finset.mem_filter.mp h).2.2
            · have := (Finset.mem_filter.mp h).2.2
              dsimp [ov_idx] at this ⊢; rwa [max_comm, min_comm]
          have h_no_LR : ¬ (x ∈ KL ∧ y ∈ KR) ∧ ¬ (y ∈ KL ∧ x ∈ KR) := by
            constructor
            · rintro ⟨hxL, hyR⟩
              have h1 := (Finset.mem_filter.mp hxL).2
              have h2 := (Finset.mem_filter.mp hyR).2
              have : min (b x) (b y) < max (a x) (a y) :=
                lt_of_le_of_lt (min_le_left _ _) (lt_of_lt_of_le (h1.trans h2) (le_max_right _ _))
              linarith [hov]
            · rintro ⟨hyL, hxR⟩
              have h1 := (Finset.mem_filter.mp hyL).2
              have h2 := (Finset.mem_filter.mp hxR).2
              have : min (b x) (b y) < max (a x) (a y) :=
                lt_of_le_of_lt (min_le_right _ _) (lt_of_lt_of_le (h1.trans h2) (le_max_left _ _))
              linarith [hov]
          constructor
          · intro hxL
            rcases hpart y hyK with hyL | hyR
            · exact hyL
            · exact False.elim (h_no_LR.1 ⟨hxL, hyR⟩)
          · intro hyL
            rcases hpart x hxK with hxL | hxR
            · exact hxL
            · exact False.elim (h_no_LR.2 ⟨hyL, hxR⟩)
        | refl => intro _; exact Iff.rfl
        | symm x y hxy ih =>
          intro hyK
          have hxK : x ∈ K q := by
            have hy_eq : Quotient.mk S_ov y = q := (Finset.mem_filter.mp hyK).2
            refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
            rw [← hy_eq]; exact Quotient.sound hxy
          exact (ih hxK).symm
        | trans x y z hxy hyz ih1 ih2 =>
          intro hxK
          have hyK : y ∈ K q := by
            have hx_eq : Quotient.mk S_ov x = q := (Finset.mem_filter.mp hxK).2
            refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
            rw [← hx_eq]; exact Quotient.sound (Relation.EqvGen.symm _ _ hxy)
          exact (ih1 hxK).trans (ih2 hyK)
      have hi1_KL : i₁ ∈ KL := (h_no_cross i₀ i₁ heqv (Finset.mem_filter.mp hi₀).1).mp hi₀
      have h_b : b i₁ < x := (Finset.mem_filter.mp hi1_KL).2
      have h_a : x < a i₁ := (Finset.mem_filter.mp hi₁).2
      linarith [(h_int i₁).2.1]
    have h_disj_LR : ∀ q₁ ∈ C_cls, ∀ q₂ ∈ C_cls, q₁ ≠ q₂ → R q₁ < L q₂ ∨ R q₂ < L q₁ := by
      intro q₁ hq₁ q₂ hq₂ hne
      by_contra hnot
      rw [not_or, not_lt, not_lt] at hnot
      have hLR1 : L q₁ ≤ R q₁ := le_of_lt (hL_le_R q₁ hq₁)
      have hLR2 : L q₂ ≤ R q₂ := le_of_lt (hL_le_R q₂ hq₂)
      let x := max (L q₁) (L q₂)
      have hx1 : x ∈ Set.Icc (L q₁) (R q₁) := ⟨le_max_left _ _, max_le hLR1 hnot.1⟩
      have hx2 : x ∈ Set.Icc (L q₂) (R q₂) := ⟨le_max_right _ _, max_le hnot.2 hLR2⟩
      obtain ⟨i₁, hi₁, hxi₁⟩ := h_cover_Icc q₁ hq₁ x hx1
      obtain ⟨i₂, hi₂, hxi₂⟩ := h_cover_Icc q₂ hq₂ x hx2
      have hij : i₁ ≠ i₂ := by
        rintro rfl
        have e1 : Quotient.mk S_ov i₁ = q₁ := (Finset.mem_filter.mp hi₁).2
        have e2 : Quotient.mk S_ov i₁ = q₂ := (Finset.mem_filter.mp hi₂).2
        exact hne (e1.symm.trans e2)
      have hov : ov_idx i₁ i₂ :=
        le_trans (max_le hxi₁.1 hxi₂.1) (le_min hxi₁.2 hxi₂.2)
      have heq_q : q₁ = q₂ := by
        have e1 : Quotient.mk S_ov i₁ = q₁ := (Finset.mem_filter.mp hi₁).2
        have e2 : Quotient.mk S_ov i₂ = q₂ := (Finset.mem_filter.mp hi₂).2
        rw [← e1, ← e2]
        apply Quotient.sound
        apply Relation.EqvGen.rel
        rcases lt_or_gt_of_ne hij with hlt | hgt
        · left; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt, hov⟩
        · right; refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, hgt, ?_⟩
          dsimp [ov_idx] at hov ⊢; rwa [max_comm, min_comm]
      exact hne heq_q
    have hL_inj : Set.InjOn L (C_cls : Set Q) := fun q₁ hq₁ q₂ hq₂ heq => by
      by_contra hne
      rcases h_disj_LR q₁ hq₁ q₂ hq₂ hne with h1 | h2
      · linarith [hL_le_R q₁ hq₁]
      · linarith [hL_le_R q₂ hq₂]
    let L_vals : Finset ℝ := C_cls.image L
    let ls : List ℝ := L_vals.sort (· ≤ ·)
    have hls_sorted : ls.SortedLT := Finset.sortedLT_sort _
    have hls_len : ls.length = C_cls.card := by
      rw [Finset.length_sort, Finset.card_image_of_injOn hL_inj]
    have hC_pos : 0 < ls.length := by
      have : 0 < C_cls.card := by
        refine Finset.card_pos.mpr ⟨Quotient.mk S_ov 0, Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩⟩
      omega
    have h_q_of_val : ∀ k : Fin ls.length, ∃ q ∈ C_cls, L q = ls.get k := fun k => by
      have hmem : ls.get k ∈ L_vals := (Finset.mem_sort (· ≤ ·)).mp (List.get_mem _ _)
      exact Finset.mem_image.mp hmem
    let qAt : Fin ls.length → Q := fun k => (h_q_of_val k).choose
    have hqAt_mem : ∀ k, qAt k ∈ C_cls := fun k => (h_q_of_val k).choose_spec.1
    have hqAt_L : ∀ k, L (qAt k) = ls.get k := fun k => (h_q_of_val k).choose_spec.2
    have hqAt_inj : Function.Injective qAt := fun k₁ k₂ heq => by
      have hget : ls.get k₁ = ls.get k₂ := by rw [← hqAt_L k₁, ← hqAt_L k₂, heq]
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · linarith [hls_sorted hlt]
      · linarith [hls_sorted hgt]
    have hqAt_surj : ∀ q ∈ C_cls, ∃ k : Fin ls.length, qAt k = q := by
      intro q hq
      have hmem : L q ∈ ls := (Finset.mem_sort (· ≤ ·)).mpr (Finset.mem_image.mpr ⟨q, hq, rfl⟩)
      obtain ⟨k, hk⟩ := List.mem_iff_get.mp hmem
      refine ⟨k, hL_inj (hqAt_mem k) hq (by rw [hqAt_L k, hk])⟩
    have h_step_RL : ∀ k₁ k₂ : Fin ls.length, k₁ < k₂ → R (qAt k₁) < L (qAt k₂) := by
      intro k₁ k₂ hlt
      have hne : qAt k₁ ≠ qAt k₂ := fun h => ne_of_lt hlt (hqAt_inj h)
      rcases h_disj_LR (qAt k₁) (hqAt_mem k₁) (qAt k₂) (hqAt_mem k₂) hne with h1 | h2
      · exact h1
      · exfalso
        have hL_lt : L (qAt k₁) < L (qAt k₂) := by rw [hqAt_L k₁, hqAt_L k₂]; exact hls_sorted hlt
        linarith [hL_le_R (qAt k₂) (hqAt_mem k₂)]
    let φ : Fin ls.length → ℝ := fun s =>
      if hs : s.val = 0 then L (qAt ⟨0, hC_pos⟩) / 2
      else (R (qAt ⟨s.val - 1, by omega⟩) + L (qAt s)) / 2
    have hφ_pos : ∀ s, 0 < φ s := fun s => by
      dsimp [φ]; split_ifs
      · linarith [hL_pos (qAt ⟨0, hC_pos⟩) (hqAt_mem _)]
      · have h1 := hL_pos (qAt ⟨s.val - 1, by omega⟩) (hqAt_mem _)
        have h2 := hL_le_R (qAt ⟨s.val - 1, by omega⟩) (hqAt_mem _)
        have h3 := hL_pos (qAt s) (hqAt_mem s)
        linarith
    have hφ_lt_L : ∀ s, φ s < L (qAt s) := fun s => by
      dsimp [φ]; split_ifs with hs
      · have hs0 : s = ⟨0, hC_pos⟩ := Fin.ext hs
        rw [hs0]; linarith [hL_pos (qAt ⟨0, hC_pos⟩) (hqAt_mem _)]
      · have hlt : (⟨s.val - 1, by omega⟩ : Fin ls.length) < s := by
          change s.val - 1 < s.val; omega
        linarith [h_step_RL _ s hlt]
    have hR_lt_φ : ∀ s t : Fin ls.length, s < t → R (qAt s) < φ t := fun s t hst => by
      dsimp [φ]
      have ht0 : t.val ≠ 0 := by
        intro h; have := hst; change s.val < t.val at this; omega
      split_ifs with ht0'
      · exact False.elim (ht0 ht0')
      · have hle : (⟨s.val, s.isLt⟩ : Fin ls.length) ≤ ⟨t.val - 1, by omega⟩ := by
          change s.val ≤ t.val - 1; omega
        have hR_le : R (qAt s) ≤ R (qAt ⟨t.val - 1, by omega⟩) := by
          rcases eq_or_lt_of_le hle with heq | hlt'
          · have h_eq_idx : s = ⟨t.val - 1, by omega⟩ := Fin.ext (by simpa using congrArg Fin.val heq)
            exact le_of_eq (congrArg (fun k => R (qAt k)) h_eq_idx)
          · have h1 := h_step_RL s ⟨t.val - 1, by omega⟩ hlt'
            have h2 := hL_le_R (qAt ⟨t.val - 1, by omega⟩) (hqAt_mem _)
            linarith
        have hlt_step : R (qAt ⟨t.val - 1, by omega⟩) < L (qAt t) :=
          h_step_RL ⟨t.val - 1, by omega⟩ t (by change t.val - 1 < t.val; omega)
        linarith
    have hφ_lt_2pi : ∀ s, φ s < 2 * Real.pi := fun s =>
      (hφ_lt_L s).trans ((hL_le_R (qAt s) (hqAt_mem s)).trans (hR_lt (qAt s) (hqAt_mem s)))
    have hφ_not_arc : ∀ s (r : Fin 6), ¬ onArc (W' r) (φ s) := fun s r hon => by
      have hiff := onArc_iff_Icc (W' r) (φ s)
      have hif : (if a r ≤ b r then b r else b r + 2 * Real.pi) = b r :=
        if_pos (le_of_lt (h_int r).2.1)
      obtain ⟨k_int, hk1, hk2⟩ := hiff.mp hon
      rw [hif] at hk2
      have hk0 : k_int = 0 := by
        have h2pi : 0 < 2 * Real.pi := by linarith [Real.pi_pos]
        by_contra hne
        rcases lt_or_gt_of_ne hne with hlt | hgt
        · have hk_le : (k_int : ℝ) ≤ -1 := by exact_mod_cast (show k_int ≤ -1 by omega)
          have : b r + k_int * (2 * Real.pi) ≤ b r - 2 * Real.pi := by nlinarith
          linarith [hφ_pos s, (h_int r).2.2.1]
        · have hk_ge : (1 : ℝ) ≤ (k_int : ℝ) := by exact_mod_cast (show 1 ≤ k_int by omega)
          have : a r + 2 * Real.pi ≤ a r + k_int * (2 * Real.pi) := by nlinarith
          linarith [hφ_lt_2pi s, (h_int r).1]
      subst hk0
      simp only [Int.cast_zero, zero_mul, add_zero] at hk1 hk2
      let q_r := Quotient.mk S_ov r
      have hqr_mem : q_r ∈ C_cls := Finset.mem_image.mpr ⟨r, Finset.mem_univ _, rfl⟩
      obtain ⟨k_r, hk_r⟩ := hqAt_surj q_r hqr_mem
      have hrK : r ∈ K (qAt k_r) := by
        rw [hk_r]; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
      have hLa : L (qAt k_r) ≤ a r := by
        dsimp [L]; rw [dif_pos (hqAt_mem k_r)]; exact Finset.inf'_le a hrK
      have hbR : b r ≤ R (qAt k_r) := by
        dsimp [R]; rw [dif_pos (hqAt_mem k_r)]; exact Finset.le_sup' b hrK
      rcases lt_trichotomy s k_r with hlt | rfl | hgt
      · have h1 := hR_lt_φ s k_r hlt
        have h2 := hφ_lt_L k_r
        have h3 := hφ_lt_L s
        have h4 := hL_le_R (qAt s) (hqAt_mem s)
        linarith
      · linarith [hφ_lt_L s]
      · linarith [hR_lt_φ k_r s hgt]
    have h_sep_pair : ∀ s t : Fin ls.length, s < t →
        ∃ V : OpenWedge, bdWedge V ⊆ ⋃ r : Fin 6, bdWedge (W' r) ∧
          ((coneMem V (uvec (φ s)) ∧ extConeMem V (uvec (φ t))) ∨
           (extConeMem V (uvec (φ s)) ∧ coneMem V (uvec (φ t)))) := by
      intro s t hst
      let side1 : Finset (Fin 6) := Finset.univ.filter (fun r => φ s < a r ∧ b r < φ t)
      let side2 : Finset (Fin 6) := Finset.univ.filter (fun r => b r < φ s ∨ φ t < a r)
      have hs1_ne : side1.Nonempty := by
        obtain ⟨r, hr⟩ := hK_ne (qAt s) (hqAt_mem s)
        have hLa : L (qAt s) ≤ a r := by
          dsimp [L]; rw [dif_pos (hqAt_mem s)]; exact Finset.inf'_le a hr
        have hbR : b r ≤ R (qAt s) := by
          dsimp [R]; rw [dif_pos (hqAt_mem s)]; exact Finset.le_sup' b hr
        exact ⟨r, Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          lt_of_lt_of_le (hφ_lt_L s) hLa, lt_of_le_of_lt hbR (hR_lt_φ s t hst)⟩⟩
      have hs2_ne : side2.Nonempty := by
        let last : Fin ls.length := ⟨ls.length - 1, Nat.sub_lt hC_pos Nat.one_pos⟩
        obtain ⟨r, hr⟩ := hK_ne (qAt last) (hqAt_mem last)
        have hLa : L (qAt last) ≤ a r := by
          dsimp [L]; rw [dif_pos (hqAt_mem last)]; exact Finset.inf'_le a hr
        have h_lt : φ t < L (qAt last) := by
          have hle : t ≤ last := Fin.mk_le_mk.mpr (Nat.le_sub_one_of_lt t.isLt)
          rcases eq_or_lt_of_le hle with rfl | hlt_last
          · exact hφ_lt_L last
          · have h1 := hR_lt_φ t last hlt_last
            have h2 := hL_le_R (qAt t) (hqAt_mem t)
            have h3 := hφ_lt_L t
            have h4 := hφ_lt_L last
            linarith
        exact ⟨r, Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr (lt_of_lt_of_le h_lt hLa)⟩⟩
      have hdisj_sides : Disjoint side1 side2 := by
        rw [Finset.disjoint_left]
        intro r hr1 hr2
        have h1 := (Finset.mem_filter.mp hr1).2
        rcases (Finset.mem_filter.mp hr2).2 with h2 | h2 <;> linarith [(h_int r).2.1]
      have hunion_sides : side1 ∪ side2 = Finset.univ := by
        ext r
        simp only [side1, side2, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
        let q_r := Quotient.mk S_ov r
        obtain ⟨k_r, hk_r⟩ := hqAt_surj q_r (Finset.mem_image.mpr ⟨r, Finset.mem_univ _, rfl⟩)
        have hrK : r ∈ K (qAt k_r) := by
          rw [hk_r]; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
        have hLa : L (qAt k_r) ≤ a r := by
          dsimp [L]; rw [dif_pos (hqAt_mem k_r)]; exact Finset.inf'_le a hrK
        have hbR : b r ≤ R (qAt k_r) := by
          dsimp [R]; rw [dif_pos (hqAt_mem k_r)]; exact Finset.le_sup' b hrK
        rcases lt_or_ge k_r s with hk_s | hk_s
        · right; left; exact lt_of_le_of_lt hbR (hR_lt_φ k_r s hk_s)
        · rcases lt_or_ge k_r t with hk_t | hk_t
          · left
            have h1 : φ s < a r := by
              rcases eq_or_lt_of_le hk_s with heq | hlt
              · rw [← heq] at hLa; exact lt_of_lt_of_le (hφ_lt_L s) hLa
              · have h1' := hR_lt_φ s k_r hlt
                have h2' := hL_le_R (qAt s) (hqAt_mem s)
                have h3' := hφ_lt_L s
                have h4' := hφ_lt_L k_r
                linarith
            exact ⟨h1, lt_of_le_of_lt hbR (hR_lt_φ k_r t hk_t)⟩
          · right; right
            have h1 : φ t < a r := by
              rcases eq_or_lt_of_le hk_t with heq | hlt
              · rw [← heq] at hLa; exact lt_of_lt_of_le (hφ_lt_L t) hLa
              · have h1' := hR_lt_φ t k_r hlt
                have h2' := hL_le_R (qAt t) (hqAt_mem t)
                have h3' := hφ_lt_L t
                have h4' := hφ_lt_L k_r
                linarith
            exact h1
      have hsum_card : side1.card + side2.card = 6 := by
        rw [← Finset.card_union_of_disjoint hdisj_sides, hunion_sides, Finset.card_univ, Fintype.card_fin]
      have hprod_ge5 : 5 ≤ side1.card * side2.card := by
        have h1 : 1 ≤ side1.card := Finset.card_pos.mpr hs1_ne
        have h2 : 1 ≤ side2.card := Finset.card_pos.mpr hs2_ne
        nlinarith
      let pairMap : Fin 6 × Fin 6 → Fin 6 × Fin 6 := fun p =>
        if p.1 < p.2 then (p.1, p.2) else (p.2, p.1)
      have hinj_pair : Set.InjOn pairMap (side1 ×ˢ side2 : Finset (Fin 6 × Fin 6)) := by
        intro p hp q hq heq
        obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp
        obtain ⟨hq1, hq2⟩ := Finset.mem_product.mp hq
        have hp_ne : p.1 ≠ p.2 := fun h =>
          Finset.disjoint_left.mp hdisj_sides hp1 (h ▸ hp2)
        have hq_ne : q.1 ≠ q.2 := fun h =>
          Finset.disjoint_left.mp hdisj_sides hq1 (h ▸ hq2)
        dsimp [pairMap] at heq
        split_ifs at heq with hp_lt hq_lt hq_lt
        · exact heq
        · exfalso
          obtain ⟨e1, e2⟩ := Prod.mk.inj heq
          rw [e1] at hp1
          exact Finset.disjoint_left.mp hdisj_sides hp1 hq2
        · exfalso
          obtain ⟨e1, e2⟩ := Prod.mk.inj heq
          rw [← e1] at hq1
          exact Finset.disjoint_left.mp hdisj_sides hq1 hp2
        · obtain ⟨e1, e2⟩ := Prod.mk.inj heq
          exact Prod.ext e2 e1
      have h_exists_good : ∃ p ∈ side1 ×ˢ side2, pairMap p ∉ badPairs' := by
        by_contra hsub_bad
        push Not at hsub_bad
        have hsub : (side1 ×ˢ side2).image pairMap ⊆ badPairs' :=
          Finset.image_subset_iff.mpr hsub_bad
        have hle1 : side1.card * side2.card ≤ badPairs'.card := by
          rw [← Finset.card_product, ← Finset.card_image_of_injOn hinj_pair]
          exact Finset.card_le_card hsub
        rw [hbad_eq] at hle1
        omega
      obtain ⟨⟨i, j⟩, hij_mem, hij_good⟩ := h_exists_good
      obtain ⟨hi_s1, hj_s2⟩ := Finset.mem_product.mp hij_mem
      have hij_ne : i ≠ j := fun h =>
        Finset.disjoint_left.mp hdisj_sides hi_s1 (h ▸ hj_s2)
      have h4 : ¬ (bdWedge (W' i) ∩ bdWedge (W' j)).ncard ≤ 3 := by
        intro hle3
        apply hij_good
        dsimp [pairMap]
        split_ifs with hlt
        · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt, hle3⟩
        · have hgt : j < i := lt_of_le_of_ne (not_lt.mp hlt) hij_ne.symm
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hgt, by rwa [Set.inter_comm]⟩
      obtain ⟨V, hV_sub, hV_sep⟩ := separating_wedge_for_pair hGP' h_int hij_ne h4
        (hφ_pos s) (by
          have h1 := hφ_lt_L s
          have h2 := hL_le_R (qAt s) (hqAt_mem s)
          have h3 := hR_lt_φ s t hst
          linarith)
        (hφ_lt_2pi t) (Finset.mem_filter.mp hi_s1).2 (Finset.mem_filter.mp hj_s2).2
      refine ⟨V, hV_sub.trans ?_, hV_sep⟩
      intro p hp
      rcases hp with hp | hp
      · exact Set.mem_iUnion.mpr ⟨i, hp⟩
      · exact Set.mem_iUnion.mpr ⟨j, hp⟩
    let pairType := {p : Fin ls.length × Fin ls.length // p.1 < p.2}
    have h_sep_T : ∀ s t : Fin ls.length, s < t →
        ∃ V : OpenWedge, bdWedge V ⊆ ⋃ r : Fin 6, bdWedge (W' r) ∧
          ∃ T₀ : ℝ, ∀ τ ≥ T₀,
            (V.MemOpen (τ * (uvec (φ s)).1, τ * (uvec (φ s)).2) ∧
             V.MemExt (τ * (uvec (φ t)).1, τ * (uvec (φ t)).2)) ∨
            (V.MemExt (τ * (uvec (φ s)).1, τ * (uvec (φ s)).2) ∧
             V.MemOpen (τ * (uvec (φ t)).1, τ * (uvec (φ t)).2)) := by
      intro s t hst
      obtain ⟨V, hV_sub, hV_sep⟩ := h_sep_pair s t hst
      rcases hV_sep with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · obtain ⟨T1, hT1⟩ := large_scale_memOpen V h1
        obtain ⟨T2, hT2⟩ := large_scale_memExt V h2
        exact ⟨V, hV_sub, max T1 T2, fun τ hτ =>
          Or.inl ⟨hT1 τ (le_trans (le_max_left _ _) hτ), hT2 τ (le_trans (le_max_right _ _) hτ)⟩⟩
      · obtain ⟨T1, hT1⟩ := large_scale_memExt V h1
        obtain ⟨T2, hT2⟩ := large_scale_memOpen V h2
        exact ⟨V, hV_sub, max T1 T2, fun τ hτ =>
          Or.inr ⟨hT1 τ (le_trans (le_max_left _ _) hτ), hT2 τ (le_trans (le_max_right _ _) hτ)⟩⟩
    let T_ext : Fin ls.length × Fin 6 → ℝ := fun ⟨s, r⟩ =>
      (large_scale_memExt (W' r) (extConeMem_of_not_onArc (W' r) (φ s) (hφ_not_arc s r))).choose
    have hT_ext : ∀ s r τ, T_ext (s, r) ≤ τ → (W' r).MemExt (τ * (uvec (φ s)).1, τ * (uvec (φ s)).2) :=
      fun s r => (large_scale_memExt (W' r) (extConeMem_of_not_onArc (W' r) (φ s) (hφ_not_arc s r))).choose_spec
    let T_sep : pairType → ℝ := fun p => (h_sep_T p.1.1 p.1.2 p.2).choose_spec.2.choose
    let M_ext : ℝ := max 0 ((Finset.univ : Finset (Fin ls.length × Fin 6)).sup'
      ⟨(⟨0, hC_pos⟩, 0), Finset.mem_univ _⟩ T_ext)
    let M_sep : ℝ := if hne : (Finset.univ : Finset pairType).Nonempty then
      max 0 ((Finset.univ : Finset pairType).sup' hne T_sep) else 0
    let T : ℝ := M_ext + M_sep
    have hT_ext_le : ∀ s r, T_ext (s, r) ≤ T := fun s r => by
      have h1 : T_ext (s, r) ≤ M_ext := le_trans (Finset.le_sup' T_ext (Finset.mem_univ (s, r))) (le_max_right _ _)
      have h2 : 0 ≤ M_sep := by dsimp [M_sep]; split_ifs <;> [exact le_max_left _ _; exact le_rfl]
      linarith
    have hT_sep_le : ∀ p : pairType, T_sep p ≤ T := fun p => by
      have h1 : 0 ≤ M_ext := le_max_left _ _
      have hne : (Finset.univ : Finset pairType).Nonempty := ⟨p, Finset.mem_univ p⟩
      have h2 : T_sep p ≤ M_sep := by
        dsimp [M_sep]; rw [dif_pos hne]
        exact le_trans (Finset.le_sup' T_sep (Finset.mem_univ p)) (le_max_right _ _)
      linarith
    let U' : Set (ℝ × ℝ) := Set.univ \ ⋃ i : Fin 6, bdWedge (W' i)
    let q : Fin ls.length → ℝ × ℝ := fun s => (T * (uvec (φ s)).1, T * (uvec (φ s)).2)
    have hq_ext : ∀ s r, (W' r).MemExt (q s) := fun s r => hT_ext s r T (hT_ext_le s r)
    have hq_mem : ∀ s, q s ∈ U' := fun s => by
      refine ⟨trivial, fun h => ?_⟩
      rw [Set.mem_iUnion] at h
      obtain ⟨r, hr⟩ := h
      exact hr.2 (hq_ext s r)
    have hq_inj : ∀ s t : Fin ls.length, s ≠ t →
        connectedComponentIn U' (q s) ≠ connectedComponentIn U' (q t) := by
      intro s t hne
      rcases lt_or_gt_of_ne hne with hst | hts
      · let p : pairType := ⟨(s, t), hst⟩
        have hspec := (h_sep_T s t hst).choose_spec
        have hV_sub := hspec.1
        have hV_sep := hspec.2.choose_spec T (hT_sep_le p)
        refine comp_ne_of_sep_any_wedge ?_ (hq_mem s) (hq_mem t) hV_sep
        intro z hz hzU
        exact hzU.2 (hV_sub hz)
      · let p : pairType := ⟨(t, s), hts⟩
        have hspec := (h_sep_T t s hts).choose_spec
        have hV_sub := hspec.1
        have hV_sep := hspec.2.choose_spec T (hT_sep_le p)
        have hV_sep' : ((h_sep_T t s hts).choose.MemOpen (q s) ∧ (h_sep_T t s hts).choose.MemExt (q t)) ∨
            ((h_sep_T t s hts).choose.MemExt (q s) ∧ (h_sep_T t s hts).choose.MemOpen (q t)) := by
          rcases hV_sep with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · exact Or.inr ⟨h2, h1⟩
          · exact Or.inl ⟨h2, h1⟩
        refine comp_ne_of_sep_any_wedge ?_ (hq_mem s) (hq_mem t) hV_sep'
        intro z hz hzU
        exact hzU.2 (hV_sub hz)
    let m0 : Fin 6 → Bool := fun _ => false
    let nonzeroMasks := (Finset.univ : Finset (Fin 6 → Bool)).erase m0
    let nzType := {m : Fin 6 → Bool // m ∈ nonzeroMasks}
    let idxType := Sum nzType (Fin ls.length)
    let ptAll : idxType → ℝ × ℝ := Sum.elim (fun m => pm' m.1) q
    have hpm'_mem : ∀ m : Fin 6 → Bool, pm' m ∈ U' := fun m => by
      refine ⟨trivial, fun h => ?_⟩
      rw [Set.mem_iUnion] at h
      obtain ⟨r, hr⟩ := h
      have hm := hpm' m r
      by_cases hmr : m r
      · simp only [hmr, ↓reduceIte] at hm; exact hr.1 hm
      · simp only [hmr, Bool.false_eq_true, ↓reduceIte] at hm; exact hr.2 hm
    have hptAll_mem : ∀ x : idxType, ptAll x ∈ U' := by
      rintro (m | s)
      · exact hpm'_mem m.1
      · exact hq_mem s
    have hptAll_inj : ∀ x y : idxType, x ≠ y →
        connectedComponentIn U' (ptAll x) ≠ connectedComponentIn U' (ptAll y) := by
      rintro (m₁ | s₁) (m₂ | s₂) hne
      · have hm_ne : m₁.1 ≠ m₂.1 := fun h => hne (congrArg Sum.inl (Subtype.ext h))
        have hdiff : ∃ j : Fin 6, m₁.1 j ≠ m₂.1 j := by
          by_contra hnot; push Not at hnot; exact hm_ne (funext hnot)
        obtain ⟨j, hj⟩ := hdiff
        refine comp_ne_of_sep_wedge_univ (j := j) (hpm'_mem m₁.1) (hpm'_mem m₂.1) ?_
        have h1 := hpm' m₁.1 j
        have h2 := hpm' m₂.1 j
        cases hm1 : m₁.1 j <;> cases hm2 : m₂.1 j
        · exact False.elim (hj (hm1.trans hm2.symm))
        · simp only [hm1, Bool.false_eq_true, ↓reduceIte] at h1
          simp only [hm2, ↓reduceIte] at h2
          exact Or.inr ⟨h1, h2⟩
        · simp only [hm1, ↓reduceIte] at h1
          simp only [hm2, Bool.false_eq_true, ↓reduceIte] at h2
          exact Or.inl ⟨h1, h2⟩
        · exact False.elim (hj (hm1.trans hm2.symm))
      · have hne0 : m₁.1 ≠ m0 := (Finset.mem_erase.mp m₁.2).1
        have hex : ∃ j : Fin 6, m₁.1 j = true := by
          by_contra hnot; push Not at hnot
          apply hne0; ext j
          exact Bool.eq_false_iff.mpr (hnot j)
        obtain ⟨j, hj⟩ := hex
        refine comp_ne_of_sep_wedge_univ (j := j) (hpm'_mem m₁.1) (hq_mem s₂) ?_
        have h1 := hpm' m₁.1 j
        simp only [hj, ↓reduceIte] at h1
        exact Or.inl ⟨h1, hq_ext s₂ j⟩
      · have hne0 : m₂.1 ≠ m0 := (Finset.mem_erase.mp m₂.2).1
        have hex : ∃ j : Fin 6, m₂.1 j = true := by
          by_contra hnot; push Not at hnot
          apply hne0; ext j
          exact Bool.eq_false_iff.mpr (hnot j)
        obtain ⟨j, hj⟩ := hex
        refine comp_ne_of_sep_wedge_univ (j := j) (hq_mem s₁) (hpm'_mem m₂.1) ?_
        have h2 := hpm' m₂.1 j
        simp only [hj, ↓reduceIte] at h2
        exact Or.inr ⟨hq_ext s₁ j, h2⟩
      · exact hq_inj s₁ s₂ fun h => hne (congrArg Sum.inr h)
    let fAll : idxType → Set (ℝ × ℝ) := fun x => connectedComponentIn U' (ptAll x)
    have hfAll_inj : Function.Injective fAll := fun a b hab => by
      by_contra hne; exact hptAll_inj a b hne hab
    have hfAll_sub : Set.range fAll ⊆ Comps U' := by
      rintro _ ⟨x, rfl⟩; exact ⟨ptAll x, hptAll_mem x, rfl⟩
    have hcard_nz : nonzeroMasks.card = 63 := by
      have h1 := Finset.card_erase_add_one (Finset.mem_univ m0)
      have h2 : (Finset.univ : Finset (Fin 6 → Bool)).card = 64 := by norm_num
      change nonzeroMasks.card + 1 = (Finset.univ : Finset (Fin 6 → Bool)).card at h1
      omega
    have hcard_idx : Fintype.card idxType = 63 + ls.length := by
      rw [Fintype.card_sum, Fintype.card_coe, hcard_nz, Fintype.card_fin]
    have h_lower : ((63 + ls.length : ℕ) : ℕ∞) ≤ (Comps U').encard := by
      calc ((63 + ls.length : ℕ) : ℕ∞)
          = (Fintype.card idxType : ℕ∞) := by rw [hcard_idx]
        _ = (Set.univ : Set idxType).encard := by
            rw [Set.encard_univ, ENat.card_eq_coe_fintype_card]
        _ = (fAll '' Set.univ).encard := (hfAll_inj.injOn.encard_image).symm
        _ = (Set.range fAll).encard := by rw [Set.image_univ]
        _ ≤ (Comps U').encard := Set.encard_le_encard hfAll_sub
    have hU'_bound : (Comps U').encard ≤ ((67 - badPairs.card : ℕ) : ℕ∞) := by
      have h_arr := arr_comps_bound_univ hGP' Finset.univ
      have hU_eq : U' = (Set.univ : Set (ℝ × ℝ)) \ ⋃ j ∈ (Finset.univ : Finset (Fin 6)), bdWedge (W' j) := by
        ext p; simp [U']
      rw [← hU_eq] at h_arr
      let ordPairs : Finset (Fin 6 × Fin 6) := Finset.univ.filter (fun p : Fin 6 × Fin 6 => p.1 < p.2)
      have hord_card : ordPairs.card = 15 := by decide
      have hbad_sub : badPairs' ⊆ ordPairs := fun p hp => by
        have hp' := (Finset.mem_filter.mp hp).2
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ p, hp'.1⟩
      have hsum_eq :
          (∑ i : Fin 6, ∑ j : Fin 6 with i < j, (bdWedge (W' i) ∩ bdWedge (W' j)).ncard) =
          ∑ p ∈ ordPairs, (bdWedge (W' p.1) ∩ bdWedge (W' p.2)).ncard := by
        have h1 : (∑ i : Fin 6, ∑ j : Fin 6 with i < j, (bdWedge (W' i) ∩ bdWedge (W' j)).ncard) =
            ∑ i : Fin 6, ∑ j : Fin 6,
              (if i < j then (bdWedge (W' i) ∩ bdWedge (W' j)).ncard else 0) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.sum_filter]
        rw [h1, ← Fintype.sum_prod_type']
        rw [Finset.sum_filter]
      have hsum_nat :
          (∑ p ∈ ordPairs, (bdWedge (W' p.1) ∩ bdWedge (W' p.2)).ncard) ≤ 60 - badPairs'.card := by
        have hsplit := Finset.sum_sdiff hbad_sub (f := fun p : Fin 6 × Fin 6 =>
          (bdWedge (W' p.1) ∩ bdWedge (W' p.2)).ncard)
        have hbad_le : (∑ p ∈ badPairs', (bdWedge (W' p.1) ∩ bdWedge (W' p.2)).ncard) ≤
            3 * badPairs'.card := by
          calc (∑ p ∈ badPairs', (bdWedge (W' p.1) ∩ bdWedge (W' p.2)).ncard)
              ≤ ∑ _p ∈ badPairs', 3 := Finset.sum_le_sum fun p hp => (Finset.mem_filter.mp hp).2.2
            _ = 3 * badPairs'.card := by simp [mul_comm]
        have hgood_le : (∑ p ∈ ordPairs \ badPairs', (bdWedge (W' p.1) ∩ bdWedge (W' p.2)).ncard) ≤
            4 * (ordPairs \ badPairs').card := by
          calc (∑ p ∈ ordPairs \ badPairs', (bdWedge (W' p.1) ∩ bdWedge (W' p.2)).ncard)
              ≤ ∑ _p ∈ ordPairs \ badPairs', 4 := Finset.sum_le_sum fun p hp => by
                have hlt : p.1 < p.2 := (Finset.mem_filter.mp (Finset.mem_sdiff.mp hp).1).2
                exact (inter_card_le_four hGP' (ne_of_lt hlt)).2
            _ = 4 * (ordPairs \ badPairs').card := by simp [mul_comm]
        have hdisj_bad' : Disjoint (ordPairs \ badPairs') badPairs' :=
          Finset.disjoint_left.mpr fun _ h1 h2 => (Finset.mem_sdiff.mp h1).2 h2
        have hcard_sdiff : (ordPairs \ badPairs').card + badPairs'.card = 15 := by
          rw [← Finset.card_union_of_disjoint hdisj_bad',
            Finset.sdiff_union_of_subset hbad_sub, hord_card]
        omega
      have h1 : (1 + ((Finset.univ : Finset (Fin 6)).card : ℕ∞) +
          ∑ i ∈ (Finset.univ : Finset (Fin 6)),
            ∑ j ∈ (Finset.univ : Finset (Fin 6)) with i < j,
              ((bdWedge (W' i) ∩ bdWedge (W' j)).ncard : ℕ∞)) =
          ((7 + ∑ p ∈ ordPairs, (bdWedge (W' p.1) ∩ bdWedge (W' p.2)).ncard : ℕ) : ℕ∞) := by
        rw [← hsum_eq]
        simp only [Finset.card_univ, Fintype.card_fin]
        push_cast
        ring
      rw [h1] at h_arr
      rw [hbad_eq] at hsum_nat
      have hbad15 : badPairs.card ≤ 15 := by
        calc badPairs.card = badPairs'.card := by rw [hbad_eq]
          _ ≤ ordPairs.card := Finset.card_le_card hbad_sub
          _ = 15 := hord_card
      exact h_arr.trans (Nat.cast_le.mpr (by omega))
    have hnat : 63 + ls.length ≤ 67 - badPairs.card := Nat.cast_le.mp (h_lower.trans hU'_bound)
    omega

end SixWedges

theorem six_wedges_not_all_64_masks (W : Fin 6 → OpenWedge) :
    ¬ (∀ m : Fin 6 → Bool, ∃ p : ℝ × ℝ,
        (∀ i : Fin 6, if m i then (W i).MemOpen p else (W i).MemExt p)) := by
  intro h_all
  obtain ⟨W', hGP', h_all'⟩ := SixWedges.exists_gp6_perturbation W h_all
  exact SixWedges.six_wedges_gp_contradiction W' hGP' h_all'

end
