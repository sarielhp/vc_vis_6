import Mathlib
import RootTask.Defs
import RootTask.CaseBSolution

open scoped Classical BigOperators
open Finset

noncomputable section

/-!
# Unconditional Planar Bridge Theorems

This module bridges:
1. `thm1_part2_upper_halfplane` to arbitrary `OpenHalfPlane`s (`thm1_part2_general_halfplane`),
2. `thm1_part2_general_halfplane` to convex hull containment (`thm1_part2_convexHull_containment`),
3. Case A origin reduction (`push_into_open_q1`, `caseA_reduces_to_origin`) and Case B (`five_wedges_L_domain_caseB`)
   into the normalized L-domain theorem (`five_wedges_L_domain_normalized`),
4. General two-half-plane L-obstruction (`five_wedges_two_halfplanes_general`) for any `Ha Hb : OpenHalfPlane`.
-/

/-- An open affine half-plane `{p : ℝ × ℝ | 0 < n.1 * p.1 + n.2 * p.2 + c}`. -/
structure OpenHalfPlane where
  n : ℝ × ℝ
  c : ℝ
  hn : n.1 ≠ 0 ∨ n.2 ≠ 0

/-- Membership in the positive open side of `H`. -/
def OpenHalfPlane.MemPos (H : OpenHalfPlane) (p : ℝ × ℝ) : Prop :=
  0 < H.n.1 * p.1 + H.n.2 * p.2 + H.c

/-- Membership in the negative open side of `H`. -/
def OpenHalfPlane.MemNeg (H : OpenHalfPlane) (p : ℝ × ℝ) : Prop :=
  H.n.1 * p.1 + H.n.2 * p.2 + H.c < 0

/-- Theorem 9.1(2) for an arbitrary `OpenHalfPlane`: if five open wedges realize all 32
    strict bitmasks inside `H.MemPos`, then their common intersection lies in `H.MemPos`. -/
theorem thm1_part2_general_halfplane
    (h_thm1 : ∀ f : Fin 5 → VFunc, ¬ (∀ m : Fin 5 → Bool, ∃ q : ℝ × ℝ, RealizesVMask f m q))
    (W : Fin 5 → OpenWedge)
    (H : OpenHalfPlane)
    (h_all_in_H : ∀ m : Fin 5 → Bool, ∃ p : ℝ × ℝ, H.MemPos p ∧ RealizesWedgeMask W m p) :
    ∀ z : ℝ × ℝ, (∀ i : Fin 5, (W i).MemOpen z) → H.MemPos z := by
  intro z hz
  by_contra hz_not
  have hz_le : H.n.1 * z.1 + H.n.2 * z.2 + H.c ≤ 0 := not_lt.mp hz_not
  let s : ℝ := H.n.1 ^ 2 + H.n.2 ^ 2
  have hs_pos : 0 < s := by
    rcases H.hn with h1 | h2
    · exact add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero h1) (sq_nonneg _)
    · exact add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_ne_zero h2)
  let T : ℝ × ℝ → ℝ × ℝ := fun p =>
    (H.n.2 * p.1 - H.n.1 * p.2, H.n.1 * p.1 + H.n.2 * p.2 + H.c)
  let rot : ℝ × ℝ → ℝ × ℝ := fun u =>
    ((H.n.2 * u.1 - H.n.1 * u.2) / s, (H.n.1 * u.1 + H.n.2 * u.2) / s)
  let W' : Fin 5 → OpenWedge := fun i =>
    { y := T (W i).y
      u₁ := rot (W i).u₁
      u₂ := rot (W i).u₂
      h_nondeg := by
        have hnd := (W i).h_nondeg
        have hs_ne : s ≠ 0 := ne_of_gt hs_pos
        have hdet :
            (rot (W i).u₁).1 * (rot (W i).u₂).2 - (rot (W i).u₁).2 * (rot (W i).u₂).1 =
              ((W i).u₁.1 * (W i).u₂.2 - (W i).u₁.2 * (W i).u₂.1) / s := by
          have hs_ne' : H.n.1 ^ 2 + H.n.2 ^ 2 ≠ 0 := hs_ne
          dsimp [rot, s]
          have hnum : (H.n.2 * (W i).u₁.1 - H.n.1 * (W i).u₁.2) *
                (H.n.1 * (W i).u₂.1 + H.n.2 * (W i).u₂.2) -
              (H.n.1 * (W i).u₁.1 + H.n.2 * (W i).u₁.2) *
                (H.n.2 * (W i).u₂.1 - H.n.1 * (W i).u₂.2) =
              (H.n.1 ^ 2 + H.n.2 ^ 2) * ((W i).u₁.1 * (W i).u₂.2 - (W i).u₁.2 * (W i).u₂.1) := by ring
          rw [div_mul_div_comm, div_mul_div_comm, ← sub_div, hnum, mul_div_mul_left _ _ hs_ne']
        rw [hdet]
        exact div_pos hnd hs_pos }
  have hlin : ∀ (u y p : ℝ × ℝ),
      (rot u).1 * ((T p).1 - (T y).1) + (rot u).2 * ((T p).2 - (T y).2) =
        u.1 * (p.1 - y.1) + u.2 * (p.2 - y.2) := by
    intro u y p
    have hs_ne : H.n.1 ^ 2 + H.n.2 ^ 2 ≠ 0 := ne_of_gt hs_pos
    dsimp [rot, T, s]
    have hnum : (H.n.2 * u.1 - H.n.1 * u.2) * (H.n.2 * p.1 - H.n.1 * p.2 - (H.n.2 * y.1 - H.n.1 * y.2)) +
        (H.n.1 * u.1 + H.n.2 * u.2) * (H.n.1 * p.1 + H.n.2 * p.2 + H.c - (H.n.1 * y.1 + H.n.2 * y.2 + H.c)) =
        (H.n.1 ^ 2 + H.n.2 ^ 2) * (u.1 * (p.1 - y.1) + u.2 * (p.2 - y.2)) := by ring
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, hnum, mul_div_cancel_left₀ _ hs_ne]
  have hmem_open : ∀ (i : Fin 5) (p : ℝ × ℝ), (W' i).MemOpen (T p) ↔ (W i).MemOpen p := by
    intro i p
    dsimp [OpenWedge.MemOpen, W']
    rw [hlin (W i).u₁ (W i).y p, hlin (W i).u₂ (W i).y p]
  have hmem_ext : ∀ (i : Fin 5) (p : ℝ × ℝ), (W' i).MemExt (T p) ↔ (W i).MemExt p := by
    intro i p
    dsimp [OpenWedge.MemExt, W']
    rw [hlin (W i).u₁ (W i).y p, hlin (W i).u₂ (W i).y p]
  have h_upper : ∀ m : Fin 5 → Bool, ∃ p' : ℝ × ℝ, 0 < p'.2 ∧ RealizesWedgeMask W' m p' := by
    intro m
    obtain ⟨p, hpH, hpmask⟩ := h_all_in_H m
    refine ⟨T p, hpH, fun i => ?_⟩
    have hi := hpmask i
    by_cases hmi : m i <;> simp only [hmi, ↓reduceIte, Bool.false_eq_true] at hi ⊢
    · exact (hmem_open i p).mpr hi
    · exact (hmem_ext i p).mpr hi
  exact thm1_part2_upper_halfplane h_thm1 W' h_upper
    ⟨T z, hz_le, fun i => (hmem_open i z).mpr (hz i)⟩

/-- Theorem 9.1(2) convex hull containment: if `pm m` realizes mask `m` for every `m : Fin 5 → Bool`,
    then every point in the common intersection of the five open wedges lies in `convexHull ℝ (Set.range pm)`. -/
theorem thm1_part2_convexHull_containment
    (h_thm1 : ∀ f : Fin 5 → VFunc, ¬ (∀ m : Fin 5 → Bool, ∃ q : ℝ × ℝ, RealizesVMask f m q))
    (W : Fin 5 → OpenWedge)
    (pm : (Fin 5 → Bool) → ℝ × ℝ)
    (hpm : ∀ m : Fin 5 → Bool, RealizesWedgeMask W m (pm m)) :
    ∀ z : ℝ × ℝ, (∀ i : Fin 5, (W i).MemOpen z) → z ∈ convexHull ℝ (Set.range pm) := by
  intro z hz
  by_contra hz_not
  have hconv : Convex ℝ (convexHull ℝ (Set.range pm)) := convex_convexHull ℝ (Set.range pm)
  have hclosed : IsClosed (convexHull ℝ (Set.range pm)) :=
    ((Set.finite_range pm).isCompact_convexHull ℝ).isClosed
  obtain ⟨(f : StrongDual ℝ (ℝ × ℝ)), u, h_lt, hu_lt⟩ :=
    geometric_hahn_banach_point_closed hconv hclosed hz_not
  have hf_decomp : ∀ p : ℝ × ℝ, f p = f (1, 0) * p.1 + f (0, 1) * p.2 := by
    intro p
    have hp : p = p.1 • ((1, 0) : ℝ × ℝ) + p.2 • ((0, 1) : ℝ × ℝ) := by
      ext <;> simp [smul_eq_mul]
    conv_lhs => rw [hp]
    rw [f.map_add, f.map_smul, f.map_smul, smul_eq_mul, smul_eq_mul]
    ring
  have hf_ne : f (1, 0) ≠ 0 ∨ f (0, 1) ≠ 0 := by
    by_contra h0
    push Not at h0
    have hz0 : f z = 0 := by rw [hf_decomp z, h0.1, h0.2]; ring
    have hpm0 : f (pm (fun _ => false)) = 0 := by
      rw [hf_decomp (pm (fun _ => false)), h0.1, h0.2]; ring
    have hmem0 : pm (fun _ => false) ∈ convexHull ℝ (Set.range pm) :=
      subset_convexHull ℝ (Set.range pm) (Set.mem_range_self _)
    have hgt0 := hu_lt (pm (fun _ => false)) hmem0
    linarith
  let H : OpenHalfPlane :=
    { n := (f (1, 0), f (0, 1))
      c := -u
      hn := hf_ne }
  have h_all_H : ∀ m : Fin 5 → Bool, ∃ p : ℝ × ℝ, H.MemPos p ∧ RealizesWedgeMask W m p := by
    intro m
    refine ⟨pm m, ?_, hpm m⟩
    have hmem : pm m ∈ convexHull ℝ (Set.range pm) :=
      subset_convexHull ℝ (Set.range pm) (Set.mem_range_self m)
    have hgt := hu_lt (pm m) hmem
    dsimp [OpenHalfPlane.MemPos, H]
    rw [← hf_decomp (pm m)]
    linarith
  have hz_H := thm1_part2_general_halfplane h_thm1 W H h_all_H z hz
  dsimp [OpenHalfPlane.MemPos, H] at hz_H
  rw [← hf_decomp z] at hz_H
  linarith

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

/-- Normalized L-domain obstruction combining Case A (`h_caseA_orig`) and Case B (`five_wedges_L_domain_caseB`). -/
theorem five_wedges_L_domain_normalized
    (h_thm1 : ∀ f : Fin 5 → VFunc, ¬ (∀ m : Fin 5 → Bool, ∃ p : ℝ × ℝ, RealizesVMask f m p))
    (h_caseA_orig :
      (∀ f : Fin 5 → VFunc, ¬ (∀ m : Fin 5 → Bool, ∃ p : ℝ × ℝ, RealizesVMask f m p)) →
      ∀ W : Fin 5 → OpenWedge,
        (∀ i : Fin 5, (W i).y.1 < 0 ∧ (W i).y.2 < 0) →
        (∀ i : Fin 5, (W i).MemOpen (0, 0)) →
        ¬ (∀ m : Fin 5 → Bool, ∃ p : ℝ × ℝ, (p.1 < 0 ∨ p.2 < 0) ∧ RealizesWedgeMask W m p))
    (W : Fin 5 → OpenWedge)
    (h_apex : ∀ i : Fin 5, (W i).y.1 < 0 ∧ (W i).y.2 < 0)
    (h_pa : ∃ pa : ℝ × ℝ, 0 < pa.1 ∧ ∀ i : Fin 5, (W i).MemOpen pa)
    (h_pb : ∃ pb : ℝ × ℝ, 0 < pb.2 ∧ ∀ i : Fin 5, (W i).MemOpen pb) :
    ¬ (∀ m : Fin 5 → Bool, ∃ p : ℝ × ℝ, (p.1 < 0 ∨ p.2 < 0) ∧ RealizesWedgeMask W m p) := by
  by_cases hq : ∃ q : ℝ × ℝ, 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ ∀ i : Fin 5, (W i).MemOpen q
  · obtain ⟨q, hq1, hq2, hq_mem⟩ := hq
    obtain ⟨q', hq'1, hq'2, hq'_mem⟩ := push_into_open_q1 W q hq1 hq2 hq_mem
    exact caseA_reduces_to_origin (h_caseA_orig h_thm1) W h_apex q' hq'1 hq'2 hq'_mem
  · exact five_wedges_L_domain_caseB h_thm1 W h_apex h_pa h_pb hq

/-- Helper for `five_wedges_two_halfplanes_general` when `Ha` and `Hb` have non-parallel normals. -/
private theorem five_wedges_two_halfplanes_nonparallel
    (h_thm1 : ∀ f : Fin 5 → VFunc, ¬ (∀ m : Fin 5 → Bool, ∃ p : ℝ × ℝ, RealizesVMask f m p))
    (h_caseA_orig :
      (∀ f : Fin 5 → VFunc, ¬ (∀ m : Fin 5 → Bool, ∃ p : ℝ × ℝ, RealizesVMask f m p)) →
      ∀ W : Fin 5 → OpenWedge,
        (∀ i : Fin 5, (W i).y.1 < 0 ∧ (W i).y.2 < 0) →
        (∀ i : Fin 5, (W i).MemOpen (0, 0)) →
        ¬ (∀ m : Fin 5 → Bool, ∃ p : ℝ × ℝ, (p.1 < 0 ∨ p.2 < 0) ∧ RealizesWedgeMask W m p))
    (Ha Hb : OpenHalfPlane)
    (h_det : Ha.n.1 * Hb.n.2 - Ha.n.2 * Hb.n.1 ≠ 0)
    (W : Fin 5 → OpenWedge)
    (h_apices : ∀ i : Fin 5, Ha.MemPos (W i).y ∧ Hb.MemPos (W i).y)
    (h_za : ∃ za : ℝ × ℝ, Ha.MemNeg za ∧ ∀ i : Fin 5, (W i).MemOpen za)
    (h_zb : ∃ zb : ℝ × ℝ, Hb.MemNeg zb ∧ ∀ i : Fin 5, (W i).MemOpen zb) :
    ¬ (∀ m : Fin 5 → Bool, ∃ p : ℝ × ℝ, (Ha.MemPos p ∨ Hb.MemPos p) ∧ RealizesWedgeMask W m p) := by
  intro hall
  let detA : ℝ := Ha.n.1 * Hb.n.2 - Ha.n.2 * Hb.n.1
  let A : ℝ × ℝ → ℝ × ℝ := fun p =>
    (-(Ha.n.1 * p.1 + Ha.n.2 * p.2 + Ha.c), -(Hb.n.1 * p.1 + Hb.n.2 * p.2 + Hb.c))
  let dual : ℝ × ℝ → ℝ × ℝ := fun u =>
    ((-Hb.n.2 * u.1 + Hb.n.1 * u.2) / detA, (Ha.n.2 * u.1 - Ha.n.1 * u.2) / detA)
  have hlin : ∀ (u y p : ℝ × ℝ),
      (dual u).1 * ((A p).1 - (A y).1) + (dual u).2 * ((A p).2 - (A y).2) =
        u.1 * (p.1 - y.1) + u.2 * (p.2 - y.2) := by
    intro u y p
    dsimp [dual, A]
    have hnum : (-Hb.n.2 * u.1 + Hb.n.1 * u.2) *
          (-(Ha.n.1 * p.1 + Ha.n.2 * p.2 + Ha.c) - -(Ha.n.1 * y.1 + Ha.n.2 * y.2 + Ha.c)) +
        (Ha.n.2 * u.1 - Ha.n.1 * u.2) *
          (-(Hb.n.1 * p.1 + Hb.n.2 * p.2 + Hb.c) - -(Hb.n.1 * y.1 + Hb.n.2 * y.2 + Hb.c)) =
        detA * (u.1 * (p.1 - y.1) + u.2 * (p.2 - y.2)) := by
      dsimp [detA]; ring
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, hnum, mul_div_cancel_left₀ _ h_det]
  have hdet_dual : ∀ u₁ u₂ : ℝ × ℝ,
      (dual u₁).1 * (dual u₂).2 - (dual u₁).2 * (dual u₂).1 =
        (u₁.1 * u₂.2 - u₁.2 * u₂.1) / detA := by
    intro u₁ u₂
    dsimp [dual]
    have hnum : (-Hb.n.2 * u₁.1 + Hb.n.1 * u₁.2) * (Ha.n.2 * u₂.1 - Ha.n.1 * u₂.2) -
        (Ha.n.2 * u₁.1 - Ha.n.1 * u₁.2) * (-Hb.n.2 * u₂.1 + Hb.n.1 * u₂.2) =
        detA * (u₁.1 * u₂.2 - u₁.2 * u₂.1) := by
      dsimp [detA]; ring
    rw [div_mul_div_comm, div_mul_div_comm, ← sub_div, hnum, mul_div_mul_left _ _ h_det]
  let W' : Fin 5 → OpenWedge := fun i =>
    if hpos : 0 < detA then
      { y := A (W i).y
        u₁ := dual (W i).u₁
        u₂ := dual (W i).u₂
        h_nondeg := by
          rw [hdet_dual]
          exact div_pos (W i).h_nondeg hpos }
    else
      { y := A (W i).y
        u₁ := dual (W i).u₂
        u₂ := dual (W i).u₁
        h_nondeg := by
          have hneg : detA < 0 := lt_of_le_of_ne (not_lt.mp hpos) h_det
          rw [hdet_dual]
          have hnum : (W i).u₂.1 * (W i).u₁.2 - (W i).u₂.2 * (W i).u₁.1 < 0 := by
            have := (W i).h_nondeg; linarith
          exact div_pos_of_neg_of_neg hnum hneg }
  have hmem_open : ∀ (i : Fin 5) (p : ℝ × ℝ), (W' i).MemOpen (A p) ↔ (W i).MemOpen p := by
    intro i p
    dsimp [W', OpenWedge.MemOpen]
    split_ifs
    · dsimp [OpenWedge.MemOpen]
      rw [hlin (W i).u₁ (W i).y p, hlin (W i).u₂ (W i).y p]
    · dsimp [OpenWedge.MemOpen]
      rw [hlin (W i).u₂ (W i).y p, hlin (W i).u₁ (W i).y p, and_comm]
  have hmem_ext : ∀ (i : Fin 5) (p : ℝ × ℝ), (W' i).MemExt (A p) ↔ (W i).MemExt p := by
    intro i p
    dsimp [W', OpenWedge.MemExt]
    split_ifs
    · dsimp [OpenWedge.MemExt]
      rw [hlin (W i).u₁ (W i).y p, hlin (W i).u₂ (W i).y p]
    · dsimp [OpenWedge.MemExt]
      rw [hlin (W i).u₂ (W i).y p, hlin (W i).u₁ (W i).y p, or_comm]
  have h_apex' : ∀ i : Fin 5, (W' i).y.1 < 0 ∧ (W' i).y.2 < 0 := by
    intro i
    have hy : (W' i).y = A (W i).y := by
      dsimp [W']; split_ifs <;> rfl
    rw [hy]
    obtain ⟨ha, hb⟩ := h_apices i
    dsimp [OpenHalfPlane.MemPos] at ha hb
    dsimp [A]
    exact ⟨by linarith, by linarith⟩
  obtain ⟨za, hza_neg, hza_open⟩ := h_za
  obtain ⟨zb, hzb_neg, hzb_open⟩ := h_zb
  have h_pa' : ∃ pa : ℝ × ℝ, 0 < pa.1 ∧ ∀ i : Fin 5, (W' i).MemOpen pa := by
    refine ⟨A za, ?_, fun i => (hmem_open i za).mpr (hza_open i)⟩
    dsimp [OpenHalfPlane.MemNeg] at hza_neg
    dsimp [A]; linarith
  have h_pb' : ∃ pb : ℝ × ℝ, 0 < pb.2 ∧ ∀ i : Fin 5, (W' i).MemOpen pb := by
    refine ⟨A zb, ?_, fun i => (hmem_open i zb).mpr (hzb_open i)⟩
    dsimp [OpenHalfPlane.MemNeg] at hzb_neg
    dsimp [A]; linarith
  apply five_wedges_L_domain_normalized h_thm1 h_caseA_orig W' h_apex' h_pa' h_pb'
  intro m
  obtain ⟨p, hp_or, hp_mask⟩ := hall m
  refine ⟨A p, ?_, fun i => ?_⟩
  · rcases hp_or with hpa | hpb
    · left; dsimp [OpenHalfPlane.MemPos] at hpa; dsimp [A]; linarith
    · right; dsimp [OpenHalfPlane.MemPos] at hpb; dsimp [A]; linarith
  · have hi := hp_mask i
    by_cases hmi : m i <;> simp only [hmi, ↓reduceIte, Bool.false_eq_true] at hi ⊢
    · exact (hmem_open i p).mpr hi
    · exact (hmem_ext i p).mpr hi

/-- Lemma 10.2 & Theorem 10.1 (`L-two-halfplanes`): for any two open half-planes `Ha, Hb` and five open
    wedges `W` whose apices lie in `Ha⁺ ∩ Hb⁺`, if `R_{11111}` meets both `Ha⁻` and `Hb⁻`, then
    the 5 wedges cannot realize all 32 strict bitmasks inside `Ha⁺ ∪ Hb⁺`. -/
theorem five_wedges_two_halfplanes_general
    (h_thm1 : ∀ f : Fin 5 → VFunc, ¬ (∀ m : Fin 5 → Bool, ∃ p : ℝ × ℝ, RealizesVMask f m p))
    (h_caseA_orig :
      (∀ f : Fin 5 → VFunc, ¬ (∀ m : Fin 5 → Bool, ∃ p : ℝ × ℝ, RealizesVMask f m p)) →
      ∀ W : Fin 5 → OpenWedge,
        (∀ i : Fin 5, (W i).y.1 < 0 ∧ (W i).y.2 < 0) →
        (∀ i : Fin 5, (W i).MemOpen (0, 0)) →
        ¬ (∀ m : Fin 5 → Bool, ∃ p : ℝ × ℝ, (p.1 < 0 ∨ p.2 < 0) ∧ RealizesWedgeMask W m p))
    (Ha Hb : OpenHalfPlane)
    (W : Fin 5 → OpenWedge)
    (h_apices : ∀ i : Fin 5, Ha.MemPos (W i).y ∧ Hb.MemPos (W i).y)
    (h_za : ∃ za : ℝ × ℝ, Ha.MemNeg za ∧ ∀ i : Fin 5, (W i).MemOpen za)
    (h_zb : ∃ zb : ℝ × ℝ, Hb.MemNeg zb ∧ ∀ i : Fin 5, (W i).MemOpen zb) :
    ¬ (∀ m : Fin 5 → Bool, ∃ p : ℝ × ℝ, (Ha.MemPos p ∨ Hb.MemPos p) ∧ RealizesWedgeMask W m p) := by
  by_cases h_det : Ha.n.1 * Hb.n.2 - Ha.n.2 * Hb.n.1 ≠ 0
  · exact five_wedges_two_halfplanes_nonparallel h_thm1 h_caseA_orig Ha Hb h_det W h_apices h_za h_zb
  · push Not at h_det
    intro hall
    choose pm hpm_or hpm_mask using hall
    obtain ⟨za, hza_neg, hza_open⟩ := h_za
    let valA : ℝ × ℝ → ℝ := fun p => Ha.n.1 * p.1 + Ha.n.2 * p.2 + Ha.c
    let errA : ℝ × ℝ → ℝ := fun p => -Ha.n.2 * p.1 + Ha.n.1 * p.2
    let Merr : ℝ :=
      1 + |errA za| + (∑ i : Fin 5, |errA (W i).y|) + (∑ m : Fin 5 → Bool, |errA (pm m)|)
    let δza : ℝ := -valA za
    have hδza : 0 < δza := by dsimp [δza, valA]; exact neg_pos.mpr hza_neg
    let invEps : ℝ :=
      1 + Merr * (1 / δza + (∑ i : Fin 5, 1 / valA (W i).y) +
        (∑ m : Fin 5 → Bool, if Ha.MemPos (pm m) then 1 / valA (pm m) else 0))
    have hMerr_pos : 0 < Merr := by
      have h1 : 0 ≤ |errA za| := abs_nonneg _
      have h2 : 0 ≤ ∑ i : Fin 5, |errA (W i).y| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
      have h3 : 0 ≤ ∑ m : Fin 5 → Bool, |errA (pm m)| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
      dsimp [Merr]; linarith
    have hsum_nonneg : 0 ≤ 1 / δza + (∑ i : Fin 5, 1 / valA (W i).y) +
        (∑ m : Fin 5 → Bool, if Ha.MemPos (pm m) then 1 / valA (pm m) else 0) := by
      have h1 : 0 ≤ 1 / δza := div_nonneg zero_le_one (le_of_lt hδza)
      have h2 : 0 ≤ ∑ i : Fin 5, 1 / valA (W i).y := Finset.sum_nonneg fun i _ =>
        div_nonneg zero_le_one (le_of_lt (h_apices i).1)
      have h3 : 0 ≤ ∑ m : Fin 5 → Bool, (if Ha.MemPos (pm m) then 1 / valA (pm m) else 0) := by
        apply Finset.sum_nonneg; intro m _
        split_ifs with hm
        · exact div_nonneg zero_le_one (le_of_lt hm)
        · exact le_rfl
      linarith
    have hinvEps_pos : 0 < invEps := by
      dsimp [invEps]
      nlinarith
    let ε : ℝ := 1 / invEps
    have hε_pos : 0 < ε := div_pos zero_lt_one hinvEps_pos
    have hmargin_lt : ∀ {δ err : ℝ}, 0 < δ → 1 / δ ≤ 1 / δza + (∑ i : Fin 5, 1 / valA (W i).y) +
        (∑ m : Fin 5 → Bool, if Ha.MemPos (pm m) then 1 / valA (pm m) else 0) →
        |err| ≤ Merr → ε * |err| < δ := by
      intro δ err hδ hle_sum hle_err
      have h1 : Merr * (1 / δ) < invEps := by
        dsimp [invEps]
        have := mul_le_mul_of_nonneg_left hle_sum (le_of_lt hMerr_pos)
        linarith
      have h2 : |err| / δ < invEps := by
        have h1' : |err| * (1 / δ) ≤ Merr * (1 / δ) :=
          mul_le_mul_of_nonneg_right hle_err (div_nonneg zero_le_one (le_of_lt hδ))
        have heq : |err| / δ = |err| * (1 / δ) := div_eq_mul_one_div _ _
        linarith
      have h3 : |err| / invEps < δ := (div_lt_comm₀ hδ hinvEps_pos).mp h2
      have h4 : ε * |err| = |err| / invEps := by dsimp [ε]; ring
      linarith
    let Ha' : OpenHalfPlane :=
      { n := (Ha.n.1 - ε * Ha.n.2, Ha.n.2 + ε * Ha.n.1)
        c := Ha.c
        hn := by
          have ha_sq : 0 < Ha.n.1 ^ 2 + Ha.n.2 ^ 2 := by
            rcases Ha.hn with h1 | h2
            · exact add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero h1) (sq_nonneg _)
            · exact add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_ne_zero h2)
          have hnorm : (Ha.n.1 - ε * Ha.n.2) ^ 2 + (Ha.n.2 + ε * Ha.n.1) ^ 2 =
              (1 + ε ^ 2) * (Ha.n.1 ^ 2 + Ha.n.2 ^ 2) := by ring
          have hpos_sq : 0 < (Ha.n.1 - ε * Ha.n.2) ^ 2 + (Ha.n.2 + ε * Ha.n.1) ^ 2 := by
            rw [hnorm]
            exact mul_pos (by positivity) ha_sq
          by_contra h0
          push Not at h0
          dsimp only at h0
          rw [h0.1, h0.2] at hpos_sq
          norm_num at hpos_sq }
    have hHa'_eq : ∀ p : ℝ × ℝ, Ha'.n.1 * p.1 + Ha'.n.2 * p.2 + Ha'.c = valA p + ε * errA p := by
      intro p; dsimp [Ha', valA, errA]; ring
    have h_det' : Ha'.n.1 * Hb.n.2 - Ha'.n.2 * Hb.n.1 ≠ 0 := by
      have hid : Ha'.n.1 * Hb.n.2 - Ha'.n.2 * Hb.n.1 =
          (Ha.n.1 * Hb.n.2 - Ha.n.2 * Hb.n.1) - ε * (Ha.n.1 * Hb.n.1 + Ha.n.2 * Hb.n.2) := by
        dsimp [Ha']; ring
      rw [hid, h_det, zero_sub]
      have hdot_sq : (Ha.n.1 * Hb.n.1 + Ha.n.2 * Hb.n.2) ^ 2 +
          (Ha.n.1 * Hb.n.2 - Ha.n.2 * Hb.n.1) ^ 2 =
          (Ha.n.1 ^ 2 + Ha.n.2 ^ 2) * (Hb.n.1 ^ 2 + Hb.n.2 ^ 2) := by ring
      have ha_sq : 0 < Ha.n.1 ^ 2 + Ha.n.2 ^ 2 := by
        rcases Ha.hn with h1 | h2
        · exact add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero h1) (sq_nonneg _)
        · exact add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_ne_zero h2)
      have hb_sq : 0 < Hb.n.1 ^ 2 + Hb.n.2 ^ 2 := by
        rcases Hb.hn with h1 | h2
        · exact add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero h1) (sq_nonneg _)
        · exact add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_ne_zero h2)
      rw [h_det] at hdot_sq
      have hdot_ne : Ha.n.1 * Hb.n.1 + Ha.n.2 * Hb.n.2 ≠ 0 := by
        intro h0
        rw [h0] at hdot_sq
        have hmul_pos := mul_pos ha_sq hb_sq
        linarith
      exact neg_ne_zero.mpr (mul_ne_zero (ne_of_gt hε_pos) hdot_ne)
    have h_apices' : ∀ i : Fin 5, Ha'.MemPos (W i).y ∧ Hb.MemPos (W i).y := by
      intro i
      refine ⟨?_, (h_apices i).2⟩
      dsimp [OpenHalfPlane.MemPos]
      rw [hHa'_eq]
      have h1 : 1 / valA (W i).y ≤ ∑ j : Fin 5, 1 / valA (W j).y :=
        Finset.single_le_sum (f := fun j : Fin 5 => 1 / valA (W j).y)
          (fun j _ => div_nonneg zero_le_one (le_of_lt (h_apices j).1)) (Finset.mem_univ i)
      have h2 : 0 ≤ ∑ m : Fin 5 → Bool, (if Ha.MemPos (pm m) then 1 / valA (pm m) else 0) := by
        apply Finset.sum_nonneg; intro m _
        split_ifs with hm
        · exact div_nonneg zero_le_one (le_of_lt hm)
        · exact le_rfl
      have hsum_i : 1 / valA (W i).y ≤ 1 / δza + (∑ j : Fin 5, 1 / valA (W j).y) +
          (∑ m : Fin 5 → Bool, if Ha.MemPos (pm m) then 1 / valA (pm m) else 0) := by
        have := div_nonneg zero_le_one (le_of_lt hδza)
        linarith
      have herr_i : |errA (W i).y| ≤ Merr := by
        have hs1 : |errA (W i).y| ≤ ∑ j : Fin 5, |errA (W j).y| :=
          Finset.single_le_sum (f := fun j : Fin 5 => |errA (W j).y|)
            (fun _ _ => abs_nonneg _) (Finset.mem_univ i)
        have hnn1 : 0 ≤ |errA za| := abs_nonneg _
        have hnn2 : 0 ≤ ∑ m : Fin 5 → Bool, |errA (pm m)| :=
          Finset.sum_nonneg (fun _ _ => abs_nonneg _)
        dsimp [Merr]; linarith
      have hlt := hmargin_lt (h_apices i).1 hsum_i herr_i
      have hneg := neg_le_abs (errA (W i).y)
      nlinarith
    have h_za' : ∃ za' : ℝ × ℝ, Ha'.MemNeg za' ∧ ∀ i : Fin 5, (W i).MemOpen za' := by
      refine ⟨za, ?_, hza_open⟩
      dsimp [OpenHalfPlane.MemNeg]
      rw [hHa'_eq]
      have hsum_za : 1 / δza ≤ 1 / δza + (∑ j : Fin 5, 1 / valA (W j).y) +
          (∑ m : Fin 5 → Bool, if Ha.MemPos (pm m) then 1 / valA (pm m) else 0) := by
        have h1 : 0 ≤ ∑ j : Fin 5, 1 / valA (W j).y := Finset.sum_nonneg fun j _ =>
          div_nonneg zero_le_one (le_of_lt (h_apices j).1)
        have h2 : 0 ≤ ∑ m : Fin 5 → Bool, (if Ha.MemPos (pm m) then 1 / valA (pm m) else 0) := by
          apply Finset.sum_nonneg; intro m _
          split_ifs with hm
          · exact div_nonneg zero_le_one (le_of_lt hm)
          · exact le_rfl
        linarith
      have herr_za : |errA za| ≤ Merr := by
        have hnn1 : 0 ≤ ∑ j : Fin 5, |errA (W j).y| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
        have hnn2 : 0 ≤ ∑ m : Fin 5 → Bool, |errA (pm m)| :=
          Finset.sum_nonneg (fun _ _ => abs_nonneg _)
        dsimp [Merr]; linarith
      have hlt := hmargin_lt hδza hsum_za herr_za
      have hpos := le_abs_self (errA za)
      dsimp [δza] at hlt
      nlinarith
    apply five_wedges_two_halfplanes_nonparallel h_thm1 h_caseA_orig Ha' Hb h_det' W h_apices' h_za' h_zb
    intro m
    refine ⟨pm m, ?_, hpm_mask m⟩
    rcases hpm_or m with hpa | hpb
    · left
      dsimp [OpenHalfPlane.MemPos]
      rw [hHa'_eq]
      have h1 : 1 / valA (pm m) ≤ ∑ m' : Fin 5 → Bool,
          (if Ha.MemPos (pm m') then 1 / valA (pm m') else 0) := by
        have hm_term : (if Ha.MemPos (pm m) then 1 / valA (pm m) else 0) = 1 / valA (pm m) :=
          if_pos hpa
        rw [← hm_term]
        apply Finset.single_le_sum (f := fun m' : Fin 5 → Bool =>
          if Ha.MemPos (pm m') then 1 / valA (pm m') else 0)
        · intro m' _
          split_ifs with hm'
          · exact div_nonneg zero_le_one (le_of_lt hm')
          · exact le_rfl
        · exact Finset.mem_univ m
      have hsum_m : 1 / valA (pm m) ≤ 1 / δza + (∑ j : Fin 5, 1 / valA (W j).y) +
          (∑ m' : Fin 5 → Bool, if Ha.MemPos (pm m') then 1 / valA (pm m') else 0) := by
        have hza_nn : 0 ≤ 1 / δza := div_nonneg zero_le_one (le_of_lt hδza)
        have hW_nn : 0 ≤ ∑ j : Fin 5, 1 / valA (W j).y := Finset.sum_nonneg fun j _ =>
          div_nonneg zero_le_one (le_of_lt (h_apices j).1)
        linarith
      have herr_m : |errA (pm m)| ≤ Merr := by
        have hs1 : |errA (pm m)| ≤ ∑ m' : Fin 5 → Bool, |errA (pm m')| :=
          Finset.single_le_sum (f := fun m' : Fin 5 → Bool => |errA (pm m')|)
            (fun _ _ => abs_nonneg _) (Finset.mem_univ m)
        have hnn1 : 0 ≤ |errA za| := abs_nonneg _
        have hnn2 : 0 ≤ ∑ j : Fin 5, |errA (W j).y| :=
          Finset.sum_nonneg (fun _ _ => abs_nonneg _)
        dsimp [Merr]; linarith
      have hlt := hmargin_lt hpa hsum_m herr_m
      have hneg := neg_le_abs (errA (pm m))
      nlinarith
    · exact Or.inr hpb

end
