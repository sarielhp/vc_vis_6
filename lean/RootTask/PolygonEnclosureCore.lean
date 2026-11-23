import Mathlib
import RootTask.PolygonDefs

open scoped Classical BigOperators
open Finset

noncomputable section

namespace PolygonCore

/-!
# Planar Visibility, Enclosure (`Lemma 2.1`), Wedge Extraction, and Certified Hull Vertices

Concrete `ℝ × ℝ` formalization of Sections 2–4 of `upper_9.tex` over `Sees P x y := segment ℝ x y ⊆ P`,
`EnclosureDomain P`, and `ShatteredSimplePolygon P S w`:
- Section 2.2: `EnclosureDomain` & segment/path enclosure helpers;
- Section 2.3: `IsTest` & Lemma 2.5 (`counting`) for `IsTest`, `IsWedgeTest`, and `IsHalfPlaneTest` on `W(F; N)`;
- Section 2.4: Equation (1) (`u_halfplanes`), Lemma 2.6 (`cone`), Lemma 2.7 (`wedge_extraction`), Corollary 2.8 (`fan`);
- Section 3: Lemma 3.2 (`hidden_targets`), Lemma 3.3 (`hidden_front_vertex`), Lemma 3.4 (`front_restoration`);
- Section 4: Lemma 4.1 (`side_corners`), Lemma 4.2 (`separation`), Proposition 4.3 (`certified_structure`),
  Corollary 4.4 (`side_preservation`), Lemma 4.5 (`exit_edge`), Corollary 4.6 (`endpoint_back_vertex_criterion`).
-/

/-! ## Section 2.2: `EnclosureDomain`, Visibility Segments, and Polygonal Paths -/

/-- Simple-polygon enclosure axioms (`Lemma 2.1(i)–(ii)` of `upper_9.tex`) over `P : Set (ℝ × ℝ)`
    with concrete segment visibility `Sees P x y := segment ℝ x y ⊆ P`. -/
structure EnclosureDomain (P : Set (ℝ × ℝ)) : Prop where
  triangle_enclosure : ∀ x ∈ P, ∀ y ∈ P, ∀ z ∈ P,
    Sees P x y → Sees P y z → Sees P x z →
    convexHull ℝ ({x, y, z} : Set (ℝ × ℝ)) ⊆ P
  two_path_enclosure : ∀ (s t : ℝ × ℝ) (π₁ π₂ : List (ℝ × ℝ)),
    s ≠ t → IsPolygonalPathIn P s t π₁ → IsPolygonalPathIn P s t π₂ →
    InteriorOnLeft s t π₁ → InteriorOnRight s t π₂ → Sees P s t

/-- Extracting `EnclosureDomain P` from `ShatteredSimplePolygon P S w`. -/
lemma _root_.ShatteredSimplePolygon.toEnclosureDomain {n : ℕ} {P : Set (ℝ × ℝ)}
    {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ}
    (hP : ShatteredSimplePolygon P S w) : EnclosureDomain P where
  triangle_enclosure := hP.triangle_enclosure
  two_path_enclosure := hP.two_path_enclosure

lemma sees_mem_left {P : Set (ℝ × ℝ)} {x y : ℝ × ℝ} (h : Sees P x y) : x ∈ P :=
  h (left_mem_segment ℝ x y)

lemma sees_mem_right {P : Set (ℝ × ℝ)} {x y : ℝ × ℝ} (h : Sees P x y) : y ∈ P :=
  h (right_mem_segment ℝ x y)

lemma sees_of_mem_segment_left {P : Set (ℝ × ℝ)} {x y z : ℝ × ℝ}
    (h : Sees P x y) (hz : z ∈ segment ℝ x y) : Sees P x z :=
  ((convex_segment x y).segment_subset (left_mem_segment ℝ x y) hz).trans h

lemma sees_of_mem_segment_right {P : Set (ℝ × ℝ)} {x y z : ℝ × ℝ}
    (h : Sees P x y) (hz : z ∈ segment ℝ x y) : Sees P z y :=
  ((convex_segment x y).segment_subset hz (right_mem_segment ℝ x y)).trans h

lemma sees_of_subsegment_ends {P : Set (ℝ × ℝ)} {x y u v : ℝ × ℝ}
    (h : Sees P x y) (hu : u ∈ segment ℝ x y) (hv : v ∈ segment ℝ x y) : Sees P u v :=
  ((convex_segment x y).segment_subset hu hv).trans h

lemma sees_trans_collinear {P : Set (ℝ × ℝ)} {x y z : ℝ × ℝ}
    (hxy : Sees P x y) (hyz : Sees P y z) (hy : y ∈ segment ℝ x z) : Sees P x z := by
  intro p hp
  rw [segment_eq_image] at hy hp
  rcases hy with ⟨s, hs, rfl⟩
  rcases hp with ⟨t, ht, rfl⟩
  rcases le_total t s with hts | hst
  · by_cases hs0 : s = 0
    · have ht0 : t = 0 := le_antisymm (hts.trans (le_of_eq hs0)) ht.1
      subst ht0
      simpa using sees_mem_left hxy
    · have hs_pos : 0 < s := lt_of_le_of_ne hs.1 (Ne.symm hs0)
      apply hxy
      rw [segment_eq_image]
      refine ⟨t / s, ⟨div_nonneg ht.1 (le_of_lt hs_pos), (div_le_one hs_pos).mpr hts⟩, ?_⟩
      ext <;> simp [smul_eq_mul] <;> field_simp [ne_of_gt hs_pos] <;> ring
  · by_cases hs1 : s = 1
    · have ht1 : t = 1 := le_antisymm ht.2 (hs1 ▸ hst)
      subst ht1
      simpa using sees_mem_right hyz
    · have hs_lt : 0 < 1 - s := sub_pos.mpr (lt_of_le_of_ne hs.2 hs1)
      apply hyz
      rw [segment_eq_image]
      refine ⟨(t - s) / (1 - s), ⟨div_nonneg (sub_nonneg.mpr hst) (le_of_lt hs_lt),
        (div_le_one hs_lt).mpr (by linarith [ht.2])⟩, ?_⟩
      ext <;> simp [smul_eq_mul] <;> field_simp [ne_of_gt hs_lt] <;> ring

lemma two_path_enclosure_either {P : Set (ℝ × ℝ)} (hEnc : EnclosureDomain P)
    {s t : ℝ × ℝ} {π₁ π₂ : List (ℝ × ℝ)} (hst : s ≠ t)
    (hp₁ : IsPolygonalPathIn P s t π₁) (hp₂ : IsPolygonalPathIn P s t π₂)
    (hsides : (InteriorOnLeft s t π₁ ∧ InteriorOnRight s t π₂) ∨
              (InteriorOnRight s t π₁ ∧ InteriorOnLeft s t π₂)) :
    Sees P s t := by
  rcases hsides with ⟨hL, hR⟩ | ⟨hR, hL⟩
  · exact hEnc.two_path_enclosure s t π₁ π₂ hst hp₁ hp₂ hL hR
  · exact hEnc.two_path_enclosure s t π₂ π₁ hst hp₂ hp₁ hL hR

lemma isPolygonalPathIn_three {P : Set (ℝ × ℝ)} {s a t : ℝ × ℝ}
    (h1 : Sees P s a) (h2 : Sees P a t) :
    IsPolygonalPathIn P s t [s, a, t] := by
  refine ⟨by simp, rfl, rfl, ?_, ?_⟩
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · exact sees_mem_left h1
    · exact sees_mem_right h1
    · exact sees_mem_right h2
  · exact List.isChain_cons_cons.mpr ⟨h1, List.isChain_cons_cons.mpr ⟨h2, List.isChain_singleton _⟩⟩

lemma isPolygonalPathIn_four {P : Set (ℝ × ℝ)} {s a b t : ℝ × ℝ}
    (h1 : Sees P s a) (h2 : Sees P a b) (h3 : Sees P b t) :
    IsPolygonalPathIn P s t [s, a, b, t] := by
  refine ⟨by simp, rfl, rfl, ?_, ?_⟩
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact sees_mem_left h1
    · exact sees_mem_right h1
    · exact sees_mem_right h2
    · exact sees_mem_right h3
  · exact List.isChain_cons_cons.mpr
      ⟨h1, List.isChain_cons_cons.mpr ⟨h2, List.isChain_cons_cons.mpr ⟨h3, List.isChain_singleton _⟩⟩⟩

lemma interiorOnLeft_three {s a t : ℝ × ℝ} (ha : 0 < orient2D s t a) :
    InteriorOnLeft s t [s, a, t] := by
  refine ⟨by simp, fun k hk hk0 hk1 => ?_⟩
  simp only [List.length_cons, List.length_nil] at hk hk1
  have hk_eq : k = 1 := by omega
  subst hk_eq
  simpa using ha

lemma interiorOnRight_three {s a t : ℝ × ℝ} (ha : orient2D s t a < 0) :
    InteriorOnRight s t [s, a, t] := by
  refine ⟨by simp, fun k hk hk0 hk1 => ?_⟩
  simp only [List.length_cons, List.length_nil] at hk hk1
  have hk_eq : k = 1 := by omega
  subst hk_eq
  simpa using ha

lemma interiorOnLeft_four {s a b t : ℝ × ℝ} (ha : 0 < orient2D s t a) (hb : 0 < orient2D s t b) :
    InteriorOnLeft s t [s, a, b, t] := by
  refine ⟨by simp, fun k hk hk0 hk1 => ?_⟩
  simp only [List.length_cons, List.length_nil] at hk hk1
  have hk_cases : k = 1 ∨ k = 2 := by omega
  rcases hk_cases with rfl | rfl
  · simpa using ha
  · simpa using hb

lemma interiorOnRight_four {s a b t : ℝ × ℝ} (ha : orient2D s t a < 0) (hb : orient2D s t b < 0) :
    InteriorOnRight s t [s, a, b, t] := by
  refine ⟨by simp, fun k hk hk0 hk1 => ?_⟩
  simp only [List.length_cons, List.length_nil] at hk hk1
  have hk_cases : k = 1 ∨ k = 2 := by omega
  rcases hk_cases with rfl | rfl
  · simpa using ha
  · simpa using hb

/-! ## Section 2.3: Tests and Lemma 2.5 (`counting`) -/

/-- General open-set test (`Definition 2.2` of `upper_9.tex`): `R` is open, no witness in `W'`
    lies on `frontier R`, and `Sees P x a ↔ x ∈ R` for all `x ∈ W'`. -/
def IsTest (P : Set (ℝ × ℝ)) (W' : Set (ℝ × ℝ)) (a : ℝ × ℝ) (R : Set (ℝ × ℝ)) : Prop :=
  IsOpen R ∧ (∀ x ∈ W', x ∉ frontier R) ∧ (∀ x ∈ W', Sees P x a ↔ x ∈ R)

lemma witnessSet_mono {n : ℕ} {F F' N N' : Finset (Fin n)} {w : Finset (Fin n) → ℝ × ℝ}
    (hF : F ⊆ F') (hN : N ⊆ N') :
    WitnessSet F' N' w ⊆ WitnessSet F N w := by
  rintro x ⟨T, hFT, hdisj, rfl⟩
  exact ⟨T, hF.trans hFT, hdisj.mono_right hN, rfl⟩

lemma isTest_mono {P : Set (ℝ × ℝ)} {W₁ W₂ : Set (ℝ × ℝ)} {a : ℝ × ℝ} {R : Set (ℝ × ℝ)}
    (hsub : W₁ ⊆ W₂) (hT : IsTest P W₂ a R) : IsTest P W₁ a R :=
  ⟨hT.1, fun x hx => hT.2.1 x (hsub hx), fun x hx => hT.2.2 x (hsub hx)⟩

lemma isWedgeTest_mono {P : Set (ℝ × ℝ)} {W₁ W₂ : Set (ℝ × ℝ)} {a : ℝ × ℝ} {R : OpenWedge}
    (hsub : W₁ ⊆ W₂) (hT : IsWedgeTest P W₂ a R) : IsWedgeTest P W₁ a R :=
  fun x hx => hT x (hsub hx)

lemma isHalfPlaneTest_mono {P : Set (ℝ × ℝ)} {W₁ W₂ : Set (ℝ × ℝ)} {a : ℝ × ℝ} {H : OpenHalfPlane}
    (hsub : W₁ ⊆ W₂) (hT : IsHalfPlaneTest P W₂ a H) : IsHalfPlaneTest P W₁ a H :=
  fun x hx => hT x (hsub hx)

lemma isOpen_wedgeOpenSet (R : OpenWedge) : IsOpen {p : ℝ × ℝ | R.MemOpen p} := by
  have heq : {p : ℝ × ℝ | R.MemOpen p} =
      {p : ℝ × ℝ | 0 < R.u₁.1 * (p.1 - R.y.1) + R.u₁.2 * (p.2 - R.y.2)} ∩
      {p : ℝ × ℝ | 0 < R.u₂.1 * (p.1 - R.y.1) + R.u₂.2 * (p.2 - R.y.2)} := by
    ext p; simp [OpenWedge.MemOpen]
  rw [heq]
  exact IsOpen.inter
    (isOpen_lt continuous_const (by continuity))
    (isOpen_lt continuous_const (by continuity))

lemma isOpen_halfPlanePosSet (H : OpenHalfPlane) : IsOpen {p : ℝ × ℝ | H.MemPos p} := by
  change IsOpen {p : ℝ × ℝ | 0 < H.n.1 * p.1 + H.n.2 * p.2 + H.c}
  exact isOpen_lt continuous_const (by continuity)

lemma openWedge_not_frontier_iff (R : OpenWedge) (p : ℝ × ℝ) :
    p ∉ frontier {q : ℝ × ℝ | R.MemOpen q} ↔ R.MemOpen p ∨ R.MemExt p := by
  have hopen := isOpen_wedgeOpenSet R
  rw [frontier_eq_closure_inter_closure]
  constructor
  · intro hp
    by_contra hnot
    push Not at hnot
    have hl1 : 0 ≤ R.u₁.1 * (p.1 - R.y.1) + R.u₁.2 * (p.2 - R.y.2) := by
      by_contra hlt
      exact hnot.2 (Or.inl (not_le.mp hlt))
    have hl2 : 0 ≤ R.u₂.1 * (p.1 - R.y.1) + R.u₂.2 * (p.2 - R.y.2) := by
      by_contra hlt
      exact hnot.2 (Or.inr (not_le.mp hlt))
    apply hp
    refine ⟨?_, ?_⟩
    · rw [Metric.mem_closure_iff]
      intro ε hε
      let d : ℝ × ℝ := (R.u₂.2 - R.u₁.2, R.u₁.1 - R.u₂.1)
      let M : ℝ := |d.1| + |d.2| + 1
      have hM : 0 < M := by positivity
      let t : ℝ := ε / (2 * M)
      have ht : 0 < t := div_pos hε (by linarith)
      refine ⟨(p.1 + t * d.1, p.2 + t * d.2), ?_, ?_⟩
      · have hnd := R.h_nondeg
        have e1 : R.u₁.1 * ((p.1 + t * d.1) - R.y.1) + R.u₁.2 * ((p.2 + t * d.2) - R.y.2) =
            (R.u₁.1 * (p.1 - R.y.1) + R.u₁.2 * (p.2 - R.y.2)) +
            t * (R.u₁.1 * R.u₂.2 - R.u₁.2 * R.u₂.1) := by dsimp [d]; ring
        have e2 : R.u₂.1 * ((p.1 + t * d.1) - R.y.1) + R.u₂.2 * ((p.2 + t * d.2) - R.y.2) =
            (R.u₂.1 * (p.1 - R.y.1) + R.u₂.2 * (p.2 - R.y.2)) +
            t * (R.u₁.1 * R.u₂.2 - R.u₁.2 * R.u₂.1) := by dsimp [d]; ring
        exact ⟨by dsimp [OpenWedge.MemOpen]; rw [e1]; nlinarith,
               by dsimp [OpenWedge.MemOpen]; rw [e2]; nlinarith⟩
      · rw [dist_comm, Prod.dist_eq]
        simp only [Real.dist_eq]
        have hx1 : |(p.1 + t * d.1) - p.1| < ε := by
          have : (p.1 + t * d.1) - p.1 = t * d.1 := by ring
          rw [this, abs_mul, abs_of_pos ht]
          have hd1 : |d.1| ≤ M := by
            have := abs_nonneg d.2
            dsimp [M]; linarith
          calc t * |d.1| ≤ t * M := mul_le_mul_of_nonneg_left hd1 (le_of_lt ht)
            _ = ε / 2 := by dsimp [t]; field_simp [ne_of_gt hM]
            _ < ε := by linarith
        have hx2 : |(p.2 + t * d.2) - p.2| < ε := by
          have : (p.2 + t * d.2) - p.2 = t * d.2 := by ring
          rw [this, abs_mul, abs_of_pos ht]
          have hd2 : |d.2| ≤ M := by
            have := abs_nonneg d.1
            dsimp [M]; linarith
          calc t * |d.2| ≤ t * M := mul_le_mul_of_nonneg_left hd2 (le_of_lt ht)
            _ = ε / 2 := by dsimp [t]; field_simp [ne_of_gt hM]
            _ < ε := by linarith
        exact max_lt hx1 hx2
    · rw [hopen.isClosed_compl.closure_eq]
      exact hnot.1
  · rintro (hopen_p | hext_p) ⟨_, hcl⟩
    · have : p ∈ ({q : ℝ × ℝ | R.MemOpen q}ᶜ)ᶜ := not_not.mpr hopen_p
      rw [hopen.isClosed_compl.closure_eq] at hcl
      exact hcl hopen_p
    · have hclosed : IsClosed {q : ℝ × ℝ | ¬ R.MemExt q} := by
        have heq : {q : ℝ × ℝ | ¬ R.MemExt q} =
            {q : ℝ × ℝ | 0 ≤ R.u₁.1 * (q.1 - R.y.1) + R.u₁.2 * (q.2 - R.y.2)} ∩
            {q : ℝ × ℝ | 0 ≤ R.u₂.1 * (q.1 - R.y.1) + R.u₂.2 * (q.2 - R.y.2)} := by
          ext q
          simp only [Set.mem_setOf_eq, Set.mem_inter_iff, OpenWedge.MemExt, not_or, not_lt]
        rw [heq]
        exact IsClosed.inter
          (isClosed_le continuous_const (by continuity))
          (isClosed_le continuous_const (by continuity))
      have hsub : {q : ℝ × ℝ | R.MemOpen q} ⊆ {q : ℝ × ℝ | ¬ R.MemExt q} := by
        intro q hq
        simp only [Set.mem_setOf_eq, OpenWedge.MemOpen, OpenWedge.MemExt, not_or, not_lt] at hq ⊢
        exact ⟨le_of_lt hq.1, le_of_lt hq.2⟩
      have := closure_minimal hsub hclosed ‹p ∈ closure {q : ℝ × ℝ | R.MemOpen q}›
      exact this hext_p

lemma openHalfPlane_not_frontier_iff (H : OpenHalfPlane) (p : ℝ × ℝ) :
    p ∉ frontier {q : ℝ × ℝ | H.MemPos q} ↔ H.MemPos p ∨ H.MemNeg p := by
  have hopen := isOpen_halfPlanePosSet H
  rw [frontier_eq_closure_inter_closure]
  constructor
  · intro hp
    by_contra hnot
    push Not at hnot
    have h0 : H.n.1 * p.1 + H.n.2 * p.2 + H.c = 0 :=
      le_antisymm (not_lt.mp hnot.1) (not_lt.mp hnot.2)
    apply hp
    refine ⟨?_, ?_⟩
    · rw [Metric.mem_closure_iff]
      intro ε hε
      let M : ℝ := |H.n.1| + |H.n.2| + 1
      have hM : 0 < M := by positivity
      let t : ℝ := ε / (2 * M)
      have ht : 0 < t := div_pos hε (by linarith)
      refine ⟨(p.1 + t * H.n.1, p.2 + t * H.n.2), ?_, ?_⟩
      · have hs : 0 < H.n.1 ^ 2 + H.n.2 ^ 2 := by
          rcases H.hn with h1 | h2
          · exact add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero h1) (sq_nonneg _)
          · exact add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_ne_zero h2)
        change 0 < H.n.1 * (p.1 + t * H.n.1) + H.n.2 * (p.2 + t * H.n.2) + H.c
        have heq : H.n.1 * (p.1 + t * H.n.1) + H.n.2 * (p.2 + t * H.n.2) + H.c =
            (H.n.1 * p.1 + H.n.2 * p.2 + H.c) + t * (H.n.1 ^ 2 + H.n.2 ^ 2) := by ring
        rw [heq, h0, zero_add]
        exact mul_pos ht hs
      · rw [dist_comm, Prod.dist_eq]
        simp only [Real.dist_eq]
        have hx1 : |(p.1 + t * H.n.1) - p.1| < ε := by
          have : (p.1 + t * H.n.1) - p.1 = t * H.n.1 := by ring
          rw [this, abs_mul, abs_of_pos ht]
          have h1 : |H.n.1| ≤ M := by have := abs_nonneg H.n.2; dsimp [M]; linarith
          calc t * |H.n.1| ≤ t * M := mul_le_mul_of_nonneg_left h1 (le_of_lt ht)
            _ = ε / 2 := by dsimp [t]; field_simp [ne_of_gt hM]
            _ < ε := by linarith
        have hx2 : |(p.2 + t * H.n.2) - p.2| < ε := by
          have : (p.2 + t * H.n.2) - p.2 = t * H.n.2 := by ring
          rw [this, abs_mul, abs_of_pos ht]
          have h2 : |H.n.2| ≤ M := by have := abs_nonneg H.n.1; dsimp [M]; linarith
          calc t * |H.n.2| ≤ t * M := mul_le_mul_of_nonneg_left h2 (le_of_lt ht)
            _ = ε / 2 := by dsimp [t]; field_simp [ne_of_gt hM]
            _ < ε := by linarith
        exact max_lt hx1 hx2
    · rw [hopen.isClosed_compl.closure_eq]
      exact hnot.1
  · rintro (hpos | hneg) ⟨hcl, hc⟩
    · rw [hopen.isClosed_compl.closure_eq] at hc
      exact hc hpos
    · have hclosed : IsClosed {q : ℝ × ℝ | ¬ H.MemNeg q} := by
        have heq : {q : ℝ × ℝ | ¬ H.MemNeg q} =
            {q : ℝ × ℝ | 0 ≤ H.n.1 * q.1 + H.n.2 * q.2 + H.c} := by
          ext q; simp [OpenHalfPlane.MemNeg]
        rw [heq]
        exact isClosed_le continuous_const (by continuity)
      have hsub : {q : ℝ × ℝ | H.MemPos q} ⊆ {q : ℝ × ℝ | ¬ H.MemNeg q} := by
        intro q hq
        simp only [Set.mem_setOf_eq, OpenHalfPlane.MemPos, OpenHalfPlane.MemNeg, not_lt] at hq ⊢
        exact le_of_lt hq
      exact (closure_minimal hsub hclosed hcl) hneg

lemma isWedgeTest_isTest {P : Set (ℝ × ℝ)} {W' : Set (ℝ × ℝ)} {a : ℝ × ℝ} {R : OpenWedge}
    (hT : IsWedgeTest P W' a R) : IsTest P W' a {q : ℝ × ℝ | R.MemOpen q} :=
  ⟨isOpen_wedgeOpenSet R, fun x hx => (openWedge_not_frontier_iff R x).mpr (hT x hx).1,
   fun x hx => (hT x hx).2⟩

lemma isHalfPlaneTest_isTest {P : Set (ℝ × ℝ)} {W' : Set (ℝ × ℝ)} {a : ℝ × ℝ} {H : OpenHalfPlane}
    (hT : IsHalfPlaneTest P W' a H) : IsTest P W' a {q : ℝ × ℝ | H.MemPos q} :=
  ⟨isOpen_halfPlanePosSet H, fun x hx => (openHalfPlane_not_frontier_iff H x).mpr (hT x hx).1,
   fun x hx => (hT x hx).2⟩

/-- Lemma 2.5 (`counting`, general open-set test form): for disjoint `F, N` and distinct points
    `a_1, ..., a_k ∉ F ∪ N` with tests `R_i` on `W(F; N)`, every subset `I ⊆ Fin k` is
    realized by a witness `w T ∈ W(F; N)` lying on no boundary `frontier (R i)`. -/
theorem counting {n k : ℕ} {P : Set (ℝ × ℝ)} {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ}
    (hP : ShatteredSimplePolygon P S w)
    {F N : Finset (Fin n)} (hdisj : Disjoint F N)
    (a : Fin k → Fin n) (ha_inj : Function.Injective a)
    (ha_out : ∀ i : Fin k, a i ∉ F ∧ a i ∉ N)
    (R : Fin k → Set (ℝ × ℝ))
    (hR : ∀ i : Fin k, IsTest P (WitnessSet F N w) (S (a i)) (R i))
    (I : Finset (Fin k)) :
    ∃ x ∈ WitnessSet F N w, (∀ i : Fin k, x ∉ frontier (R i)) ∧ (∀ i : Fin k, x ∈ R i ↔ i ∈ I) := by
  let T : Finset (Fin n) := F ∪ I.image a
  have hFT : F ⊆ T := Finset.subset_union_left
  have hTN : Disjoint T N := by
    rw [Finset.disjoint_union_left]
    refine ⟨hdisj, Finset.disjoint_left.mpr ?_⟩
    intro y hy
    rcases Finset.mem_image.mp hy with ⟨i, _, rfl⟩
    exact (ha_out i).2
  have hxW : w T ∈ WitnessSet F N w := ⟨T, hFT, hTN, rfl⟩
  refine ⟨w T, hxW, fun i => (hR i).2.1 (w T) hxW, fun i => ?_⟩
  rw [← (hR i).2.2 (w T) hxW, hP.shatters T (a i)]
  simp only [T, Finset.mem_union, Finset.mem_image]
  constructor
  · rintro (hF | ⟨j, hjI, hj_eq⟩)
    · exact False.elim ((ha_out i).1 hF)
    · exact (ha_inj hj_eq) ▸ hjI
  · intro hiI
    exact Or.inr ⟨i, hiI, rfl⟩

/-- Lemma 2.5 (`counting`, wedge-test bitmask form). -/
theorem counting_wedge_tests {n k : ℕ} {P : Set (ℝ × ℝ)} {S : Fin n → ℝ × ℝ}
    {w : Finset (Fin n) → ℝ × ℝ}
    (hP : ShatteredSimplePolygon P S w)
    {F N : Finset (Fin n)} (hdisj : Disjoint F N)
    (a : Fin k → Fin n) (ha_inj : Function.Injective a)
    (ha_out : ∀ i : Fin k, a i ∉ F ∧ a i ∉ N)
    (R : Fin k → OpenWedge)
    (hR : ∀ i : Fin k, IsWedgeTest P (WitnessSet F N w) (S (a i)) (R i))
    (m : Fin k → Bool) :
    ∃ x ∈ WitnessSet F N w, ∀ i : Fin k, if m i then (R i).MemOpen x else (R i).MemExt x := by
  let I : Finset (Fin k) := Finset.univ.filter (fun i => m i = true)
  obtain ⟨x, hxW, _, hmem⟩ :=
    counting hP hdisj a ha_inj ha_out (fun i => {q | (R i).MemOpen q})
      (fun i => isWedgeTest_isTest (hR i)) I
  refine ⟨x, hxW, fun i => ?_⟩
  by_cases hmi : m i
  · simp only [hmi, ↓reduceIte]
    exact (hmem i).mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hmi⟩)
  · simp only [hmi, Bool.false_eq_true, ↓reduceIte]
    have hnot : x ∉ {q : ℝ × ℝ | (R i).MemOpen q} := by
      intro hxR
      have hiI := (hmem i).mp hxR
      simp [I] at hiI
      exact hmi hiI
    rcases (hR i x hxW).1 with ho | he
    · exact False.elim (hnot ho)
    · exact he

/-- Contradiction from six wedge tests on `W(F; N)` using `isler_six_wedges`. -/
theorem no_six_wedge_tests {n : ℕ} {P : Set (ℝ × ℝ)} {S : Fin n → ℝ × ℝ}
    {w : Finset (Fin n) → ℝ × ℝ}
    (hP : ShatteredSimplePolygon P S w)
    {F N : Finset (Fin n)} (hdisj : Disjoint F N)
    (a : Fin 6 → Fin n) (ha_inj : Function.Injective a)
    (ha_out : ∀ i : Fin 6, a i ∉ F ∧ a i ∉ N)
    (R : Fin 6 → OpenWedge)
    (hR : ∀ i : Fin 6, IsWedgeTest P (WitnessSet F N w) (S (a i)) (R i)) :
    False := by
  apply hP.isler_six_wedges R
  intro m
  obtain ⟨x, _, hmask⟩ := counting_wedge_tests hP hdisj a ha_inj ha_out R hR m
  exact ⟨x, hmask⟩

/-- Lemma 2.5 (`counting`, mixed half-plane + wedge-test bitmask form). -/
theorem counting_mixed_tests {n k₁ k₂ : ℕ} {P : Set (ℝ × ℝ)} {S : Fin n → ℝ × ℝ}
    {w : Finset (Fin n) → ℝ × ℝ}
    (hP : ShatteredSimplePolygon P S w)
    {F N : Finset (Fin n)} (hdisj : Disjoint F N)
    (ah : Fin k₁ → Fin n) (aw : Fin k₂ → Fin n)
    (hah_inj : Function.Injective ah) (haw_inj : Function.Injective aw)
    (hdisj_a : ∀ i j, ah i ≠ aw j)
    (hah_out : ∀ i, ah i ∉ F ∧ ah i ∉ N)
    (haw_out : ∀ j, aw j ∉ F ∧ aw j ∉ N)
    (H : Fin k₁ → OpenHalfPlane) (R : Fin k₂ → OpenWedge)
    (hH : ∀ i, IsHalfPlaneTest P (WitnessSet F N w) (S (ah i)) (H i))
    (hR : ∀ j, IsWedgeTest P (WitnessSet F N w) (S (aw j)) (R j))
    (mh : Fin k₁ → Bool) (mw : Fin k₂ → Bool) :
    ∃ x ∈ WitnessSet F N w,
      (∀ i, if mh i then (H i).MemPos x else (H i).MemNeg x) ∧
      (∀ j, if mw j then (R j).MemOpen x else (R j).MemExt x) := by
  let a : Fin (k₁ + k₂) → Fin n := Fin.addCases ah aw
  have ha_inj : Function.Injective a := by
    intro u v huv
    refine Fin.addCases (fun i => Fin.addCases (fun i' h => ?_) (fun j' h => ?_) v)
      (fun j => Fin.addCases (fun i' h => ?_) (fun j' h => ?_) v) u huv
    · simp only [a, Fin.addCases_left] at h
      exact congrArg (Fin.castAdd k₂) (hah_inj h)
    · simp only [a, Fin.addCases_left, Fin.addCases_right] at h
      exact False.elim (hdisj_a i j' h)
    · simp only [a, Fin.addCases_left, Fin.addCases_right] at h
      exact False.elim (hdisj_a i' j h.symm)
    · simp only [a, Fin.addCases_right] at h
      exact congrArg (Fin.natAdd k₁) (haw_inj h)
  have ha_out : ∀ u, a u ∉ F ∧ a u ∉ N := by
    refine Fin.addCases (fun i => ?_) (fun j => ?_)
    · simpa [a] using hah_out i
    · simpa [a] using haw_out j
  let Reg : Fin (k₁ + k₂) → Set (ℝ × ℝ) :=
    Fin.addCases (fun i => {q | (H i).MemPos q}) (fun j => {q | (R j).MemOpen q})
  have hReg : ∀ u, IsTest P (WitnessSet F N w) (S (a u)) (Reg u) := by
    refine Fin.addCases (fun i => ?_) (fun j => ?_)
    · simpa [a, Reg] using isHalfPlaneTest_isTest (hH i)
    · simpa [a, Reg] using isWedgeTest_isTest (hR j)
  let m : Fin (k₁ + k₂) → Bool := Fin.addCases mh mw
  let I : Finset (Fin (k₁ + k₂)) := Finset.univ.filter (fun u => m u = true)
  obtain ⟨x, hxW, _, hmem⟩ := counting hP hdisj a ha_inj ha_out Reg hReg I
  refine ⟨x, hxW, fun i => ?_, fun j => ?_⟩
  · have hi := hmem (Fin.castAdd k₂ i)
    simp only [Reg, Fin.addCases_left, Set.mem_setOf_eq, I, Finset.mem_filter, Finset.mem_univ,
      true_and, m] at hi
    by_cases hmi : mh i
    · simp only [hmi, ↓reduceIte]
      exact hi.mpr hmi
    · simp only [hmi, Bool.false_eq_true, ↓reduceIte]
      have hnot : ¬ (H i).MemPos x := fun hp => hmi (hi.mp hp)
      rcases (hH i x hxW).1 with hp | hn
      · exact False.elim (hnot hp)
      · exact hn
  · have hj := hmem (Fin.natAdd k₁ j)
    simp only [Reg, Fin.addCases_right, Set.mem_setOf_eq, I, Finset.mem_filter, Finset.mem_univ,
      true_and, m] at hj
    by_cases hmj : mw j
    · simp only [hmj, ↓reduceIte]
      exact hj.mpr hmj
    · simp only [hmj, Bool.false_eq_true, ↓reduceIte]
      have hnot : ¬ (R j).MemOpen x := fun ho => hmj (hj.mp ho)
      rcases (hR j x hxW).1 with ho | he
      · exact False.elim (hnot ho)
      · exact he

/-! ## Section 2.4: Open Triangles, `U(a; b, c)`, Equation (1), Lemma 2.6 (`Cone`), Lemma 2.7, Corollary 2.8 -/

/-- Strict interior of the triangle `(p, q, r)` via strictly positive barycentric coordinates. -/
def InOpenTri (p q r z : ℝ × ℝ) : Prop :=
  ∃ μ₁ μ₂ μ₃ : ℝ, 0 < μ₁ ∧ 0 < μ₂ ∧ 0 < μ₃ ∧ μ₁ + μ₂ + μ₃ = 1 ∧
    z.1 = μ₁ * p.1 + μ₂ * q.1 + μ₃ * r.1 ∧
    z.2 = μ₁ * p.2 + μ₂ * q.2 + μ₃ * r.2

lemma inOpenTri_inClosedTri {p q r z : ℝ × ℝ} (h : InOpenTri p q r z) : InClosedTri p q r z := by
  rcases h with ⟨μ₁, μ₂, μ₃, h1, h2, h3, hsum, hx, hy⟩
  exact ⟨μ₁, μ₂, μ₃, le_of_lt h1, le_of_lt h2, le_of_lt h3, hsum, hx, hy⟩

lemma inOpenTri_mem_convexHull {p q r z : ℝ × ℝ} (h : InOpenTri p q r z) :
    z ∈ convexHull ℝ ({p, q, r} : Set (ℝ × ℝ)) :=
  (inClosedTri_iff_mem_convexHull p q r z).mp (inOpenTri_inClosedTri h)

lemma inOpenTri_perm_23 {p q r z : ℝ × ℝ} (h : InOpenTri p q r z) : InOpenTri p r q z := by
  rcases h with ⟨μ₁, μ₂, μ₃, h1, h2, h3, hsum, hx, hy⟩
  exact ⟨μ₁, μ₃, μ₂, h1, h3, h2, by linarith, by linarith, by linarith⟩

lemma inOpenTri_perm_12 {p q r z : ℝ × ℝ} (h : InOpenTri p q r z) : InOpenTri q p r z := by
  rcases h with ⟨μ₁, μ₂, μ₃, h1, h2, h3, hsum, hx, hy⟩
  exact ⟨μ₂, μ₁, μ₃, h2, h1, h3, by linarith, by linarith, by linarith⟩

lemma inOpenTri_cycle {p q r z : ℝ × ℝ} (h : InOpenTri p q r z) : InOpenTri q r p z := by
  rcases h with ⟨μ₁, μ₂, μ₃, h1, h2, h3, hsum, hx, hy⟩
  exact ⟨μ₂, μ₃, μ₁, h2, h3, h1, by linarith, by linarith, by linarith⟩

lemma inOpenTri_of_noncollinear_inClosedTri {p q r z : ℝ × ℝ}
    (hclosed : InClosedTri p q r z)
    (h1 : orient2D q r z ≠ 0) (h2 : orient2D r p z ≠ 0) (h3 : orient2D p q z ≠ 0) :
    InOpenTri p q r z := by
  rcases hclosed with ⟨μ₁, μ₂, μ₃, hm1, hm2, hm3, hsum, hz1, hz2⟩
  have hpos1 : 0 < μ₁ := by
    refine lt_of_le_of_ne hm1 (fun heq => h1 ?_)
    subst heq
    have hμ : μ₂ = 1 - μ₃ := by linarith
    unfold orient2D
    rw [hz1, hz2, hμ]
    ring
  have hpos2 : 0 < μ₂ := by
    refine lt_of_le_of_ne hm2 (fun heq => h2 ?_)
    subst heq
    have hμ : μ₁ = 1 - μ₃ := by linarith
    unfold orient2D
    rw [hz1, hz2, hμ]
    ring
  have hpos3 : 0 < μ₃ := by
    refine lt_of_le_of_ne hm3 (fun heq => h3 ?_)
    subst heq
    have hμ : μ₁ = 1 - μ₂ := by linarith
    unfold orient2D
    rw [hz1, hz2, hμ]
    ring
  exact ⟨μ₁, μ₂, μ₃, hpos1, hpos2, hpos3, hsum, hz1, hz2⟩

/-- Open cone `cone(d₁, d₂) = {α d₁ + β d₂ : α, β > 0}` (`upper_9.tex` line 83). -/
def OpenCone (d₁ d₂ : ℝ × ℝ) : Set (ℝ × ℝ) :=
  {v : ℝ × ℝ | ∃ α β : ℝ, 0 < α ∧ 0 < β ∧ v = α • d₁ + β • d₂}

/-- Opposite cone `U(a; b, c) = a + cone(a - b, a - c)` (`upper_9.tex` line 215). -/
def UCone (a b c : ℝ × ℝ) : Set (ℝ × ℝ) :=
  {x : ℝ × ℝ | ∃ α β : ℝ, 0 < α ∧ 0 < β ∧ x = a + α • (a - b) + β • (a - c)}

lemma uCone_symm (a b c : ℝ × ℝ) : UCone a b c = UCone a c b := by
  ext x
  simp only [UCone, Set.mem_setOf_eq]
  constructor <;> rintro ⟨α, β, hα, hβ, rfl⟩
  · exact ⟨β, α, hβ, hα, by ext <;> simp <;> ring⟩
  · exact ⟨β, α, hβ, hα, by ext <;> simp <;> ring⟩

lemma mem_uCone_iff_inOpenTri (a b c x : ℝ × ℝ) :
    x ∈ UCone a b c ↔ InOpenTri x b c a := by
  constructor
  · rintro ⟨α, β, hα, hβ, rfl⟩
    let s : ℝ := 1 + α + β
    have hs : 0 < s := by linarith
    refine ⟨1 / s, α / s, β / s, div_pos zero_lt_one hs, div_pos hα hs, div_pos hβ hs, ?_, ?_, ?_⟩
    · field_simp [ne_of_gt hs]; ring
    · change a.1 = (1 / s) * (a.1 + α * (a.1 - b.1) + β * (a.1 - c.1)) + (α / s) * b.1 + (β / s) * c.1
      field_simp [ne_of_gt hs]; dsimp [s]; ring
    · change a.2 = (1 / s) * (a.2 + α * (a.2 - b.2) + β * (a.2 - c.2)) + (α / s) * b.2 + (β / s) * c.2
      field_simp [ne_of_gt hs]; dsimp [s]; ring
  · rintro ⟨μ₁, μ₂, μ₃, h1, h2, h3, hsum, ha1, ha2⟩
    refine ⟨μ₂ / μ₁, μ₃ / μ₁, div_pos h2 h1, div_pos h3 h1, ?_⟩
    have h1_ne : μ₁ ≠ 0 := ne_of_gt h1
    ext
    · change x.1 = a.1 + (μ₂ / μ₁) * (a.1 - b.1) + (μ₃ / μ₁) * (a.1 - c.1)
      field_simp [h1_ne]
      rw [ha1, show μ₁ = 1 - μ₂ - μ₃ by linarith]
      ring
    · change x.2 = a.2 + (μ₂ / μ₁) * (a.2 - b.2) + (μ₃ / μ₁) * (a.2 - c.2)
      field_simp [h1_ne]
      rw [ha2, show μ₁ = 1 - μ₂ - μ₃ by linarith]
      ring

/-- Equation (1) (`U-halfplanes`, `upper_9.tex` lines 218–221): when `0 < orient2D a b c`,
    `U(a; b, c) = H^-(c, a) ∩ H^-(a, b) = (oppositeConeWedge a b c h_ccw).MemOpen ⊆ H^-(c, b)`. -/
theorem u_halfplanes {a b c : ℝ × ℝ} (h_ccw : 0 < orient2D a b c) (x : ℝ × ℝ) :
    (x ∈ UCone a b c ↔ orient2D c a x < 0 ∧ orient2D a b x < 0) ∧
    (x ∈ UCone a b c ↔ (oppositeConeWedge a b c h_ccw).MemOpen x) ∧
    (x ∈ UCone a b c → orient2D c b x < 0) := by
  have hcax_eq : ∀ α β : ℝ,
      orient2D c a (a + α • (a - b) + β • (a - c)) = -α * orient2D a b c := by
    intro α β
    unfold orient2D
    simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
      Prod.fst_sub, Prod.snd_sub, smul_eq_mul]
    ring
  have habx_eq : ∀ α β : ℝ,
      orient2D a b (a + α • (a - b) + β • (a - c)) = -β * orient2D a b c := by
    intro α β
    unfold orient2D
    simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
      Prod.fst_sub, Prod.snd_sub, smul_eq_mul]
    ring
  have hcbx_eq : ∀ α β : ℝ,
      orient2D c b (a + α • (a - b) + β • (a - c)) = -(1 + α + β) * orient2D a b c := by
    intro α β
    unfold orient2D
    simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
      Prod.fst_sub, Prod.snd_sub, smul_eq_mul]
    ring
  have h1 : x ∈ UCone a b c ↔ orient2D c a x < 0 ∧ orient2D a b x < 0 := by
    constructor
    · rintro ⟨α, β, hα, hβ, rfl⟩
      rw [hcax_eq, habx_eq]
      exact ⟨by nlinarith, by nlinarith⟩
    · rintro ⟨hcax, habx⟩
      have hd_ne : orient2D a b c ≠ 0 := ne_of_gt h_ccw
      let α := -orient2D c a x / orient2D a b c
      let β := -orient2D a b x / orient2D a b c
      refine ⟨α, β, div_pos (neg_pos.mpr hcax) h_ccw, div_pos (neg_pos.mpr habx) h_ccw, ?_⟩
      ext
      · change x.1 = a.1 + α * (a.1 - b.1) + β * (a.1 - c.1)
        dsimp [α, β]
        unfold orient2D
        unfold orient2D at hd_ne
        field_simp [hd_ne]
        ring
      · change x.2 = a.2 + α * (a.2 - b.2) + β * (a.2 - c.2)
        dsimp [α, β]
        unfold orient2D
        unfold orient2D at hd_ne
        field_simp [hd_ne]
        ring
  have hwedge : (oppositeConeWedge a b c h_ccw).MemOpen x ↔
      orient2D c a x < 0 ∧ orient2D a b x < 0 := by
    unfold OpenWedge.MemOpen oppositeConeWedge orient2D
    dsimp only
    constructor <;> rintro ⟨u, v⟩ <;> exact ⟨by linarith, by linarith⟩
  have h2 : x ∈ UCone a b c ↔ (oppositeConeWedge a b c h_ccw).MemOpen x :=
    h1.trans hwedge.symm
  have h3 : x ∈ UCone a b c → orient2D c b x < 0 := by
    rintro ⟨α, β, hα, hβ, rfl⟩
    rw [hcbx_eq]
    nlinarith
  exact ⟨h1, h2, h3⟩

lemma u_halfplanes_separates {a b c x : ℝ × ℝ} (h_neq : orient2D a b c ≠ 0)
    (hx : x ∈ UCone a b c) : orient2D a x b * orient2D a x c < 0 := by
  rcases lt_trichotomy (orient2D a b c) 0 with hneg | hzero | hpos
  · have hccw : 0 < orient2D a c b := by rw [orient2D_swap23]; linarith
    have hx' : x ∈ UCone a c b := (uCone_symm a b c) ▸ hx
    obtain ⟨hb, hc⟩ := ((u_halfplanes hccw x).1).mp hx'
    have hb' : orient2D a x b < 0 := by
      have heq : orient2D a x b = orient2D b a x := orient2D_cycle b a x
      linarith
    have hc' : 0 < orient2D a x c := by rw [orient2D_swap23]; linarith
    exact mul_neg_of_neg_of_pos hb' hc'
  · exact False.elim (h_neq hzero)
  · obtain ⟨hc, hb⟩ := ((u_halfplanes hpos x).1).mp hx
    have hb' : 0 < orient2D a x b := by rw [orient2D_swap23]; linarith
    have hc' : orient2D a x c < 0 := by
      have heq : orient2D a x c = orient2D c a x := orient2D_cycle c a x
      linarith
    exact mul_neg_of_pos_of_neg hb' hc'

/-- Helper: if `w, b, c` are collinear, `Sees P w b`, `Sees P w c`, and `InOpenTri w b c a`,
    then `Sees P w a`. -/
private lemma sees_of_collinear_inOpenTri {P : Set (ℝ × ℝ)} {w b c a : ℝ × ℝ}
    (hwb : Sees P w b) (hwc : Sees P w c)
    (ha : InOpenTri w b c a) (hcol : orient2D w b c = 0) :
    Sees P w a := by
  have exists_dir : ∃ (d : ℝ × ℝ) (tb tc : ℝ),
      b = w + tb • d ∧ c = w + tc • d ∧
      segment ℝ w b ∪ segment ℝ w c ⊆ (fun t : ℝ => w + t • d) '' Set.Icc (min 0 (min tb tc)) (max 1 (max tb tc)) ∧
      ((fun t : ℝ => w + t • d) '' Set.Icc (min 0 (min tb tc)) (max 1 (max tb tc)) ⊆ segment ℝ w b ∪ segment ℝ w c) := by
    by_cases hbw : b = w
    · refine ⟨c - w, 0, 1, ?_, ?_, ?_, ?_⟩
      · rw [hbw]; ext <;> simp
      · ext <;> simp
      · rintro z (hzb | hzc)
        · rw [hbw, segment_same] at hzb
          rw [Set.mem_singleton_iff.mp hzb]
          exact ⟨0, ⟨min_le_left _ _, le_max_of_le_left zero_le_one⟩,
            by ext <;> simp⟩
        · rw [segment_eq_image] at hzc
          rcases hzc with ⟨t, ht, rfl⟩
          exact ⟨t, ⟨le_trans (min_le_left _ _) ht.1, le_trans ht.2 (le_max_left _ _)⟩,
            by ext <;> simp [smul_eq_mul] <;> ring⟩
      · rintro _ ⟨t, ht, rfl⟩
        have ht01 : t ∈ Set.Icc 0 1 := by
          have hm1 : min 0 (min (0 : ℝ) 1) = 0 := by norm_num
          have hm2 : max 1 (max (0 : ℝ) 1) = 1 := by norm_num
          rw [hm1, hm2] at ht; exact ht
        right; rw [segment_eq_image]
        exact ⟨t, ht01, by ext <;> simp [smul_eq_mul] <;> ring⟩
    · have hbw_coord : b.1 - w.1 ≠ 0 ∨ b.2 - w.2 ≠ 0 := by
        by_contra hc; push Not at hc; exact hbw (by ext <;> linarith [hc.1, hc.2])
      obtain ⟨k, hk1, hk2⟩ : ∃ k : ℝ, c.1 = w.1 + k * (b.1 - w.1) ∧ c.2 = w.2 + k * (b.2 - w.2) := by
        unfold orient2D at hcol
        rcases hbw_coord with hx | hy
        · refine ⟨(c.1 - w.1) / (b.1 - w.1), ?_, ?_⟩
          · field_simp [hx]; ring
          · field_simp [hx]; linear_combination hcol
        · refine ⟨(c.2 - w.2) / (b.2 - w.2), ?_, ?_⟩
          · field_simp [hy]; linear_combination -hcol
          · field_simp [hy]; ring
      refine ⟨b - w, 1, k, by ext <;> simp, by ext <;> simp [hk1, hk2], ?_, ?_⟩
      · rintro z (hzb | hzc)
        · rw [segment_eq_image] at hzb
          rcases hzb with ⟨t, ht, rfl⟩
          exact ⟨t, ⟨le_trans (min_le_left _ _) ht.1, le_trans ht.2 (le_max_left _ _)⟩,
            by ext <;> simp [smul_eq_mul] <;> ring⟩
        · rw [segment_eq_image] at hzc
          rcases hzc with ⟨t, ht, rfl⟩
          refine ⟨t * k, ⟨?_, ?_⟩, ?_⟩
          · by_cases hk0 : 0 ≤ k
            · exact le_trans (min_le_left _ _) (mul_nonneg ht.1 hk0)
            · have hk_neg : k < 0 := not_le.mp hk0
              have : k ≤ t * k := by nlinarith [ht.1, ht.2]
              exact le_trans (min_le_of_right_le (min_le_right _ _)) this
          · by_cases hk0 : 0 ≤ k
            · have : t * k ≤ k := mul_le_of_le_one_left hk0 ht.2
              exact le_trans this (le_max_of_le_right (le_max_right _ _))
            · have hk_neg : k < 0 := not_le.mp hk0
              have : t * k ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ht.1 (le_of_lt hk_neg)
              exact le_trans this (le_max_of_le_left zero_le_one)
          · ext <;> simp [smul_eq_mul, hk1, hk2] <;> ring
      · rintro _ ⟨t, ht, rfl⟩
        by_cases ht01 : 0 ≤ t ∧ t ≤ 1
        · left; rw [segment_eq_image]
          exact ⟨t, ht01, by ext <;> simp [smul_eq_mul] <;> ring⟩
        · right; rw [segment_eq_image]
          have ht' : min 0 k ≤ t ∧ t ≤ max 1 k := by
            simp only [Set.mem_Icc, min_le_iff, le_max_iff] at ht
            rcases ht with ⟨hlo, hhi⟩
            constructor
            · rcases hlo with h0 | h1 | hk <;>
                [exact min_le_of_left_le h0; exact min_le_of_left_le (by linarith); exact min_le_of_right_le hk]
            · rcases hhi with h1 | h1' | hk <;>
                [exact le_max_of_le_left h1; exact le_max_of_le_left h1'; exact le_max_of_le_right hk]
          by_cases ht_neg : t < 0
          · have hk_neg : k < 0 := by
              rcases min_le_iff.mp ht'.1 with h0 | hk <;> linarith
            refine ⟨t / k, ⟨div_nonneg_of_nonpos (le_of_lt ht_neg) (le_of_lt hk_neg), ?_⟩, ?_⟩
            · rw [div_le_one_of_neg hk_neg]
              rcases min_le_iff.mp ht'.1 with h0 | hk <;> linarith
            · have hk_ne : k ≠ 0 := ne_of_lt hk_neg
              ext <;> simp [smul_eq_mul, hk1, hk2] <;> field_simp [hk_ne] <;> ring
          · have ht_gt1 : 1 < t := by
              push Not at ht_neg
              by_contra hle; exact ht01 ⟨ht_neg, not_lt.mp hle⟩
            have hk_gt1 : 1 < k := by
              rcases le_max_iff.mp ht'.2 with h1 | hk <;> linarith
            refine ⟨t / k, ⟨div_nonneg (by linarith) (by linarith), (div_le_one (by linarith)).mpr ?_⟩, ?_⟩
            · rcases le_max_iff.mp ht'.2 with h1 | hk <;> linarith
            · have hk_ne : k ≠ 0 := by linarith
              ext <;> simp [smul_eq_mul, hk1, hk2] <;> field_simp [hk_ne] <;> ring
  rcases exists_dir with ⟨d, tb, tc, hb_eq, hc_eq, hsub1, hsub2⟩
  let Img := (fun t : ℝ => w + t • d) '' Set.Icc (min 0 (min tb tc)) (max 1 (max tb tc))
  have hImg_conv : Convex ℝ Img := by
    rintro _ ⟨t₁, ht1, rfl⟩ _ ⟨t₂, ht2, rfl⟩ α β hα hβ hαβ
    refine ⟨α * t₁ + β * t₂, (convex_Icc _ _) ht1 ht2 hα hβ hαβ, ?_⟩
    ext
    · simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]
      rw [show α = 1 - β by linarith]; ring
    · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
      rw [show α = 1 - β by linarith]; ring
  have ha_Img : a ∈ Img := by
    have htri : ({w, b, c} : Set (ℝ × ℝ)) ⊆ Img := by
      intro p hp
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
      rcases hp with hpw | hpb | hpc
      · rw [hpw]; exact hsub1 (Or.inl (left_mem_segment ℝ w b))
      · rw [hpb]; exact hsub1 (Or.inl (right_mem_segment ℝ w b))
      · rw [hpc]; exact hsub1 (Or.inr (right_mem_segment ℝ w c))
    exact convexHull_min htri hImg_conv (inOpenTri_mem_convexHull ha)
  have hw_Img : w ∈ Img := hsub1 (Or.inl (left_mem_segment ℝ w b))
  exact (hImg_conv.segment_subset hw_Img ha_Img).trans (hsub2.trans (Set.union_subset hwb hwc))

private lemma cone_aux {P : Set (ℝ × ℝ)} (hEnc : EnclosureDomain P)
    {a b c w x : ℝ × ℝ}
    (hwb : Sees P w b) (hwc : Sees P w c) (hnwa : ¬ Sees P w a)
    (ha : InOpenTri w b c a) (hxb : Sees P x b) (hxc : Sees P x c)
    (hwab : orient2D w a b < 0) (hwac : 0 < orient2D w a c) (hwax : 0 < orient2D w a x)
    (hxab : orient2D a b x ≠ 0) :
    x ∈ UCone a b c := by
  rcases ha with ⟨μ₁, μ₂, μ₃, hμ1, hμ2, hμ3, hμsum, ha1, ha2⟩
  have hμ23 : 0 < μ₂ + μ₃ := add_pos hμ2 hμ3
  let h : ℝ × ℝ := ((μ₂ / (μ₂ + μ₃)) * b.1 + (μ₃ / (μ₂ + μ₃)) * c.1,
                    (μ₂ / (μ₂ + μ₃)) * b.2 + (μ₃ / (μ₂ + μ₃)) * c.2)
  have h_mem_bc : h ∈ segment ℝ b c := by
    rw [segment_eq_image]
    refine ⟨μ₃ / (μ₂ + μ₃), ⟨div_nonneg (le_of_lt hμ3) (le_of_lt hμ23),
      (div_le_one hμ23).mpr (by linarith)⟩, ?_⟩
    have h23_ne : μ₂ + μ₃ ≠ 0 := ne_of_gt hμ23
    ext
    · change (1 - μ₃ / (μ₂ + μ₃)) * b.1 + (μ₃ / (μ₂ + μ₃)) * c.1 =
        (μ₂ / (μ₂ + μ₃)) * b.1 + (μ₃ / (μ₂ + μ₃)) * c.1
      field_simp [h23_ne]; ring
    · change (1 - μ₃ / (μ₂ + μ₃)) * b.2 + (μ₃ / (μ₂ + μ₃)) * c.2 =
        (μ₂ / (μ₂ + μ₃)) * b.2 + (μ₃ / (μ₂ + μ₃)) * c.2
      field_simp [h23_ne]; ring
  have ha_wh : a.1 = μ₁ * w.1 + (μ₂ + μ₃) * h.1 ∧ a.2 = μ₁ * w.2 + (μ₂ + μ₃) * h.2 := by
    have h23_ne : μ₂ + μ₃ ≠ 0 := ne_of_gt hμ23
    constructor <;> dsimp [h] <;> field_simp [h23_ne]
    · rw [ha1]; ring
    · rw [ha2]; ring
  have hden : 0 < orient2D w a x - orient2D w a b := by linarith
  let α₁ : ℝ := orient2D w a x / (orient2D w a x - orient2D w a b)
  let α₂ : ℝ := -orient2D w a b / (orient2D w a x - orient2D w a b)
  have hα1 : 0 < α₁ := div_pos hwax hden
  have hα2 : 0 < α₂ := div_pos (neg_pos.mpr hwab) hden
  have hαsum : α₁ + α₂ = 1 := by
    dsimp [α₁, α₂]
    field_simp [ne_of_gt hden]
    ring
  let t : ℝ × ℝ := (α₁ * b.1 + α₂ * x.1, α₁ * b.2 + α₂ * x.2)
  have ht_seg : t ∈ segment ℝ b x := by
    rw [segment_eq_image]
    refine ⟨α₂, ⟨le_of_lt hα2, by linarith⟩, ?_⟩
    ext
    · change (1 - α₂) * b.1 + α₂ * x.1 = α₁ * b.1 + α₂ * x.1
      rw [show 1 - α₂ = α₁ by linarith]
    · change (1 - α₂) * b.2 + α₂ * x.2 = α₁ * b.2 + α₂ * x.2
      rw [show 1 - α₂ = α₁ by linarith]
  have ht_seg' : t ∈ segment ℝ x b := by rwa [segment_symm]
  have ht_col : orient2D w a t = 0 := by
    have heq := orient2D_affine_comb w a b x t α₂
      (by dsimp [t]; linear_combination b.1 * hαsum)
      (by dsimp [t]; linear_combination b.2 * hαsum)
    rw [heq]
    dsimp [α₂]
    field_simp [ne_of_gt hden]
    ring
  have hwa_ne : w ≠ a := by
    intro hwa
    subst hwa
    exact hnwa (sees_refl (sees_mem_left hwb))
  have hwa_coord : a.1 - w.1 ≠ 0 ∨ a.2 - w.2 ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hwa_ne (by ext <;> linarith [hc.1, hc.2])
  obtain ⟨τ, hτ1, hτ2⟩ : ∃ τ : ℝ, t.1 - w.1 = τ * (a.1 - w.1) ∧ t.2 - w.2 = τ * (a.2 - w.2) := by
    unfold orient2D at ht_col
    rcases hwa_coord with hx1 | hx2
    · exact ⟨(t.1 - w.1) / (a.1 - w.1), by field_simp [hx1],
        by field_simp [hx1]; linear_combination ht_col⟩
    · exact ⟨(t.2 - w.2) / (a.2 - w.2),
        by field_simp [hx2]; linear_combination -ht_col, by field_simp [hx2]⟩
  have hτ_ne1 : τ ≠ 1 := by
    intro hτeq
    subst hτeq
    have hta : t = a := by ext <;> linarith
    apply hxab
    have h1 : t.1 = (1 - α₂) * b.1 + α₂ * x.1 := by dsimp [t]; linear_combination b.1 * hαsum
    have h2 : t.2 = (1 - α₂) * b.2 + α₂ * x.2 := by dsimp [t]; linear_combination b.2 * hαsum
    rw [hta] at h1 h2
    unfold orient2D
    rw [h1, h2]
    ring
  rcases lt_or_gt_of_ne hτ_ne1 with hτ_lt | hτ_gt
  · -- τ < 1: a lies strictly between t and h
    let s := μ₂ + μ₃
    have hs_lt1 : s < 1 := by linarith
    have hs_pos : 0 < s := hμ23
    have h1_lt_sinv : 1 < 1 / s := one_lt_one_div hs_pos hs_lt1
    have hden_th : 0 < 1 / s - τ := by linarith
    let γ₁ : ℝ := (1 / s - 1) / (1 / s - τ)
    let γ₂ : ℝ := (1 - τ) / (1 / s - τ)
    have hγ1 : 0 < γ₁ := div_pos (by linarith) hden_th
    have hγ2 : 0 < γ₂ := div_pos (by linarith) hden_th
    have hγsum : γ₁ + γ₂ = 1 := by
      dsimp [γ₁, γ₂]
      have hs_ne : s ≠ 0 := ne_of_gt hs_pos
      have hne2 : 1 / s - τ ≠ 0 := ne_of_gt hden_th
      have hne3 : 1 - s * τ ≠ 0 := by
        have h1 : 0 < s * (1 / s - τ) := mul_pos hs_pos hden_th
        have h2 : s * (1 / s - τ) = 1 - s * τ := by field_simp [hs_ne]
        linarith
      field_simp [hne2, hs_ne, hne3]
      ring
    have ha_th : a.1 = γ₁ * t.1 + γ₂ * h.1 ∧ a.2 = γ₁ * t.2 + γ₂ * h.2 := by
      have hs_ne : s ≠ 0 := ne_of_gt hs_pos
      have hh1 : h.1 - w.1 = (1 / s) * (a.1 - w.1) := by
        dsimp [s]
        field_simp [hs_ne]
        rw [ha_wh.1]
        linear_combination -w.1 * hμsum
      have hh2 : h.2 - w.2 = (1 / s) * (a.2 - w.2) := by
        dsimp [s]
        field_simp [hs_ne]
        rw [ha_wh.2]
        linear_combination -w.2 * hμsum
      have hne2 : 1 / s - τ ≠ 0 := ne_of_gt hden_th
      have hne3 : 1 - s * τ ≠ 0 := by
        have : 0 < 1 - s * τ := by
          have : 0 < s * (1 / s - τ) := mul_pos hs_pos hden_th
          have heq : s * (1 / s - τ) = 1 - s * τ := by field_simp [hs_ne]
          linarith
        exact ne_of_gt this
      constructor
      · dsimp [γ₁, γ₂]
        have ht1' : t.1 = w.1 + τ * (a.1 - w.1) := by linarith
        have hh1' : h.1 = w.1 + (1 / s) * (a.1 - w.1) := by linarith
        rw [ht1', hh1']
        field_simp [hne2, hs_ne, hne3]
        ring
      · dsimp [γ₁, γ₂]
        have ht2' : t.2 = w.2 + τ * (a.2 - w.2) := by linarith
        have hh2' : h.2 = w.2 + (1 / s) * (a.2 - w.2) := by linarith
        rw [ht2', hh2']
        field_simp [hne2, hs_ne, hne3]
        ring
    have ha_tri : InOpenTri x b c a := by
      let ν₁ : ℝ := γ₁ * α₂
      let ν₂ : ℝ := γ₁ * α₁ + γ₂ * (μ₂ / s)
      let ν₃ : ℝ := γ₂ * (μ₃ / s)
      refine ⟨ν₁, ν₂, ν₃, mul_pos hγ1 hα2,
        add_pos (mul_pos hγ1 hα1) (mul_pos hγ2 (div_pos hμ2 hs_pos)),
        mul_pos hγ2 (div_pos hμ3 hs_pos), ?_, ?_, ?_⟩
      · have hs_ne : s ≠ 0 := ne_of_gt hs_pos
        dsimp [ν₁, ν₂, ν₃, s]
        field_simp [hs_ne]
        have heq : γ₁ * α₂ * (μ₂ + μ₃) + (γ₁ * α₁ * (μ₂ + μ₃) + γ₂ * μ₂) + γ₂ * μ₃ =
            (γ₁ * (α₁ + α₂) + γ₂) * (μ₂ + μ₃) := by ring
        rw [heq, hαsum, mul_one, hγsum, one_mul]
      · have hs_ne : s ≠ 0 := ne_of_gt hs_pos
        rw [ha_th.1]
        dsimp [ν₁, ν₂, ν₃, t, h, s]
        field_simp [hs_ne]; ring
      · have hs_ne : s ≠ 0 := ne_of_gt hs_pos
        rw [ha_th.2]
        dsimp [ν₁, ν₂, ν₃, t, h, s]
        field_simp [hs_ne]; ring
    exact (mem_uCone_iff_inOpenTri a b c x).mpr ha_tri
  · -- τ > 1: paths w - b - t and w - c - x - t enclose wt
    have hτ_pos : 0 < τ := by linarith
    have hwt_ne : w ≠ t := by
      intro hwt
      apply hwa_ne
      have h1 : w.1 - w.1 = τ * (a.1 - w.1) := hwt ▸ hτ1
      have h2 : w.2 - w.2 = τ * (a.2 - w.2) := hwt ▸ hτ2
      ext <;> nlinarith
    have hwt_orient : ∀ p : ℝ × ℝ, orient2D w t p = τ * orient2D w a p := by
      intro p
      unfold orient2D
      have ht1 : t.1 - w.1 = τ * (a.1 - w.1) := hτ1
      have ht2 : t.2 - w.2 = τ * (a.2 - w.2) := hτ2
      rw [ht1, ht2]
      ring
    have hbt : Sees P b t := sees_of_mem_segment_left (sees_symm hxb) ht_seg
    have hxt : Sees P x t := sees_of_mem_segment_left hxb ht_seg'
    have hwt_sees : Sees P w t := by
      refine two_path_enclosure_either hEnc hwt_ne
        (isPolygonalPathIn_three hwb hbt)
        (isPolygonalPathIn_four hwc (sees_symm hxc) hxt)
        (Or.inr ⟨interiorOnRight_three ?_, interiorOnLeft_four ?_ ?_⟩)
      · rw [hwt_orient]; exact mul_neg_of_pos_of_neg hτ_pos hwab
      · rw [hwt_orient]; exact mul_pos hτ_pos hwac
      · rw [hwt_orient]; exact mul_pos hτ_pos hwax
    exfalso
    apply hnwa
    refine sees_of_mem_segment_left hwt_sees ?_
    rw [segment_eq_image]
    refine ⟨1 / τ, ⟨div_nonneg zero_le_one (le_of_lt hτ_pos), (div_le_one hτ_pos).mpr (le_of_lt hτ_gt)⟩, ?_⟩
    have hτ_ne : τ ≠ 0 := ne_of_gt hτ_pos
    ext <;> simp [smul_eq_mul]
    · have : t.1 = w.1 + τ * (a.1 - w.1) := by linarith
      rw [this]; field_simp [hτ_ne]; ring
    · have : t.2 = w.2 + τ * (a.2 - w.2) := by linarith
      rw [this]; field_simp [hτ_ne]; ring

private def reflectY (p : ℝ × ℝ) : ℝ × ℝ := (p.1, -p.2)

private lemma reflectY_invol (p : ℝ × ℝ) : reflectY (reflectY p) = p := by
  ext <;> simp [reflectY]

private lemma orient2D_reflectY (a b c : ℝ × ℝ) :
    orient2D (reflectY a) (reflectY b) (reflectY c) = -orient2D a b c := by
  unfold orient2D reflectY; ring

private lemma sees_reflectY_iff {P : Set (ℝ × ℝ)} {x y : ℝ × ℝ} :
    Sees (reflectY '' P) (reflectY x) (reflectY y) ↔ Sees P x y := by
  have himg : segment ℝ (reflectY x) (reflectY y) = reflectY '' segment ℝ x y := by
    ext p
    simp only [segment_eq_image, Set.mem_image]
    constructor
    · rintro ⟨t, ht, rfl⟩
      refine ⟨(1 - t) • x + t • y, ⟨t, ht, rfl⟩, ?_⟩
      ext
      · simp [reflectY, smul_eq_mul]
      · simp [reflectY, smul_eq_mul]; ring
    · rintro ⟨q, ⟨t, ht, rfl⟩, rfl⟩
      refine ⟨t, ht, ?_⟩
      ext
      · simp [reflectY, smul_eq_mul]
      · simp [reflectY, smul_eq_mul]; ring
  constructor
  · intro h p hp
    have hmem : reflectY p ∈ reflectY '' P := h (himg ▸ ⟨p, hp, rfl⟩)
    rcases hmem with ⟨q, hq, hqp⟩
    have : q = p := by
      have := congrArg reflectY hqp
      simpa [reflectY_invol] using this
    rwa [← this]
  · intro h p hp
    rw [himg] at hp
    rcases hp with ⟨q, hq, rfl⟩
    exact ⟨q, h hq, rfl⟩

private lemma enclosureDomain_reflectY {P : Set (ℝ × ℝ)} (hEnc : EnclosureDomain P) :
    EnclosureDomain (reflectY '' P) := by
  constructor
  · intro x hx y hy z hz hxy hyz hxz
    rcases hx with ⟨x', _, rfl⟩
    rcases hy with ⟨y', _, rfl⟩
    rcases hz with ⟨z', _, rfl⟩
    have hxy' : Sees P x' y' := sees_reflectY_iff.mp hxy
    have hyz' : Sees P y' z' := sees_reflectY_iff.mp hyz
    have hxz' : Sees P x' z' := sees_reflectY_iff.mp hxz
    have htri := hEnc.triangle_enclosure x' (sees_mem_left hxy') y' (sees_mem_right hxy')
      z' (sees_mem_right hxz') hxy' hyz' hxz'
    intro p hp
    rw [← inClosedTri_iff_mem_convexHull] at hp
    rcases hp with ⟨μ₁, μ₂, μ₃, h1, h2, h3, hsum, hp1, hp2⟩
    refine ⟨(μ₁ * x'.1 + μ₂ * y'.1 + μ₃ * z'.1, μ₁ * x'.2 + μ₂ * y'.2 + μ₃ * z'.2), ?_, ?_⟩
    · apply htri
      rw [← inClosedTri_iff_mem_convexHull]
      exact ⟨μ₁, μ₂, μ₃, h1, h2, h3, hsum, rfl, rfl⟩
    · ext <;> simp only [reflectY] at hp1 hp2 ⊢ <;> linarith
  · intro s t π₁ π₂ hst hp₁ hp₂ hL hR
    have hst' : reflectY s ≠ reflectY t := fun h => hst (by
      have := congrArg reflectY h; simpa [reflectY_invol] using this)
    have hpath : ∀ {π : List (ℝ × ℝ)}, IsPolygonalPathIn (reflectY '' P) s t π →
        IsPolygonalPathIn P (reflectY s) (reflectY t) (π.map reflectY) := by
      intro π hπ
      rcases hπ with ⟨hne, hhead, hlast, hmem, hchain⟩
      refine ⟨by simp [hne], ?_, ?_, ?_, ?_⟩
      · cases π with | nil => contradiction | cons a l => simpa [List.head_cons] using congrArg reflectY hhead
      · rw [List.getLast_map]; exact congrArg reflectY hlast
      · intro x hx
        rcases List.mem_map.mp hx with ⟨y, hy, rfl⟩
        rcases hmem y hy with ⟨z, hz, hyz⟩
        have : z = reflectY y := by
          have := congrArg reflectY hyz
          simpa [reflectY_invol] using this
        rwa [← this]
      · rw [List.isChain_map]
        exact hchain.imp (fun u v huv => sees_reflectY_iff.mp (by simpa [reflectY_invol] using huv))
    have hL' : InteriorOnRight (reflectY s) (reflectY t) (π₁.map reflectY) := by
      refine ⟨by simpa using hL.1, fun k hk hk0 hk1 => ?_⟩
      simp only [List.length_map] at hk hk1
      rw [List.getElem_map, orient2D_reflectY]
      exact neg_lt_zero.mpr (hL.2 k hk hk0 hk1)
    have hR' : InteriorOnLeft (reflectY s) (reflectY t) (π₂.map reflectY) := by
      refine ⟨by simpa using hR.1, fun k hk hk0 hk1 => ?_⟩
      simp only [List.length_map] at hk hk1
      rw [List.getElem_map, orient2D_reflectY]
      exact neg_pos.mpr (hR.2 k hk hk0 hk1)
    have hsees := hEnc.two_path_enclosure (reflectY s) (reflectY t) (π₂.map reflectY) (π₁.map reflectY)
      hst' (hpath hp₂) (hpath hp₁) hR' hL'
    rw [← reflectY_invol s, ← reflectY_invol t]
    exact sees_reflectY_iff.mpr hsees

private lemma inOpenTri_reflectY {p q r z : ℝ × ℝ} (h : InOpenTri p q r z) :
    InOpenTri (reflectY p) (reflectY q) (reflectY r) (reflectY z) := by
  rcases h with ⟨μ₁, μ₂, μ₃, h1, h2, h3, hsum, hz1, hz2⟩
  exact ⟨μ₁, μ₂, μ₃, h1, h2, h3, hsum, hz1, by simp [reflectY]; linarith⟩

private lemma uCone_reflectY {a b c x : ℝ × ℝ}
    (h : reflectY x ∈ UCone (reflectY a) (reflectY b) (reflectY c)) :
    x ∈ UCone a b c := by
  rw [mem_uCone_iff_inOpenTri] at h ⊢
  simpa [reflectY_invol] using inOpenTri_reflectY h

/-- Lemma 2.6 (`Cone`, `upper_9.tex` lines 223–231): if `w` sees `b, c` and misses `a`,
    `a ∈ interior Δ(w, b, c)`, and `x ∈ P` off lines `ab, ac, wa` sees `b, c`, then `x ∈ U(a; b, c)`. -/
theorem cone {P : Set (ℝ × ℝ)} (hEnc : EnclosureDomain P)
    {a b c w x : ℝ × ℝ}
    (hwb : Sees P w b) (hwc : Sees P w c) (hnwa : ¬ Sees P w a)
    (ha : InOpenTri w b c a)
    (hxb : Sees P x b) (hxc : Sees P x c)
    (hxab : orient2D a b x ≠ 0) (hxac : orient2D a c x ≠ 0) (hxwa : orient2D w a x ≠ 0) :
    x ∈ UCone a b c := by
  have hwbc_ne : orient2D w b c ≠ 0 := by
    intro hcol
    exact hnwa (sees_of_collinear_inOpenTri hwb hwc ha hcol)
  have hwa_bc : orient2D w a b * orient2D w a c < 0 := by
    rcases ha with ⟨μ₁, μ₂, μ₃, h1, h2, h3, hsum, ha1, ha2⟩
    have hμ1 : μ₁ = 1 - μ₂ - μ₃ := by linarith
    have hwab_eq : orient2D w a b = μ₃ * orient2D w c b := by
      unfold orient2D; rw [ha1, ha2, hμ1]; ring
    have hwac_eq : orient2D w a c = μ₂ * orient2D w b c := by
      unfold orient2D; rw [ha1, ha2, hμ1]; ring
    rw [hwab_eq, hwac_eq, orient2D_swap23 w c b]
    have hsq : 0 < (orient2D w c b) ^ 2 := by
      have hne' : orient2D w c b ≠ 0 := by
        intro h0
        apply hwbc_ne
        rw [orient2D_swap23, h0, neg_zero]
      exact sq_pos_of_ne_zero hne'
    nlinarith [mul_pos h2 h3, hsq]
  have cone_pos : ∀ {P' : Set (ℝ × ℝ)} (_ : EnclosureDomain P')
      {a' b' c' w' x' : ℝ × ℝ},
      Sees P' w' b' → Sees P' w' c' → ¬ Sees P' w' a' → InOpenTri w' b' c' a' →
      Sees P' x' b' → Sees P' x' c' →
      orient2D a' b' x' ≠ 0 → orient2D a' c' x' ≠ 0 →
      orient2D w' a' b' * orient2D w' a' c' < 0 → 0 < orient2D w' a' x' →
      x' ∈ UCone a' b' c' := by
    intro P' hEnc' a' b' c' w' x' hwb' hwc' hnwa' ha' hxb' hxc' hxab' hxac' hmul' hwax'
    rcases lt_trichotomy (orient2D w' a' b') 0 with hwab_neg | hwab_0 | hwab_pos
    · have hwac_pos : 0 < orient2D w' a' c' := by nlinarith
      exact cone_aux hEnc' hwb' hwc' hnwa' ha' hxb' hxc' hwab_neg hwac_pos hwax' hxab'
    · exact False.elim (by rw [hwab_0, zero_mul] at hmul'; exact lt_irrefl 0 hmul')
    · have hwac_neg : orient2D w' a' c' < 0 := by nlinarith
      rw [uCone_symm]
      exact cone_aux hEnc' hwc' hwb' hnwa' (inOpenTri_perm_23 ha') hxc' hxb' hwac_neg hwab_pos hwax' hxac'
  rcases lt_or_gt_of_ne hxwa with hwax_neg | hwax_pos
  · apply uCone_reflectY
    apply cone_pos (enclosureDomain_reflectY hEnc)
      (sees_reflectY_iff.mpr hwb) (sees_reflectY_iff.mpr hwc)
      (fun h => hnwa (sees_reflectY_iff.mp h)) (inOpenTri_reflectY ha)
      (sees_reflectY_iff.mpr hxb) (sees_reflectY_iff.mpr hxc)
      (by rw [orient2D_reflectY]; exact neg_ne_zero.mpr hxab)
      (by rw [orient2D_reflectY]; exact neg_ne_zero.mpr hxac)
      (by rw [orient2D_reflectY, orient2D_reflectY]; linarith)
      (by rw [orient2D_reflectY]; exact neg_pos.mpr hwax_neg)
  · exact cone_pos hEnc hwb hwc hnwa ha hxb hxc hxab hxac hwa_bc hwax_pos

/-- Corollary of `cone` directly under `ShatteredSimplePolygon`. -/
theorem cone_of_shattered {n : ℕ} {P : Set (ℝ × ℝ)} {S : Fin n → ℝ × ℝ}
    {w : Finset (Fin n) → ℝ × ℝ} (hP : ShatteredSimplePolygon P S w)
    {a b c w₀ x : ℝ × ℝ}
    (hwb : Sees P w₀ b) (hwc : Sees P w₀ c) (hnwa : ¬ Sees P w₀ a)
    (ha : InOpenTri w₀ b c a) (hxb : Sees P x b) (hxc : Sees P x c)
    (hxab : orient2D a b x ≠ 0) (hxac : orient2D a c x ≠ 0) (hxwa : orient2D w₀ a x ≠ 0) :
    x ∈ UCone a b c :=
  cone hP.toEnclosureDomain hwb hwc hnwa ha hxb hxc hxab hxac hxwa

private lemma cramer_2d (a u₁ u₂ z : ℝ × ℝ) (hd : orient2D a u₁ u₂ ≠ 0) :
    z.1 - a.1 = (orient2D a z u₂ / orient2D a u₁ u₂) * (u₁.1 - a.1) +
        (orient2D a u₁ z / orient2D a u₁ u₂) * (u₂.1 - a.1) ∧
    z.2 - a.2 = (orient2D a z u₂ / orient2D a u₁ u₂) * (u₁.2 - a.2) +
        (orient2D a u₁ z / orient2D a u₁ u₂) * (u₂.2 - a.2) := by
  have h1 : orient2D a u₁ u₂ * (z.1 - a.1) =
      orient2D a z u₂ * (u₁.1 - a.1) + orient2D a u₁ z * (u₂.1 - a.1) := by
    unfold orient2D; ring
  have h2 : orient2D a u₁ u₂ * (z.2 - a.2) =
      orient2D a z u₂ * (u₁.2 - a.2) + orient2D a u₁ z * (u₂.2 - a.2) := by
    unfold orient2D; ring
  constructor
  · have heq1 : orient2D a u₁ u₂ * (orient2D a z u₂ / orient2D a u₁ u₂ * (u₁.1 - a.1) +
        orient2D a u₁ z / orient2D a u₁ u₂ * (u₂.1 - a.1)) =
        orient2D a z u₂ * (u₁.1 - a.1) + orient2D a u₁ z * (u₂.1 - a.1) := by
      field_simp [hd]
    exact mul_left_cancel₀ hd (h1.trans heq1.symm)
  · have heq2 : orient2D a u₁ u₂ * (orient2D a z u₂ / orient2D a u₁ u₂ * (u₁.2 - a.2) +
        orient2D a u₁ z / orient2D a u₁ u₂ * (u₂.2 - a.2)) =
        orient2D a z u₂ * (u₁.2 - a.2) + orient2D a u₁ z * (u₂.2 - a.2) := by
      field_simp [hd]
    exact mul_left_cancel₀ hd (h2.trans heq2.symm)

/-- Lemma 2.7 (`Wedge extraction`, `upper_9.tex` lines 233–241):
    For distinct `ia, ib, ic`, `W' ⊆ W({ib, ic})`, and a wedge `U` with apex `S ia` whose lines
    through `S ia` separate `S ib` from `S ic`, if every witness of `W'` seeing `S ia` lies in `U`,
    then `S ia` has a wedge test `R` on `W'` (with `R.y = S ia`). -/
theorem wedge_extraction {n : ℕ} {P : Set (ℝ × ℝ)} {S : Fin n → ℝ × ℝ}
    {w : Finset (Fin n) → ℝ × ℝ}
    (hP : ShatteredSimplePolygon P S w)
    {ia ib ic : Fin n} (_hab : ia ≠ ib) (_hbc : ib ≠ ic) (_hac : ia ≠ ic)
    {W' : Set (ℝ × ℝ)} (hW'_sub : W' ⊆ WitnessSet {ib, ic} ∅ w)
    (U : OpenWedge) (hUy : U.y = S ia)
    (hU_sep : ∀ z : ℝ × ℝ, U.MemOpen z →
      orient2D (S ia) z (S ib) * orient2D (S ia) z (S ic) < 0)
    (hX_in_U : ∀ x ∈ W', Sees P x (S ia) → U.MemOpen x) :
    ∃ R : OpenWedge, R.y = S ia ∧ IsWedgeTest P W' (S ia) R := by
  let a := S ia
  let b := S ib
  let c := S ic
  let W'_idx : Finset (Finset (Fin n)) := Finset.univ.filter (fun T => w T ∈ W')
  let X : Finset (Finset (Fin n)) := W'_idx.filter (fun T => ia ∈ T)
  have hW'_mem : ∀ x ∈ W', ∃ T ∈ W'_idx, x = w T ∧ ib ∈ T ∧ ic ∈ T := by
    intro x hx
    obtain ⟨T, hsub, _, rfl⟩ := hW'_sub hx
    refine ⟨T, Finset.mem_filter.mpr ⟨Finset.mem_univ T, hx⟩, rfl, ?_, ?_⟩
    · exact hsub (by simp)
    · exact hsub (by simp)
  by_cases hX : X.Nonempty
  · -- Case 2: X is nonempty; pick extreme rays in U
    let L₁ : ℝ × ℝ → ℝ := fun p => U.u₁.1 * (p.1 - a.1) + U.u₁.2 * (p.2 - a.2)
    let L₂ : ℝ × ℝ → ℝ := fun p => U.u₂.1 * (p.1 - a.1) + U.u₂.2 * (p.2 - a.2)
    let detU : ℝ := U.u₁.1 * U.u₂.2 - U.u₁.2 * U.u₂.1
    have hdetU : 0 < detU := U.h_nondeg
    have hL_orient : ∀ p q : ℝ × ℝ, L₁ p * L₂ q - L₂ p * L₁ q = detU * orient2D a p q := by
      intro p q
      dsimp [L₁, L₂, detU, orient2D]
      ring
    have hX_U : ∀ T ∈ X, U.MemOpen (w T) := by
      intro T hT
      have hTf := Finset.mem_filter.mp hT
      have hTidx := Finset.mem_filter.mp hTf.1
      exact hX_in_U (w T) hTidx.2 ((hP.shatters T ia).mpr hTf.2)
    have hX_L1_pos : ∀ T ∈ X, 0 < L₁ (w T) := by
      intro T hT
      have hmem := hX_U T hT
      dsimp [OpenWedge.MemOpen] at hmem
      rw [hUy] at hmem
      exact hmem.1
    have hX_L2_pos : ∀ T ∈ X, 0 < L₂ (w T) := by
      intro T hT
      have hmem := hX_U T hT
      dsimp [OpenWedge.MemOpen] at hmem
      rw [hUy] at hmem
      exact hmem.2
    let r : Finset (Fin n) → ℝ := fun T => L₂ (w T) / L₁ (w T)
    obtain ⟨T₁, hT1_mem, hT1_min⟩ := Finset.exists_min_image X r hX
    obtain ⟨T₂, hT2_mem, hT2_max⟩ := Finset.exists_max_image X r hX
    have hT1_ne : T₁.Nonempty := ⟨ia, (Finset.mem_filter.mp hT1_mem).2⟩
    have hT2_ne : T₂.Nonempty := ⟨ia, (Finset.mem_filter.mp hT2_mem).2⟩
    have hT1_bc : ib ∈ T₁ ∧ ic ∈ T₁ := by
      have h1 := (Finset.mem_filter.mp (Finset.mem_filter.mp hT1_mem).1).2
      obtain ⟨T', _, heq, hbc'⟩ := hW'_mem (w T₁) h1
      have : T₁ = T' := hP.w_inj heq
      subst this; exact hbc'
    have hT2_bc : ib ∈ T₂ ∧ ic ∈ T₂ := by
      have h2 := (Finset.mem_filter.mp (Finset.mem_filter.mp hT2_mem).1).2
      obtain ⟨T', _, heq, hbc'⟩ := hW'_mem (w T₂) h2
      have : T₂ = T' := hP.w_inj heq
      subst this; exact hbc'
    obtain ⟨ε₁, hε1, hball1⟩ := hP.open_vis_nbhd T₁ hT1_ne
    obtain ⟨ε₂, hε2, hball2⟩ := hP.open_vis_nbhd T₂ hT2_ne
    let v₂ : ℝ × ℝ := (-U.u₁.2, U.u₁.1)
    let Mv : ℝ := |v₂.1| + |v₂.2| + 1
    have hMv : 0 < Mv := by positivity
    have hL1_T1 := hX_L1_pos T₁ hT1_mem
    have hL2_T1 := hX_L2_pos T₁ hT1_mem
    have hL1_T2 := hX_L1_pos T₂ hT2_mem
    have hL2_T2 := hX_L2_pos T₂ hT2_mem
    let δ₁_max : ℝ := min (L₂ (w T₁) / detU) (ε₁ / (2 * Mv))
    have hδ₁_max : 0 < δ₁_max := lt_min (div_pos hL2_T1 hdetU) (div_pos hε1 (by linarith))
    let bad₁ : Finset ℝ := W'_idx.image (fun T =>
      (L₂ (w T₁) * L₁ (w T) - L₁ (w T₁) * L₂ (w T)) / (detU * L₁ (w T)))
    obtain ⟨δ₁, hδ1_mem⟩ := (Set.Ioo_infinite hδ₁_max).sdiff bad₁.finite_toSet |>.nonempty
    have hδ1_pos : 0 < δ₁ := hδ1_mem.1.1
    have hδ1_lt : δ₁ < δ₁_max := hδ1_mem.1.2
    have hδ1_nb : δ₁ ∉ bad₁ := by simpa using hδ1_mem.2
    let u₁ : ℝ × ℝ := ((w T₁).1 - δ₁ * v₂.1, (w T₁).2 - δ₁ * v₂.2)
    have hu1_L1 : L₁ u₁ = L₁ (w T₁) := by dsimp [L₁, u₁, v₂]; ring
    have hu1_L2 : L₂ u₁ = L₂ (w T₁) - δ₁ * detU := by dsimp [L₂, u₁, v₂, detU]; ring
    have hu1_in_U : U.MemOpen u₁ := by
      dsimp [OpenWedge.MemOpen]
      rw [hUy]
      refine ⟨by change 0 < L₁ u₁; rw [hu1_L1]; exact hL1_T1, ?_⟩
      change 0 < L₂ u₁; rw [hu1_L2]
      have h1 : δ₁ < L₂ (w T₁) / detU := lt_of_lt_of_le hδ1_lt (min_le_left _ _)
      have h2 := (lt_div_iff₀ hdetU).mp h1
      linarith
    have hu1_dist : dist u₁ (w T₁) < ε₁ := by
      rw [Prod.dist_eq]
      simp only [Real.dist_eq]
      have h1 : |u₁.1 - (w T₁).1| < ε₁ := by
        have : u₁.1 - (w T₁).1 = -(δ₁ * v₂.1) := by dsimp [u₁]; ring
        rw [this, abs_neg, abs_mul, abs_of_pos hδ1_pos]
        have hv1 : |v₂.1| ≤ Mv := by have := abs_nonneg v₂.2; dsimp [Mv]; linarith
        have hlt : δ₁ < ε₁ / (2 * Mv) := lt_of_lt_of_le hδ1_lt (min_le_right _ _)
        calc δ₁ * |v₂.1| ≤ δ₁ * Mv := mul_le_mul_of_nonneg_left hv1 (le_of_lt hδ1_pos)
          _ < (ε₁ / (2 * Mv)) * Mv := mul_lt_mul_of_pos_right hlt hMv
          _ = ε₁ / 2 := by field_simp [ne_of_gt hMv]
          _ < ε₁ := by linarith
      have h2 : |u₁.2 - (w T₁).2| < ε₁ := by
        have : u₁.2 - (w T₁).2 = -(δ₁ * v₂.2) := by dsimp [u₁]; ring
        rw [this, abs_neg, abs_mul, abs_of_pos hδ1_pos]
        have hv2 : |v₂.2| ≤ Mv := by have := abs_nonneg v₂.1; dsimp [Mv]; linarith
        have hlt : δ₁ < ε₁ / (2 * Mv) := lt_of_lt_of_le hδ1_lt (min_le_right _ _)
        calc δ₁ * |v₂.2| ≤ δ₁ * Mv := mul_le_mul_of_nonneg_left hv2 (le_of_lt hδ1_pos)
          _ < (ε₁ / (2 * Mv)) * Mv := mul_lt_mul_of_pos_right hlt hMv
          _ = ε₁ / 2 := by field_simp [ne_of_gt hMv]
          _ < ε₁ := by linarith
      exact max_lt h1 h2
    have hu1_vis : Sees P u₁ a ∧ Sees P u₁ b ∧ Sees P u₁ c := by
      have h := (hball1 u₁ hu1_dist).2
      exact ⟨h ia (Finset.mem_filter.mp hT1_mem).2, h ib hT1_bc.1, h ic hT1_bc.2⟩
    have hu1_not_col : ∀ T ∈ W'_idx, orient2D a u₁ (w T) ≠ 0 := by
      intro T hT h0
      have hmul : detU * orient2D a u₁ (w T) = 0 := by rw [h0, mul_zero]
      rw [← hL_orient u₁ (w T), hu1_L1, hu1_L2] at hmul
      by_cases hL1T : L₁ (w T) = 0
      · have hL2T_0 : L₂ (w T) = 0 := by
          have : L₁ (w T₁) * L₂ (w T) = 0 := by rw [hL1T] at hmul; linarith
          exact (mul_eq_zero.mp this).resolve_left (ne_of_gt hL1_T1)
        have hwa : w T = a := by
          have h1 : U.u₁.1 * ((w T).1 - a.1) + U.u₁.2 * ((w T).2 - a.2) = 0 := hL1T
          have h2 : U.u₂.1 * ((w T).1 - a.1) + U.u₂.2 * ((w T).2 - a.2) = 0 := hL2T_0
          have hdet_ne : detU ≠ 0 := ne_of_gt hdetU
          have hx : detU * ((w T).1 - a.1) = 0 := by
            dsimp [detU]; linear_combination U.u₂.2 * h1 - U.u₁.2 * h2
          have hy : detU * ((w T).2 - a.2) = 0 := by
            dsimp [detU]; linear_combination -U.u₂.1 * h1 + U.u₁.1 * h2
          have hx0 : (w T).1 - a.1 = 0 := (mul_eq_zero.mp hx).resolve_left hdet_ne
          have hy0 : (w T).2 - a.2 = 0 := (mul_eq_zero.mp hy).resolve_left hdet_ne
          ext <;> linarith
        exact hP.s_ne_w ia T hwa.symm
      · apply hδ1_nb
        refine Finset.mem_image.mpr ⟨T, hT, ?_⟩
        have hden_ne : detU * L₁ (w T) ≠ 0 := mul_ne_zero (ne_of_gt hdetU) hL1T
        field_simp [hden_ne]
        linarith
    let δ₂_max : ℝ := ε₂ / (2 * Mv)
    have hδ₂_max : 0 < δ₂_max := div_pos hε2 (by linarith)
    let bad₂ : Finset ℝ := W'_idx.image (fun T =>
      (L₁ (w T₂) * L₂ (w T) - L₂ (w T₂) * L₁ (w T)) / (detU * L₁ (w T)))
    obtain ⟨δ₂, hδ2_mem⟩ := (Set.Ioo_infinite hδ₂_max).sdiff bad₂.finite_toSet |>.nonempty
    have hδ2_pos : 0 < δ₂ := hδ2_mem.1.1
    have hδ2_lt : δ₂ < δ₂_max := hδ2_mem.1.2
    have hδ2_nb : δ₂ ∉ bad₂ := by simpa using hδ2_mem.2
    let u₂ : ℝ × ℝ := ((w T₂).1 + δ₂ * v₂.1, (w T₂).2 + δ₂ * v₂.2)
    have hu2_L1 : L₁ u₂ = L₁ (w T₂) := by dsimp [L₁, u₂, v₂]; ring
    have hu2_L2 : L₂ u₂ = L₂ (w T₂) + δ₂ * detU := by dsimp [L₂, u₂, v₂, detU]; ring
    have hu2_in_U : U.MemOpen u₂ := by
      dsimp [OpenWedge.MemOpen]
      rw [hUy]
      refine ⟨by change 0 < L₁ u₂; rw [hu2_L1]; exact hL1_T2, ?_⟩
      change 0 < L₂ u₂; rw [hu2_L2]
      nlinarith
    have hu2_dist : dist u₂ (w T₂) < ε₂ := by
      rw [Prod.dist_eq]
      simp only [Real.dist_eq]
      have h1 : |u₂.1 - (w T₂).1| < ε₂ := by
        have : u₂.1 - (w T₂).1 = δ₂ * v₂.1 := by dsimp [u₂]; ring
        rw [this, abs_mul, abs_of_pos hδ2_pos]
        have hv1 : |v₂.1| ≤ Mv := by have := abs_nonneg v₂.2; dsimp [Mv]; linarith
        calc δ₂ * |v₂.1| ≤ δ₂ * Mv := mul_le_mul_of_nonneg_left hv1 (le_of_lt hδ2_pos)
          _ < (ε₂ / (2 * Mv)) * Mv := mul_lt_mul_of_pos_right hδ2_lt hMv
          _ = ε₂ / 2 := by field_simp [ne_of_gt hMv]
          _ < ε₂ := by linarith
      have h2 : |u₂.2 - (w T₂).2| < ε₂ := by
        have : u₂.2 - (w T₂).2 = δ₂ * v₂.2 := by dsimp [u₂]; ring
        rw [this, abs_mul, abs_of_pos hδ2_pos]
        have hv2 : |v₂.2| ≤ Mv := by have := abs_nonneg v₂.1; dsimp [Mv]; linarith
        calc δ₂ * |v₂.2| ≤ δ₂ * Mv := mul_le_mul_of_nonneg_left hv2 (le_of_lt hδ2_pos)
          _ < (ε₂ / (2 * Mv)) * Mv := mul_lt_mul_of_pos_right hδ2_lt hMv
          _ = ε₂ / 2 := by field_simp [ne_of_gt hMv]
          _ < ε₂ := by linarith
      exact max_lt h1 h2
    have hu2_vis : Sees P u₂ a ∧ Sees P u₂ b ∧ Sees P u₂ c := by
      have h := (hball2 u₂ hu2_dist).2
      exact ⟨h ia (Finset.mem_filter.mp hT2_mem).2, h ib hT2_bc.1, h ic hT2_bc.2⟩
    have hu2_not_col : ∀ T ∈ W'_idx, orient2D a (w T) u₂ ≠ 0 := by
      intro T hT h0
      have hmul : detU * orient2D a (w T) u₂ = 0 := by rw [h0, mul_zero]
      rw [← hL_orient (w T) u₂, hu2_L1, hu2_L2] at hmul
      by_cases hL1T : L₁ (w T) = 0
      · have hL2T_0 : L₂ (w T) = 0 := by
          have : -L₂ (w T) * L₁ (w T₂) = 0 := by rw [hL1T] at hmul; linarith
          have : L₂ (w T) * L₁ (w T₂) = 0 := by linarith
          exact (mul_eq_zero.mp this).resolve_right (ne_of_gt hL1_T2)
        have hwa : w T = a := by
          have h1 : U.u₁.1 * ((w T).1 - a.1) + U.u₁.2 * ((w T).2 - a.2) = 0 := hL1T
          have h2 : U.u₂.1 * ((w T).1 - a.1) + U.u₂.2 * ((w T).2 - a.2) = 0 := hL2T_0
          have hdet_ne : detU ≠ 0 := ne_of_gt hdetU
          have hx : detU * ((w T).1 - a.1) = 0 := by
            dsimp [detU]; linear_combination U.u₂.2 * h1 - U.u₁.2 * h2
          have hy : detU * ((w T).2 - a.2) = 0 := by
            dsimp [detU]; linear_combination -U.u₂.1 * h1 + U.u₁.1 * h2
          have hx0 : (w T).1 - a.1 = 0 := (mul_eq_zero.mp hx).resolve_left hdet_ne
          have hy0 : (w T).2 - a.2 = 0 := (mul_eq_zero.mp hy).resolve_left hdet_ne
          ext <;> linarith
        exact hP.s_ne_w ia T hwa.symm
      · apply hδ2_nb
        refine Finset.mem_image.mpr ⟨T, hT, ?_⟩
        have hden_ne : detU * L₁ (w T) ≠ 0 := mul_ne_zero (ne_of_gt hdetU) hL1T
        field_simp [hden_ne]
        linarith
    have hu1_u2_pos : 0 < orient2D a u₁ u₂ := by
      have hT12 : L₂ (w T₁) * L₁ (w T₂) ≤ L₂ (w T₂) * L₁ (w T₁) := by
        have hle : r T₁ ≤ r T₂ := hT1_min T₂ hT2_mem
        dsimp [r] at hle
        exact (div_le_div_iff₀ hL1_T1 hL1_T2).mp hle
      have hmul : 0 < detU * orient2D a u₁ u₂ := by
        rw [← hL_orient u₁ u₂, hu1_L1, hu1_L2, hu2_L1, hu2_L2]
        have hid : L₁ (w T₁) * (L₂ (w T₂) + δ₂ * detU) - (L₂ (w T₁) - δ₁ * detU) * L₁ (w T₂) =
            (L₁ (w T₁) * L₂ (w T₂) - L₂ (w T₁) * L₁ (w T₂)) +
            δ₂ * detU * L₁ (w T₁) + δ₁ * detU * L₁ (w T₂) := by ring
        rw [hid]
        have p1 : 0 < δ₂ * detU * L₁ (w T₁) := mul_pos (mul_pos hδ2_pos hdetU) hL1_T1
        have p2 : 0 < δ₁ * detU * L₁ (w T₂) := mul_pos (mul_pos hδ1_pos hdetU) hL1_T2
        linarith
      exact pos_of_mul_pos_right hmul (le_of_lt hdetU)
    let R : OpenWedge :=
      { y := a
        u₁ := (u₂.2 - a.2, -(u₂.1 - a.1))
        u₂ := (-(u₁.2 - a.2), u₁.1 - a.1)
        h_nondeg := by
          unfold orient2D at hu1_u2_pos
          linarith [show (u₂.2 - a.2) * (u₁.1 - a.1) - (-(u₂.1 - a.1)) * (-(u₁.2 - a.2)) =
            (u₁.1 - a.1) * (u₂.2 - a.2) - (u₁.2 - a.2) * (u₂.1 - a.1) by ring] }
    have hR_open_iff : ∀ z : ℝ × ℝ, R.MemOpen z ↔ 0 < orient2D a z u₂ ∧ 0 < orient2D a u₁ z := by
      intro z
      unfold OpenWedge.MemOpen orient2D
      dsimp [R]
      constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨by linarith, by linarith⟩
    have hR_ext_iff : ∀ z : ℝ × ℝ, R.MemExt z ↔ orient2D a z u₂ < 0 ∨ orient2D a u₁ z < 0 := by
      intro z
      unfold OpenWedge.MemExt orient2D
      dsimp [R]
      constructor
      · rintro (h1 | h2)
        · left; linarith
        · right; linarith
      · rintro (h1 | h2)
        · left; linarith
        · right; linarith
    have hR_sub_U : ∀ z : ℝ × ℝ, R.MemOpen z → U.MemOpen z := by
      intro z hz
      rw [hR_open_iff] at hz
      have hα : 0 < orient2D a z u₂ / orient2D a u₁ u₂ := div_pos hz.1 hu1_u2_pos
      have hβ : 0 < orient2D a u₁ z / orient2D a u₁ u₂ := div_pos hz.2 hu1_u2_pos
      obtain ⟨hz1, hz2⟩ := cramer_2d a u₁ u₂ z (ne_of_gt hu1_u2_pos)
      have hL1z : L₁ z = (orient2D a z u₂ / orient2D a u₁ u₂) * L₁ u₁ +
          (orient2D a u₁ z / orient2D a u₁ u₂) * L₁ u₂ := by
        dsimp [L₁]; rw [hz1, hz2]; ring
      have hL2z : L₂ z = (orient2D a z u₂ / orient2D a u₁ u₂) * L₂ u₁ +
          (orient2D a u₁ z / orient2D a u₁ u₂) * L₂ u₂ := by
        dsimp [L₂]; rw [hz1, hz2]; ring
      have hu1_L := hu1_in_U; have hu2_L := hu2_in_U
      dsimp [OpenWedge.MemOpen] at hu1_L hu2_L
      rw [hUy] at hu1_L hu2_L
      have hu1_1 : 0 < L₁ u₁ := hu1_L.1
      have hu1_2 : 0 < L₂ u₁ := hu1_L.2
      have hu2_1 : 0 < L₁ u₂ := hu2_L.1
      have hu2_2 : 0 < L₂ u₂ := hu2_L.2
      dsimp [OpenWedge.MemOpen]
      rw [hUy]
      exact ⟨by change 0 < L₁ z; rw [hL1z]; exact add_pos (mul_pos hα hu1_1) (mul_pos hβ hu2_1),
             by change 0 < L₂ z; rw [hL2z]; exact add_pos (mul_pos hα hu1_2) (mul_pos hβ hu2_2)⟩
    refine ⟨R, rfl, fun x hx => ?_⟩
    obtain ⟨T, hTidx, rfl, hTib, hTic⟩ := hW'_mem x hx
    have hnot1 := hu1_not_col T hTidx
    have hnot2 := hu2_not_col T hTidx
    have hdec : R.MemOpen (w T) ∨ R.MemExt (w T) := by
      rw [hR_open_iff, hR_ext_iff]
      rcases lt_or_gt_of_ne hnot2 with h2lt | h2gt
      · exact Or.inr (Or.inl h2lt)
      · rcases lt_or_gt_of_ne hnot1 with h1lt | h1gt
        · exact Or.inr (Or.inr h1lt)
        · exact Or.inl ⟨h2gt, h1gt⟩
    refine ⟨hdec, ⟨fun hsees => ?_, fun hmem => ?_⟩⟩
    · have hTX : T ∈ X := Finset.mem_filter.mpr ⟨hTidx, (hP.shatters T ia).mp hsees⟩
      have hle1 : L₂ (w T₁) * L₁ (w T) ≤ L₂ (w T) * L₁ (w T₁) :=
        (div_le_div_iff₀ hL1_T1 (hX_L1_pos T hTX)).mp (hT1_min T hTX)
      have hle2 : L₂ (w T) * L₁ (w T₂) ≤ L₂ (w T₂) * L₁ (w T) :=
        (div_le_div_iff₀ (hX_L1_pos T hTX) hL1_T2).mp (hT2_max T hTX)
      have hpos1 : 0 < detU * orient2D a u₁ (w T) := by
        rw [← hL_orient u₁ (w T), hu1_L1, hu1_L2]
        have hid : L₁ (w T₁) * L₂ (w T) - (L₂ (w T₁) - δ₁ * detU) * L₁ (w T) =
            (L₁ (w T₁) * L₂ (w T) - L₂ (w T₁) * L₁ (w T)) + δ₁ * detU * L₁ (w T) := by ring
        rw [hid]
        have p1 : 0 < δ₁ * detU * L₁ (w T) := mul_pos (mul_pos hδ1_pos hdetU) (hX_L1_pos T hTX)
        linarith
      have hpos2 : 0 < detU * orient2D a (w T) u₂ := by
        rw [← hL_orient (w T) u₂, hu2_L1, hu2_L2]
        have hid : L₁ (w T) * (L₂ (w T₂) + δ₂ * detU) - L₂ (w T) * L₁ (w T₂) =
            (L₁ (w T) * L₂ (w T₂) - L₂ (w T) * L₁ (w T₂)) + δ₂ * detU * L₁ (w T) := by ring
        rw [hid]
        have p2 : 0 < δ₂ * detU * L₁ (w T) := mul_pos (mul_pos hδ2_pos hdetU) (hX_L1_pos T hTX)
        linarith
      rw [hR_open_iff]
      exact ⟨pos_of_mul_pos_right hpos2 (le_of_lt hdetU),
             pos_of_mul_pos_right hpos1 (le_of_lt hdetU)⟩
    · have hU := hR_sub_U (w T) hmem
      have hsep := hU_sep (w T) hU
      rw [hR_open_iff] at hmem
      have hxu1 : orient2D a (w T) u₁ < 0 := by rw [orient2D_swap23]; linarith [hmem.2]
      have hxu2 : 0 < orient2D a (w T) u₂ := hmem.1
      have hax_ne : a ≠ w T := hP.s_ne_w ia T
      have hxb : Sees P (w T) b := (hP.shatters T ib).mpr hTib
      have hxc : Sees P (w T) c := (hP.shatters T ic).mpr hTic
      rcases lt_or_gt_of_ne (mul_ne_zero_iff.mp (ne_of_lt hsep)).1 with hbc_lt | hbc_gt
      · have hc_pos : 0 < orient2D a (w T) c := by
          by_contra hc_le; push Not at hc_le
          have : 0 ≤ orient2D a (w T) b * orient2D a (w T) c :=
            mul_nonneg_of_nonpos_of_nonpos (le_of_lt hbc_lt) hc_le
          linarith
        exact sees_symm (two_path_enclosure_either hP.toEnclosureDomain hax_ne
          (isPolygonalPathIn_four (sees_symm hu2_vis.1) hu2_vis.2.2 (sees_symm hxc))
          (isPolygonalPathIn_four (sees_symm hu1_vis.1) hu1_vis.2.1 (sees_symm hxb))
          (Or.inl ⟨interiorOnLeft_four hxu2 hc_pos, interiorOnRight_four hxu1 hbc_lt⟩))
      · have hc_neg : orient2D a (w T) c < 0 := by
          by_contra hc_ge; push Not at hc_ge
          have : 0 ≤ orient2D a (w T) b * orient2D a (w T) c := mul_nonneg (le_of_lt hbc_gt) hc_ge
          linarith
        exact sees_symm (two_path_enclosure_either hP.toEnclosureDomain hax_ne
          (isPolygonalPathIn_four (sees_symm hu2_vis.1) hu2_vis.2.1 (sees_symm hxb))
          (isPolygonalPathIn_four (sees_symm hu1_vis.1) hu1_vis.2.2 (sees_symm hxc))
          (Or.inl ⟨interiorOnLeft_four hxu2 hbc_gt, interiorOnRight_four hxu1 hc_neg⟩))
  · -- Case 1: X is empty; pick a narrow wedge avoiding all of W'
    have hX_empty : ∀ T ∈ W'_idx, ia ∉ T := by
      intro T hT hia
      exact hX ⟨T, Finset.mem_filter.mpr ⟨hT, hia⟩⟩
    let badSlope : Finset ℝ := W'_idx.image (fun T => ((w T).2 - a.2) / ((w T).1 - a.1))
    obtain ⟨t, ht_mem⟩ := (Set.infinite_univ.sdiff badSlope.finite_toSet).nonempty
    have ht_nb : t ∉ badSlope := by simpa using ht_mem
    have hline_ne : ∀ T ∈ W'_idx, ((w T).2 - a.2) - t * ((w T).1 - a.1) ≠ 0 := by
      intro T hT h0
      by_cases hx1 : (w T).1 = a.1
      · have hy : (w T).2 = a.2 := by rw [hx1] at h0; linarith
        exact hP.s_ne_w ia T (by ext <;> [exact hx1.symm; exact hy.symm])
      · apply ht_nb
        refine Finset.mem_image.mpr ⟨T, hT, ?_⟩
        have hxne : (w T).1 - a.1 ≠ 0 := sub_ne_zero.mpr hx1
        field_simp [hxne]; linarith
    let W'_pos : Finset (Finset (Fin n)) := W'_idx.filter (fun T => a.1 < (w T).1)
    let δ : ℝ := if hpos : W'_pos.Nonempty then
      (W'_pos.inf' hpos (fun T => |((w T).2 - a.2) - t * ((w T).1 - a.1)| / ((w T).1 - a.1))) / 2
      else 1
    have hδ_pos : 0 < δ := by
      dsimp [δ]
      split_ifs with hpos
      · apply div_pos _ (by norm_num)
        rw [Finset.lt_inf'_iff]
        intro T hT
        have hTidx : T ∈ W'_idx := (Finset.mem_filter.mp hT).1
        have hTx : a.1 < (w T).1 := (Finset.mem_filter.mp hT).2
        exact div_pos (abs_pos.mpr (hline_ne T hTidx)) (sub_pos.mpr hTx)
      · exact zero_lt_one
    let R : OpenWedge :=
      { y := a
        u₁ := (δ + t, -1)
        u₂ := (δ - t, 1)
        h_nondeg := by linarith }
    refine ⟨R, rfl, fun x hx => ?_⟩
    obtain ⟨T, hTidx, rfl, _, _⟩ := hW'_mem x hx
    have hext : R.MemExt (w T) := by
      dsimp [OpenWedge.MemExt, R]
      have hl_sum : ((δ + t) * ((w T).1 - a.1) + (-1) * ((w T).2 - a.2)) +
          ((δ - t) * ((w T).1 - a.1) + 1 * ((w T).2 - a.2)) = 2 * δ * ((w T).1 - a.1) := by ring
      by_cases hgt : a.1 < (w T).1
      · have hTpos : T ∈ W'_pos := Finset.mem_filter.mpr ⟨hTidx, hgt⟩
        have hinf : 2 * δ ≤ |((w T).2 - a.2) - t * ((w T).1 - a.1)| / ((w T).1 - a.1) := by
          have hle := Finset.inf'_le (fun T' => |((w T').2 - a.2) - t * ((w T').1 - a.1)| / ((w T').1 - a.1)) hTpos
          dsimp [δ]; rw [dif_pos ⟨T, hTpos⟩]; linarith
        have hmul : 2 * δ * ((w T).1 - a.1) ≤ |((w T).2 - a.2) - t * ((w T).1 - a.1)| := by
          have hden : 0 < (w T).1 - a.1 := sub_pos.mpr hgt
          exact (le_div_iff₀ hden).mp hinf
        have hstrict : δ * ((w T).1 - a.1) < |((w T).2 - a.2) - t * ((w T).1 - a.1)| := by
          have : 0 < δ * ((w T).1 - a.1) := mul_pos hδ_pos (sub_pos.mpr hgt)
          linarith
        rcases lt_abs.mp hstrict with hpos | hneg
        · left; linarith
        · right; linarith
      · have hle : (w T).1 ≤ a.1 := not_lt.mp hgt
        have hnonpos : 2 * δ * ((w T).1 - a.1) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos (by linarith) (sub_nonpos.mpr hle)
        by_contra hnot
        push Not at hnot
        have hsum_eq : ((δ + t) * ((w T).1 - a.1) + (-1) * ((w T).2 - a.2)) +
            ((δ - t) * ((w T).1 - a.1) + 1 * ((w T).2 - a.2)) = 2 * δ * ((w T).1 - a.1) := by ring
        have hx0 : (w T).1 - a.1 = 0 := by nlinarith [hnot.1, hnot.2]
        have hy0 : (w T).2 - a.2 = 0 := by
          have h1 : 0 ≤ -((w T).2 - a.2) := by
            have := hnot.1; rw [hx0] at this; linarith
          have h2 : 0 ≤ (w T).2 - a.2 := by
            have := hnot.2; rw [hx0] at this; linarith
          linarith
        exact hline_ne T hTidx (by rw [hx0, hy0]; ring)
    refine ⟨Or.inr hext, ⟨fun hsees => ?_, fun hopen => ?_⟩⟩
    · exact False.elim (hX_empty T hTidx ((hP.shatters T ia).mp hsees))
    · rcases hext with h1 | h2 <;> [linarith [hopen.1]; linarith [hopen.2]]

/-- Planar Carathéodory theorem (`ℝ × ℝ`): every point of `convexHull ℝ s` lies in `InClosedTri p q r z`
    for three points `p, q, r ∈ s` (possibly repeated if `s` has `< 3` points). -/
lemma planar_caratheodory {s : Set (ℝ × ℝ)} {z : ℝ × ℝ} (hz : z ∈ convexHull ℝ s) :
    ∃ p ∈ s, ∃ q ∈ s, ∃ r ∈ s, InClosedTri p q r z := by
  rw [mem_convexHull_iff_exists_fintype] at hz
  rcases hz with ⟨ι, _, μ, pts, hμ_nn, hμ_sum, hpts_s, hz_eq⟩
  have hfin : ∃ (k : ℕ) (f : Fin k → ℝ) (q : Fin k → ℝ × ℝ),
      (∀ i, 0 < f i) ∧ (∑ i, f i = 1) ∧ (∀ i, q i ∈ s) ∧ (∑ i, f i • q i = z) := by
    let I := Finset.univ.filter (fun i : ι => 0 < μ i)
    have hI_sum : ∑ i ∈ I, μ i = 1 := by
      rw [← hμ_sum]
      apply Finset.sum_subset (Finset.subset_univ _)
      intro i _ hi
      simp only [I, Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hi
      exact le_antisymm hi (hμ_nn i)
    have hI_eq : ∑ i ∈ I, μ i • pts i = z := by
      rw [← hz_eq]
      apply Finset.sum_subset (Finset.subset_univ _)
      intro i _ hi
      simp only [I, Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hi
      have h0 : μ i = 0 := le_antisymm hi (hμ_nn i)
      rw [h0, zero_smul]
    let e := I.equivFin
    refine ⟨I.card, fun j => μ (e.symm j), fun j => pts (e.symm j), ?_, ?_, ?_, ?_⟩
    · intro j
      have hm := (e.symm j).2
      exact (Finset.mem_filter.mp hm).2
    · rw [← hI_sum, ← Finset.sum_coe_sort I, ← Equiv.sum_comp e.symm]
    · intro j
      exact hpts_s (e.symm j).1
    · rw [← hI_eq, ← Finset.sum_coe_sort I, ← Equiv.sum_comp e.symm]
  rcases hfin with ⟨k, f, q, hf_pos, hf_sum, hq_s, hq_sum⟩
  have h_reduce : ∀ (m : ℕ) (g : Fin m → ℝ) (p : Fin m → ℝ × ℝ),
      (∀ i, 0 < g i) → (∑ i, g i = 1) → (∀ i, p i ∈ s) → (∑ i, g i • p i = z) →
      ∃ p₁ ∈ s, ∃ p₂ ∈ s, ∃ p₃ ∈ s, InClosedTri p₁ p₂ p₃ z := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro g p hg_pos hg_sum hp_s hp_sum
      by_cases hm3 : m ≤ 3
      · have hm_ne0 : 0 < m := by
          by_contra hm0
          have hm_eq0 : m = 0 := by omega
          subst hm_eq0
          simp at hg_sum
        rcases (by omega : m = 1 ∨ m = 2 ∨ m = 3) with rfl | rfl | rfl
        · refine ⟨p 0, hp_s 0, p 0, hp_s 0, p 0, hp_s 0, 1, 0, 0, zero_le_one, le_rfl, le_rfl,
            by ring, ?_, ?_⟩
          · have h0 : g 0 = 1 := by simpa using hg_sum
            have hz0 : z = p 0 := by rw [← hp_sum]; simp [h0]
            rw [hz0]; ring
          · have h0 : g 0 = 1 := by simpa using hg_sum
            have hz0 : z = p 0 := by rw [← hp_sum]; simp [h0]
            rw [hz0]; ring
        · refine ⟨p 0, hp_s 0, p 1, hp_s 1, p 1, hp_s 1, g 0, g 1, 0,
            le_of_lt (hg_pos 0), le_of_lt (hg_pos 1), le_rfl, ?_, ?_, ?_⟩
          · simpa [Fin.sum_univ_two] using hg_sum
          · rw [← hp_sum]; simp [Fin.sum_univ_two, smul_eq_mul]
          · rw [← hp_sum]; simp [Fin.sum_univ_two, smul_eq_mul]
        · refine ⟨p 0, hp_s 0, p 1, hp_s 1, p 2, hp_s 2, g 0, g 1, g 2,
            le_of_lt (hg_pos 0), le_of_lt (hg_pos 1), le_of_lt (hg_pos 2), ?_, ?_, ?_⟩
          · simpa [Fin.sum_univ_three] using hg_sum
          · rw [← hp_sum]; simp [Fin.sum_univ_three, smul_eq_mul]
          · rw [← hp_sum]; simp [Fin.sum_univ_three, smul_eq_mul]
      · have hm4 : 4 ≤ m := by omega
        let i0 : Fin m := ⟨0, by omega⟩
        let i1 : Fin m := ⟨1, by omega⟩
        let i2 : Fin m := ⟨2, by omega⟩
        let i3 : Fin m := ⟨3, by omega⟩
        have hlin_dep : ∃ c0 c1 c2 c3 : ℝ, (0 < c0 ∨ 0 < c1 ∨ 0 < c2 ∨ 0 < c3) ∧
            c0 + c1 + c2 + c3 = 0 ∧
            c0 • p i0 + c1 • p i1 + c2 • p i2 + c3 • p i3 = 0 := by
          let d0 := orient2D (p i1) (p i2) (p i3)
          let d1 := -orient2D (p i0) (p i2) (p i3)
          let d2 := orient2D (p i0) (p i1) (p i3)
          let d3 := -orient2D (p i0) (p i1) (p i2)
          have hd_sum : d0 + d1 + d2 + d3 = 0 := by
            dsimp [d0, d1, d2, d3]; unfold orient2D; ring
          have hd_lin : d0 • p i0 + d1 • p i1 + d2 • p i2 + d3 • p i3 = 0 := by
            ext <;> simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
              Prod.fst_zero, Prod.snd_zero, smul_eq_mul] <;>
              dsimp [d0, d1, d2, d3, orient2D] <;> ring
          by_cases hd_nz : d0 ≠ 0 ∨ d1 ≠ 0 ∨ d2 ≠ 0 ∨ d3 ≠ 0
          · have hpos_or_neg : (0 < d0 ∨ 0 < d1 ∨ 0 < d2 ∨ 0 < d3) ∨
                (0 < -d0 ∨ 0 < -d1 ∨ 0 < -d2 ∨ 0 < -d3) := by
              rcases hd_nz with h | h | h | h
              · rcases lt_or_gt_of_ne h with hlt | hgt
                · right; left; exact neg_pos.mpr hlt
                · left; left; exact hgt
              · rcases lt_or_gt_of_ne h with hlt | hgt
                · right; right; left; exact neg_pos.mpr hlt
                · left; right; left; exact hgt
              · rcases lt_or_gt_of_ne h with hlt | hgt
                · right; right; right; left; exact neg_pos.mpr hlt
                · left; right; right; left; exact hgt
              · rcases lt_or_gt_of_ne h with hlt | hgt
                · right; right; right; right; exact neg_pos.mpr hlt
                · left; right; right; right; exact hgt
            rcases hpos_or_neg with hp | hn
            · exact ⟨d0, d1, d2, d3, hp, hd_sum, hd_lin⟩
            · exact ⟨-d0, -d1, -d2, -d3, hn, by linarith,
                by simp only [neg_smul]; rw [← neg_add, ← neg_add, ← neg_add]; simp [hd_lin]⟩
          · push Not at hd_nz
            by_cases hp01 : p i0 = p i1
            · exact ⟨1, -1, 0, 0, Or.inl zero_lt_one, by ring,
                by rw [hp01]; ext <;> simp⟩
            · have hc : (p i1).1 - (p i0).1 ≠ 0 ∨ (p i1).2 - (p i0).2 ≠ 0 := by
                by_contra h0; push Not at h0; exact hp01 (by ext <;> linarith [h0.1, h0.2])
              have hd3_0 : orient2D (p i0) (p i1) (p i2) = 0 := by linarith [hd_nz.2.2.2]
              obtain ⟨τ, hτ1, hτ2⟩ : ∃ τ : ℝ, (p i2).1 - (p i0).1 = τ * ((p i1).1 - (p i0).1) ∧
                  (p i2).2 - (p i0).2 = τ * ((p i1).2 - (p i0).2) := by
                unfold orient2D at hd3_0
                rcases hc with hx | hy
                · exact ⟨((p i2).1 - (p i0).1) / ((p i1).1 - (p i0).1), by field_simp [hx],
                    by field_simp [hx]; linear_combination hd3_0⟩
                · exact ⟨((p i2).2 - (p i0).2) / ((p i1).2 - (p i0).2),
                    by field_simp [hy]; linear_combination -hd3_0, by field_simp [hy]⟩
              by_cases hpos : 0 < τ - 1 ∨ 0 < -τ ∨ 0 < (1 : ℝ)
              · exact ⟨τ - 1, -τ, 1, 0, Or.inr (Or.inr (Or.inl zero_lt_one)), by ring, by
                  ext <;> simp [smul_eq_mul] <;> [linarith; linarith]⟩
              · exact False.elim (hpos (Or.inr (Or.inr zero_lt_one)))
        rcases hlin_dep with ⟨c0, c1, c2, c3, hc_pos, hc_sum, hc_lin⟩
        let c : Fin m → ℝ := fun i =>
          if i = i0 then c0 else if i = i1 then c1 else if i = i2 then c2 else if i = i3 then c3 else 0
        have hi01 : i0 ≠ i1 := by simp [i0, i1, Fin.ext_iff]
        have hi02 : i0 ≠ i2 := by simp [i0, i2, Fin.ext_iff]
        have hi03 : i0 ≠ i3 := by simp [i0, i3, Fin.ext_iff]
        have hi12 : i1 ≠ i2 := by simp [i1, i2, Fin.ext_iff]
        have hi13 : i1 ≠ i3 := by simp [i1, i3, Fin.ext_iff]
        have hi23 : i2 ≠ i3 := by simp [i2, i3, Fin.ext_iff]
        let J : Finset (Fin m) := Finset.univ.filter (fun i => 0 < c i)
        have hJ_ne : J.Nonempty := by
          rcases hc_pos with h0 | h1 | h2 | h3
          · exact ⟨i0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp [c, h0]⟩⟩
          · exact ⟨i1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp [c, hi01.symm, h1]⟩⟩
          · exact ⟨i2, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp [c, hi02.symm, hi12.symm, h2]⟩⟩
          · exact ⟨i3, Finset.mem_filter.mpr ⟨Finset.mem_univ _,
              by simp [c, hi03.symm, hi13.symm, hi23.symm, h3]⟩⟩
        obtain ⟨jstar, hjstar_mem, hjstar_min⟩ := Finset.exists_min_image J (fun i => g i / c i) hJ_ne
        let t : ℝ := g jstar / c jstar
        have hc_jstar : 0 < c jstar := (Finset.mem_filter.mp hjstar_mem).2
        have ht_pos : 0 < t := div_pos (hg_pos jstar) hc_jstar
        let g' : Fin m → ℝ := fun i => g i - t * c i
        have hg'_nn : ∀ i, 0 ≤ g' i := by
          intro i
          dsimp [g']
          by_cases hci : 0 < c i
          · have hiJ : i ∈ J := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hci⟩
            have hle := hjstar_min i hiJ
            have := (le_div_iff₀ hci).mp hle
            linarith
          · have hle : c i ≤ 0 := not_lt.mp hci
            have : t * c i ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (le_of_lt ht_pos) hle
            linarith [hg_pos i]
        have hg'_jstar : g' jstar = 0 := by
          dsimp [g', t]; field_simp [ne_of_gt hc_jstar]; ring
        have hc_total_sum : ∑ i : Fin m, c i = 0 := by
          have hsub : ({i0, i1, i2, i3} : Finset (Fin m)) ⊆ Finset.univ := Finset.subset_univ _
          rw [← Finset.sum_subset hsub]
          · simp only [Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton,
              Finset.sum_singleton, hi01, hi02, hi03, hi12, hi13, hi23, or_self, not_false_eq_true]
            simp only [c, if_true, hi01.symm, hi02.symm, hi03.symm, hi12.symm, hi13.symm, hi23.symm,
              if_false]
            linarith
          · intro i _ hi
            simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hi
            simp [c, hi.1, hi.2.1, hi.2.2.1, hi.2.2.2]
        have hc_total_lin : ∑ i : Fin m, c i • p i = 0 := by
          have hsub : ({i0, i1, i2, i3} : Finset (Fin m)) ⊆ Finset.univ := Finset.subset_univ _
          rw [← Finset.sum_subset hsub]
          · simp only [Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton,
              Finset.sum_singleton, hi01, hi02, hi03, hi12, hi13, hi23, or_self, not_false_eq_true]
            simp only [c, if_true, hi01.symm, hi02.symm, hi03.symm, hi12.symm, hi13.symm, hi23.symm,
              if_false]
            simpa [add_assoc] using hc_lin
          · intro i _ hi
            simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hi
            simp [c, hi.1, hi.2.1, hi.2.2.1, hi.2.2.2]
        have hg'_sum : ∑ i : Fin m, g' i = 1 := by
          simp only [g', Finset.sum_sub_distrib, ← Finset.mul_sum, hc_total_sum, mul_zero, sub_zero]
          exact hg_sum
        have hg'_lin : ∑ i : Fin m, g' i • p i = z := by
          simp only [g', sub_smul, Finset.sum_sub_distrib, mul_smul, ← Finset.smul_sum,
            hc_total_lin, smul_zero, sub_zero]
          exact hp_sum
        let K := Finset.univ.filter (fun i : Fin m => 0 < g' i)
        have hK_lt : K.card < m := by
          have hss : K ⊂ Finset.univ := by
            rw [Finset.ssubset_iff_of_subset (Finset.subset_univ _)]
            refine ⟨jstar, Finset.mem_univ _, ?_⟩
            simp [K, hg'_jstar]
          simpa using Finset.card_lt_card hss
        have hK_sum : ∑ i ∈ K, g' i = 1 := by
          rw [← hg'_sum]
          apply Finset.sum_subset (Finset.subset_univ _)
          intro i _ hi
          simp only [K, Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hi
          exact le_antisymm hi (hg'_nn i)
        have hK_lin : ∑ i ∈ K, g' i • p i = z := by
          rw [← hg'_lin]
          apply Finset.sum_subset (Finset.subset_univ _)
          intro i _ hi
          simp only [K, Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hi
          rw [le_antisymm hi (hg'_nn i), zero_smul]
        let e := K.equivFin
        exact ih K.card hK_lt (fun j => g' (e.symm j)) (fun j => p (e.symm j))
          (fun j => (Finset.mem_filter.mp (e.symm j).2).2)
          (by rw [← hK_sum, ← Finset.sum_coe_sort K, ← Equiv.sum_comp e.symm])
          (fun j => hp_s (e.symm j).1)
          (by rw [← hK_lin, ← Finset.sum_coe_sort K, ← Equiv.sum_comp e.symm])
  exact h_reduce k f q hf_pos hf_sum hq_s hq_sum

/-- Corollary 2.8 (`Fan`, `upper_9.tex` lines 243–250):
    if witness `w T` sees `F` and misses `a ∉ F`, and `S a ∈ conv(F ∪ {w T})`,
    then `S a` has a wedge test on `W(F)`. -/
theorem fan {n : ℕ} {P : Set (ℝ × ℝ)} {S : Fin n → ℝ × ℝ}
    {w : Finset (Fin n) → ℝ × ℝ}
    (hP : ShatteredSimplePolygon P S w)
    {T F : Finset (Fin n)} {ia : Fin n}
    (hFT : F ⊆ T) (hia_not : ia ∉ T)
    (ha_conv : S ia ∈ convexHull ℝ (insert (w T) (F.image S : Set (ℝ × ℝ)))) :
    ∃ R : OpenWedge, R.y = S ia ∧ IsWedgeTest P (WitnessSet F ∅ w) (S ia) R := by
  obtain ⟨p, hp, q, hq, r, hr, htri⟩ := planar_caratheodory ha_conv
  have hmem : S ia ∈ convexHull ℝ ({p, q, r} : Set (ℝ × ℝ)) :=
    (inClosedTri_iff_mem_convexHull _ _ _ _).mp htri
  have fan_step : ∀ {p' q' : ℝ × ℝ},
      p' ∈ insert (w T) (F.image S : Set (ℝ × ℝ)) →
      q' ∈ insert (w T) (F.image S : Set (ℝ × ℝ)) →
      S ia ∈ convexHull ℝ ({w T, p', q'} : Set (ℝ × ℝ)) →
      ∃ R : OpenWedge, R.y = S ia ∧ IsWedgeTest P (WitnessSet F ∅ w) (S ia) R := by
    intro p' q' hp' hq' htri_conv
    have htri' : InClosedTri (w T) p' q' (S ia) := (inClosedTri_iff_mem_convexHull _ _ _ _).mpr htri_conv
    have h_not_w : ∀ {u v : ℝ × ℝ},
        u ∈ insert (w T) (F.image S : Set (ℝ × ℝ)) →
        v ∈ insert (w T) (F.image S : Set (ℝ × ℝ)) →
        InClosedTri (w T) u v (S ia) → u ≠ w T := by
      intro u v _ hv htr huw
      rw [huw] at htr
      rcases htr with ⟨μ₁, μ₂, μ₃, _, _, _, hsum, hx1, hx2⟩
      have hcol : orient2D (w T) v (S ia) = 0 := by
        unfold orient2D; rw [hx1, hx2, show μ₁ = 1 - μ₂ - μ₃ by linarith]; ring
      rcases hv with rfl | hvF
      · have hseg : S ia = w T := by
          ext
          · rw [hx1]; rw [show μ₁ * (w T).1 + μ₂ * (w T).1 + μ₃ * (w T).1 =
              (μ₁ + μ₂ + μ₃) * (w T).1 by ring, hsum, one_mul]
          · rw [hx2]; rw [show μ₁ * (w T).2 + μ₂ * (w T).2 + μ₃ * (w T).2 =
              (μ₁ + μ₂ + μ₃) * (w T).2 by ring, hsum, one_mul]
        exact hP.s_ne_w ia T hseg
      · rcases Finset.mem_image.mp hvF with ⟨iv, hvF', rfl⟩
        exact hP.no_three_collinear (w T) (S iv) (S ia) (Or.inr ⟨T, rfl⟩) (Or.inl ⟨iv, rfl⟩)
          (Or.inl ⟨ia, rfl⟩) (hP.s_ne_w iv T).symm (fun h => hia_not (hFT (hP.s_inj h ▸ hvF')))
          (hP.s_ne_w ia T).symm hcol
    have hp_ne_w : p' ≠ w T := h_not_w hp' hq' htri'
    have hq_ne_w : q' ≠ w T := h_not_w hq' hp' (by
      rcases htri' with ⟨μ₁, μ₂, μ₃, h1, h2, h3, hs, hx1, hx2⟩
      exact ⟨μ₁, μ₃, μ₂, h1, h3, h2, by linarith, by linarith, by linarith⟩)
    rcases hp' with hpw | hpF; · exact False.elim (hp_ne_w hpw)
    rcases hq' with hqw | hqF; · exact False.elim (hq_ne_w hqw)
    rcases Finset.mem_image.mp hpF with ⟨ib, hibF, rfl⟩
    rcases Finset.mem_image.mp hqF with ⟨ic, hicF, rfl⟩
    have hbc : ib ≠ ic := by
      intro heq
      subst heq
      rcases htri' with ⟨μ₁, μ₂, μ₃, _, _, _, hsum, hx1, hx2⟩
      have hcol : orient2D (w T) (S ib) (S ia) = 0 := by
        unfold orient2D; rw [hx1, hx2, show μ₁ = 1 - μ₂ - μ₃ by linarith]; ring
      exact hP.no_three_collinear (w T) (S ib) (S ia) (Or.inr ⟨T, rfl⟩) (Or.inl ⟨ib, rfl⟩)
        (Or.inl ⟨ia, rfl⟩) (hP.s_ne_w ib T).symm (fun h => hia_not (hFT (hP.s_inj h ▸ hibF)))
        (hP.s_ne_w ia T).symm hcol
    have hab : ia ≠ ib := fun h => hia_not (hFT (h ▸ hibF))
    have hac : ia ≠ ic := fun h => hia_not (hFT (h ▸ hicF))
    have hopen : InOpenTri (w T) (S ib) (S ic) (S ia) := by
      refine inOpenTri_of_noncollinear_inClosedTri htri' ?_ ?_ ?_
      · exact hP.no_three_collinear (S ib) (S ic) (S ia) (Or.inl ⟨ib, rfl⟩) (Or.inl ⟨ic, rfl⟩)
          (Or.inl ⟨ia, rfl⟩) (fun h => hbc (hP.s_inj h)) (fun h => hac (hP.s_inj h).symm)
          (fun h => hab (hP.s_inj h).symm)
      · exact hP.no_three_collinear (S ic) (w T) (S ia) (Or.inl ⟨ic, rfl⟩) (Or.inr ⟨T, rfl⟩)
          (Or.inl ⟨ia, rfl⟩) (hP.s_ne_w ic T) (hP.s_ne_w ia T).symm (fun h => hac (hP.s_inj h).symm)
      · exact hP.no_three_collinear (w T) (S ib) (S ia) (Or.inr ⟨T, rfl⟩) (Or.inl ⟨ib, rfl⟩)
          (Or.inl ⟨ia, rfl⟩) (hP.s_ne_w ib T).symm (fun h => hab (hP.s_inj h).symm)
          (hP.s_ne_w ia T).symm
    have hwb : Sees P (w T) (S ib) := (hP.shatters T ib).mpr (hFT hibF)
    have hwc : Sees P (w T) (S ic) := (hP.shatters T ic).mpr (hFT hicF)
    have hnwa : ¬ Sees P (w T) (S ia) := fun hs => hia_not ((hP.shatters T ia).mp hs)
    have hbc_ne : orient2D (S ia) (S ib) (S ic) ≠ 0 :=
      hP.no_three_collinear (S ia) (S ib) (S ic) (Or.inl ⟨ia, rfl⟩) (Or.inl ⟨ib, rfl⟩)
        (Or.inl ⟨ic, rfl⟩) (fun h => hab (hP.s_inj h)) (fun h => hbc (hP.s_inj h))
        (fun h => hac (hP.s_inj h))
    have hW_sub : WitnessSet F ∅ w ⊆ WitnessSet {ib, ic} ∅ w :=
      witnessSet_mono (Finset.insert_subset_iff.mpr ⟨hibF, Finset.singleton_subset_iff.mpr hicF⟩)
        (Finset.Subset.refl _)
    have h_all_U : ∀ x ∈ WitnessSet F ∅ w, Sees P x (S ia) → x ∈ UCone (S ia) (S ib) (S ic) := by
      intro x hxW hxa
      rcases hxW with ⟨Tx, hFTx, _, rfl⟩
      have hx_ne_wT : w Tx ≠ w T := fun h => hia_not ((hP.shatters T ia).mp (by
        rw [← hP.w_inj h]; exact hxa))
      have hxb : Sees P (w Tx) (S ib) := (hP.shatters Tx ib).mpr (hFTx hibF)
      have hxc : Sees P (w Tx) (S ic) := (hP.shatters Tx ic).mpr (hFTx hicF)
      have hxab : orient2D (S ia) (S ib) (w Tx) ≠ 0 :=
        hP.no_three_collinear (S ia) (S ib) (w Tx) (Or.inl ⟨ia, rfl⟩) (Or.inl ⟨ib, rfl⟩)
          (Or.inr ⟨Tx, rfl⟩) (fun h => hab (hP.s_inj h)) (hP.s_ne_w ib Tx) (hP.s_ne_w ia Tx)
      have hxac : orient2D (S ia) (S ic) (w Tx) ≠ 0 :=
        hP.no_three_collinear (S ia) (S ic) (w Tx) (Or.inl ⟨ia, rfl⟩) (Or.inl ⟨ic, rfl⟩)
          (Or.inr ⟨Tx, rfl⟩) (fun h => hac (hP.s_inj h)) (hP.s_ne_w ic Tx) (hP.s_ne_w ia Tx)
      have hxwa : orient2D (w T) (S ia) (w Tx) ≠ 0 :=
        hP.no_three_collinear (w T) (S ia) (w Tx) (Or.inr ⟨T, rfl⟩) (Or.inl ⟨ia, rfl⟩)
          (Or.inr ⟨Tx, rfl⟩) (hP.s_ne_w ia T).symm (hP.s_ne_w ia Tx) (fun h => hx_ne_wT h.symm)
      exact cone hP.toEnclosureDomain hwb hwc hnwa hopen hxb hxc hxab hxac hxwa
    rcases lt_or_gt_of_ne hbc_ne with hneg | hpos
    · have hccw : 0 < orient2D (S ia) (S ic) (S ib) := by rw [orient2D_swap23]; linarith
      let U := oppositeConeWedge (S ia) (S ic) (S ib) hccw
      have hW_sub' : WitnessSet F ∅ w ⊆ WitnessSet {ic, ib} ∅ w := by
        simpa only [Finset.pair_comm ib ic] using hW_sub
      obtain ⟨R, hRy, hRtest⟩ := wedge_extraction hP hac hbc.symm hab hW_sub' U rfl
        (fun z hz => by
          have hzU : z ∈ UCone (S ia) (S ic) (S ib) := ((u_halfplanes hccw z).2.1).mpr hz
          have hsep := u_halfplanes_separates (by rw [orient2D_swap23]; linarith) hzU
          linarith [mul_comm (orient2D (S ia) z (S ic)) (orient2D (S ia) z (S ib))])
        (fun x hx hxa => ((u_halfplanes hccw x).2.1).mp ((uCone_symm _ _ _) ▸ h_all_U x hx hxa))
      exact ⟨R, hRy, hRtest⟩
    · let U := oppositeConeWedge (S ia) (S ib) (S ic) hpos
      exact wedge_extraction hP hab hbc hac hW_sub U rfl
        (fun z hz => u_halfplanes_separates hbc_ne (((u_halfplanes hpos z).2.1).mpr hz))
        (fun x hx hxa => ((u_halfplanes hpos x).2.1).mp (h_all_U x hx hxa))
  rcases convexHull_triangle_three_piece_cover r (w T) p q (S ia) hmem with h1 | h2 | h3
  · exact fan_step hp hq h1
  · exact fan_step hq hr h2
  · exact fan_step hr hp h3

/-! ## Section 3: Hull Vertices, Interior Points, Convex Position, and Lemmas 3.2–3.4 -/

/-- Extreme points of a finite planar point set `F`. -/
def extremePointsFinset (F : Finset (ℝ × ℝ)) : Finset (ℝ × ℝ) :=
  F.filter (fun p => p ∉ convexHull ℝ ((F.erase p : Finset (ℝ × ℝ)) : Set (ℝ × ℝ)))

private lemma convexHull_insert_decomp {p q : ℝ × ℝ} {R : Finset (ℝ × ℝ)}
    (hpq : p ≠ q) (hp : p ∈ convexHull ℝ ((insert q R : Finset (ℝ × ℝ)) : Set (ℝ × ℝ))) :
    ∃ β : ℝ, 0 ≤ β ∧ β < 1 ∧ ∃ y ∈ convexHull ℝ (R : Set (ℝ × ℝ)),
      p = β • q + (1 - β) • y := by
  rw [mem_convexHull_iff_exists_fintype] at hp
  rcases hp with ⟨ι, _, μ, pts, hμ_nn, hμ_sum, hpts_mem, hp_eq⟩
  let Iq := Finset.univ.filter (fun i : ι => pts i = q)
  let IR := Finset.univ \ Iq
  let β : ℝ := ∑ i ∈ Iq, μ i
  have hβ_nn : 0 ≤ β := Finset.sum_nonneg (fun i _ => hμ_nn i)
  have hsum_split : β + ∑ i ∈ IR, μ i = 1 := by
    dsimp [β, IR]
    rw [add_comm]
    exact (Finset.sum_sdiff (Finset.filter_subset _ Finset.univ)).trans hμ_sum
  have hβ_lt1 : β < 1 := by
    have hle : β ≤ 1 := by
      have hnn : 0 ≤ ∑ i ∈ IR, μ i := Finset.sum_nonneg (fun i _ => hμ_nn i)
      linarith
    refine lt_of_le_of_ne hle (fun hβ1 => hpq ?_)
    have hIR0 : ∑ i ∈ IR, μ i = 0 := by linarith
    have hμ0 : ∀ i ∈ IR, μ i = 0 := fun i hi =>
      (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hμ_nn j)).mp hIR0 i hi
    rw [← hp_eq]
    have hsplit_vec : ∑ i : ι, μ i • pts i =
        (∑ i ∈ Iq, μ i • pts i) + (∑ i ∈ IR, μ i • pts i) := by
      dsimp [IR]
      rw [add_comm]
      exact (Finset.sum_sdiff (Finset.filter_subset (fun i : ι => pts i = q) Finset.univ)).symm
    rw [hsplit_vec]
    have hIq_val : ∑ i ∈ Iq, μ i • pts i = β • q := by
      have h1 : ∑ i ∈ Iq, μ i • pts i = ∑ i ∈ Iq, μ i • q :=
        Finset.sum_congr rfl (fun i hi => by rw [(Finset.mem_filter.mp hi).2])
      rw [h1, ← Finset.sum_smul]
    have hIR_val : ∑ i ∈ IR, μ i • pts i = 0 :=
      Finset.sum_eq_zero (fun i hi => by rw [hμ0 i hi, zero_smul])
    rw [hIq_val, hIR_val, add_zero, hβ1, one_smul]
  have h1β_pos : 0 < 1 - β := sub_pos.mpr hβ_lt1
  let y : ℝ × ℝ := (1 / (1 - β)) • ∑ i ∈ IR, μ i • pts i
  have hy_mem : y ∈ convexHull ℝ (R : Set (ℝ × ℝ)) := by
    by_cases hIR_ne : IR.Nonempty
    · rw [mem_convexHull_iff_exists_fintype]
      refine ⟨IR, inferInstance, fun i => μ i.1 / (1 - β), fun i => pts i.1, ?_, ?_, ?_, ?_⟩
      · intro i; exact div_nonneg (hμ_nn i.1) (le_of_lt h1β_pos)
      · rw [Finset.univ_eq_attach, Finset.sum_attach IR (fun i => μ i / (1 - β)), ← Finset.sum_div]
        have hsum_IR : ∑ i ∈ IR, μ i = 1 - β := by linarith
        rw [hsum_IR, div_self (ne_of_gt h1β_pos)]
      · intro i
        have hi_mem := hpts_mem i.1
        simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at hi_mem
        have hi_neq : pts i.1 ≠ q := by
          have := (Finset.mem_sdiff.mp i.2).2
          simpa [Iq] using this
        exact hi_mem.resolve_left hi_neq
      · rw [Finset.univ_eq_attach, Finset.sum_attach IR (fun i => (μ i / (1 - β)) • pts i)]
        dsimp [y]
        rw [Finset.smul_sum]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [smul_smul, one_div, div_eq_mul_inv, mul_comm]
    · exfalso
      rw [Finset.not_nonempty_iff_eq_empty] at hIR_ne
      rw [hIR_ne, Finset.sum_empty, add_zero] at hsum_split
      linarith
  refine ⟨β, hβ_nn, hβ_lt1, y, hy_mem, ?_⟩
  rw [← hp_eq]
  have hsplit_vec : ∑ i : ι, μ i • pts i =
      (∑ i ∈ Iq, μ i • pts i) + (∑ i ∈ IR, μ i • pts i) := by
    dsimp [IR]
    rw [add_comm]
    exact (Finset.sum_sdiff (Finset.filter_subset (fun i : ι => pts i = q) Finset.univ)).symm
  rw [hsplit_vec]
  have hIq_val : ∑ i ∈ Iq, μ i • pts i = β • q := by
    have h1 : ∑ i ∈ Iq, μ i • pts i = ∑ i ∈ Iq, μ i • q :=
      Finset.sum_congr rfl (fun i hi => by rw [(Finset.mem_filter.mp hi).2])
    rw [h1, ← Finset.sum_smul]
  have hIR_val : ∑ i ∈ IR, μ i • pts i = (1 - β) • y := by
    dsimp [y]
    rw [smul_smul, mul_one_div_cancel (ne_of_gt h1β_pos), one_smul]
  rw [hIq_val, hIR_val]

lemma extremePointsFinset_convexHull_eq (F : Finset (ℝ × ℝ)) :
    convexHull ℝ (extremePointsFinset F : Set (ℝ × ℝ)) = convexHull ℝ (F : Set (ℝ × ℝ)) := by
  have h_ind : ∀ m : ℕ, ∀ F : Finset (ℝ × ℝ), F.card = m →
      convexHull ℝ (extremePointsFinset F : Set (ℝ × ℝ)) = convexHull ℝ (F : Set (ℝ × ℝ)) := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro F hcard
      by_cases hex : ∃ p ∈ F, p ∈ convexHull ℝ ((F.erase p : Finset (ℝ × ℝ)) : Set (ℝ × ℝ))
      · rcases hex with ⟨p, hpF, hp_conv⟩
        let F' := F.erase p
        have hF'_card : F'.card < m := by
          rw [← hcard]; exact Finset.card_erase_lt_of_mem hpF
        have h_conv_eq : convexHull ℝ (F' : Set (ℝ × ℝ)) = convexHull ℝ (F : Set (ℝ × ℝ)) := by
          apply le_antisymm
          · exact convexHull_mono (by intro z hz; exact Finset.erase_subset p F hz)
          · apply convexHull_min _ (convex_convexHull ℝ _)
            intro z hz
            by_cases hzp : z = p
            · rwa [hzp]
            · exact subset_convexHull ℝ _ (Finset.mem_erase.mpr ⟨hzp, hz⟩)
        have h_ext_eq : extremePointsFinset F = extremePointsFinset F' := by
          ext q
          simp only [extremePointsFinset, Finset.mem_filter]
          constructor
          · rintro ⟨hqF, hq_not⟩
            have hqp : q ≠ p := fun h => hq_not (h ▸ hp_conv)
            refine ⟨Finset.mem_erase.mpr ⟨hqp, hqF⟩, fun hq' => hq_not ?_⟩
            exact convexHull_mono (Finset.coe_subset.mpr (Finset.erase_subset_erase q (Finset.erase_subset p F))) hq'
          · rintro ⟨hqF', hq'_not⟩
            have hqF : q ∈ F := (Finset.mem_erase.mp hqF').2
            have hqp : q ≠ p := (Finset.mem_erase.mp hqF').1
            refine ⟨hqF, fun hq_conv => hq'_not ?_⟩
            let R : Finset (ℝ × ℝ) := F'.erase q
            have hFq : F.erase q = insert p R := by
              ext z
              simp only [R, Finset.mem_erase, Finset.mem_insert, F']
              by_cases hzp : z = p
              · subst hzp; simp [hpF, hqp.symm]
              · simp [hzp]
            have hFp : F.erase p = insert q R := by
              ext z
              simp only [R, Finset.mem_erase, Finset.mem_insert, F']
              by_cases hzq : z = q
              · subst hzq; simp [hqF, hqp]
              · simp [hzq]
            rw [hFq] at hq_conv
            rw [hFp] at hp_conv
            obtain ⟨α, hα_nn, hα_lt1, x, hxR, hq_eq⟩ := convexHull_insert_decomp hqp hq_conv
            obtain ⟨β, hβ_nn, hβ_lt1, y, hyR, hp_eq⟩ := convexHull_insert_decomp hqp.symm hp_conv
            have h1ab : 0 < 1 - α * β := by nlinarith
            have hsum_comb : (1 - α) / (1 - α * β) + (α * (1 - β)) / (1 - α * β) = 1 := by
              field_simp [ne_of_gt h1ab]; ring
            have hcomb : q = ((1 - α) / (1 - α * β)) • x + ((α * (1 - β)) / (1 - α * β)) • y := by
              have hlin : (1 - α * β) • q = (1 - α) • x + (α * (1 - β)) • y := by
                have h1 : q = α • (β • q + (1 - β) • y) + (1 - α) • x := by rw [← hp_eq]; exact hq_eq
                ext
                · have h1x := congrArg Prod.fst h1; simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul] at h1x ⊢; linarith
                · have h1y := congrArg Prod.snd h1; simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul] at h1y ⊢; linarith
              have hinv : q = (1 / (1 - α * β)) • ((1 - α * β) • q) := by
                rw [smul_smul, one_div_mul_cancel (ne_of_gt h1ab), one_smul]
              rw [hinv, hlin, smul_add, smul_smul, smul_smul]
              congr 2 <;> ring
            have hcomb_mem := (convex_convexHull ℝ (R : Set (ℝ × ℝ))) hxR hyR
              (div_nonneg (by linarith) (le_of_lt h1ab))
              (div_nonneg (mul_nonneg hα_nn (by linarith)) (le_of_lt h1ab))
              hsum_comb
            rw [← hcomb] at hcomb_mem
            exact hcomb_mem
        rw [h_ext_eq, ih F'.card hF'_card F' rfl, h_conv_eq]
      · push Not at hex
        have heq : extremePointsFinset F = F := by
          ext p
          simp only [extremePointsFinset, Finset.mem_filter]
          exact ⟨fun h => h.1, fun hpF => ⟨hpF, hex p hpF⟩⟩
        rw [heq]
  exact h_ind F.card F rfl

/-- Hull vertices `B ⊆ Fin n` of `S`. -/
def hullVertices {n : ℕ} (S : Fin n → ℝ × ℝ) : Finset (Fin n) :=
  Finset.univ.filter (fun i =>
    S i ∉ convexHull ℝ (((Finset.univ.erase i).image S : Finset (ℝ × ℝ)) : Set (ℝ × ℝ)))

/-- Interior points `A = S \ B` (`interiorPoints S`). -/
def interiorPoints {n : ℕ} (S : Fin n → ℝ × ℝ) : Finset (Fin n) :=
  Finset.univ \ hullVertices S

lemma hullVertices_image_eq_extremePoints {n : ℕ} (S : Fin n → ℝ × ℝ) (hinj : Function.Injective S) :
    (hullVertices S).image S = extremePointsFinset (Finset.univ.image S) := by
  ext p
  simp only [hullVertices, extremePointsFinset, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
    true_and]
  constructor
  · rintro ⟨i, hi, rfl⟩
    refine ⟨⟨i, rfl⟩, fun hmem => hi ?_⟩
    have her : (Finset.univ.image S).erase (S i) = (Finset.univ.erase i).image S := by
      ext q
      simp only [Finset.mem_erase, Finset.mem_image, Finset.mem_univ, true_and, and_true]
      constructor
      · rintro ⟨hne, j, rfl⟩; exact ⟨j, fun hij => hne (congrArg S hij), rfl⟩
      · rintro ⟨j, hji, rfl⟩; exact ⟨fun h => hji (hinj h), j, rfl⟩
    rwa [← her]
  · rintro ⟨⟨i, rfl⟩, hi⟩
    refine ⟨i, fun hmem => hi ?_, rfl⟩
    have her : (Finset.univ.image S).erase (S i) = (Finset.univ.erase i).image S := by
      ext q
      simp only [Finset.mem_erase, Finset.mem_image, Finset.mem_univ, true_and, and_true]
      constructor
      · rintro ⟨hne, j, rfl⟩; exact ⟨j, fun hij => hne (congrArg S hij), rfl⟩
      · rintro ⟨j, hji, rfl⟩; exact ⟨fun h => hji (hinj h), j, rfl⟩
    rwa [her]

lemma hullVertices_convexHull_eq {n : ℕ} (S : Fin n → ℝ × ℝ) (hinj : Function.Injective S) :
    convexHull ℝ (((hullVertices S).image S : Finset (ℝ × ℝ)) : Set (ℝ × ℝ)) =
      convexHull ℝ (Set.range S) := by
  rw [hullVertices_image_eq_extremePoints S hinj, extremePointsFinset_convexHull_eq]
  simp [Finset.coe_image, Finset.coe_univ]

/-- Convex position of a finite planar point set `C`. -/
def IsConvexPos (C : Finset (ℝ × ℝ)) : Prop :=
  (∀ p ∈ C, p ∉ convexHull ℝ ((C.erase p : Finset (ℝ × ℝ)) : Set (ℝ × ℝ))) ∧
  (∀ x ∈ C, ∀ y ∈ C, ∀ z ∈ C, x ≠ y → y ≠ z → x ≠ z → orient2D x y z ≠ 0)

lemma hullVertices_isConvexPos {n : ℕ} {P : Set (ℝ × ℝ)} {S : Fin n → ℝ × ℝ}
    {w : Finset (Fin n) → ℝ × ℝ} (hP : ShatteredSimplePolygon P S w) :
    IsConvexPos ((hullVertices S).image S) := by
  rw [hullVertices_image_eq_extremePoints S hP.s_inj]
  refine ⟨fun p hp => ?_, fun x hx y hy z hz hxy hyz hxz => ?_⟩
  · have hmem := (Finset.mem_filter.mp hp).2
    intro hc
    apply hmem
    exact convexHull_mono (Finset.coe_subset.mpr (Finset.erase_subset_erase p (Finset.filter_subset _ _))) hc
  · have hx' : x ∈ Set.range S ∪ Set.range w := by
      have := (Finset.mem_filter.mp hx).1
      rcases Finset.mem_image.mp this with ⟨i, _, rfl⟩
      exact Or.inl ⟨i, rfl⟩
    have hy' : y ∈ Set.range S ∪ Set.range w := by
      have := (Finset.mem_filter.mp hy).1
      rcases Finset.mem_image.mp this with ⟨i, _, rfl⟩
      exact Or.inl ⟨i, rfl⟩
    have hz' : z ∈ Set.range S ∪ Set.range w := by
      have := (Finset.mem_filter.mp hz).1
      rcases Finset.mem_image.mp this with ⟨i, _, rfl⟩
      exact Or.inl ⟨i, rfl⟩
    exact hP.no_three_collinear x y z hx' hy' hz' hxy hyz hxz

lemma subset_isConvexPos {C D : Finset (ℝ × ℝ)} (hsub : C ⊆ D) (hD : IsConvexPos D) :
    IsConvexPos C := by
  refine ⟨fun p hp => ?_, fun x hx y hy z hz => hD.2 x (hsub hx) y (hsub hy) z (hsub hz)⟩
  intro hc
  apply hD.1 p (hsub hp)
  exact convexHull_mono (Finset.coe_subset.mpr (Finset.erase_subset_erase p hsub)) hc

lemma hullVertices_card_ge_three {n : ℕ} (hn : 3 ≤ n) {P : Set (ℝ × ℝ)}
    {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ} (hP : ShatteredSimplePolygon P S w) :
    3 ≤ (hullVertices S).card := by
  by_contra hlt
  have hle : (hullVertices S).card ≤ 2 := by omega
  have hmem_range : ∀ i : Fin n, S i ∈ convexHull ℝ (((hullVertices S).image S : Finset (ℝ × ℝ)) : Set (ℝ × ℝ)) := by
    intro i
    rw [hullVertices_convexHull_eq S hP.s_inj]
    exact subset_convexHull ℝ _ ⟨i, rfl⟩
  let i0 : Fin n := ⟨0, by omega⟩
  let i1 : Fin n := ⟨1, by omega⟩
  let i2 : Fin n := ⟨2, by omega⟩
  have hcol : orient2D (S i0) (S i1) (S i2) = 0 := by
    have hcard_img : ((hullVertices S).image S).card ≤ 2 :=
      le_trans Finset.card_image_le hle
    have hcases : ((hullVertices S).image S).card = 0 ∨ ((hullVertices S).image S).card = 1 ∨
        ((hullVertices S).image S).card = 2 := by omega
    rcases hcases with h0 | h1 | h2
    · rw [Finset.card_eq_zero.mp h0] at hmem_range
      simp at hmem_range
      exact False.elim (hmem_range i0)
    · obtain ⟨p, hp⟩ := Finset.card_eq_one.mp h1
      have h0p := hmem_range i0; have h1p := hmem_range i1
      rw [hp, Finset.coe_singleton, convexHull_singleton] at h0p h1p
      simp only [Set.mem_singleton_iff] at h0p h1p
      rw [h0p, h1p, orient2D_self_left]
    · obtain ⟨p, q, hpq, hpq_eq⟩ := Finset.card_eq_two.mp h2
      have h0p := hmem_range i0; have h1p := hmem_range i1; have h2p := hmem_range i2
      rw [hpq_eq, Finset.coe_insert, Finset.coe_singleton, convexHull_pair] at h0p h1p h2p
      rw [segment_eq_image] at h0p h1p h2p
      rcases h0p with ⟨t0, _, ht0⟩
      rcases h1p with ⟨t1, _, ht1⟩
      rcases h2p with ⟨t2, _, ht2⟩
      rw [← ht0, ← ht1, ← ht2]
      unfold orient2D
      simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
      ring
  have h01 : i0 ≠ i1 := by simp [i0, i1, Fin.ext_iff]
  have h12 : i1 ≠ i2 := by simp [i1, i2, Fin.ext_iff]
  have h02 : i0 ≠ i2 := by simp [i0, i2, Fin.ext_iff]
  exact hP.no_three_collinear (S i0) (S i1) (S i2) (Or.inl ⟨i0, rfl⟩) (Or.inl ⟨i1, rfl⟩)
    (Or.inl ⟨i2, rfl⟩) (fun h => h01 (hP.s_inj h)) (fun h => h12 (hP.s_inj h))
    (fun h => h02 (hP.s_inj h)) hcol

/-- Directed CCW hull edge `(a, b)` of a finite set `C`: `a, b ∈ C`, `a ≠ b`, and all other
    points of `C` lie strictly to the left of `a → b`. -/
def IsCCWHullEdge (C : Finset (ℝ × ℝ)) (a b : ℝ × ℝ) : Prop :=
  a ∈ C ∧ b ∈ C ∧ a ≠ b ∧ ∀ c ∈ C, c ≠ a → c ≠ b → 0 < orient2D a b c

/-- Front vertex of `C` from `v`: both incident CCW hull edges face `v`. -/
def IsFrontVertex (C : Finset (ℝ × ℝ)) (v f : ℝ × ℝ) : Prop :=
  ∃ b c : ℝ × ℝ, IsCCWHullEdge C b f ∧ IsCCWHullEdge C f c ∧
    orient2D b f v < 0 ∧ orient2D f c v < 0

/-- Back vertex of `C` from `v`: neither incident CCW hull edge faces `v`. -/
def IsBackVertex (C : Finset (ℝ × ℝ)) (v p : ℝ × ℝ) : Prop :=
  ∃ b c : ℝ × ℝ, IsCCWHullEdge C b p ∧ IsCCWHullEdge C p c ∧
    0 < orient2D b p v ∧ 0 < orient2D p c v

lemma isCCWHullEdge_succ_unique {C : Finset (ℝ × ℝ)} {a b₁ b₂ : ℝ × ℝ}
    (h1 : IsCCWHullEdge C a b₁) (h2 : IsCCWHullEdge C a b₂) : b₁ = b₂ := by
  by_contra hne
  have ho1 := h1.2.2.2 b₂ h2.2.1 h2.2.2.1.symm (Ne.symm hne)
  have ho2 := h2.2.2.2 b₁ h1.2.1 h1.2.2.1.symm hne
  rw [orient2D_swap23] at ho2
  linarith

lemma isCCWHullEdge_pred_unique {C : Finset (ℝ × ℝ)} {b₁ b₂ a : ℝ × ℝ}
    (h1 : IsCCWHullEdge C b₁ a) (h2 : IsCCWHullEdge C b₂ a) : b₁ = b₂ := by
  by_contra hne
  have ho1 := h1.2.2.2 b₂ h2.1 (Ne.symm hne) h2.2.2.1
  have ho2 := h2.2.2.2 b₁ h1.1 hne h1.2.2.1
  have : orient2D b₁ a b₂ = -orient2D b₂ a b₁ := by unfold orient2D; ring
  linarith

lemma isFrontVertex_iff_inOpenTri {C : Finset (ℝ × ℝ)} {v f b c : ℝ × ℝ}
    (hbf : IsCCWHullEdge C b f) (hfc : IsCCWHullEdge C f c) (hbc : b ≠ c) :
    (orient2D b f v < 0 ∧ orient2D f c v < 0) ↔ InOpenTri v b c f := by
  have h_ccw : 0 < orient2D f c b := by
    have h1 := hbf.2.2.2 c hfc.2.1 hbc.symm hfc.2.2.1.symm
    have heq : orient2D f c b = orient2D b f c := by unfold orient2D; ring
    linarith
  have heq : (orient2D b f v < 0 ∧ orient2D f c v < 0) ↔ v ∈ UCone f c b :=
    ((u_halfplanes h_ccw v).1).symm
  rw [heq, mem_uCone_iff_inOpenTri]
  constructor <;> exact inOpenTri_perm_23

lemma isFrontVertex_iff_inOpenTri' {C : Finset (ℝ × ℝ)} {v f b c : ℝ × ℝ}
    (hbf : IsCCWHullEdge C b f) (hfc : IsCCWHullEdge C f c) (hbc : b ≠ c) :
    IsFrontVertex C v f ↔ InOpenTri v b c f := by
  constructor
  · rintro ⟨b', c', hb'f, hfc', ho1, ho2⟩
    have hb_eq : b' = b := isCCWHullEdge_pred_unique hb'f hbf
    have hc_eq : c' = c := isCCWHullEdge_succ_unique hfc' hfc
    subst hb_eq hc_eq
    exact (isFrontVertex_iff_inOpenTri hbf hfc hbc).mp ⟨ho1, ho2⟩
  · intro htri
    obtain ⟨ho1, ho2⟩ := (isFrontVertex_iff_inOpenTri hbf hfc hbc).mpr htri
    exact ⟨b, c, hbf, hfc, ho1, ho2⟩

lemma isBackVertex_iff_cone {C : Finset (ℝ × ℝ)} {v p b c : ℝ × ℝ}
    (hbp : IsCCWHullEdge C b p) (hpc : IsCCWHullEdge C p c) (hbc : b ≠ c) :
    IsBackVertex C v p ↔ ∃ α β : ℝ, 0 < α ∧ 0 < β ∧ v = p + α • (b - p) + β • (c - p) := by
  have h_ccw : 0 < orient2D p c b := by
    have h1 := hbp.2.2.2 c hpc.2.1 hbc.symm hpc.2.2.1.symm
    have heq : orient2D p c b = orient2D b p c := by unfold orient2D; ring
    linarith
  have h_eq : (0 < orient2D b p v ∧ 0 < orient2D p c v) ↔
      ∃ α β : ℝ, 0 < α ∧ 0 < β ∧ v = p + α • (b - p) + β • (c - p) := by
    -- v = p + α(b - p) + β(c - p) iff (2p - v) ∈ UCone p c b!
    let v' : ℝ × ℝ := (2 * p.1 - v.1, 2 * p.2 - v.2)
    have hv1 : orient2D b p v' = -orient2D b p v := by unfold orient2D v'; ring
    have hv2 : orient2D p c v' = -orient2D p c v := by unfold orient2D v'; ring
    have hsub : (0 < orient2D b p v ∧ 0 < orient2D p c v) ↔ v' ∈ UCone p c b := by
      rw [(u_halfplanes h_ccw v').1, hv1, hv2]
      simp only [neg_lt_zero]
    rw [hsub]
    constructor
    · rintro ⟨β, α, hβ, hα, hv'⟩
      refine ⟨α, β, hα, hβ, ?_⟩
      ext
      · have h1 := congrArg Prod.fst hv'
        simp only [v', Prod.fst_add, Prod.smul_fst, Prod.fst_sub, smul_eq_mul] at h1 ⊢; linarith
      · have h2 := congrArg Prod.snd hv'
        simp only [v', Prod.snd_add, Prod.smul_snd, Prod.snd_sub, smul_eq_mul] at h2 ⊢; linarith
    · rintro ⟨α, β, hα, hβ, rfl⟩
      refine ⟨β, α, hβ, hα, ?_⟩
      ext <;> simp [v', smul_eq_mul] <;> ring
  constructor
  · rintro ⟨b', c', hb'p, hpc', ho1, ho2⟩
    have hb_eq : b' = b := isCCWHullEdge_pred_unique hb'p hbp
    have hc_eq : c' = c := isCCWHullEdge_succ_unique hpc' hpc
    subst hb_eq hc_eq
    exact h_eq.mp ⟨ho1, ho2⟩
  · intro hcone
    obtain ⟨ho1, ho2⟩ := h_eq.mpr hcone
    exact ⟨b, c, hbp, hpc, ho1, ho2⟩

/-- Lemma 3.2 (`Hidden targets`, `upper_9.tex` lines 296–308):
    If `T ⊆ B` and every `t ∈ T` has `b_t, c_t ∈ B \ T` and a witness `v_t` seeing `b_t, c_t`,
    missing `t`, with `t ∈ interior Δ(v_t, b_t, c_t)`, then `|A| + |T| ≤ 5` (and `|A| ≤ 5`). -/
theorem hidden_targets {n : ℕ} {P : Set (ℝ × ℝ)} {S : Fin n → ℝ × ℝ}
    {w : Finset (Fin n) → ℝ × ℝ}
    (hP : ShatteredSimplePolygon P S w)
    (T : Finset (Fin n)) (hTB : T ⊆ hullVertices S)
    (htarg : ∀ t ∈ T, ∃ bt ∈ hullVertices S \ T, ∃ ct ∈ hullVertices S \ T,
      ∃ vt : Finset (Fin n), Sees P (w vt) (S bt) ∧ Sees P (w vt) (S ct) ∧
        ¬ Sees P (w vt) (S t) ∧ InOpenTri (w vt) (S bt) (S ct) (S t)) :
    (interiorPoints S).card + T.card ≤ 5 := by
  let B := hullVertices S
  let A := interiorPoints S
  let F := B \ T
  have hT_tests : ∀ t ∈ T, ∃ R : OpenWedge, IsWedgeTest P (WitnessSet F ∅ w) (S t) R := by
    intro t ht
    obtain ⟨bt, hbtF, ct, hctF, vt, hvbt, hvct, hvnt, htri⟩ := htarg t ht
    have hbt_in : bt ∈ vt := (hP.shatters vt bt).mp hvbt
    have hct_in : ct ∈ vt := (hP.shatters vt ct).mp hvct
    have ht_notin : t ∉ vt := fun h => hvnt ((hP.shatters vt t).mpr h)
    have hF_sub : ({bt, ct} : Finset (Fin n)) ⊆ vt :=
      Finset.insert_subset_iff.mpr ⟨hbt_in, Finset.singleton_subset_iff.mpr hct_in⟩
    have h_conv : S t ∈ convexHull ℝ (insert (w vt) (({bt, ct} : Finset (Fin n)).image S : Set (ℝ × ℝ))) := by
      have htri_mem := inOpenTri_mem_convexHull htri
      apply convexHull_mono _ htri_mem
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl | rfl
      · exact Set.mem_insert _ _
      · exact Set.mem_insert_of_mem _ (Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨bt, by simp, rfl⟩))
      · exact Set.mem_insert_of_mem _ (Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨ct, by simp, rfl⟩))
    obtain ⟨R, _, hRtest⟩ := fan hP hF_sub ht_notin h_conv
    have hW_sub : WitnessSet F ∅ w ⊆ WitnessSet {bt, ct} ∅ w :=
      witnessSet_mono (Finset.insert_subset_iff.mpr ⟨hbtF, Finset.singleton_subset_iff.mpr hctF⟩)
        (Finset.Subset.refl _)
    exact ⟨R, isWedgeTest_mono hW_sub hRtest⟩
  have hB_in_conv : convexHull ℝ ((B.image S : Finset (ℝ × ℝ)) : Set (ℝ × ℝ)) ⊆
      convexHull ℝ (insert (w B) (F.image S : Set (ℝ × ℝ))) := by
    apply convexHull_min _ (convex_convexHull ℝ _)
    intro p hp
    rcases Finset.mem_image.mp hp with ⟨b, hbB, rfl⟩
    by_cases hbT : b ∈ T
    · obtain ⟨bt, hbtF, ct, hctF, vt, hvbt, hvct, hvnt, htri⟩ := htarg b hbT
      have hbtB : bt ∈ B := (Finset.mem_sdiff.mp hbtF).1
      have hctB : ct ∈ B := (Finset.mem_sdiff.mp hctF).1
      have hwB_bt : Sees P (w B) (S bt) := (hP.shatters B bt).mpr hbtB
      have hwB_ct : Sees P (w B) (S ct) := (hP.shatters B ct).mpr hctB
      have hwB_ne_vt : w B ≠ w vt := fun heq => hvnt (by
        rw [← hP.w_inj heq]; exact (hP.shatters B b).mpr hbB)
      have h_b_ne_bt : b ≠ bt := fun heq => ((Finset.mem_sdiff.mp hbtF).2) (heq ▸ hbT)
      have h_b_ne_ct : b ≠ ct := fun heq => ((Finset.mem_sdiff.mp hctF).2) (heq ▸ hbT)
      have hwB_in_U : w B ∈ UCone (S b) (S bt) (S ct) := by
        apply cone hP.toEnclosureDomain hvbt hvct hvnt htri hwB_bt hwB_ct
        · exact hP.no_three_collinear (S b) (S bt) (w B) (Or.inl ⟨b, rfl⟩) (Or.inl ⟨bt, rfl⟩)
            (Or.inr ⟨B, rfl⟩) (fun h => h_b_ne_bt (hP.s_inj h)) (hP.s_ne_w bt B) (hP.s_ne_w b B)
        · exact hP.no_three_collinear (S b) (S ct) (w B) (Or.inl ⟨b, rfl⟩) (Or.inl ⟨ct, rfl⟩)
            (Or.inr ⟨B, rfl⟩) (fun h => h_b_ne_ct (hP.s_inj h)) (hP.s_ne_w ct B) (hP.s_ne_w b B)
        · exact hP.no_three_collinear (w vt) (S b) (w B) (Or.inr ⟨vt, rfl⟩) (Or.inl ⟨b, rfl⟩)
            (Or.inr ⟨B, rfl⟩) (hP.s_ne_w b vt).symm (hP.s_ne_w b B) hwB_ne_vt.symm
      have h_tri_wB := inOpenTri_mem_convexHull ((mem_uCone_iff_inOpenTri (S b) (S bt) (S ct) (w B)).mp hwB_in_U)
      apply convexHull_mono _ h_tri_wB
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl | rfl
      · exact Set.mem_insert _ _
      · exact Set.mem_insert_of_mem _ (Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨bt, hbtF, rfl⟩))
      · exact Set.mem_insert_of_mem _ (Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨ct, hctF, rfl⟩))
    · have hbF : b ∈ F := Finset.mem_sdiff.mpr ⟨hbB, hbT⟩
      exact subset_convexHull ℝ _ (Set.mem_insert_of_mem _ (Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨b, hbF, rfl⟩)))
  have hA_tests : ∀ a ∈ A, ∃ R : OpenWedge, IsWedgeTest P (WitnessSet F ∅ w) (S a) R := by
    intro a haA
    have ha_notin_B : a ∉ B := (Finset.mem_sdiff.mp haA).2
    have ha_conv : S a ∈ convexHull ℝ (insert (w B) (F.image S : Set (ℝ × ℝ))) := by
      apply hB_in_conv
      rw [hullVertices_convexHull_eq S hP.s_inj]
      exact subset_convexHull ℝ _ ⟨a, rfl⟩
    obtain ⟨R, _, hRtest⟩ := fan hP Finset.sdiff_subset ha_notin_B ha_conv
    exact ⟨R, hRtest⟩
  let M_all := A ∪ T
  have hdisj_AT : Disjoint A T :=
    Finset.disjoint_left.mpr (fun x hxA hxT => (Finset.mem_sdiff.mp hxA).2 (hTB hxT))
  have hcard_eq : M_all.card = A.card + T.card := Finset.card_union_of_disjoint hdisj_AT
  by_contra hgt
  have h6 : 6 ≤ M_all.card := by
    dsimp [A] at hcard_eq
    rw [hcard_eq]
    omega
  obtain ⟨U, hU_sub, hU_card⟩ := Finset.exists_subset_card_eq h6
  let e := U.equivFin
  let a : Fin 6 → Fin n := fun i => (e.symm (Fin.cast hU_card.symm i)).1
  have ha_inj : Function.Injective a := by
    intro i j hij
    have heq : e.symm (Fin.cast hU_card.symm i) = e.symm (Fin.cast hU_card.symm j) :=
      Subtype.ext hij
    have hcast : Fin.cast hU_card.symm i = Fin.cast hU_card.symm j := e.symm.injective heq
    exact Fin.ext (by simpa using congrArg Fin.val hcast)
  have ha_out : ∀ i : Fin 6, a i ∉ F ∧ a i ∉ (∅ : Finset (Fin n)) := by
    intro i
    refine ⟨fun hF => ?_, Finset.notMem_empty _⟩
    have hm : a i ∈ M_all := hU_sub (e.symm (Fin.cast hU_card.symm i)).2
    have hB : a i ∈ B := (Finset.mem_sdiff.mp hF).1
    have hnotT : a i ∉ T := (Finset.mem_sdiff.mp hF).2
    rcases Finset.mem_union.mp hm with hA | hT
    · exact (Finset.mem_sdiff.mp hA).2 hB
    · exact hnotT hT
  have hR_exists : ∀ i : Fin 6, ∃ R : OpenWedge, IsWedgeTest P (WitnessSet F ∅ w) (S (a i)) R := by
    intro i
    have hm : a i ∈ M_all := hU_sub (e.symm (Fin.cast hU_card.symm i)).2
    rcases Finset.mem_union.mp hm with hA | hT
    · exact hA_tests (a i) hA
    · exact hT_tests (a i) hT
  choose R hR using hR_exists
  exact no_six_wedge_tests hP (Finset.disjoint_empty_right F) a ha_inj ha_out R hR

/-- Lemma 3.3 (`Hidden front vertex`, `upper_9.tex` lines 324–334). -/
theorem hidden_front_vertex {n : ℕ} {P : Set (ℝ × ℝ)} {S : Fin n → ℝ × ℝ}
    {w : Finset (Fin n) → ℝ × ℝ}
    (hP : ShatteredSimplePolygon P S w)
    (C : Finset (Fin n)) (_hCB : C ⊆ hullVertices S) (hC3 : 3 ≤ C.card)
    (v_idx : Finset (Fin n)) {f b c : Fin n}
    (_hf : f ∈ C) (_hb : b ∈ C) (_hc : c ∈ C)
    (hbf : IsCCWHullEdge (C.image S) (S b) (S f))
    (hfc : IsCCWHullEdge (C.image S) (S f) (S c))
    (hv_front : IsFrontVertex (C.image S) (w v_idx) (S f))
    (hvb : Sees P (w v_idx) (S b)) (hwc : Sees P (w v_idx) (S c))
    (hnvf : ¬ Sees P (w v_idx) (S f)) :
    InOpenTri (w v_idx) (S b) (S c) (S f) ∧
    ∀ x_idx : Finset (Fin n), Sees P (w x_idx) (S b) → Sees P (w x_idx) (S c) →
      InOpenTri (w x_idx) (S b) (S c) (S f) ∧ IsFrontVertex (C.image S) (w x_idx) (S f) := by
  have hbc : S b ≠ S c := by
    intro hbc_eq
    have hbc' : b = c := hP.s_inj hbc_eq
    subst hbc'
    have hC_img_card : 3 ≤ (C.image S).card := by
      rwa [Finset.card_image_of_injective C hP.s_inj]
    obtain ⟨d, hd_mem, hdb, hdf⟩ : ∃ d ∈ C.image S, d ≠ S b ∧ d ≠ S f := by
      have hsub_ne : (C.image S).card > ({S b, S f} : Finset (ℝ × ℝ)).card := by
        have : ({S b, S f} : Finset (ℝ × ℝ)).card ≤ 2 := Finset.card_le_two
        omega
      obtain ⟨d, hd1, hd2⟩ := Finset.exists_mem_notMem_of_card_lt_card hsub_ne
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hd2
      exact ⟨d, hd1, hd2.1, hd2.2⟩
    have h1 := hbf.2.2.2 d hd_mem hdb hdf
    have h2 := hfc.2.2.2 d hd_mem hdf hdb
    have : orient2D (S b) (S f) d = -orient2D (S f) (S b) d := by unfold orient2D; ring
    linarith
  have htri : InOpenTri (w v_idx) (S b) (S c) (S f) :=
    (isFrontVertex_iff_inOpenTri' hbf hfc hbc).mp hv_front
  refine ⟨htri, fun x_idx hxb hxc => ?_⟩
  have hx_tri : InOpenTri (w x_idx) (S b) (S c) (S f) := by
    by_cases hx_eq : x_idx = v_idx
    · subst hx_eq; exact htri
    · have hfb_ne : f ≠ b := fun h => hbf.2.2.1 (congrArg S h).symm
      have hfc_ne : f ≠ c := fun h => hfc.2.2.1 (congrArg S h)
      have hxU : w x_idx ∈ UCone (S f) (S b) (S c) := by
        apply cone hP.toEnclosureDomain hvb hwc hnvf htri hxb hxc
        · exact hP.no_three_collinear (S f) (S b) (w x_idx) (Or.inl ⟨f, rfl⟩) (Or.inl ⟨b, rfl⟩)
            (Or.inr ⟨x_idx, rfl⟩) (fun h => hfb_ne (hP.s_inj h)) (hP.s_ne_w b x_idx) (hP.s_ne_w f x_idx)
        · exact hP.no_three_collinear (S f) (S c) (w x_idx) (Or.inl ⟨f, rfl⟩) (Or.inl ⟨c, rfl⟩)
            (Or.inr ⟨x_idx, rfl⟩) (fun h => hfc_ne (hP.s_inj h)) (hP.s_ne_w c x_idx) (hP.s_ne_w f x_idx)
        · exact hP.no_three_collinear (w v_idx) (S f) (w x_idx) (Or.inr ⟨v_idx, rfl⟩) (Or.inl ⟨f, rfl⟩)
            (Or.inr ⟨x_idx, rfl⟩) (hP.s_ne_w f v_idx).symm (hP.s_ne_w f x_idx)
            (fun h => hx_eq (hP.w_inj h).symm)
      exact (mem_uCone_iff_inOpenTri (S f) (S b) (S c) (w x_idx)).mp hxU
  exact ⟨hx_tri, (isFrontVertex_iff_inOpenTri' hbf hfc hbc).mpr hx_tri⟩

/-- Lemma 3.4 (`Front restoration`, `upper_9.tex` lines 338–344):
    If `C ⊆ D ⊆ S` are in convex position and `f ∈ C` is a front vertex of `C` from `v`,
    then `f` is a front vertex of `D` from `v`. -/
theorem front_restoration {C D : Finset (ℝ × ℝ)} {v f : ℝ × ℝ}
    (hCD : C ⊆ D) (_hD_conv : IsConvexPos D) (_hfC : f ∈ C)
    (hfront : IsFrontVertex C v f)
    {b' c' : ℝ × ℝ} (hb'f : IsCCWHullEdge D b' f) (hfc' : IsCCWHullEdge D f c') :
    IsFrontVertex D v f := by
  rcases hfront with ⟨b, c, hbf, hfc, hbv, hcv⟩
  have hbc : b ≠ c := by
    intro heq
    subst heq
    have h1 := hbf.2.2.2 v
    --Wait: v might not be in C! Instead check if C has ≥3 points or b=c is impossible:
    --If b = c, then hbf gives b ≠ f, and IsFrontVertex has orient2D b f v < 0 and orient2D f b v < 0!
    have : orient2D f b v = -orient2D b f v := by unfold orient2D; ring
    linarith
  have htri : InOpenTri v b c f := (isFrontVertex_iff_inOpenTri hbf hfc hbc).mp ⟨hbv, hcv⟩
  have hv_cone : v ∈ UCone f b c := (mem_uCone_iff_inOpenTri f b c v).mpr htri
  rcases hv_cone with ⟨α, β, hα, hβ, rfl⟩
  have hbD : b ∈ D := hCD hbf.1
  have hcD : c ∈ D := hCD hfc.2.1
  have h_b'f_nonneg : ∀ q ∈ D, q ≠ f → 0 ≤ orient2D b' f q := by
    intro q hqD hqf
    by_cases hqb' : q = b'
    · rw [hqb', orient2D_self_outer]
    · exact le_of_lt (hb'f.2.2.2 q hqD hqb' hqf)
  have h_fc'_nonneg : ∀ q ∈ D, q ≠ f → 0 ≤ orient2D f c' q := by
    intro q hqD hqf
    by_cases hqc' : q = c'
    · rw [hqc', orient2D_self_right]
    · exact le_of_lt (hfc'.2.2.2 q hqD hqf hqc')
  have hb_pos_or_hc_pos_1 : 0 < orient2D b' f b + orient2D b' f c := by
    have h1 := h_b'f_nonneg b hbD hbf.2.2.1
    have h2 := h_b'f_nonneg c hcD hfc.2.2.1.symm
    by_cases hbb' : b = b'
    · have hcb' : c ≠ b' := fun h => hbc (hbb'.trans h.symm)
      have h2' := hb'f.2.2.2 c hcD hcb' hfc.2.2.1.symm
      linarith
    · have h1' := hb'f.2.2.2 b hbD hbb' hbf.2.2.1
      linarith
  have hb_pos_or_hc_pos_2 : 0 < orient2D f c' b + orient2D f c' c := by
    have h1 := h_fc'_nonneg b hbD hbf.2.2.1
    have h2 := h_fc'_nonneg c hcD hfc.2.2.1.symm
    by_cases hbc' : b = c'
    · have hcc' : c ≠ c' := fun h => hbc (hbc'.trans h.symm)
      have h2' := hfc'.2.2.2 c hcD hfc.2.2.1.symm hcc'
      linarith
    · have h1' := hfc'.2.2.2 b hbD hbf.2.2.1 hbc'
      linarith
  have h1_lt : orient2D b' f (f + α • (f - b) + β • (f - c)) < 0 := by
    have hid : orient2D b' f (f + α • (f - b) + β • (f - c)) =
        -(α * orient2D b' f b + β * orient2D b' f c) := by
      unfold orient2D
      simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
        Prod.fst_sub, Prod.snd_sub, smul_eq_mul]
      ring
    rw [hid]
    have h1 := h_b'f_nonneg b hbD hbf.2.2.1
    have h2 := h_b'f_nonneg c hcD hfc.2.2.1.symm
    rcases lt_or_eq_of_le h1 with h1p | h1z
    · nlinarith
    · have h2p : 0 < orient2D b' f c := by linarith
      nlinarith
  have h2_lt : orient2D f c' (f + α • (f - b) + β • (f - c)) < 0 := by
    have hid : orient2D f c' (f + α • (f - b) + β • (f - c)) =
        -(α * orient2D f c' b + β * orient2D f c' c) := by
      unfold orient2D
      simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
        Prod.fst_sub, Prod.snd_sub, smul_eq_mul]
      ring
    rw [hid]
    have h1 := h_fc'_nonneg b hbD hbf.2.2.1
    have h2 := h_fc'_nonneg c hcD hfc.2.2.1.symm
    rcases lt_or_eq_of_le h1 with h1p | h1z
    · nlinarith
    · have h2p : 0 < orient2D f c' c := by linarith
      nlinarith
  exact ⟨b', c', hb'f, hfc', h1_lt, h2_lt⟩

/-! ## Cyclic CCW Boundary, Near/Far Chains, and Single Sign-Change -/

lemma inOpenTri_of_orient_pos {a b c x : ℝ × ℝ}
    (habc : 0 < orient2D a b c)
    (habx : 0 < orient2D a b x) (hbcx : 0 < orient2D b c x) (hcax : 0 < orient2D c a x) :
    InOpenTri a b c x := by
  have hsum_or : orient2D b c x + orient2D c a x + orient2D a b x = orient2D a b c := by
    unfold orient2D; ring
  have hdet_ne : orient2D a b c ≠ 0 := ne_of_gt habc
  refine ⟨orient2D b c x / orient2D a b c, orient2D c a x / orient2D a b c,
    orient2D a b x / orient2D a b c,
    div_pos hbcx habc, div_pos hcax habc, div_pos habx habc, ?_, ?_, ?_⟩
  · field_simp [hdet_ne]; linarith
  · field_simp [hdet_ne]; unfold orient2D; ring
  · field_simp [hdet_ne]; unfold orient2D; ring

/-- Strict cyclic counterclockwise order on `Fin N`. -/
def CyclicOrder {N : ℕ} (i j k : Fin N) : Prop :=
  (i < j ∧ j < k) ∨ (j < k ∧ k < i) ∨ (k < i ∧ i < j)

lemma cyclicOrder_cycle {N : ℕ} {i j k : Fin N} (h : CyclicOrder i j k) :
    CyclicOrder j k i := by
  rcases h with h1 | h2 | h3
  · exact Or.inr (Or.inr h1)
  · exact Or.inl h2
  · exact Or.inr (Or.inl h3)

lemma cyclicOrder_pair_ne {N : ℕ} {i j k : Fin N} (h : CyclicOrder i j k) :
    i ≠ j ∧ j ≠ k ∧ k ≠ i := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨ne_of_lt h1, ne_of_lt h2, ne_of_gt (lt_trans h1 h2)⟩
  · exact ⟨ne_of_gt (lt_trans h1 h2), ne_of_lt h1, ne_of_lt h2⟩
  · exact ⟨ne_of_lt h2, ne_of_gt (lt_trans h1 h2), ne_of_lt h1⟩

lemma cyclicOrder_succ {N : ℕ} (hN : 3 ≤ N) {i j : Fin N} (hji : j ≠ i)
    (hj1 : j ≠ i + ⟨1 % N, Nat.mod_lt 1 (by omega)⟩) :
    CyclicOrder i (i + ⟨1 % N, Nat.mod_lt 1 (by omega)⟩) j := by
  haveI : NeZero N := ⟨by omega⟩
  have hi_lt : i.val < N := i.isLt
  have hj_lt : j.val < N := j.isLt
  have hne1 : j.val ≠ i.val := fun h => hji (Fin.ext h)
  have h1val : (⟨1 % N, Nat.mod_lt 1 (by omega)⟩ : Fin N).val = 1 := Nat.mod_eq_of_lt (by omega)
  have hsumval : (i + ⟨1 % N, Nat.mod_lt 1 (by omega)⟩ : Fin N).val = (i.val + 1) % N := by
    rw [Fin.val_add, h1val]
  have hne2 : j.val ≠ (i.val + 1) % N := fun h => hj1 (Fin.ext (h.trans hsumval.symm))
  change (i.val < (i + ⟨1 % N, Nat.mod_lt 1 (by omega)⟩ : Fin N).val ∧
      (i + ⟨1 % N, Nat.mod_lt 1 (by omega)⟩ : Fin N).val < j.val) ∨
    ((i + ⟨1 % N, Nat.mod_lt 1 (by omega)⟩ : Fin N).val < j.val ∧ j.val < i.val) ∨
    (j.val < i.val ∧ i.val < (i + ⟨1 % N, Nat.mod_lt 1 (by omega)⟩ : Fin N).val)
  rw [hsumval]
  by_cases hwrap : i.val + 1 < N
  · rw [Nat.mod_eq_of_lt hwrap] at hne2 ⊢
    omega
  · have hi_max : i.val + 1 = N := by omega
    rw [hi_max, Nat.mod_self] at hne2 ⊢
    omega

/-- Cyclic shift on `Fin N` by `k : ℕ`. -/
def finShift {N : ℕ} [NeZero N] (i : Fin N) (k : ℕ) : Fin N :=
  ⟨(i.val + k) % N, Nat.mod_lt _ (NeZero.pos N)⟩

@[simp] lemma finShift_zero {N : ℕ} [NeZero N] (i : Fin N) : finShift i 0 = i := by
  ext; simp [finShift, Nat.mod_eq_of_lt i.isLt]

lemma finShift_eq_add {N : ℕ} [NeZero N] (i : Fin N) {k : ℕ} (hk : k < N) :
    finShift i k = i + ⟨k, hk⟩ := by
  ext; simp [finShift, Fin.val_add]

lemma finShift_one {N : ℕ} [NeZero N] (hN : 2 ≤ N) (i : Fin N) :
    finShift i 1 = i + 1 := by
  rw [finShift_eq_add i (by omega : 1 < N)]
  congr 1
  exact Fin.ext (Nat.mod_eq_of_lt (by omega)).symm

lemma finShift_succ {N : ℕ} [NeZero N] (hN : 2 ≤ N) (i : Fin N) (k : ℕ) :
    finShift i k + 1 = finShift i (k + 1) := by
  ext
  have h1 : (1 : Fin N).val = 1 := by
    change 1 % N = 1
    exact Nat.mod_eq_of_lt (by omega)
  simp only [finShift, Fin.val_add, h1]
  rw [Nat.mod_add_mod, Nat.add_assoc]

lemma finShift_pred {N : ℕ} [NeZero N] (hN : 2 ≤ N) (i : Fin N) (k : ℕ) :
    finShift i (k + 1) - 1 = finShift i k := by
  rw [← finShift_succ hN i k, add_sub_cancel_right]

lemma finShift_len {N : ℕ} [NeZero N] (i : Fin N) : finShift i N = i := by
  ext; simp [finShift, Nat.mod_eq_of_lt i.isLt]

lemma finShift_sub {N : ℕ} [NeZero N] (i j : Fin N) :
    finShift i (j - i).val = j := by
  rw [finShift_eq_add i (j - i).isLt]
  exact add_sub_cancel i j

private lemma hahn_banach_dir {p₀ : ℝ × ℝ} {R : Finset (ℝ × ℝ)}
    (hR_ne : R.Nonempty) (hp_not : p₀ ∉ convexHull ℝ (R : Set (ℝ × ℝ))) :
    ∃ e₁ e₂ : ℝ, 0 < e₁ ^ 2 + e₂ ^ 2 ∧
      ∀ q ∈ R, 0 < e₁ * (q.1 - p₀.1) + e₂ * (q.2 - p₀.2) := by
  have hK_closed : IsClosed (convexHull ℝ (R : Set (ℝ × ℝ))) :=
    ((R.finite_toSet).isCompact_convexHull ℝ).isClosed
  obtain ⟨φ, u, hφp, huK⟩ :=
    geometric_hahn_banach_point_closed (convex_convexHull ℝ _) hK_closed hp_not
  let e₁ : ℝ := φ (1, 0)
  let e₂ : ℝ := φ (0, 1)
  have hφ_eq : ∀ d : ℝ × ℝ, φ d = e₁ * d.1 + e₂ * d.2 := by
    intro d
    have hd : d = d.1 • ((1 : ℝ), (0 : ℝ)) + d.2 • ((0 : ℝ), (1 : ℝ)) := by
      ext <;> simp
    conv_lhs => rw [hd]
    rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
    dsimp [e₁, e₂]
    ring
  have hpos : ∀ q ∈ R, 0 < e₁ * (q.1 - p₀.1) + e₂ * (q.2 - p₀.2) := by
    intro q hqR
    have hqK : q ∈ convexHull ℝ (R : Set (ℝ × ℝ)) := subset_convexHull ℝ _ hqR
    have hlt : φ p₀ < φ q := lt_trans hφp (huK q hqK)
    have hdiff : 0 < φ (q - p₀) := by rw [map_sub]; linarith
    simpa [hφ_eq (q - p₀)] using hdiff
  rcases hR_ne with ⟨q₀, hq₀⟩
  have hq0_pos := hpos q₀ hq₀
  have hsq : 0 < e₁ ^ 2 + e₂ ^ 2 := by
    by_contra hle
    have he1 : e₁ = 0 := by nlinarith [sq_nonneg e₁, sq_nonneg e₂]
    have he2 : e₂ = 0 := by nlinarith [sq_nonneg e₁, sq_nonneg e₂]
    rw [he1, he2] at hq0_pos
    linarith
  exact ⟨e₁, e₂, hsq, hpos⟩

/-- Every finite convex-position set `C` with `C.card = m + 3` admits a counterclockwise
    cyclic enumeration `p : Fin (m + 3) → ℝ × ℝ` with `StrictConvexCCWPoly p` and strict
    positivity on all cyclically ordered triples. -/
theorem strictConvexCCWPoly_of_isConvexPos {C : Finset (ℝ × ℝ)} {m : ℕ}
    (hC : IsConvexPos C) (hcard : C.card = m + 3) :
    ∃ p : Fin (m + 3) → ℝ × ℝ,
      StrictConvexCCWPoly p ∧ Function.Injective p ∧ Finset.univ.image p = C ∧
      ∀ i j k : Fin (m + 3), CyclicOrder i j k → 0 < orient2D (p i) (p j) (p k) := by
  have hC_ne : C.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨p₀, hp0⟩ := hC_ne
  let R := C.erase p₀
  have hR_card : R.card = m + 2 := by
    dsimp [R]; rw [Finset.card_erase_of_mem hp0, hcard]; omega
  have hR_ne : R.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨e₁, e₂, hsq, hpos⟩ := hahn_banach_dir hR_ne (hC.1 p₀ hp0)
  let dot₁ : ℝ × ℝ → ℝ := fun q => e₁ * (q.1 - p₀.1) + e₂ * (q.2 - p₀.2)
  let dot₂ : ℝ × ℝ → ℝ := fun q => (-e₂) * (q.1 - p₀.1) + e₁ * (q.2 - p₀.2)
  let key : ℝ × ℝ → ℝ := fun q => dot₂ q / dot₁ q
  have h_orient_key : ∀ q q' : ℝ × ℝ,
      (e₁ ^ 2 + e₂ ^ 2) * orient2D p₀ q q' = dot₁ q * dot₂ q' - dot₂ q * dot₁ q' := by
    intro q q'
    dsimp [dot₁, dot₂, orient2D]
    ring
  have h_pos_iff : ∀ q ∈ R, ∀ q' ∈ R, 0 < orient2D p₀ q q' ↔ key q < key q' := by
    intro q hq q' hq'
    have hd1 : 0 < dot₁ q := hpos q hq
    have hd2 : 0 < dot₁ q' := hpos q' hq'
    have hid := h_orient_key q q'
    constructor
    · intro ho
      have hmul : 0 < (e₁ ^ 2 + e₂ ^ 2) * orient2D p₀ q q' := mul_pos hsq ho
      dsimp [key]
      rw [div_lt_div_iff₀ hd1 hd2]
      linarith
    · intro hlt
      dsimp [key] at hlt
      rw [div_lt_div_iff₀ hd1 hd2] at hlt
      have hmul : 0 < (e₁ ^ 2 + e₂ ^ 2) * orient2D p₀ q q' := by linarith
      exact pos_of_mul_pos_right hmul (le_of_lt hsq)
  have hkey_inj : Set.InjOn key (R : Set (ℝ × ℝ)) := by
    intro q hq q' hq' heq
    by_contra hne
    have hqC : q ∈ C := (Finset.mem_erase.mp hq).2
    have hq'C : q' ∈ C := (Finset.mem_erase.mp hq').2
    have hqp : p₀ ≠ q := (Finset.mem_erase.mp hq).1.symm
    have hq'p : p₀ ≠ q' := (Finset.mem_erase.mp hq').1.symm
    have hne0 := hC.2 p₀ hp0 q hqC q' hq'C hqp hne hq'p
    rcases lt_or_gt_of_ne hne0 with hlt | hgt
    · have hgt' : 0 < orient2D p₀ q' q := by rw [orient2D_swap23]; linarith
      have hlt_key := (h_pos_iff q' hq' q hq).mp hgt'
      linarith
    · have hlt_key := (h_pos_iff q hq q' hq').mp hgt
      linarith
  let L := (R.image key).sort (· ≤ ·)
  have hL_len : L.length = m + 2 := by
    dsimp [L]
    rw [Finset.length_sort, Finset.card_image_of_injOn hkey_inj, hR_card]
  have hL_sorted : L.SortedLT := Finset.sortedLT_sort (R.image key)
  have hL_mem : ∀ k : Fin (m + 2), ∃ q ∈ R, key q = L[k.val]'(by rw [hL_len]; exact k.isLt) := by
    intro k
    have hmem : L[k.val]'(by rw [hL_len]; exact k.isLt) ∈ R.image key := by
      rw [← Finset.mem_sort (· ≤ ·)]
      exact List.getElem_mem _
    rcases Finset.mem_image.mp hmem with ⟨q, hqR, hqk⟩
    exact ⟨q, hqR, hqk⟩
  choose qFn hqFn_mem hqFn_key using hL_mem
  have hL_lt : ∀ k₁ k₂ : Fin (m + 2), k₁ < k₂ →
      L[k₁.val]'(by rw [hL_len]; exact k₁.isLt) < L[k₂.val]'(by rw [hL_len]; exact k₂.isLt) := by
    intro k₁ k₂ hlt
    have hcast : Fin.cast hL_len.symm k₁ < Fin.cast hL_len.symm k₂ := hlt
    simpa [List.get_eq_getElem] using hL_sorted hcast
  have hqFn_inj : Function.Injective qFn := by
    intro k₁ k₂ heq
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have hget := hL_lt k₁ k₂ hlt
      rw [← hqFn_key k₁, ← hqFn_key k₂, heq] at hget
      exact lt_irrefl _ hget
    · have hget := hL_lt k₂ k₁ hlt
      rw [← hqFn_key k₁, ← hqFn_key k₂, heq] at hget
      exact lt_irrefl _ hget
  have hqFn_orient : ∀ k₁ k₂ : Fin (m + 2), k₁ < k₂ → 0 < orient2D p₀ (qFn k₁) (qFn k₂) := by
    intro k₁ k₂ hlt
    apply (h_pos_iff _ (hqFn_mem k₁) _ (hqFn_mem k₂)).mpr
    rw [hqFn_key k₁, hqFn_key k₂]
    exact hL_lt k₁ k₂ hlt
  let p : Fin (m + 3) → ℝ × ℝ := fun i =>
    if hi : i.val = 0 then p₀ else qFn ⟨i.val - 1, by omega⟩
  have hp_mem : ∀ i : Fin (m + 3), p i ∈ C := by
    intro i
    dsimp [p]
    split_ifs with hi
    · exact hp0
    · exact (Finset.mem_erase.mp (hqFn_mem ⟨i.val - 1, by omega⟩)).2
  have hp_inj : Function.Injective p := by
    intro i j hij
    dsimp [p] at hij
    split_ifs at hij with hi hj
    · exact Fin.ext (hi.trans hj.symm)
    · exfalso
      have hm := hqFn_mem ⟨j.val - 1, by omega⟩
      rw [← hij] at hm
      exact (Finset.mem_erase.mp hm).1 rfl
    · exfalso
      have hm := hqFn_mem ⟨i.val - 1, by omega⟩
      rw [hij] at hm
      exact (Finset.mem_erase.mp hm).1 rfl
    · have hk := hqFn_inj hij
      have hval := congrArg Fin.val hk
      simp only at hval
      exact Fin.ext (by omega)
  have hp_img : Finset.univ.image p = C := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      rcases Finset.mem_image.mp hx with ⟨i, _, rfl⟩
      exact hp_mem i
    · rw [Finset.card_image_of_injective Finset.univ hp_inj, Finset.card_univ, Fintype.card_fin, hcard]
  have h_ord_pos : ∀ i j k : Fin (m + 3), i < j → j < k → 0 < orient2D (p i) (p j) (p k) := by
    intro i j k hij hjk
    have hi0_or : i.val = 0 ∨ 0 < i.val := Nat.eq_zero_or_pos i.val
    rcases hi0_or with hi0 | hi_pos
    · have hj_ne : j.val ≠ 0 := by omega
      have hk_ne : k.val ≠ 0 := by omega
      have hp_eq0 : p i = p₀ := by dsimp [p]; simp [hi0]
      have hp_eqj : p j = qFn ⟨j.val - 1, by omega⟩ := by dsimp [p]; simp [hj_ne]
      have hp_eqk : p k = qFn ⟨k.val - 1, by omega⟩ := by dsimp [p]; simp [hk_ne]
      rw [hp_eq0, hp_eqj, hp_eqk]
      exact hqFn_orient ⟨j.val - 1, by omega⟩ ⟨k.val - 1, by omega⟩ (by simp [Fin.lt_def]; omega)
    · have hj_ne : j.val ≠ 0 := by omega
      have hk_ne : k.val ≠ 0 := by omega
      let ki : Fin (m + 2) := ⟨i.val - 1, by omega⟩
      let kj : Fin (m + 2) := ⟨j.val - 1, by omega⟩
      let kk : Fin (m + 2) := ⟨k.val - 1, by omega⟩
      have hpi : p i = qFn ki := by dsimp [p, ki]; simp [Nat.ne_of_gt hi_pos]
      have hpj : p j = qFn kj := by dsimp [p, kj]; simp [hj_ne]
      have hpk : p k = qFn kk := by dsimp [p, kk]; simp [hk_ne]
      have h0ij : 0 < orient2D p₀ (p i) (p j) := by
        rw [hpi, hpj]; exact hqFn_orient ki kj (by simp [ki, kj, Fin.lt_def]; omega)
      have h0jk : 0 < orient2D p₀ (p j) (p k) := by
        rw [hpj, hpk]; exact hqFn_orient kj kk (by simp [kj, kk, Fin.lt_def]; omega)
      have h0ik : 0 < orient2D p₀ (p i) (p k) := by
        rw [hpi, hpk]; exact hqFn_orient ki kk (by simp [ki, kk, Fin.lt_def]; omega)
      by_contra hle
      have hneg : orient2D (p i) (p j) (p k) < 0 := by
        have hne0 := hC.2 (p i) (hp_mem i) (p j) (hp_mem j) (p k) (hp_mem k)
          (fun h => ne_of_lt hij (hp_inj h))
          (fun h => ne_of_lt hjk (hp_inj h))
          (fun h => ne_of_lt (lt_trans hij hjk) (hp_inj h))
        exact lt_of_le_of_ne (not_lt.mp hle) hne0
      have hikj : 0 < orient2D (p i) (p k) (p j) := by rw [orient2D_swap23]; linarith
      have hk0j : 0 < orient2D (p k) p₀ (p j) := by
        have : orient2D (p k) p₀ (p j) = orient2D p₀ (p j) (p k) := by unfold orient2D; ring
        linarith
      have htri : InOpenTri p₀ (p i) (p k) (p j) :=
        inOpenTri_of_orient_pos h0ik h0ij hikj hk0j
      have hmem_erase : p j ∈ convexHull ℝ ((C.erase (p j) : Finset (ℝ × ℝ)) : Set (ℝ × ℝ)) := by
        have hi_ne_j : p i ≠ p j := fun h => ne_of_lt hij (hp_inj h)
        have hk_ne_j : p k ≠ p j := fun h => ne_of_gt hjk (hp_inj h)
        have hp0_ne_j : p₀ ≠ p j := by
          intro h
          have h0_eq_j : (⟨0, by omega⟩ : Fin (m + 3)) = j := by
            apply hp_inj
            change (if hi : (⟨0, by omega⟩ : Fin (m + 3)).val = 0 then p₀ else qFn _) = p j
            rw [dif_pos rfl]
            exact h
          exact hj_ne (congrArg Fin.val h0_eq_j).symm
        refine convexHull_mono ?_ (inOpenTri_mem_convexHull htri)
        intro z hz
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
        rcases hz with rfl | rfl | rfl
        · exact Finset.mem_coe.mpr (Finset.mem_erase.mpr ⟨hp0_ne_j, hp0⟩)
        · exact Finset.mem_coe.mpr (Finset.mem_erase.mpr ⟨hi_ne_j, hp_mem i⟩)
        · exact Finset.mem_coe.mpr (Finset.mem_erase.mpr ⟨hk_ne_j, hp_mem k⟩)
      exact hC.1 (p j) (hp_mem j) hmem_erase
  have hcyc : ∀ i j k : Fin (m + 3), CyclicOrder i j k → 0 < orient2D (p i) (p j) (p k) := by
    intro i j k h
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact h_ord_pos i j k h1 h2
    · have : orient2D (p i) (p j) (p k) = orient2D (p j) (p k) (p i) := by unfold orient2D; ring
      rw [this]; exact h_ord_pos j k i h1 h2
    · have : orient2D (p i) (p j) (p k) = orient2D (p k) (p i) (p j) := by unfold orient2D; ring
      rw [this]; exact h_ord_pos k i j h1 h2
  have hstrict : StrictConvexCCWPoly p := fun i j hji hj1 => by
    have h1eq : (1 : Fin (m + 3)) = ⟨1 % (m + 3), Nat.mod_lt 1 (by omega)⟩ := by
      ext; simp [Nat.mod_eq_of_lt (by omega : 1 < m + 3)]
    rw [h1eq] at hj1 ⊢
    exact hcyc i _ j (cyclicOrder_succ (by omega) hji hj1)
  exact ⟨p, hstrict, hp_inj, hp_img, hcyc⟩

lemma isCCWHullEdge_iff_succ {m : ℕ} {p : Fin (m + 3) → ℝ × ℝ}
    (hp : StrictConvexCCWPoly p) (hinj : Function.Injective p) {a b : ℝ × ℝ} :
    IsCCWHullEdge (Finset.univ.image p) a b ↔ ∃ i : Fin (m + 3), p i = a ∧ p (i + 1) = b := by
  have h1_ne_0 : (1 : Fin (m + 3)) ≠ 0 := by
    intro h
    have hv := congrArg Fin.val h
    simp [Nat.mod_eq_of_lt (by omega : 1 < m + 3)] at hv
  have hi_ne_succ : ∀ i : Fin (m + 3), i ≠ i + 1 := by
    intro i h
    nth_rw 1 [← add_zero i] at h
    exact h1_ne_0 (add_left_cancel h).symm
  constructor
  · rintro ⟨ha, hb, hab, hall⟩
    rcases Finset.mem_image.mp ha with ⟨i, _, rfl⟩
    rcases Finset.mem_image.mp hb with ⟨j, _, rfl⟩
    refine ⟨i, rfl, ?_⟩
    by_contra hj1
    have hji : j ≠ i := fun h => hab (congrArg p h).symm
    have ho1 := hp i j hji (fun h => hj1 (congrArg p h).symm)
    have hsucc_ne_i : p (i + 1) ≠ p i := fun h => (hi_ne_succ i).symm (hinj h)
    have hsucc_ne_j : p (i + 1) ≠ p j := fun h => hj1 h
    have ho2 := hall (p (i + 1)) (Finset.mem_image.mpr ⟨i + 1, Finset.mem_univ _, rfl⟩)
      hsucc_ne_i hsucc_ne_j
    rw [orient2D_swap23] at ho2
    linarith
  · rintro ⟨i, rfl, rfl⟩
    refine ⟨Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩,
      Finset.mem_image.mpr ⟨i + 1, Finset.mem_univ _, rfl⟩,
      fun h => hi_ne_succ i (hinj h), fun c hc hca hcb => ?_⟩
    rcases Finset.mem_image.mp hc with ⟨j, _, rfl⟩
    exact hp i j (fun h => hca (congrArg p h)) (fun h => hcb (congrArg p h))

/-- Near/far chain decomposition of a strictly convex CCW polygon `p` from an external
    point `v` off all vertex-pair lines (`upper_9.tex` Section 3). -/
structure VisibleContour {m : ℕ} (p : Fin (m + 3) → ℝ × ℝ) (v : ℝ × ℝ) where
  i_max : Fin (m + 3)
  i_min : Fin (m + 3)
  d_near : ℕ
  slope : Fin (m + 3) → ℝ
  hi_ne : i_max ≠ i_min
  hd_pos : 0 < d_near
  hd_lt : d_near < m + 3
  hmin_eq : finShift i_max d_near = i_min
  h_orient : ∀ i j : Fin (m + 3), 0 < orient2D v (p i) (p j) ↔ slope i < slope j
  h_slope_inj : Function.Injective slope
  h_near_face : ∀ k : ℕ, k < d_near →
    orient2D (p (finShift i_max k)) (p (finShift i_max (k + 1))) v < 0 ∧
    slope (finShift i_max (k + 1)) < slope (finShift i_max k)
  h_far_nofacing : ∀ k : ℕ, d_near ≤ k → k < m + 3 →
    0 < orient2D (p (finShift i_max k)) (p (finShift i_max (k + 1))) v ∧
    slope (finShift i_max k) < slope (finShift i_max (k + 1))
  h_extrema : ∀ i : Fin (m + 3), slope i_min ≤ slope i ∧ slope i ≤ slope i_max
  h_front_iff : ∀ r : Fin (m + 3),
    IsFrontVertex (Finset.univ.image p) v (p r) ↔
      ∃ k : ℕ, 0 < k ∧ k < d_near ∧ r = finShift i_max k
  h_back_iff : ∀ r : Fin (m + 3),
    IsBackVertex (Finset.univ.image p) v (p r) ↔
      ∃ k : ℕ, d_near < k ∧ k < m + 3 ∧ r = finShift i_max k

lemma inOpenTri_slope_between {m : ℕ} {p : Fin (m + 3) → ℝ × ℝ} {v : ℝ × ℝ}
    (vc : VisibleContour p v) {a b c : Fin (m + 3)}
    (hab : a ≠ b)
    (htri : InOpenTri v (p a) (p b) (p c)) :
    (vc.slope a < vc.slope c ∧ vc.slope c < vc.slope b) ∨
    (vc.slope b < vc.slope c ∧ vc.slope c < vc.slope a) := by
  rcases htri with ⟨μ₁, μ₂, μ₃, _, h2, h3, hsum, hc1, hc2⟩
  have hμ1 : μ₁ = 1 - μ₂ - μ₃ := by linarith
  have hcab : orient2D v (p c) (p a) = μ₃ * orient2D v (p b) (p a) := by
    unfold orient2D; rw [hc1, hc2, hμ1]; ring
  have hcba : orient2D v (p c) (p b) = μ₂ * orient2D v (p a) (p b) := by
    unfold orient2D; rw [hc1, hc2, hμ1]; ring
  have hne : vc.slope a ≠ vc.slope b := fun h => hab (vc.h_slope_inj h)
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · left
    have hvab : 0 < orient2D v (p a) (p b) := (vc.h_orient a b).mpr hlt
    have hvba : orient2D v (p b) (p a) < 0 := by rw [orient2D_swap23]; linarith
    have h1 : 0 < orient2D v (p a) (p c) := by
      have : orient2D v (p c) (p a) < 0 := by rw [hcab]; nlinarith
      rw [orient2D_swap23]; linarith
    have h2' : 0 < orient2D v (p c) (p b) := by rw [hcba]; nlinarith
    exact ⟨(vc.h_orient a c).mp h1, (vc.h_orient c b).mp h2'⟩
  · right
    have hvba : 0 < orient2D v (p b) (p a) := (vc.h_orient b a).mpr hlt
    have hvab : orient2D v (p a) (p b) < 0 := by rw [orient2D_swap23]; linarith
    have h1 : 0 < orient2D v (p b) (p c) := by
      have : orient2D v (p c) (p b) < 0 := by rw [hcba]; nlinarith
      rw [orient2D_swap23]; linarith
    have h2' : 0 < orient2D v (p c) (p a) := by rw [hcab]; nlinarith
    exact ⟨(vc.h_orient b c).mp h1, (vc.h_orient c a).mp h2'⟩

lemma near_slope_strictAnti {m : ℕ} {p : Fin (m + 3) → ℝ × ℝ} {v : ℝ × ℝ}
    (vc : VisibleContour p v) {k₁ k₂ : ℕ} (hk12 : k₁ < k₂) (hk2 : k₂ ≤ vc.d_near) :
    vc.slope (finShift vc.i_max k₂) < vc.slope (finShift vc.i_max k₁) := by
  have hd : ∀ d : ℕ, k₁ + d ≤ vc.d_near → 0 < d →
      vc.slope (finShift vc.i_max (k₁ + d)) < vc.slope (finShift vc.i_max k₁) := by
    intro d
    induction d with
    | zero => intro _ h0; omega
    | succ d ih =>
      intro hle _
      have hstep := (vc.h_near_face (k₁ + d) (by omega)).2
      rcases Nat.eq_zero_or_pos d with rfl | hd_pos
      · simpa using hstep
      · exact lt_trans hstep (ih (by omega) hd_pos)
  have hres := hd (k₂ - k₁) (by omega) (by omega)
  have heq : k₁ + (k₂ - k₁) = k₂ := by omega
  simpa [heq] using hres

lemma far_slope_strictMono {m : ℕ} {p : Fin (m + 3) → ℝ × ℝ} {v : ℝ × ℝ}
    (vc : VisibleContour p v) {k₁ k₂ : ℕ} (hd1 : vc.d_near ≤ k₁) (hk12 : k₁ < k₂)
    (hk2 : k₂ ≤ m + 3) :
    vc.slope (finShift vc.i_max k₁) < vc.slope (finShift vc.i_max k₂) := by
  have hd : ∀ d : ℕ, k₁ + d ≤ m + 3 → 0 < d →
      vc.slope (finShift vc.i_max k₁) < vc.slope (finShift vc.i_max (k₁ + d)) := by
    intro d
    induction d with
    | zero => intro _ h0; omega
    | succ d ih =>
      intro hle _
      have hstep := (vc.h_far_nofacing (k₁ + d) (by omega) (by omega)).2
      rcases Nat.eq_zero_or_pos d with rfl | hd_pos
      · simpa using hstep
      · exact lt_trans (ih (by omega) hd_pos) hstep
  have hres := hd (k₂ - k₁) (by omega) (by omega)
  have heq : k₁ + (k₂ - k₁) = k₂ := by omega
  simpa [heq] using hres

private lemma plucker_contour_id (v a b c r : ℝ × ℝ) :
    orient2D v c b * orient2D a b r + orient2D v a b * orient2D b c r =
      orient2D a b c * orient2D v r b := by
  unfold orient2D; ring

/-- Constructs the `VisibleContour` for a strictly convex CCW polygon `p` from an external
    point `v` off all vertex-pair lines. -/
theorem exists_visibleContour {m : ℕ} (p : Fin (m + 3) → ℝ × ℝ)
    (hp : StrictConvexCCWPoly p) (hinj : Function.Injective p)
    (hv_out : v ∉ convexHull ℝ ((Finset.univ.image p : Finset (ℝ × ℝ)) : Set (ℝ × ℝ)))
    (hv_off : ∀ i j : Fin (m + 3), i ≠ j → orient2D (p i) (p j) v ≠ 0) :
    Nonempty (VisibleContour p v) := by
  let R := Finset.univ.image p
  have hR_ne : R.Nonempty := ⟨p 0, Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩⟩
  obtain ⟨e₁, e₂, hsq, hpos⟩ := hahn_banach_dir hR_ne hv_out
  let dot₁ : Fin (m + 3) → ℝ := fun i => e₁ * ((p i).1 - v.1) + e₂ * ((p i).2 - v.2)
  let dot₂ : Fin (m + 3) → ℝ := fun i => (-e₂) * ((p i).1 - v.1) + e₁ * ((p i).2 - v.2)
  let slope : Fin (m + 3) → ℝ := fun i => dot₂ i / dot₁ i
  have hdot1_pos : ∀ i : Fin (m + 3), 0 < dot₁ i := fun i =>
    hpos (p i) (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
  have h_orient : ∀ i j : Fin (m + 3), 0 < orient2D v (p i) (p j) ↔ slope i < slope j := by
    intro i j
    have hd1 := hdot1_pos i
    have hd2 := hdot1_pos j
    have hid : (e₁ ^ 2 + e₂ ^ 2) * orient2D v (p i) (p j) = dot₁ i * dot₂ j - dot₂ i * dot₁ j := by
      dsimp [dot₁, dot₂, orient2D]; ring
    dsimp [slope]
    rw [div_lt_div_iff₀ hd1 hd2]
    constructor
    · intro ho; have := mul_pos hsq ho; linarith
    · intro hlt; have hmul : 0 < (e₁ ^ 2 + e₂ ^ 2) * orient2D v (p i) (p j) := by linarith
      exact pos_of_mul_pos_right hmul (le_of_lt hsq)
  have hslope_inj : Function.Injective slope := by
    intro i j hij
    by_contra hne
    have hvne : orient2D v (p i) (p j) ≠ 0 := by
      have : orient2D v (p i) (p j) = orient2D (p i) (p j) v := by unfold orient2D; ring
      rw [this]
      exact hv_off i j hne
    rcases lt_or_gt_of_ne hvne with hlt | hgt
    · have hpos' : 0 < orient2D v (p j) (p i) := by rw [orient2D_swap23]; linarith
      have := (h_orient j i).mp hpos'
      linarith
    · have := (h_orient i j).mp hgt
      linarith
  obtain ⟨i_max, _, hi_max⟩ := Finset.exists_max_image Finset.univ slope Finset.univ_nonempty
  obtain ⟨i_min, _, hi_min⟩ := Finset.exists_min_image Finset.univ slope Finset.univ_nonempty
  have h1_ne_0 : (1 : Fin (m + 3)) ≠ 0 := by
    intro h; have hv := congrArg Fin.val h
    simp [Nat.mod_eq_of_lt (by omega : 1 < m + 3)] at hv
  have hi_ne_succ : ∀ i : Fin (m + 3), i ≠ i + 1 := fun i h =>
    h1_ne_0 (add_left_cancel (by nth_rw 1 [← add_zero i] at h; exact h)).symm
  have hpred_ne_succ : ∀ i : Fin (m + 3), i - 1 ≠ i + 1 := fun i h => by
    have h' := congrArg (· + (1 : Fin (m + 3))) h
    rw [sub_add_cancel, add_assoc] at h'
    nth_rw 1 [← add_zero i] at h'
    have h20 : (0 : Fin (m + 3)) = 1 + 1 := add_left_cancel h'
    have hv := congrArg Fin.val h20.symm
    change (1 % (m + 3) + 1 % (m + 3)) % (m + 3) = 0 at hv
    rw [Nat.mod_eq_of_lt (by omega : 1 < m + 3)] at hv
    have : (1 + 1) % (m + 3) = 2 := Nat.mod_eq_of_lt (by omega)
    omega
  have hi_ne : i_max ≠ i_min := by
    intro heq
    have hne := hi_ne_succ i_max
    have h1 := hi_max (i_max + 1) (Finset.mem_univ _)
    have h2 := hi_min (i_max + 1) (Finset.mem_univ _)
    rw [← heq] at h2
    exact hne (hslope_inj (le_antisymm h2 h1))
  have h_local_max : ∀ i : Fin (m + 3), slope (i - 1) < slope i → slope (i + 1) < slope i →
      i = i_max := by
    intro i hpi hsi
    by_contra hne
    have hlt_max' : slope i < slope i_max :=
      lt_of_le_of_ne (hi_max i (Finset.mem_univ _)) (fun h => hne (hslope_inj h))
    have hir_max : i_max ≠ i := Ne.symm hne
    have h_or1 : 0 < orient2D v (p (i - 1)) (p i) := (h_orient (i - 1) i).mpr hpi
    have h_or2 : 0 < orient2D v (p (i + 1)) (p i) := (h_orient (i + 1) i).mpr hsi
    have h_or3 : 0 < orient2D v (p i) (p i_max) := (h_orient i i_max).mpr hlt_max'
    have h_or_r : orient2D v (p i_max) (p i) < 0 := by rw [orient2D_swap23]; linarith
    have h1_lt : i_max ≠ i - 1 := by intro heq; subst heq; linarith
    have h2_lt : i_max ≠ i + 1 := by intro heq; subst heq; linarith
    have h_abc : 0 < orient2D (p (i - 1)) (p i) (p (i + 1)) := by
      have := hp (i - 1) (i + 1) (hpred_ne_succ i).symm (by rw [sub_add_cancel]; exact (hi_ne_succ i).symm)
      rwa [sub_add_cancel] at this
    have h_abr : 0 < orient2D (p (i - 1)) (p i) (p i_max) := by
      have := hp (i - 1) i_max h1_lt (by rw [sub_add_cancel]; exact hir_max)
      rwa [sub_add_cancel] at this
    have h_bcr : 0 < orient2D (p i) (p (i + 1)) (p i_max) := hp i i_max hir_max h2_lt
    have hid := plucker_contour_id v (p (i - 1)) (p i) (p (i + 1)) (p i_max)
    nlinarith
  have h_local_min : ∀ i : Fin (m + 3), slope i < slope (i - 1) → slope i < slope (i + 1) →
      i = i_min := by
    intro i hpi hsi
    by_contra hne
    have hlt_min : slope i_min < slope i :=
      lt_of_le_of_ne (hi_min i (Finset.mem_univ _)) (fun h => hne (hslope_inj h.symm))
    have hir_min : i_min ≠ i := Ne.symm hne
    have h_or1 : 0 < orient2D v (p i) (p (i - 1)) := (h_orient i (i - 1)).mpr hpi
    have h_or2 : 0 < orient2D v (p i) (p (i + 1)) := (h_orient i (i + 1)).mpr hsi
    have h_or3 : 0 < orient2D v (p i_min) (p i) := (h_orient i_min i).mpr hlt_min
    have h1_lt : i_min ≠ i - 1 := by intro heq; subst heq; linarith
    have h2_lt : i_min ≠ i + 1 := by intro heq; subst heq; linarith
    have h_abc : 0 < orient2D (p (i - 1)) (p i) (p (i + 1)) := by
      have := hp (i - 1) (i + 1) (hpred_ne_succ i).symm (by rw [sub_add_cancel]; exact (hi_ne_succ i).symm)
      rwa [sub_add_cancel] at this
    have h_abr : 0 < orient2D (p (i - 1)) (p i) (p i_min) := by
      have := hp (i - 1) i_min h1_lt (by rw [sub_add_cancel]; exact hir_min)
      rwa [sub_add_cancel] at this
    have h_bcr : 0 < orient2D (p i) (p (i + 1)) (p i_min) := hp i i_min hir_min h2_lt
    have hid := plucker_contour_id v (p (i - 1)) (p i) (p (i + 1)) (p i_min)
    have hneg1 : orient2D v (p (i + 1)) (p i) = -orient2D v (p i) (p (i + 1)) := orient2D_swap23 _ _ _
    have hneg2 : orient2D v (p (i - 1)) (p i) = -orient2D v (p i) (p (i - 1)) := orient2D_swap23 _ _ _
    have hneg3 : orient2D v (p i_min) (p i) = -orient2D v (p i) (p i_min) := orient2D_swap23 _ _ _
    nlinarith
  let d_near : ℕ := (i_min - i_max).val
  have hd_lt : d_near < m + 3 := (i_min - i_max).isLt
  have hd_pos : 0 < d_near := by
    by_contra h0
    have hz : d_near = 0 := by omega
    exact hi_ne (sub_eq_zero.mp (Fin.ext hz)).symm
  have hmin_eq : finShift i_max d_near = i_min := finShift_sub i_max i_min
  have h_near_slope : ∀ k : ℕ, k < d_near →
      slope (finShift i_max (k + 1)) < slope (finShift i_max k) := by
    intro k
    induction k with
    | zero =>
      intro _
      rw [finShift_zero, finShift_one (by omega)]
      exact lt_of_le_of_ne (hi_max (i_max + 1) (Finset.mem_univ _))
        (fun h => (hi_ne_succ i_max).symm (hslope_inj h))
    | succ k ih =>
      intro hk
      have ih' := ih (by omega)
      let cur := finShift i_max (k + 1)
      have hpred : cur - 1 = finShift i_max k := finShift_pred (by omega) i_max k
      have hcur_lt_prev : slope cur < slope (cur - 1) := by rw [hpred]; exact ih'
      have hcur_ne_min : cur ≠ i_min := by
        intro heq
        have hsub : cur - i_max = i_min - i_max := congrArg (· - i_max) heq
        dsimp [cur] at hsub
        rw [finShift_eq_add i_max (by omega : k + 1 < m + 3), add_sub_cancel_left] at hsub
        have hv := congrArg Fin.val hsub
        dsimp [d_near] at hk
        simp only at hv
        omega
      have hne_succ : slope cur ≠ slope (cur + 1) :=
        fun h => hi_ne_succ cur (hslope_inj h)
      rw [← finShift_succ (by omega) i_max (k + 1)]
      rcases lt_or_gt_of_ne hne_succ with hlt | hgt
      · exfalso; exact hcur_ne_min (h_local_min cur hcur_lt_prev hlt)
      · exact hgt
  have h_far_slope : ∀ k : ℕ, d_near ≤ k → k < m + 3 →
      slope (finShift i_max k) < slope (finShift i_max (k + 1)) := by
    intro k hdk hk
    have hdown : ∀ t : ℕ, 0 < t → d_near ≤ m + 3 - t → t ≤ m + 3 - d_near →
        slope (finShift i_max (m + 3 - t)) < slope (finShift i_max (m + 3 - t + 1)) := by
      intro t
      induction t with
      | zero => intro h0 _ _; omega
      | succ t ih =>
        intro _ h1 h2
        rcases Nat.eq_zero_or_pos t with rfl | ht_pos
        · have heq : m + 3 - 1 + 1 = m + 3 := by omega
          have hwrap : finShift i_max (m + 3 - 1) + 1 = i_max := by
            rw [finShift_succ (by omega : 2 ≤ m + 3), heq, finShift_len]
          rw [heq, finShift_len]
          exact lt_of_le_of_ne (hi_max _ (Finset.mem_univ _)) (fun h => by
            have hinv := hslope_inj h
            exact (hi_ne_succ (finShift i_max (m + 3 - 1))) (hinv.trans hwrap.symm))
        · have ih' := ih ht_pos (by omega) (by omega)
          let cur := finShift i_max (m + 3 - (t + 1))
          have hcur_succ : cur + 1 = finShift i_max (m + 3 - t) := by
            dsimp [cur]
            rw [finShift_succ (by omega : 2 ≤ m + 3)]
            congr 1; omega
          let nxt := cur + 1
          have hnxt_lt : slope nxt < slope (nxt + 1) := by
            dsimp [nxt]; rw [hcur_succ, finShift_succ (by omega : 2 ≤ m + 3)]; exact ih'
          have hne_pred : slope cur ≠ slope nxt := fun h => hi_ne_succ cur (hslope_inj h)
          rw [← finShift_succ (by omega : 2 ≤ m + 3) i_max (m + 3 - (t + 1))]
          rcases lt_or_gt_of_ne hne_pred with hlt | hgt
          · exact hlt
          · exfalso
            have hn1 : nxt - 1 = cur := add_sub_cancel_right cur 1
            have hlocal : nxt = i_min := h_local_min nxt (by rw [hn1]; exact hgt) hnxt_lt
            have hsub := congrArg (· - i_max) hlocal
            dsimp [nxt] at hsub
            rw [hcur_succ, finShift_eq_add i_max (by omega : m + 3 - t < m + 3), add_sub_cancel_left] at hsub
            have hv := congrArg Fin.val hsub
            dsimp [d_near] at h1
            simp only at hv
            omega
    have hres := hdown (m + 3 - k) (by omega) (by omega) (by omega)
    have heq : m + 3 - (m + 3 - k) = k := by omega
    simpa [heq] using hres
  have h_near_face : ∀ k : ℕ, k < d_near →
      orient2D (p (finShift i_max k)) (p (finShift i_max (k + 1))) v < 0 ∧
      slope (finShift i_max (k + 1)) < slope (finShift i_max k) := by
    intro k hk
    have hs := h_near_slope k hk
    have ho : 0 < orient2D v (p (finShift i_max (k + 1))) (p (finShift i_max k)) :=
      (h_orient _ _).mpr hs
    refine ⟨?_, hs⟩
    have : orient2D (p (finShift i_max k)) (p (finShift i_max (k + 1))) v =
        -orient2D v (p (finShift i_max (k + 1))) (p (finShift i_max k)) := by
      unfold orient2D; ring
    linarith
  have h_far_nofacing : ∀ k : ℕ, d_near ≤ k → k < m + 3 →
      0 < orient2D (p (finShift i_max k)) (p (finShift i_max (k + 1))) v ∧
      slope (finShift i_max k) < slope (finShift i_max (k + 1)) := by
    intro k hdk hk
    have hs := h_far_slope k hdk hk
    have ho : 0 < orient2D v (p (finShift i_max k)) (p (finShift i_max (k + 1))) :=
      (h_orient _ _).mpr hs
    refine ⟨?_, hs⟩
    have : orient2D (p (finShift i_max k)) (p (finShift i_max (k + 1))) v =
        orient2D v (p (finShift i_max k)) (p (finShift i_max (k + 1))) := by
      unfold orient2D; ring
    linarith
  have h_front_iff : ∀ r : Fin (m + 3),
      IsFrontVertex (Finset.univ.image p) v (p r) ↔
        ∃ k : ℕ, 0 < k ∧ k < d_near ∧ r = finShift i_max k := by
    intro r
    let k := (r - i_max).val
    have hk_lt : k < m + 3 := (r - i_max).isLt
    have hr_eq : r = finShift i_max k := (finShift_sub i_max r).symm
    have hpred_edge : IsCCWHullEdge (Finset.univ.image p) (p (r - 1)) (p r) :=
      (isCCWHullEdge_iff_succ hp hinj).mpr ⟨r - 1, rfl, by rw [sub_add_cancel]⟩
    have hsucc_edge : IsCCWHullEdge (Finset.univ.image p) (p r) (p (r + 1)) :=
      (isCCWHullEdge_iff_succ hp hinj).mpr ⟨r, rfl, rfl⟩
    have hfront_char : IsFrontVertex (Finset.univ.image p) v (p r) ↔
        orient2D (p (r - 1)) (p r) v < 0 ∧ orient2D (p r) (p (r + 1)) v < 0 := by
      constructor
      · rintro ⟨b', c', hb', hc', ho1, ho2⟩
        rw [isCCWHullEdge_pred_unique hb' hpred_edge] at ho1
        rw [isCCWHullEdge_succ_unique hc' hsucc_edge] at ho2
        exact ⟨ho1, ho2⟩
      · rintro ⟨ho1, ho2⟩
        exact ⟨p (r - 1), p (r + 1), hpred_edge, hsucc_edge, ho1, ho2⟩
    rw [hfront_char]
    constructor
    · rintro ⟨ho1, ho2⟩
      have ho1' : 0 < orient2D v (p r) (p (r - 1)) := by
        have : orient2D v (p r) (p (r - 1)) = -orient2D (p (r - 1)) (p r) v := by unfold orient2D; ring
        linarith
      have ho2' : 0 < orient2D v (p (r + 1)) (p r) := by
        have : orient2D v (p (r + 1)) (p r) = -orient2D (p r) (p (r + 1)) v := by unfold orient2D; ring
        linarith
      have hs1 : slope r < slope (r - 1) := (h_orient _ _).mp ho1'
      have hs2 : slope (r + 1) < slope r := (h_orient _ _).mp ho2'
      refine ⟨k, ?_, ?_, hr_eq⟩
      · by_contra hk0
        have hk0' : k = 0 := by omega
        have hr0 : r = i_max := by rw [hr_eq, hk0', finShift_zero]
        have := hi_max (r - 1) (Finset.mem_univ _)
        rw [← hr0] at this; linarith
      · by_contra hkd
        have hkd' : d_near ≤ k := by omega
        by_cases hkd_eq : k = d_near
        · have hrm : r = i_min := by rw [hr_eq, hkd_eq]; exact hmin_eq
          have := hi_min (r + 1) (Finset.mem_univ _)
          rw [← hrm] at this; linarith
        · have hfar := (h_far_nofacing (k - 1) (by omega) (by omega)).2
          have hsucc_eq : finShift i_max (k - 1 + 1) = r := by
            rw [show k - 1 + 1 = k by omega, ← hr_eq]
          have hpred_eq : finShift i_max (k - 1) = r - 1 := by
            rw [← finShift_pred (by omega) i_max (k - 1), hsucc_eq]
          rw [hsucc_eq, hpred_eq] at hfar
          linarith
    · rintro ⟨k', hk0, hkd, rfl⟩
      have h1 := (h_near_face (k' - 1) (by omega)).1
      have h2 := (h_near_face k' hkd).1
      have hk1 : k' - 1 + 1 = k' := by omega
      rw [hk1] at h1
      have hpred' : finShift i_max k' - 1 = finShift i_max (k' - 1) := by
        conv_lhs => rw [← hk1]
        exact finShift_pred (by omega) i_max (k' - 1)
      rw [hpred', finShift_succ (by omega) i_max k']
      exact ⟨h1, h2⟩
  have h_back_iff : ∀ r : Fin (m + 3),
      IsBackVertex (Finset.univ.image p) v (p r) ↔
        ∃ k : ℕ, d_near < k ∧ k < m + 3 ∧ r = finShift i_max k := by
    intro r
    let k := (r - i_max).val
    have hk_lt : k < m + 3 := (r - i_max).isLt
    have hr_eq : r = finShift i_max k := (finShift_sub i_max r).symm
    have hpred_edge : IsCCWHullEdge (Finset.univ.image p) (p (r - 1)) (p r) :=
      (isCCWHullEdge_iff_succ hp hinj).mpr ⟨r - 1, rfl, by rw [sub_add_cancel]⟩
    have hsucc_edge : IsCCWHullEdge (Finset.univ.image p) (p r) (p (r + 1)) :=
      (isCCWHullEdge_iff_succ hp hinj).mpr ⟨r, rfl, rfl⟩
    have hback_char : IsBackVertex (Finset.univ.image p) v (p r) ↔
        0 < orient2D (p (r - 1)) (p r) v ∧ 0 < orient2D (p r) (p (r + 1)) v := by
      constructor
      · rintro ⟨b', c', hb', hc', ho1, ho2⟩
        rw [isCCWHullEdge_pred_unique hb' hpred_edge] at ho1
        rw [isCCWHullEdge_succ_unique hc' hsucc_edge] at ho2
        exact ⟨ho1, ho2⟩
      · rintro ⟨ho1, ho2⟩
        exact ⟨p (r - 1), p (r + 1), hpred_edge, hsucc_edge, ho1, ho2⟩
    rw [hback_char]
    constructor
    · rintro ⟨ho1, ho2⟩
      have ho1' : 0 < orient2D v (p (r - 1)) (p r) := by
        have : orient2D v (p (r - 1)) (p r) = orient2D (p (r - 1)) (p r) v := by unfold orient2D; ring
        linarith
      have ho2' : 0 < orient2D v (p r) (p (r + 1)) := by
        have : orient2D v (p r) (p (r + 1)) = orient2D (p r) (p (r + 1)) v := by unfold orient2D; ring
        linarith
      have hs1 : slope (r - 1) < slope r := (h_orient _ _).mp ho1'
      have hs2 : slope r < slope (r + 1) := (h_orient _ _).mp ho2'
      refine ⟨k, ?_, hk_lt, hr_eq⟩
      by_contra hk_le
      have hk_le' : k ≤ d_near := by omega
      rcases Nat.eq_zero_or_pos k with hk0 | hk_pos
      · have hr0 : r = i_max := by rw [hr_eq, hk0, finShift_zero]
        have := hi_max (r + 1) (Finset.mem_univ _)
        rw [← hr0] at this; linarith
      · have hnear := (h_near_face (k - 1) (by omega)).2
        have hsucc_eq : finShift i_max (k - 1 + 1) = r := by
          rw [show k - 1 + 1 = k by omega, ← hr_eq]
        have hpred_eq : finShift i_max (k - 1) = r - 1 := by
          rw [← finShift_pred (by omega) i_max (k - 1), hsucc_eq]
        rw [hsucc_eq, hpred_eq] at hnear
        linarith
    · rintro ⟨k', hdk, hkm, rfl⟩
      have h1 := (h_far_nofacing (k' - 1) (by omega) (by omega)).1
      have h2 := (h_far_nofacing k' (by omega) hkm).1
      have hk1 : k' - 1 + 1 = k' := by omega
      rw [hk1] at h1
      have hpred' : finShift i_max k' - 1 = finShift i_max (k' - 1) := by
        conv_lhs => rw [← hk1]
        exact finShift_pred (by omega) i_max (k' - 1)
      rw [hpred', finShift_succ (by omega) i_max k']
      exact ⟨h1, h2⟩
  exact ⟨{
    i_max := i_max
    i_min := i_min
    d_near := d_near
    slope := slope
    hi_ne := hi_ne
    hd_pos := hd_pos
    hd_lt := hd_lt
    hmin_eq := hmin_eq
    h_orient := h_orient
    h_slope_inj := hslope_inj
    h_near_face := h_near_face
    h_far_nofacing := h_far_nofacing
    h_extrema := fun i => ⟨hi_min i (Finset.mem_univ _), hi_max i (Finset.mem_univ _)⟩
    h_front_iff := h_front_iff
    h_back_iff := h_back_iff
  }⟩

lemma not_mem_convexHull_of_isFrontVertex {C : Finset (ℝ × ℝ)} {v f : ℝ × ℝ}
    (hf : IsFrontVertex C v f) :
    v ∉ convexHull ℝ (C : Set (ℝ × ℝ)) := by
  rcases hf with ⟨b, _, hbf, _, ho1, _⟩
  intro hv
  have hle : 0 ≤ orient2D b f v := by
    let H : Set (ℝ × ℝ) := {x | 0 ≤ orient2D b f x}
    have hH_conv : Convex ℝ H := by
      intro x hx y hy α β hα hβ hαβ
      dsimp [H] at hx hy ⊢
      unfold orient2D at hx hy ⊢
      change 0 ≤ (f.1 - b.1) * ((α * x.2 + β * y.2) - b.2) -
        (f.2 - b.2) * ((α * x.1 + β * y.1) - b.1)
      have hlin : (f.1 - b.1) * ((α * x.2 + β * y.2) - b.2) -
          (f.2 - b.2) * ((α * x.1 + β * y.1) - b.1) =
          α * ((f.1 - b.1) * (x.2 - b.2) - (f.2 - b.2) * (x.1 - b.1)) +
          β * ((f.1 - b.1) * (y.2 - b.2) - (f.2 - b.2) * (y.1 - b.1)) +
          (1 - (α + β)) * ((f.1 - b.1) * (-b.2) - (f.2 - b.2) * (-b.1)) := by ring
      rw [hlin, hαβ, sub_self, zero_mul, add_zero]
      exact add_nonneg (mul_nonneg hα hx) (mul_nonneg hβ hy)
    have hsub : (C : Set (ℝ × ℝ)) ⊆ H := by
      intro x hx
      dsimp [H]
      by_cases hxb : x = b
      · rw [hxb, orient2D_self_outer]
      · by_cases hxf : x = f
        · rw [hxf, orient2D_self_right]
        · exact le_of_lt (hbf.2.2.2 x hx hxb hxf)
    exact convexHull_min hsub hH_conv hv
  linarith

/-- Any line through vertex `p i_h` separating `p (i_h + 1)` from `p (i_h - 1)` partitions
    `B \ {p i_h}` into two contiguous boundary arcs (positive/negative sides). -/
lemma line_separates_boundary_contiguous {m : ℕ} (p : Fin (m + 3) → ℝ × ℝ)
    (hcyc : ∀ i j k : Fin (m + 3), CyclicOrder i j k → 0 < orient2D (p i) (p j) (p k))
    (i_h : Fin (m + 3)) (z : ℝ × ℝ)
    (h1 : 0 < orient2D z (p i_h) (p (i_h + 1)))
    (h2 : orient2D z (p i_h) (p (i_h - 1)) < 0)
    (hne0 : ∀ k : ℕ, 1 ≤ k → k < m + 3 → orient2D z (p i_h) (p (finShift i_h k)) ≠ 0) :
    ∃ k_split : ℕ, 1 ≤ k_split ∧ k_split < m + 2 ∧
      (∀ k : ℕ, 1 ≤ k → k ≤ k_split → 0 < orient2D z (p i_h) (p (finShift i_h k))) ∧
      (∀ k : ℕ, k_split < k → k < m + 3 → orient2D z (p i_h) (p (finShift i_h k)) < 0) := by
  let ℓ : ℕ → ℝ := fun k => orient2D z (p i_h) (p (finShift i_h k))
  have hc_ord : ∀ a b : ℕ, 1 ≤ a → a < b → b < m + 3 →
      CyclicOrder i_h (finShift i_h a) (finShift i_h b) := by
    intro a b ha hab hb
    have hi_lt := i_h.isLt
    by_cases ha_wrap : i_h.val + a < m + 3
    · by_cases hb_wrap : i_h.val + b < m + 3
      · left
        refine ⟨Fin.lt_def.mpr ?_, Fin.lt_def.mpr ?_⟩ <;>
          simp [finShift, Nat.mod_eq_of_lt ha_wrap, Nat.mod_eq_of_lt hb_wrap] <;> omega
      · right; right
        refine ⟨Fin.lt_def.mpr ?_, Fin.lt_def.mpr ?_⟩ <;>
          simp [finShift, Nat.mod_eq_of_lt ha_wrap]
        · have : (i_h.val + b) % (m + 3) = i_h.val + b - (m + 3) := by
            rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
          omega
        · omega
    · right; left
      refine ⟨Fin.lt_def.mpr ?_, Fin.lt_def.mpr ?_⟩ <;> simp [finShift]
      · have ha' : (i_h.val + a) % (m + 3) = i_h.val + a - (m + 3) := by
          rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
        have hb' : (i_h.val + b) % (m + 3) = i_h.val + b - (m + 3) := by
          rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
        omega
      · have hb' : (i_h.val + b) % (m + 3) = i_h.val + b - (m + 3) := by
          rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
        omega
  have hno_cross : ∀ k₁ k₂ k₃ : ℕ, 1 ≤ k₁ → k₁ < k₂ → k₂ < k₃ → k₃ < m + 3 →
      ¬ (0 < ℓ k₁ ∧ ℓ k₂ < 0 ∧ 0 < ℓ k₃) := by
    intro k₁ k₂ k₃ hk1 hk12 hk23 hk3
    let j₁ := finShift i_h k₁
    let j₂ := finShift i_h k₂
    let j₃ := finShift i_h k₃
    have ho13 : 0 < orient2D (p i_h) (p j₁) (p j₃) := hcyc i_h j₁ j₃ (hc_ord k₁ k₃ hk1 (lt_trans hk12 hk23) hk3)
    have ho12 : 0 < orient2D (p i_h) (p j₁) (p j₂) := hcyc i_h j₁ j₂ (hc_ord k₁ k₂ hk1 hk12 (by omega))
    have ho23 : 0 < orient2D (p i_h) (p j₂) (p j₃) := hcyc i_h j₂ j₃ (hc_ord k₂ k₃ (by omega) hk23 hk3)
    have hℓ_comb : orient2D (p i_h) (p j₁) (p j₃) * orient2D z (p i_h) (p j₂) =
        orient2D (p i_h) (p j₂) (p j₃) * orient2D z (p i_h) (p j₁) +
        orient2D (p i_h) (p j₁) (p j₂) * orient2D z (p i_h) (p j₃) := by
      unfold orient2D; ring
    change ¬ (0 < orient2D z (p i_h) (p j₁) ∧ orient2D z (p i_h) (p j₂) < 0 ∧
      0 < orient2D z (p i_h) (p j₃))
    rintro ⟨a1, a2, a3⟩
    nlinarith [mul_pos ho23 a1, mul_pos ho12 a3]
  let negs := (Finset.range (m + 3)).filter (fun k => 1 ≤ k ∧ ℓ k < 0)
  have hm2_in : m + 2 ∈ negs := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), by omega, ?_⟩
    dsimp [ℓ]
    have heq : finShift i_h (m + 2) = i_h - 1 := by
      apply eq_sub_of_add_eq
      rw [finShift_succ (by omega : 2 ≤ m + 3)]
      have hlen : finShift i_h (m + 2 + 1) = finShift i_h (m + 3) := congrArg (finShift i_h) (by omega)
      exact hlen.trans (finShift_len i_h)
    rwa [heq]
  let k_neg := negs.min' ⟨m + 2, hm2_in⟩
  have hk_neg_mem := Finset.min'_mem negs ⟨m + 2, hm2_in⟩
  have hk_neg_lt : k_neg < m + 3 := Finset.mem_range.mp (Finset.mem_filter.mp hk_neg_mem).1
  have hk_neg_ge1 : 1 ≤ k_neg := (Finset.mem_filter.mp hk_neg_mem).2.1
  have hk_neg_val : ℓ k_neg < 0 := (Finset.mem_filter.mp hk_neg_mem).2.2
  have hk1_pos : 0 < ℓ 1 := by
    dsimp [ℓ]; rw [finShift_one (by omega)]; exact h1
  have hk_neg_gt1 : 1 < k_neg := by
    by_contra hle
    have : k_neg = 1 := by omega
    rw [this] at hk_neg_val; linarith
  refine ⟨k_neg - 1, by omega, by omega, fun k hk1 hk2 => ?_, fun k hk1 hk2 => ?_⟩
  · have h_not_neg : ¬ ℓ k < 0 := fun hlt => by
      have hmin := Finset.min'_le negs k (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hk1, hlt⟩)
      omega
    exact lt_of_le_of_ne (not_lt.mp h_not_neg) (Ne.symm (hne0 k hk1 (by omega)))
  · by_cases hkeq : k = k_neg
    · subst hkeq; exact hk_neg_val
    · by_contra hge
      have hpos : 0 < ℓ k := lt_of_le_of_ne (not_lt.mp hge) (Ne.symm (hne0 k (by omega) hk2))
      exact hno_cross 1 k_neg k (by omega) hk_neg_gt1 (by omega) hk2 ⟨hk1_pos, hk_neg_val, hpos⟩

/-! ## Section 4: Certified Hull Vertices (`Lemmas 4.1–4.5`, `Prop 4.3`, `Cor 4.4`, `Cor 4.6`) -/

/-- The witness `z_f = w_{S \ {f}}` missing only `f`. -/
def zWitness {n : ℕ} (w : Finset (Fin n) → ℝ × ℝ) (f : Fin n) : ℝ × ℝ :=
  w (Finset.univ.erase f)

/-- Certified hull vertex (`upper_9.tex` Definition 4.1): `f ∈ B` has some witness
    missing `f` that sees both neighbors of `f` in `B` and has `f` as a front vertex of `B`. -/
def IsCertified {n : ℕ} (P : Set (ℝ × ℝ)) (S : Fin n → ℝ × ℝ)
    (w : Finset (Fin n) → ℝ × ℝ) (f : Fin n) : Prop :=
  f ∈ hullVertices S ∧
    ∃ vt : Finset (Fin n),
      ¬ Sees P (w vt) (S f) ∧
      (∀ b ∈ hullVertices S,
        (IsCCWHullEdge ((hullVertices S).image S) (S b) (S f) ∨
         IsCCWHullEdge ((hullVertices S).image S) (S f) (S b)) →
        Sees P (w vt) (S b)) ∧
      IsFrontVertex ((hullVertices S).image S) (w vt) (S f)

/-- The set `H ⊆ B` of all certified hull vertices. -/
def certifiedSet {n : ℕ} (P : Set (ℝ × ℝ)) (S : Fin n → ℝ × ℝ)
    (w : Finset (Fin n) → ℝ × ℝ) : Finset (Fin n) :=
  (hullVertices S).filter (IsCertified P S w)

/-- CCW cyclic hull boundary enumeration for a convex-position subset `C ⊆ Fin n`. -/
structure CyclicSubsetBoundary {n : ℕ} (S : Fin n → ℝ × ℝ) (C : Finset (Fin n)) where
  m : ℕ
  p_idx : Fin (m + 3) → Fin n
  hp_idx_inj : Function.Injective p_idx
  hp_idx_img : Finset.univ.image p_idx = C
  hstrict : StrictConvexCCWPoly (S ∘ p_idx)
  hcyc : ∀ i j k : Fin (m + 3), CyclicOrder i j k → 0 < orient2D (S (p_idx i)) (S (p_idx j)) (S (p_idx k))

lemma exists_cyclicSubsetBoundary {n : ℕ} {P : Set (ℝ × ℝ)} {S : Fin n → ℝ × ℝ}
    {w : Finset (Fin n) → ℝ × ℝ} (hP : ShatteredSimplePolygon P S w)
    {C : Finset (Fin n)} (hCB : C ⊆ hullVertices S) (hC3 : 3 ≤ C.card) :
    Nonempty (CyclicSubsetBoundary S C) := by
  have hC_pos : IsConvexPos (C.image S) :=
    subset_isConvexPos (Finset.image_subset_image hCB) (hullVertices_isConvexPos hP)
  have hcard : (C.image S).card = (C.card - 3) + 3 := by
    rw [Finset.card_image_of_injective C hP.s_inj]; omega
  obtain ⟨p, hstrict, hp_inj, hp_img, hcyc⟩ :=
    strictConvexCCWPoly_of_isConvexPos hC_pos hcard
  have hp_mem_C : ∀ i : Fin ((C.card - 3) + 3), ∃ idx ∈ C, S idx = p i := by
    intro i
    have hm : p i ∈ C.image S := by rw [← hp_img]; exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
    exact Finset.mem_image.mp hm
  choose p_idx hp_idx_mem hp_idx_eq using hp_mem_C
  have hp_fun_eq : S ∘ p_idx = p := funext hp_idx_eq
  have hp_idx_inj : Function.Injective p_idx := by
    intro i j hij
    exact hp_inj (by rw [← hp_idx_eq i, ← hp_idx_eq j, hij])
  have hp_idx_img : Finset.univ.image p_idx = C := by
    apply Finset.eq_of_subset_of_card_le
    · intro idx hidx
      rcases Finset.mem_image.mp hidx with ⟨i, _, rfl⟩
      exact hp_idx_mem i
    · rw [Finset.card_image_of_injective Finset.univ hp_idx_inj, Finset.card_univ, Fintype.card_fin]
      omega
  exact ⟨{
    m := C.card - 3
    p_idx := p_idx
    hp_idx_inj := hp_idx_inj
    hp_idx_img := hp_idx_img
    hstrict := by rw [hp_fun_eq]; exact hstrict
    hcyc := fun i j k hk => by simpa [hp_idx_eq] using hcyc i j k hk
  }⟩

lemma certified_neighbors_and_front {n : ℕ} {P : Set (ℝ × ℝ)} {S : Fin n → ℝ × ℝ}
    {w : Finset (Fin n) → ℝ × ℝ}
    (hP : ShatteredSimplePolygon P S w) (hn : 3 ≤ n)
    {f : Fin n} (hf : IsCertified P S w f) :
    ∃ b c : Fin n, b ∈ hullVertices S ∧ c ∈ hullVertices S ∧ b ≠ f ∧ c ≠ f ∧ b ≠ c ∧
      IsCCWHullEdge ((hullVertices S).image S) (S b) (S f) ∧
      IsCCWHullEdge ((hullVertices S).image S) (S f) (S c) ∧
      (∀ x_idx : Finset (Fin n), Sees P (w x_idx) (S b) → Sees P (w x_idx) (S c) →
        InOpenTri (w x_idx) (S b) (S c) (S f) ∧
        IsFrontVertex ((hullVertices S).image S) (w x_idx) (S f)) := by
  let B := hullVertices S
  have hB3 : 3 ≤ B.card := hullVertices_card_ge_three hn hP
  rcases hf with ⟨hfB, vt, hvnf, hvs_nbr, b_pt, c_pt, hbf_pt, hfc_pt, hv_bo, hv_co⟩
  rcases Finset.mem_image.mp hbf_pt.1 with ⟨b, hbB, rfl⟩
  rcases Finset.mem_image.mp hfc_pt.2.1 with ⟨c, hcB, rfl⟩
  have hbf_ne : b ≠ f := fun h => hbf_pt.2.2.1 (congrArg S h)
  have hfc_ne : c ≠ f := fun h => hfc_pt.2.2.1 (congrArg S h).symm
  have hvb := hvs_nbr b hbB (Or.inl hbf_pt)
  have hvc := hvs_nbr c hcB (Or.inr hfc_pt)
  have hbc_ne : b ≠ c := by
    intro hbc_eq
    subst hbc_eq
    have : orient2D (S b) (S f) (w vt) = -orient2D (S f) (S b) (w vt) := by unfold orient2D; ring
    linarith
  obtain ⟨htri, hall⟩ := hidden_front_vertex hP B (Finset.Subset.refl B) hB3 vt hfB hbB hcB
    hbf_pt hfc_pt ⟨S b, S c, hbf_pt, hfc_pt, hv_bo, hv_co⟩ hvb hvc hvnf
  exact ⟨b, c, hbB, hcB, hbf_ne, hfc_ne, hbc_ne, hbf_pt, hfc_pt, hall⟩

/-- Lemma 4.1 (`Side corners`, `upper_9.tex` lines 362–368):
    Let `f` be certified, and let `a, b ∈ B \ {f}` lie on different sides of line `z_f f`.
    Then `f ∈ interior Δ(x, a, b)` for every witness `x` that sees `a` and `b`. -/
theorem side_corners {n : ℕ} {P : Set (ℝ × ℝ)} {S : Fin n → ℝ × ℝ}
    {w : Finset (Fin n) → ℝ × ℝ}
    (hP : ShatteredSimplePolygon P S w) (hn : 3 ≤ n)
    {f a b : Fin n} (hf : IsCertified P S w f)
    (ha : a ∈ hullVertices S) (hb : b ∈ hullVertices S)
    (haf : a ≠ f) (hbf : b ≠ f)
    (hopp : orient2D (zWitness w f) (S f) (S a) * orient2D (zWitness w f) (S f) (S b) < 0) :
    ∀ x_idx : Finset (Fin n), Sees P (w x_idx) (S a) → Sees P (w x_idx) (S b) →
      InOpenTri (w x_idx) (S a) (S b) (S f) := by
  let B := hullVertices S
  let zf := zWitness w f
  obtain ⟨b₀, c₀, _, _, hb0f, hc0f, hb0c0, hb0f_edge, hfc0_edge, hall⟩ :=
    certified_neighbors_and_front hP hn hf
  have hzf_b0 : Sees P zf (S b₀) := (hP.shatters (Finset.univ.erase f) b₀).mpr (Finset.mem_erase.mpr ⟨hb0f, Finset.mem_univ _⟩)
  have hzf_c0 : Sees P zf (S c₀) := (hP.shatters (Finset.univ.erase f) c₀).mpr (Finset.mem_erase.mpr ⟨hc0f, Finset.mem_univ _⟩)
  have hzf_nf : ¬ Sees P zf (S f) := fun h => (Finset.mem_erase.mp ((hP.shatters (Finset.univ.erase f) f).mp h)).1 rfl
  obtain ⟨htri0, ⟨b0', c0', hb0', hc0', hzb0, hzc0⟩⟩ := hall (Finset.univ.erase f) hzf_b0 hzf_c0
  rw [isCCWHullEdge_pred_unique hb0' hb0f_edge] at hzb0
  rw [isCCWHullEdge_succ_unique hc0' hfc0_edge] at hzc0
  have h_b0f_nonneg : ∀ q ∈ B, q ≠ f → 0 ≤ orient2D (S b₀) (S f) (S q) := by
    intro q hqB hqf
    by_cases hqb0 : q = b₀
    · rw [hqb0, orient2D_self_outer]
    · exact le_of_lt (hb0f_edge.2.2.2 (S q) (Finset.mem_image.mpr ⟨q, hqB, rfl⟩)
        (fun h => hqb0 (hP.s_inj h)) (fun h => hqf (hP.s_inj h)))
  have h_fc0_nonneg : ∀ q ∈ B, q ≠ f → 0 ≤ orient2D (S f) (S c₀) (S q) := by
    intro q hqB hqf
    by_cases hqc0 : q = c₀
    · rw [hqc0, orient2D_self_right]
    · exact le_of_lt (hfc0_edge.2.2.2 (S q) (Finset.mem_image.mpr ⟨q, hqB, rfl⟩)
        (fun h => hqf (hP.s_inj h)) (fun h => hqc0 (hP.s_inj h)))
  let da := orient2D zf (S f) (S a)
  let db := orient2D zf (S f) (S b)
  have hopp' : da * db < 0 := hopp
  have hden_ne : da - db ≠ 0 := by
    intro h0
    have heq : da = db := sub_eq_zero.mp h0
    rw [heq] at hopp'
    have : 0 ≤ db * db := mul_self_nonneg db
    linarith
  let t := da / (da - db)
  have ht01 : 0 < t ∧ t < 1 := by
    rcases lt_or_gt_of_ne (mul_ne_zero_iff.mp (ne_of_lt hopp')).1 with hda | hda
    · have hdb : 0 < db := by nlinarith
      have hdd : da - db < 0 := by linarith
      exact ⟨div_pos_of_neg_of_neg hda hdd, (div_lt_one_of_neg hdd).mpr (by linarith)⟩
    · have hdb : db < 0 := by nlinarith
      have hdd : 0 < da - db := by linarith
      exact ⟨div_pos hda hdd, (div_lt_one hdd).mpr (by linarith)⟩
  let y : ℝ × ℝ := ((1 - t) * (S a).1 + t * (S b).1, (1 - t) * (S a).2 + t * (S b).2)
  have hy_col : orient2D zf (S f) y = 0 := by
    rw [orient2D_affine_comb zf (S f) (S a) (S b) y t rfl rfl]
    change (1 - t) * da + t * db = 0
    dsimp [t]
    field_simp [hden_ne]
    ring
  have hy_ne_f : y ≠ S f := by
    intro hyf
    have hconv_pos := hullVertices_isConvexPos hP
    apply hconv_pos.1 (S f) (Finset.mem_image.mpr ⟨f, hf.1, rfl⟩)
    have ha_er : S a ∈ (B.image S).erase (S f) :=
      Finset.mem_erase.mpr ⟨fun h => haf (hP.s_inj h), Finset.mem_image.mpr ⟨a, ha, rfl⟩⟩
    have hb_er : S b ∈ (B.image S).erase (S f) :=
      Finset.mem_erase.mpr ⟨fun h => hbf (hP.s_inj h), Finset.mem_image.mpr ⟨b, hb, rfl⟩⟩
    have hy_eq_comb : y = (1 - t) • S a + t • S b := by ext <;> simp [y]
    have h_in := (convex_convexHull ℝ _) (subset_convexHull ℝ _ ha_er) (subset_convexHull ℝ _ hb_er)
      (show 0 ≤ 1 - t by linarith) (le_of_lt ht01.1) (by ring : (1 - t) + t = 1)
    rwa [← hy_eq_comb, hyf] at h_in
  have hy_b0f_nn : 0 ≤ orient2D (S b₀) (S f) y := by
    rw [orient2D_affine_comb (S b₀) (S f) (S a) (S b) y t rfl rfl]
    exact add_nonneg (mul_nonneg (by linarith) (h_b0f_nonneg a ha haf))
      (mul_nonneg (le_of_lt ht01.1) (h_b0f_nonneg b hb hbf))
  have hy_fc0_nn : 0 ≤ orient2D (S f) (S c₀) y := by
    rw [orient2D_affine_comb (S f) (S c₀) (S a) (S b) y t rfl rfl]
    exact add_nonneg (mul_nonneg (by linarith) (h_fc0_nonneg a ha haf))
      (mul_nonneg (le_of_lt ht01.1) (h_fc0_nonneg b hb hbf))
  have hy_pos_one : 0 < orient2D (S b₀) (S f) y ∨ 0 < orient2D (S f) (S c₀) y := by
    by_contra hboth
    push Not at hboth
    have hz1 : orient2D (S b₀) (S f) y = 0 := le_antisymm hboth.1 hy_b0f_nn
    have hz2 : orient2D (S f) (S c₀) y = 0 := le_antisymm hboth.2 hy_fc0_nn
    have hc_pos : 0 < orient2D (S b₀) (S f) (S c₀) :=
      hb0f_edge.2.2.2 (S c₀) hfc0_edge.2.1 (fun h => hb0c0 (hP.s_inj h).symm)
        (fun h => hc0f (hP.s_inj h))
    have h_id1 : orient2D (S b₀) (S f) (S c₀) * (y.1 - (S f).1) =
        ((S c₀).1 - (S f).1) * orient2D (S b₀) (S f) y +
        ((S b₀).1 - (S f).1) * orient2D (S f) (S c₀) y := by unfold orient2D; ring
    have h_id2 : orient2D (S b₀) (S f) (S c₀) * (y.2 - (S f).2) =
        ((S c₀).2 - (S f).2) * orient2D (S b₀) (S f) y +
        ((S b₀).2 - (S f).2) * orient2D (S f) (S c₀) y := by unfold orient2D; ring
    rw [hz1, hz2, mul_zero, mul_zero, add_zero] at h_id1 h_id2
    have hdx : y.1 - (S f).1 = 0 := (mul_eq_zero.mp h_id1).resolve_left (ne_of_gt hc_pos)
    have hdy : y.2 - (S f).2 = 0 := (mul_eq_zero.mp h_id2).resolve_left (ne_of_gt hc_pos)
    exact hy_ne_f (by ext <;> linarith)
  have hzf_ne_f : zf ≠ S f := (hP.s_ne_w f (Finset.univ.erase f)).symm
  have hzf_coord : (S f).1 - zf.1 ≠ 0 ∨ (S f).2 - zf.2 ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hzf_ne_f (by ext <;> linarith)
  obtain ⟨lam, hlam1, hlam2⟩ : ∃ lam : ℝ,
      y.1 - (S f).1 = lam * ((S f).1 - zf.1) ∧
      y.2 - (S f).2 = lam * ((S f).2 - zf.2) := by
    unfold orient2D at hy_col
    rcases hzf_coord with hx | hyc
    · exact ⟨(y.1 - (S f).1) / ((S f).1 - zf.1), by field_simp [hx],
        by field_simp [hx]; linarith⟩
    · exact ⟨(y.2 - (S f).2) / ((S f).2 - zf.2),
        by field_simp [hyc]; linarith, by field_simp [hyc]⟩
  have hlam_pos : 0 < lam := by
    have hzb0' : orient2D (S b₀) (S f) zf < 0 := hzb0
    have hzc0' : orient2D (S f) (S c₀) zf < 0 := hzc0
    have hid1 : orient2D (S b₀) (S f) y = -lam * orient2D (S b₀) (S f) zf := by
      unfold orient2D
      have hy1 : y.1 = (S f).1 + lam * ((S f).1 - zf.1) := by linarith
      have hy2 : y.2 = (S f).2 + lam * ((S f).2 - zf.2) := by linarith
      rw [hy1, hy2]; ring
    have hid2 : orient2D (S f) (S c₀) y = -lam * orient2D (S f) (S c₀) zf := by
      unfold orient2D
      have hy1 : y.1 = (S f).1 + lam * ((S f).1 - zf.1) := by linarith
      have hy2 : y.2 = (S f).2 + lam * ((S f).2 - zf.2) := by linarith
      rw [hy1, hy2]; ring
    rcases hy_pos_one with hpos1 | hpos2
    · rw [hid1] at hpos1; nlinarith
    · rw [hid2] at hpos2; nlinarith
  have h1lam : 0 < 1 + lam := by linarith
  have h1lam_ne : 1 + lam ≠ 0 := ne_of_gt h1lam
  have htri_zf : InOpenTri zf (S a) (S b) (S f) := by
    refine ⟨lam / (1 + lam), (1 - t) / (1 + lam), t / (1 + lam),
      div_pos hlam_pos h1lam, div_pos (by linarith) h1lam, div_pos ht01.1 h1lam, ?_, ?_, ?_⟩
    · field_simp [h1lam_ne]; ring
    · have hy1 : y.1 = (S f).1 + lam * ((S f).1 - zf.1) := by linarith
      dsimp [y] at hy1
      field_simp [h1lam_ne]; linarith
    · have hy2 : y.2 = (S f).2 + lam * ((S f).2 - zf.2) := by linarith
      dsimp [y] at hy2
      field_simp [h1lam_ne]; linarith
  intro x_idx hxa hxb
  by_cases hxeq : x_idx = Finset.univ.erase f
  · subst hxeq; exact htri_zf
  · have hxU : w x_idx ∈ UCone (S f) (S a) (S b) := by
      apply cone hP.toEnclosureDomain
        ((hP.shatters (Finset.univ.erase f) a).mpr (Finset.mem_erase.mpr ⟨haf, Finset.mem_univ _⟩))
        ((hP.shatters (Finset.univ.erase f) b).mpr (Finset.mem_erase.mpr ⟨hbf, Finset.mem_univ _⟩))
        hzf_nf htri_zf hxa hxb
      · exact hP.no_three_collinear (S f) (S a) (w x_idx) (Or.inl ⟨f, rfl⟩) (Or.inl ⟨a, rfl⟩)
          (Or.inr ⟨x_idx, rfl⟩) (fun h => haf (hP.s_inj h).symm) (hP.s_ne_w a x_idx) (hP.s_ne_w f x_idx)
      · exact hP.no_three_collinear (S f) (S b) (w x_idx) (Or.inl ⟨f, rfl⟩) (Or.inl ⟨b, rfl⟩)
          (Or.inr ⟨x_idx, rfl⟩) (fun h => hbf (hP.s_inj h).symm) (hP.s_ne_w b x_idx) (hP.s_ne_w f x_idx)
      · exact hP.no_three_collinear zf (S f) (w x_idx) (Or.inr ⟨Finset.univ.erase f, rfl⟩)
          (Or.inl ⟨f, rfl⟩) (Or.inr ⟨x_idx, rfl⟩) (hP.s_ne_w f (Finset.univ.erase f)).symm
          (hP.s_ne_w f x_idx) (fun h => hxeq (hP.w_inj h).symm)
    exact (mem_uCone_iff_inOpenTri (S f) (S a) (S b) (w x_idx)).mp hxU

lemma q_not_mem_hull {n : ℕ} {P : Set (ℝ × ℝ)} {S : Fin n → ℝ × ℝ}
    {w : Finset (Fin n) → ℝ × ℝ} (hP : ShatteredSimplePolygon P S w) (hn : 3 ≤ n)
    {f : Fin n} (hf : IsCertified P S w f) :
    w Finset.univ ∉ convexHull ℝ (((hullVertices S).image S : Finset (ℝ × ℝ)) : Set (ℝ × ℝ)) := by
  obtain ⟨b, c, _, _, _, _, _, _, _, hall⟩ := certified_neighbors_and_front hP hn hf
  have hqb := (hP.shatters Finset.univ b).mpr (Finset.mem_univ b)
  have hqc := (hP.shatters Finset.univ c).mpr (Finset.mem_univ c)
  exact not_mem_convexHull_of_isFrontVertex (hall Finset.univ hqb hqc).2

lemma exists_q_visibleContour {n : ℕ} {P : Set (ℝ × ℝ)} {S : Fin n → ℝ × ℝ}
    {w : Finset (Fin n) → ℝ × ℝ} (hP : ShatteredSimplePolygon P S w) (hn : 3 ≤ n)
    (cb : CyclicSubsetBoundary S (hullVertices S))
    {f : Fin n} (hf : IsCertified P S w f) :
    Nonempty (VisibleContour (S ∘ cb.p_idx) (w Finset.univ)) := by
  have hq_out : w Finset.univ ∉
      convexHull ℝ ((Finset.univ.image (S ∘ cb.p_idx) : Finset (ℝ × ℝ)) : Set (ℝ × ℝ)) := by
    have himg : Finset.univ.image (S ∘ cb.p_idx) = (hullVertices S).image S := by
      calc Finset.univ.image (S ∘ cb.p_idx)
          = (Finset.univ.image cb.p_idx).image S := Finset.image_image.symm
        _ = (hullVertices S).image S := by rw [cb.hp_idx_img]
    rw [himg]
    exact q_not_mem_hull hP hn hf
  refine exists_visibleContour (S ∘ cb.p_idx) cb.hstrict (hP.s_inj.comp cb.hp_idx_inj) hq_out ?_
  intro i j hij
  exact hP.no_three_collinear (S (cb.p_idx i)) (S (cb.p_idx j)) (w Finset.univ)
    (Or.inl ⟨cb.p_idx i, rfl⟩) (Or.inl ⟨cb.p_idx j, rfl⟩) (Or.inr ⟨Finset.univ, rfl⟩)
    (fun h => hij (cb.hp_idx_inj (hP.s_inj h)))
    (hP.s_ne_w (cb.p_idx j) Finset.univ)
    (hP.s_ne_w (cb.p_idx i) Finset.univ)

lemma line_separates_boundary_contiguous_neg {m : ℕ} (p : Fin (m + 3) → ℝ × ℝ)
    (hcyc : ∀ i j k : Fin (m + 3), CyclicOrder i j k → 0 < orient2D (p i) (p j) (p k))
    (i_h : Fin (m + 3)) (z : ℝ × ℝ)
    (h1 : orient2D z (p i_h) (p (i_h + 1)) < 0)
    (h2 : 0 < orient2D z (p i_h) (p (i_h - 1)))
    (hne0 : ∀ k : ℕ, 1 ≤ k → k < m + 3 → orient2D z (p i_h) (p (finShift i_h k)) ≠ 0) :
    ∃ k_split : ℕ, 1 ≤ k_split ∧ k_split < m + 2 ∧
      (∀ k : ℕ, 1 ≤ k → k ≤ k_split → orient2D z (p i_h) (p (finShift i_h k)) < 0) ∧
      (∀ k : ℕ, k_split < k → k < m + 3 → 0 < orient2D z (p i_h) (p (finShift i_h k))) := by
  let z' : ℝ × ℝ := (2 * (p i_h).1 - z.1, 2 * (p i_h).2 - z.2)
  have hflip : ∀ x : ℝ × ℝ, orient2D z' (p i_h) x = -orient2D z (p i_h) x := by
    intro x; dsimp [z', orient2D]; ring
  have h1' : 0 < orient2D z' (p i_h) (p (i_h + 1)) := by rw [hflip]; linarith
  have h2' : orient2D z' (p i_h) (p (i_h - 1)) < 0 := by rw [hflip]; linarith
  have hne0' : ∀ k : ℕ, 1 ≤ k → k < m + 3 → orient2D z' (p i_h) (p (finShift i_h k)) ≠ 0 :=
    fun k hk1 hk2 => by rw [hflip]; exact neg_ne_zero.mpr (hne0 k hk1 hk2)
  obtain ⟨k_split, hk1, hk2, hpos, hneg⟩ :=
    line_separates_boundary_contiguous p hcyc i_h z' h1' h2' hne0'
  refine ⟨k_split, hk1, hk2, fun k ha hb => ?_, fun k ha hb => ?_⟩
  · have := hpos k ha hb; rw [hflip] at this; linarith
  · have := hneg k ha hb; rw [hflip] at this; linarith

/-- Lemma 4.2 (`Separation`, `upper_9.tex` lines 374–382):
    For a certified vertex `f`, `f` is an inner vertex of `N_q`, its predecessor/successor
    edges have `l`-side (`0 < orient2D z_f f ·`) and `r`-side (`orient2D z_f f · < 0`),
    and the line `z_f f` separates all predecessors on `N_q` from all successors on `N_q`
    (and splits `∂ conv B \ {f}` into two contiguous boundary arcs). -/
theorem separation {n : ℕ} {P : Set (ℝ × ℝ)} {S : Fin n → ℝ × ℝ}
    {w : Finset (Fin n) → ℝ × ℝ}
    (hP : ShatteredSimplePolygon P S w) (hn : 3 ≤ n)
    (cb : CyclicSubsetBoundary S (hullVertices S))
    (vc : VisibleContour (S ∘ cb.p_idx) (w Finset.univ))
    {f : Fin n} (hf : IsCertified P S w f) :
    ∃ kf : ℕ, 0 < kf ∧ kf < vc.d_near ∧ cb.p_idx (finShift vc.i_max kf) = f ∧
      (∀ k₁ : ℕ, k₁ < kf →
        0 < orient2D (zWitness w f) (S f) (S (cb.p_idx (finShift vc.i_max k₁)))) ∧
      (∀ k₂ : ℕ, kf < k₂ → k₂ ≤ vc.d_near →
        orient2D (zWitness w f) (S f) (S (cb.p_idx (finShift vc.i_max k₂))) < 0) ∧
      (∃ k_split : ℕ, 1 ≤ k_split ∧ k_split < cb.m + 2 ∧
        (∀ k : ℕ, 1 ≤ k → k ≤ k_split →
          orient2D (zWitness w f) (S f) (S (cb.p_idx (finShift (finShift vc.i_max kf) k))) < 0) ∧
        (∀ k : ℕ, k_split < k → k < cb.m + 3 →
          0 < orient2D (zWitness w f) (S f) (S (cb.p_idx (finShift (finShift vc.i_max kf) k))))) := by
  let B := hullVertices S
  let p := S ∘ cb.p_idx
  have hp_inj : Function.Injective p := hP.s_inj.comp cb.hp_idx_inj
  have himg_eq : Finset.univ.image p = B.image S := by
    calc Finset.univ.image (S ∘ cb.p_idx)
        = (Finset.univ.image cb.p_idx).image S := Finset.image_image.symm
      _ = B.image S := by rw [cb.hp_idx_img]
  obtain ⟨b₀, c₀, _, _, hb0f, hc0f, _, hb0f_edge, hfc0_edge, hall⟩ :=
    certified_neighbors_and_front hP hn hf
  have hqb := (hP.shatters Finset.univ b₀).mpr (Finset.mem_univ b₀)
  have hqc := (hP.shatters Finset.univ c₀).mpr (Finset.mem_univ c₀)
  have hq_front : IsFrontVertex (Finset.univ.image p) (w Finset.univ) (S f) := by
    rw [himg_eq]; exact (hall Finset.univ hqb hqc).2
  have hf_mem : f ∈ B := hf.1
  have hf_img : f ∈ Finset.univ.image cb.p_idx := by rw [cb.hp_idx_img]; exact hf_mem
  rcases Finset.mem_image.mp hf_img with ⟨i_f, _, hif_eq⟩
  have hfront_if : IsFrontVertex (Finset.univ.image p) (w Finset.univ) (p i_f) := by
    change IsFrontVertex (Finset.univ.image p) (w Finset.univ) (S (cb.p_idx i_f))
    rw [hif_eq]; exact hq_front
  obtain ⟨kf, hkf_pos, hkf_lt, hif_shift⟩ := (vc.h_front_iff i_f).mp hfront_if
  have hkf_eq_f : cb.p_idx (finShift vc.i_max kf) = f := by rw [← hif_shift, hif_eq]
  have hf_ne_shift : ∀ k : ℕ, k ≤ vc.d_near → k ≠ kf →
      cb.p_idx (finShift vc.i_max k) ≠ f := by
    intro k hk hne heq
    have hinj : finShift vc.i_max k = finShift vc.i_max kf :=
      cb.hp_idx_inj (heq.trans hkf_eq_f.symm)
    have hsub := congrArg (· - vc.i_max) hinj
    have := vc.hd_lt
    rw [finShift_eq_add vc.i_max (by omega : k < cb.m + 3),
      finShift_eq_add vc.i_max (by omega : kf < cb.m + 3),
      add_sub_cancel_left, add_sub_cancel_left] at hsub
    exact hne (congrArg Fin.val hsub)
  have hkf_mem_shift : ∀ k : ℕ, k ≤ vc.d_near → cb.p_idx (finShift vc.i_max k) ∈ B := by
    intro k _
    have hm : cb.p_idx (finShift vc.i_max k) ∈ Finset.univ.image cb.p_idx :=
      Finset.mem_image.mpr ⟨finShift vc.i_max k, Finset.mem_univ _, rfl⟩
    rwa [cb.hp_idx_img] at hm
  have hz_edge_l : IsCCWHullEdge (B.image S) (p (i_f - 1)) (S f) := by
    rw [← himg_eq, ← hif_eq]
    exact (isCCWHullEdge_iff_succ cb.hstrict hp_inj).mpr
      ⟨i_f - 1, rfl, congrArg p (sub_add_cancel i_f 1)⟩
  have hz_edge_r : IsCCWHullEdge (B.image S) (S f) (p (i_f + 1)) := by
    rw [← himg_eq, ← hif_eq]
    exact (isCCWHullEdge_iff_succ cb.hstrict hp_inj).mpr ⟨i_f, rfl, rfl⟩
  have hpred_b0 : p (i_f - 1) = S b₀ := isCCWHullEdge_pred_unique hz_edge_l hb0f_edge
  have hsucc_c0 : p (i_f + 1) = S c₀ := isCCWHullEdge_succ_unique hz_edge_r hfc0_edge
  have hzf_b0 : Sees P (zWitness w f) (S b₀) :=
    (hP.shatters (Finset.univ.erase f) b₀).mpr (Finset.mem_erase.mpr ⟨hb0f, Finset.mem_univ _⟩)
  have hzf_c0 : Sees P (zWitness w f) (S c₀) :=
    (hP.shatters (Finset.univ.erase f) c₀).mpr (Finset.mem_erase.mpr ⟨hc0f, Finset.mem_univ _⟩)
  obtain ⟨_, ⟨b0', c0', hb0', hc0', hzb0, hzc0⟩⟩ := hall (Finset.univ.erase f) hzf_b0 hzf_c0
  rw [isCCWHullEdge_pred_unique hb0' hb0f_edge] at hzb0
  rw [isCCWHullEdge_succ_unique hc0' hfc0_edge] at hzc0
  have hl_pos : 0 < orient2D (zWitness w f) (S f) (p (i_f - 1)) := by
    rw [hpred_b0]
    have hzb0' : orient2D (S b₀) (S f) (zWitness w f) < 0 := hzb0
    have : orient2D (zWitness w f) (S f) (S b₀) = -orient2D (S b₀) (S f) (zWitness w f) := by
      unfold orient2D; ring
    linarith
  have hr_neg : orient2D (zWitness w f) (S f) (p (i_f + 1)) < 0 := by
    rw [hsucc_c0]
    have hzc0' : orient2D (S f) (S c₀) (zWitness w f) < 0 := hzc0
    have : orient2D (zWitness w f) (S f) (S c₀) = orient2D (S f) (S c₀) (zWitness w f) := by
      unfold orient2D; ring
    linarith
  have hstep_same : ∀ k : ℕ, k + 1 ≤ vc.d_near → (k + 1 < kf ∨ kf < k) →
      0 < orient2D (zWitness w f) (S f) (p (finShift vc.i_max k)) *
          orient2D (zWitness w f) (S f) (p (finShift vc.i_max (k + 1))) := by
    intro k hk1 hside
    have hk_ne_f : cb.p_idx (finShift vc.i_max k) ≠ f :=
      hf_ne_shift k (by omega) (by rcases hside with h | h <;> omega)
    have hk1_ne_f : cb.p_idx (finShift vc.i_max (k + 1)) ≠ f :=
      hf_ne_shift (k + 1) hk1 (by rcases hside with h | h <;> omega)
    have h0_k : orient2D (zWitness w f) (S f) (p (finShift vc.i_max k)) ≠ 0 :=
      hP.no_three_collinear (zWitness w f) (S f) (p (finShift vc.i_max k))
        (Or.inr ⟨Finset.univ.erase f, rfl⟩) (Or.inl ⟨f, rfl⟩)
        (Or.inl ⟨cb.p_idx (finShift vc.i_max k), rfl⟩)
        (hP.s_ne_w f _).symm (fun h => hk_ne_f (hP.s_inj h).symm)
        (hP.s_ne_w (cb.p_idx (finShift vc.i_max k)) (Finset.univ.erase f)).symm
    have h0_k1 : orient2D (zWitness w f) (S f) (p (finShift vc.i_max (k + 1))) ≠ 0 :=
      hP.no_three_collinear (zWitness w f) (S f) (p (finShift vc.i_max (k + 1)))
        (Or.inr ⟨Finset.univ.erase f, rfl⟩) (Or.inl ⟨f, rfl⟩)
        (Or.inl ⟨cb.p_idx (finShift vc.i_max (k + 1)), rfl⟩)
        (hP.s_ne_w f _).symm (fun h => hk1_ne_f (hP.s_inj h).symm)
        (hP.s_ne_w (cb.p_idx (finShift vc.i_max (k + 1))) (Finset.univ.erase f)).symm
    have hprod_ne : orient2D (zWitness w f) (S f) (p (finShift vc.i_max k)) *
        orient2D (zWitness w f) (S f) (p (finShift vc.i_max (k + 1))) ≠ 0 :=
      mul_ne_zero h0_k h0_k1
    by_contra hle
    have hopp : orient2D (zWitness w f) (S f) (p (finShift vc.i_max k)) *
        orient2D (zWitness w f) (S f) (p (finShift vc.i_max (k + 1))) < 0 :=
      lt_of_le_of_ne (not_lt.mp hle) hprod_ne
    have htri := side_corners hP hn hf (hkf_mem_shift k (by omega)) (hkf_mem_shift (k + 1) hk1)
      hk_ne_f hk1_ne_f hopp Finset.univ
      ((hP.shatters Finset.univ _).mpr (Finset.mem_univ _))
      ((hP.shatters Finset.univ _).mpr (Finset.mem_univ _))
    have hne_idx : finShift vc.i_max k ≠ finShift vc.i_max (k + 1) := by
      intro heq
      have hsub := congrArg (· - vc.i_max) heq
      have := vc.hd_lt
      rw [finShift_eq_add vc.i_max (by omega : k < cb.m + 3),
        finShift_eq_add vc.i_max (by omega : k + 1 < cb.m + 3),
        add_sub_cancel_left, add_sub_cancel_left] at hsub
      have hv := congrArg Fin.val hsub
      simp only at hv
      omega
    have hbtw := inOpenTri_slope_between vc hne_idx (by
      change InOpenTri (w Finset.univ) (p (finShift vc.i_max k))
        (p (finShift vc.i_max (k + 1))) (p i_f)
      dsimp [p]; rw [hif_eq]; exact htri)
    have hs_step := (vc.h_near_face k (by omega)).2
    rcases hside with hk1_lt | hk_gt
    · have hs_f := near_slope_strictAnti vc hk1_lt (le_of_lt hkf_lt)
      rw [← hif_shift] at hs_f
      rcases hbtw with ⟨ha, hb⟩ | ⟨ha, hb⟩ <;> linarith
    · have hs_f := near_slope_strictAnti vc hk_gt (by omega)
      rw [← hif_shift] at hs_f
      rcases hbtw with ⟨ha, hb⟩ | ⟨ha, hb⟩ <;> linarith
  have hleft : ∀ k₁ : ℕ, k₁ < kf →
      0 < orient2D (zWitness w f) (S f) (S (cb.p_idx (finShift vc.i_max k₁))) := by
    intro k₁ hk1
    have hwalk : ∀ d : ℕ, d ≤ kf - 1 →
        0 < orient2D (zWitness w f) (S f) (p (finShift vc.i_max (kf - 1 - d))) := by
      intro d
      induction d with
      | zero =>
        intro _
        have hpred_eq : finShift vc.i_max (kf - 1 - 0) = i_f - 1 := by
          rw [hif_shift]
          have : kf - 1 - 0 + 1 = kf := by omega
          conv_rhs => rw [← this]
          exact (finShift_pred (by omega : 2 ≤ cb.m + 3) vc.i_max (kf - 1 - 0)).symm
        rw [hpred_eq]
        exact hl_pos
      | succ d ih =>
        intro hd
        have ih' := ih (by omega)
        have hstep := hstep_same (kf - 1 - (d + 1)) (by omega) (Or.inl (by omega))
        have heq1 : kf - 1 - (d + 1) + 1 = kf - 1 - d := by omega
        rw [heq1] at hstep
        exact pos_of_mul_pos_left hstep (le_of_lt ih')
    have hres := hwalk (kf - 1 - k₁) (by omega)
    have heq : kf - 1 - (kf - 1 - k₁) = k₁ := by omega
    rw [heq] at hres
    exact hres
  have hright : ∀ k₂ : ℕ, kf < k₂ → k₂ ≤ vc.d_near →
      orient2D (zWitness w f) (S f) (S (cb.p_idx (finShift vc.i_max k₂))) < 0 := by
    intro k₂ hk2 hk2_le
    have hwalk : ∀ d : ℕ, kf + 1 + d ≤ vc.d_near →
        orient2D (zWitness w f) (S f) (p (finShift vc.i_max (kf + 1 + d))) < 0 := by
      intro d
      induction d with
      | zero =>
        intro _
        have hsucc_eq : finShift vc.i_max (kf + 1 + 0) = i_f + 1 := by
          change finShift vc.i_max (kf + 1) = i_f + 1
          rw [← finShift_succ (by omega : 2 ≤ cb.m + 3) vc.i_max kf, ← hif_shift]
        rw [hsucc_eq]
        exact hr_neg
      | succ d ih =>
        intro hd
        have ih' := ih (by omega)
        have hstep := hstep_same (kf + 1 + d) (by omega) (Or.inr (by omega))
        have heq : kf + 1 + d + 1 = kf + 1 + (d + 1) := by omega
        rw [heq] at hstep
        exact neg_of_mul_pos_right hstep (le_of_lt ih')
    have hres := hwalk (k₂ - (kf + 1)) (by omega)
    have heq : kf + 1 + (k₂ - (kf + 1)) = k₂ := by omega
    rw [heq] at hres
    exact hres
  have hpart : ∃ k_split : ℕ, 1 ≤ k_split ∧ k_split < cb.m + 2 ∧
      (∀ k : ℕ, 1 ≤ k → k ≤ k_split →
        orient2D (zWitness w f) (S f) (p (finShift i_f k)) < 0) ∧
      (∀ k : ℕ, k_split < k → k < cb.m + 3 →
        0 < orient2D (zWitness w f) (S f) (p (finShift i_f k))) := by
    have hres := line_separates_boundary_contiguous_neg p cb.hcyc i_f (zWitness w f)
      (by dsimp [p]; rw [hif_eq]; exact hr_neg)
      (by dsimp [p]; rw [hif_eq]; exact hl_pos) (by
      intro k hk1 hk2
      have hne_f : cb.p_idx (finShift i_f k) ≠ f := by
        rw [← hif_eq]
        intro heq
        have hinj := cb.hp_idx_inj heq
        have hsub := congrArg (· - i_f) hinj
        rw [finShift_eq_add i_f hk2, add_sub_cancel_left, sub_self] at hsub
        have hv := congrArg Fin.val hsub
        simp only [Fin.val_zero] at hv
        omega
      have hpf : S f = p i_f := (congrArg S hif_eq).symm
      rw [← hpf]
      exact hP.no_three_collinear (zWitness w f) (S f) (p (finShift i_f k))
        (Or.inr ⟨Finset.univ.erase f, rfl⟩) (Or.inl ⟨f, rfl⟩)
        (Or.inl ⟨cb.p_idx (finShift i_f k), rfl⟩)
        (hP.s_ne_w f _).symm (fun h => hne_f (hP.s_inj h).symm)
        (hP.s_ne_w (cb.p_idx (finShift i_f k)) (Finset.univ.erase f)).symm)
    dsimp [p] at hres
    rw [hif_eq] at hres
    exact hres
  rcases hpart with ⟨k_split, hs1, hs2, hneg_arc, hpos_arc⟩
  refine ⟨kf, hkf_pos, hkf_lt, hkf_eq_f, hleft, hright, k_split, hs1, hs2, ?_, ?_⟩
  · intro k ha hb; rw [← hif_shift]; exact hneg_arc k ha hb
  · intro k ha hb; rw [← hif_shift]; exact hpos_arc k ha hb

lemma cyclicOrder_finShift {N : ℕ} [NeZero N] (i : Fin N) {a b c : ℕ}
    (hab : a < b) (hbc : b < c) (hc : c < N) :
    CyclicOrder (finShift i a) (finShift i b) (finShift i c) := by
  have hi_lt := i.isLt
  by_cases ha_w : i.val + a < N
  · by_cases hb_w : i.val + b < N
    · by_cases hc_w : i.val + c < N
      · left
        refine ⟨Fin.lt_def.mpr ?_, Fin.lt_def.mpr ?_⟩ <;>
          simp [finShift, Nat.mod_eq_of_lt ha_w, Nat.mod_eq_of_lt hb_w, Nat.mod_eq_of_lt hc_w] <;> omega
      · right; right
        refine ⟨Fin.lt_def.mpr ?_, Fin.lt_def.mpr ?_⟩ <;>
          simp [finShift, Nat.mod_eq_of_lt ha_w, Nat.mod_eq_of_lt hb_w]
        · have : (i.val + c) % N = i.val + c - N := by
            rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
          omega
        · omega
    · right; left
      have hc_nw : ¬ i.val + c < N := by omega
      refine ⟨Fin.lt_def.mpr ?_, Fin.lt_def.mpr ?_⟩ <;>
        simp [finShift, Nat.mod_eq_of_lt ha_w]
      · have hb' : (i.val + b) % N = i.val + b - N := by
          rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
        have hc' : (i.val + c) % N = i.val + c - N := by
          rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
        omega
      · have hc' : (i.val + c) % N = i.val + c - N := by
          rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
        omega
  · left
    have ha' : (i.val + a) % N = i.val + a - N := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    have hb' : (i.val + b) % N = i.val + b - N := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    have hc' : (i.val + c) % N = i.val + c - N := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    refine ⟨Fin.lt_def.mpr ?_, Fin.lt_def.mpr ?_⟩ <;> simp [finShift, ha', hb', hc'] <;> omega

lemma finShift_add {N : ℕ} [NeZero N] (i : Fin N) (a b : ℕ) :
    finShift (finShift i a) b = finShift i (a + b) := by
  ext
  simp only [finShift]
  rw [Nat.mod_add_mod, Nat.add_assoc]

/-- Proposition 4.3 (`Structure of the certified set`, `upper_9.tex` lines 384–403):
    If `H` is nonempty, then:
    (i) `H` is a contiguous block `[k_f .. k_g]` on `N_q` (and `∂ conv B`), with distinct
        adjacent neighbors `l, r ∈ B \ H`;
    (ii) `H ⊆ interior Δ(x, l, r)` for every witness `x` seeing `l` and `r`;
    (iii) `|A| + |H| ≤ 5`. -/
theorem certified_structure {n : ℕ} {P : Set (ℝ × ℝ)} {S : Fin n → ℝ × ℝ}
    {w : Finset (Fin n) → ℝ × ℝ}
    (hP : ShatteredSimplePolygon P S w) (hn : 3 ≤ n)
    (cb : CyclicSubsetBoundary S (hullVertices S))
    (vc : VisibleContour (S ∘ cb.p_idx) (w Finset.univ))
    (hH : (certifiedSet P S w).Nonempty) :
    ∃ (k_f k_g : ℕ) (l r : Fin n),
      0 < k_f ∧ k_f ≤ k_g ∧ k_g < vc.d_near ∧
      l = cb.p_idx (finShift vc.i_max (k_f - 1)) ∧
      r = cb.p_idx (finShift vc.i_max (k_g + 1)) ∧
      l ∈ hullVertices S \ certifiedSet P S w ∧
      r ∈ hullVertices S \ certifiedSet P S w ∧
      l ≠ r ∧
      (∀ k : ℕ, k < cb.m + 3 →
        (k_f ≤ k ∧ k ≤ k_g ↔ cb.p_idx (finShift vc.i_max k) ∈ certifiedSet P S w)) ∧
      (∀ h ∈ certifiedSet P S w, ∀ x_idx : Finset (Fin n),
        Sees P (w x_idx) (S l) → Sees P (w x_idx) (S r) →
        InOpenTri (w x_idx) (S l) (S r) (S h)) ∧
      (interiorPoints S).card + (certifiedSet P S w).card ≤ 5 := by
  let B := hullVertices S
  let H := certifiedSet P S w
  let Kf := (Finset.range vc.d_near).filter (fun k => 0 < k ∧ cb.p_idx (finShift vc.i_max k) ∈ H)
  have hKf_ne : Kf.Nonempty := by
    rcases hH with ⟨h₀, hh₀⟩
    have hcert : IsCertified P S w h₀ := (Finset.mem_filter.mp hh₀).2
    obtain ⟨kh, hkh0, hkh_lt, hkh_eq, _⟩ := separation hP hn cb vc hcert
    exact ⟨kh, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hkh_lt, hkh0, hkh_eq ▸ hh₀⟩⟩
  let k_f := Kf.min' hKf_ne
  let k_g := Kf.max' hKf_ne
  have hkf_mem := Finset.min'_mem Kf hKf_ne
  have hkg_mem := Finset.max'_mem Kf hKf_ne
  have hkf_pos : 0 < k_f := (Finset.mem_filter.mp hkf_mem).2.1
  have hkf_lt : k_f < vc.d_near := Finset.mem_range.mp (Finset.mem_filter.mp hkf_mem).1
  have hkg_lt : k_g < vc.d_near := Finset.mem_range.mp (Finset.mem_filter.mp hkg_mem).1
  have hkf_le_kg : k_f ≤ k_g := Finset.min'_le Kf k_g hkg_mem
  have hkf_inH : cb.p_idx (finShift vc.i_max k_f) ∈ H := (Finset.mem_filter.mp hkf_mem).2.2
  have hkg_inH : cb.p_idx (finShift vc.i_max k_g) ∈ H := (Finset.mem_filter.mp hkg_mem).2.2
  let l := cb.p_idx (finShift vc.i_max (k_f - 1))
  let r := cb.p_idx (finShift vc.i_max (k_g + 1))
  have hidx_inj : ∀ a b : ℕ, a < cb.m + 3 → b < cb.m + 3 → a ≠ b →
      cb.p_idx (finShift vc.i_max a) ≠ cb.p_idx (finShift vc.i_max b) := by
    intro a b ha hb hab heq
    have h1 := cb.hp_idx_inj heq
    have hsub := congrArg (· - vc.i_max) h1
    rw [finShift_eq_add vc.i_max ha, finShift_eq_add vc.i_max hb,
      add_sub_cancel_left, add_sub_cancel_left] at hsub
    exact hab (congrArg Fin.val hsub)
  have hcb_mem : ∀ j : Fin (cb.m + 3), cb.p_idx j ∈ B := fun j => by
    have h : cb.p_idx j ∈ Finset.univ.image cb.p_idx := Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
    rwa [cb.hp_idx_img] at h
  have himg_eq : Finset.univ.image (S ∘ cb.p_idx) = B.image S := by
    calc Finset.univ.image (S ∘ cb.p_idx)
        = (Finset.univ.image cb.p_idx).image S := Finset.image_image.symm
      _ = B.image S := by rw [cb.hp_idx_img]
  have hl_memB : l ∈ B := hcb_mem _
  have hr_memB : r ∈ B := hcb_mem _
  have hl_notH : l ∉ H := by
    intro hlH
    obtain ⟨kl, hkl0, hkl_lt, hkl_eq, _⟩ := separation hP hn cb vc (Finset.mem_filter.mp hlH).2
    have heq : k_f - 1 = kl := by
      by_contra hne
      exact hidx_inj (k_f - 1) kl (by have := vc.hd_lt; omega) (by have := vc.hd_lt; omega) hne hkl_eq.symm
    have hkl_Kf : kl ∈ Kf := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hkl_lt, hkl0, hkl_eq ▸ hlH⟩
    have := Finset.min'_le Kf kl hkl_Kf
    omega
  have hr_notH : r ∉ H := by
    intro hrH
    obtain ⟨kr, hkr0, hkr_lt, hkr_eq, _⟩ := separation hP hn cb vc (Finset.mem_filter.mp hrH).2
    have heq : k_g + 1 = kr := by
      by_contra hne
      exact hidx_inj (k_g + 1) kr (by have := vc.hd_lt; omega) (by have := vc.hd_lt; omega) hne hkr_eq.symm
    have hkr_Kf : kr ∈ Kf := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hkr_lt, hkr0, hkr_eq ▸ hrH⟩
    have := Finset.le_max' Kf kr hkr_Kf
    omega
  have hl_ne_r : l ≠ r := hidx_inj (k_f - 1) (k_g + 1)
    (by have := vc.hd_lt; omega) (by have := vc.hd_lt; omega) (by omega)
  have h_only_if : ∀ k : ℕ, k < cb.m + 3 →
      cb.p_idx (finShift vc.i_max k) ∈ H → k_f ≤ k ∧ k ≤ k_g := by
    intro k hk hkH
    obtain ⟨kh, hkh0, hkh_lt, hkh_eq, _⟩ := separation hP hn cb vc (Finset.mem_filter.mp hkH).2
    have heq : k = kh := by
      by_contra hne
      exact hidx_inj k kh hk (by have := vc.hd_lt; omega) hne hkh_eq.symm
    subst heq
    have hk_Kf : k ∈ Kf := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hkh_lt, hkh0, hkH⟩
    exact ⟨Finset.min'_le Kf k hk_Kf, Finset.le_max' Kf k hk_Kf⟩
  have h_part_ii : ∀ h ∈ H, ∀ x_idx : Finset (Fin n),
      Sees P (w x_idx) (S l) → Sees P (w x_idx) (S r) →
      InOpenTri (w x_idx) (S l) (S r) (S h) := by
    intro h hh x_idx hxl hxr
    have hcert := (Finset.mem_filter.mp hh).2
    obtain ⟨kh, hkh0, hkh_lt, hkh_eq, hleft, hright, _⟩ := separation hP hn cb vc hcert
    have hk_range : k_f ≤ kh ∧ kh ≤ k_g := h_only_if kh (by have := vc.hd_lt; omega) (hkh_eq ▸ hh)
    have h1 := hleft (k_f - 1) (by omega)
    have h2 := hright (k_g + 1) (by omega) (by omega)
    have hl_ne_h : l ≠ h := by
      rw [← hkh_eq]; exact hidx_inj (k_f - 1) kh (by have := vc.hd_lt; omega) (by have := vc.hd_lt; omega) (by omega)
    have hr_ne_h : r ≠ h := by
      rw [← hkh_eq]; exact hidx_inj (k_g + 1) kh (by have := vc.hd_lt; omega) (by have := vc.hd_lt; omega) (by omega)
    exact side_corners hP hn hcert hl_memB hr_memB hl_ne_h hr_ne_h (mul_neg_of_pos_of_neg h1 h2) x_idx hxl hxr
  have h_part_iii : (interiorPoints S).card + H.card ≤ 5 := by
    apply hidden_targets hP H (Finset.filter_subset _ _)
    intro h hh
    have hl_notin : l ∉ H := hl_notH
    have hr_notin : r ∉ H := hr_notH
    have hl_ne_h : l ≠ h := fun heq => hl_notH (heq ▸ hh)
    have hr_ne_h : r ≠ h := fun heq => hr_notH (heq ▸ hh)
    refine ⟨l, Finset.mem_sdiff.mpr ⟨hl_memB, hl_notH⟩, r, Finset.mem_sdiff.mpr ⟨hr_memB, hr_notH⟩,
      Finset.univ.erase h, ?_, ?_, ?_, ?_⟩
    · exact (hP.shatters (Finset.univ.erase h) l).mpr (Finset.mem_erase.mpr ⟨hl_ne_h, Finset.mem_univ _⟩)
    · exact (hP.shatters (Finset.univ.erase h) r).mpr (Finset.mem_erase.mpr ⟨hr_ne_h, Finset.mem_univ _⟩)
    · exact fun hs => (Finset.mem_erase.mp ((hP.shatters (Finset.univ.erase h) h).mp hs)).1 rfl
    · exact h_part_ii h hh (Finset.univ.erase h)
        ((hP.shatters (Finset.univ.erase h) l).mpr (Finset.mem_erase.mpr ⟨hl_ne_h, Finset.mem_univ _⟩))
        ((hP.shatters (Finset.univ.erase h) r).mpr (Finset.mem_erase.mpr ⟨hr_ne_h, Finset.mem_univ _⟩))
  have h_if : ∀ k : ℕ, k_f ≤ k → k ≤ k_g → cb.p_idx (finShift vc.i_max k) ∈ H := by
    intro k hk1 hk2
    by_cases hkf_eq : k = k_f
    · subst hkf_eq; exact hkf_inH
    by_cases hkg_eq : k = k_g
    · subst hkg_eq; exact hkg_inH
    have hk_strict : k_f < k ∧ k < k_g := ⟨lt_of_le_of_ne hk1 (Ne.symm hkf_eq), lt_of_le_of_ne hk2 hkg_eq⟩
    let i_l := finShift vc.i_max (k_f - 1)
    let i_f := finShift vc.i_max k_f
    let i_t := finShift vc.i_max k
    let i_g := finShift vc.i_max k_g
    let i_r := finShift vc.i_max (k_g + 1)
    let t := cb.p_idx i_t
    let f := cb.p_idx i_f
    let g := cb.p_idx i_g
    let x_idx := Finset.univ.erase t
    let x := w x_idx
    have htB : t ∈ B := hcb_mem i_t
    have htl : t ≠ l := hidx_inj k (k_f - 1) (by have := vc.hd_lt; omega) (by have := vc.hd_lt; omega) (by omega)
    have htr : t ≠ r := hidx_inj k (k_g + 1) (by have := vc.hd_lt; omega) (by have := vc.hd_lt; omega) (by omega)
    have hxl : Sees P x (S l) := (hP.shatters x_idx l).mpr (Finset.mem_erase.mpr ⟨htl.symm, Finset.mem_univ _⟩)
    have hxr : Sees P x (S r) := (hP.shatters x_idx r).mpr (Finset.mem_erase.mpr ⟨htr.symm, Finset.mem_univ _⟩)
    have htri_f : InOpenTri x (S l) (S r) (S f) := h_part_ii f hkf_inH x_idx hxl hxr
    have htri_g : InOpenTri x (S l) (S r) (S g) := h_part_ii g hkg_inH x_idx hxl hxr
    have hccw_f : 0 < orient2D (S l) (S f) (S r) :=
      cb.hcyc i_l i_f i_r (cyclicOrder_finShift vc.i_max (by omega) (by omega) (by have := vc.hd_lt; omega))
    have hccw_g : 0 < orient2D (S l) (S g) (S r) :=
      cb.hcyc i_l i_g i_r (cyclicOrder_finShift vc.i_max (by omega) (by omega) (by have := vc.hd_lt; omega))
    have htri_front : ∀ u : Fin n, InOpenTri x (S l) (S r) (S u) →
        0 < orient2D (S l) (S u) (S r) → u ∈ B → IsFrontVertex (B.image S) x (S u) := by
      intro u htriu hccwu huB
      have hlu : S l ≠ S u := by intro heq; rw [heq, orient2D_self_left] at hccwu; linarith
      have hur : S u ≠ S r := by intro heq; rw [heq, orient2D_self_right] at hccwu; linarith
      have hlr : S l ≠ S r := fun heq => hl_ne_r (hP.s_inj heq)
      have hedge_lu : IsCCWHullEdge {S l, S u, S r} (S l) (S u) := by
        refine ⟨by simp, by simp, hlu, fun z hz hzl hzu => ?_⟩
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl | rfl
        · exact False.elim (hzl rfl)
        · exact False.elim (hzu rfl)
        · exact hccwu
      have hedge_ur : IsCCWHullEdge {S l, S u, S r} (S u) (S r) := by
        refine ⟨by simp, by simp, hur, fun z hz hzu hzr => ?_⟩
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl | rfl
        · have : orient2D (S u) (S r) (S l) = orient2D (S l) (S u) (S r) := by unfold orient2D; ring
          linarith
        · exact False.elim (hzu rfl)
        · exact False.elim (hzr rfl)
      have hfront_tri := (isFrontVertex_iff_inOpenTri' hedge_lu hedge_ur hlr).mpr htriu
      have hb_img : ∃ b' c' : ℝ × ℝ, IsCCWHullEdge (B.image S) b' (S u) ∧ IsCCWHullEdge (B.image S) (S u) c' := by
        rw [← himg_eq]
        rcases Finset.mem_image.mp (by rw [cb.hp_idx_img]; exact huB : u ∈ Finset.univ.image cb.p_idx) with ⟨iu, _, rfl⟩
        exact ⟨_, _,
          (isCCWHullEdge_iff_succ cb.hstrict (hP.s_inj.comp cb.hp_idx_inj)).mpr
            ⟨iu - 1, rfl, congrArg (S ∘ cb.p_idx) (sub_add_cancel iu 1)⟩,
          (isCCWHullEdge_iff_succ cb.hstrict (hP.s_inj.comp cb.hp_idx_inj)).mpr ⟨iu, rfl, rfl⟩⟩
      rcases hb_img with ⟨b', c', hb'u, huc'⟩
      have hsub_tri : ({S l, S u, S r} : Finset (ℝ × ℝ)) ⊆ B.image S := by
        intro z hz; simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl | rfl
        · exact Finset.mem_image.mpr ⟨l, hl_memB, rfl⟩
        · exact Finset.mem_image.mpr ⟨u, huB, rfl⟩
        · exact Finset.mem_image.mpr ⟨r, hr_memB, rfl⟩
      exact front_restoration hsub_tri (hullVertices_isConvexPos hP) (by simp) hfront_tri hb'u huc'
    have hx_front_f : IsFrontVertex (B.image S) x (S f) :=
      htri_front f htri_f hccw_f (hcb_mem i_f)
    have hx_front_g : IsFrontVertex (B.image S) x (S g) :=
      htri_front g htri_g hccw_g (hcb_mem i_g)
    have hx_out : x ∉ convexHull ℝ ((Finset.univ.image (S ∘ cb.p_idx) : Finset (ℝ × ℝ)) : Set (ℝ × ℝ)) := by
      rw [himg_eq]
      exact not_mem_convexHull_of_isFrontVertex hx_front_f
    have hvcx_ne := exists_visibleContour (S ∘ cb.p_idx) cb.hstrict (hP.s_inj.comp cb.hp_idx_inj) hx_out (fun i j hij =>
      hP.no_three_collinear (S (cb.p_idx i)) (S (cb.p_idx j)) x
        (Or.inl ⟨cb.p_idx i, rfl⟩) (Or.inl ⟨cb.p_idx j, rfl⟩) (Or.inr ⟨x_idx, rfl⟩)
        (fun h => hij (cb.hp_idx_inj (hP.s_inj h))) (hP.s_ne_w _ _) (hP.s_ne_w _ _))
    rcases hvcx_ne with ⟨vc_x⟩
    obtain ⟨kfx, hkfx0, hkfx_lt, hifx⟩ := (vc_x.h_front_iff i_f).mp (by rw [himg_eq]; exact hx_front_f)
    obtain ⟨kgx, hkgx0, hkgx_lt, higx⟩ := (vc_x.h_front_iff i_g).mp (by rw [himg_eq]; exact hx_front_g)
    have hfx_ne_gx : kfx ≠ kgx := by
      intro heq
      have h1 : i_f = i_g := by rw [hifx, higx, heq]
      have hsub := congrArg (· - vc.i_max) h1
      dsimp [i_f, i_g] at hsub
      have := vc.hd_lt
      rw [finShift_eq_add vc.i_max (by omega : k_f < cb.m + 3),
        finShift_eq_add vc.i_max (by omega : k_g < cb.m + 3),
        add_sub_cancel_left, add_sub_cancel_left] at hsub
      have := congrArg Fin.val hsub
      simp only at this; omega
    have hkf_lt_kg : kfx < kgx := by
      by_contra hle
      have hgt : kgx < kfx := lt_of_le_of_ne (not_lt.mp hle) hfx_ne_gx.symm
      have hd_vc := vc.hd_lt
      have hd_vx := vc_x.hd_lt
      have hdiff_eq : (i_f - i_g).val = (cb.m + 3) - (k_g - k_f) := by
        have hstep1 : i_g + ⟨(cb.m + 3) - (k_g - k_f), by omega⟩ = i_f := by
          dsimp [i_g, i_f]
          rw [← finShift_eq_add _ (by omega : (cb.m + 3) - (k_g - k_f) < cb.m + 3), finShift_add]
          have h1 : k_g + ((cb.m + 3) - (k_g - k_f)) = k_f + (cb.m + 3) := by omega
          rw [h1, ← finShift_add, finShift_len]
        have h2 : i_f - i_g = ⟨(cb.m + 3) - (k_g - k_f), by omega⟩ := (eq_sub_of_add_eq' hstep1).symm
        rw [h2]
      have hdiff_x : (i_f - i_g).val = kfx - kgx := by
        have hstep1 : i_g + ⟨kfx - kgx, by omega⟩ = i_f := by
          rw [higx, hifx, ← finShift_eq_add _ (by omega : kfx - kgx < cb.m + 3), finShift_add]
          congr 1; omega
        have h2 : i_f - i_g = ⟨kfx - kgx, by omega⟩ := (eq_sub_of_add_eq' hstep1).symm
        rw [h2]
      have hd_large : kfx - kgx ≥ 3 := by omega
      have hir_pos : i_r = finShift vc_x.i_max (kgx + 1) := by
        have hir_eq : i_r = i_g + 1 := by
          dsimp [i_r, i_g]
          exact (finShift_succ (by omega : 2 ≤ cb.m + 3) vc.i_max k_g).symm
        rw [hir_eq, higx]
        exact finShift_succ (by omega : 2 ≤ cb.m + 3) vc_x.i_max kgx
      have hil_pos : i_l = finShift vc_x.i_max (kfx - 1) := by
        dsimp [i_l]
        rw [← (by
          have h1 : k_f - 1 + 1 = k_f := by omega
          have := finShift_pred (by omega : 2 ≤ cb.m + 3) vc.i_max (k_f - 1)
          rw [h1] at this; exact this : i_f - 1 = finShift vc.i_max (k_f - 1))]
        rw [hifx]
        conv_lhs => rw [show kfx = kfx - 1 + 1 by omega]
        exact finShift_pred (by omega : 2 ≤ cb.m + 3) vc_x.i_max (kfx - 1)
      have hs1 : vc_x.slope i_l < vc_x.slope i_r := by
        rw [hil_pos, hir_pos]
        exact near_slope_strictAnti vc_x (by omega) (by omega)
      have hs2 : vc_x.slope i_f < vc_x.slope i_l := by
        rw [hifx, hil_pos]
        exact near_slope_strictAnti vc_x (by omega) (by omega)
      have hbtw := inOpenTri_slope_between vc_x (by
        intro heq; exact hl_ne_r (congrArg cb.p_idx heq)) (by
        change InOpenTri x ((S ∘ cb.p_idx) i_l) ((S ∘ cb.p_idx) i_r) ((S ∘ cb.p_idx) i_f)
        exact htri_f)
      rcases hbtw with ⟨ha, hb⟩ | ⟨ha, hb⟩ <;> linarith
    have hgap : kgx - kfx = k_g - k_f := by
      have hd_vc := vc.hd_lt
      have hd_vx := vc_x.hd_lt
      have hstep_b : i_f + ⟨k_g - k_f, by omega⟩ = i_g := by
        dsimp [i_f, i_g]
        rw [← finShift_eq_add _ (by omega : k_g - k_f < cb.m + 3), finShift_add]
        congr 1; omega
      have hstep_x : i_f + ⟨kgx - kfx, by omega⟩ = i_g := by
        rw [hifx, higx, ← finShift_eq_add _ (by omega : kgx - kfx < cb.m + 3), finShift_add]
        congr 1; omega
      have heq1 : (⟨k_g - k_f, by omega⟩ : Fin (cb.m + 3)) = i_g - i_f := eq_sub_of_add_eq' hstep_b
      have heq2 : (⟨kgx - kfx, by omega⟩ : Fin (cb.m + 3)) = i_g - i_f := eq_sub_of_add_eq' hstep_x
      have hv := congrArg Fin.val (heq1.trans heq2.symm)
      simp only at hv
      omega
    have hkt_x : i_t = finShift vc_x.i_max (kfx + (k - k_f)) := by
      have hsub : i_t = finShift i_f (k - k_f) := by
        dsimp [i_t, i_f]
        rw [finShift_add]
        congr 1; omega
      rw [hsub, hifx, finShift_add]
    have hfront_t : IsFrontVertex (B.image S) x (S t) := by
      rw [← himg_eq]
      change IsFrontVertex (Finset.univ.image (S ∘ cb.p_idx)) x ((S ∘ cb.p_idx) i_t)
      rw [vc_x.h_front_iff]
      exact ⟨kfx + (k - k_f), by omega, by omega, hkt_x⟩
    refine Finset.mem_filter.mpr ⟨htB, htB, x_idx, ?_, ?_, hfront_t⟩
    · exact fun hs => (Finset.mem_erase.mp ((hP.shatters x_idx t).mp hs)).1 rfl
    · intro u _ hedge
      have hut : u ≠ t := by
        rintro rfl
        rcases hedge with h | h <;> exact h.2.2.1 rfl
      exact (hP.shatters x_idx u).mpr (Finset.mem_erase.mpr ⟨hut, Finset.mem_univ _⟩)
  refine ⟨k_f, k_g, l, r, hkf_pos, hkf_le_kg, hkg_lt, rfl, rfl,
    Finset.mem_sdiff.mpr ⟨hl_memB, hl_notH⟩, Finset.mem_sdiff.mpr ⟨hr_memB, hr_notH⟩,
    hl_ne_r, ?_, h_part_ii, h_part_iii⟩
  intro k hk
  exact ⟨fun ⟨h1, h2⟩ => h_if k h1 h2, h_only_if k hk⟩

private lemma eps_blend_al (β eps : ℝ) (h : 1 + eps ≠ 0) :
    (β + (1 - β) * (eps / (1 + eps))) -
      (1 - (β + (1 - β) * (eps / (1 + eps)))) * eps = β := by
  field_simp [h]; ring

private lemma eps_blend_ar (β eps : ℝ) (h : 1 + eps ≠ 0) :
    (1 - (β + (1 - β) * (eps / (1 + eps)))) * (1 + eps) = 1 - β := by
  field_simp [h]; ring

private lemma exit_edge_non_lr_isCCW {n : ℕ} {P : Set (ℝ × ℝ)} {S : Fin n → ℝ × ℝ}
    {w : Finset (Fin n) → ℝ × ℝ}
    (hP : ShatteredSimplePolygon P S w) (hn : 3 ≤ n)
    (cb : CyclicSubsetBoundary S (hullVertices S))
    (vc : VisibleContour (S ∘ cb.p_idx) (w Finset.univ))
    (dc : CyclicSubsetBoundary S (hullVertices S \ certifiedSet P S w))
    {k_f k_g : ℕ} {l r : Fin n}
    (hkf0 : 0 < k_f) (hkfg : k_f ≤ k_g) (hkg_lt : k_g < vc.d_near)
    (hl_eq : l = cb.p_idx (finShift vc.i_max (k_f - 1)))
    (hr_eq : r = cb.p_idx (finShift vc.i_max (k_g + 1)))
    (hlD : l ∈ hullVertices S \ certifiedSet P S w)
    (hrD : r ∈ hullVertices S \ certifiedSet P S w)
    (hblock : ∀ k : ℕ, k < cb.m + 3 →
      (k_f ≤ k ∧ k ≤ k_g ↔ cb.p_idx (finShift vc.i_max k) ∈ certifiedSet P S w))
    (hpart_ii : ∀ h ∈ certifiedSet P S w, ∀ x_idx : Finset (Fin n),
      Sees P (w x_idx) (S l) → Sees P (w x_idx) (S r) → InOpenTri (w x_idx) (S l) (S r) (S h))
    (i_lr : Fin (dc.m + 3)) (hilr_eq : dc.p_idx i_lr = l)
    (j : Fin (dc.m + 3)) (hj_lr : j ≠ i_lr) :
    IsCCWHullEdge ((hullVertices S).image S) (S (dc.p_idx j)) (S (dc.p_idx (j + 1))) := by
  let B := hullVertices S
  let H := certifiedSet P S w
  let D := B \ H
  let u := w D
  let p := S ∘ dc.p_idx
  let _ := hkf0
  let _ := hkfg
  let _ := hkg_lt
  let _ := hr_eq
  have hdc_mem : ∀ k : Fin (dc.m + 3), dc.p_idx k ∈ D := fun k => by
    have h : dc.p_idx k ∈ Finset.univ.image dc.p_idx := Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩
    rwa [dc.hp_idx_img] at h
  have h_edge_ne : ∀ k : Fin (dc.m + 3), dc.p_idx k ≠ dc.p_idx (k + 1) := by
    intro k heq
    have hinj := dc.hp_idx_inj heq
    nth_rw 1 [← add_zero k] at hinj
    have h01 : (0 : Fin (dc.m + 3)) = 1 := add_left_cancel hinj
    have hv := congrArg Fin.val h01
    simp [Nat.mod_eq_of_lt (by omega : 1 < dc.m + 3)] at hv
  refine ⟨Finset.mem_image.mpr ⟨dc.p_idx j, (Finset.mem_sdiff.mp (hdc_mem j)).1, rfl⟩,
    Finset.mem_image.mpr ⟨dc.p_idx (j + 1), (Finset.mem_sdiff.mp (hdc_mem (j + 1))).1, rfl⟩,
    fun h => h_edge_ne j (hP.s_inj h), fun c hc hca hcb => ?_⟩
  rcases Finset.mem_image.mp hc with ⟨b, hbB, rfl⟩
  by_cases hbD : b ∈ D
  · have hb_img : b ∈ Finset.univ.image dc.p_idx := by rw [dc.hp_idx_img]; exact hbD
    rcases Finset.mem_image.mp hb_img with ⟨jb, _, rfl⟩
    exact dc.hstrict j jb (fun h => hca (congrArg p h)) (fun h => hcb (congrArg p h))
  · have hbH : b ∈ H := by by_contra hnot; exact hbD (Finset.mem_sdiff.mpr ⟨hbB, hnot⟩)
    have htri_b := hpart_ii b hbH D ((hP.shatters D l).mpr hlD) ((hP.shatters D r).mpr hrD)
    let _ := (inOpenTri_mem_convexHull htri_b)
    -- Use h_lr_edge_D / dc.p_idx j ≠ i_lr: on ∂ conv B, H is inside Δ(q, l, r) and between l, r!
    have hbi : b ∈ Finset.univ.image cb.p_idx := by rw [cb.hp_idx_img]; exact hbB
    rcases Finset.mem_image.mp hbi with ⟨kb_fin, _, rfl⟩
    obtain ⟨kh, hkh0, hkh_lt, hkh_eq, _⟩ := separation hP hn cb vc (Finset.mem_filter.mp hbH).2
    have hkh_range := (hblock kh (by have := vc.hd_lt; omega)).mpr (hkh_eq ▸ hbH)
    -- Since p j and p (j+1) are in D and (j ≠ i_lr), walking CCW on ∂ conv B from j to j+1 doesn't cross H!
    have hj_img : dc.p_idx j ∈ Finset.univ.image cb.p_idx := by
      rw [cb.hp_idx_img]; exact (Finset.mem_sdiff.mp (hdc_mem j)).1
    have hj1_img : dc.p_idx (j + 1) ∈ Finset.univ.image cb.p_idx := by
      rw [cb.hp_idx_img]; exact (Finset.mem_sdiff.mp (hdc_mem (j + 1))).1
    rcases Finset.mem_image.mp hj_img with ⟨ij, _, hij⟩
    rcases Finset.mem_image.mp hj1_img with ⟨ij1, _, hij1⟩
    -- Wait: why is 0 < orient2D (p j) (p (j+1)) (S (cb.p_idx kb_fin))?
    -- Actually notice: S l, S r ∈ conv D so 0 ≤ orient2D (p j) (p (j+1)) (S l) and (S r)!
    -- If orient2D (p j) (p (j+1)) (S (cb.p_idx kb_fin)) ≤ 0, then since 0 < orient2D (p j) (p (j+1)) (S d) for all d ∈ D \ {j, j+1}
    -- wait if S b is on ≤ 0 side of p j -> p (j+1), could (p j, p (j+1)) have S b on the ≤ 0 side?!
    -- Check! b is in H (strictly on the [k_f .. k_g] arc between l and r), while p j, p(j+1) ∈ D!
    -- On ∂ conv B, let kj := (ij - vc.i_max).val and kj1 := (ij1 - vc.i_max).val!
    -- Wait: if kj and kj1 are NOT adjacent in B? The only non-adjacent edge of D in B is (l, r), which would mean ij = i_l and ij1 = i_r, i.e., j = i_lr!
    -- Let's prove ij1 = ij + 1!
    have hij_succ : ij1 = ij + 1 := by
      by_contra hne_s
      have hpB_inj : Function.Injective (S ∘ cb.p_idx) := hP.s_inj.comp cb.hp_idx_inj
      have h_succ_ne_j : cb.p_idx (ij + 1) ≠ dc.p_idx j := by
        intro heq
        have h10 : ij + 0 = ij + 1 := by rw [add_zero]; exact (cb.hp_idx_inj (heq.trans hij.symm)).symm
        have hv := congrArg Fin.val (add_left_cancel h10)
        have h1v : (1 : Fin (cb.m + 3)).val = 1 := by
          change 1 % (cb.m + 3) = 1; exact Nat.mod_eq_of_lt (by omega)
        rw [Fin.val_zero, h1v] at hv; omega
      have h_succ_ne_j1 : cb.p_idx (ij + 1) ≠ dc.p_idx (j + 1) :=
        fun heq => hne_s (cb.hp_idx_inj (hij1.trans heq.symm))
      have h_succ_inB : cb.p_idx (ij + 1) ∈ B := by
        have h' : cb.p_idx (ij + 1) ∈ Finset.univ.image cb.p_idx := Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩
        rwa [cb.hp_idx_img] at h'
      by_cases hs_D : cb.p_idx (ij + 1) ∈ D
      · have h_img_D : cb.p_idx (ij + 1) ∈ Finset.univ.image dc.p_idx := by rw [dc.hp_idx_img]; exact hs_D
        rcases Finset.mem_image.mp h_img_D with ⟨js, _, hjs⟩
        have ho1 := dc.hstrict j js (fun h => h_succ_ne_j (hjs.symm ▸ congrArg dc.p_idx h))
          (fun h => h_succ_ne_j1 (hjs.symm ▸ congrArg dc.p_idx h))
        have ho2 := cb.hstrict ij ij1 (fun h => h_edge_ne j (hij ▸ hij1 ▸ congrArg cb.p_idx h.symm))
          (fun h => hne_s h)
        change 0 < orient2D (S (dc.p_idx j)) (S (dc.p_idx (j + 1))) (S (dc.p_idx js)) at ho1
        rw [hjs] at ho1
        change 0 < orient2D (S (cb.p_idx ij)) (S (cb.p_idx (ij + 1))) (S (cb.p_idx ij1)) at ho2
        rw [hij, hij1] at ho2
        rw [orient2D_swap23] at ho2
        linarith [ho1, ho2]
      · have hs_H : cb.p_idx (ij + 1) ∈ H := by
          by_contra hnot; exact hs_D (Finset.mem_sdiff.mpr ⟨h_succ_inB, hnot⟩)
        -- Wait: if cb.p_idx (ij + 1) ∈ H, then since ij ∈ D, ij MUST BE l (and ij + 1 = f)!
        -- And if ij = l, what can ij1 ∈ D be?! Any d ∈ D \ {l, r} has 0 < orient2D (S l) (S r) (S d), so r would be between (l, d) unless ij1 = r!
        obtain ⟨ks, hks0, hks_lt, hks_eq, _⟩ := separation hP hn cb vc (Finset.mem_filter.mp hs_H).2
        have hks_range := (hblock ks (by have := vc.hd_lt; omega)).mpr (hks_eq ▸ hs_H)
        have hij_eq_l : ij = finShift vc.i_max (k_f - 1) := by
          have hpred_eq : cb.p_idx (finShift vc.i_max (ks - 1)) = cb.p_idx ij := by
            apply congrArg cb.p_idx
            have hsucc : ij + 1 = finShift vc.i_max ks := cb.hp_idx_inj hks_eq.symm
            have h1 : ks - 1 + 1 = ks := by omega
            have hadd : finShift vc.i_max (ks - 1) + 1 = ij + 1 := by
              rw [finShift_succ (by omega : 2 ≤ cb.m + 3) vc.i_max (ks - 1), h1, hsucc]
            exact add_right_cancel hadd
          have hpred_idx : ij = finShift vc.i_max (ks - 1) := (cb.hp_idx_inj hpred_eq).symm
          by_cases hks_kf : ks = k_f
          · rw [hpred_idx, hks_kf]
          · exfalso
            have hpred_H : cb.p_idx ij ∈ H := by
              rw [hpred_idx]
              exact (hblock (ks - 1) (by have := vc.hd_lt; omega)).mp ⟨by omega, by omega⟩
            rw [hij] at hpred_H
            exact (Finset.mem_sdiff.mp (hdc_mem j)).2 hpred_H
        have h_dc_l : dc.p_idx j = l := by rw [← hij, hij_eq_l, ← hl_eq]
        have hj_eq_ilr : j = i_lr := dc.hp_idx_inj (h_dc_l.trans hilr_eq.symm)
        exact hj_lr hj_eq_ilr
    have hk_ne_ij : kb_fin ≠ ij := fun h => hca (by rw [← hij, h])
    have hk_ne_ij1 : kb_fin ≠ ij + 1 := fun h => hcb (by rw [← hij1, hij_succ, h])
    have hres := cb.hstrict ij kb_fin hk_ne_ij hk_ne_ij1
    change 0 < orient2D (S (cb.p_idx ij)) (S (cb.p_idx (ij + 1))) (S (cb.p_idx kb_fin)) at hres
    rwa [← hij_succ, hij, hij1] at hres

private lemma exit_edge_lr_perturb {n : ℕ} {P : Set (ℝ × ℝ)} {S : Fin n → ℝ × ℝ}
    {w : Finset (Fin n) → ℝ × ℝ}
    (hP : ShatteredSimplePolygon P S w)
    (dc : CyclicSubsetBoundary S (hullVertices S \ certifiedSet P S w))
    (y : Fin n)
    (hy_notin_D : y ∉ hullVertices S \ certifiedSet P S w)
    (β : ℝ) (hβ_pos : 0 < β) (hβ_lt1 : β < 1) (z' : ℝ × ℝ)
    (hz'_range : z' ∈ convexHull ℝ (Set.range (S ∘ dc.p_idx)))
    (h_nonneg_edge : ∀ j : Fin (dc.m + 3), ∀ q ∈ convexHull ℝ (Set.range (S ∘ dc.p_idx)),
      0 ≤ orient2D ((S ∘ dc.p_idx) j) ((S ∘ dc.p_idx) (j + 1)) q)
    {l r : Fin n} (hlD : l ∈ hullVertices S \ certifiedSet P S w)
    (hrD : r ∈ hullVertices S \ certifiedSet P S w) (hl_ne_r : l ≠ r)
    (i_lr : Fin (dc.m + 3)) (hilr_eq : dc.p_idx i_lr = l) (hir_eq : dc.p_idx (i_lr + 1) = r)
    (h_lr_u_neg : orient2D (S l) (S r) (w (hullVertices S \ certifiedSet P S w)) < 0)
    (hj0 : orient2D ((S ∘ dc.p_idx) i_lr) ((S ∘ dc.p_idx) (i_lr + 1)) z' = 0)
    (hy_decomp : S y = β • w (hullVertices S \ certifiedSet P S w) + (1 - β) • z') :
    ∃ z'' : ℝ × ℝ, ∃ β' : ℝ, 0 < β' ∧ β' < 1 ∧
      z'' ∈ convexHull ℝ (Set.range (S ∘ dc.p_idx)) ∧
      (∀ k : Fin (dc.m + 3), 0 < orient2D ((S ∘ dc.p_idx) k) ((S ∘ dc.p_idx) (k + 1)) z'') ∧
      S y = β' • w (hullVertices S \ certifiedSet P S w) + (1 - β') • z'' := by
  let B := hullVertices S
  let H := certifiedSet P S w
  let D := B \ H
  let u := w D
  let p := S ∘ dc.p_idx
  have hdc_mem : ∀ k : Fin (dc.m + 3), dc.p_idx k ∈ D := fun k => by
    have h : dc.p_idx k ∈ Finset.univ.image dc.p_idx := Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩
    rwa [dc.hp_idx_img] at h
  have hj0' : orient2D (p i_lr) (p (i_lr + 1)) z' = 0 := hj0
  have h_seg_lr : ∃ s : ℝ, 0 < s ∧ s < 1 ∧ z' = (1 - s) • S l + s • S r := by
    have hid_z' : orient2D (p i_lr) (p (i_lr + 1)) z' = 0 := hj0'
    have hpl : p i_lr = S l := by dsimp [p]; rw [hilr_eq]
    have hpr : p (i_lr + 1) = S r := by dsimp [p]; rw [hir_eq]
    rw [hpl, hpr] at hid_z'
    have hlr_s : S l ≠ S r := fun h => hl_ne_r (hP.s_inj h)
    have hcoord : (S r).1 - (S l).1 ≠ 0 ∨ (S r).2 - (S l).2 ≠ 0 := by
      by_contra hc; push Not at hc; exact hlr_s (by ext <;> linarith)
    obtain ⟨s, hs1, hs2⟩ : ∃ s : ℝ,
        z'.1 = (1 - s) * (S l).1 + s * (S r).1 ∧
        z'.2 = (1 - s) * (S l).2 + s * (S r).2 := by
      unfold orient2D at hid_z'
      rcases hcoord with hx | hyc
      · refine ⟨(z'.1 - (S l).1) / ((S r).1 - (S l).1), by field_simp [hx]; ring,
          by field_simp [hx]; linear_combination hid_z'⟩
      · refine ⟨(z'.2 - (S l).2) / ((S r).2 - (S l).2),
          by field_simp [hyc]; linear_combination -hid_z', by field_simp [hyc]; ring⟩
    have h1v : (1 : Fin (dc.m + 3)).val = 1 := by
      change 1 % (dc.m + 3) = 1; exact Nat.mod_eq_of_lt (by omega)
    have h11v : ((1 + 1 : Fin (dc.m + 3)) : ℕ) = 2 := by
      rw [Fin.val_add, h1v]; exact Nat.mod_eq_of_lt (by omega)
    have hs_ge0 : 0 ≤ s := by
      have hnn := h_nonneg_edge (i_lr - 1) z' hz'_range
      rw [sub_add_cancel] at hnn
      have h_pre : 0 < orient2D (p (i_lr - 1)) (S l) (S r) := by
        have h1 := dc.hstrict (i_lr - 1) (i_lr + 1)
          (by
            intro heq
            have h' := congrArg (· + (1 : Fin (dc.m + 3))) heq
            rw [sub_add_cancel, add_assoc] at h'
            have heq' : i_lr + 0 = i_lr + (1 + 1) := by rw [add_zero]; exact h'.symm
            have hv := congrArg Fin.val (add_left_cancel heq')
            rw [Fin.val_zero, h11v] at hv; omega)
          (by
            intro heq
            rw [sub_add_cancel] at heq
            have heq' : i_lr + 0 = i_lr + 1 := by rw [add_zero]; exact heq.symm
            have hv := congrArg Fin.val (add_left_cancel heq')
            rw [Fin.val_zero, h1v] at hv; omega)
        rw [sub_add_cancel] at h1
        change 0 < orient2D (p (i_lr - 1)) (p i_lr) (p (i_lr + 1)) at h1
        rw [hpl, hpr] at h1; exact h1
      change 0 ≤ orient2D (p (i_lr - 1)) (p i_lr) z' at hnn
      rw [hpl] at hnn
      have hid := orient2D_affine_comb (p (i_lr - 1)) (S l) (S l) (S r) z' s hs1 hs2
      rw [orient2D_self_right, mul_zero, zero_add] at hid
      rw [hid] at hnn
      exact nonneg_of_mul_nonneg_left hnn h_pre
    have hs_le1 : s ≤ 1 := by
      have hnn := h_nonneg_edge (i_lr + 1) z' hz'_range
      have h_suc : 0 < orient2D (S r) (p (i_lr + 1 + 1)) (S l) := by
        have h1 := dc.hstrict (i_lr + 1) i_lr
          (by intro heq
              have heq' : i_lr + 0 = i_lr + 1 := by rw [add_zero]; exact heq
              have hv := congrArg Fin.val (add_left_cancel heq')
              rw [Fin.val_zero, h1v] at hv; omega)
          (by intro heq; rw [add_assoc] at heq
              have heq' : i_lr + 0 = i_lr + (1 + 1) := by rw [add_zero]; exact heq
              have hv := congrArg Fin.val (add_left_cancel heq')
              rw [Fin.val_zero, h11v] at hv; omega)
        change 0 < orient2D (p (i_lr + 1)) (p (i_lr + 1 + 1)) (p i_lr) at h1
        rw [hpl, hpr] at h1; exact h1
      change 0 ≤ orient2D (p (i_lr + 1)) (p (i_lr + 1 + 1)) z' at hnn
      rw [hpr] at hnn
      have hid := orient2D_affine_comb (S r) (p (i_lr + 1 + 1)) (S l) (S r) z' s hs1 hs2
      rw [orient2D_self_outer, mul_zero, add_zero] at hid
      rw [hid] at hnn
      have h1s := nonneg_of_mul_nonneg_left hnn h_suc
      linarith
    have hs_gt0 : 0 < s := by
      refine lt_of_le_of_ne hs_ge0 (fun hs0 => ?_)
      have hzl : z' = S l := by ext <;> [rw [hs1, ← hs0]; rw [hs2, ← hs0]] <;> ring
      rw [hzl] at hy_decomp
      have hcol : orient2D u (S l) (S y) = 0 := by
        have hx1 := congrArg Prod.fst hy_decomp; have hx2 := congrArg Prod.snd hy_decomp
        simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at hx1 hx2
        unfold orient2D; rw [hx1, hx2]; ring
      exact hP.no_three_collinear u (S l) (S y)
        (Or.inr ⟨D, rfl⟩) (Or.inl ⟨l, rfl⟩) (Or.inl ⟨y, rfl⟩)
        (hP.s_ne_w l D).symm (fun h => hy_notin_D (hP.s_inj h ▸ hlD)) (hP.s_ne_w y D).symm hcol
    have hs_lt1 : s < 1 := by
      refine lt_of_le_of_ne hs_le1 (fun hs1' => ?_)
      have hzr : z' = S r := by ext <;> [rw [hs1, hs1']; rw [hs2, hs1']] <;> ring
      rw [hzr] at hy_decomp
      have hcol : orient2D u (S r) (S y) = 0 := by
        have hx1 := congrArg Prod.fst hy_decomp; have hx2 := congrArg Prod.snd hy_decomp
        simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at hx1 hx2
        unfold orient2D; rw [hx1, hx2]; ring
      exact hP.no_three_collinear u (S r) (S y)
        (Or.inr ⟨D, rfl⟩) (Or.inl ⟨r, rfl⟩) (Or.inl ⟨y, rfl⟩)
        (hP.s_ne_w r D).symm (fun h => hy_notin_D (hP.s_inj h ▸ hrD)) (hP.s_ne_w y D).symm hcol
    exact ⟨s, hs_gt0, hs_lt1, by ext <;> [exact hs1; exact hs2]⟩
  rcases h_seg_lr with ⟨s, hs0, hs1, hz'_eq⟩
  let d₀ := p (i_lr + 2)
  have hi2_ne0 : i_lr + 2 ≠ i_lr := by
    intro heq; nth_rw 2 [← add_zero i_lr] at heq
    have h20 := add_left_cancel heq
    have hv := congrArg Fin.val h20
    have : (2 : Fin (dc.m + 3)).val = 2 := by
      change 2 % (dc.m + 3) = 2; exact Nat.mod_eq_of_lt (by omega)
    rw [Fin.val_zero] at hv; omega
  have hi2_ne1 : i_lr + 2 ≠ i_lr + 1 := by
    intro heq; rw [show (2 : Fin (dc.m + 3)) = 1 + 1 from rfl, ← add_assoc] at heq
    nth_rw 2 [← add_zero (i_lr + 1)] at heq
    have h10 := add_left_cancel heq
    have hv := congrArg Fin.val h10
    have : (1 : Fin (dc.m + 3)).val = 1 := by
      change 1 % (dc.m + 3) = 1; exact Nat.mod_eq_of_lt (by omega)
    rw [Fin.val_zero] at hv; omega
  have hd₀_pos : 0 < orient2D (S l) (S r) d₀ := by
    have := dc.hstrict i_lr (i_lr + 2) hi2_ne0 hi2_ne1
    change 0 < orient2D (p i_lr) (p (i_lr + 1)) d₀ at this
    rwa [show p i_lr = S l by dsimp [p]; rw [hilr_eq],
      show p (i_lr + 1) = S r by dsimp [p]; rw [hir_eq]] at this
  have hu_decomp := cramer_2d (S l) (S r) d₀ u (ne_of_gt hd₀_pos)
  let μ_r := orient2D (S l) u d₀ / orient2D (S l) (S r) d₀
  let μ_d := orient2D (S l) (S r) u / orient2D (S l) (S r) d₀
  let μ_l := 1 - μ_r - μ_d
  have hμ_d_neg : μ_d < 0 := div_neg_of_neg_of_pos h_lr_u_neg hd₀_pos
  have hu_vec : u = μ_l • S l + μ_r • S r + μ_d • d₀ := by
    ext
    · change u.1 = μ_l * (S l).1 + μ_r * (S r).1 + μ_d * d₀.1
      have h1 := hu_decomp.1
      dsimp [μ_l, μ_r, μ_d]
      linarith
    · change u.2 = μ_l * (S l).2 + μ_r * (S r).2 + μ_d * d₀.2
      have h2 := hu_decomp.2
      dsimp [μ_l, μ_r, μ_d]
      linarith
  let M_bnd := |1 - s - μ_l| + |s - μ_r| + 1
  have hM_pos : 0 < M_bnd := by positivity
  let eps := min (1 - s) s / (2 * M_bnd)
  have heps_pos : 0 < eps := div_pos (lt_min (by linarith) hs0) (by linarith)
  let z'' := (1 + eps) • z' - eps • u
  let c_l := (1 - s) + eps * (1 - s - μ_l)
  let c_r := s + eps * (s - μ_r)
  let c_d := eps * (-μ_d)
  have hc_l : 0 < c_l := by
    have h1 : eps * |1 - s - μ_l| ≤ (1 - s) / 2 := by
      have hle1 : eps ≤ (1 - s) / (2 * M_bnd) := div_le_div_of_nonneg_right (min_le_left _ _) (by positivity)
      have hle2 : |1 - s - μ_l| ≤ M_bnd := by dsimp [M_bnd]; linarith [abs_nonneg (s - μ_r)]
      calc eps * |1 - s - μ_l| ≤ ((1 - s) / (2 * M_bnd)) * M_bnd :=
            mul_le_mul hle1 hle2 (abs_nonneg _) (div_nonneg (by linarith) (by positivity))
        _ = (1 - s) / 2 := by field_simp [ne_of_gt hM_pos]
    have h2 := neg_abs_le (1 - s - μ_l)
    nlinarith
  have hc_r : 0 < c_r := by
    have h1 : eps * |s - μ_r| ≤ s / 2 := by
      have hle1 : eps ≤ s / (2 * M_bnd) := div_le_div_of_nonneg_right (min_le_right _ _) (by positivity)
      have hle2 : |s - μ_r| ≤ M_bnd := by dsimp [M_bnd]; linarith [abs_nonneg (1 - s - μ_l)]
      calc eps * |s - μ_r| ≤ (s / (2 * M_bnd)) * M_bnd :=
            mul_le_mul hle1 hle2 (abs_nonneg _) (div_nonneg (le_of_lt hs0) (by positivity))
        _ = s / 2 := by field_simp [ne_of_gt hM_pos]
    have h2 := neg_abs_le (s - μ_r)
    nlinarith
  have hc_d : 0 < c_d := mul_pos heps_pos (neg_pos.mpr hμ_d_neg)
  have hc_sum : c_l + c_r + c_d = 1 := by dsimp [c_l, c_r, c_d, μ_l]; ring
  have hz''_eq : z'' = c_l • S l + c_r • S r + c_d • d₀ := by
    dsimp [z'']; rw [hz'_eq, hu_vec]
    ext <;> simp only [Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add,
      Prod.smul_fst, Prod.smul_snd, smul_eq_mul, c_l, c_r, c_d, μ_l] <;> ring
  have hz''_mem : z'' ∈ convexHull ℝ (Set.range p) := by
    rw [hz''_eq]
    have hl_m : S l ∈ convexHull ℝ (Set.range p) := subset_convexHull ℝ _ ⟨i_lr, by dsimp [p]; rw [hilr_eq]⟩
    have hr_m : S r ∈ convexHull ℝ (Set.range p) := subset_convexHull ℝ _ ⟨i_lr + 1, by dsimp [p]; rw [hir_eq]⟩
    have hd_m : d₀ ∈ convexHull ℝ (Set.range p) := subset_convexHull ℝ _ ⟨i_lr + 2, rfl⟩
    have hcl_cr : 0 < c_l + c_r := add_pos hc_l hc_r
    have hlr_m : ((c_l / (c_l + c_r)) • S l + (c_r / (c_l + c_r)) • S r) ∈ convexHull ℝ (Set.range p) :=
      (convex_convexHull ℝ _) hl_m hr_m (div_nonneg (le_of_lt hc_l) (le_of_lt hcl_cr))
        (div_nonneg (le_of_lt hc_r) (le_of_lt hcl_cr)) (by field_simp [ne_of_gt hcl_cr])
    have hfull := (convex_convexHull ℝ _) hlr_m hd_m (le_of_lt hcl_cr) (le_of_lt hc_d) (by linarith)
    convert hfull using 1
    ext <;> simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] <;>
      field_simp [ne_of_gt hcl_cr]
  have hz''_pos : ∀ k : Fin (dc.m + 3), 0 < orient2D (p k) (p (k + 1)) z'' := by
    intro k
    have hl_nn := h_nonneg_edge k (S l) (subset_convexHull ℝ _ ⟨i_lr, by dsimp [p]; rw [hilr_eq]⟩)
    have hr_nn := h_nonneg_edge k (S r) (subset_convexHull ℝ _ ⟨i_lr + 1, by dsimp [p]; rw [hir_eq]⟩)
    have hd_nn := h_nonneg_edge k d₀ (subset_convexHull ℝ _ ⟨i_lr + 2, rfl⟩)
    have hid : orient2D (p k) (p (k + 1)) z'' =
        c_l * orient2D (p k) (p (k + 1)) (S l) +
        c_r * orient2D (p k) (p (k + 1)) (S r) +
        c_d * orient2D (p k) (p (k + 1)) d₀ := by
      have hcl_m : c_l = 1 - c_r - c_d := by linarith
      unfold orient2D
      rw [congrArg Prod.fst hz''_eq, congrArg Prod.snd hz''_eq]
      simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
      rw [hcl_m]; ring
    rw [hid]
    by_cases hk_lr : k = i_lr
    · rw [hk_lr]
      have hd_strict : 0 < orient2D (p i_lr) (p (i_lr + 1)) d₀ := dc.hstrict i_lr (i_lr + 2) hi2_ne0 hi2_ne1
      exact add_pos_of_nonneg_of_pos (add_nonneg (mul_nonneg (le_of_lt hc_l) (hk_lr ▸ hl_nn))
        (mul_nonneg (le_of_lt hc_r) (hk_lr ▸ hr_nn))) (mul_pos hc_d hd_strict)
    · by_cases hk_1 : k + 1 = i_lr
      · have hr_strict : 0 < orient2D (p k) (p (k + 1)) (S r) := by
          rw [← hir_eq]
          exact dc.hstrict k (i_lr + 1)
            (by intro heq; rw [← heq] at hk_1
                have : (i_lr + 1) + 1 = i_lr + 2 := by rw [add_assoc]; rfl
                rw [this] at hk_1; exact hi2_ne0 hk_1)
            (by intro heq; rw [hk_1] at heq
                have heq' : i_lr + 0 = i_lr + 1 := by rw [add_zero]; exact heq.symm
                have hv := congrArg Fin.val (add_left_cancel heq')
                have h1v : (1 : Fin (dc.m + 3)).val = 1 := by
                  change 1 % (dc.m + 3) = 1; exact Nat.mod_eq_of_lt (by omega)
                rw [Fin.val_zero, h1v] at hv; omega)
        exact add_pos_of_pos_of_nonneg (add_pos_of_nonneg_of_pos
          (mul_nonneg (le_of_lt hc_l) hl_nn) (mul_pos hc_r hr_strict)) (mul_nonneg (le_of_lt hc_d) hd_nn)
      · have hl_strict : 0 < orient2D (p k) (p (k + 1)) (S l) := by
          rw [← hilr_eq]
          exact dc.hstrict k i_lr (Ne.symm hk_lr) (fun h => hk_1 h.symm)
        exact add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg
          (mul_pos hc_l hl_strict) (mul_nonneg (le_of_lt hc_r) hr_nn)) (mul_nonneg (le_of_lt hc_d) hd_nn)
  let β' := β + (1 - β) * (eps / (1 + eps))
  have h1eps : 0 < 1 + eps := by linarith
  have hβ'0 : 0 < β' := add_pos hβ_pos (mul_pos (by linarith) (div_pos heps_pos h1eps))
  have hβ'1 : β' < 1 := by
    have hprod : (1 - β') * (1 + eps) = 1 - β := eps_blend_ar β eps (ne_of_gt h1eps)
    have hpos : 0 < (1 - β') * (1 + eps) := by rw [hprod]; exact sub_pos.mpr hβ_lt1
    have hpos2 : 0 < 1 - β' := pos_of_mul_pos_left hpos (le_of_lt h1eps)
    linarith
  have hy_eq'' : S y = β' • u + (1 - β') • z'' := by
    have h_al : β' - (1 - β') * eps = β := eps_blend_al β eps (ne_of_gt h1eps)
    have h_ar : (1 - β') * (1 + eps) = 1 - β := eps_blend_ar β eps (ne_of_gt h1eps)
    rw [hy_decomp]
    have hxz : z''.1 = (1 + eps) * z'.1 - eps * u.1 := rfl
    have hyz : z''.2 = (1 + eps) * z'.2 - eps * u.2 := rfl
    ext
    · change β * u.1 + (1 - β) * z'.1 = β' * u.1 + (1 - β') * z''.1
      rw [hxz]; linear_combination u.1 * h_al.symm + z'.1 * h_ar.symm
    · change β * u.2 + (1 - β) * z'.2 = β' * u.2 + (1 - β') * z''.2
      rw [hyz]; linear_combination u.2 * h_al.symm + z'.2 * h_ar.symm
  exact ⟨z'', β', hβ'0, hβ'1, hz''_mem, hz''_pos, hy_eq''⟩

private lemma exit_edge_exists {n : ℕ} {P : Set (ℝ × ℝ)} {S : Fin n → ℝ × ℝ}
    {w : Finset (Fin n) → ℝ × ℝ}
    (hP : ShatteredSimplePolygon P S w) (hn : 3 ≤ n)
    (hD3 : 3 ≤ (hullVertices S \ certifiedSet P S w).card)
    (dc : CyclicSubsetBoundary S (hullVertices S \ certifiedSet P S w))
    (y : Fin n) (hyM : y ∈ interiorPoints S ∪ certifiedSet P S w) :
    let D := hullVertices S \ certifiedSet P S w
    ∃ i : Fin (dc.m + 3),
      0 < orient2D (S (dc.p_idx i)) (S (dc.p_idx (i + 1))) (w D) ∧
      InOpenTri (w D) (S (dc.p_idx i)) (S (dc.p_idx (i + 1))) (S y) := by
  let B := hullVertices S
  let H := certifiedSet P S w
  let D := B \ H
  let u := w D
  let p := S ∘ dc.p_idx
  have hp_inj : Function.Injective p := hP.s_inj.comp dc.hp_idx_inj
  have himg_eq : Finset.univ.image p = D.image S := by
    calc Finset.univ.image (S ∘ dc.p_idx)
        = (Finset.univ.image dc.p_idx).image S := Finset.image_image.symm
      _ = D.image S := by rw [dc.hp_idx_img]
  have hrange_eq : Set.range p = (D.image S : Set (ℝ × ℝ)) := by
    rw [← himg_eq]; simp
  have hdc_mem : ∀ j : Fin (dc.m + 3), dc.p_idx j ∈ D := fun j => by
    have h : dc.p_idx j ∈ Finset.univ.image dc.p_idx := Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
    rwa [dc.hp_idx_img] at h
  have hy_notin_D : y ∉ D := by
    rcases Finset.mem_union.mp hyM with hyA | hyH
    · exact fun hyD => (Finset.mem_sdiff.mp hyA).2 (Finset.mem_sdiff.mp hyD).1
    · exact fun hyD => (Finset.mem_sdiff.mp hyD).2 hyH
  have h_edge_ne : ∀ i : Fin (dc.m + 3), dc.p_idx i ≠ dc.p_idx (i + 1) := by
    intro i heq
    have hinj := dc.hp_idx_inj heq
    nth_rw 1 [← add_zero i] at hinj
    have h01 : (0 : Fin (dc.m + 3)) = 1 := add_left_cancel hinj
    have hv := congrArg Fin.val h01
    simp [Nat.mod_eq_of_lt (by omega : 1 < dc.m + 3)] at hv
  have h_closed_to_open : ∀ i : Fin (dc.m + 3),
      InClosedTri (p i) (p (i + 1)) u (S y) → InOpenTri u (p i) (p (i + 1)) (S y) := by
    intro i hcl
    have hcl' : InClosedTri u (p i) (p (i + 1)) (S y) := by
      rcases hcl with ⟨μ₁, μ₂, μ₃, h1, h2, h3, hsum, hx, hy⟩
      exact ⟨μ₃, μ₁, μ₂, h3, h1, h2, by linarith, by linarith, by linarith⟩
    refine inOpenTri_of_noncollinear_inClosedTri hcl' ?_ ?_ ?_
    · exact hP.no_three_collinear (p i) (p (i + 1)) (S y)
        (Or.inl ⟨dc.p_idx i, rfl⟩) (Or.inl ⟨dc.p_idx (i + 1), rfl⟩) (Or.inl ⟨y, rfl⟩)
        (fun h => h_edge_ne i (hP.s_inj h))
        (fun h => hy_notin_D (hP.s_inj h ▸ hdc_mem (i + 1))) (fun h => hy_notin_D (hP.s_inj h ▸ hdc_mem i))
    · exact hP.no_three_collinear (p (i + 1)) u (S y)
        (Or.inl ⟨dc.p_idx (i + 1), rfl⟩) (Or.inr ⟨D, rfl⟩) (Or.inl ⟨y, rfl⟩)
        (hP.s_ne_w _ _) (hP.s_ne_w _ _).symm (fun h => hy_notin_D (hP.s_inj h ▸ hdc_mem (i + 1)))
    · exact hP.no_three_collinear u (p i) (S y)
        (Or.inr ⟨D, rfl⟩) (Or.inl ⟨dc.p_idx i, rfl⟩) (Or.inl ⟨y, rfl⟩)
        (hP.s_ne_w _ _).symm (fun h => hy_notin_D (hP.s_inj h ▸ hdc_mem i)) (hP.s_ne_w _ _).symm
  let _ := hD3
  let _ := hp_inj
  by_cases hy_in_convD : S y ∈ convexHull ℝ (Set.range p)
  · obtain ⟨i, hi⟩ := ray_exit_polygon_cover p dc.hstrict u (S y) hy_in_convD
    have hopen := h_closed_to_open i hi
    have h_pos_y : 0 < orient2D (p i) (p (i + 1)) (S y) := by
      have hnn : 0 ≤ orient2D (p i) (p (i + 1)) (S y) := by
        let Hs : Set (ℝ × ℝ) := {x | 0 ≤ orient2D (p i) (p (i + 1)) x}
        have hHs_conv : Convex ℝ Hs := by
          intro x hx z hz α β hα hβ hαβ
          dsimp [Hs] at hx hz ⊢
          unfold orient2D at hx hz ⊢
          change 0 ≤ ((p (i + 1)).1 - (p i).1) * ((α * x.2 + β * z.2) - (p i).2) -
            ((p (i + 1)).2 - (p i).2) * ((α * x.1 + β * z.1) - (p i).1)
          have hlin : ((p (i + 1)).1 - (p i).1) * ((α * x.2 + β * z.2) - (p i).2) -
              ((p (i + 1)).2 - (p i).2) * ((α * x.1 + β * z.1) - (p i).1) =
              α * (((p (i + 1)).1 - (p i).1) * (x.2 - (p i).2) -
                ((p (i + 1)).2 - (p i).2) * (x.1 - (p i).1)) +
              β * (((p (i + 1)).1 - (p i).1) * (z.2 - (p i).2) -
                ((p (i + 1)).2 - (p i).2) * (z.1 - (p i).1)) +
              (1 - (α + β)) * (((p (i + 1)).1 - (p i).1) * (-(p i).2) -
                ((p (i + 1)).2 - (p i).2) * (-(p i).1)) := by ring
          rw [hlin, hαβ, sub_self, zero_mul, add_zero]
          exact add_nonneg (mul_nonneg hα hx) (mul_nonneg hβ hz)
        have hsub : Set.range p ⊆ Hs := by
          rintro _ ⟨j, rfl⟩
          dsimp [Hs]
          by_cases hji : j = i
          · subst hji; rw [orient2D_self_outer]
          · by_cases hj1 : j = i + 1
            · subst hj1; rw [orient2D_self_right]
            · exact le_of_lt (dc.hstrict i j hji hj1)
        exact convexHull_min hsub hHs_conv hy_in_convD
      have hne0 : orient2D (p i) (p (i + 1)) (S y) ≠ 0 :=
        hP.no_three_collinear (p i) (p (i + 1)) (S y)
          (Or.inl ⟨dc.p_idx i, rfl⟩) (Or.inl ⟨dc.p_idx (i + 1), rfl⟩) (Or.inl ⟨y, rfl⟩)
          (fun h => h_edge_ne i (hP.s_inj h))
          (fun h => hy_notin_D (hP.s_inj h ▸ hdc_mem (i + 1))) (fun h => hy_notin_D (hP.s_inj h ▸ hdc_mem i))
      exact lt_of_le_of_ne hnn hne0.symm
    rcases hopen with ⟨μ₁, μ₂, μ₃, h1, h2, h3, hsum, hx1, hx2⟩
    have hor_y : orient2D (p i) (p (i + 1)) (S y) = μ₁ * orient2D (p i) (p (i + 1)) u := by
      have h1m : μ₁ = 1 - μ₂ - μ₃ := by linarith
      unfold orient2D; rw [hx1, hx2, h1m]; ring
    have hpos_u : 0 < orient2D (p i) (p (i + 1)) u := by nlinarith
    exact ⟨i, hpos_u, ⟨μ₁, μ₂, μ₃, h1, h2, h3, hsum, hx1, hx2⟩⟩
  · have hH_ne : H.Nonempty := by
      by_contra hHe
      rw [Finset.not_nonempty_iff_eq_empty] at hHe
      have hDB : D = B := by dsimp [D]; rw [hHe, Finset.sdiff_empty]
      apply hy_in_convD
      rw [hrange_eq, hDB, hullVertices_convexHull_eq S hP.s_inj]
      exact subset_convexHull ℝ _ ⟨y, rfl⟩
    have hcb_ne : Nonempty (CyclicSubsetBoundary S B) :=
      exists_cyclicSubsetBoundary hP (Finset.Subset.refl B) (hullVertices_card_ge_three hn hP)
    rcases hcb_ne with ⟨cb⟩
    obtain ⟨h₀, hh₀⟩ := hH_ne
    have hvc_ne := exists_q_visibleContour hP hn cb (Finset.mem_filter.mp hh₀).2
    rcases hvc_ne with ⟨vc⟩
    obtain ⟨k_f, k_g, l, r, hkf0, hkfg, hkg_lt, hl_eq, hr_eq, hlD, hrD, hl_ne_r, hblock, hpart_ii, _⟩ :=
      certified_structure hP hn cb vc ⟨h₀, hh₀⟩
    have hB_in_Du : convexHull ℝ (B.image S : Set (ℝ × ℝ)) ⊆
        convexHull ℝ (insert u (D.image S : Set (ℝ × ℝ))) := by
      apply convexHull_min _ (convex_convexHull ℝ _)
      intro z hz
      rcases Finset.mem_image.mp hz with ⟨b, hbB, rfl⟩
      by_cases hbH : b ∈ H
      · have hlD' : l ∈ D := hlD
        have hrD' : r ∈ D := hrD
        have htri_b := hpart_ii b hbH D ((hP.shatters D l).mpr hlD') ((hP.shatters D r).mpr hrD')
        refine convexHull_mono ?_ (inOpenTri_mem_convexHull htri_b)
        intro q hq
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
        rcases hq with rfl | rfl | rfl
        · exact Set.mem_insert _ _
        · exact Set.mem_insert_of_mem _ (Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨l, hlD', rfl⟩))
        · exact Set.mem_insert_of_mem _ (Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨r, hrD', rfl⟩))
      · have hbD : b ∈ D := Finset.mem_sdiff.mpr ⟨hbB, hbH⟩
        exact subset_convexHull ℝ _ (Set.mem_insert_of_mem _
          (Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨b, hbD, rfl⟩)))
    have hy_in_Du : S y ∈ convexHull ℝ (insert u (D.image S : Set (ℝ × ℝ))) := by
      apply hB_in_Du
      rw [hullVertices_convexHull_eq S hP.s_inj]
      exact subset_convexHull ℝ _ ⟨y, rfl⟩
    have hy_ne_u : S y ≠ u := hP.s_ne_w y D
    rw [← Finset.coe_insert] at hy_in_Du
    obtain ⟨β, hβ_nn, hβ_lt1, z', hz'_mem, hy_decomp⟩ :=
      convexHull_insert_decomp hy_ne_u hy_in_Du
    have hz'_range : z' ∈ convexHull ℝ (Set.range p) := by rwa [hrange_eq]
    have h_nonneg_edge : ∀ j : Fin (dc.m + 3), ∀ q ∈ convexHull ℝ (Set.range p),
        0 ≤ orient2D (p j) (p (j + 1)) q := by
      intro j q hq
      let Hs : Set (ℝ × ℝ) := {x | 0 ≤ orient2D (p j) (p (j + 1)) x}
      have hHs_conv : Convex ℝ Hs := by
        intro x hx z hz α γ hα hγ hαγ
        dsimp [Hs] at hx hz ⊢
        unfold orient2D at hx hz ⊢
        change 0 ≤ ((p (j + 1)).1 - (p j).1) * ((α * x.2 + γ * z.2) - (p j).2) -
          ((p (j + 1)).2 - (p j).2) * ((α * x.1 + γ * z.1) - (p j).1)
        have hlin : ((p (j + 1)).1 - (p j).1) * ((α * x.2 + γ * z.2) - (p j).2) -
            ((p (j + 1)).2 - (p j).2) * ((α * x.1 + γ * z.1) - (p j).1) =
            α * (((p (j + 1)).1 - (p j).1) * (x.2 - (p j).2) -
              ((p (j + 1)).2 - (p j).2) * (x.1 - (p j).1)) +
            γ * (((p (j + 1)).1 - (p j).1) * (z.2 - (p j).2) -
              ((p (j + 1)).2 - (p j).2) * (z.1 - (p j).1)) +
            (1 - (α + γ)) * (((p (j + 1)).1 - (p j).1) * (-(p j).2) -
              ((p (j + 1)).2 - (p j).2) * (-(p j).1)) := by ring
        rw [hlin, hαγ, sub_self, zero_mul, add_zero]
        exact add_nonneg (mul_nonneg hα hx) (mul_nonneg hγ hz)
      have hsub : Set.range p ⊆ Hs := by
        rintro _ ⟨k, rfl⟩
        dsimp [Hs]
        by_cases hkj : k = j
        · subst hkj; rw [orient2D_self_outer]
        · by_cases hk1 : k = j + 1
          · subst hk1; rw [orient2D_self_right]
          · exact le_of_lt (dc.hstrict j k hkj hk1)
      exact convexHull_min hsub hHs_conv hq
    have h_lr_edge_D : IsCCWHullEdge (D.image S) (S l) (S r) := by
      refine ⟨Finset.mem_image.mpr ⟨l, hlD, rfl⟩, Finset.mem_image.mpr ⟨r, hrD, rfl⟩,
        fun h => hl_ne_r (hP.s_inj h), fun c hc hcl hcr => ?_⟩
      rcases Finset.mem_image.mp hc with ⟨d, hdD, rfl⟩
      have hdB : d ∈ B := (Finset.mem_sdiff.mp hdD).1
      have hd_img : d ∈ Finset.univ.image cb.p_idx := by rw [cb.hp_idx_img]; exact hdB
      rcases Finset.mem_image.mp hd_img with ⟨jd, _, rfl⟩
      let kd := (jd - vc.i_max).val
      have hkd_lt : kd < cb.m + 3 := (jd - vc.i_max).isLt
      have hjd_eq : jd = finShift vc.i_max kd := (finShift_sub vc.i_max jd).symm
      have hd_notH : cb.p_idx jd ∉ H := (Finset.mem_sdiff.mp hdD).2
      have hd_vc := vc.hd_lt
      have hkd_out : kd < k_f - 1 ∨ k_g + 1 < kd := by
        by_contra hle
        have h1 : k_f - 1 ≤ kd ∧ kd ≤ k_g + 1 := by omega
        by_cases heq1 : kd = k_f - 1
        · apply hcl; rw [hl_eq, hjd_eq, heq1]
        · by_cases heq2 : kd = k_g + 1
          · apply hcr; rw [hr_eq, hjd_eq, heq2]
          · apply hd_notH
            rw [hjd_eq]
            exact (hblock kd hkd_lt).mp ⟨by omega, by omega⟩
      rw [hl_eq, hr_eq, hjd_eq]
      rcases hkd_out with hlt | hgt
      · exact cb.hcyc (finShift vc.i_max (k_f - 1)) (finShift vc.i_max (k_g + 1)) (finShift vc.i_max kd)
          (cyclicOrder_cycle (cyclicOrder_finShift vc.i_max hlt (by omega) (by omega)))
      · exact cb.hcyc (finShift vc.i_max (k_f - 1)) (finShift vc.i_max (k_g + 1)) (finShift vc.i_max kd)
          (cyclicOrder_finShift vc.i_max (by omega) hgt hkd_lt)
    obtain ⟨i_lr, hilr_eq, hir_eq⟩ : ∃ i_lr : Fin (dc.m + 3), dc.p_idx i_lr = l ∧ dc.p_idx (i_lr + 1) = r := by
      rw [← himg_eq] at h_lr_edge_D
      obtain ⟨i_lr, hi1, hi2⟩ := (isCCWHullEdge_iff_succ dc.hstrict hp_inj).mp h_lr_edge_D
      exact ⟨i_lr, hP.s_inj hi1, hP.s_inj hi2⟩
    have h_lr_u_neg : orient2D (S l) (S r) u < 0 := by
      have htri_h := hpart_ii h₀ hh₀ D ((hP.shatters D l).mpr hlD) ((hP.shatters D r).mpr hrD)
      have hlrh : orient2D (S l) (S r) (S h₀) < 0 := by
        have hh₀B : h₀ ∈ B := (Finset.mem_filter.mp hh₀).1
        have hh₀_img : h₀ ∈ Finset.univ.image cb.p_idx := by rw [cb.hp_idx_img]; exact hh₀B
        rcases Finset.mem_image.mp hh₀_img with ⟨jh, _, rfl⟩
        obtain ⟨kh, hkh0, hkh_lt, hkh_eq, _⟩ := separation hP hn cb vc (Finset.mem_filter.mp hh₀).2
        have hkh_range := (hblock kh (by have := vc.hd_lt; omega)).mpr (hkh_eq ▸ hh₀)
        have hkh_eq_jh : finShift vc.i_max kh = jh := cb.hp_idx_inj hkh_eq
        have hd_vc := vc.hd_lt
        have hpos := cb.hcyc (finShift vc.i_max (k_f - 1)) (finShift vc.i_max kh) (finShift vc.i_max (k_g + 1))
          (cyclicOrder_finShift vc.i_max (by omega) (by omega) (by omega))
        rw [← hl_eq, hkh_eq_jh, ← hr_eq] at hpos
        rw [orient2D_swap23]; linarith
      rcases htri_h with ⟨μ₁, μ₂, μ₃, h1, h2, h3, hsum, hx1, hx2⟩
      have hor : orient2D (S l) (S r) (S h₀) = μ₁ * orient2D (S l) (S r) u := by
        have h1m : μ₁ = 1 - μ₂ - μ₃ := by linarith
        unfold orient2D; rw [hx1, hx2, h1m]; ring
      nlinarith
    have hβ_pos : 0 < β := by
      by_contra h0
      have hβ0 : β = 0 := le_antisymm (not_lt.mp h0) hβ_nn
      rw [hβ0, zero_smul, zero_add, sub_zero, one_smul] at hy_decomp
      apply hy_in_convD
      rwa [hy_decomp]
    have h_cover_interior_z : ∀ z'' : ℝ × ℝ, ∀ β' : ℝ, 0 < β' → β' < 1 →
        z'' ∈ convexHull ℝ (Set.range p) →
        (∀ j : Fin (dc.m + 3), 0 < orient2D (p j) (p (j + 1)) z'') →
        S y = β' • u + (1 - β') • z'' →
        ∃ i : Fin (dc.m + 3), 0 < orient2D (p i) (p (i + 1)) u ∧ InOpenTri u (p i) (p (i + 1)) (S y) := by
      intro z'' β' hβ'0 hβ'1 hz''_mem hz''_pos hy_eq''
      obtain ⟨i, hi_cl⟩ := ray_exit_polygon_cover p dc.hstrict u z'' hz''_mem
      have hpos_u : 0 < orient2D (p i) (p (i + 1)) u := by
        rcases hi_cl with ⟨ν₁, ν₂, ν₃, h1, h2, h3, hsum, hx1, hx2⟩
        have hor : orient2D (p i) (p (i + 1)) z'' = ν₃ * orient2D (p i) (p (i + 1)) u := by
          have h3m : ν₃ = 1 - ν₁ - ν₂ := by linarith
          unfold orient2D; rw [hx1, hx2, h3m]; ring
        have hpos_z := hz''_pos i
        have hν3_pos : 0 < ν₃ := by
          by_contra h0
          have hν0 : ν₃ = 0 := le_antisymm (not_lt.mp h0) h3
          rw [hν0, zero_mul] at hor; linarith
        nlinarith
      have hcl_y : InClosedTri (p i) (p (i + 1)) u (S y) := by
        rcases hi_cl with ⟨ν₁, ν₂, ν₃, h1, h2, h3, hsum, hx1, hx2⟩
        refine ⟨(1 - β') * ν₁, (1 - β') * ν₂, β' + (1 - β') * ν₃,
          mul_nonneg (by linarith) h1, mul_nonneg (by linarith) h2,
          add_nonneg (le_of_lt hβ'0) (mul_nonneg (by linarith) h3), by linear_combination (1 - β') * hsum, ?_, ?_⟩
        · have hy1 := congrArg Prod.fst hy_eq''
          simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul] at hy1
          rw [hy1, hx1]; ring
        · have hy2 := congrArg Prod.snd hy_eq''
          simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul] at hy2
          rw [hy2, hx2]; ring
      exact ⟨i, hpos_u, h_closed_to_open i hcl_y⟩
    by_cases hz'_strict : ∀ j : Fin (dc.m + 3), 0 < orient2D (p j) (p (j + 1)) z'
    · exact h_cover_interior_z z' β hβ_pos hβ_lt1 hz'_range hz'_strict hy_decomp
    · push Not at hz'_strict
      rcases hz'_strict with ⟨j, hj_le⟩
      have hj0 : orient2D (p j) (p (j + 1)) z' = 0 :=
        le_antisymm hj_le (h_nonneg_edge j z' hz'_range)
      by_cases hj_lr : j = i_lr
      · obtain ⟨z'', β', hβ'0, hβ'1, hz''_mem, hz''_pos, hy_eq''⟩ :=
          exit_edge_lr_perturb hP dc y hy_notin_D β hβ_pos hβ_lt1 z' hz'_range h_nonneg_edge
            hlD hrD hl_ne_r i_lr hilr_eq hir_eq h_lr_u_neg (hj_lr ▸ hj0) hy_decomp
        exact h_cover_interior_z z'' β' hβ'0 hβ'1 hz''_mem hz''_pos hy_eq''
      · have hedge_B : IsCCWHullEdge (B.image S) (p j) (p (j + 1)) :=
          exit_edge_non_lr_isCCW hP hn cb vc dc hkf0 hkfg hkg_lt hl_eq hr_eq hlD hrD hblock hpart_ii i_lr hilr_eq j hj_lr
        have hy_pos_j : 0 < orient2D (p j) (p (j + 1)) (S y) := by
          have hnn_y : 0 ≤ orient2D (p j) (p (j + 1)) (S y) := by
            let Hs : Set (ℝ × ℝ) := {x | 0 ≤ orient2D (p j) (p (j + 1)) x}
            have hHs_conv : Convex ℝ Hs := by
              intro x hx z hz α γ hα hγ hαγ
              dsimp [Hs] at hx hz ⊢; unfold orient2D at hx hz ⊢
              change 0 ≤ ((p (j + 1)).1 - (p j).1) * ((α * x.2 + γ * z.2) - (p j).2) -
                ((p (j + 1)).2 - (p j).2) * ((α * x.1 + γ * z.1) - (p j).1)
              have hlin : ((p (j + 1)).1 - (p j).1) * ((α * x.2 + γ * z.2) - (p j).2) -
                  ((p (j + 1)).2 - (p j).2) * ((α * x.1 + γ * z.1) - (p j).1) =
                  α * (((p (j + 1)).1 - (p j).1) * (x.2 - (p j).2) -
                    ((p (j + 1)).2 - (p j).2) * (x.1 - (p j).1)) +
                  γ * (((p (j + 1)).1 - (p j).1) * (z.2 - (p j).2) -
                    ((p (j + 1)).2 - (p j).2) * (z.1 - (p j).1)) +
                  (1 - (α + γ)) * (((p (j + 1)).1 - (p j).1) * (-(p j).2) -
                    ((p (j + 1)).2 - (p j).2) * (-(p j).1)) := by ring
              rw [hlin, hαγ, sub_self, zero_mul, add_zero]
              exact add_nonneg (mul_nonneg hα hx) (mul_nonneg hγ hz)
            have hsub : (B.image S : Set (ℝ × ℝ)) ⊆ Hs := by
              intro x hx
              dsimp [Hs]
              by_cases hxa : x = p j
              · rw [hxa, orient2D_self_outer]
              · by_cases hxb : x = p (j + 1)
                · rw [hxb, orient2D_self_right]
                · exact le_of_lt (hedge_B.2.2.2 x hx hxa hxb)
            have hy_in_B : S y ∈ convexHull ℝ (B.image S : Set (ℝ × ℝ)) := by
              rw [hullVertices_convexHull_eq S hP.s_inj]
              exact subset_convexHull ℝ _ ⟨y, rfl⟩
            exact convexHull_min hsub hHs_conv hy_in_B
          have hne0 := hP.no_three_collinear (p j) (p (j + 1)) (S y)
            (Or.inl ⟨dc.p_idx j, rfl⟩) (Or.inl ⟨dc.p_idx (j + 1), rfl⟩) (Or.inl ⟨y, rfl⟩)
            (fun h => h_edge_ne j (hP.s_inj h))
            (fun h => hy_notin_D (hP.s_inj h ▸ hdc_mem (j + 1))) (fun h => hy_notin_D (hP.s_inj h ▸ hdc_mem j))
          exact lt_of_le_of_ne hnn_y hne0.symm
        have hpos_u : 0 < orient2D (p j) (p (j + 1)) u := by
          have hid : orient2D (p j) (p (j + 1)) (S y) =
              β * orient2D (p j) (p (j + 1)) u + (1 - β) * orient2D (p j) (p (j + 1)) z' := by
            unfold orient2D
            rw [congrArg Prod.fst hy_decomp, congrArg Prod.snd hy_decomp]
            simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
            ring
          rw [hj0, mul_zero, add_zero] at hid
          exact pos_of_mul_pos_right (by linarith [hid, hy_pos_j] : 0 < β * orient2D (p j) (p (j + 1)) u) (le_of_lt hβ_pos)
        have hz'_seg : ∃ s : ℝ, 0 < s ∧ s < 1 ∧ z' = (1 - s) • p j + s • p (j + 1) := by
          have hcoord : (p (j + 1)).1 - (p j).1 ≠ 0 ∨ (p (j + 1)).2 - (p j).2 ≠ 0 := by
            by_contra hc; push Not at hc
            exact h_edge_ne j (hP.s_inj (show p j = p (j + 1) by ext <;> linarith))
          obtain ⟨s, hs1, hs2⟩ : ∃ s : ℝ,
              z'.1 = (1 - s) * (p j).1 + s * (p (j + 1)).1 ∧
              z'.2 = (1 - s) * (p j).2 + s * (p (j + 1)).2 := by
            unfold orient2D at hj0
            rcases hcoord with hx | hyc
            · refine ⟨(z'.1 - (p j).1) / ((p (j + 1)).1 - (p j).1), by field_simp [hx]; ring,
                by field_simp [hx]; linear_combination hj0⟩
            · refine ⟨(z'.2 - (p j).2) / ((p (j + 1)).2 - (p j).2),
                by field_simp [hyc]; linear_combination -hj0, by field_simp [hyc]; ring⟩
          have h1v : (1 : Fin (dc.m + 3)).val = 1 := by
            change 1 % (dc.m + 3) = 1; exact Nat.mod_eq_of_lt (by omega)
          have h11v : ((1 + 1 : Fin (dc.m + 3)) : ℕ) = 2 := by
            rw [Fin.val_add, h1v]; exact Nat.mod_eq_of_lt (by omega)
          have hs_ge0 : 0 ≤ s := by
            have hnn := h_nonneg_edge (j - 1) z' hz'_range
            rw [sub_add_cancel] at hnn
            have h_pre : 0 < orient2D (p (j - 1)) (p j) (p (j + 1)) := by
              have h1 := dc.hstrict (j - 1) (j + 1)
                (by intro heq; have h' := congrArg (· + (1 : Fin (dc.m + 3))) heq
                    rw [sub_add_cancel, add_assoc] at h'
                    have heq' : j + 0 = j + (1 + 1) := by rw [add_zero]; exact h'.symm
                    have hv := congrArg Fin.val (add_left_cancel heq')
                    rw [Fin.val_zero, h11v] at hv; omega)
                (by intro heq; rw [sub_add_cancel] at heq
                    have heq' : j + 0 = j + 1 := by rw [add_zero]; exact heq.symm
                    have hv := congrArg Fin.val (add_left_cancel heq')
                    rw [Fin.val_zero, h1v] at hv; omega)
              rw [sub_add_cancel] at h1; exact h1
            have hid := orient2D_affine_comb (p (j - 1)) (p j) (p j) (p (j + 1)) z' s hs1 hs2
            rw [orient2D_self_right, mul_zero, zero_add] at hid
            rw [hid] at hnn; exact nonneg_of_mul_nonneg_left hnn h_pre
          have hs_le1 : s ≤ 1 := by
            have hnn := h_nonneg_edge (j + 1) z' hz'_range
            have h_suc : 0 < orient2D (p (j + 1)) (p (j + 1 + 1)) (p j) := by
              exact dc.hstrict (j + 1) j
                (by intro heq
                    have heq' : j + 0 = j + 1 := by rw [add_zero]; exact heq
                    have hv := congrArg Fin.val (add_left_cancel heq')
                    rw [Fin.val_zero, h1v] at hv; omega)
                (by intro heq; rw [add_assoc] at heq
                    have heq' : j + 0 = j + (1 + 1) := by rw [add_zero]; exact heq
                    have hv := congrArg Fin.val (add_left_cancel heq')
                    rw [Fin.val_zero, h11v] at hv; omega)
            have hid := orient2D_affine_comb (p (j + 1)) (p (j + 1 + 1)) (p j) (p (j + 1)) z' s hs1 hs2
            rw [orient2D_self_outer, mul_zero, add_zero] at hid
            rw [hid] at hnn
            have h1s := nonneg_of_mul_nonneg_left hnn h_suc; linarith
          have hs_gt0 : 0 < s := by
            refine lt_of_le_of_ne hs_ge0 (fun hs0 => ?_)
            have hzj : z' = p j := by ext <;> [rw [hs1, ← hs0]; rw [hs2, ← hs0]] <;> ring
            rw [hzj] at hy_decomp
            have hcol : orient2D u (p j) (S y) = 0 := by
              have hx1 := congrArg Prod.fst hy_decomp; have hx2 := congrArg Prod.snd hy_decomp
              simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at hx1 hx2
              unfold orient2D; rw [hx1, hx2]; ring
            exact hP.no_three_collinear u (p j) (S y)
              (Or.inr ⟨D, rfl⟩) (Or.inl ⟨dc.p_idx j, rfl⟩) (Or.inl ⟨y, rfl⟩)
              (hP.s_ne_w _ _).symm (fun h => hy_notin_D (hP.s_inj h ▸ hdc_mem j)) (hP.s_ne_w _ _).symm hcol
          have hs_lt1 : s < 1 := by
            refine lt_of_le_of_ne hs_le1 (fun hs1' => ?_)
            have hzj1 : z' = p (j + 1) := by ext <;> [rw [hs1, hs1']; rw [hs2, hs1']] <;> ring
            rw [hzj1] at hy_decomp
            have hcol : orient2D u (p (j + 1)) (S y) = 0 := by
              have hx1 := congrArg Prod.fst hy_decomp; have hx2 := congrArg Prod.snd hy_decomp
              simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at hx1 hx2
              unfold orient2D; rw [hx1, hx2]; ring
            exact hP.no_three_collinear u (p (j + 1)) (S y)
              (Or.inr ⟨D, rfl⟩) (Or.inl ⟨dc.p_idx (j + 1), rfl⟩) (Or.inl ⟨y, rfl⟩)
              (hP.s_ne_w _ _).symm (fun h => hy_notin_D (hP.s_inj h ▸ hdc_mem (j + 1))) (hP.s_ne_w _ _).symm hcol
          exact ⟨s, hs_gt0, hs_lt1, by ext <;> [exact hs1; exact hs2]⟩
        rcases hz'_seg with ⟨s, hs0, hs1, hz'_eq⟩
        refine ⟨j, hpos_u, β, (1 - β) * (1 - s), (1 - β) * s, hβ_pos, mul_pos (by linarith) (by linarith),
          mul_pos (by linarith) hs0, by ring, ?_, ?_⟩
        · rw [congrArg Prod.fst hy_decomp]
          simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]
          rw [congrArg Prod.fst hz'_eq]
          simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]; dsimp [u, p, D]; ring
        · rw [congrArg Prod.snd hy_decomp]
          simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
          rw [congrArg Prod.snd hz'_eq]
          simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]; dsimp [u, p, D]; ring

/-- Lemma 4.5 (`Exit edges for A ∪ H`, `upper_9.tex` lines 418–424). -/
theorem exit_edge {n : ℕ} {P : Set (ℝ × ℝ)} {S : Fin n → ℝ × ℝ}
    {w : Finset (Fin n) → ℝ × ℝ}
    (hP : ShatteredSimplePolygon P S w) (hn : 3 ≤ n)
    (hD3 : 3 ≤ (hullVertices S \ certifiedSet P S w).card)
    (dc : CyclicSubsetBoundary S (hullVertices S \ certifiedSet P S w))
    (y : Fin n) (hyM : y ∈ interiorPoints S ∪ certifiedSet P S w) :
    let B := hullVertices S
    let H := certifiedSet P S w
    let D := B \ H
    let u := w D
    (∃! i : Fin (dc.m + 3),
      0 < orient2D (S (dc.p_idx i)) (S (dc.p_idx (i + 1))) u ∧
      InOpenTri u (S (dc.p_idx i)) (S (dc.p_idx (i + 1))) (S y)) ∧
    (∀ i : Fin (dc.m + 3),
      0 < orient2D (S (dc.p_idx i)) (S (dc.p_idx (i + 1))) u →
      InOpenTri u (S (dc.p_idx i)) (S (dc.p_idx (i + 1))) (S y) →
      (∀ x_idx : Finset (Fin n),
        Sees P (w x_idx) (S (dc.p_idx i)) → Sees P (w x_idx) (S (dc.p_idx (i + 1))) →
        InOpenTri (w x_idx) (S (dc.p_idx i)) (S (dc.p_idx (i + 1))) (S y)) ∧
      (H.Nonempty → IsCCWHullEdge (B.image S) (S (dc.p_idx i)) (S (dc.p_idx (i + 1))))) := by
  let B := hullVertices S
  let H := certifiedSet P S w
  let D := B \ H
  let u := w D
  let p := S ∘ dc.p_idx
  have hp_inj : Function.Injective p := hP.s_inj.comp dc.hp_idx_inj
  have himg_eq : Finset.univ.image p = D.image S := by
    calc Finset.univ.image (S ∘ dc.p_idx)
        = (Finset.univ.image dc.p_idx).image S := Finset.image_image.symm
      _ = D.image S := by rw [dc.hp_idx_img]
  have hrange_eq : Set.range p = (D.image S : Set (ℝ × ℝ)) := by
    rw [← himg_eq]; simp
  have hdc_mem : ∀ j : Fin (dc.m + 3), dc.p_idx j ∈ D := fun j => by
    have h : dc.p_idx j ∈ Finset.univ.image dc.p_idx := Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
    rwa [dc.hp_idx_img] at h
  have hy_notin_D : y ∉ D := by
    rcases Finset.mem_union.mp hyM with hyA | hyH
    · exact fun hyD => (Finset.mem_sdiff.mp hyA).2 (Finset.mem_sdiff.mp hyD).1
    · exact fun hyD => (Finset.mem_sdiff.mp hyD).2 hyH
  have h_edge_ne : ∀ i : Fin (dc.m + 3), dc.p_idx i ≠ dc.p_idx (i + 1) := by
    intro i heq
    have hinj := dc.hp_idx_inj heq
    nth_rw 1 [← add_zero i] at hinj
    have h01 : (0 : Fin (dc.m + 3)) = 1 := add_left_cancel hinj
    have hv := congrArg Fin.val h01
    simp [Nat.mod_eq_of_lt (by omega : 1 < dc.m + 3)] at hv
  have h_closed_to_open : ∀ i : Fin (dc.m + 3),
      InClosedTri (p i) (p (i + 1)) u (S y) → InOpenTri u (p i) (p (i + 1)) (S y) := by
    intro i hcl
    have hcl' : InClosedTri u (p i) (p (i + 1)) (S y) := by
      rcases hcl with ⟨μ₁, μ₂, μ₃, h1, h2, h3, hsum, hx, hy⟩
      exact ⟨μ₃, μ₁, μ₂, h3, h1, h2, by linarith, by linarith, by linarith⟩
    refine inOpenTri_of_noncollinear_inClosedTri hcl' ?_ ?_ ?_
    · exact hP.no_three_collinear (p i) (p (i + 1)) (S y)
        (Or.inl ⟨dc.p_idx i, rfl⟩) (Or.inl ⟨dc.p_idx (i + 1), rfl⟩) (Or.inl ⟨y, rfl⟩)
        (fun h => h_edge_ne i (hP.s_inj h))
        (fun h => hy_notin_D (hP.s_inj h ▸ hdc_mem (i + 1))) (fun h => hy_notin_D (hP.s_inj h ▸ hdc_mem i))
    · exact hP.no_three_collinear (p (i + 1)) u (S y)
        (Or.inl ⟨dc.p_idx (i + 1), rfl⟩) (Or.inr ⟨D, rfl⟩) (Or.inl ⟨y, rfl⟩)
        (hP.s_ne_w _ _) (hP.s_ne_w _ _).symm (fun h => hy_notin_D (hP.s_inj h ▸ hdc_mem (i + 1)))
    · exact hP.no_three_collinear u (p i) (S y)
        (Or.inr ⟨D, rfl⟩) (Or.inl ⟨dc.p_idx i, rfl⟩) (Or.inl ⟨y, rfl⟩)
        (hP.s_ne_w _ _).symm (fun h => hy_notin_D (hP.s_inj h ▸ hdc_mem i)) (hP.s_ne_w _ _).symm
  have h_exists := exit_edge_exists hP hn hD3 dc y hyM
  have h_unique : ∀ i j : Fin (dc.m + 3),
      0 < orient2D (p i) (p (i + 1)) u → InOpenTri u (p i) (p (i + 1)) (S y) →
      0 < orient2D (p j) (p (j + 1)) u → InOpenTri u (p j) (p (j + 1)) (S y) → i = j := by
    intro i j hui hti huj htj
    by_contra hij
    rcases hti with ⟨μ₁, μ₂, μ₃, hμ1, hμ2, hμ3, hμsum, hxi1, hxi2⟩
    rcases htj with ⟨ν₁, ν₂, ν₃, hν1, hν2, hν3, hνsum, hxj1, hxj2⟩
    have h1μ : 0 < 1 - μ₁ := by linarith
    have h1ν : 0 < 1 - ν₁ := by linarith
    let wi : ℝ × ℝ := ((μ₂ / (1 - μ₁)) * (p i).1 + (μ₃ / (1 - μ₁)) * (p (i + 1)).1,
                        (μ₂ / (1 - μ₁)) * (p i).2 + (μ₃ / (1 - μ₁)) * (p (i + 1)).2)
    let wj : ℝ × ℝ := ((ν₂ / (1 - ν₁)) * (p j).1 + (ν₃ / (1 - ν₁)) * (p (j + 1)).1,
                        (ν₂ / (1 - ν₁)) * (p j).2 + (ν₃ / (1 - ν₁)) * (p (j + 1)).2)
    have hwi_seg : wi ∈ convexHull ℝ (Set.range p) := by
      have h1 : (p i) ∈ convexHull ℝ (Set.range p) := subset_convexHull ℝ _ ⟨i, rfl⟩
      have h2 : (p (i + 1)) ∈ convexHull ℝ (Set.range p) := subset_convexHull ℝ _ ⟨i + 1, rfl⟩
      have hs : μ₂ / (1 - μ₁) + μ₃ / (1 - μ₁) = 1 := by field_simp [ne_of_gt h1μ]; linarith
      exact (convex_convexHull ℝ _) h1 h2 (div_nonneg (le_of_lt hμ2) (le_of_lt h1μ))
        (div_nonneg (le_of_lt hμ3) (le_of_lt h1μ)) hs
    have hwj_seg : wj ∈ convexHull ℝ (Set.range p) := by
      have h1 : (p j) ∈ convexHull ℝ (Set.range p) := subset_convexHull ℝ _ ⟨j, rfl⟩
      have h2 : (p (j + 1)) ∈ convexHull ℝ (Set.range p) := subset_convexHull ℝ _ ⟨j + 1, rfl⟩
      have hs : ν₂ / (1 - ν₁) + ν₃ / (1 - ν₁) = 1 := by field_simp [ne_of_gt h1ν]; linarith
      exact (convex_convexHull ℝ _) h1 h2 (div_nonneg (le_of_lt hν2) (le_of_lt h1ν))
        (div_nonneg (le_of_lt hν3) (le_of_lt h1ν)) hs
    have h_edge_nn : ∀ k : Fin (dc.m + 3), ∀ q ∈ convexHull ℝ (Set.range p),
        0 ≤ orient2D (p k) (p (k + 1)) q := by
      intro k q hq
      let Hs : Set (ℝ × ℝ) := {x | 0 ≤ orient2D (p k) (p (k + 1)) x}
      have hHs_conv : Convex ℝ Hs := by
        intro x hx z hz α γ hα hγ hαγ
        dsimp [Hs] at hx hz ⊢; unfold orient2D at hx hz ⊢
        change 0 ≤ ((p (k + 1)).1 - (p k).1) * ((α * x.2 + γ * z.2) - (p k).2) -
          ((p (k + 1)).2 - (p k).2) * ((α * x.1 + γ * z.1) - (p k).1)
        have hlin : ((p (k + 1)).1 - (p k).1) * ((α * x.2 + γ * z.2) - (p k).2) -
            ((p (k + 1)).2 - (p k).2) * ((α * x.1 + γ * z.1) - (p k).1) =
            α * (((p (k + 1)).1 - (p k).1) * (x.2 - (p k).2) -
              ((p (k + 1)).2 - (p k).2) * (x.1 - (p k).1)) +
            γ * (((p (k + 1)).1 - (p k).1) * (z.2 - (p k).2) -
              ((p (k + 1)).2 - (p k).2) * (z.1 - (p k).1)) +
            (1 - (α + γ)) * (((p (k + 1)).1 - (p k).1) * (-(p k).2) -
              ((p (k + 1)).2 - (p k).2) * (-(p k).1)) := by ring
        rw [hlin, hαγ, sub_self, zero_mul, add_zero]
        exact add_nonneg (mul_nonneg hα hx) (mul_nonneg hγ hz)
      have hsub : Set.range p ⊆ Hs := by
        rintro _ ⟨m, rfl⟩; dsimp [Hs]
        by_cases hmk : m = k
        · subst hmk; rw [orient2D_self_outer]
        · by_cases hm1 : m = k + 1
          · subst hm1; rw [orient2D_self_right]
          · exact le_of_lt (dc.hstrict k m hmk hm1)
      exact convexHull_min hsub hHs_conv hq
    have hwi_eq : (1 - μ₁) * wi.1 + μ₁ * u.1 = (S y).1 ∧ (1 - μ₁) * wi.2 + μ₁ * u.2 = (S y).2 := by
      dsimp [wi]; constructor <;> field_simp [ne_of_gt h1μ] <;> linarith
    have hwj_eq : (1 - ν₁) * wj.1 + ν₁ * u.1 = (S y).1 ∧ (1 - ν₁) * wj.2 + ν₁ * u.2 = (S y).2 := by
      dsimp [wj]; constructor <;> field_simp [ne_of_gt h1ν] <;> linarith
    rcases lt_trichotomy μ₁ ν₁ with hlt | heq | hgt
    · have hwj_or : (1 - ν₁) * orient2D (p i) (p (i + 1)) wj =
          -(ν₁ - μ₁) * orient2D (p i) (p (i + 1)) u := by
        have hwi0 : orient2D (p i) (p (i + 1)) wi = 0 := by
          have h1mu : 1 - μ₁ = μ₂ + μ₃ := by linarith
          dsimp [wi, orient2D]; rw [h1mu]; field_simp [ne_of_gt (add_pos hμ2 hμ3)]; ring
        unfold orient2D at hwi0 ⊢
        have hdx : (1 - ν₁) * wj.1 = (1 - μ₁) * wi.1 - (ν₁ - μ₁) * u.1 := by linarith [hwi_eq.1, hwj_eq.1]
        have hdy : (1 - ν₁) * wj.2 = (1 - μ₁) * wi.2 - (ν₁ - μ₁) * u.2 := by linarith [hwi_eq.2, hwj_eq.2]
        linear_combination (1 - μ₁) * hwi0 + ((p (i + 1)).1 - (p i).1) * hdy - ((p (i + 1)).2 - (p i).2) * hdx
      have hnn := h_edge_nn i wj hwj_seg
      have hneg : -(ν₁ - μ₁) * orient2D (p i) (p (i + 1)) u < 0 :=
        mul_neg_of_neg_of_pos (neg_lt_zero.mpr (sub_pos.mpr hlt)) hui
      have hpos2 : 0 ≤ (1 - ν₁) * orient2D (p i) (p (i + 1)) wj := mul_nonneg (le_of_lt h1ν) hnn
      linarith [hwj_or]
    · subst heq
      have hwi_wj : wi = wj := by
        ext
        · exact mul_left_cancel₀ (ne_of_gt h1μ) (by linarith [hwi_eq.1, hwj_eq.1])
        · exact mul_left_cancel₀ (ne_of_gt h1μ) (by linarith [hwi_eq.2, hwj_eq.2])
      have hwi_pos : 0 < orient2D (p j) (p (j + 1)) wi := by
        have h1 : 0 ≤ orient2D (p j) (p (j + 1)) (p i) := by
          by_cases h1a : i = j
          · exact False.elim (hij h1a)
          · by_cases h1b : i = j + 1
            · rw [h1b, orient2D_self_right]
            · exact le_of_lt (dc.hstrict j i h1a h1b)
        have h2 : 0 ≤ orient2D (p j) (p (j + 1)) (p (i + 1)) := by
          by_cases h2a : i + 1 = j
          · rw [h2a, orient2D_self_outer]
          · by_cases h2b : i + 1 = j + 1
            · exact False.elim (hij (add_right_cancel h2b))
            · exact le_of_lt (dc.hstrict j (i + 1) h2a h2b)
        have h_one : 0 < orient2D (p j) (p (j + 1)) (p i) ∨ 0 < orient2D (p j) (p (j + 1)) (p (i + 1)) := by
          by_cases hij1 : i = j + 1
          · right
            have h2a : i + 1 ≠ j := by
              rw [hij1, add_assoc]; intro heq
              nth_rw 2 [← add_zero j] at heq
              have h20 := add_left_cancel heq
              have hv := congrArg Fin.val h20
              have h1v : (1 : Fin (dc.m + 3)).val = 1 := by
                change 1 % (dc.m + 3) = 1; exact Nat.mod_eq_of_lt (by omega)
              have h11v : ((1 + 1 : Fin (dc.m + 3)) : ℕ) = 2 := by
                rw [Fin.val_add, h1v]; exact Nat.mod_eq_of_lt (by omega)
              rw [h11v, Fin.val_zero] at hv; omega
            exact dc.hstrict j (i + 1) h2a (fun h => hij (add_right_cancel h))
          · left; exact dc.hstrict j i hij hij1
        have hid : orient2D (p j) (p (j + 1)) wi =
            (μ₂ / (1 - μ₁)) * orient2D (p j) (p (j + 1)) (p i) +
            (μ₃ / (1 - μ₁)) * orient2D (p j) (p (j + 1)) (p (i + 1)) := by
          have h1mu : 1 - μ₁ = μ₂ + μ₃ := by linarith
          dsimp [wi, orient2D]; rw [h1mu]; field_simp [ne_of_gt (add_pos hμ2 hμ3)]; ring
        rw [hid]
        have hc2 := div_pos hμ2 h1μ
        have hc3 := div_pos hμ3 h1μ
        rcases h_one with hp1 | hp2
        · exact add_pos_of_pos_of_nonneg (mul_pos hc2 hp1) (mul_nonneg (le_of_lt hc3) h2)
        · exact add_pos_of_nonneg_of_pos (mul_nonneg (le_of_lt hc2) h1) (mul_pos hc3 hp2)
      have hwj0 : orient2D (p j) (p (j + 1)) wj = 0 := by
        have h1nu : 1 - μ₁ = ν₂ + ν₃ := by linarith
        dsimp [wj, orient2D]; rw [h1nu]; field_simp [ne_of_gt (add_pos hν2 hν3)]; ring
      rw [hwi_wj] at hwi_pos; linarith
    · have hwi_or : (1 - μ₁) * orient2D (p j) (p (j + 1)) wi =
          -(μ₁ - ν₁) * orient2D (p j) (p (j + 1)) u := by
        have hwj0 : orient2D (p j) (p (j + 1)) wj = 0 := by
          have h1nu : 1 - ν₁ = ν₂ + ν₃ := by linarith
          dsimp [wj, orient2D]; rw [h1nu]; field_simp [ne_of_gt (add_pos hν2 hν3)]; ring
        unfold orient2D at hwj0 ⊢
        have hdx : (1 - μ₁) * wi.1 = (1 - ν₁) * wj.1 - (μ₁ - ν₁) * u.1 := by linarith [hwi_eq.1, hwj_eq.1]
        have hdy : (1 - μ₁) * wi.2 = (1 - ν₁) * wj.2 - (μ₁ - ν₁) * u.2 := by linarith [hwi_eq.2, hwj_eq.2]
        linear_combination (1 - ν₁) * hwj0 + ((p (j + 1)).1 - (p j).1) * hdy - ((p (j + 1)).2 - (p j).2) * hdx
      have hnn := h_edge_nn j wi hwi_seg
      have hneg : -(μ₁ - ν₁) * orient2D (p j) (p (j + 1)) u < 0 :=
        mul_neg_of_neg_of_pos (neg_lt_zero.mpr (sub_pos.mpr hgt)) huj
      have hpos2 : 0 ≤ (1 - μ₁) * orient2D (p j) (p (j + 1)) wi := mul_nonneg (le_of_lt h1μ) hnn
      linarith [hwi_or]
  rcases h_exists with ⟨i₀, hui0, hti0⟩
  refine ⟨⟨i₀, ⟨hui0, hti0⟩, fun j ⟨huj, htj⟩ => (h_unique i₀ j hui0 hti0 huj htj).symm⟩, ?_⟩
  intro i hui htri
  refine ⟨?_, ?_⟩
  · intro x_idx hx1 hx2
    by_cases hxeq : x_idx = D
    · subst hxeq; exact htri
    · have hu_miss_y : ¬ Sees P u (S y) := fun hs => hy_notin_D ((hP.shatters D y).mp hs)
      have hxU : w x_idx ∈ UCone (S y) (p i) (p (i + 1)) := by
        apply cone hP.toEnclosureDomain ((hP.shatters D _).mpr (hdc_mem i))
          ((hP.shatters D _).mpr (hdc_mem (i + 1))) hu_miss_y htri hx1 hx2
        · exact hP.no_three_collinear (S y) (p i) (w x_idx) (Or.inl ⟨y, rfl⟩)
            (Or.inl ⟨dc.p_idx i, rfl⟩) (Or.inr ⟨x_idx, rfl⟩)
            (fun h => hy_notin_D (hP.s_inj h ▸ hdc_mem i)) (hP.s_ne_w _ _) (hP.s_ne_w _ _)
        · exact hP.no_three_collinear (S y) (p (i + 1)) (w x_idx) (Or.inl ⟨y, rfl⟩)
            (Or.inl ⟨dc.p_idx (i + 1), rfl⟩) (Or.inr ⟨x_idx, rfl⟩)
            (fun h => hy_notin_D (hP.s_inj h ▸ hdc_mem (i + 1))) (hP.s_ne_w _ _) (hP.s_ne_w _ _)
        · exact hP.no_three_collinear u (S y) (w x_idx) (Or.inr ⟨D, rfl⟩)
            (Or.inl ⟨y, rfl⟩) (Or.inr ⟨x_idx, rfl⟩)
            (hP.s_ne_w y D).symm (hP.s_ne_w y x_idx) (fun h => hxeq (hP.w_inj h).symm)
      exact (mem_uCone_iff_inOpenTri (S y) (p i) (p (i + 1)) (w x_idx)).mp hxU
  · intro hH_ne
    have hcb_ne : Nonempty (CyclicSubsetBoundary S B) :=
      exists_cyclicSubsetBoundary hP (Finset.Subset.refl B) (hullVertices_card_ge_three hn hP)
    rcases hcb_ne with ⟨cb⟩
    obtain ⟨h₀, hh₀⟩ := hH_ne
    have hvc_ne := exists_q_visibleContour hP hn cb (Finset.mem_filter.mp hh₀).2
    rcases hvc_ne with ⟨vc⟩
    obtain ⟨_, _, l, r, _, _, _, _, _, hlD, hrD, _, _, hpart_ii, _⟩ :=
      certified_structure hP hn cb vc ⟨h₀, hh₀⟩
    refine ⟨Finset.mem_image.mpr ⟨dc.p_idx i, (Finset.mem_sdiff.mp (hdc_mem i)).1, rfl⟩,
      Finset.mem_image.mpr ⟨dc.p_idx (i + 1), (Finset.mem_sdiff.mp (hdc_mem (i + 1))).1, rfl⟩,
      fun h => h_edge_ne i (hP.s_inj h), fun c hc hca hcb => ?_⟩
    rcases Finset.mem_image.mp hc with ⟨b, hbB, rfl⟩
    by_cases hbD : b ∈ D
    · have hbi : b ∈ Finset.univ.image dc.p_idx := by rw [dc.hp_idx_img]; exact hbD
      rcases Finset.mem_image.mp hbi with ⟨jb, _, rfl⟩
      exact dc.hstrict i jb (fun h => hca (congrArg p h)) (fun h => hcb (congrArg p h))
    · have hbH : b ∈ H := by by_contra hnot; exact hbD (Finset.mem_sdiff.mpr ⟨hbB, hnot⟩)
      have htri_b := hpart_ii b hbH D ((hP.shatters D l).mpr hlD) ((hP.shatters D r).mpr hrD)
      rcases htri_b with ⟨μ₁, μ₂, μ₃, h1, h2, h3, hsum, hx1, hx2⟩
      have hl_nn : 0 ≤ orient2D (p i) (p (i + 1)) (S l) := by
        have hli : l ∈ Finset.univ.image dc.p_idx := by rw [dc.hp_idx_img]; exact hlD
        rcases Finset.mem_image.mp hli with ⟨jl, _, hjl⟩
        rw [← hjl]
        change 0 ≤ orient2D (p i) (p (i + 1)) (p jl)
        by_cases h1a : jl = i
        · rw [h1a, orient2D_self_outer]
        · by_cases h1b : jl = i + 1
          · rw [h1b, orient2D_self_right]
          · exact le_of_lt (dc.hstrict i jl h1a h1b)
      have hr_nn : 0 ≤ orient2D (p i) (p (i + 1)) (S r) := by
        have hri : r ∈ Finset.univ.image dc.p_idx := by rw [dc.hp_idx_img]; exact hrD
        rcases Finset.mem_image.mp hri with ⟨jr, _, hjr⟩
        rw [← hjr]
        change 0 ≤ orient2D (p i) (p (i + 1)) (p jr)
        by_cases h1a : jr = i
        · rw [h1a, orient2D_self_outer]
        · by_cases h1b : jr = i + 1
          · rw [h1b, orient2D_self_right]
          · exact le_of_lt (dc.hstrict i jr h1a h1b)
      have hid : orient2D (p i) (p (i + 1)) (S b) =
          μ₁ * orient2D (p i) (p (i + 1)) u +
          μ₂ * orient2D (p i) (p (i + 1)) (S l) +
          μ₃ * orient2D (p i) (p (i + 1)) (S r) := by
        have h1m : μ₁ = 1 - μ₂ - μ₃ := by linarith
        unfold orient2D; rw [hx1, hx2, h1m]; ring
      change 0 < orient2D (p i) (p (i + 1)) (S b)
      rw [hid]
      exact add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg (mul_pos h1 hui) (mul_nonneg (le_of_lt h2) hl_nn))
        (mul_nonneg (le_of_lt h3) hr_nn)

private lemma two_corners_isFrontVertex {n : ℕ} {P : Set (ℝ × ℝ)} {S : Fin n → ℝ × ℝ}
    {w : Finset (Fin n) → ℝ × ℝ}
    (hP : ShatteredSimplePolygon P S w)
    (cb : CyclicSubsetBoundary S (hullVertices S))
    {f a b : Fin n} (hf : f ∈ hullVertices S) (ha : a ∈ hullVertices S) (hb : b ∈ hullVertices S)
    (haf : a ≠ f) (hbf : b ≠ f) (hab : a ≠ b)
    (hccw : 0 < orient2D (S a) (S f) (S b))
    {v : ℝ × ℝ} (htri : InOpenTri v (S a) (S b) (S f)) :
    IsFrontVertex ((hullVertices S).image S) v (S f) := by
  let B := hullVertices S
  have hp_inj : Function.Injective (S ∘ cb.p_idx) := hP.s_inj.comp cb.hp_idx_inj
  have himg_eq : Finset.univ.image (S ∘ cb.p_idx) = B.image S := by
    calc Finset.univ.image (S ∘ cb.p_idx)
        = (Finset.univ.image cb.p_idx).image S := Finset.image_image.symm
      _ = B.image S := by rw [cb.hp_idx_img]
  have haf_s : S a ≠ S f := fun h => haf (hP.s_inj h)
  have hfb_s : S f ≠ S b := fun h => hbf (hP.s_inj h).symm
  have hab_s : S a ≠ S b := fun h => hab (hP.s_inj h)
  have h1 : IsCCWHullEdge {S a, S f, S b} (S a) (S f) := by
    refine ⟨by simp, by simp, haf_s, fun z hz hza hzf => ?_⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl
    · exact False.elim (hza rfl)
    · exact False.elim (hzf rfl)
    · exact hccw
  have h2 : IsCCWHullEdge {S a, S f, S b} (S f) (S b) := by
    refine ⟨by simp, by simp, hfb_s, fun z hz hzf hzb => ?_⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl
    · have : orient2D (S f) (S b) (S a) = orient2D (S a) (S f) (S b) := by unfold orient2D; ring
      linarith
    · exact False.elim (hzf rfl)
    · exact False.elim (hzb rfl)
  have hfront_tri := (isFrontVertex_iff_inOpenTri' h1 h2 hab_s).mpr htri
  have hf_img : f ∈ Finset.univ.image cb.p_idx := by rw [cb.hp_idx_img]; exact hf
  rcases Finset.mem_image.mp hf_img with ⟨i_f, _, rfl⟩
  have hb' : IsCCWHullEdge (B.image S) ((S ∘ cb.p_idx) (i_f - 1)) (S (cb.p_idx i_f)) := by
    rw [← himg_eq]
    exact (isCCWHullEdge_iff_succ cb.hstrict hp_inj).mpr
      ⟨i_f - 1, rfl, congrArg (S ∘ cb.p_idx) (sub_add_cancel i_f 1)⟩
  have hc' : IsCCWHullEdge (B.image S) (S (cb.p_idx i_f)) ((S ∘ cb.p_idx) (i_f + 1)) := by
    rw [← himg_eq]
    exact (isCCWHullEdge_iff_succ cb.hstrict hp_inj).mpr ⟨i_f, rfl, rfl⟩
  have hsub : ({S a, S (cb.p_idx i_f), S b} : Finset (ℝ × ℝ)) ⊆ B.image S := by
    intro z hz; simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl
    · exact Finset.mem_image.mpr ⟨a, ha, rfl⟩
    · exact Finset.mem_image.mpr ⟨cb.p_idx i_f, hf, rfl⟩
    · exact Finset.mem_image.mpr ⟨b, hb, rfl⟩
  exact front_restoration hsub (hullVertices_isConvexPos hP) (by simp) hfront_tri hb' hc'

/-- Corollary 4.4 (`Side preservation`, `upper_9.tex` lines 407–416). -/
theorem side_preservation {n : ℕ} {P : Set (ℝ × ℝ)} {S : Fin n → ℝ × ℝ}
    {w : Finset (Fin n) → ℝ × ℝ}
    (hP : ShatteredSimplePolygon P S w) (hn : 3 ≤ n)
    (cb : CyclicSubsetBoundary S (hullVertices S))
    (vc : VisibleContour (S ∘ cb.p_idx) (w Finset.univ))
    (hH : (certifiedSet P S w).Nonempty)
    (hD5 : 5 ≤ (hullVertices S \ certifiedSet P S w).card)
    {k_f k_g : ℕ} {l r : Fin n}
    (hkf0 : 0 < k_f) (hkfg : k_f ≤ k_g) (hkg_lt : k_g < vc.d_near)
    (hl_eq : l = cb.p_idx (finShift vc.i_max (k_f - 1)))
    (hr_eq : r = cb.p_idx (finShift vc.i_max (k_g + 1)))
    (hblock : ∀ k : ℕ, k < cb.m + 3 →
      (k_f ≤ k ∧ k ≤ k_g ↔ cb.p_idx (finShift vc.i_max k) ∈ certifiedSet P S w)) :
    let B := hullVertices S
    let H := certifiedSet P S w
    let D := B \ H
    (∀ (p : Fin n) (O : Finset (Fin n)),
      p ∈ D → p ∉ O →
      (∀ a ∈ O ∩ D, ∀ b ∈ O ∩ D, ¬ IsCCWHullEdge (B.image S) (S a) (S b)) →
      IsBackVertex (B.image S) (w (Finset.univ \ O)) (S p) →
      ∀ h ∈ H,
        (2 ≤ (D.filter (fun u => orient2D (zWitness w h) (S h) (S u) < 0)).card → p ≠ l) ∧
        (2 ≤ (D.filter (fun u => 0 < orient2D (zWitness w h) (S h) (S u))).card → p ≠ r)) ∧
    (∀ (Q : Finset (Fin n)), Q ⊆ D → Q.card ≤ 2 →
      (∀ p ∈ Q, ∃ O : Finset (Fin n), p ∉ O ∧
        (∀ a ∈ O ∩ D, ∀ b ∈ O ∩ D, ¬ IsCCWHullEdge (B.image S) (S a) (S b)) ∧
        IsBackVertex (B.image S) (w (Finset.univ \ O)) (S p)) →
      ∀ M₀ : Finset (Fin n), M₀ ⊆ interiorPoints S ∪ H →
        let F := (D \ Q) ∪ M₀
        ∀ h ∈ H \ M₀, ∃ a ∈ F, ∃ b ∈ F,
          ∀ x_idx : Finset (Fin n), Sees P (w x_idx) (S a) → Sees P (w x_idx) (S b) →
            InOpenTri (w x_idx) (S a) (S b) (S h)) := by
  let _ := hH
  let B := hullVertices S
  let H := certifiedSet P S w
  let D := B \ H
  have hp_inj : Function.Injective (S ∘ cb.p_idx) := hP.s_inj.comp cb.hp_idx_inj
  have himg_eq : Finset.univ.image (S ∘ cb.p_idx) = B.image S := by
    calc Finset.univ.image (S ∘ cb.p_idx)
        = (Finset.univ.image cb.p_idx).image S := Finset.image_image.symm
      _ = B.image S := by rw [cb.hp_idx_img]
  have hcb_mem : ∀ j : Fin (cb.m + 3), cb.p_idx j ∈ B := fun j => by
    have h : cb.p_idx j ∈ Finset.univ.image cb.p_idx := Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
    rwa [cb.hp_idx_img] at h
  have hidx_inj : ∀ a b : ℕ, a < cb.m + 3 → b < cb.m + 3 → a ≠ b →
      cb.p_idx (finShift vc.i_max a) ≠ cb.p_idx (finShift vc.i_max b) := by
    intro a b ha hb hab heq
    have hsub := congrArg (· - vc.i_max) (cb.hp_idx_inj heq)
    rw [finShift_eq_add vc.i_max ha, finShift_eq_add vc.i_max hb,
      add_sub_cancel_left, add_sub_cancel_left] at hsub
    exact hab (congrArg Fin.val hsub)
  have hd_vc := vc.hd_lt
  have hl_memB : l ∈ B := hl_eq ▸ hcb_mem _
  have hr_memB : r ∈ B := hr_eq ▸ hcb_mem _
  have hl_notH : l ∉ H := fun hlH => by
    rw [hl_eq, ← hblock (k_f - 1) (by omega)] at hlH; omega
  have hr_notH : r ∉ H := fun hrH => by
    rw [hr_eq, ← hblock (k_g + 1) (by omega)] at hrH; omega
  have hl_memD : l ∈ D := Finset.mem_sdiff.mpr ⟨hl_memB, hl_notH⟩
  have hr_memD : r ∈ D := Finset.mem_sdiff.mpr ⟨hr_memB, hr_notH⟩
  have h_part1 : ∀ (p : Fin n) (O : Finset (Fin n)),
      p ∈ D → p ∉ O →
      (∀ a ∈ O ∩ D, ∀ b ∈ O ∩ D, ¬ IsCCWHullEdge (B.image S) (S a) (S b)) →
      IsBackVertex (B.image S) (w (Finset.univ \ O)) (S p) →
      ∀ h ∈ H,
        (2 ≤ (D.filter (fun u => orient2D (zWitness w h) (S h) (S u) < 0)).card → p ≠ l) ∧
        (2 ≤ (D.filter (fun u => 0 < orient2D (zWitness w h) (S h) (S u))).card → p ≠ r) := by
    intro p O hpD hpO hO_noadj hp_back h hh
    have hcert := (Finset.mem_filter.mp hh).2
    obtain ⟨kh, hkh0, hkh_lt, hkh_eq, hleft_h, hright_h, k_split, hs1, hs2, hneg_arc, hpos_arc⟩ :=
      separation hP hn cb vc hcert
    have hkh_range : k_f ≤ kh ∧ kh ≤ k_g := (hblock kh (by omega)).mpr (hkh_eq ▸ hh)
    let i_h := finShift vc.i_max kh
    have hih_eq : cb.p_idx i_h = h := hkh_eq
    have h_u_of_k : ∀ u ∈ D, ∃ s : ℕ, 1 ≤ s ∧ s < cb.m + 3 ∧ cb.p_idx (finShift i_h s) = u := by
      intro u huD
      have huB : u ∈ B := (Finset.mem_sdiff.mp huD).1
      have hu_img : u ∈ Finset.univ.image cb.p_idx := by rw [cb.hp_idx_img]; exact huB
      rcases Finset.mem_image.mp hu_img with ⟨i_u, _, hiu_eq⟩
      let s := (i_u - i_h).val
      have hs_lt : s < cb.m + 3 := (i_u - i_h).isLt
      have hs_pos : 1 ≤ s := by
        by_contra h0
        have hs0 : s = 0 := by omega
        have heq : i_u = i_h := sub_eq_zero.mp (Fin.ext hs0)
        have huh : u = h := by rw [← hiu_eq, heq, hih_eq]
        exact (Finset.mem_sdiff.mp huD).2 (huh ▸ hh)
      exact ⟨s, hs_pos, hs_lt, by rw [finShift_sub, hiu_eq]⟩
    constructor
    · intro hcard2 hpl
      have hlO : l ∉ O := hpl ▸ hpO
      have hl_back : IsBackVertex (B.image S) (w (Finset.univ \ O)) (S l) := hpl ▸ hp_back
      let Dr := D.filter (fun u => orient2D (zWitness w h) (S h) (S u) < 0)
      have hcard2' : 2 ≤ Dr.card := hcard2
      have hr_shift : r = cb.p_idx (finShift i_h (k_g + 1 - kh)) := by
        rw [hr_eq]
        dsimp [i_h]
        rw [finShift_add]
        congr 2; omega
      have hr_in_Dr : r ∈ Dr := by
        refine Finset.mem_filter.mpr ⟨hr_memD, ?_⟩
        rw [hr_eq]
        exact hright_h (k_g + 1) (by omega) (by omega)
      have hk_r_le_split : k_g + 1 - kh ≤ k_split := by
        by_contra hgt
        have h1 := hpos_arc (k_g + 1 - kh) (by omega) (by omega)
        have h2 : orient2D (zWitness w h) (S h) (S r) < 0 := (Finset.mem_filter.mp hr_in_Dr).2
        rw [hr_shift] at h2
        linarith
      have hDr_sub : ∀ u ∈ Dr, ∃ s : ℕ, k_g + 1 - kh ≤ s ∧ s ≤ k_split ∧
          cb.p_idx (finShift i_h s) = u := by
        intro u huDr
        obtain ⟨s, hs_pos, hs_lt, hsu⟩ := h_u_of_k u (Finset.mem_filter.mp huDr).1
        have hs_le : s ≤ k_split := by
          by_contra hgt
          have hpos := hpos_arc s (by omega) hs_lt
          have hneg := (Finset.mem_filter.mp huDr).2
          rw [← hsu] at hneg
          linarith
        have hs_ge : k_g + 1 - kh ≤ s := by
          by_contra hlt
          have hmem_H : cb.p_idx (finShift i_h s) ∈ H := by
            dsimp [i_h]; rw [finShift_add]
            exact (hblock (kh + s) (by omega)).mp ⟨by omega, by omega⟩
          rw [hsu] at hmem_H
          exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp huDr).1).2 hmem_H
        exact ⟨s, hs_ge, hs_le, hsu⟩
      have h_split_gt : k_g + 1 - kh < k_split := by
        by_contra hle
        have heq_s : k_g + 1 - kh = k_split := le_antisymm hk_r_le_split (not_lt.mp hle)
        have hDr_le1 : Dr.card ≤ 1 := Finset.card_le_one.mpr (fun a ha b hb => by
          obtain ⟨sa, ha1, ha2, rfl⟩ := hDr_sub a ha
          obtain ⟨sb, hb1, hb2, rfl⟩ := hDr_sub b hb
          have hsa : sa = k_split := by omega
          have hsb : sb = k_split := by omega
          rw [hsa, hsb])
        omega
      let s_rp := k_g + 2 - kh
      let i_r := finShift vc.i_max (k_g + 1)
      let r_plus := cb.p_idx (i_r + 1)
      have hrp_shift : r_plus = cb.p_idx (finShift i_h s_rp) := by
        dsimp [r_plus, i_r, i_h, s_rp]
        rw [finShift_succ (by omega : 2 ≤ cb.m + 3), finShift_add]
        congr 2; omega
      have hrp_neg_h : orient2D (zWitness w h) (S h) (S r_plus) < 0 := by
        rw [hrp_shift]; exact hneg_arc s_rp (by omega) (by omega)
      have hrp_memB : r_plus ∈ B := hcb_mem _
      have hrp_notH : r_plus ∉ H := by
        intro hrpH
        obtain ⟨krp, hkrp0, hkrp_lt, hkrp_eq, _⟩ := separation hP hn cb vc (Finset.mem_filter.mp hrpH).2
        have hkrp_range := (hblock krp (by omega)).mpr (hkrp_eq ▸ hrpH)
        rcases lt_trichotomy krp kh with hlt | rfl | hgt
        · have := hleft_h krp hlt; rw [hkrp_eq] at this; linarith
        · have heq : i_h = finShift i_h s_rp := cb.hp_idx_inj (by rw [hih_eq, ← hrp_shift, ← hkrp_eq]; exact hkh_eq.symm)
          have hsub := congrArg (· - i_h) heq
          rw [sub_self, finShift_eq_add i_h (by omega : s_rp < cb.m + 3), add_sub_cancel_left] at hsub
          have hv := congrArg Fin.val hsub
          simp only [Fin.val_zero] at hv; omega
        · have heq : finShift i_h (krp - kh) = finShift i_h s_rp := by
            apply cb.hp_idx_inj
            rw [← hrp_shift, ← hkrp_eq]
            dsimp [i_h]; rw [finShift_add]; congr 2; omega
          have hsub := congrArg (· - i_h) heq
          rw [finShift_eq_add i_h (by omega : krp - kh < cb.m + 3),
            finShift_eq_add i_h (by omega : s_rp < cb.m + 3),
            add_sub_cancel_left, add_sub_cancel_left] at hsub
          have hv := congrArg Fin.val hsub
          simp only at hv; omega
      have hrp_memD : r_plus ∈ D := Finset.mem_sdiff.mpr ⟨hrp_memB, hrp_notH⟩
      let f := cb.p_idx (finShift vc.i_max k_f)
      have hfH : f ∈ H := (hblock k_f (by omega)).mp ⟨le_rfl, hkfg⟩
      have hf_cert := (Finset.mem_filter.mp hfH).2
      obtain ⟨kf', hkf'0, hkf'_lt, hkf'_eq, hleft_f, hright_f, _⟩ := separation hP hn cb vc hf_cert
      have hkf'_eq_kf : kf' = k_f := by
        by_contra hne
        exact hidx_inj kf' k_f (by omega) (by omega) hne hkf'_eq
      rw [hkf'_eq_kf] at hkf'_eq hleft_f hright_f
      have hf_r : orient2D (zWitness w f) (S f) (S r) < 0 := by
        rw [hr_eq]; exact hright_f (k_g + 1) (by omega) (by omega)
      have hf_rp : orient2D (zWitness w f) (S f) (S r_plus) < 0 := by
        by_cases hfh : f = h
        · rwa [hfh]
        · have hkf_lt_kh : k_f < kh := by
            refine lt_of_le_of_ne hkh_range.1 (fun heq => hfh ?_)
            dsimp [f]; rw [← hkh_eq, heq]
          by_contra hge
          have hne0 : orient2D (zWitness w f) (S f) (S r_plus) ≠ 0 := by
            have hrp_ne_f : r_plus ≠ f := fun heq => hrp_notH (heq ▸ hfH)
            exact hP.no_three_collinear (zWitness w f) (S f) (S r_plus)
              (Or.inr ⟨Finset.univ.erase f, rfl⟩) (Or.inl ⟨f, rfl⟩) (Or.inl ⟨r_plus, rfl⟩)
              (hP.s_ne_w f _).symm (fun h' => hrp_ne_f (hP.s_inj h').symm)
              (hP.s_ne_w r_plus (Finset.univ.erase f)).symm
          have hpos_f : 0 < orient2D (zWitness w f) (S f) (S r_plus) :=
            lt_of_le_of_ne (not_lt.mp hge) hne0.symm
          have hrp_ne_f : r_plus ≠ f := fun heq => hrp_notH (heq ▸ hfH)
          have hr_ne_f : r ≠ f := fun heq => hr_notH (heq ▸ hfH)
          have htri_f := side_corners hP hn hf_cert hrp_memB hr_memB hrp_ne_f hr_ne_f
            (mul_neg_of_pos_of_neg hpos_f hf_r) Finset.univ
            ((hP.shatters Finset.univ _).mpr (Finset.mem_univ _))
            ((hP.shatters Finset.univ _).mpr (Finset.mem_univ _))
          have hl_pos_h : 0 < orient2D (zWitness w h) (S h) (S l) := by
            rw [hl_eq]; exact hleft_h (k_f - 1) (by omega)
          have hl_ne_h : l ≠ h := fun heq => hl_notH (heq ▸ hh)
          have hrp_ne_h : r_plus ≠ h := fun heq => hrp_notH (heq ▸ hh)
          have htri_h := side_corners hP hn hcert hl_memB hrp_memB hl_ne_h hrp_ne_h
            (mul_neg_of_pos_of_neg hl_pos_h hrp_neg_h) Finset.univ
            ((hP.shatters Finset.univ _).mpr (Finset.mem_univ _))
            ((hP.shatters Finset.univ _).mpr (Finset.mem_univ _))
          have hirp_ne_r : (i_r + 1) ≠ finShift vc.i_max (k_g + 1) := by
            intro heq
            have : i_r + 1 = i_r := heq
            nth_rw 2 [← add_zero i_r] at this
            have h10 : (1 : Fin (cb.m + 3)) = 0 := add_left_cancel this
            have hv := congrArg Fin.val h10
            simp [Nat.mod_eq_of_lt (by omega : 1 < cb.m + 3)] at hv
          have htri_f' : InOpenTri (w Finset.univ) ((S ∘ cb.p_idx) (i_r + 1))
              ((S ∘ cb.p_idx) (finShift vc.i_max (k_g + 1))) ((S ∘ cb.p_idx) (finShift vc.i_max k_f)) := by
            dsimp only [Function.comp_apply]; dsimp [f, r_plus] at htri_f ⊢; rw [← hr_eq]; exact htri_f
          have hbtw_f := inOpenTri_slope_between vc hirp_ne_r htri_f'
          have hil_ne_rp : finShift vc.i_max (k_f - 1) ≠ (i_r + 1) := by
            intro heq
            have heq' : l = r_plus := by rw [hl_eq]; exact congrArg cb.p_idx heq
            rw [← heq'] at hrp_neg_h
            linarith
          have htri_h' : InOpenTri (w Finset.univ) ((S ∘ cb.p_idx) (finShift vc.i_max (k_f - 1)))
              ((S ∘ cb.p_idx) (i_r + 1)) ((S ∘ cb.p_idx) (finShift vc.i_max kh)) := by
            dsimp only [Function.comp_apply]; rw [← hl_eq, hkh_eq]; exact htri_h
          have hbtw_h := inOpenTri_slope_between vc hil_ne_rp htri_h'
          have hs_rf : vc.slope (finShift vc.i_max (k_g + 1)) < vc.slope (finShift vc.i_max k_f) :=
            near_slope_strictAnti vc (by omega) (by omega)
          have hs_hl : vc.slope (finShift vc.i_max kh) < vc.slope (finShift vc.i_max (k_f - 1)) :=
            near_slope_strictAnti vc (by omega) (by omega)
          have hs_hf : vc.slope (finShift vc.i_max kh) < vc.slope (finShift vc.i_max k_f) :=
            near_slope_strictAnti vc hkf_lt_kh (by omega)
          rcases hbtw_f with ⟨hf1, hf2⟩ | ⟨hf1, hf2⟩ <;>
            rcases hbtw_h with ⟨hh1, hh2⟩ | ⟨hh1, hh2⟩ <;> linarith
      have hr_rp_edge : IsCCWHullEdge (B.image S) (S r) (S r_plus) := by
        rw [← himg_eq, hr_eq]
        exact (isCCWHullEdge_iff_succ cb.hstrict hp_inj).mpr ⟨i_r, rfl, rfl⟩
      obtain ⟨b', hb'_mem, hb'_notO⟩ : ∃ b' ∈ ({r, r_plus} : Finset (Fin n)), b' ∉ O := by
        by_contra hnone
        push Not at hnone
        have hrO : r ∈ O ∩ D := Finset.mem_inter.mpr ⟨hnone r (by simp), hr_memD⟩
        have hrpO : r_plus ∈ O ∩ D := Finset.mem_inter.mpr ⟨hnone r_plus (by simp), hrp_memD⟩
        exact hO_noadj r hrO r_plus hrpO hr_rp_edge
      have hb'_memD : b' ∈ D := by
        rcases Finset.mem_insert.mp hb'_mem with rfl | hb'_mem2
        · exact hr_memD
        · rw [Finset.mem_singleton.mp hb'_mem2]; exact hrp_memD
      have hb'_memB : b' ∈ B := (Finset.mem_sdiff.mp hb'_memD).1
      have hb'_neg_f : orient2D (zWitness w f) (S f) (S b') < 0 := by
        rcases Finset.mem_insert.mp hb'_mem with rfl | hb'_mem2
        · exact hf_r
        · rw [Finset.mem_singleton.mp hb'_mem2]; exact hf_rp
      have hl_pos_f : 0 < orient2D (zWitness w f) (S f) (S l) := by
        rw [hl_eq]; exact hleft_f (k_f - 1) (by omega)
      have hl_ne_f : l ≠ f := fun heq => hl_notH (heq ▸ hfH)
      have hb'_ne_f : b' ≠ f := fun heq => (Finset.mem_sdiff.mp hb'_memD).2 (heq ▸ hfH)
      have hl_ne_b' : l ≠ b' := by
        intro heq; rw [heq] at hl_pos_f; linarith
      have htri_v := side_corners hP hn hf_cert hl_memB hb'_memB hl_ne_f hb'_ne_f
        (mul_neg_of_pos_of_neg hl_pos_f hb'_neg_f) (Finset.univ \ O)
        ((hP.shatters _ l).mpr (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hlO⟩))
        ((hP.shatters _ b').mpr (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hb'_notO⟩))
      have hlf_edge : IsCCWHullEdge (B.image S) (S l) (S f) := by
        rw [← himg_eq, hl_eq]
        dsimp [f]
        have heq_f : finShift vc.i_max k_f = finShift vc.i_max (k_f - 1) + 1 := by
          rw [finShift_succ (by omega : 2 ≤ cb.m + 3)]; congr 1; omega
        rw [heq_f]
        exact (isCCWHullEdge_iff_succ cb.hstrict hp_inj).mpr ⟨finShift vc.i_max (k_f - 1), rfl, rfl⟩
      have hlfb' : 0 < orient2D (S l) (S f) (S b') :=
        hlf_edge.2.2.2 (S b') (Finset.mem_image.mpr ⟨b', hb'_memB, rfl⟩)
          (fun h' => hl_ne_b' (hP.s_inj h').symm) (fun h' => hb'_ne_f (hP.s_inj h'))
      have hv_front_f := two_corners_isFrontVertex hP cb (hfH |> fun hh' => (Finset.mem_filter.mp hh').1)
        hl_memB hb'_memB hl_ne_f hb'_ne_f hl_ne_b' hlfb' htri_v
      rcases hv_front_f with ⟨b1, _, hb1f, _, ho_v, _⟩
      have hb1_eq : b1 = S l := isCCWHullEdge_pred_unique hb1f hlf_edge
      rw [hb1_eq] at ho_v
      rcases hl_back with ⟨_, c1, _, hlc1, _, ho_back⟩
      have hc1_eq : c1 = S f := isCCWHullEdge_succ_unique hlc1 hlf_edge
      rw [hc1_eq] at ho_back
      linarith
    · intro hcard2 hpr
      have hrO : r ∉ O := hpr ▸ hpO
      have hr_back : IsBackVertex (B.image S) (w (Finset.univ \ O)) (S r) := hpr ▸ hp_back
      let Dl := D.filter (fun u => 0 < orient2D (zWitness w h) (S h) (S u))
      have hcard2' : 2 ≤ Dl.card := hcard2
      let s_l := cb.m + 3 - (kh - (k_f - 1))
      have hl_shift : l = cb.p_idx (finShift i_h s_l) := by
        rw [hl_eq]
        dsimp [i_h, s_l]
        rw [finShift_add]
        have hsum : kh + (cb.m + 3 - (kh - (k_f - 1))) = (k_f - 1) + (cb.m + 3) := by omega
        rw [hsum, ← finShift_add, finShift_len]
      have hl_in_Dl : l ∈ Dl := by
        refine Finset.mem_filter.mpr ⟨hl_memD, ?_⟩
        rw [hl_eq]; exact hleft_h (k_f - 1) (by omega)
      have hk_split_lt_sl : k_split < s_l := by
        by_contra hle
        have h1 := hneg_arc s_l (by omega) (not_lt.mp hle)
        have h2 : 0 < orient2D (zWitness w h) (S h) (S l) := (Finset.mem_filter.mp hl_in_Dl).2
        rw [hl_shift] at h2
        linarith
      have hDl_sub : ∀ u ∈ Dl, ∃ s : ℕ, k_split < s ∧ s ≤ s_l ∧
          cb.p_idx (finShift i_h s) = u := by
        intro u huDl
        obtain ⟨s, hs_pos, hs_lt, hsu⟩ := h_u_of_k u (Finset.mem_filter.mp huDl).1
        have hs_gt : k_split < s := by
          by_contra hle
          have hneg := hneg_arc s hs_pos (not_lt.mp hle)
          have hpos := (Finset.mem_filter.mp huDl).2
          rw [← hsu] at hpos
          linarith
        have hs_le : s ≤ s_l := by
          by_contra hgt
          have hs_gt_sl : s_l < s := by omega
          have hmem_H : cb.p_idx (finShift i_h s) ∈ H := by
            dsimp [i_h]; rw [finShift_add]
            have heq_idx : finShift vc.i_max (kh + s) = finShift vc.i_max (kh + s - (cb.m + 3)) := by
              have hadd : kh + s = (kh + s - (cb.m + 3)) + (cb.m + 3) := by omega
              conv_lhs => rw [hadd, ← finShift_add, finShift_len]
            rw [heq_idx]
            exact (hblock (kh + s - (cb.m + 3)) (by omega)).mp ⟨by omega, by omega⟩
          rw [hsu] at hmem_H
          exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp huDl).1).2 hmem_H
        exact ⟨s, hs_gt, hs_le, hsu⟩
      have h_split_lt2 : k_split + 1 < s_l := by
        by_contra hle
        have hDl_le1 : Dl.card ≤ 1 := Finset.card_le_one.mpr (fun a ha b hb => by
          obtain ⟨sa, ha1, ha2, rfl⟩ := hDl_sub a ha
          obtain ⟨sb, hb1, hb2, rfl⟩ := hDl_sub b hb
          have hsa : sa = s_l := by omega
          have hsb : sb = s_l := by omega
          rw [hsa, hsb])
        omega
      let s_lm := s_l - 1
      let i_l := finShift vc.i_max (k_f - 1)
      let l_minus := cb.p_idx (i_l - 1)
      have hlm_shift : l_minus = cb.p_idx (finShift i_h s_lm) := by
        dsimp [l_minus, i_l, i_h, s_lm, s_l]
        congr 1
        symm; apply eq_sub_of_add_eq
        rw [finShift_succ (by omega : 2 ≤ cb.m + 3), finShift_add]
        have hsum : kh + (cb.m + 3 - (kh - (k_f - 1)) - 1 + 1) = (k_f - 1) + (cb.m + 3) := by omega
        rw [hsum, ← finShift_add, finShift_len]
      have hlm_pos_h : 0 < orient2D (zWitness w h) (S h) (S l_minus) := by
        rw [hlm_shift]; exact hpos_arc s_lm (by omega) (by omega)
      have hlm_memB : l_minus ∈ B := hcb_mem _
      have hlm_notH : l_minus ∉ H := by
        intro hlmH
        obtain ⟨klm, hklm0, hklm_lt, hklm_eq, _⟩ := separation hP hn cb vc (Finset.mem_filter.mp hlmH).2
        have hklm_range := (hblock klm (by omega)).mpr (hklm_eq ▸ hlmH)
        rcases lt_trichotomy klm kh with hlt | rfl | hgt
        · have hs_le_sl : s_lm = cb.m + 3 - (kh - klm) := by
            have heq : finShift i_h (cb.m + 3 - (kh - klm)) = finShift i_h s_lm := by
              apply cb.hp_idx_inj
              rw [← hlm_shift, ← hklm_eq]
              dsimp [i_h]; rw [finShift_add]
              have hsum : kh + (cb.m + 3 - (kh - klm)) = klm + (cb.m + 3) := by omega
              rw [hsum, ← finShift_add, finShift_len]
            have hsub := congrArg (· - i_h) heq
            rw [finShift_eq_add i_h (by omega : cb.m + 3 - (kh - klm) < cb.m + 3),
              finShift_eq_add i_h (by omega : s_lm < cb.m + 3),
              add_sub_cancel_left, add_sub_cancel_left] at hsub
            have hv := congrArg Fin.val hsub
            simp only at hv; omega
          omega
        · have heq : i_h = finShift i_h s_lm := cb.hp_idx_inj (by rw [hih_eq, ← hlm_shift, ← hklm_eq]; exact hkh_eq.symm)
          have hsub := congrArg (· - i_h) heq
          rw [sub_self, finShift_eq_add i_h (by omega : s_lm < cb.m + 3), add_sub_cancel_left] at hsub
          have hv := congrArg Fin.val hsub
          simp only [Fin.val_zero] at hv; omega
        · have := hright_h klm hgt (by omega); rw [hklm_eq] at this; linarith
      have hlm_memD : l_minus ∈ D := Finset.mem_sdiff.mpr ⟨hlm_memB, hlm_notH⟩
      let g := cb.p_idx (finShift vc.i_max k_g)
      have hgH : g ∈ H := (hblock k_g (by omega)).mp ⟨hkfg, le_rfl⟩
      have hg_cert := (Finset.mem_filter.mp hgH).2
      obtain ⟨kg', hkg'0, hkg'_lt, hkg'_eq, hleft_g, hright_g, _⟩ := separation hP hn cb vc hg_cert
      have hkg'_eq_kg : kg' = k_g := by
        by_contra hne
        exact hidx_inj kg' k_g (by omega) (by omega) hne hkg'_eq
      rw [hkg'_eq_kg] at hkg'_eq hleft_g hright_g
      have hg_l : 0 < orient2D (zWitness w g) (S g) (S l) := by
        rw [hl_eq]; exact hleft_g (k_f - 1) (by omega)
      have hg_lm : 0 < orient2D (zWitness w g) (S g) (S l_minus) := by
        by_cases hgh : g = h
        · rwa [hgh]
        · have hkh_lt_kg : kh < k_g := by
            refine lt_of_le_of_ne hkh_range.2 (fun heq => hgh ?_)
            dsimp [g]; rw [← hkh_eq, heq]
          by_contra hle
          have hne0 : orient2D (zWitness w g) (S g) (S l_minus) ≠ 0 := by
            have hlm_ne_g : l_minus ≠ g := fun heq => hlm_notH (heq ▸ hgH)
            exact hP.no_three_collinear (zWitness w g) (S g) (S l_minus)
              (Or.inr ⟨Finset.univ.erase g, rfl⟩) (Or.inl ⟨g, rfl⟩) (Or.inl ⟨l_minus, rfl⟩)
              (hP.s_ne_w g _).symm (fun h' => hlm_ne_g (hP.s_inj h').symm)
              (hP.s_ne_w l_minus (Finset.univ.erase g)).symm
          have hneg_g : orient2D (zWitness w g) (S g) (S l_minus) < 0 :=
            lt_of_le_of_ne (not_lt.mp hle) hne0
          have hl_ne_g : l ≠ g := fun heq => hl_notH (heq ▸ hgH)
          have hlm_ne_g : l_minus ≠ g := fun heq => hlm_notH (heq ▸ hgH)
          have htri_g := side_corners hP hn hg_cert hl_memB hlm_memB hl_ne_g hlm_ne_g
            (mul_neg_of_pos_of_neg hg_l hneg_g) Finset.univ
            ((hP.shatters Finset.univ _).mpr (Finset.mem_univ _))
            ((hP.shatters Finset.univ _).mpr (Finset.mem_univ _))
          have hr_neg_h : orient2D (zWitness w h) (S h) (S r) < 0 := by
            rw [hr_eq]; exact hright_h (k_g + 1) (by omega) (by omega)
          have hr_ne_h : r ≠ h := fun heq => hr_notH (heq ▸ hh)
          have hlm_ne_h : l_minus ≠ h := fun heq => hlm_notH (heq ▸ hh)
          have htri_h := side_corners hP hn hcert hlm_memB hr_memB hlm_ne_h hr_ne_h
            (mul_neg_of_pos_of_neg hlm_pos_h hr_neg_h) Finset.univ
            ((hP.shatters Finset.univ _).mpr (Finset.mem_univ _))
            ((hP.shatters Finset.univ _).mpr (Finset.mem_univ _))
          have hilm_ne_l : (i_l - 1) ≠ finShift vc.i_max (k_f - 1) := by
            intro heq
            have : i_l - 1 = i_l := heq
            have heq2 : i_l = i_l + 1 := eq_add_of_sub_eq this
            nth_rw 1 [← add_zero i_l] at heq2
            have h01 : (0 : Fin (cb.m + 3)) = 1 := add_left_cancel heq2
            have hv := congrArg Fin.val h01
            simp [Nat.mod_eq_of_lt (by omega : 1 < cb.m + 3)] at hv
          have htri_g' : InOpenTri (w Finset.univ) ((S ∘ cb.p_idx) (finShift vc.i_max (k_f - 1)))
              ((S ∘ cb.p_idx) (i_l - 1)) ((S ∘ cb.p_idx) (finShift vc.i_max k_g)) := by
            dsimp only [Function.comp_apply]; dsimp [g, l_minus] at htri_g ⊢; rw [← hl_eq]; exact htri_g
          have hbtw_g := inOpenTri_slope_between vc hilm_ne_l.symm htri_g'
          have hlm_ne_r : (i_l - 1) ≠ finShift vc.i_max (k_g + 1) := by
            intro heq
            have heq' : l_minus = r := by dsimp [l_minus]; rw [hr_eq]; exact congrArg cb.p_idx heq
            rw [← heq'] at hr_neg_h
            linarith
          have htri_h' : InOpenTri (w Finset.univ) ((S ∘ cb.p_idx) (i_l - 1))
              ((S ∘ cb.p_idx) (finShift vc.i_max (k_g + 1))) ((S ∘ cb.p_idx) (finShift vc.i_max kh)) := by
            dsimp only [Function.comp_apply]; rw [← hr_eq, hkh_eq]; exact htri_h
          have hbtw_h := inOpenTri_slope_between vc hlm_ne_r htri_h'
          have hs_gl : vc.slope (finShift vc.i_max k_g) < vc.slope (finShift vc.i_max (k_f - 1)) :=
            near_slope_strictAnti vc (by omega) (by omega)
          have hs_rh : vc.slope (finShift vc.i_max (k_g + 1)) < vc.slope (finShift vc.i_max kh) :=
            near_slope_strictAnti vc (by omega) (by omega)
          have hs_gh : vc.slope (finShift vc.i_max k_g) < vc.slope (finShift vc.i_max kh) :=
            near_slope_strictAnti vc hkh_lt_kg (by omega)
          rcases hbtw_g with ⟨hg1, hg2⟩ | ⟨hg1, hg2⟩ <;>
            rcases hbtw_h with ⟨hh1, hh2⟩ | ⟨hh1, hh2⟩ <;> linarith
      have hlm_l_edge : IsCCWHullEdge (B.image S) (S l_minus) (S l) := by
        rw [← himg_eq, hl_eq]
        exact (isCCWHullEdge_iff_succ cb.hstrict hp_inj).mpr
          ⟨i_l - 1, rfl, congrArg (S ∘ cb.p_idx) (sub_add_cancel i_l 1)⟩
      obtain ⟨a', ha'_mem, ha'_notO⟩ : ∃ a' ∈ ({l, l_minus} : Finset (Fin n)), a' ∉ O := by
        by_contra hnone
        push Not at hnone
        have hlO : l ∈ O ∩ D := Finset.mem_inter.mpr ⟨hnone l (by simp), hl_memD⟩
        have hlmO : l_minus ∈ O ∩ D := Finset.mem_inter.mpr ⟨hnone l_minus (by simp), hlm_memD⟩
        exact hO_noadj l_minus hlmO l hlO hlm_l_edge
      have ha'_memD : a' ∈ D := by
        rcases Finset.mem_insert.mp ha'_mem with rfl | ha'_mem2
        · exact hl_memD
        · rw [Finset.mem_singleton.mp ha'_mem2]; exact hlm_memD
      have ha'_memB : a' ∈ B := (Finset.mem_sdiff.mp ha'_memD).1
      have ha'_pos_g : 0 < orient2D (zWitness w g) (S g) (S a') := by
        rcases Finset.mem_insert.mp ha'_mem with rfl | ha'_mem2
        · exact hg_l
        · rw [Finset.mem_singleton.mp ha'_mem2]; exact hg_lm
      have hr_neg_g : orient2D (zWitness w g) (S g) (S r) < 0 := by
        rw [hr_eq]; exact hright_g (k_g + 1) (by omega) (by omega)
      have ha'_ne_g : a' ≠ g := fun heq => (Finset.mem_sdiff.mp ha'_memD).2 (heq ▸ hgH)
      have hr_ne_g : r ≠ g := fun heq => hr_notH (heq ▸ hgH)
      have ha'_ne_r : a' ≠ r := by
        intro heq; rw [heq] at ha'_pos_g; linarith
      have htri_v := side_corners hP hn hg_cert ha'_memB hr_memB ha'_ne_g hr_ne_g
        (mul_neg_of_pos_of_neg ha'_pos_g hr_neg_g) (Finset.univ \ O)
        ((hP.shatters _ a').mpr (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ha'_notO⟩))
        ((hP.shatters _ r).mpr (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hrO⟩))
      have hgr_edge : IsCCWHullEdge (B.image S) (S g) (S r) := by
        rw [← himg_eq, hr_eq]
        dsimp [g]
        have heq_r : finShift vc.i_max (k_g + 1) = finShift vc.i_max k_g + 1 :=
          (finShift_succ (by omega : 2 ≤ cb.m + 3) vc.i_max k_g).symm
        rw [heq_r]
        exact (isCCWHullEdge_iff_succ cb.hstrict hp_inj).mpr ⟨finShift vc.i_max k_g, rfl, rfl⟩
      have hgra' : 0 < orient2D (S g) (S r) (S a') :=
        hgr_edge.2.2.2 (S a') (Finset.mem_image.mpr ⟨a', ha'_memB, rfl⟩)
          (fun h' => ha'_ne_g (hP.s_inj h')) (fun h' => ha'_ne_r (hP.s_inj h'))
      have hagr : 0 < orient2D (S a') (S g) (S r) := by
        have : orient2D (S a') (S g) (S r) = orient2D (S g) (S r) (S a') := by unfold orient2D; ring
        linarith
      have hv_front_g := two_corners_isFrontVertex hP cb ((Finset.mem_filter.mp hgH).1)
        ha'_memB hr_memB ha'_ne_g hr_ne_g ha'_ne_r hagr htri_v
      rcases hv_front_g with ⟨_, c1, _, hgc1, _, ho_v⟩
      have hc1_eq : c1 = S r := isCCWHullEdge_succ_unique hgc1 hgr_edge
      rw [hc1_eq] at ho_v
      rcases hr_back with ⟨b1, _, hb1r, _, ho_back, _⟩
      have hb1_eq : b1 = S g := isCCWHullEdge_pred_unique hb1r hgr_edge
      rw [hb1_eq] at ho_back
      linarith
  refine ⟨h_part1, fun Q hQD hQ2 hQ_back M₀ _ h hm => ?_⟩
  have hhH : h ∈ H := (Finset.mem_sdiff.mp hm).1
  let Dl := D.filter (fun u => 0 < orient2D (zWitness w h) (S h) (S u))
  let Dr := D.filter (fun u => orient2D (zWitness w h) (S h) (S u) < 0)
  have hD_part : Dl ∪ Dr = D ∧ Disjoint Dl Dr := by
    refine ⟨?_, ?_⟩
    · ext u
      simp only [Dl, Dr, Finset.mem_union, Finset.mem_filter]
      constructor
      · rintro (⟨hu, _⟩ | ⟨hu, _⟩) <;> exact hu
      · intro hu
        have huh : u ≠ h := fun heq => (Finset.mem_sdiff.mp hu).2 (heq ▸ hhH)
        have hne0 : orient2D (zWitness w h) (S h) (S u) ≠ 0 :=
          hP.no_three_collinear (zWitness w h) (S h) (S u)
            (Or.inr ⟨Finset.univ.erase h, rfl⟩) (Or.inl ⟨h, rfl⟩) (Or.inl ⟨u, rfl⟩)
            (hP.s_ne_w h _).symm (fun h' => huh (hP.s_inj h').symm)
            (hP.s_ne_w u (Finset.univ.erase h)).symm
        rcases lt_or_gt_of_ne hne0 with hlt | hgt
        · exact Or.inr ⟨hu, hlt⟩
        · exact Or.inl ⟨hu, hgt⟩
    · exact Finset.disjoint_filter.mpr (fun _ _ h1 h2 => by linarith)
  have hD5' : 5 ≤ D.card := hD5
  have hcard_sum : Dl.card + Dr.card = D.card := by
    rw [← Finset.card_union_of_disjoint hD_part.2, hD_part.1]
  have hcert := (Finset.mem_filter.mp hhH).2
  obtain ⟨kh, hkh0, hkh_lt, hkh_eq, hleft_h, hright_h, _⟩ := separation hP hn cb vc hcert
  have hkh_range := (hblock kh (by omega)).mpr (hkh_eq ▸ hhH)
  have hl_in_Dl : l ∈ Dl := Finset.mem_filter.mpr ⟨hl_memD, by rw [hl_eq]; exact hleft_h (k_f - 1) (by omega)⟩
  have hr_in_Dr : r ∈ Dr := Finset.mem_filter.mpr ⟨hr_memD, by rw [hr_eq]; exact hright_h (k_g + 1) (by omega) (by omega)⟩
  have ha_ex : (Dl \ Q).Nonempty := by
    by_contra h_empty
    rw [Finset.not_nonempty_iff_eq_empty, Finset.sdiff_eq_empty_iff_subset] at h_empty
    have hlQ : l ∈ Q := h_empty hl_in_Dl
    have hDl_le2 : Dl.card ≤ 2 := le_trans (Finset.card_le_card h_empty) hQ2
    have hDr_ge2 : 2 ≤ Dr.card := by omega
    obtain ⟨O, hpO, hOnoadj, hback⟩ := hQ_back l hlQ
    exact (h_part1 l O hl_memD hpO hOnoadj hback h hhH).1 hDr_ge2 rfl
  have hb_ex : (Dr \ Q).Nonempty := by
    by_contra h_empty
    rw [Finset.not_nonempty_iff_eq_empty, Finset.sdiff_eq_empty_iff_subset] at h_empty
    have hrQ : r ∈ Q := h_empty hr_in_Dr
    have hDr_le2 : Dr.card ≤ 2 := le_trans (Finset.card_le_card h_empty) hQ2
    have hDl_ge2 : 2 ≤ Dl.card := by omega
    obtain ⟨O, hpO, hOnoadj, hback⟩ := hQ_back r hrQ
    exact (h_part1 r O hr_memD hpO hOnoadj hback h hhH).2 hDl_ge2 rfl
  obtain ⟨a, ha⟩ := ha_ex
  obtain ⟨b, hb⟩ := hb_ex
  have ha_sdiff := Finset.mem_sdiff.mp ha
  have hb_sdiff := Finset.mem_sdiff.mp hb
  have ha_F : a ∈ (D \ Q) ∪ M₀ := Finset.mem_union_left M₀ (Finset.mem_sdiff.mpr ⟨(Finset.mem_filter.mp ha_sdiff.1).1, ha_sdiff.2⟩)
  have hb_F : b ∈ (D \ Q) ∪ M₀ := Finset.mem_union_left M₀ (Finset.mem_sdiff.mpr ⟨(Finset.mem_filter.mp hb_sdiff.1).1, hb_sdiff.2⟩)
  have ha_memB : a ∈ B := (Finset.mem_sdiff.mp (Finset.mem_filter.mp ha_sdiff.1).1).1
  have hb_memB : b ∈ B := (Finset.mem_sdiff.mp (Finset.mem_filter.mp hb_sdiff.1).1).1
  have ha_ne_h : a ≠ h := fun heq => (Finset.mem_sdiff.mp (Finset.mem_filter.mp ha_sdiff.1).1).2 (heq ▸ hhH)
  have hb_ne_h : b ≠ h := fun heq => (Finset.mem_sdiff.mp (Finset.mem_filter.mp hb_sdiff.1).1).2 (heq ▸ hhH)
  have ha_pos : 0 < orient2D (zWitness w h) (S h) (S a) := (Finset.mem_filter.mp ha_sdiff.1).2
  have hb_neg : orient2D (zWitness w h) (S h) (S b) < 0 := (Finset.mem_filter.mp hb_sdiff.1).2
  exact ⟨a, ha_F, b, hb_F, side_corners hP hn hcert ha_memB hb_memB ha_ne_h hb_ne_h (mul_neg_of_pos_of_neg ha_pos hb_neg)⟩

private lemma endpoint_split_arc {n : ℕ} {P : Set (ℝ × ℝ)} {S : Fin n → ℝ × ℝ}
    {w : Finset (Fin n) → ℝ × ℝ}
    (hP : ShatteredSimplePolygon P S w) (hn : 3 ≤ n)
    (cb : CyclicSubsetBoundary S (hullVertices S))
    (vc : VisibleContour (S ∘ cb.p_idx) (w Finset.univ))
    (hH : (certifiedSet P S w).Nonempty)
    (hD5 : 5 ≤ (hullVertices S \ certifiedSet P S w).card)
    (dc : CyclicSubsetBoundary S (hullVertices S \ certifiedSet P S w))
    {k_f k_g : ℕ} {l r : Fin n}
    (hkf0 : 0 < k_f) (hkfg : k_f ≤ k_g) (hkg_lt : k_g < vc.d_near)
    (hl_eq : l = cb.p_idx (finShift vc.i_max (k_f - 1)))
    (hr_eq : r = cb.p_idx (finShift vc.i_max (k_g + 1)))
    (hblock : ∀ k : ℕ, k < cb.m + 3 →
      (k_f ≤ k ∧ k ≤ k_g ↔ cb.p_idx (finShift vc.i_max k) ∈ certifiedSet P S w))
    {p y_other : Fin n}
    (hp_end : (p = l ∧ y_other = r) ∨ (p = r ∧ y_other = l))
    (O : Finset (Fin n)) (hpO : p ∉ O)
    (hOnoadj : ∀ a ∈ O ∩ (hullVertices S \ certifiedSet P S w),
      ∀ b ∈ O ∩ (hullVertices S \ certifiedSet P S w),
      ¬ IsCCWHullEdge ((hullVertices S).image S) (S a) (S b))
    (hp_back : IsBackVertex ((hullVertices S).image S) (w (Finset.univ \ O)) (S p))
    (i_lr : Fin (dc.m + 3)) (hilr_eq : dc.p_idx i_lr = l) (hir_eq : dc.p_idx (i_lr + 1) = r)
    (h : Fin n) (hh : h ∈ certifiedSet P S w) :
    let D := hullVertices S \ certifiedSet P S w
    ∃ k_s : ℕ, 1 ≤ k_s ∧ k_s ≤ dc.m + 2 ∧
      (∀ k : ℕ, 1 ≤ k → k ≤ k_s → orient2D (zWitness w h) (S h) (S (dc.p_idx (finShift i_lr k))) < 0) ∧
      (∀ k : ℕ, k_s < k → k ≤ dc.m + 3 → 0 < orient2D (zWitness w h) (S h) (S (dc.p_idx (finShift i_lr k)))) ∧
      (k_s ≤ (D.filter (fun u => orient2D (zWitness w h) (S h) (S u) < 0)).card) ∧
      (dc.m + 3 - k_s ≤ (D.filter (fun u => 0 < orient2D (zWitness w h) (S h) (S u))).card) ∧
      (p = l → k_s = 1) ∧ (p = r → k_s = dc.m + 2) := by

  let B := hullVertices S
  let H := certifiedSet P S w
  let D := B \ H
  have hcb_mem : ∀ j : Fin (cb.m + 3), cb.p_idx j ∈ B := fun j => by
    have h : cb.p_idx j ∈ Finset.univ.image cb.p_idx := Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
    rwa [cb.hp_idx_img] at h
  have hdc_mem : ∀ j : Fin (dc.m + 3), dc.p_idx j ∈ D := fun j => by
    have h : dc.p_idx j ∈ Finset.univ.image dc.p_idx := Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
    rwa [dc.hp_idx_img] at h
  have hDc_card : dc.m + 3 = D.card := by
    have himg : (Finset.univ : Finset (Fin (dc.m + 3))).image dc.p_idx = D := dc.hp_idx_img
    calc dc.m + 3 = (Finset.univ : Finset (Fin (dc.m + 3))).card := (Fintype.card_fin _).symm
      _ = ((Finset.univ : Finset (Fin (dc.m + 3))).image dc.p_idx).card :=
          (Finset.card_image_of_injective _ dc.hp_idx_inj).symm
      _ = D.card := by rw [himg]
  have hD5' : 5 ≤ D.card := hD5
  have hD_ge5 : 5 ≤ dc.m + 3 := by omega
  have hl_memD : l ∈ D := Finset.mem_sdiff.mpr ⟨hl_eq ▸ hcb_mem _, fun hh => by
    rw [hl_eq, ← hblock (k_f - 1) (by have := vc.hd_lt; omega)] at hh; omega⟩
  have hr_memD : r ∈ D := Finset.mem_sdiff.mpr ⟨hr_eq ▸ hcb_mem _, fun hh => by
    rw [hr_eq, ← hblock (k_g + 1) (by have := vc.hd_lt; omega)] at hh; omega⟩
  have hl_ne_r : l ≠ r := by
    intro heq
    rw [hl_eq, hr_eq] at heq
    have hsub := congrArg (· - vc.i_max) (cb.hp_idx_inj heq)
    have := vc.hd_lt
    rw [finShift_eq_add vc.i_max (by omega : k_f - 1 < cb.m + 3),
      finShift_eq_add vc.i_max (by omega : k_g + 1 < cb.m + 3),
      add_sub_cancel_left, add_sub_cancel_left] at hsub
    have hv := congrArg Fin.val hsub
    simp only at hv; omega
  have h_lr_edge_D : IsCCWHullEdge (D.image S) (S l) (S r) := by
    refine ⟨Finset.mem_image.mpr ⟨l, hl_memD, rfl⟩, Finset.mem_image.mpr ⟨r, hr_memD, rfl⟩,
      fun h => hl_ne_r (hP.s_inj h), fun c hc hcl hcr => ?_⟩
    rcases Finset.mem_image.mp hc with ⟨d, hdD, rfl⟩
    have hdB : d ∈ B := (Finset.mem_sdiff.mp hdD).1
    have hd_img : d ∈ Finset.univ.image cb.p_idx := by rw [cb.hp_idx_img]; exact hdB
    rcases Finset.mem_image.mp hd_img with ⟨jd, _, rfl⟩
    let kd := (jd - vc.i_max).val
    have hkd_lt : kd < cb.m + 3 := (jd - vc.i_max).isLt
    have hjd_eq : jd = finShift vc.i_max kd := (finShift_sub vc.i_max jd).symm
    have hd_notH : cb.p_idx jd ∉ H := (Finset.mem_sdiff.mp hdD).2
    have hd_vc := vc.hd_lt
    have hkd_out : kd < k_f - 1 ∨ k_g + 1 < kd := by
      by_contra hle; have h1 : k_f - 1 ≤ kd ∧ kd ≤ k_g + 1 := by omega
      by_cases heq1 : kd = k_f - 1
      · apply hcl; rw [hl_eq, hjd_eq, heq1]
      · by_cases heq2 : kd = k_g + 1
        · apply hcr; rw [hr_eq, hjd_eq, heq2]
        · apply hd_notH; rw [hjd_eq]; exact (hblock kd hkd_lt).mp ⟨by omega, by omega⟩
    rw [hl_eq, hr_eq, hjd_eq]
    rcases hkd_out with hlt | hgt
    · exact cb.hcyc (finShift vc.i_max (k_f - 1)) (finShift vc.i_max (k_g + 1)) (finShift vc.i_max kd)
        (cyclicOrder_cycle (cyclicOrder_finShift vc.i_max hlt (by omega) (by omega)))
    · exact cb.hcyc (finShift vc.i_max (k_f - 1)) (finShift vc.i_max (k_g + 1)) (finShift vc.i_max kd)
        (cyclicOrder_finShift vc.i_max (by omega) hgt hkd_lt)
  have himg_D : Finset.univ.image (S ∘ dc.p_idx) = D.image S := by
    calc Finset.univ.image (S ∘ dc.p_idx)
        = (Finset.univ.image dc.p_idx).image S := Finset.image_image.symm
      _ = D.image S := by rw [dc.hp_idx_img]
  have h_sp := side_preservation hP hn cb vc hH hD5 hkf0 hkfg hkg_lt hl_eq hr_eq hblock
  have hp_memD : p ∈ D := by rcases hp_end with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> assumption
  have hy_memD : y_other ∈ D := by rcases hp_end with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> assumption
  have h_forbid : ∀ h ∈ H,
      (p = l → (D.filter (fun u => orient2D (zWitness w h) (S h) (S u) < 0)).card < 2) ∧
      (p = r → (D.filter (fun u => 0 < orient2D (zWitness w h) (S h) (S u))).card < 2) := by
    intro h hh
    have hsp1 := h_sp.1 p O hp_memD hpO hOnoadj hp_back h hh
    exact ⟨fun hpl => by by_contra hge; exact hsp1.1 (Nat.le_of_not_lt hge) hpl,
      fun hpr => by by_contra hge; exact hsp1.2 (Nat.le_of_not_lt hge) hpr⟩
  let f_arc : ℕ → Fin n := fun k => dc.p_idx (finShift i_lr k)
  have hf_arc_inj : Set.InjOn f_arc (Finset.Icc 1 (dc.m + 3) : Set ℕ) := by
    intro a ha b hb heq
    rw [Finset.mem_coe, Finset.mem_Icc] at ha hb
    have hsh : finShift i_lr a = finShift i_lr b := dc.hp_idx_inj heq
    have hsub := congrArg (· - i_lr) hsh
    dsimp [finShift] at hsub
    have hval := congrArg Fin.val hsub
    have ha' : ((⟨(i_lr.val + a) % (dc.m + 3), Nat.mod_lt _ (by omega)⟩ : Fin (dc.m + 3)) - i_lr).val =
        a % (dc.m + 3) := by
      have : finShift i_lr a = finShift i_lr (a % (dc.m + 3)) := by
        dsimp [finShift]; congr 1; simp [Nat.add_mod]
      rw [finShift_eq_add i_lr (Nat.mod_lt _ (by omega))] at this
      have h1 : (⟨(i_lr.val + a) % (dc.m + 3), Nat.mod_lt _ (by omega)⟩ : Fin (dc.m + 3)) - i_lr =
          ⟨a % (dc.m + 3), Nat.mod_lt _ (by omega)⟩ := by
        have := congrArg (· - i_lr) this
        simpa [finShift] using this
      rw [h1]
    have hb' : ((⟨(i_lr.val + b) % (dc.m + 3), Nat.mod_lt _ (by omega)⟩ : Fin (dc.m + 3)) - i_lr).val =
        b % (dc.m + 3) := by
      have : finShift i_lr b = finShift i_lr (b % (dc.m + 3)) := by
        dsimp [finShift]; congr 1; simp [Nat.add_mod]
      rw [finShift_eq_add i_lr (Nat.mod_lt _ (by omega))] at this
      have h1 : (⟨(i_lr.val + b) % (dc.m + 3), Nat.mod_lt _ (by omega)⟩ : Fin (dc.m + 3)) - i_lr =
          ⟨b % (dc.m + 3), Nat.mod_lt _ (by omega)⟩ := by
        have := congrArg (· - i_lr) this
        simpa [finShift] using this
      rw [h1]
    rw [ha', hb'] at hval
    rcases Nat.eq_or_lt_of_le ha.2 with rfl | ha_lt <;> rcases Nat.eq_or_lt_of_le hb.2 with rfl | hb_lt
    · rfl
    · rw [Nat.mod_self, Nat.mod_eq_of_lt hb_lt] at hval; omega
    · rw [Nat.mod_self, Nat.mod_eq_of_lt ha_lt] at hval; omega
    · rw [Nat.mod_eq_of_lt ha_lt, Nat.mod_eq_of_lt hb_lt] at hval; exact hval
  let _ := hy_memD
  let _ := himg_D
  let _ := h_lr_edge_D
  have hcert := (Finset.mem_filter.mp hh).2
  obtain ⟨kh, _, _, hkh_eq, hleft_h, hright_h, _⟩ := separation hP hn cb vc hcert
  have hkh_range := (hblock kh (by have := vc.hd_lt; omega)).mpr (hkh_eq ▸ hh)
  have hl_pos : 0 < orient2D (zWitness w h) (S h) (S l) := by
    rw [hl_eq]; exact hleft_h (k_f - 1) (by omega)
  have hr_neg : orient2D (zWitness w h) (S h) (S r) < 0 := by
    rw [hr_eq]; exact hright_h (k_g + 1) (by omega) (by omega)
  have hl_tri : InOpenTri (zWitness w h) (S l) (S r) (S h) :=
    side_corners hP hn hcert (Finset.mem_sdiff.mp hl_memD).1 (Finset.mem_sdiff.mp hr_memD).1
      (fun heq => (Finset.mem_sdiff.mp hl_memD).2 (heq ▸ hh))
      (fun heq => (Finset.mem_sdiff.mp hr_memD).2 (heq ▸ hh))
      (mul_neg_of_pos_of_neg hl_pos hr_neg) (Finset.univ.erase h)
      ((hP.shatters _ l).mpr (Finset.mem_erase.mpr ⟨fun heq => (Finset.mem_sdiff.mp hl_memD).2 (heq ▸ hh), Finset.mem_univ _⟩))
      ((hP.shatters _ r).mpr (Finset.mem_erase.mpr ⟨fun heq => (Finset.mem_sdiff.mp hr_memD).2 (heq ▸ hh), Finset.mem_univ _⟩))
  rcases hl_tri with ⟨μ₁, μ₂, μ₃, hμ1, hμ2, hμ3, hμsum, hxh1, hxh2⟩
  let s₀ := μ₃ / (μ₂ + μ₃)
  let y₁ : ℝ × ℝ := ((1 - s₀) * (S l).1 + s₀ * (S r).1, (1 - s₀) * (S l).2 + s₀ * (S r).2)
  have hμ23 : 0 < μ₂ + μ₃ := add_pos hμ2 hμ3
  have hs0_01 : 0 < s₀ ∧ s₀ < 1 := ⟨div_pos hμ3 hμ23, (div_lt_one hμ23).mpr (by linarith)⟩
  have h_line_ratio : ∀ x : ℝ × ℝ,
      (μ₂ + μ₃) * orient2D (zWitness w h) y₁ x = orient2D (zWitness w h) (S h) x := by
    intro x
    have h1m : μ₁ = 1 - μ₂ - μ₃ := by linarith
    unfold orient2D; dsimp [y₁, s₀]; rw [hxh1, hxh2, h1m]
    field_simp [ne_of_gt hμ23]; ring
  have hy1_arc_ord : ∀ a b : ℕ, 1 ≤ a → a < b → b ≤ dc.m + 3 → ¬ (a = 1 ∧ b = dc.m + 3) →
      0 < orient2D y₁ (S (f_arc a)) (S (f_arc b)) := by
    intro a b ha hab hb hnot1end
    have hl_nn : 0 ≤ orient2D (S l) (S (f_arc a)) (S (f_arc b)) := by
      rcases Nat.eq_or_lt_of_le hb with rfl | hb_lt
      · have hbe : f_arc (dc.m + 3) = l := by
          dsimp [f_arc]; rw [finShift_len, hilr_eq]
        rw [hbe, orient2D_self_outer]
      · have ha_pos : 0 < a := by omega
        have h0 : f_arc 0 = l := by
          dsimp [f_arc]; rw [finShift_zero, hilr_eq]
        rw [← h0]
        exact le_of_lt (dc.hcyc (finShift i_lr 0) (finShift i_lr a) (finShift i_lr b)
          (cyclicOrder_finShift i_lr ha_pos hab hb_lt))
    have hr_nn : 0 ≤ orient2D (S r) (S (f_arc a)) (S (f_arc b)) := by
      rcases Nat.eq_or_lt_of_le ha with rfl | ha_gt
      · have hae : f_arc 1 = r := by
          dsimp [f_arc]; rw [finShift_one (by omega), hir_eq]
        rw [hae, orient2D_self_left]
      · have h1 : f_arc 1 = r := by
          dsimp [f_arc]; rw [finShift_one (by omega), hir_eq]
        rw [← h1]
        rcases Nat.eq_or_lt_of_le hb with rfl | hb_lt
        · have h0 : f_arc 0 = l := by
            dsimp [f_arc]; rw [finShift_zero, hilr_eq]
          have hbe : f_arc (dc.m + 3) = l := by
            dsimp [f_arc]; rw [finShift_len, hilr_eq]
          rw [hbe, ← h0]
          exact le_of_lt (dc.hcyc (finShift i_lr 1) (finShift i_lr a) (finShift i_lr 0)
            (cyclicOrder_cycle (cyclicOrder_finShift i_lr (by omega : 0 < 1) ha_gt (by omega))))
        · exact le_of_lt (dc.hcyc (finShift i_lr 1) (finShift i_lr a) (finShift i_lr b)
            (cyclicOrder_finShift i_lr ha_gt hab hb_lt))
    have h_strict_one : 0 < orient2D (S l) (S (f_arc a)) (S (f_arc b)) ∨
        0 < orient2D (S r) (S (f_arc a)) (S (f_arc b)) := by
      rcases Nat.eq_or_lt_of_le ha with rfl | ha_gt
      · have hb_lt : b < dc.m + 3 := by omega
        have h0 : f_arc 0 = l := by
          dsimp [f_arc]; rw [finShift_zero, hilr_eq]
        left; rw [← h0]
        exact dc.hcyc (finShift i_lr 0) (finShift i_lr 1) (finShift i_lr b)
          (cyclicOrder_finShift i_lr (by omega) hab hb_lt)
      · right
        have h1 : f_arc 1 = r := by
          dsimp [f_arc]; rw [finShift_one (by omega), hir_eq]
        rw [← h1]
        rcases Nat.eq_or_lt_of_le hb with rfl | hb_lt
        · have h0 : f_arc 0 = l := by
            dsimp [f_arc]; rw [finShift_zero, hilr_eq]
          have hbe : f_arc (dc.m + 3) = l := by
            dsimp [f_arc]; rw [finShift_len, hilr_eq]
          rw [hbe, ← h0]
          exact dc.hcyc (finShift i_lr 1) (finShift i_lr a) (finShift i_lr 0)
            (cyclicOrder_cycle (cyclicOrder_finShift i_lr (by omega : 0 < 1) ha_gt (by omega)))
        · exact dc.hcyc (finShift i_lr 1) (finShift i_lr a) (finShift i_lr b)
            (cyclicOrder_finShift i_lr ha_gt hab hb_lt)
    have hid : orient2D y₁ (S (f_arc a)) (S (f_arc b)) =
        (1 - s₀) * orient2D (S l) (S (f_arc a)) (S (f_arc b)) +
        s₀ * orient2D (S r) (S (f_arc a)) (S (f_arc b)) := by
      unfold orient2D; dsimp [y₁]; ring
    rw [hid]
    rcases h_strict_one with hp1 | hp2 <;> nlinarith [hs0_01.1, hs0_01.2]
  have h_mono : ∀ a b : ℕ, 1 ≤ a → a < b → b ≤ dc.m + 3 →
      0 ≤ orient2D (zWitness w h) (S h) (S (f_arc a)) →
      0 < orient2D (zWitness w h) (S h) (S (f_arc b)) := by
    intro a b ha hab hb ha_nn
    have ha1 : f_arc 1 = r := by dsimp [f_arc]; rw [finShift_one (by omega), hir_eq]
    have ha_ne1 : a ≠ 1 := by
      intro heq; rw [heq, ha1] at ha_nn; linarith
    rcases Nat.eq_or_lt_of_le hb with rfl | hb_lt
    · have hbe : f_arc (dc.m + 3) = l := by dsimp [f_arc]; rw [finShift_len, hilr_eq]
      rwa [hbe]
    · have h1a := hy1_arc_ord 1 a le_rfl (by omega) (by omega) (by omega)
      have h1b := hy1_arc_ord 1 b le_rfl (by omega) (by omega) (by omega)
      have hab_or := hy1_arc_ord a b (by omega) hab (by omega) (by omega)
      have hplucker : orient2D y₁ (S (f_arc 1)) (S (f_arc b)) * orient2D (zWitness w h) y₁ (S (f_arc a)) =
          orient2D y₁ (S (f_arc a)) (S (f_arc b)) * orient2D (zWitness w h) y₁ (S (f_arc 1)) +
          orient2D y₁ (S (f_arc 1)) (S (f_arc a)) * orient2D (zWitness w h) y₁ (S (f_arc b)) := by
        unfold orient2D; ring
      have hy_a_nn : 0 ≤ orient2D (zWitness w h) y₁ (S (f_arc a)) := by
        have := h_line_ratio (S (f_arc a)); nlinarith
      have hy_1_neg : orient2D (zWitness w h) y₁ (S (f_arc 1)) < 0 := by
        rw [ha1]; have := h_line_ratio (S r); nlinarith
      have hy_b_pos : 0 < orient2D (zWitness w h) y₁ (S (f_arc b)) := by nlinarith
      rw [← h_line_ratio]; exact mul_pos hμ23 hy_b_pos
  let Kneg := (Finset.Icc 1 (dc.m + 3)).filter
    (fun k => orient2D (zWitness w h) (S h) (S (f_arc k)) < 0)
  have h1_in_Kneg : 1 ∈ Kneg := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩, ?_⟩
    have ha1 : f_arc 1 = r := by dsimp [f_arc]; rw [finShift_one (by omega), hir_eq]
    rwa [ha1]
  have hKneg_ne : Kneg.Nonempty := ⟨1, h1_in_Kneg⟩
  let k_s := Kneg.max' hKneg_ne
  have hks_mem := Finset.max'_mem Kneg hKneg_ne
  have hks_ge1 : 1 ≤ k_s := (Finset.mem_Icc.mp (Finset.mem_filter.mp hks_mem).1).1
  have hks_le_end : k_s ≤ dc.m + 3 := (Finset.mem_Icc.mp (Finset.mem_filter.mp hks_mem).1).2
  have hks_neg : orient2D (zWitness w h) (S h) (S (f_arc k_s)) < 0 :=
    (Finset.mem_filter.mp hks_mem).2
  have hks_le2 : k_s ≤ dc.m + 2 := by
    by_contra hgt
    have heq : k_s = dc.m + 3 := by omega
    have hbe : f_arc (dc.m + 3) = l := by dsimp [f_arc]; rw [finShift_len, hilr_eq]
    rw [heq, hbe] at hks_neg; linarith
  have hk_neg_all : ∀ k : ℕ, 1 ≤ k → k ≤ k_s →
      orient2D (zWitness w h) (S h) (S (f_arc k)) < 0 := by
    intro k hk1 hk2
    rcases Nat.eq_or_lt_of_le hk2 with rfl | hk_lt
    · exact hks_neg
    · by_contra hnn
      have := h_mono k k_s hk1 hk_lt hks_le_end (not_lt.mp hnn)
      linarith
  have hk_pos_all : ∀ k : ℕ, k_s < k → k ≤ dc.m + 3 →
      0 < orient2D (zWitness w h) (S h) (S (f_arc k)) := by
    intro k hk1 hk2
    have hk_not : k ∉ Kneg := fun hm => by
      have := Finset.le_max' Kneg k hm; omega
    have hnn : 0 ≤ orient2D (zWitness w h) (S h) (S (f_arc k)) := by
      by_contra hlt; apply hk_not
      exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, hk2⟩, lt_of_not_ge hlt⟩
    have hne0 : orient2D (zWitness w h) (S h) (S (f_arc k)) ≠ 0 := by
      have hfD : f_arc k ∈ D := hdc_mem _
      have hfh : f_arc k ≠ h := fun heq => (Finset.mem_sdiff.mp hfD).2 (heq ▸ hh)
      exact hP.no_three_collinear (zWitness w h) (S h) (S (f_arc k))
        (Or.inr ⟨Finset.univ.erase h, rfl⟩) (Or.inl ⟨h, rfl⟩) (Or.inl ⟨f_arc k, rfl⟩)
        (hP.s_ne_w h _).symm (fun h' => hfh (hP.s_inj h').symm)
        (hP.s_ne_w (f_arc k) (Finset.univ.erase h)).symm
    exact lt_of_le_of_ne hnn hne0.symm
  let Dr := D.filter (fun u => orient2D (zWitness w h) (S h) (S u) < 0)
  let Dl := D.filter (fun u => 0 < orient2D (zWitness w h) (S h) (S u))
  have hDr_ge : k_s ≤ Dr.card := by
    have hsub : (Finset.Icc 1 k_s).image f_arc ⊆ Dr := by
      intro u hu
      rcases Finset.mem_image.mp hu with ⟨k, hk, rfl⟩
      rw [Finset.mem_Icc] at hk
      exact Finset.mem_filter.mpr ⟨hdc_mem _, hk_neg_all k hk.1 hk.2⟩
    have hinj : Set.InjOn f_arc (Finset.Icc 1 k_s : Set ℕ) :=
      hf_arc_inj.mono (Finset.coe_subset.mpr (Finset.Icc_subset_Icc_right (by omega)))
    calc k_s = (Finset.Icc 1 k_s).card := by rw [Nat.card_Icc]; omega
      _ = ((Finset.Icc 1 k_s).image f_arc).card := (Finset.card_image_of_injOn hinj).symm
      _ ≤ Dr.card := Finset.card_le_card hsub
  have hDl_ge : dc.m + 3 - k_s ≤ Dl.card := by
    have hsub : (Finset.Icc (k_s + 1) (dc.m + 3)).image f_arc ⊆ Dl := by
      intro u hu
      rcases Finset.mem_image.mp hu with ⟨k, hk, rfl⟩
      rw [Finset.mem_Icc] at hk
      exact Finset.mem_filter.mpr ⟨hdc_mem _, hk_pos_all k (by omega) hk.2⟩
    have hinj : Set.InjOn f_arc (Finset.Icc (k_s + 1) (dc.m + 3) : Set ℕ) :=
      hf_arc_inj.mono (Finset.coe_subset.mpr (Finset.Icc_subset_Icc_left (by omega)))
    calc dc.m + 3 - k_s = (Finset.Icc (k_s + 1) (dc.m + 3)).card := by rw [Nat.card_Icc]; omega
      _ = ((Finset.Icc (k_s + 1) (dc.m + 3)).image f_arc).card := (Finset.card_image_of_injOn hinj).symm
      _ ≤ Dl.card := Finset.card_le_card hsub
  have hks_l : p = l → k_s = 1 := fun hpl => by
    have hlt : Dr.card < 2 := (h_forbid h hh).1 hpl
    omega
  have hks_r : p = r → k_s = dc.m + 2 := fun hpr => by
    have hlt : Dl.card < 2 := (h_forbid h hh).2 hpr
    omega
  exact ⟨k_s, hks_ge1, hks_le2, hk_neg_all, hk_pos_all, hDr_ge, hDl_ge, hks_l, hks_r⟩

/-- Corollary 4.6 (`Endpoint back-vertex criterion`, `upper_9.tex` lines 426–432). -/
theorem endpoint_back_vertex_criterion {n : ℕ} {P : Set (ℝ × ℝ)} {S : Fin n → ℝ × ℝ}
    {w : Finset (Fin n) → ℝ × ℝ}
    (hP : ShatteredSimplePolygon P S w) (hn : 3 ≤ n)
    (cb : CyclicSubsetBoundary S (hullVertices S))
    (vc : VisibleContour (S ∘ cb.p_idx) (w Finset.univ))
    (hH : (certifiedSet P S w).Nonempty)
    (hD5 : 5 ≤ (hullVertices S \ certifiedSet P S w).card)
    (dc : CyclicSubsetBoundary S (hullVertices S \ certifiedSet P S w))
    {k_f k_g : ℕ} {l r : Fin n}
    (hkf0 : 0 < k_f) (hkfg : k_f ≤ k_g) (hkg_lt : k_g < vc.d_near)
    (hl_eq : l = cb.p_idx (finShift vc.i_max (k_f - 1)))
    (hr_eq : r = cb.p_idx (finShift vc.i_max (k_g + 1)))
    (hblock : ∀ k : ℕ, k < cb.m + 3 →
      (k_f ≤ k ∧ k ≤ k_g ↔ cb.p_idx (finShift vc.i_max k) ∈ certifiedSet P S w))
    {p y_other : Fin n}
    (hp_end : (p = l ∧ y_other = r) ∨ (p = r ∧ y_other = l))
    (O : Finset (Fin n)) (hpO : p ∉ O)
    (hOnoadj : ∀ a ∈ O ∩ (hullVertices S \ certifiedSet P S w),
      ∀ b ∈ O ∩ (hullVertices S \ certifiedSet P S w),
      ¬ IsCCWHullEdge ((hullVertices S).image S) (S a) (S b))
    (hp_back : IsBackVertex ((hullVertices S).image S) (w (Finset.univ \ O)) (S p)) :
    let B := hullVertices S
    let H := certifiedSet P S w
    let D := B \ H
    (∀ h ∈ H, ∀ i : Fin (dc.m + 3),
      0 < orient2D (S (dc.p_idx i)) (S (dc.p_idx (i + 1))) (w D) →
      InOpenTri (w D) (S (dc.p_idx i)) (S (dc.p_idx (i + 1))) (S h) →
      (y_other = dc.p_idx i ∨ y_other = dc.p_idx (i + 1))) ∧
    (∀ O' : Finset (Fin n), y_other ∉ O' →
      (∀ a ∈ O' ∩ D, ∀ b ∈ O' ∩ D, ¬ IsCCWHullEdge (B.image S) (S a) (S b)) →
      ¬ IsBackVertex (B.image S) (w (Finset.univ \ O')) (S y_other)) := by

  let B := hullVertices S
  let H := certifiedSet P S w
  let D := B \ H
  have hcb_mem : ∀ j : Fin (cb.m + 3), cb.p_idx j ∈ B := fun j => by
    have h : cb.p_idx j ∈ Finset.univ.image cb.p_idx := Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
    rwa [cb.hp_idx_img] at h
  have hdc_mem : ∀ j : Fin (dc.m + 3), dc.p_idx j ∈ D := fun j => by
    have h : dc.p_idx j ∈ Finset.univ.image dc.p_idx := Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
    rwa [dc.hp_idx_img] at h
  have hDc_card : dc.m + 3 = D.card := by
    have himg : (Finset.univ : Finset (Fin (dc.m + 3))).image dc.p_idx = D := dc.hp_idx_img
    calc dc.m + 3 = (Finset.univ : Finset (Fin (dc.m + 3))).card := (Fintype.card_fin _).symm
      _ = ((Finset.univ : Finset (Fin (dc.m + 3))).image dc.p_idx).card :=
          (Finset.card_image_of_injective _ dc.hp_idx_inj).symm
      _ = D.card := by rw [himg]
  have hD5' : 5 ≤ D.card := hD5
  have hD_ge5 : 5 ≤ dc.m + 3 := by omega
  have hl_memD : l ∈ D := Finset.mem_sdiff.mpr ⟨hl_eq ▸ hcb_mem _, fun hh => by
    rw [hl_eq, ← hblock (k_f - 1) (by have := vc.hd_lt; omega)] at hh; omega⟩
  have hr_memD : r ∈ D := Finset.mem_sdiff.mpr ⟨hr_eq ▸ hcb_mem _, fun hh => by
    rw [hr_eq, ← hblock (k_g + 1) (by have := vc.hd_lt; omega)] at hh; omega⟩
  have hl_ne_r : l ≠ r := by
    intro heq
    rw [hl_eq, hr_eq] at heq
    have hsub := congrArg (· - vc.i_max) (cb.hp_idx_inj heq)
    have := vc.hd_lt
    rw [finShift_eq_add vc.i_max (by omega : k_f - 1 < cb.m + 3),
      finShift_eq_add vc.i_max (by omega : k_g + 1 < cb.m + 3),
      add_sub_cancel_left, add_sub_cancel_left] at hsub
    have hv := congrArg Fin.val hsub
    simp only at hv; omega
  have h_lr_edge_D : IsCCWHullEdge (D.image S) (S l) (S r) := by
    refine ⟨Finset.mem_image.mpr ⟨l, hl_memD, rfl⟩, Finset.mem_image.mpr ⟨r, hr_memD, rfl⟩,
      fun h => hl_ne_r (hP.s_inj h), fun c hc hcl hcr => ?_⟩
    rcases Finset.mem_image.mp hc with ⟨d, hdD, rfl⟩
    have hdB : d ∈ B := (Finset.mem_sdiff.mp hdD).1
    have hd_img : d ∈ Finset.univ.image cb.p_idx := by rw [cb.hp_idx_img]; exact hdB
    rcases Finset.mem_image.mp hd_img with ⟨jd, _, rfl⟩
    let kd := (jd - vc.i_max).val
    have hkd_lt : kd < cb.m + 3 := (jd - vc.i_max).isLt
    have hjd_eq : jd = finShift vc.i_max kd := (finShift_sub vc.i_max jd).symm
    have hd_notH : cb.p_idx jd ∉ H := (Finset.mem_sdiff.mp hdD).2
    have hd_vc := vc.hd_lt
    have hkd_out : kd < k_f - 1 ∨ k_g + 1 < kd := by
      by_contra hle; have h1 : k_f - 1 ≤ kd ∧ kd ≤ k_g + 1 := by omega
      by_cases heq1 : kd = k_f - 1
      · apply hcl; rw [hl_eq, hjd_eq, heq1]
      · by_cases heq2 : kd = k_g + 1
        · apply hcr; rw [hr_eq, hjd_eq, heq2]
        · apply hd_notH; rw [hjd_eq]; exact (hblock kd hkd_lt).mp ⟨by omega, by omega⟩
    rw [hl_eq, hr_eq, hjd_eq]
    rcases hkd_out with hlt | hgt
    · exact cb.hcyc (finShift vc.i_max (k_f - 1)) (finShift vc.i_max (k_g + 1)) (finShift vc.i_max kd)
        (cyclicOrder_cycle (cyclicOrder_finShift vc.i_max hlt (by omega) (by omega)))
    · exact cb.hcyc (finShift vc.i_max (k_f - 1)) (finShift vc.i_max (k_g + 1)) (finShift vc.i_max kd)
        (cyclicOrder_finShift vc.i_max (by omega) hgt hkd_lt)
  have himg_D : Finset.univ.image (S ∘ dc.p_idx) = D.image S := by
    calc Finset.univ.image (S ∘ dc.p_idx)
        = (Finset.univ.image dc.p_idx).image S := Finset.image_image.symm
      _ = D.image S := by rw [dc.hp_idx_img]
  obtain ⟨i_lr, hilr_eq, hir_eq⟩ : ∃ i_lr : Fin (dc.m + 3), dc.p_idx i_lr = l ∧ dc.p_idx (i_lr + 1) = r := by
    rw [← himg_D] at h_lr_edge_D
    obtain ⟨i_lr, hi1, hi2⟩ := (isCCWHullEdge_iff_succ dc.hstrict (hP.s_inj.comp dc.hp_idx_inj)).mp h_lr_edge_D
    exact ⟨i_lr, hP.s_inj hi1, hP.s_inj hi2⟩
  have h_sp := side_preservation hP hn cb vc hH hD5 hkf0 hkfg hkg_lt hl_eq hr_eq hblock
  have hp_memD : p ∈ D := by rcases hp_end with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> assumption
  have hy_memD : y_other ∈ D := by rcases hp_end with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> assumption
  have h_forbid : ∀ h ∈ H,
      (p = l → (D.filter (fun u => orient2D (zWitness w h) (S h) (S u) < 0)).card < 2) ∧
      (p = r → (D.filter (fun u => 0 < orient2D (zWitness w h) (S h) (S u))).card < 2) := by
    intro h hh
    have hsp1 := h_sp.1 p O hp_memD hpO hOnoadj hp_back h hh
    exact ⟨fun hpl => by by_contra hge; exact hsp1.1 (Nat.le_of_not_lt hge) hpl,
      fun hpr => by by_contra hge; exact hsp1.2 (Nat.le_of_not_lt hge) hpr⟩
  have h_split_arc := fun h hh => endpoint_split_arc hP hn cb vc hH hD5 dc hkf0 hkfg hkg_lt
    hl_eq hr_eq hblock hp_end O hpO hOnoadj hp_back i_lr hilr_eq hir_eq h hh
  refine ⟨?_, ?_⟩
  · intro h hh i hui htri_u
    obtain ⟨k_s, hks1, hks2, hk_neg_all, hk_pos_all, _, _, hks_l, hks_r⟩ := h_split_arc h hh
    have hcert := (Finset.mem_filter.mp hh).2
    obtain ⟨kh, _, _, hkh_eq, _⟩ := separation hP hn cb vc hcert
    have hkh_range := (hblock kh (by have := vc.hd_lt; omega)).mpr (hkh_eq ▸ hh)
    have h_tri_zh : InOpenTri (zWitness w h) (S (dc.p_idx i)) (S (dc.p_idx (i + 1))) (S h) := by
      have hh_memM : h ∈ interiorPoints S ∪ H := Finset.mem_union_right _ hh
      have h_ex := exit_edge hP hn (by omega) dc h hh_memM
      have hi_mem : dc.p_idx i ∈ D := hdc_mem i
      have hi1_mem : dc.p_idx (i + 1) ∈ D := hdc_mem (i + 1)
      have h_zh_i : Sees P (zWitness w h) (S (dc.p_idx i)) :=
        (hP.shatters (Finset.univ.erase h) _).mpr
          (Finset.mem_erase.mpr ⟨fun heq => (Finset.mem_sdiff.mp hi_mem).2 (heq ▸ hh), Finset.mem_univ _⟩)
      have h_zh_i1 : Sees P (zWitness w h) (S (dc.p_idx (i + 1))) :=
        (hP.shatters (Finset.univ.erase h) _).mpr
          (Finset.mem_erase.mpr ⟨fun heq => (Finset.mem_sdiff.mp hi1_mem).2 (heq ▸ hh), Finset.mem_univ _⟩)
      exact (h_ex.2 i hui htri_u).1 (Finset.univ.erase h) h_zh_i h_zh_i1
    have hopp_uv : orient2D (zWitness w h) (S h) (S (dc.p_idx i)) *
        orient2D (zWitness w h) (S h) (S (dc.p_idx (i + 1))) < 0 := by
      rcases h_tri_zh with ⟨μ₁, μ₂, μ₃, h1, h2, h3, hsum, hx1, hx2⟩
      have h1_eq : μ₁ = 1 - μ₂ - μ₃ := by linarith
      have ho1 : orient2D (zWitness w h) (S h) (S (dc.p_idx i)) =
          μ₃ * orient2D (zWitness w h) (S (dc.p_idx (i + 1))) (S (dc.p_idx i)) := by
        unfold orient2D; rw [hx1, hx2, h1_eq]; ring
      have ho2 : orient2D (zWitness w h) (S h) (S (dc.p_idx (i + 1))) =
          μ₂ * orient2D (zWitness w h) (S (dc.p_idx i)) (S (dc.p_idx (i + 1))) := by
        unfold orient2D; rw [hx1, hx2, h1_eq]; ring
      rw [ho1, ho2, orient2D_swap23 (zWitness w h) (S (dc.p_idx (i + 1))) (S (dc.p_idx i))]
      have hne : orient2D (zWitness w h) (S (dc.p_idx i)) (S (dc.p_idx (i + 1))) ≠ 0 := by
        have hed : dc.p_idx i ≠ dc.p_idx (i + 1) := by
          intro heq; have := dc.hp_idx_inj heq
          nth_rw 1 [← add_zero i] at this
          have h01 := add_left_cancel this
          have hv := congrArg Fin.val h01
          simp [Nat.mod_eq_of_lt (by omega : 1 < dc.m + 3)] at hv
        exact hP.no_three_collinear (zWitness w h) (S (dc.p_idx i)) (S (dc.p_idx (i + 1)))
          (Or.inr ⟨Finset.univ.erase h, rfl⟩) (Or.inl ⟨dc.p_idx i, rfl⟩) (Or.inl ⟨dc.p_idx (i + 1), rfl⟩)
          (hP.s_ne_w _ _).symm (fun h' => hed (hP.s_inj h')) (hP.s_ne_w _ _).symm
      have hsq : 0 < (orient2D (zWitness w h) (S (dc.p_idx (i + 1))) (S (dc.p_idx i))) ^ 2 :=
        sq_pos_of_ne_zero (fun h0 => hne (by rw [orient2D_swap23, h0, neg_zero]))
      nlinarith [mul_pos h2 h3]
    have hi_ne_ilr : i ≠ i_lr := by
      intro heq; subst heq
      rw [hilr_eq, hir_eq] at hui htri_u
      have hlhr : 0 < orient2D (S l) (S h) (S r) := by
        rw [hl_eq, hr_eq, ← hkh_eq]
        exact cb.hcyc _ _ _ (cyclicOrder_finShift vc.i_max (by omega) (by omega) (by have := vc.hd_lt; omega))
      rcases htri_u with ⟨μ₁, μ₂, μ₃, h1, h2, h3, hsum, hx1, hx2⟩
      have hor : orient2D (S l) (S r) (S h) = μ₁ * orient2D (S l) (S r) (w D) := by
        have h1m : μ₁ = 1 - μ₂ - μ₃ := by linarith
        unfold orient2D; rw [hx1, hx2, h1m]; ring
      rw [orient2D_swap23] at hor
      nlinarith
    let ki := (i - i_lr).val
    have hki_lt : ki < dc.m + 3 := (i - i_lr).isLt
    have hki_ge1 : 1 ≤ ki := by
      by_contra h0
      have hki0 : ki = 0 := by omega
      exact hi_ne_ilr (sub_eq_zero.mp (Fin.ext hki0))
    have hi_shift : dc.p_idx i = dc.p_idx (finShift i_lr ki) := by
      rw [finShift_sub]
    have hi1_shift : dc.p_idx (i + 1) = dc.p_idx (finShift i_lr (ki + 1)) := by
      rw [← finShift_succ (by omega : 2 ≤ dc.m + 3), finShift_sub]
    have hki_eq_ks : ki = k_s := by
      rcases lt_trichotomy ki k_s with hlt | heq | hgt
      · have hs1 := hk_neg_all ki hki_ge1 (le_of_lt hlt)
        have hs2 := hk_neg_all (ki + 1) (by omega) hlt
        rw [← hi_shift] at hs1; rw [← hi1_shift] at hs2
        have hpos : 0 < orient2D (zWitness w h) (S h) (S (dc.p_idx i)) *
            orient2D (zWitness w h) (S h) (S (dc.p_idx (i + 1))) := mul_pos_of_neg_of_neg hs1 hs2
        linarith
      · exact heq
      · have hs1 := hk_pos_all ki hgt (by omega)
        have hs2 := hk_pos_all (ki + 1) (by omega) (by omega)
        rw [← hi_shift] at hs1; rw [← hi1_shift] at hs2
        have hpos : 0 < orient2D (zWitness w h) (S h) (S (dc.p_idx i)) *
            orient2D (zWitness w h) (S h) (S (dc.p_idx (i + 1))) := mul_pos hs1 hs2
        linarith
    rcases hp_end with ⟨hpl, hyr⟩ | ⟨hpr, hyl⟩
    · left
      have hks : k_s = 1 := hks_l hpl
      rw [hyr, hi_shift, hki_eq_ks, hks, finShift_one (by omega), hir_eq]
    · right
      have hks : k_s = dc.m + 2 := hks_r hpr
      have hsum : dc.m + 2 + 1 = dc.m + 3 := by omega
      have hlen : finShift i_lr (dc.m + 2 + 1) = i_lr :=
        (congrArg (finShift i_lr) hsum).trans (finShift_len i_lr)
      rw [hyl, hi1_shift, hki_eq_ks, hks, hlen, hilr_eq]
  · intro O' hyO' hO'noadj hy_back
    obtain ⟨h, hh⟩ := hH
    obtain ⟨k_s, hks1, hks2, _, _, hDr_ge, hDl_ge, hks_l, hks_r⟩ := h_split_arc h hh
    have hsp1 := h_sp.1 y_other O' hy_memD hyO' hO'noadj hy_back h hh
    rcases hp_end with ⟨hpl, hyr⟩ | ⟨hpr, hyl⟩
    · have hks : k_s = 1 := hks_l hpl
      have h2_nat : 2 ≤ dc.m + 3 - k_s := by
        rw [hks]
        exact Nat.le_trans (by decide : 2 ≤ 4) (Nat.sub_le_sub_right hD_ge5 1)
      have h2_dl : 2 ≤ (D.filter (fun u => 0 < orient2D (zWitness w h) (S h) (S u))).card :=
        le_trans h2_nat hDl_ge
      exact hsp1.2 h2_dl hyr
    · have hks : k_s = dc.m + 2 := hks_r hpr
      have h2_nat : 2 ≤ k_s := by
        rw [hks]
        exact le_trans (by decide : 2 ≤ 4) (Nat.sub_le_sub_right hD_ge5 1)
      have h2_dr : 2 ≤ (D.filter (fun u => orient2D (zWitness w h) (S h) (S u) < 0)).card :=
        le_trans h2_nat hDr_ge
      exact hsp1.1 h2_dr hyl

end PolygonCore

end
