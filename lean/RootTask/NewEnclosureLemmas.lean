import Mathlib
import RootTask.PolygonDefs
import RootTask.PolygonEnclosureCore

open scoped Classical BigOperators
open Finset

noncomputable section

namespace NewEnclosure

open PolygonCore

/-!
# New Polygon Enclosure Lemmas & Hereditary Shattering (`Upper8Verified`)

Formalizes over `ShatteredSimplePolygon P S w`:
1. `vis_SS_chord_enclosure` & `vis_SS_triangle_enclosure` (Two-Round Chord & Triangle Enclosure),
2. `crossed_segment_tri_T1` & `crossed_segment_tri_T2` (`T1` & `T2`),
3. `convex_quad_vertex_enclosure_N1` & `dart_star_kernel_enclosure` (`N1` + Dart Star-Kernel),
4. `hereditary_shattered_subset` (every 7-element subset of a 9-point shattered set under `(G1)-(G2)`
   is shattered in `P` under `(G1)-(G2)` without re-perturbation).
-/

/-! ## Helper Predicates and Planar Geometry Lemmas -/

/-- Two points `x, y` lie strictly on the same open side of the directed line `a -> b`. -/
def SameSide (a b x y : ℝ × ℝ) : Prop :=
  0 < orient2D a b x * orient2D a b y

/-- Segments `[p₁, p₂]` and `[q₁, q₂]` properly cross in their open interiors. -/
def ProperCross (p₁ p₂ q₁ q₂ : ℝ × ℝ) : Prop :=
  orient2D p₁ p₂ q₁ * orient2D p₁ p₂ q₂ < 0 ∧
  orient2D q₁ q₂ p₁ * orient2D q₁ q₂ p₂ < 0

/-- Four points `(p₀, p₁, p₂, p₃)` form a strictly convex CCW quadrilateral. -/
def StrictConvexCCWQuad (p₀ p₁ p₂ p₃ : ℝ × ℝ) : Prop :=
  0 < orient2D p₀ p₁ p₂ ∧ 0 < orient2D p₁ p₂ p₃ ∧
  0 < orient2D p₂ p₃ p₀ ∧ 0 < orient2D p₃ p₀ p₁

/-- Four points `(p₀, p₁, p₂, p₃)` form a strictly convex (CCW or CW) quadrilateral. -/
def StrictConvexQuad (p₀ p₁ p₂ p₃ : ℝ × ℝ) : Prop :=
  StrictConvexCCWQuad p₀ p₁ p₂ p₃ ∨ StrictConvexCCWQuad p₃ p₂ p₁ p₀

lemma sameSide_symm {a b x y : ℝ × ℝ} (h : SameSide a b x y) : SameSide a b y x := by
  unfold SameSide at *; linarith

lemma orient2D_ne_zero_of_mul_neg {x y : ℝ} (h : x * y < 0) : x ≠ 0 ∧ y ≠ 0 :=
  ⟨fun hx => by rw [hx, zero_mul] at h; exact lt_irrefl 0 h,
   fun hy => by rw [hy, mul_zero] at h; exact lt_irrefl 0 h⟩

lemma inClosedTri_of_orient_nonneg {a b c x : ℝ × ℝ}
    (habc : 0 < orient2D a b c)
    (habx : 0 ≤ orient2D a b x) (hbcx : 0 ≤ orient2D b c x) (hcax : 0 ≤ orient2D c a x) :
    InClosedTri a b c x := by
  have hsum_or : orient2D b c x + orient2D c a x + orient2D a b x = orient2D a b c := by
    unfold orient2D; ring
  have hdet_ne : orient2D a b c ≠ 0 := ne_of_gt habc
  refine ⟨orient2D b c x / orient2D a b c, orient2D c a x / orient2D a b c,
    orient2D a b x / orient2D a b c,
    div_nonneg hbcx (le_of_lt habc), div_nonneg hcax (le_of_lt habc), div_nonneg habx (le_of_lt habc),
    ?_, ?_, ?_⟩
  · field_simp [hdet_ne]; linarith
  · field_simp [hdet_ne]; unfold orient2D; ring
  · field_simp [hdet_ne]; unfold orient2D; ring

lemma mem_convexHull_tri_of_orient_same {a b c x : ℝ × ℝ}
    (hne : orient2D a b c ≠ 0)
    (h1 : 0 ≤ orient2D a b x * orient2D a b c)
    (h2 : 0 ≤ orient2D b c x * orient2D b c a)
    (h3 : 0 ≤ orient2D c a x * orient2D c a b) :
    x ∈ convexHull ℝ ({a, b, c} : Set (ℝ × ℝ)) := by
  have hbc : orient2D b c a = orient2D a b c := by unfold orient2D; ring
  have hca : orient2D c a b = orient2D a b c := by unfold orient2D; ring
  rw [hbc] at h2
  rw [hca] at h3
  have nonpos_of_mul_nn_neg : ∀ {u v : ℝ}, 0 ≤ u * v → v < 0 → u ≤ 0 := fun hu hv =>
    by_contra fun h => absurd (mul_neg_of_pos_of_neg (lt_of_not_ge h) hv) (not_lt.mpr hu)
  rw [← inClosedTri_iff_mem_convexHull]
  rcases lt_or_gt_of_ne hne with hneg | hpos
  · have hpos' : 0 < orient2D a c b := by rw [orient2D_swap23]; linarith
    have hc1 : 0 ≤ orient2D a c x := by
      rw [show orient2D a c x = -orient2D c a x by unfold orient2D; ring]
      linarith [nonpos_of_mul_nn_neg h3 hneg]
    have hc2 : 0 ≤ orient2D c b x := by
      rw [show orient2D c b x = -orient2D b c x by unfold orient2D; ring]
      linarith [nonpos_of_mul_nn_neg h2 hneg]
    have hc3 : 0 ≤ orient2D b a x := by
      rw [show orient2D b a x = -orient2D a b x by unfold orient2D; ring]
      linarith [nonpos_of_mul_nn_neg h1 hneg]
    have hin := inClosedTri_of_orient_nonneg hpos' hc1 hc2 hc3
    rcases hin with ⟨μ₁, μ₂, μ₃, hμ1, hμ2, hμ3, hsum, hx1, hx2⟩
    exact ⟨μ₁, μ₃, μ₂, hμ1, hμ3, hμ2, by linarith, by linarith, by linarith⟩
  · exact inClosedTri_of_orient_nonneg hpos
      (nonneg_of_mul_nonneg_left h1 hpos)
      (nonneg_of_mul_nonneg_left h2 hpos)
      (nonneg_of_mul_nonneg_left h3 hpos)

lemma inOpenTri_of_sameSide {a b c z : ℝ × ℝ}
    (hne : orient2D a b c ≠ 0)
    (h1 : SameSide a b z c) (h2 : SameSide b c z a) (h3 : SameSide c a z b) :
    InOpenTri a b c z := by
  have hbc : orient2D b c a = orient2D a b c := by unfold orient2D; ring
  have hca : orient2D c a b = orient2D a b c := by unfold orient2D; ring
  unfold SameSide at h1 h2 h3
  rw [hbc] at h2
  rw [hca] at h3
  have neg_of_mul_pos_neg : ∀ {u v : ℝ}, 0 < u * v → v < 0 → u < 0 := fun hu hv =>
    by_contra fun h =>
      absurd (mul_nonpos_of_nonneg_of_nonpos (not_lt.mp h) (le_of_lt hv)) (not_le.mpr hu)
  rcases lt_or_gt_of_ne hne with hneg | hpos
  · refine inOpenTri_perm_23 (inOpenTri_of_orient_pos ?_ ?_ ?_ ?_)
    · rw [orient2D_swap23]; linarith
    · rw [show orient2D a c z = -orient2D c a z by unfold orient2D; ring]
      linarith [neg_of_mul_pos_neg h3 hneg]
    · rw [show orient2D c b z = -orient2D b c z by unfold orient2D; ring]
      linarith [neg_of_mul_pos_neg h2 hneg]
    · rw [show orient2D b a z = -orient2D a b z by unfold orient2D; ring]
      linarith [neg_of_mul_pos_neg h1 hneg]
  · exact inOpenTri_of_orient_pos hpos (by nlinarith) (by nlinarith) (by nlinarith)

lemma sees_of_mem_convexHull_tri {P : Set (ℝ × ℝ)} {a b c x y : ℝ × ℝ}
    (htri : convexHull ℝ ({a, b, c} : Set (ℝ × ℝ)) ⊆ P)
    (hx : x ∈ convexHull ℝ ({a, b, c} : Set (ℝ × ℝ)))
    (hy : y ∈ convexHull ℝ ({a, b, c} : Set (ℝ × ℝ))) :
    Sees P x y :=
  ((convex_convexHull ℝ ({a, b, c} : Set (ℝ × ℝ))).segment_subset hx hy).trans htri

lemma mem_convexHull_tri_left {a b c : ℝ × ℝ} :
    a ∈ convexHull ℝ ({a, b, c} : Set (ℝ × ℝ)) :=
  subset_convexHull ℝ _ (by simp)

lemma mem_convexHull_tri_mid {a b c : ℝ × ℝ} :
    b ∈ convexHull ℝ ({a, b, c} : Set (ℝ × ℝ)) :=
  subset_convexHull ℝ _ (by simp)

lemma mem_convexHull_tri_right {a b c : ℝ × ℝ} :
    c ∈ convexHull ℝ ({a, b, c} : Set (ℝ × ℝ)) :=
  subset_convexHull ℝ _ (by simp)

/-- Proper crossing `[p₁, p₂] × [q₁, q₂]` yields a unique intersection `X` strictly inside both segments. -/
lemma properCross_exists_intersection {p₁ p₂ q₁ q₂ : ℝ × ℝ} (hc : ProperCross p₁ p₂ q₁ q₂) :
    ∃ t s : ℝ, 0 < t ∧ t < 1 ∧ 0 < s ∧ s < 1 ∧
      ((1 - t) • p₁ + t • p₂) = ((1 - s) • q₁ + s • q₂) := by
  rcases hc with ⟨hp, hq⟩
  set d₁ := orient2D q₁ q₂ p₁
  set d₂ := orient2D q₁ q₂ p₂
  set e₁ := orient2D p₁ p₂ q₁
  set e₂ := orient2D p₁ p₂ q₂
  have hd_diff_ne : d₁ - d₂ ≠ 0 := by
    intro h0
    have heq : d₁ = d₂ := sub_eq_zero.mp h0
    have hsq : d₁ * d₂ = d₁ * d₁ := by rw [heq]
    nlinarith [sq_nonneg d₁]
  have he_diff_ne : e₁ - e₂ ≠ 0 := by
    intro h0
    have heq : e₁ = e₂ := sub_eq_zero.mp h0
    have hsq : e₁ * e₂ = e₁ * e₁ := by rw [heq]
    nlinarith [sq_nonneg e₁]
  let t : ℝ := d₁ / (d₁ - d₂)
  let s : ℝ := e₁ / (e₁ - e₂)
  have ht0 : 0 < t := by
    have hnum : 0 < d₁ * (d₁ - d₂) := by
      have : d₁ * (d₁ - d₂) = d₁ ^ 2 - d₁ * d₂ := by ring
      nlinarith [sq_nonneg d₁]
    dsimp [t]
    rcases lt_or_gt_of_ne hd_diff_ne with hneg | hpos
    · exact div_pos_of_neg_of_neg (by nlinarith) hneg
    · exact div_pos (by nlinarith) hpos
  have ht1 : t < 1 := by
    have h1t : 1 - t = -d₂ / (d₁ - d₂) := by
      dsimp [t]; field_simp [hd_diff_ne]; ring
    have hpos : 0 < 1 - t := by
      rw [h1t]
      have hnum : 0 < (-d₂) * (d₁ - d₂) := by
        have : (-d₂) * (d₁ - d₂) = d₂ ^ 2 - d₁ * d₂ := by ring
        nlinarith [sq_nonneg d₂]
      rcases lt_or_gt_of_ne hd_diff_ne with hneg | hpos'
      · exact div_pos_of_neg_of_neg (by nlinarith) hneg
      · exact div_pos (by nlinarith) hpos'
    linarith
  have hs0 : 0 < s := by
    have hnum : 0 < e₁ * (e₁ - e₂) := by
      have : e₁ * (e₁ - e₂) = e₁ ^ 2 - e₁ * e₂ := by ring
      nlinarith [sq_nonneg e₁]
    dsimp [s]
    rcases lt_or_gt_of_ne he_diff_ne with hneg | hpos
    · exact div_pos_of_neg_of_neg (by nlinarith) hneg
    · exact div_pos (by nlinarith) hpos
  have hs1 : s < 1 := by
    have h1s : 1 - s = -e₂ / (e₁ - e₂) := by
      dsimp [s]; field_simp [he_diff_ne]; ring
    have hpos : 0 < 1 - s := by
      rw [h1s]
      have hnum : 0 < (-e₂) * (e₁ - e₂) := by
        have : (-e₂) * (e₁ - e₂) = e₂ ^ 2 - e₁ * e₂ := by ring
        nlinarith [sq_nonneg e₂]
      rcases lt_or_gt_of_ne he_diff_ne with hneg | hpos'
      · exact div_pos_of_neg_of_neg (by nlinarith) hneg
      · exact div_pos (by nlinarith) hpos'
    linarith
  have hdet_eq : d₁ - d₂ = -(e₁ - e₂) := by
    dsimp [d₁, d₂, e₁, e₂]; unfold orient2D; ring
  refine ⟨t, s, ht0, ht1, hs0, hs1, ?_⟩
  ext
  · change (1 - t) * p₁.1 + t * p₂.1 = (1 - s) * q₁.1 + s * q₂.1
    dsimp [t, s]
    rw [hdet_eq]
    field_simp [he_diff_ne]
    dsimp [d₁, d₂, e₁, e₂]; unfold orient2D; ring
  · change (1 - t) * p₁.2 + t * p₂.2 = (1 - s) * q₁.2 + s * q₂.2
    dsimp [t, s]
    rw [hdet_eq]
    field_simp [he_diff_ne]
    dsimp [d₁, d₂, e₁, e₂]; unfold orient2D; ring


/-! ## 1. Two-Round Iterated Chord & Triangle Enclosure (`vis_SS`) -/

/-- **Round 1 (`vis_SS_chord_enclosure`)**: If two witnesses `w T₁, w T₂` both see `S a` and `S b`
    (`a ≠ b`) and lie on strictly opposite sides of the line `S a -> S b`, then `[S a, S b] ⊆ P`. -/
theorem vis_SS_chord_enclosure {n : ℕ} {P : Set (ℝ × ℝ)}
    {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ}
    (hP : ShatteredSimplePolygon P S w)
    {a b : Fin n} (hab : a ≠ b) {T₁ T₂ : Finset (Fin n)}
    (ha1 : a ∈ T₁) (hb1 : b ∈ T₁) (ha2 : a ∈ T₂) (hb2 : b ∈ T₂)
    (hopp : orient2D (S a) (S b) (w T₁) * orient2D (S a) (S b) (w T₂) < 0) :
    Sees P (S a) (S b) := by
  have hne : S a ≠ S b := fun h => hab (hP.s_inj h)
  have hsa1 : Sees P (S a) (w T₁) := sees_symm ((hP.shatters T₁ a).mpr ha1)
  have hsb1 : Sees P (w T₁) (S b) := (hP.shatters T₁ b).mpr hb1
  have hsa2 : Sees P (S a) (w T₂) := sees_symm ((hP.shatters T₂ a).mpr ha2)
  have hsb2 : Sees P (w T₂) (S b) := (hP.shatters T₂ b).mpr hb2
  have hpath1 : IsPolygonalPathIn P (S a) (S b) [S a, w T₁, S b] :=
    isPolygonalPathIn_three hsa1 hsb1
  have hpath2 : IsPolygonalPathIn P (S a) (S b) [S a, w T₂, S b] :=
    isPolygonalPathIn_three hsa2 hsb2
  have hne0 := orient2D_ne_zero_of_mul_neg hopp
  have hsides :
      (InteriorOnLeft (S a) (S b) [S a, w T₁, S b] ∧ InteriorOnRight (S a) (S b) [S a, w T₂, S b]) ∨
      (InteriorOnRight (S a) (S b) [S a, w T₁, S b] ∧ InteriorOnLeft (S a) (S b) [S a, w T₂, S b]) := by
    rcases lt_or_gt_of_ne hne0.1 with h1n | h1p
    · right
      refine ⟨interiorOnRight_three h1n, interiorOnLeft_three (by nlinarith)⟩
    · left
      refine ⟨interiorOnLeft_three h1p, interiorOnRight_three (by nlinarith)⟩
  exact two_path_enclosure_either hP.toEnclosureDomain hne hpath1 hpath2 hsides

/-- **Round 2 (`vis_SS_triangle_enclosure`)**: Under Round 1 chord enclosure of `[S a, S b]`,
    any third witness `w T₃` seeing `S a` and `S b` encloses the triangle
    `conv {w T₃, S a, S b} ⊆ P`, trapping every point inside it to see both `S a` and `S b`. -/
theorem vis_SS_triangle_enclosure {n : ℕ} {P : Set (ℝ × ℝ)}
    {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ}
    (hP : ShatteredSimplePolygon P S w)
    {a b : Fin n} (hab : a ≠ b) {T₁ T₂ T₃ : Finset (Fin n)}
    (ha1 : a ∈ T₁) (hb1 : b ∈ T₁) (ha2 : a ∈ T₂) (hb2 : b ∈ T₂)
    (hopp : orient2D (S a) (S b) (w T₁) * orient2D (S a) (S b) (w T₂) < 0)
    (ha3 : a ∈ T₃) (hb3 : b ∈ T₃) :
    convexHull ℝ ({w T₃, S a, S b} : Set (ℝ × ℝ)) ⊆ P ∧
    (∀ z : ℝ × ℝ, z ∈ convexHull ℝ ({w T₃, S a, S b} : Set (ℝ × ℝ)) →
      Sees P z (S a) ∧ Sees P z (S b)) := by
  have hchord : Sees P (S a) (S b) :=
    vis_SS_chord_enclosure hP hab ha1 hb1 ha2 hb2 hopp
  have h3a : Sees P (w T₃) (S a) := (hP.shatters T₃ a).mpr ha3
  have h3b : Sees P (w T₃) (S b) := (hP.shatters T₃ b).mpr hb3
  have htri : convexHull ℝ ({w T₃, S a, S b} : Set (ℝ × ℝ)) ⊆ P :=
    hP.triangle_enclosure (w T₃) (hP.w_in_P T₃) (S a) (hP.s_in_P a) (S b) (hP.s_in_P b)
      h3a hchord h3b
  refine ⟨htri, fun z hz => ⟨?_, ?_⟩⟩
  · exact sees_of_mem_convexHull_tri htri hz mem_convexHull_tri_mid
  · exact sees_of_mem_convexHull_tri htri hz mem_convexHull_tri_right


/-! ## 2. Crossed-Segment Triangles `T1` and `T2` -/

/-- **Rule `T1` (`crossed_segment_tri_T1`)**: If `w T₁` sees `S a, S b`, `w T₂` sees `S b`, and
    `[w T₁, S a]` properly crosses `[w T₂, S b]` at `X`, then `conv {w T₁, S b, X} ⊆ P`.
    Moreover, any point `z` satisfying the three `SameSide` chirotope tests of `T1`
    lies in `InOpenTri (w T₁) (S b) X`, hence `z ∈ P` and `Sees P z (S b)`. -/
theorem crossed_segment_tri_T1 {n : ℕ} {P : Set (ℝ × ℝ)}
    {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ}
    (hP : ShatteredSimplePolygon P S w)
    {a b : Fin n} {T₁ T₂ : Finset (Fin n)}
    (ha1 : a ∈ T₁) (hb1 : b ∈ T₁) (hb2 : b ∈ T₂)
    (hcross : ProperCross (w T₁) (S a) (w T₂) (S b)) :
    ∃ X : ℝ × ℝ,
      X ∈ segment ℝ (w T₁) (S a) ∧
      X ∈ segment ℝ (w T₂) (S b) ∧
      convexHull ℝ ({w T₁, S b, X} : Set (ℝ × ℝ)) ⊆ P ∧
      (∀ z : ℝ × ℝ,
        SameSide (w T₁) (S a) z (S b) →
        SameSide (w T₂) (S b) z (w T₁) →
        SameSide (w T₁) (S b) z (S a) →
        InOpenTri (w T₁) (S b) X z ∧ z ∈ P ∧ Sees P z (S b)) := by
  obtain ⟨t, s, ht0, ht1, hs0, hs1, hXeq⟩ := properCross_exists_intersection hcross
  let X : ℝ × ℝ := (1 - t) • w T₁ + t • S a
  have hX_seg1 : X ∈ segment ℝ (w T₁) (S a) := by
    rw [segment_eq_image]
    exact ⟨t, ⟨le_of_lt ht0, le_of_lt ht1⟩, by ext <;> simp [X, smul_eq_mul]⟩
  have hX_seg2 : X ∈ segment ℝ (w T₂) (S b) := by
    dsimp [X]; rw [hXeq, segment_eq_image]
    exact ⟨s, ⟨le_of_lt hs0, le_of_lt hs1⟩, by ext <;> simp [smul_eq_mul]⟩
  have hw1a : Sees P (w T₁) (S a) := (hP.shatters T₁ a).mpr ha1
  have hw1b : Sees P (w T₁) (S b) := (hP.shatters T₁ b).mpr hb1
  have hw2b : Sees P (w T₂) (S b) := (hP.shatters T₂ b).mpr hb2
  have hw1X : Sees P (w T₁) X := sees_of_mem_segment_left hw1a hX_seg1
  have hbX : Sees P (S b) X := sees_symm (sees_of_mem_segment_right hw2b hX_seg2)
  have hX_in_P : X ∈ P := sees_mem_right hw1X
  have htri : convexHull ℝ ({w T₁, S b, X} : Set (ℝ × ℝ)) ⊆ P :=
    hP.triangle_enclosure (w T₁) (hP.w_in_P T₁) (S b) (hP.s_in_P b) X hX_in_P
      hw1b hbX hw1X
  refine ⟨X, hX_seg1, hX_seg2, htri, fun z hz1 hz2 hz3 => ?_⟩
  have hX_coords : X.1 = (1 - t) * (w T₁).1 + t * (S a).1 ∧
                   X.2 = (1 - t) * (w T₁).2 + t * (S a).2 := by
    dsimp [X]; simp
  have hX_coords2 : X.1 = (1 - s) * (w T₂).1 + s * (S b).1 ∧
                    X.2 = (1 - s) * (w T₂).2 + s * (S b).2 := by
    have hx1 := congrArg Prod.fst hXeq
    have hx2 := congrArg Prod.snd hXeq
    dsimp [X]; simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at hx1 hx2 ⊢
    exact ⟨hx1, hx2⟩
  have hor_w1_b_X : orient2D (w T₁) (S b) X = t * orient2D (w T₁) (S b) (S a) := by
    unfold orient2D; rw [hX_coords.1, hX_coords.2]; ring
  have hor_w1_b_a_ne : orient2D (w T₁) (S b) (S a) ≠ 0 := by
    have := (orient2D_ne_zero_of_mul_neg hcross.1).2
    intro h0; apply this; rw [orient2D_swap23, h0, neg_zero]
  have hor_tri_ne : orient2D (w T₁) (S b) X ≠ 0 := by
    rw [hor_w1_b_X]; exact mul_ne_zero (ne_of_gt ht0) hor_w1_b_a_ne
  have hs1' : SameSide (w T₁) (S b) z X := by
    unfold SameSide at hz3 ⊢
    rw [hor_w1_b_X]
    have : orient2D (w T₁) (S b) z * (t * orient2D (w T₁) (S b) (S a)) =
        t * (orient2D (w T₁) (S b) z * orient2D (w T₁) (S b) (S a)) := by ring
    rw [this]; exact mul_pos ht0 hz3
  have hs2' : SameSide (S b) X z (w T₁) := by
    have hid : ∀ p : ℝ × ℝ, orient2D (S b) X p = (1 - s) * orient2D (S b) (w T₂) p := by
      intro p; unfold orient2D; rw [hX_coords2.1, hX_coords2.2]; ring
    unfold SameSide at hz2 ⊢
    rw [hid z, hid (w T₁)]
    have h1s : 0 < 1 - s := sub_pos.mpr hs1
    have hswap : ∀ p : ℝ × ℝ, orient2D (S b) (w T₂) p = -orient2D (w T₂) (S b) p := by
      intro p; unfold orient2D; ring
    rw [hswap z, hswap (w T₁)]
    have : (1 - s) * -orient2D (w T₂) (S b) z * ((1 - s) * -orient2D (w T₂) (S b) (w T₁)) =
        (1 - s) ^ 2 * (orient2D (w T₂) (S b) z * orient2D (w T₂) (S b) (w T₁)) := by ring
    rw [this]; exact mul_pos (sq_pos_of_pos h1s) hz2
  have hs3' : SameSide X (w T₁) z (S b) := by
    have hid : ∀ p : ℝ × ℝ, orient2D X (w T₁) p = t * orient2D (S a) (w T₁) p := by
      intro p; unfold orient2D; rw [hX_coords.1, hX_coords.2]; ring
    unfold SameSide at hz1 ⊢
    rw [hid z, hid (S b)]
    have hswap : ∀ p : ℝ × ℝ, orient2D (S a) (w T₁) p = -orient2D (w T₁) (S a) p := by
      intro p; unfold orient2D; ring
    rw [hswap z, hswap (S b)]
    have : t * -orient2D (w T₁) (S a) z * (t * -orient2D (w T₁) (S a) (S b)) =
        t ^ 2 * (orient2D (w T₁) (S a) z * orient2D (w T₁) (S a) (S b)) := by ring
    rw [this]; exact mul_pos (sq_pos_of_pos ht0) hz1
  have hopen : InOpenTri (w T₁) (S b) X z := inOpenTri_of_sameSide hor_tri_ne hs1' hs2' hs3'
  have hz_hull : z ∈ convexHull ℝ ({w T₁, S b, X} : Set (ℝ × ℝ)) := inOpenTri_mem_convexHull hopen
  exact ⟨hopen, htri hz_hull, sees_of_mem_convexHull_tri htri hz_hull mem_convexHull_tri_mid⟩

/-- **Rule `T2` (`crossed_segment_tri_T2`)**: If `w T₂` sees `S b, S c` (`b ≠ c`), `w T₁` sees `S a`,
    and `[w T₁, S a]` properly crosses both `[w T₂, S b]` at `Xb` and `[w T₂, S c]` at `Xc`,
    then `conv {w T₂, Xb, Xc} ⊆ P`. Moreover, any point `z` satisfying the three `SameSide`
    chirotope tests of `T2` lies in `InOpenTri (w T₂) Xb Xc`, hence `z ∈ P`. -/
theorem crossed_segment_tri_T2 {n : ℕ} {P : Set (ℝ × ℝ)}
    {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ}
    (hP : ShatteredSimplePolygon P S w)
    {a b c : Fin n} (hbc : b ≠ c) {T₁ T₂ : Finset (Fin n)}
    (ha1 : a ∈ T₁) (hb2 : b ∈ T₂) (hc2 : c ∈ T₂)
    (hcross_b : ProperCross (w T₁) (S a) (w T₂) (S b))
    (hcross_c : ProperCross (w T₁) (S a) (w T₂) (S c)) :
    ∃ Xb Xc : ℝ × ℝ,
      Xb ∈ segment ℝ (w T₁) (S a) ∧ Xb ∈ segment ℝ (w T₂) (S b) ∧
      Xc ∈ segment ℝ (w T₁) (S a) ∧ Xc ∈ segment ℝ (w T₂) (S c) ∧
      convexHull ℝ ({w T₂, Xb, Xc} : Set (ℝ × ℝ)) ⊆ P ∧
      (∀ z : ℝ × ℝ,
        SameSide (w T₁) (S a) z (w T₂) →
        SameSide (w T₂) (S b) z (S c) →
        SameSide (w T₂) (S c) z (S b) →
        InOpenTri (w T₂) Xb Xc z ∧ z ∈ P) := by
  obtain ⟨tb, sb, htb0, htb1, hsb0, hsb1, hXbeq⟩ := properCross_exists_intersection hcross_b
  obtain ⟨tc, sc, htc0, htc1, hsc0, hsc1, hXceq⟩ := properCross_exists_intersection hcross_c
  let Xb : ℝ × ℝ := (1 - tb) • w T₁ + tb • S a
  let Xc : ℝ × ℝ := (1 - tc) • w T₁ + tc • S a
  have hXb_seg1 : Xb ∈ segment ℝ (w T₁) (S a) := by
    rw [segment_eq_image]
    exact ⟨tb, ⟨le_of_lt htb0, le_of_lt htb1⟩, by ext <;> simp [Xb, smul_eq_mul]⟩
  have hXb_seg2 : Xb ∈ segment ℝ (w T₂) (S b) := by
    dsimp [Xb]; rw [hXbeq, segment_eq_image]
    exact ⟨sb, ⟨le_of_lt hsb0, le_of_lt hsb1⟩, by ext <;> simp [smul_eq_mul]⟩
  have hXc_seg1 : Xc ∈ segment ℝ (w T₁) (S a) := by
    rw [segment_eq_image]
    exact ⟨tc, ⟨le_of_lt htc0, le_of_lt htc1⟩, by ext <;> simp [Xc, smul_eq_mul]⟩
  have hXc_seg2 : Xc ∈ segment ℝ (w T₂) (S c) := by
    dsimp [Xc]; rw [hXceq, segment_eq_image]
    exact ⟨sc, ⟨le_of_lt hsc0, le_of_lt hsc1⟩, by ext <;> simp [smul_eq_mul]⟩
  have hw1a : Sees P (w T₁) (S a) := (hP.shatters T₁ a).mpr ha1
  have hw2b : Sees P (w T₂) (S b) := (hP.shatters T₂ b).mpr hb2
  have hw2c : Sees P (w T₂) (S c) := (hP.shatters T₂ c).mpr hc2
  have hw2Xb : Sees P (w T₂) Xb := sees_of_mem_segment_left hw2b hXb_seg2
  have hw2Xc : Sees P (w T₂) Xc := sees_of_mem_segment_left hw2c hXc_seg2
  have hXbXc : Sees P Xb Xc := sees_of_subsegment_ends hw1a hXb_seg1 hXc_seg1
  have htri : convexHull ℝ ({w T₂, Xb, Xc} : Set (ℝ × ℝ)) ⊆ P :=
    hP.triangle_enclosure (w T₂) (hP.w_in_P T₂) Xb (sees_mem_right hw2Xb) Xc (sees_mem_right hw2Xc)
      hw2Xb hXbXc hw2Xc
  refine ⟨Xb, Xc, hXb_seg1, hXb_seg2, hXc_seg1, hXc_seg2, htri, fun z hz1 hz2 hz3 => ?_⟩
  have hXb_c1 : Xb.1 = (1 - tb) * (w T₁).1 + tb * (S a).1 ∧
               Xb.2 = (1 - tb) * (w T₁).2 + tb * (S a).2 := by
    dsimp [Xb]; simp
  have hXc_c1 : Xc.1 = (1 - tc) * (w T₁).1 + tc * (S a).1 ∧
               Xc.2 = (1 - tc) * (w T₁).2 + tc * (S a).2 := by
    dsimp [Xc]; simp
  have hXb_c2 : Xb.1 = (1 - sb) * (w T₂).1 + sb * (S b).1 ∧
               Xb.2 = (1 - sb) * (w T₂).2 + sb * (S b).2 := by
    have hx1 := congrArg Prod.fst hXbeq
    have hx2 := congrArg Prod.snd hXbeq
    dsimp [Xb]; simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at hx1 hx2 ⊢
    exact ⟨hx1, hx2⟩
  have hXc_c2 : Xc.1 = (1 - sc) * (w T₂).1 + sc * (S c).1 ∧
               Xc.2 = (1 - sc) * (w T₂).2 + sc * (S c).2 := by
    have hx1 := congrArg Prod.fst hXceq
    have hx2 := congrArg Prod.snd hXceq
    dsimp [Xc]; simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at hx1 hx2 ⊢
    exact ⟨hx1, hx2⟩
  have hor_w2bc_ne : orient2D (w T₂) (S b) (S c) ≠ 0 :=
    hP.no_three_collinear (w T₂) (S b) (S c)
      (Or.inr ⟨T₂, rfl⟩) (Or.inl ⟨b, rfl⟩) (Or.inl ⟨c, rfl⟩)
      (hP.s_ne_w b T₂).symm (fun h => hbc (hP.s_inj h)) (hP.s_ne_w c T₂).symm
  have hor_w2XbXc : orient2D (w T₂) Xb Xc = sb * sc * orient2D (w T₂) (S b) (S c) := by
    unfold orient2D; rw [hXb_c2.1, hXb_c2.2, hXc_c2.1, hXc_c2.2]; ring
  have hor_tri_ne : orient2D (w T₂) Xb Xc ≠ 0 := by
    rw [hor_w2XbXc]
    exact mul_ne_zero (mul_ne_zero (ne_of_gt hsb0) (ne_of_gt hsc0)) hor_w2bc_ne
  have htb_ne_tc : tb - tc ≠ 0 := by
    intro h0
    have hteq : tb = tc := sub_eq_zero.mp h0
    have hX_same : Xb = Xc := by dsimp [Xb, Xc]; rw [hteq]
    have hor0 : orient2D (w T₂) Xb Xc = 0 := by rw [hX_same, orient2D_self_right]
    exact hor_tri_ne hor0
  have hs1' : SameSide (w T₂) Xb z Xc := by
    have hz_id : orient2D (w T₂) Xb z = sb * orient2D (w T₂) (S b) z := by
      unfold orient2D; rw [hXb_c2.1, hXb_c2.2]; ring
    have hXc_id : orient2D (w T₂) Xb Xc = sb * sc * orient2D (w T₂) (S b) (S c) := hor_w2XbXc
    unfold SameSide at hz2 ⊢
    rw [hz_id, hXc_id]
    have : sb * orient2D (w T₂) (S b) z * (sb * sc * orient2D (w T₂) (S b) (S c)) =
        (sb ^ 2 * sc) * (orient2D (w T₂) (S b) z * orient2D (w T₂) (S b) (S c)) := by ring
    rw [this]; exact mul_pos (mul_pos (sq_pos_of_pos hsb0) hsc0) hz2
  have hs2' : SameSide Xb Xc z (w T₂) := by
    have hid : ∀ p : ℝ × ℝ, orient2D Xb Xc p = (tc - tb) * orient2D (w T₁) (S a) p := by
      intro p; unfold orient2D; rw [hXb_c1.1, hXb_c1.2, hXc_c1.1, hXc_c1.2]; ring
    unfold SameSide at hz1 ⊢
    rw [hid z, hid (w T₂)]
    have hsq : 0 < (tc - tb) ^ 2 := sq_pos_of_ne_zero (fun h0 => htb_ne_tc (by linarith))
    have : (tc - tb) * orient2D (w T₁) (S a) z * ((tc - tb) * orient2D (w T₁) (S a) (w T₂)) =
        (tc - tb) ^ 2 * (orient2D (w T₁) (S a) z * orient2D (w T₁) (S a) (w T₂)) := by ring
    rw [this]; exact mul_pos hsq hz1
  have hs3' : SameSide Xc (w T₂) z Xb := by
    have hz_id : orient2D Xc (w T₂) z = -sc * orient2D (w T₂) (S c) z := by
      unfold orient2D; rw [hXc_c2.1, hXc_c2.2]; ring
    have hXb_id : orient2D Xc (w T₂) Xb = -sc * sb * orient2D (w T₂) (S c) (S b) := by
      unfold orient2D; rw [hXb_c2.1, hXb_c2.2, hXc_c2.1, hXc_c2.2]; ring
    unfold SameSide at hz3 ⊢
    rw [hz_id, hXb_id]
    have : -sc * orient2D (w T₂) (S c) z * (-sc * sb * orient2D (w T₂) (S c) (S b)) =
        (sc ^ 2 * sb) * (orient2D (w T₂) (S c) z * orient2D (w T₂) (S c) (S b)) := by ring
    rw [this]; exact mul_pos (mul_pos (sq_pos_of_pos hsc0) hsb0) hz3
  have hopen : InOpenTri (w T₂) Xb Xc z := inOpenTri_of_sameSide hor_tri_ne hs1' hs2' hs3'
  exact ⟨hopen, htri (inOpenTri_mem_convexHull hopen)⟩


/-! ## 3. Convex Quadrilateral `N1` & Reflex-Dart Star-Kernel Enclosure -/

/-- Any 4-cycle `(p₀, p₁, p₂, p₃)` in `P` forming a strictly convex CCW quadrilateral encloses
    both triangles `(p₀, p₁, p₂)` and `(p₀, p₂, p₃)` and the entire `conv {p₀, p₁, p₂, p₃}`. -/
lemma convex_quad_enclosure_ccw {P : Set (ℝ × ℝ)} (hEnc : EnclosureDomain P)
    {p₀ p₁ p₂ p₃ : ℝ × ℝ}
    (h01 : Sees P p₀ p₁) (h12 : Sees P p₁ p₂) (h23 : Sees P p₂ p₃) (h30 : Sees P p₃ p₀)
    (hccw : StrictConvexCCWQuad p₀ p₁ p₂ p₃) :
    Sees P p₀ p₂ ∧ convexHull ℝ ({p₀, p₁, p₂, p₃} : Set (ℝ × ℝ)) ⊆ P := by
  rcases hccw with ⟨h012, h123, h230, h301⟩
  have hne02 : p₀ ≠ p₂ := by
    intro heq; subst heq; rw [orient2D_self_outer] at h012; exact lt_irrefl 0 h012
  have h021 : orient2D p₀ p₂ p₁ < 0 := by rw [orient2D_swap23]; linarith
  have h023 : 0 < orient2D p₀ p₂ p₃ := by rw [← orient2D_cycle]; exact h230
  have hp1 : IsPolygonalPathIn P p₀ p₂ [p₀, p₁, p₂] := isPolygonalPathIn_three h01 h12
  have hp2 : IsPolygonalPathIn P p₀ p₂ [p₀, p₃, p₂] :=
    isPolygonalPathIn_three (sees_symm h30) (sees_symm h23)
  have h02 : Sees P p₀ p₂ :=
    two_path_enclosure_either hEnc hne02 hp1 hp2
      (Or.inr ⟨interiorOnRight_three h021, interiorOnLeft_three h023⟩)
  have htri1 : convexHull ℝ ({p₀, p₁, p₂} : Set (ℝ × ℝ)) ⊆ P :=
    hEnc.triangle_enclosure p₀ (sees_mem_left h01) p₁ (sees_mem_right h01) p₂ (sees_mem_right h12)
      h01 h12 h02
  have htri2 : convexHull ℝ ({p₀, p₂, p₃} : Set (ℝ × ℝ)) ⊆ P :=
    hEnc.triangle_enclosure p₀ (sees_mem_left h01) p₂ (sees_mem_right h12) p₃ (sees_mem_left h30)
      h02 h23 (sees_symm h30)
  refine ⟨h02, fun z hz => ?_⟩
  have hhalf : ∀ a b : ℝ × ℝ,
      0 ≤ orient2D a b p₀ → 0 ≤ orient2D a b p₁ →
      0 ≤ orient2D a b p₂ → 0 ≤ orient2D a b p₃ →
      0 ≤ orient2D a b z := by
    intro a b h₀ h₁ h₂ h₃
    rw [mem_convexHull_iff_exists_fintype] at hz
    rcases hz with ⟨ι, _, μ, pts, hμ_nn, hμ_sum, hpts_mem, hz_eq⟩
    have hfst : ∀ t : Finset ι, (∑ i ∈ t, μ i • pts i).1 = ∑ i ∈ t, μ i * (pts i).1 := by
      intro t; induction t using Finset.induction_on with
      | empty => simp
      | @insert x s hx ih => simp [Finset.sum_insert hx, ih, smul_eq_mul]
    have hsnd : ∀ t : Finset ι, (∑ i ∈ t, μ i • pts i).2 = ∑ i ∈ t, μ i * (pts i).2 := by
      intro t; induction t using Finset.induction_on with
      | empty => simp
      | @insert x s hx ih => simp [Finset.sum_insert hx, ih, smul_eq_mul]
    have hsum1 : (∑ i : ι, μ i * (pts i).1) = z.1 := by
      rw [← hfst Finset.univ]; exact congrArg Prod.fst hz_eq
    have hsum2 : (∑ i : ι, μ i * (pts i).2) = z.2 := by
      rw [← hsnd Finset.univ]; exact congrArg Prod.snd hz_eq
    have hid : orient2D a b z = ∑ i : ι, μ i * orient2D a b (pts i) := by
      have hterm : ∀ i : ι, μ i * orient2D a b (pts i) =
          (b.1 - a.1) * (μ i * (pts i).2) - (b.2 - a.2) * (μ i * (pts i).1) -
          μ i * ((b.1 - a.1) * a.2 - (b.2 - a.2) * a.1) := fun i => by
        unfold orient2D; ring
      simp_rw [hterm, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_mul,
        hsum1, hsum2, hμ_sum, one_mul]
      unfold orient2D; ring
    rw [hid]
    refine Finset.sum_nonneg (fun i _ => mul_nonneg (hμ_nn i) ?_)
    have hm := hpts_mem i
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hm
    rcases hm with rfl | rfl | rfl | rfl <;> assumption
  have h01z : 0 ≤ orient2D p₀ p₁ z :=
    hhalf p₀ p₁
      (by unfold orient2D; linarith)
      (by unfold orient2D; linarith)
      (le_of_lt h012)
      (by rw [show orient2D p₀ p₁ p₃ = orient2D p₃ p₀ p₁ by unfold orient2D; ring]; exact le_of_lt h301)
  have h12z : 0 ≤ orient2D p₁ p₂ z :=
    hhalf p₁ p₂
      (by rw [show orient2D p₁ p₂ p₀ = orient2D p₀ p₁ p₂ by unfold orient2D; ring]; exact le_of_lt h012)
      (by unfold orient2D; linarith)
      (by unfold orient2D; linarith)
      (le_of_lt h123)
  have h23z : 0 ≤ orient2D p₂ p₃ z :=
    hhalf p₂ p₃
      (le_of_lt h230)
      (by rw [show orient2D p₂ p₃ p₁ = orient2D p₁ p₂ p₃ by unfold orient2D; ring]; exact le_of_lt h123)
      (by unfold orient2D; linarith)
      (by unfold orient2D; linarith)
  have h30z : 0 ≤ orient2D p₃ p₀ z :=
    hhalf p₃ p₀
      (by unfold orient2D; linarith)
      (le_of_lt h301)
      (by rw [show orient2D p₃ p₀ p₂ = orient2D p₂ p₃ p₀ by unfold orient2D; ring]; exact le_of_lt h230)
      (by unfold orient2D; linarith)
  rcases le_total 0 (orient2D p₀ p₂ z) with hdiag | hdiag
  · apply htri2
    rw [← inClosedTri_iff_mem_convexHull]
    exact inClosedTri_of_orient_nonneg h023 hdiag h23z (by rw [← orient2D_cycle, orient2D_cycle]; exact h30z)
  · apply htri1
    rw [← inClosedTri_iff_mem_convexHull]
    have h20z : 0 ≤ orient2D p₂ p₀ z := by
      rw [show orient2D p₂ p₀ z = -orient2D p₀ p₂ z by unfold orient2D; ring]
      linarith
    exact inClosedTri_of_orient_nonneg h012 h01z h12z h20z

/-- **Rule `N1` Convex Quadrilateral Enclosure (`convex_quad_vertex_enclosure_N1`)**:
    If `w T₁, w T₂` both see `S a, S b` (`a ≠ b`) and `(w T₁, S a, w T₂, S b)` forms a strictly
    convex quadrilateral, then `conv {w T₁, S a, w T₂, S b} ⊆ P`. Consequently, any point
    `z ∈ conv {w T₁, S a, w T₂, S b}` sees `S a` and `S b` (so `w T₃ ∈ conv Q` forces `a, b ∈ T₃`). -/
theorem convex_quad_vertex_enclosure_N1 {n : ℕ} {P : Set (ℝ × ℝ)}
    {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ}
    (hP : ShatteredSimplePolygon P S w)
    {a b : Fin n} {T₁ T₂ : Finset (Fin n)}
    (ha1 : a ∈ T₁) (hb1 : b ∈ T₁) (ha2 : a ∈ T₂) (hb2 : b ∈ T₂)
    (hquad : StrictConvexQuad (w T₁) (S a) (w T₂) (S b)) :
    convexHull ℝ ({w T₁, S a, w T₂, S b} : Set (ℝ × ℝ)) ⊆ P ∧
    (∀ z ∈ convexHull ℝ ({w T₁, S a, w T₂, S b} : Set (ℝ × ℝ)),
      Sees P z (S a) ∧ Sees P z (S b)) := by
  have h1a : Sees P (w T₁) (S a) := (hP.shatters T₁ a).mpr ha1
  have h1b : Sees P (w T₁) (S b) := (hP.shatters T₁ b).mpr hb1
  have h2a : Sees P (w T₂) (S a) := (hP.shatters T₂ a).mpr ha2
  have h2b : Sees P (w T₂) (S b) := (hP.shatters T₂ b).mpr hb2
  have hsub : convexHull ℝ ({w T₁, S a, w T₂, S b} : Set (ℝ × ℝ)) ⊆ P := by
    rcases hquad with hccw | hcw
    · exact (convex_quad_enclosure_ccw hP.toEnclosureDomain h1a (sees_symm h2a) h2b (sees_symm h1b) hccw).2
    · have hsub' := (convex_quad_enclosure_ccw hP.toEnclosureDomain (sees_symm h2b) h2a (sees_symm h1a) h1b hcw).2
      intro z hz
      apply hsub'
      have hset : ({w T₁, S a, w T₂, S b} : Set (ℝ × ℝ)) = {S b, w T₂, S a, w T₁} := by
        ext x; simp [or_comm, or_left_comm]
      rw [← hset]; exact hz
  refine ⟨hsub, fun z hz => ⟨?_, ?_⟩⟩
  · have ha_mem : S a ∈ convexHull ℝ ({w T₁, S a, w T₂, S b} : Set (ℝ × ℝ)) :=
      subset_convexHull ℝ _ (by simp)
    exact ((convex_convexHull ℝ _).segment_subset hz ha_mem).trans hsub
  · have hb_mem : S b ∈ convexHull ℝ ({w T₁, S a, w T₂, S b} : Set (ℝ × ℝ)) :=
      subset_convexHull ℝ _ (by simp)
    exact ((convex_convexHull ℝ _).segment_subset hz hb_mem).trans hsub

/-- General Reflex-Dart Star-Kernel Enclosure for any 4-cycle `(v_r, v_p, v_q, v_s)` in `P`
    with `v_r ∈ int tri(v_p, v_q, v_s)`. -/
lemma dart_star_kernel_of_4cycle {P : Set (ℝ × ℝ)} (hEnc : EnclosureDomain P)
    {vr vp vq vs : ℝ × ℝ}
    (hrp : Sees P vr vp) (hpq : Sees P vp vq) (hqs : Sees P vq vs) (hsr : Sees P vs vr)
    (h_dart : InOpenTri vp vq vs vr) (h_nondeg : orient2D vp vq vs ≠ 0) :
    Sees P vr vq ∧
    convexHull ℝ ({vr, vp, vq} : Set (ℝ × ℝ)) ⊆ P ∧
    convexHull ℝ ({vr, vq, vs} : Set (ℝ × ℝ)) ⊆ P ∧
    (∀ z : ℝ × ℝ,
      (z ∈ convexHull ℝ ({vr, vp, vq} : Set (ℝ × ℝ)) ∨
       z ∈ convexHull ℝ ({vr, vq, vs} : Set (ℝ × ℝ))) →
      Sees P z vr ∧ Sees P z vq) ∧
    (∀ z : ℝ × ℝ,
      z ∈ convexHull ℝ ({vp, vq, vs} : Set (ℝ × ℝ)) →
      0 ≤ orient2D vr vp z * orient2D vr vp vq →
      (z ∈ convexHull ℝ ({vr, vp, vq} : Set (ℝ × ℝ)) ∨
       z ∈ convexHull ℝ ({vr, vq, vs} : Set (ℝ × ℝ))) ∧ Sees P z vp) ∧
    (∀ z : ℝ × ℝ,
      z ∈ convexHull ℝ ({vp, vq, vs} : Set (ℝ × ℝ)) →
      0 ≤ orient2D vr vs z * orient2D vr vs vq →
      (z ∈ convexHull ℝ ({vr, vp, vq} : Set (ℝ × ℝ)) ∨
       z ∈ convexHull ℝ ({vr, vq, vs} : Set (ℝ × ℝ))) ∧ Sees P z vs) := by
  rcases h_dart with ⟨μ₁, μ₂, μ₃, hμ1, hμ2, hμ3, hμsum, hvr1, hvr2⟩
  have hμ1_eq : μ₁ = 1 - μ₂ - μ₃ := by linarith
  have hvr_ne_vq : vr ≠ vq := by
    intro heq
    have h1 : orient2D vr vp vs = μ₂ * -orient2D vp vq vs := by
      unfold orient2D; rw [hvr1, hvr2, hμ1_eq]; ring
    have h2 : orient2D vq vp vs = -orient2D vp vq vs := by unfold orient2D; ring
    rw [heq] at h1
    have h3 : (1 - μ₂) * orient2D vp vq vs = 0 := by linarith
    rcases mul_eq_zero.mp h3 with hm | ho
    · linarith
    · exact h_nondeg ho
  have hor_rq_p : orient2D vr vq vp = -μ₃ * orient2D vp vq vs := by
    unfold orient2D; rw [hvr1, hvr2, hμ1_eq]; ring
  have hor_rq_s : orient2D vr vq vs = μ₁ * orient2D vp vq vs := by
    unfold orient2D; rw [hvr1, hvr2, hμ1_eq]; ring
  have hp1 : IsPolygonalPathIn P vr vq [vr, vp, vq] := isPolygonalPathIn_three hrp hpq
  have hp2 : IsPolygonalPathIn P vr vq [vr, vs, vq] :=
    isPolygonalPathIn_three (sees_symm hsr) (sees_symm hqs)
  have hsides_rq :
      (InteriorOnLeft vr vq [vr, vp, vq] ∧ InteriorOnRight vr vq [vr, vs, vq]) ∨
      (InteriorOnRight vr vq [vr, vp, vq] ∧ InteriorOnLeft vr vq [vr, vs, vq]) := by
    rcases lt_or_gt_of_ne h_nondeg with hneg | hpos
    · left
      refine ⟨interiorOnLeft_three (by rw [hor_rq_p]; nlinarith),
              interiorOnRight_three (by rw [hor_rq_s]; nlinarith)⟩
    · right
      refine ⟨interiorOnRight_three (by rw [hor_rq_p]; nlinarith),
              interiorOnLeft_three (by rw [hor_rq_s]; nlinarith)⟩
  have hrq : Sees P vr vq :=
    two_path_enclosure_either hEnc hvr_ne_vq hp1 hp2 hsides_rq
  have htri_rpq : convexHull ℝ ({vr, vp, vq} : Set (ℝ × ℝ)) ⊆ P :=
    hEnc.triangle_enclosure vr (sees_mem_left hrp) vp (sees_mem_right hrp) vq (sees_mem_right hpq)
      hrp hpq hrq
  have htri_rqs : convexHull ℝ ({vr, vq, vs} : Set (ℝ × ℝ)) ⊆ P :=
    hEnc.triangle_enclosure vr (sees_mem_left hrp) vq (sees_mem_right hpq) vs (sees_mem_right hqs)
      hrq hqs (sees_symm hsr)
  have h_union_sees_rq : ∀ z : ℝ × ℝ,
      (z ∈ convexHull ℝ ({vr, vp, vq} : Set (ℝ × ℝ)) ∨
       z ∈ convexHull ℝ ({vr, vq, vs} : Set (ℝ × ℝ))) →
      Sees P z vr ∧ Sees P z vq := by
    rintro z (hz1 | hz2)
    · exact ⟨sees_of_mem_convexHull_tri htri_rpq hz1 mem_convexHull_tri_left,
             sees_of_mem_convexHull_tri htri_rpq hz1 mem_convexHull_tri_right⟩
    · exact ⟨sees_of_mem_convexHull_tri htri_rqs hz2 mem_convexHull_tri_left,
             sees_of_mem_convexHull_tri htri_rqs hz2 mem_convexHull_tri_mid⟩
  have hor_rp_q : orient2D vr vp vq = μ₃ * orient2D vp vq vs := by
    unfold orient2D; rw [hvr1, hvr2, hμ1_eq]; ring
  have hor_rs_q : orient2D vr vs vq = -μ₁ * orient2D vp vq vs := by
    unfold orient2D; rw [hvr1, hvr2, hμ1_eq]; ring
  have hor_rpq_ne : orient2D vr vp vq ≠ 0 := by
    rw [hor_rp_q]; exact mul_ne_zero (ne_of_gt hμ3) h_nondeg
  have hor_rqs_ne : orient2D vr vq vs ≠ 0 := by
    rw [hor_rq_s]; exact mul_ne_zero (ne_of_gt hμ1) h_nondeg
  have h_split_vp : ∀ z : ℝ × ℝ,
      z ∈ convexHull ℝ ({vp, vq, vs} : Set (ℝ × ℝ)) →
      0 ≤ orient2D vr vp z * orient2D vr vp vq →
      z ∈ convexHull ℝ ({vr, vp, vq} : Set (ℝ × ℝ)) ∨
      z ∈ convexHull ℝ ({vr, vq, vs} : Set (ℝ × ℝ)) := by
    intro z hz hside
    rw [← inClosedTri_iff_mem_convexHull] at hz
    rcases hz with ⟨ν₁, ν₂, ν₃, hν1, hν2, hν3, hνsum, hz1, hz2⟩
    set D := orient2D vp vq vs
    have hDsq : 0 < D ^ 2 := sq_pos_of_ne_zero h_nondeg
    have h_rp_z : orient2D vr vp z = (μ₃ * ν₂ - μ₂ * ν₃) * D := by
      dsimp [D]; unfold orient2D; rw [hvr1, hvr2, hz1, hz2, hμ1_eq, show ν₁ = 1 - ν₂ - ν₃ by linarith]; ring
    have h_rq_z : orient2D vr vq z = (μ₁ * ν₃ - μ₃ * ν₁) * D := by
      dsimp [D]; unfold orient2D; rw [hvr1, hvr2, hz1, hz2, hμ1_eq, show ν₁ = 1 - ν₂ - ν₃ by linarith]; ring
    have h_rs_z : orient2D vr vs z = (μ₂ * ν₁ - μ₁ * ν₂) * D := by
      dsimp [D]; unfold orient2D; rw [hvr1, hvr2, hz1, hz2, hμ1_eq, show ν₁ = 1 - ν₂ - ν₃ by linarith]; ring
    have h_pq_z : orient2D vp vq z = ν₃ * D := by
      dsimp [D]; unfold orient2D; rw [hz1, hz2, show ν₁ = 1 - ν₂ - ν₃ by linarith]; ring
    have h_qs_z : orient2D vq vs z = ν₁ * D := by
      dsimp [D]; unfold orient2D; rw [hz1, hz2, show ν₂ = 1 - ν₁ - ν₃ by linarith]; ring
    have h_mul : 0 ≤ (μ₃ * ν₂ - μ₂ * ν₃) * μ₃ * D ^ 2 := by
      have := hside; rw [h_rp_z, hor_rp_q] at this; dsimp [D] at this ⊢; linarith
    have hc_rp : 0 ≤ μ₃ * ν₂ - μ₂ * ν₃ := by
      by_contra hlt
      have hneg1 : (μ₃ * ν₂ - μ₂ * ν₃) * μ₃ < 0 := mul_neg_of_neg_of_pos (not_le.mp hlt) hμ3
      have hneg2 : (μ₃ * ν₂ - μ₂ * ν₃) * μ₃ * D ^ 2 < 0 := mul_neg_of_neg_of_pos hneg1 hDsq
      linarith
    rcases le_total (μ₁ * ν₃ - μ₃ * ν₁) 0 with hrq_le | hrq_ge
    · left
      refine mem_convexHull_tri_of_orient_same hor_rpq_ne ?_ ?_ ?_
      · rw [h_rp_z, hor_rp_q]; dsimp [D]
        have : (μ₃ * ν₂ - μ₂ * ν₃) * D * (μ₃ * D) = (μ₃ * ν₂ - μ₂ * ν₃) * μ₃ * D ^ 2 := by ring
        rw [this]; exact mul_nonneg (mul_nonneg hc_rp (le_of_lt hμ3)) (le_of_lt hDsq)
      · rw [show orient2D vp vq vr = orient2D vr vp vq by unfold orient2D; ring, hor_rp_q, h_pq_z]; dsimp [D]
        have : ν₃ * D * (μ₃ * D) = ν₃ * μ₃ * D ^ 2 := by ring
        rw [this]; exact mul_nonneg (mul_nonneg hν3 (le_of_lt hμ3)) (le_of_lt hDsq)
      · rw [show orient2D vq vr z = -orient2D vr vq z by unfold orient2D; ring,
            show orient2D vq vr vp = orient2D vr vp vq by unfold orient2D; ring, hor_rp_q, h_rq_z]; dsimp [D]
        have : -((μ₁ * ν₃ - μ₃ * ν₁) * D) * (μ₃ * D) = (-(μ₁ * ν₃ - μ₃ * ν₁)) * μ₃ * D ^ 2 := by ring
        rw [this]; exact mul_nonneg (mul_nonneg (neg_nonneg.mpr hrq_le) (le_of_lt hμ3)) (le_of_lt hDsq)
    · right
      have hbal : μ₁ * (μ₃ * ν₂ - μ₂ * ν₃) + μ₂ * (μ₁ * ν₃ - μ₃ * ν₁) + μ₃ * (μ₂ * ν₁ - μ₁ * ν₂) = 0 := by
        ring
      have hsum_nonneg : 0 ≤ μ₁ * (μ₃ * ν₂ - μ₂ * ν₃) + μ₂ * (μ₁ * ν₃ - μ₃ * ν₁) :=
        add_nonneg (mul_nonneg (le_of_lt hμ1) hc_rp) (mul_nonneg (le_of_lt hμ2) hrq_ge)
      have hc_rs : μ₂ * ν₁ - μ₁ * ν₂ ≤ 0 := by
        by_contra hlt
        have hpos : 0 < μ₃ * (μ₂ * ν₁ - μ₁ * ν₂) := mul_pos hμ3 (not_le.mp hlt)
        linarith
      refine mem_convexHull_tri_of_orient_same hor_rqs_ne ?_ ?_ ?_
      · rw [h_rq_z, hor_rq_s]; dsimp [D]
        have : (μ₁ * ν₃ - μ₃ * ν₁) * D * (μ₁ * D) = (μ₁ * ν₃ - μ₃ * ν₁) * μ₁ * D ^ 2 := by ring
        rw [this]; exact mul_nonneg (mul_nonneg hrq_ge (le_of_lt hμ1)) (le_of_lt hDsq)
      · rw [show orient2D vq vs vr = orient2D vr vq vs by unfold orient2D; ring, hor_rq_s, h_qs_z]; dsimp [D]
        have : ν₁ * D * (μ₁ * D) = ν₁ * μ₁ * D ^ 2 := by ring
        rw [this]; exact mul_nonneg (mul_nonneg hν1 (le_of_lt hμ1)) (le_of_lt hDsq)
      · rw [show orient2D vs vr z = -orient2D vr vs z by unfold orient2D; ring,
            show orient2D vs vr vq = orient2D vr vq vs by unfold orient2D; ring, hor_rq_s, h_rs_z]; dsimp [D]
        have : -((μ₂ * ν₁ - μ₁ * ν₂) * D) * (μ₁ * D) = (-(μ₂ * ν₁ - μ₁ * ν₂)) * μ₁ * D ^ 2 := by ring
        rw [this]; exact mul_nonneg (mul_nonneg (neg_nonneg.mpr hc_rs) (le_of_lt hμ1)) (le_of_lt hDsq)
  have h_split_vs : ∀ z : ℝ × ℝ,
      z ∈ convexHull ℝ ({vp, vq, vs} : Set (ℝ × ℝ)) →
      0 ≤ orient2D vr vs z * orient2D vr vs vq →
      z ∈ convexHull ℝ ({vr, vp, vq} : Set (ℝ × ℝ)) ∨
      z ∈ convexHull ℝ ({vr, vq, vs} : Set (ℝ × ℝ)) := by
    intro z hz hside
    rw [← inClosedTri_iff_mem_convexHull] at hz
    rcases hz with ⟨ν₁, ν₂, ν₃, hν1, hν2, hν3, hνsum, hz1, hz2⟩
    set D := orient2D vp vq vs
    have hDsq : 0 < D ^ 2 := sq_pos_of_ne_zero h_nondeg
    have h_rp_z : orient2D vr vp z = (μ₃ * ν₂ - μ₂ * ν₃) * D := by
      dsimp [D]; unfold orient2D; rw [hvr1, hvr2, hz1, hz2, hμ1_eq, show ν₁ = 1 - ν₂ - ν₃ by linarith]; ring
    have h_rq_z : orient2D vr vq z = (μ₁ * ν₃ - μ₃ * ν₁) * D := by
      dsimp [D]; unfold orient2D; rw [hvr1, hvr2, hz1, hz2, hμ1_eq, show ν₁ = 1 - ν₂ - ν₃ by linarith]; ring
    have h_rs_z : orient2D vr vs z = (μ₂ * ν₁ - μ₁ * ν₂) * D := by
      dsimp [D]; unfold orient2D; rw [hvr1, hvr2, hz1, hz2, hμ1_eq, show ν₁ = 1 - ν₂ - ν₃ by linarith]; ring
    have h_pq_z : orient2D vp vq z = ν₃ * D := by
      dsimp [D]; unfold orient2D; rw [hz1, hz2, show ν₁ = 1 - ν₂ - ν₃ by linarith]; ring
    have h_qs_z : orient2D vq vs z = ν₁ * D := by
      dsimp [D]; unfold orient2D; rw [hz1, hz2, show ν₂ = 1 - ν₁ - ν₃ by linarith]; ring
    have h_mul : 0 ≤ -(μ₂ * ν₁ - μ₁ * ν₂) * μ₁ * D ^ 2 := by
      have := hside; rw [h_rs_z, hor_rs_q] at this; dsimp [D] at this ⊢; linarith
    have hc_rs : μ₂ * ν₁ - μ₁ * ν₂ ≤ 0 := by
      by_contra hlt
      have hneg1 : -(μ₂ * ν₁ - μ₁ * ν₂) * μ₁ < 0 := mul_neg_of_neg_of_pos (neg_lt_zero.mpr (not_le.mp hlt)) hμ1
      have hneg2 : -(μ₂ * ν₁ - μ₁ * ν₂) * μ₁ * D ^ 2 < 0 := mul_neg_of_neg_of_pos hneg1 hDsq
      linarith
    rcases le_total 0 (μ₁ * ν₃ - μ₃ * ν₁) with hrq_ge | hrq_le
    · right
      refine mem_convexHull_tri_of_orient_same hor_rqs_ne ?_ ?_ ?_
      · rw [h_rq_z, hor_rq_s]; dsimp [D]
        have : (μ₁ * ν₃ - μ₃ * ν₁) * D * (μ₁ * D) = (μ₁ * ν₃ - μ₃ * ν₁) * μ₁ * D ^ 2 := by ring
        rw [this]; exact mul_nonneg (mul_nonneg hrq_ge (le_of_lt hμ1)) (le_of_lt hDsq)
      · rw [show orient2D vq vs vr = orient2D vr vq vs by unfold orient2D; ring, hor_rq_s, h_qs_z]; dsimp [D]
        have : ν₁ * D * (μ₁ * D) = ν₁ * μ₁ * D ^ 2 := by ring
        rw [this]; exact mul_nonneg (mul_nonneg hν1 (le_of_lt hμ1)) (le_of_lt hDsq)
      · rw [show orient2D vs vr z = -orient2D vr vs z by unfold orient2D; ring,
            show orient2D vs vr vq = orient2D vr vq vs by unfold orient2D; ring, hor_rq_s, h_rs_z]; dsimp [D]
        have : -((μ₂ * ν₁ - μ₁ * ν₂) * D) * (μ₁ * D) = (-(μ₂ * ν₁ - μ₁ * ν₂)) * μ₁ * D ^ 2 := by ring
        rw [this]; exact mul_nonneg (mul_nonneg (neg_nonneg.mpr hc_rs) (le_of_lt hμ1)) (le_of_lt hDsq)
    · left
      have hbal : μ₁ * (μ₃ * ν₂ - μ₂ * ν₃) + μ₂ * (μ₁ * ν₃ - μ₃ * ν₁) + μ₃ * (μ₂ * ν₁ - μ₁ * ν₂) = 0 := by
        ring
      have hsum_nonpos : μ₂ * (μ₁ * ν₃ - μ₃ * ν₁) + μ₃ * (μ₂ * ν₁ - μ₁ * ν₂) ≤ 0 :=
        add_nonpos (mul_nonpos_of_nonneg_of_nonpos (le_of_lt hμ2) hrq_le) (mul_nonpos_of_nonneg_of_nonpos (le_of_lt hμ3) hc_rs)
      have hc_rp : 0 ≤ μ₃ * ν₂ - μ₂ * ν₃ := by
        by_contra hlt
        have hneg : μ₁ * (μ₃ * ν₂ - μ₂ * ν₃) < 0 := mul_neg_of_pos_of_neg hμ1 (not_le.mp hlt)
        linarith
      refine mem_convexHull_tri_of_orient_same hor_rpq_ne ?_ ?_ ?_
      · rw [h_rp_z, hor_rp_q]; dsimp [D]
        have : (μ₃ * ν₂ - μ₂ * ν₃) * D * (μ₃ * D) = (μ₃ * ν₂ - μ₂ * ν₃) * μ₃ * D ^ 2 := by ring
        rw [this]; exact mul_nonneg (mul_nonneg hc_rp (le_of_lt hμ3)) (le_of_lt hDsq)
      · rw [show orient2D vp vq vr = orient2D vr vp vq by unfold orient2D; ring, hor_rp_q, h_pq_z]; dsimp [D]
        have : ν₃ * D * (μ₃ * D) = ν₃ * μ₃ * D ^ 2 := by ring
        rw [this]; exact mul_nonneg (mul_nonneg hν3 (le_of_lt hμ3)) (le_of_lt hDsq)
      · rw [show orient2D vq vr z = -orient2D vr vq z by unfold orient2D; ring,
            show orient2D vq vr vp = orient2D vr vp vq by unfold orient2D; ring, hor_rp_q, h_rq_z]; dsimp [D]
        have : -((μ₁ * ν₃ - μ₃ * ν₁) * D) * (μ₃ * D) = (-(μ₁ * ν₃ - μ₃ * ν₁)) * μ₃ * D ^ 2 := by ring
        rw [this]; exact mul_nonneg (mul_nonneg (neg_nonneg.mpr hrq_le) (le_of_lt hμ3)) (le_of_lt hDsq)
  refine ⟨hrq, htri_rpq, htri_rqs, h_union_sees_rq, ?_, ?_⟩
  · intro z hz hside
    refine ⟨h_split_vp z hz hside, fun u hu => ?_⟩
    rw [segment_eq_image] at hu
    rcases hu with ⟨t, ⟨ht0, ht1⟩, rfl⟩
    have hu_tri : (1 - t) • z + t • vp ∈ convexHull ℝ ({vp, vq, vs} : Set (ℝ × ℝ)) :=
      (convex_convexHull ℝ _).segment_subset hz mem_convexHull_tri_left
        (by rw [segment_eq_image]; exact ⟨t, ⟨ht0, ht1⟩, rfl⟩)
    have hu_side : 0 ≤ orient2D vr vp ((1 - t) • z + t • vp) * orient2D vr vp vq := by
      have hid : orient2D vr vp ((1 - t) • z + t • vp) = (1 - t) * orient2D vr vp z := by
        rw [orient2D_affine_comb vr vp z vp _ t (by simp [smul_eq_mul]) (by simp [smul_eq_mul]),
          orient2D_self_right, mul_zero, add_zero]
      rw [hid]
      have : (1 - t) * orient2D vr vp z * orient2D vr vp vq =
          (1 - t) * (orient2D vr vp z * orient2D vr vp vq) := by ring
      rw [this]; exact mul_nonneg (sub_nonneg.mpr ht1) hside
    rcases h_split_vp _ hu_tri hu_side with h1 | h2
    · exact htri_rpq h1
    · exact htri_rqs h2
  · intro z hz hside
    refine ⟨h_split_vs z hz hside, fun u hu => ?_⟩
    rw [segment_eq_image] at hu
    rcases hu with ⟨t, ⟨ht0, ht1⟩, rfl⟩
    have hu_tri : (1 - t) • z + t • vs ∈ convexHull ℝ ({vp, vq, vs} : Set (ℝ × ℝ)) :=
      (convex_convexHull ℝ _).segment_subset hz mem_convexHull_tri_right
        (by rw [segment_eq_image]; exact ⟨t, ⟨ht0, ht1⟩, rfl⟩)
    have hu_side : 0 ≤ orient2D vr vs ((1 - t) • z + t • vs) * orient2D vr vs vq := by
      have hid : orient2D vr vs ((1 - t) • z + t • vs) = (1 - t) * orient2D vr vs z := by
        rw [orient2D_affine_comb vr vs z vs _ t (by simp [smul_eq_mul]) (by simp [smul_eq_mul]),
          orient2D_self_right, mul_zero, add_zero]
      rw [hid]
      have : (1 - t) * orient2D vr vs z * orient2D vr vs vq =
          (1 - t) * (orient2D vr vs z * orient2D vr vs vq) := by ring
      rw [this]; exact mul_nonneg (sub_nonneg.mpr ht1) hside
    rcases h_split_vs _ hu_tri hu_side with h1 | h2
    · exact htri_rpq h1
    · exact htri_rqs h2

/-- **Reflex-Dart Star-Kernel Enclosure (`dart_star_kernel_enclosure`)** over `ShatteredSimplePolygon P S w`:
    Whenever a visibility 4-cycle `(v_r, v_p, v_q, v_s)` in `P` (from `range S ∪ range w`)
    has `v_r ∈ int tri(v_p, v_q, v_s)`, the dart `tri(v_r, v_p, v_q) ∪ tri(v_r, v_q, v_s)`
    is enclosed in `P`, and every witness in the star-kernel from `v_r`, `v_q`, `v_p`, or `v_s`
    sees that vertex. -/
theorem dart_star_kernel_enclosure {n : ℕ} {P : Set (ℝ × ℝ)}
    {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ}
    (hP : ShatteredSimplePolygon P S w)
    {vr vp vq vs : ℝ × ℝ}
    (h_mem : vr ∈ Set.range S ∪ Set.range w ∧ vp ∈ Set.range S ∪ Set.range w ∧
             vq ∈ Set.range S ∪ Set.range w ∧ vs ∈ Set.range S ∪ Set.range w)
    (h_dist : vp ≠ vq ∧ vq ≠ vs ∧ vp ≠ vs)
    (hrp : Sees P vr vp) (hpq : Sees P vp vq) (hqs : Sees P vq vs) (hsr : Sees P vs vr)
    (h_dart : InOpenTri vp vq vs vr) :
    convexHull ℝ ({vr, vp, vq} : Set (ℝ × ℝ)) ⊆ P ∧
    convexHull ℝ ({vr, vq, vs} : Set (ℝ × ℝ)) ⊆ P ∧
    (∀ z : ℝ × ℝ,
      (z ∈ convexHull ℝ ({vr, vp, vq} : Set (ℝ × ℝ)) ∨
       z ∈ convexHull ℝ ({vr, vq, vs} : Set (ℝ × ℝ))) →
      Sees P z vr ∧ Sees P z vq) ∧
    (∀ z ∈ convexHull ℝ ({vp, vq, vs} : Set (ℝ × ℝ)),
      0 ≤ orient2D vr vp z * orient2D vr vp vq → Sees P z vp) ∧
    (∀ z ∈ convexHull ℝ ({vp, vq, vs} : Set (ℝ × ℝ)),
      0 ≤ orient2D vr vs z * orient2D vr vs vq → Sees P z vs) := by
  have h_nondeg : orient2D vp vq vs ≠ 0 :=
    hP.no_three_collinear vp vq vs h_mem.2.1 h_mem.2.2.1 h_mem.2.2.2
      h_dist.1 h_dist.2.1 h_dist.2.2
  obtain ⟨_, htri1, htri2, hrq, hvp, hvs⟩ :=
    dart_star_kernel_of_4cycle hP.toEnclosureDomain hrp hpq hqs hsr h_dart h_nondeg
  exact ⟨htri1, htri2, hrq, fun z hz hs => (hvp z hz hs).2, fun z hz hs => (hvs z hz hs).2⟩


/-! ## 4. Hereditary Shattered Subset Preservation (`(G1)-(G2)` without re-perturbation) -/

/-- General hereditary preservation along any injective re-indexing `ι : Fin m ↪ Fin n`:
    if `S` is shattered in `P` under `(G1)-(G2)`, then `S ∘ ι` with induced witness map
    `w' T' := w (T'.image ι)` satisfies `ShatteredSimplePolygon P (S ∘ ι) w'`. -/
theorem hereditary_shattered_emb {n m : ℕ} {P : Set (ℝ × ℝ)}
    {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ}
    (hP : ShatteredSimplePolygon P S w) (ι : Fin m ↪ Fin n) :
    ShatteredSimplePolygon P (S ∘ ι) (fun T' => w (T'.image ι)) where
  s_in_P i := hP.s_in_P (ι i)
  w_in_P T' := hP.w_in_P (T'.image ι)
  shatters T' i := by
    change Sees P (w (T'.image ι)) (S (ι i)) ↔ i ∈ T'
    rw [hP.shatters (T'.image ι) (ι i)]
    simp [Finset.mem_image, ι.injective.eq_iff]
  s_inj := hP.s_inj.comp ι.injective
  w_inj := hP.w_inj.comp (Finset.image_injective ι.injective)
  s_ne_w i T' := hP.s_ne_w (ι i) (T'.image ι)
  no_three_collinear p q r hp hq hr hpq hqr hpr := by
    have hsub : Set.range (S ∘ ι) ∪ Set.range (fun T' : Finset (Fin m) => w (T'.image ι)) ⊆
        Set.range S ∪ Set.range w := by
      rintro x (⟨i, rfl⟩ | ⟨T', rfl⟩)
      · exact Or.inl ⟨ι i, rfl⟩
      · exact Or.inr ⟨T'.image ι, rfl⟩
    exact hP.no_three_collinear p q r (hsub hp) (hsub hq) (hsub hr) hpq hqr hpr
  open_vis_nbhd T' hT' := by
    obtain ⟨ε, hε, hball⟩ := hP.open_vis_nbhd (T'.image ι) (Finset.image_nonempty.mpr hT')
    refine ⟨ε, hε, fun u hu => ?_⟩
    obtain ⟨huP, hu_sees⟩ := hball u hu
    exact ⟨huP, fun i hi => hu_sees (ι i) (Finset.mem_image_of_mem ι hi)⟩
  triangle_enclosure := hP.triangle_enclosure
  two_path_enclosure := hP.two_path_enclosure
  gk14_no_ten_convex B' hconv := by
    have hcard : B'.card = (B'.image ι).card :=
      (Finset.card_image_of_injective B' ι.injective).symm
    rw [hcard]
    refine hP.gk14_no_ten_convex (B'.image ι) (fun j hj => ?_)
    rcases Finset.mem_image.mp hj with ⟨i, hiB, rfl⟩
    have herase : ((B'.image ι).erase (ι i)) = (B'.erase i).image ι := by
      ext k
      simp only [Finset.mem_erase, Finset.mem_image]
      constructor
      · rintro ⟨hne, a, ha, rfl⟩
        exact ⟨a, ⟨fun heq => hne (congrArg ι heq), ha⟩, rfl⟩
      · rintro ⟨a, ⟨hne, ha⟩, rfl⟩
        exact ⟨fun heq => hne (ι.injective heq), a, ha, rfl⟩
    have hci := hconv i hiB
    rw [Finset.coe_image] at hci
    rw [herase, Finset.coe_image, Finset.coe_image, ← Set.image_comp]
    exact hci
  isler_six_wedges := hP.isler_six_wedges

/-- **Hereditary Shattered 7-Subset (`hereditary_shattered_subset`)**:
    If `S : Fin 9 → ℝ × ℝ` is shattered in `P` under `(G1)-(G2)`, then every 7-element subset
    `S₇ : Finset (Fin 9)` (`S₇.card = 7`) admits an enumeration `ι : Fin 7 ↪ Fin 9` with image `S₇`
    and witness map `w' T' := w (T'.image ι)` satisfying `ShatteredSimplePolygon P (S ∘ ι) w'`. -/
theorem hereditary_shattered_subset {P : Set (ℝ × ℝ)}
    {S : Fin 9 → ℝ × ℝ} {w : Finset (Fin 9) → ℝ × ℝ}
    (hP : ShatteredSimplePolygon P S w)
    (S₇ : Finset (Fin 9)) (hcard : S₇.card = 7) :
    ∃ ι : Fin 7 ↪ Fin 9,
      Finset.univ.image ι = S₇ ∧
      ShatteredSimplePolygon P (S ∘ ι) (fun T' => w (T'.image ι)) := by
  let e : S₇ ≃ Fin 7 := S₇.equivFinOfCardEq hcard
  let ι : Fin 7 ↪ Fin 9 :=
    { toFun := fun i => (e.symm i).1
      inj' := fun i j h => e.symm.injective (Subtype.ext h) }
  refine ⟨ι, ?_, hereditary_shattered_emb hP ι⟩
  ext x
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, rfl⟩
    exact (e.symm i).2
  · intro hx
    refine ⟨e ⟨x, hx⟩, ?_⟩
    change (e.symm (e ⟨x, hx⟩)).1 = x
    simp

end NewEnclosure

end
