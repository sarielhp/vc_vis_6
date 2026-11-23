import Mathlib
import RootTask.Defs
import RootTask.UnconditionalBridge
import RootTask.Sec7Combination
import RootTask.PolygonDefs

open scoped Classical BigOperators
open Finset

noncomputable section

namespace Sec5HP

/-!
# Section 5: The Half-Plane Lemma (`upper_9.tex`, Lemma 5.1)

Formalizes the complete proof of Section 5 (`upper_9.tex` lines 434–592):
- Angle ordering `rayAngle` / `AngleLtFromRay` and proper segment crossing `SegmentsCross`,
- Affine coordinate normalization `toNormCoords` / `fromNormCoords` sending `(v, q, p) ↦ ((0,0), (1,0), (0,1))`,
- Claim 5.2 (`Ta ⊆ P`), Claim 5.3 (`coords`), Claim 5.4 (`witness-pos`), Claim 5.5 (`monotone-slope`),
- Lemma 5.1 (`half_plane_lemma_orient` and `half_plane_lemma`).
-/

/-! ## 1. Geometric Predicates: Same-Side, Angles, Segment Crossing -/

/-- Two points `x, y` lie in the same open half-plane bounded by the line through `v` and `q`. -/
def SameSideOfLine (v q x y : ℝ × ℝ) : Prop :=
  0 < orient2D v q x * orient2D v q y

/-- Proper crossing of two closed segments `[x₁, x₂]` and `[y₁, y₂]` (endpoints lie strictly
    on opposite open sides of each other's supporting lines). -/
def SegmentsCross (x₁ x₂ y₁ y₂ : ℝ × ℝ) : Prop :=
  orient2D x₁ x₂ y₁ * orient2D x₁ x₂ y₂ < 0 ∧
  orient2D y₁ y₂ x₁ * orient2D y₁ y₂ x₂ < 0

/-- Angle `θ(y) ∈ [0, π]` between rays `v → q` and `v → y`. -/
def rayAngle (v q y : ℝ × ℝ) : ℝ :=
  Real.arccos
    (((q.1 - v.1) * (y.1 - v.1) + (q.2 - v.2) * (y.2 - v.2)) /
      (Real.sqrt ((q.1 - v.1) ^ 2 + (q.2 - v.2) ^ 2) *
       Real.sqrt ((y.1 - v.1) ^ 2 + (y.2 - v.2) ^ 2)))

private lemma norm_pos_of_orient_ne_zero {v a b : ℝ × ℝ} (h : orient2D v a b ≠ 0) :
    0 < Real.sqrt ((a.1 - v.1) ^ 2 + (a.2 - v.2) ^ 2) ∧
    0 < Real.sqrt ((b.1 - v.1) ^ 2 + (b.2 - v.2) ^ 2) := by
  constructor
  · rw [Real.sqrt_pos]
    by_contra hle
    have h0 : (a.1 - v.1) ^ 2 + (a.2 - v.2) ^ 2 = 0 :=
      le_antisymm (not_lt.mp hle) (add_nonneg (sq_nonneg _) (sq_nonneg _))
    have ha1 : a.1 - v.1 = 0 := by nlinarith [sq_nonneg (a.1 - v.1), sq_nonneg (a.2 - v.2)]
    have ha2 : a.2 - v.2 = 0 := by nlinarith [sq_nonneg (a.1 - v.1), sq_nonneg (a.2 - v.2)]
    apply h
    unfold orient2D
    rw [ha1, ha2]
    ring
  · rw [Real.sqrt_pos]
    by_contra hle
    have h0 : (b.1 - v.1) ^ 2 + (b.2 - v.2) ^ 2 = 0 :=
      le_antisymm (not_lt.mp hle) (add_nonneg (sq_nonneg _) (sq_nonneg _))
    have hb1 : b.1 - v.1 = 0 := by nlinarith [sq_nonneg (b.1 - v.1), sq_nonneg (b.2 - v.2)]
    have hb2 : b.2 - v.2 = 0 := by nlinarith [sq_nonneg (b.1 - v.1), sq_nonneg (b.2 - v.2)]
    apply h
    unfold orient2D
    rw [hb1, hb2]
    ring

private lemma unit_cos_sin_det_iff {cx sx cy sy : ℝ}
    (hx : cx ^ 2 + sx ^ 2 = 1) (hy : cy ^ 2 + sy ^ 2 = 1)
    (hsx : 0 < sx) (hsy : 0 < sy) :
    cy < cx ↔ 0 < cx * sy - sx * cy := by
  constructor
  · intro hlt
    rcases le_total 0 cx with hcx | hcx
    · rcases le_total cy 0 with hcy | hcy
      · have h1 : 0 ≤ cx * sy := mul_nonneg hcx (le_of_lt hsy)
        have h2 : sx * cy ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (le_of_lt hsx) hcy
        rcases eq_or_lt_of_le hcx with hcx0 | hcx_pos
        · have hcy_neg : cy < 0 := by linarith
          have : sx * cy < 0 := mul_neg_of_pos_of_neg hsx hcy_neg
          linarith
        · have : 0 < cx * sy := mul_pos hcx_pos hsy
          linarith
      · have hsq : sx ^ 2 < sy ^ 2 := by nlinarith
        have hlt_s : sx < sy := by nlinarith
        nlinarith
    · have hsq : sy ^ 2 < sx ^ 2 := by nlinarith
      have hlt_s : sy < sx := by nlinarith
      nlinarith
  · intro hdet
    by_contra hle
    replace hle : cx ≤ cy := not_lt.mp hle
    rcases eq_or_lt_of_le hle with heq | hlt
    · subst heq
      have hsq : sx ^ 2 = sy ^ 2 := by linarith
      have heq_s : sx = sy := by nlinarith
      rw [heq_s] at hdet
      linarith
    · rcases le_total 0 cy with hcy | hcy
      · rcases le_total cx 0 with hcx | hcx
        · have h1 : cx * sy ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hcx (le_of_lt hsy)
          have h2 : 0 ≤ sx * cy := mul_nonneg (le_of_lt hsx) hcy
          linarith
        · have hsq : sy ^ 2 < sx ^ 2 := by nlinarith
          have hlt_s : sy < sx := by nlinarith
          nlinarith
      · have hsq : sx ^ 2 < sy ^ 2 := by nlinarith
        have hlt_s : sx < sy := by nlinarith
        nlinarith

/-- Equivalence between `rayAngle v q x < rayAngle v q y` and the orientation condition
    `0 < orient2D v x y * orient2D v q x` whenever `x, y` lie on the same open side of `vq`. -/
lemma rayAngle_lt_iff_orient {v q x y : ℝ × ℝ} (hsame : SameSideOfLine v q x y) :
    rayAngle v q x < rayAngle v q y ↔ 0 < orient2D v x y * orient2D v q x := by
  have hqx_ne : orient2D v q x ≠ 0 := by
    intro h0; rw [SameSideOfLine, h0, zero_mul] at hsame; exact lt_irrefl 0 hsame
  have hqy_ne : orient2D v q y ≠ 0 := by
    intro h0; rw [SameSideOfLine, h0, mul_zero] at hsame; exact lt_irrefl 0 hsame
  obtain ⟨hrq, hrx⟩ := norm_pos_of_orient_ne_zero hqx_ne
  obtain ⟨_, hry⟩ := norm_pos_of_orient_ne_zero hqy_ne
  let rq := Real.sqrt ((q.1 - v.1) ^ 2 + (q.2 - v.2) ^ 2)
  let rx := Real.sqrt ((x.1 - v.1) ^ 2 + (x.2 - v.2) ^ 2)
  let ry := Real.sqrt ((y.1 - v.1) ^ 2 + (y.2 - v.2) ^ 2)
  have hrq2 : rq ^ 2 = (q.1 - v.1) ^ 2 + (q.2 - v.2) ^ 2 :=
    Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _))
  have hrx2 : rx ^ 2 = (x.1 - v.1) ^ 2 + (x.2 - v.2) ^ 2 :=
    Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _))
  have hry2 : ry ^ 2 = (y.1 - v.1) ^ 2 + (y.2 - v.2) ^ 2 :=
    Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _))
  let cx := ((q.1 - v.1) * (x.1 - v.1) + (q.2 - v.2) * (x.2 - v.2)) / (rq * rx)
  let sx := orient2D v q x / (rq * rx)
  let cy := ((q.1 - v.1) * (y.1 - v.1) + (q.2 - v.2) * (y.2 - v.2)) / (rq * ry)
  let sy := orient2D v q y / (rq * ry)
  have hrqx : 0 < rq * rx := mul_pos hrq hrx
  have hrqy : 0 < rq * ry := mul_pos hrq hry
  have hux : cx ^ 2 + sx ^ 2 = 1 := by
    have hid : ((q.1 - v.1) * (x.1 - v.1) + (q.2 - v.2) * (x.2 - v.2)) ^ 2 +
        orient2D v q x ^ 2 =
        ((q.1 - v.1) ^ 2 + (q.2 - v.2) ^ 2) * ((x.1 - v.1) ^ 2 + (x.2 - v.2) ^ 2) := by
      unfold orient2D; ring
    dsimp [cx, sx]
    rw [div_pow, div_pow, ← add_div, hid, ← hrq2, ← hrx2, ← mul_pow,
        div_self (ne_of_gt (pow_pos hrqx 2))]
  have huy : cy ^ 2 + sy ^ 2 = 1 := by
    have hid : ((q.1 - v.1) * (y.1 - v.1) + (q.2 - v.2) * (y.2 - v.2)) ^ 2 +
        orient2D v q y ^ 2 =
        ((q.1 - v.1) ^ 2 + (q.2 - v.2) ^ 2) * ((y.1 - v.1) ^ 2 + (y.2 - v.2) ^ 2) := by
      unfold orient2D; ring
    dsimp [cy, sy]
    rw [div_pow, div_pow, ← add_div, hid, ← hrq2, ← hry2, ← mul_pow,
        div_self (ne_of_gt (pow_pos hrqy 2))]
  have hcx_le : cx ≤ 1 := by nlinarith [sq_nonneg sx, sq_nonneg (cx - 1)]
  have hcx_ge : -1 ≤ cx := by nlinarith [sq_nonneg sx, sq_nonneg (cx + 1)]
  have hcy_le : cy ≤ 1 := by nlinarith [sq_nonneg sy, sq_nonneg (cy - 1)]
  have hcy_ge : -1 ≤ cy := by nlinarith [sq_nonneg sy, sq_nonneg (cy + 1)]
  have harccos_iff : rayAngle v q x < rayAngle v q y ↔ cy < cx := by
    dsimp [rayAngle]
    change Real.arccos cx < Real.arccos cy ↔ cy < cx
    constructor
    · intro hlt
      by_contra hle
      exact absurd hlt (not_lt.mpr (Real.arccos_le_arccos (not_lt.mp hle)))
    · intro hlt
      exact Real.arccos_lt_arccos hcy_ge hlt hcx_le
  have hdet_id : cx * sy - sx * cy = orient2D v x y / (rx * ry) := by
    dsimp [cx, sx, cy, sy, orient2D]
    have hne1 : rq ≠ 0 := ne_of_gt hrq
    have hne2 : rx ≠ 0 := ne_of_gt hrx
    have hne3 : ry ≠ 0 := ne_of_gt hry
    field_simp [hne1, hne2, hne3]
    rw [hrq2]
    ring
  rw [harccos_iff]
  have hs_same : 0 < sx * sy := by
    dsimp [sx, sy]
    rw [div_mul_div_comm]
    exact div_pos hsame (mul_pos hrqx hrqy)
  rcases lt_trichotomy 0 sx with hsx_pos | hsx_zero | hsx_neg
  · have hsy_pos : 0 < sy := by nlinarith
    rw [unit_cos_sin_det_iff hux huy hsx_pos hsy_pos, hdet_id]
    have hq_pos : 0 < orient2D v q x := by
      have : orient2D v q x = sx * (rq * rx) := by
        dsimp [sx]; exact (div_mul_cancel₀ _ (ne_of_gt hrqx)).symm
      rw [this]; exact mul_pos hsx_pos hrqx
    have hrxy : 0 < rx * ry := mul_pos hrx hry
    constructor
    · intro h
      have h1 : 0 < orient2D v x y := by
        have : orient2D v x y = (orient2D v x y / (rx * ry)) * (rx * ry) :=
          (div_mul_cancel₀ _ (ne_of_gt hrxy)).symm
        rw [this]; exact mul_pos h hrxy
      exact mul_pos h1 hq_pos
    · intro h
      have h1 : 0 < orient2D v x y := pos_of_mul_pos_left h (le_of_lt hq_pos)
      exact div_pos h1 hrxy
  · exact absurd hsx_zero.symm (by dsimp [sx]; exact div_ne_zero hqx_ne (ne_of_gt hrqx))
  · have hsy_neg : sy < 0 := by nlinarith
    have hux' : cx ^ 2 + (-sx) ^ 2 = 1 := by linear_combination hux
    have huy' : cy ^ 2 + (-sy) ^ 2 = 1 := by linear_combination huy
    rw [unit_cos_sin_det_iff hux' huy' (neg_pos.mpr hsx_neg) (neg_pos.mpr hsy_neg)]
    have hneg_det : cx * (-sy) - (-sx) * cy = -(cx * sy - sx * cy) := by ring
    rw [hneg_det, hdet_id]
    have hq_neg : orient2D v q x < 0 := by
      have : orient2D v q x = sx * (rq * rx) := by
        dsimp [sx]; exact (div_mul_cancel₀ _ (ne_of_gt hrqx)).symm
      rw [this]; exact mul_neg_of_neg_of_pos hsx_neg hrqx
    have hrxy : 0 < rx * ry := mul_pos hrx hry
    constructor
    · intro h
      have h1 : orient2D v x y / (rx * ry) < 0 := neg_pos.mp h
      have h2 : orient2D v x y < 0 := by
        have : orient2D v x y = (orient2D v x y / (rx * ry)) * (rx * ry) :=
          (div_mul_cancel₀ _ (ne_of_gt hrxy)).symm
        rw [this]; exact mul_neg_of_neg_of_pos h1 hrxy
      exact mul_pos_of_neg_of_neg h2 hq_neg
    · intro h
      have h1 : orient2D v x y < 0 := neg_of_mul_pos_left h (le_of_lt hq_neg)
      have h2 : orient2D v x y / (rx * ry) < 0 := div_neg_of_neg_of_pos h1 hrxy
      exact neg_pos.mpr h2

/-- If two segments intersect and their four endpoints have no collinear triples, they properly cross. -/
lemma segmentsCross_of_mem_segment {x₁ x₂ y₁ y₂ z : ℝ × ℝ}
    (hzx : z ∈ segment ℝ x₁ x₂) (hzy : z ∈ segment ℝ y₁ y₂)
    (hx_y1 : orient2D x₁ x₂ y₁ ≠ 0) (hx_y2 : orient2D x₁ x₂ y₂ ≠ 0)
    (hy_x1 : orient2D y₁ y₂ x₁ ≠ 0) (hy_x2 : orient2D y₁ y₂ x₂ ≠ 0) :
    SegmentsCross x₁ x₂ y₁ y₂ := by
  rw [segment_eq_image] at hzx hzy
  rcases hzx with ⟨t, ht, htz⟩
  rcases hzy with ⟨s, hs, hsz⟩
  have htz1 : z.1 = (1 - t) * x₁.1 + t * x₂.1 := by
    have := congrArg Prod.fst htz; simpa [AffineMap.lineMap_apply_module, smul_eq_mul] using this.symm
  have htz2 : z.2 = (1 - t) * x₁.2 + t * x₂.2 := by
    have := congrArg Prod.snd htz; simpa [AffineMap.lineMap_apply_module, smul_eq_mul] using this.symm
  have hsz1 : z.1 = (1 - s) * y₁.1 + s * y₂.1 := by
    have := congrArg Prod.fst hsz; simpa [AffineMap.lineMap_apply_module, smul_eq_mul] using this.symm
  have hsz2 : z.2 = (1 - s) * y₁.2 + s * y₂.2 := by
    have := congrArg Prod.snd hsz; simpa [AffineMap.lineMap_apply_module, smul_eq_mul] using this.symm
  have hox : orient2D x₁ x₂ z = 0 := by
    rw [orient2D_affine_comb x₁ x₂ x₁ x₂ z t htz1 htz2, orient2D_self_outer, orient2D_self_right]
    ring
  have hoy : orient2D y₁ y₂ z = 0 := by
    rw [orient2D_affine_comb y₁ y₂ y₁ y₂ z s hsz1 hsz2, orient2D_self_outer, orient2D_self_right]
    ring
  have h1 : (1 - s) * orient2D x₁ x₂ y₁ + s * orient2D x₁ x₂ y₂ = 0 := by
    rw [← orient2D_affine_comb x₁ x₂ y₁ y₂ z s hsz1 hsz2, hox]
  have h2 : (1 - t) * orient2D y₁ y₂ x₁ + t * orient2D y₁ y₂ x₂ = 0 := by
    rw [← orient2D_affine_comb y₁ y₂ x₁ x₂ z t htz1 htz2, hoy]
  have hs_pos : 0 < s := by
    rcases eq_or_lt_of_le hs.1 with rfl | hlt
    · exfalso; apply hx_y1; linarith
    · exact hlt
  have hs_lt1 : s < 1 := by
    rcases eq_or_lt_of_le hs.2 with rfl | hlt
    · exfalso; apply hx_y2; linarith
    · exact hlt
  have ht_pos : 0 < t := by
    rcases eq_or_lt_of_le ht.1 with rfl | hlt
    · exfalso; apply hy_x1; linarith
    · exact hlt
  have ht_lt1 : t < 1 := by
    rcases eq_or_lt_of_le ht.2 with rfl | hlt
    · exfalso; apply hy_x2; linarith
    · exact hlt
  constructor
  · have hmul : (1 - s) * s * (orient2D x₁ x₂ y₁ * orient2D x₁ x₂ y₂) =
        -(s * orient2D x₁ x₂ y₂) ^ 2 := by
      have : (1 - s) * orient2D x₁ x₂ y₁ = -(s * orient2D x₁ x₂ y₂) := by linarith
      calc
        (1 - s) * s * (orient2D x₁ x₂ y₁ * orient2D x₁ x₂ y₂)
            = s * ((1 - s) * orient2D x₁ x₂ y₁) * orient2D x₁ x₂ y₂ := by ring
        _ = s * (-(s * orient2D x₁ x₂ y₂)) * orient2D x₁ x₂ y₂ := by rw [this]
        _ = -(s * orient2D x₁ x₂ y₂) ^ 2 := by ring
    have hsq_pos : 0 < (s * orient2D x₁ x₂ y₂) ^ 2 := sq_pos_of_ne_zero (mul_ne_zero (ne_of_gt hs_pos) hx_y2)
    have hcoeff : 0 < (1 - s) * s := mul_pos (sub_pos.mpr hs_lt1) hs_pos
    nlinarith
  · have hmul : (1 - t) * t * (orient2D y₁ y₂ x₁ * orient2D y₁ y₂ x₂) =
        -(t * orient2D y₁ y₂ x₂) ^ 2 := by
      have : (1 - t) * orient2D y₁ y₂ x₁ = -(t * orient2D y₁ y₂ x₂) := by linarith
      calc
        (1 - t) * t * (orient2D y₁ y₂ x₁ * orient2D y₁ y₂ x₂)
            = t * ((1 - t) * orient2D y₁ y₂ x₁) * orient2D y₁ y₂ x₂ := by ring
        _ = t * (-(t * orient2D y₁ y₂ x₂)) * orient2D y₁ y₂ x₂ := by rw [this]
        _ = -(t * orient2D y₁ y₂ x₂) ^ 2 := by ring
    have hsq_pos : 0 < (t * orient2D y₁ y₂ x₂) ^ 2 := sq_pos_of_ne_zero (mul_ne_zero (ne_of_gt ht_pos) hy_x2)
    have hcoeff : 0 < (1 - t) * t := mul_pos (sub_pos.mpr ht_lt1) ht_pos
    nlinarith

/-! ## 2. Segment, Convexity, and Polygonal-Path Helpers -/

private lemma mem_segment_of_coords {x y z : ℝ × ℝ} (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hz1 : z.1 = (1 - t) * x.1 + t * y.1)
    (hz2 : z.2 = (1 - t) * x.2 + t * y.2) :
    z ∈ segment ℝ x y := by
  refine ⟨1 - t, t, sub_nonneg.mpr ht1, ht0, by ring, ?_⟩
  ext <;> simp [smul_eq_mul, hz1, hz2]

private lemma sees_of_convex_subset {P C : Set (ℝ × ℝ)} {x y : ℝ × ℝ}
    (hsub : C ⊆ P) (hconv : Convex ℝ C) (hx : x ∈ C) (hy : y ∈ C) :
    Sees P x y :=
  (hconv.segment_subset hx hy).trans hsub

private lemma sees_subsegment {P : Set (ℝ × ℝ)} {x y u v : ℝ × ℝ}
    (h : Sees P x y) (hu : u ∈ segment ℝ x y) (hv : v ∈ segment ℝ x y) :
    Sees P u v :=
  ((convex_segment x y).segment_subset hu hv).trans h

private lemma sees_of_mem_segment {P : Set (ℝ × ℝ)} {x y z : ℝ × ℝ}
    (hz : z ∈ segment ℝ x y) (hxz : Sees P x z) (hzy : Sees P z y) :
    Sees P x y := by
  intro w hw
  rw [segment_eq_image] at hz hw
  rcases hz with ⟨t, ht, htz⟩
  rcases hw with ⟨s, hs, hsw⟩
  have htz_eq : z = (1 - t) • x + t • y := by simpa [AffineMap.lineMap_apply_module] using htz.symm
  have hsw_eq : w = (1 - s) • x + s • y := by simpa [AffineMap.lineMap_apply_module] using hsw.symm
  rcases le_total s t with hst | hts
  · apply hxz
    rcases eq_or_lt_of_le ht.1 with rfl | ht_pos
    · have hs0 : s = 0 := le_antisymm (by linarith) hs.1
      rw [hsw_eq, hs0]; simp [left_mem_segment]
    · have hst' : s / t ≤ 1 := (div_le_one ht_pos).mpr hst
      have h0 : 0 ≤ s / t := div_nonneg hs.1 (le_of_lt ht_pos)
      refine mem_segment_of_coords (s / t) h0 hst' ?_ ?_
      · have h1 := congrArg Prod.fst htz_eq
        have h2 := congrArg Prod.fst hsw_eq
        simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul] at h1 h2
        rw [h2, h1]; field_simp [ne_of_gt ht_pos]; ring
      · have h1 := congrArg Prod.snd htz_eq
        have h2 := congrArg Prod.snd hsw_eq
        simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul] at h1 h2
        rw [h2, h1]; field_simp [ne_of_gt ht_pos]; ring
  · apply hzy
    rcases eq_or_lt_of_le ht.2 with rfl | ht_lt1
    · have hs1 : s = 1 := le_antisymm hs.2 (by linarith)
      rw [hsw_eq, hs1]; simp [right_mem_segment]
    · have h1mt : 0 < 1 - t := sub_pos.mpr ht_lt1
      have h0 : 0 ≤ (s - t) / (1 - t) := div_nonneg (sub_nonneg.mpr hts) (le_of_lt h1mt)
      have h1 : (s - t) / (1 - t) ≤ 1 := (div_le_one h1mt).mpr (by linarith [hs.2])
      refine mem_segment_of_coords ((s - t) / (1 - t)) h0 h1 ?_ ?_
      · have h1 := congrArg Prod.fst htz_eq
        have h2 := congrArg Prod.fst hsw_eq
        simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul] at h1 h2
        rw [h2, h1]; field_simp [ne_of_gt h1mt]; ring
      · have h1 := congrArg Prod.snd htz_eq
        have h2 := congrArg Prod.snd hsw_eq
        simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul] at h1 h2
        rw [h2, h1]; field_simp [ne_of_gt h1mt]; ring

private lemma mem_P_left_of_sees {P : Set (ℝ × ℝ)} {x y : ℝ × ℝ} (h : Sees P x y) : x ∈ P :=
  h (left_mem_segment ℝ x y)

private lemma mem_P_right_of_sees {P : Set (ℝ × ℝ)} {x y : ℝ × ℝ} (h : Sees P x y) : y ∈ P :=
  h (right_mem_segment ℝ x y)

private lemma isPolygonalPathIn_three {P : Set (ℝ × ℝ)} {s u t : ℝ × ℝ}
    (h1 : Sees P s u) (h2 : Sees P u t) :
    IsPolygonalPathIn P s t [s, u, t] := by
  refine ⟨by simp, rfl, rfl, ?_, ?_⟩
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · exact mem_P_left_of_sees h1
    · exact mem_P_right_of_sees h1
    · exact mem_P_right_of_sees h2
  · simp [List.isChain_cons_cons, h1, h2]

private lemma isPolygonalPathIn_four {P : Set (ℝ × ℝ)} {s u₁ u₂ t : ℝ × ℝ}
    (h1 : Sees P s u₁) (h2 : Sees P u₁ u₂) (h3 : Sees P u₂ t) :
    IsPolygonalPathIn P s t [s, u₁, u₂, t] := by
  refine ⟨by simp, rfl, rfl, ?_, ?_⟩
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact mem_P_left_of_sees h1
    · exact mem_P_right_of_sees h1
    · exact mem_P_right_of_sees h2
    · exact mem_P_right_of_sees h3
  · simp [List.isChain_cons_cons, h1, h2, h3]

private lemma interiorOnLeft_three {s u t : ℝ × ℝ} (hu : 0 < orient2D s t u) :
    InteriorOnLeft s t [s, u, t] := by
  refine ⟨by simp, fun k hk hk0 hk1 => ?_⟩
  have hk_eq : k = 1 := by simp at hk1; omega
  subst hk_eq
  simpa using hu

private lemma interiorOnRight_three {s u t : ℝ × ℝ} (hu : orient2D s t u < 0) :
    InteriorOnRight s t [s, u, t] := by
  refine ⟨by simp, fun k hk hk0 hk1 => ?_⟩
  have hk_eq : k = 1 := by simp at hk1; omega
  subst hk_eq
  simpa using hu

private lemma interiorOnLeft_four {s u₁ u₂ t : ℝ × ℝ}
    (h1 : 0 < orient2D s t u₁) (h2 : 0 < orient2D s t u₂) :
    InteriorOnLeft s t [s, u₁, u₂, t] := by
  refine ⟨by simp, fun k hk hk0 hk1 => ?_⟩
  have hk_cases : k = 1 ∨ k = 2 := by simp at hk1; omega
  rcases hk_cases with rfl | rfl
  · simpa using h1
  · simpa using h2

private lemma interiorOnRight_four {s u₁ u₂ t : ℝ × ℝ}
    (h1 : orient2D s t u₁ < 0) (h2 : orient2D s t u₂ < 0) :
    InteriorOnRight s t [s, u₁, u₂, t] := by
  refine ⟨by simp, fun k hk hk0 hk1 => ?_⟩
  have hk_cases : k = 1 ∨ k = 2 := by simp at hk1; omega
  rcases hk_cases with rfl | rfl
  · simpa using h1
  · simpa using h2

/-! ## 3. Affine Coordinate Normalization -/

/-- Affine map sending `v ↦ (0, 0)`, `q ↦ (1, 0)`, `p ↦ (0, 1)` when `orient2D v q p ≠ 0`. -/
def toNormCoords (v q p y : ℝ × ℝ) : ℝ × ℝ :=
  (orient2D v y p / orient2D v q p, orient2D v q y / orient2D v q p)

/-- Inverse affine map sending `(0, 0) ↦ v`, `(1, 0) ↦ q`, `(0, 1) ↦ p`. -/
def fromNormCoords (v q p x : ℝ × ℝ) : ℝ × ℝ :=
  (v.1 + x.1 * (q.1 - v.1) + x.2 * (p.1 - v.1),
   v.2 + x.1 * (q.2 - v.2) + x.2 * (p.2 - v.2))

lemma fromNormCoords_toNormCoords (v q p y : ℝ × ℝ) (hD : orient2D v q p ≠ 0) :
    fromNormCoords v q p (toNormCoords v q p y) = y := by
  have hid1 : (orient2D v q p) * v.1 + orient2D v y p * (q.1 - v.1) + orient2D v q y * (p.1 - v.1) =
      orient2D v q p * y.1 := by unfold orient2D; ring
  have hid2 : (orient2D v q p) * v.2 + orient2D v y p * (q.2 - v.2) + orient2D v q y * (p.2 - v.2) =
      orient2D v q p * y.2 := by unfold orient2D; ring
  ext <;> dsimp [fromNormCoords, toNormCoords] <;> field_simp [hD]
  · linarith
  · linarith

lemma toNormCoords_fromNormCoords (v q p x : ℝ × ℝ) (hD : orient2D v q p ≠ 0) :
    toNormCoords v q p (fromNormCoords v q p x) = x := by
  have hid1 : orient2D v (fromNormCoords v q p x) p = orient2D v q p * x.1 := by
    unfold orient2D fromNormCoords; ring
  have hid2 : orient2D v q (fromNormCoords v q p x) = orient2D v q p * x.2 := by
    unfold orient2D fromNormCoords; ring
  ext <;> dsimp [toNormCoords]
  · rw [hid1, mul_div_cancel_left₀ _ hD]
  · rw [hid2, mul_div_cancel_left₀ _ hD]

lemma toNormCoords_v (v q p : ℝ × ℝ) : toNormCoords v q p v = (0, 0) := by
  simp [toNormCoords, orient2D]

lemma toNormCoords_q (v q p : ℝ × ℝ) (hD : orient2D v q p ≠ 0) :
    toNormCoords v q p q = (1, 0) := by
  dsimp [toNormCoords]
  rw [orient2D_self_right, zero_div, div_self hD]

lemma toNormCoords_p (v q p : ℝ × ℝ) (hD : orient2D v q p ≠ 0) :
    toNormCoords v q p p = (0, 1) := by
  dsimp [toNormCoords]
  rw [orient2D_self_right, zero_div, div_self hD]

lemma orient2D_fromNormCoords (v q p x y z : ℝ × ℝ) :
    orient2D (fromNormCoords v q p x) (fromNormCoords v q p y) (fromNormCoords v q p z) =
      orient2D v q p * orient2D x y z := by
  dsimp [fromNormCoords, orient2D]
  ring

lemma orient2D_toNormCoords (v q p a b c : ℝ × ℝ) (hD : orient2D v q p ≠ 0) :
    orient2D (toNormCoords v q p a) (toNormCoords v q p b) (toNormCoords v q p c) =
      orient2D a b c / orient2D v q p := by
  have h1 := orient2D_fromNormCoords v q p (toNormCoords v q p a) (toNormCoords v q p b)
    (toNormCoords v q p c)
  rw [fromNormCoords_toNormCoords v q p a hD,
      fromNormCoords_toNormCoords v q p b hD,
      fromNormCoords_toNormCoords v q p c hD] at h1
  field_simp [hD]
  linarith

/-- Pullback of an `OpenHalfPlane` from normalized coordinates along `toNormCoords v q p`. -/
def pullbackHalfPlane (v q p : ℝ × ℝ) (hD : orient2D v q p ≠ 0) (H' : OpenHalfPlane) :
    OpenHalfPlane where
  n :=
    ((H'.n.1 * (p.2 - v.2) - H'.n.2 * (q.2 - v.2)) / orient2D v q p,
     (-H'.n.1 * (p.1 - v.1) + H'.n.2 * (q.1 - v.1)) / orient2D v q p)
  c :=
    (H'.n.1 * (v.2 * (p.1 - v.1) - v.1 * (p.2 - v.2)) +
     H'.n.2 * (v.1 * (q.2 - v.2) - v.2 * (q.1 - v.1))) / orient2D v q p + H'.c
  hn := by
    by_contra h0
    push Not at h0
    have h1 : H'.n.1 * (p.2 - v.2) - H'.n.2 * (q.2 - v.2) = 0 := by
      have := h0.1; dsimp at this; exact (div_eq_zero_iff.mp this).resolve_right hD
    have h2 : -H'.n.1 * (p.1 - v.1) + H'.n.2 * (q.1 - v.1) = 0 := by
      have := h0.2; dsimp at this; exact (div_eq_zero_iff.mp this).resolve_right hD
    have hdet : (q.1 - v.1) * (p.2 - v.2) - (q.2 - v.2) * (p.1 - v.1) ≠ 0 := hD
    have hn1 : H'.n.1 = 0 := by
      have : H'.n.1 * ((q.1 - v.1) * (p.2 - v.2) - (q.2 - v.2) * (p.1 - v.1)) = 0 := by
        linear_combination (q.1 - v.1) * h1 + (q.2 - v.2) * h2
      exact (mul_eq_zero.mp this).resolve_right hdet
    have hn2 : H'.n.2 = 0 := by
      have : H'.n.2 * ((q.1 - v.1) * (p.2 - v.2) - (q.2 - v.2) * (p.1 - v.1)) = 0 := by
        linear_combination (p.1 - v.1) * h1 + (p.2 - v.2) * h2
      exact (mul_eq_zero.mp this).resolve_right hdet
    rcases H'.hn with ha | hb
    · exact ha hn1
    · exact hb hn2

lemma pullbackHalfPlane_eval (v q p : ℝ × ℝ) (hD : orient2D v q p ≠ 0) (H' : OpenHalfPlane)
    (u : ℝ × ℝ) :
    (pullbackHalfPlane v q p hD H').n.1 * u.1 +
      (pullbackHalfPlane v q p hD H').n.2 * u.2 +
      (pullbackHalfPlane v q p hD H').c =
    H'.n.1 * (toNormCoords v q p u).1 + H'.n.2 * (toNormCoords v q p u).2 + H'.c := by
  dsimp [pullbackHalfPlane, toNormCoords, orient2D] at hD ⊢
  field_simp [hD]
  ring

/-- Normalized visibility/enclosure environment obtained via `toNormCoords v q p`. -/
private structure NormEnv {n : ℕ} (P : Set (ℝ × ℝ))
    (S : Fin n → ℝ × ℝ) (w : Finset (Fin n) → ℝ × ℝ) : Prop where
  s_in_P : ∀ i : Fin n, S i ∈ P
  w_in_P : ∀ T : Finset (Fin n), w T ∈ P
  shatters : ∀ (T : Finset (Fin n)) (i : Fin n), Sees P (w T) (S i) ↔ i ∈ T
  s_inj : Function.Injective S
  w_inj : Function.Injective w
  s_ne_w : ∀ (i : Fin n) (T : Finset (Fin n)), S i ≠ w T
  no_three_collinear : ∀ p q r : ℝ × ℝ,
    p ∈ Set.range S ∪ Set.range w →
    q ∈ Set.range S ∪ Set.range w →
    r ∈ Set.range S ∪ Set.range w →
    p ≠ q → q ≠ r → p ≠ r → orient2D p q r ≠ 0
  open_vis_nbhd : ∀ T : Finset (Fin n), T.Nonempty →
    ∃ ε : ℝ, 0 < ε ∧ ∀ u : ℝ × ℝ, dist u (w T) < ε →
      u ∈ P ∧ ∀ i ∈ T, Sees P u (S i)
  triangle_enclosure : ∀ x ∈ P, ∀ y ∈ P, ∀ z ∈ P,
    Sees P x y → Sees P y z → Sees P x z →
    convexHull ℝ ({x, y, z} : Set (ℝ × ℝ)) ⊆ P
  two_path_enclosure : ∀ (s t : ℝ × ℝ) (π₁ π₂ : List (ℝ × ℝ)),
    s ≠ t → IsPolygonalPathIn P s t π₁ → IsPolygonalPathIn P s t π₂ →
    InteriorOnLeft s t π₁ → InteriorOnRight s t π₂ → Sees P s t

private lemma segment_fromNormCoords (v q p x y : ℝ × ℝ) (_hD : orient2D v q p ≠ 0) :
    fromNormCoords v q p '' segment ℝ x y =
      segment ℝ (fromNormCoords v q p x) (fromNormCoords v q p y) := by
  ext z
  simp only [Set.mem_image, segment_eq_image]
  constructor
  · rintro ⟨u, ⟨t, ht, htu⟩, rfl⟩
    refine ⟨t, ht, ?_⟩
    have htu1 : u.1 = (1 - t) * x.1 + t * y.1 := by
      have := congrArg Prod.fst htu; simpa [smul_eq_mul] using this.symm
    have htu2 : u.2 = (1 - t) * x.2 + t * y.2 := by
      have := congrArg Prod.snd htu; simpa [smul_eq_mul] using this.symm
    ext <;> simp [smul_eq_mul, fromNormCoords, htu1, htu2] <;> ring
  · rintro ⟨t, ht, htz⟩
    refine ⟨((1 - t) * x.1 + t * y.1, (1 - t) * x.2 + t * y.2), ⟨t, ht, ?_⟩, ?_⟩
    · ext <;> simp [smul_eq_mul]
    · have htz1 : z.1 = (1 - t) * (fromNormCoords v q p x).1 + t * (fromNormCoords v q p y).1 := by
        have := congrArg Prod.fst htz
        simpa [smul_eq_mul] using this.symm
      have htz2 : z.2 = (1 - t) * (fromNormCoords v q p x).2 + t * (fromNormCoords v q p y).2 := by
        have := congrArg Prod.snd htz
        simpa [smul_eq_mul] using this.symm
      ext
      · dsimp [fromNormCoords]; rw [htz1]; dsimp [fromNormCoords]; ring
      · dsimp [fromNormCoords]; rw [htz2]; dsimp [fromNormCoords]; ring

private lemma sees_fromNormCoords_iff {P : Set (ℝ × ℝ)} {v q p : ℝ × ℝ}
    (hD : orient2D v q p ≠ 0) {x y : ℝ × ℝ} :
    Sees (toNormCoords v q p '' P) x y ↔
      Sees P (fromNormCoords v q p x) (fromNormCoords v q p y) := by
  unfold Sees
  rw [← segment_fromNormCoords v q p x y hD]
  constructor
  · intro h z hz
    rcases hz with ⟨u, hu, rfl⟩
    rcases h hu with ⟨w, hwP, hwu⟩
    have h1 := congrArg (fromNormCoords v q p) hwu
    rw [fromNormCoords_toNormCoords v q p w hD] at h1
    rwa [← h1]
  · intro h u hu
    refine ⟨fromNormCoords v q p u, h ⟨u, hu, rfl⟩, toNormCoords_fromNormCoords v q p u hD⟩

private lemma isPolygonalPathIn_fromNormCoords {P : Set (ℝ × ℝ)} {v q p s t : ℝ × ℝ}
    (hD : orient2D v q p ≠ 0) {verts : List (ℝ × ℝ)}
    (hpath : IsPolygonalPathIn (toNormCoords v q p '' P) s t verts) :
    IsPolygonalPathIn P (fromNormCoords v q p s) (fromNormCoords v q p t)
      (verts.map (fromNormCoords v q p)) := by
  rcases hpath with ⟨hne, hhead, hlast, hmem, hchain⟩
  refine ⟨by simpa using hne, ?_, ?_, ?_, ?_⟩
  · rw [List.head_map, hhead]
  · rw [List.getLast_map, hlast]
  · intro y hy
    rcases List.mem_map.mp hy with ⟨u, hu, rfl⟩
    rcases hmem u hu with ⟨z, hzP, hzu⟩
    have := congrArg (fromNormCoords v q p) hzu
    rw [fromNormCoords_toNormCoords v q p z hD] at this
    rwa [← this]
  · rw [List.isChain_map]
    exact hchain.imp fun {a b} hab => (sees_fromNormCoords_iff hD).mp hab

private lemma normEnv_of_shattered {n : ℕ} {P : Set (ℝ × ℝ)}
    {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ}
    (hP : ShatteredSimplePolygon P S w) (v q p : ℝ × ℝ) (hD : orient2D v q p ≠ 0) :
    NormEnv (toNormCoords v q p '' P) (fun i => toNormCoords v q p (S i))
      (fun T => toNormCoords v q p (w T)) := by
  let Φ := toNormCoords v q p
  let Ψ := fromNormCoords v q p
  have hΦΨ : ∀ x, Φ (Ψ x) = x := fun x => toNormCoords_fromNormCoords v q p x hD
  have hΨΦ : ∀ y, Ψ (Φ y) = y := fun y => fromNormCoords_toNormCoords v q p y hD
  have hΦ_inj : Function.Injective Φ := fun a b hab => by
    have := congrArg Ψ hab; rwa [hΨΦ, hΨΦ] at this
  refine
    { s_in_P := fun i => ⟨S i, hP.s_in_P i, rfl⟩
      w_in_P := fun T => ⟨w T, hP.w_in_P T, rfl⟩
      shatters := fun T i => by
        rw [sees_fromNormCoords_iff hD]
        change Sees P (Ψ (Φ (w T))) (Ψ (Φ (S i))) ↔ i ∈ T
        rw [hΨΦ, hΨΦ]
        exact hP.shatters T i
      s_inj := hΦ_inj.comp hP.s_inj
      w_inj := hΦ_inj.comp hP.w_inj
      s_ne_w := fun i T h => hP.s_ne_w i T (hΦ_inj h)
      no_three_collinear := ?_
      open_vis_nbhd := ?_
      triangle_enclosure := ?_
      two_path_enclosure := ?_ }
  · intro x' y' z' hx' hy' hz' hxy hyz hxz
    have hmem : ∀ u', u' ∈ Set.range (Φ ∘ S) ∪ Set.range (Φ ∘ w) →
        Ψ u' ∈ Set.range S ∪ Set.range w := by
      intro u' hu'
      rcases hu' with ⟨i, rfl⟩ | ⟨T, rfl⟩
      · left; exact ⟨i, (hΨΦ (S i)).symm⟩
      · right; exact ⟨T, (hΨΦ (w T)).symm⟩
    have hne : ∀ a b : ℝ × ℝ, a ≠ b → Ψ a ≠ Ψ b := fun a b hab h =>
      hab (by have := congrArg Φ h; rwa [hΦΨ, hΦΨ] at this)
    have hor := hP.no_three_collinear (Ψ x') (Ψ y') (Ψ z')
      (hmem x' hx') (hmem y' hy') (hmem z' hz')
      (hne x' y' hxy) (hne y' z' hyz) (hne x' z' hxz)
    rw [orient2D_fromNormCoords] at hor
    intro h0
    apply hor
    rw [h0, mul_zero]
  · intro T hT
    obtain ⟨ε, hε, hball⟩ := hP.open_vis_nbhd T hT
    have hcont : Continuous Ψ := by
      unfold Ψ fromNormCoords
      fun_prop
    obtain ⟨δ, hδ, hδball⟩ :=
      Metric.continuousAt_iff.mp (hcont.continuousAt (x := Φ (w T))) ε hε
    refine ⟨δ, hδ, fun u hu => ?_⟩
    have hdist : dist (Ψ u) (w T) < ε := by
      have := hδball hu
      rwa [hΨΦ] at this
    obtain ⟨huP, husee⟩ := hball (Ψ u) hdist
    refine ⟨⟨Ψ u, huP, hΦΨ u⟩, fun i hi => ?_⟩
    rw [sees_fromNormCoords_iff hD]
    change Sees P (Ψ u) (Ψ (Φ (S i)))
    rw [hΨΦ]
    exact husee i hi
  · intro x hx y hy z hz hxy hyz hxz u hu
    rcases hx with ⟨x0, hx0, rfl⟩
    rcases hy with ⟨y0, hy0, rfl⟩
    rcases hz with ⟨z0, hz0, rfl⟩
    rw [sees_fromNormCoords_iff hD] at hxy hyz hxz
    change Sees P (Ψ (Φ x0)) (Ψ (Φ y0)) at hxy
    change Sees P (Ψ (Φ y0)) (Ψ (Φ z0)) at hyz
    change Sees P (Ψ (Φ x0)) (Ψ (Φ z0)) at hxz
    rw [hΨΦ, hΨΦ] at hxy hyz hxz
    have htri := hP.triangle_enclosure x0 hx0 y0 hy0 z0 hz0 hxy hyz hxz
    have hconv : Convex ℝ {w : ℝ × ℝ | Ψ w ∈ convexHull ℝ ({x0, y0, z0} : Set (ℝ × ℝ))} := by
      intro a ha b hb α β hα hβ hαβ
      have hc := (convex_convexHull ℝ ({x0, y0, z0} : Set (ℝ × ℝ))) ha hb hα hβ hαβ
      have hlin : Ψ (α • a + β • b) = α • Ψ a + β • Ψ b := by
        have hfst : (α • a + β • b).1 = α * a.1 + β * b.1 := rfl
        have hsnd : (α • a + β • b).2 = α * a.2 + β * b.2 := rfl
        ext
        · change v.1 + (α • a + β • b).1 * (q.1 - v.1) + (α • a + β • b).2 * (p.1 - v.1) =
            α * (v.1 + a.1 * (q.1 - v.1) + a.2 * (p.1 - v.1)) +
            β * (v.1 + b.1 * (q.1 - v.1) + b.2 * (p.1 - v.1))
          rw [hfst, hsnd]; linear_combination -v.1 * hαβ
        · change v.2 + (α • a + β • b).1 * (q.2 - v.2) + (α • a + β • b).2 * (p.2 - v.2) =
            α * (v.2 + a.1 * (q.2 - v.2) + a.2 * (p.2 - v.2)) +
            β * (v.2 + b.1 * (q.2 - v.2) + b.2 * (p.2 - v.2))
          rw [hfst, hsnd]; linear_combination -v.2 * hαβ
      rwa [Set.mem_setOf_eq, hlin]
    have hsub : ({Φ x0, Φ y0, Φ z0} : Set (ℝ × ℝ)) ⊆
        {w : ℝ × ℝ | Ψ w ∈ convexHull ℝ ({x0, y0, z0} : Set (ℝ × ℝ))} := by
      intro w hw
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
      rcases hw with rfl | rfl | rfl <;> rw [Set.mem_setOf_eq, hΨΦ] <;>
        exact subset_convexHull ℝ _ (by simp)
    have hu_in : Ψ u ∈ convexHull ℝ ({x0, y0, z0} : Set (ℝ × ℝ)) :=
      convexHull_min hsub hconv hu
    exact ⟨Ψ u, htri hu_in, hΦΨ u⟩
  · intro s t π₁ π₂ hst hπ₁ hπ₂ hleft hright
    rw [sees_fromNormCoords_iff hD]
    have hst' : Ψ s ≠ Ψ t := fun h => hst (by have := congrArg Φ h; rwa [hΦΨ, hΦΨ] at this)
    have hπ₁' := isPolygonalPathIn_fromNormCoords hD hπ₁
    have hπ₂' := isPolygonalPathIn_fromNormCoords hD hπ₂
    rcases lt_or_gt_of_ne hD with hDneg | hDpos
    · have hleft' : InteriorOnLeft (Ψ s) (Ψ t) (π₂.map Ψ) := by
        refine ⟨by simpa using hright.1, fun k hk hk0 hk1 => ?_⟩
        simp only [List.length_map] at hk hk1
        rw [List.getElem_map, orient2D_fromNormCoords]
        exact mul_pos_of_neg_of_neg hDneg (hright.2 k hk hk0 hk1)
      have hright' : InteriorOnRight (Ψ s) (Ψ t) (π₁.map Ψ) := by
        refine ⟨by simpa using hleft.1, fun k hk hk0 hk1 => ?_⟩
        simp only [List.length_map] at hk hk1
        rw [List.getElem_map, orient2D_fromNormCoords]
        exact mul_neg_of_neg_of_pos hDneg (hleft.2 k hk hk0 hk1)
      exact sees_symm (hP.two_path_enclosure (Ψ s) (Ψ t) (π₂.map Ψ) (π₁.map Ψ)
        hst' hπ₂' hπ₁' hleft' hright' |> sees_symm)
    · have hleft' : InteriorOnLeft (Ψ s) (Ψ t) (π₁.map Ψ) := by
        refine ⟨by simpa using hleft.1, fun k hk hk0 hk1 => ?_⟩
        simp only [List.length_map] at hk hk1
        rw [List.getElem_map, orient2D_fromNormCoords]
        exact mul_pos hDpos (hleft.2 k hk hk0 hk1)
      have hright' : InteriorOnRight (Ψ s) (Ψ t) (π₂.map Ψ) := by
        refine ⟨by simpa using hright.1, fun k hk hk0 hk1 => ?_⟩
        simp only [List.length_map] at hk hk1
        rw [List.getElem_map, orient2D_fromNormCoords]
        exact mul_neg_of_pos_of_neg hDpos (hright.2 k hk hk0 hk1)
      exact hP.two_path_enclosure (Ψ s) (Ψ t) (π₁.map Ψ) (π₂.map Ψ)
        hst' hπ₁' hπ₂' hleft' hright'

/-! ## 4. Normalized Claims 5.2 – 5.5 (`upper_9.tex` lines 506–583) -/

/-- Normalized base triangle `T₀ = △((0,0), (1,0), (0,1))`. -/
private def T0 : Set (ℝ × ℝ) :=
  {y : ℝ × ℝ | 0 ≤ y.1 ∧ 0 ≤ y.2 ∧ y.1 + y.2 ≤ 1}

/-- Wedge subtriangle `T_a = {y ∈ T₀ : orient2D (0,0) a y ≥ 0}`. -/
private def Ta (a : ℝ × ℝ) : Set (ℝ × ℝ) :=
  {y ∈ T0 | 0 ≤ a.1 * y.2 - a.2 * y.1}

private lemma T0_eq_convexHull :
    T0 = convexHull ℝ ({(0, 0), (1, 0), (0, 1)} : Set (ℝ × ℝ)) := by
  ext z
  rw [← inClosedTri_iff_mem_convexHull]
  constructor
  · rintro ⟨hz1, hz2, hzsum⟩
    refine ⟨1 - z.1 - z.2, z.1, z.2, by linarith, hz1, hz2, by ring, by ring, by ring⟩
  · rintro ⟨μ₁, μ₂, μ₃, h1, h2, h3, hsum, hz1, hz2⟩
    refine ⟨by linarith, by linarith, by linarith⟩

private lemma Ta_convex (a : ℝ × ℝ) : Convex ℝ (Ta a) := by
  intro x hx y hy α β hα hβ hαβ
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · change 0 ≤ α * x.1 + β * y.1; nlinarith [hx.1.1, hy.1.1]
  · change 0 ≤ α * x.2 + β * y.2; nlinarith [hx.1.2.1, hy.1.2.1]
  · change (α * x.1 + β * y.1) + (α * x.2 + β * y.2) ≤ 1
    nlinarith [hx.1.2.2, hy.1.2.2]
  · change 0 ≤ a.1 * (α * x.2 + β * y.2) - a.2 * (α * x.1 + β * y.1)
    nlinarith [hx.2, hy.2]

/-- Claim 5.2 (`Ta`, `upper_9.tex` lines 506–516): `T_a ⊆ P`. -/
private lemma claim_Ta_subset_P {n : ℕ} {P : Set (ℝ × ℝ)}
    {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ}
    (hE : NormEnv P S w)
    {Tv Tq : Finset (Fin n)} {ia ip : Fin n}
    (hv_eq : w Tv = (0, 0)) (hq_eq : w Tq = (1, 0)) (hp_eq : S ip = (0, 1))
    (hvp : Sees P (0, 0) (0, 1)) (hqp : Sees P (1, 0) (0, 1))
    (ha1 : 0 < (S ia).1) (ha2 : 0 < (S ia).2)
    (hiv : Sees P (0, 0) (1, 0) ∨
      ∃ ie : Fin n, Sees P (0, 0) (S ie) ∧ Sees P (1, 0) (S ie) ∧
        0 < (S ie).2 ∧ 0 < (S ie).1 * (S ia).2 - (S ie).2 * (S ia).1) :
    Ta (S ia) ⊆ P := by
  rcases hiv with hvq | ⟨ie, hve, hqe, he2, hoea⟩
  · have hT0 : T0 ⊆ P := by
      rw [T0_eq_convexHull]
      exact hE.triangle_enclosure (0, 0) (by rw [← hv_eq]; exact hE.w_in_P Tv)
        (1, 0) (by rw [← hq_eq]; exact hE.w_in_P Tq)
        (0, 1) (by rw [← hp_eq]; exact hE.s_in_P ip) hvq hqp hvp
    exact fun y hy => hT0 hy.1
  · have he1 : 0 < (S ie).1 := by
      have : (S ie).2 * (S ia).1 < (S ie).1 * (S ia).2 := by linarith
      nlinarith
    have he_ne_p : S ie ≠ S ip := by
      intro h; rw [h, hp_eq] at he1; linarith
    have he_ne_q : S ie ≠ w Tq := hE.s_ne_w ie Tq
    have hp_ne_q : S ip ≠ w Tq := hE.s_ne_w ip Tq
    have h_not_col : orient2D (S ip) (w Tq) (S ie) ≠ 0 :=
      hE.no_three_collinear (S ip) (w Tq) (S ie)
        (Or.inl (Set.mem_range_self _)) (Or.inr (Set.mem_range_self _))
        (Or.inl (Set.mem_range_self _)) hp_ne_q he_ne_q.symm he_ne_p.symm
    have he_sum_ne : (S ie).1 + (S ie).2 ≠ 1 := by
      rw [hp_eq, hq_eq] at h_not_col
      unfold orient2D at h_not_col
      intro h1; apply h_not_col; linarith
    have he_sum_pos : 0 < (S ie).1 + (S ie).2 := add_pos he1 he2
    let xstar : ℝ × ℝ := ((S ie).1 / ((S ie).1 + (S ie).2), (S ie).2 / ((S ie).1 + (S ie).2))
    have hxstar_seg_qp : xstar ∈ segment ℝ (1, 0) (0, 1) := by
      refine mem_segment_of_coords ((S ie).2 / ((S ie).1 + (S ie).2))
        (div_nonneg (le_of_lt he2) (le_of_lt he_sum_pos))
        ((div_le_one he_sum_pos).mpr (by linarith)) ?_ ?_
      · dsimp [xstar]; field_simp [ne_of_gt he_sum_pos]; ring
      · dsimp [xstar]; ring
    have hxstar_in_P : xstar ∈ P := hqp hxstar_seg_qp
    have hTa_sub_xstar : ∀ y ∈ Ta (S ia),
        y ∈ convexHull ℝ ({(0, 0), xstar, (0, 1)} : Set (ℝ × ℝ)) := by
      intro y hy
      rw [← inClosedTri_iff_mem_convexHull]
      have hey : 0 ≤ (S ie).1 * y.2 - (S ie).2 * y.1 := by
        have h1 : (S ia).1 * ((S ie).1 * y.2 - (S ie).2 * y.1) =
            (S ie).1 * ((S ia).1 * y.2 - (S ia).2 * y.1) +
            ((S ie).1 * (S ia).2 - (S ie).2 * (S ia).1) * y.1 := by ring
        have h2 : 0 ≤ (S ia).1 * ((S ie).1 * y.2 - (S ie).2 * y.1) := by
          rw [h1]; exact add_nonneg (mul_nonneg (le_of_lt he1) hy.2)
            (mul_nonneg (le_of_lt hoea) hy.1.1)
        exact nonneg_of_mul_nonneg_right h2 ha1
      refine ⟨1 - y.1 - y.2, y.1 * ((S ie).1 + (S ie).2) / (S ie).1,
        y.2 - y.1 * (S ie).2 / (S ie).1,
        by linarith [hy.1.2.2],
        div_nonneg (mul_nonneg hy.1.1 (le_of_lt he_sum_pos)) (le_of_lt he1),
        by rw [sub_nonneg, div_le_iff₀ he1]; linarith,
        ?_, ?_, ?_⟩
      · field_simp [ne_of_gt he1]; ring
      · dsimp [xstar]; field_simp [ne_of_gt he1, ne_of_gt he_sum_pos]; ring
      · dsimp [xstar]; field_simp [ne_of_gt he1, ne_of_gt he_sum_pos]; ring
    rcases lt_or_gt_of_ne he_sum_ne with he_lt1 | he_gt1
    · -- Subcase 2b: `e ∈ T₀` (`e₁ + e₂ < 1`)
      have hep_left : InteriorOnLeft (S ie) (0, 1) [S ie, (0, 0), (0, 1)] := by
        apply interiorOnLeft_three
        unfold orient2D
        linarith
      have hep_right : InteriorOnRight (S ie) (0, 1) [S ie, (1, 0), (0, 1)] := by
        apply interiorOnRight_three
        unfold orient2D
        linarith
      have hep : Sees P (S ie) (0, 1) :=
        hE.two_path_enclosure (S ie) (0, 1) [S ie, (0, 0), (0, 1)] [S ie, (1, 0), (0, 1)]
          (by intro h; rw [h] at he1; linarith)
          (isPolygonalPathIn_three (sees_symm hve) hvp)
          (isPolygonalPathIn_three (sees_symm hqe) hqp)
          hep_left hep_right
      have htri1 : convexHull ℝ ({(0, 0), S ie, (0, 1)} : Set (ℝ × ℝ)) ⊆ P :=
        hE.triangle_enclosure (0, 0) (by rw [← hv_eq]; exact hE.w_in_P Tv)
          (S ie) (hE.s_in_P ie) (0, 1) (by rw [← hp_eq]; exact hE.s_in_P ip) hve hep hvp
      have htri2 : convexHull ℝ ({S ie, (1, 0), (0, 1)} : Set (ℝ × ℝ)) ⊆ P :=
        hE.triangle_enclosure (S ie) (hE.s_in_P ie)
          (1, 0) (by rw [← hq_eq]; exact hE.w_in_P Tq)
          (0, 1) (by rw [← hp_eq]; exact hE.s_in_P ip) (sees_symm hqe) hqp hep
      intro y hy
      have hey : 0 ≤ (S ie).1 * y.2 - (S ie).2 * y.1 := by
        have h1 : (S ia).1 * ((S ie).1 * y.2 - (S ie).2 * y.1) =
            (S ie).1 * ((S ia).1 * y.2 - (S ia).2 * y.1) +
            ((S ie).1 * (S ia).2 - (S ie).2 * (S ia).1) * y.1 := by ring
        have h2 : 0 ≤ (S ia).1 * ((S ie).1 * y.2 - (S ie).2 * y.1) := by
          rw [h1]; exact add_nonneg (mul_nonneg (le_of_lt he1) hy.2)
            (mul_nonneg (le_of_lt hoea) hy.1.1)
        exact nonneg_of_mul_nonneg_right h2 ha1
      by_cases hside : 0 ≤ (S ie).1 - (S ie).1 * y.2 - (1 - (S ie).2) * y.1
      · apply htri1
        rw [← inClosedTri_iff_mem_convexHull]
        refine ⟨1 - y.1 * (1 - (S ie).2) / (S ie).1 - y.2, y.1 / (S ie).1,
          y.2 - y.1 * (S ie).2 / (S ie).1,
          ?_, div_nonneg hy.1.1 (le_of_lt he1), ?_, ?_, ?_, ?_⟩
        · have heq : 1 - y.1 * (1 - (S ie).2) / (S ie).1 - y.2 =
              ((S ie).1 - (S ie).1 * y.2 - (1 - (S ie).2) * y.1) / (S ie).1 := by
            field_simp [ne_of_gt he1]; ring
          rw [heq]
          exact div_nonneg hside (le_of_lt he1)
        · rw [sub_nonneg, div_le_iff₀ he1]; linarith [hey]
        · field_simp [ne_of_gt he1]; ring
        · field_simp [ne_of_gt he1]; ring
        · field_simp [ne_of_gt he1]; ring
      · have hside' : (S ie).1 ≤ (S ie).1 * y.2 + (1 - (S ie).2) * y.1 := by linarith
        have heq_side : 0 ≤ (1 - (S ie).1) * y.2 + (S ie).2 * y.1 - (S ie).2 := by
          have hid : (S ie).1 * ((1 - (S ie).1) * y.2 + (S ie).2 * y.1 - (S ie).2) =
              (1 - (S ie).1 - (S ie).2) * ((S ie).1 * y.2 - (S ie).2 * y.1) +
              (S ie).2 * ((S ie).1 * y.2 + (1 - (S ie).2) * y.1 - (S ie).1) := by ring
          have hpos : 0 ≤ (S ie).1 * ((1 - (S ie).1) * y.2 + (S ie).2 * y.1 - (S ie).2) := by
            rw [hid]
            exact add_nonneg (mul_nonneg (by linarith) hey)
              (mul_nonneg (le_of_lt he2) (by linarith))
          exact nonneg_of_mul_nonneg_right hpos he1
        apply htri2
        rw [← inClosedTri_iff_mem_convexHull]
        have hden : 0 < 1 - (S ie).1 - (S ie).2 := by linarith
        refine ⟨(1 - y.1 - y.2) / (1 - (S ie).1 - (S ie).2),
          ((S ie).1 * y.2 + (1 - (S ie).2) * y.1 - (S ie).1) / (1 - (S ie).1 - (S ie).2),
          ((1 - (S ie).1) * y.2 + (S ie).2 * y.1 - (S ie).2) / (1 - (S ie).1 - (S ie).2),
          div_nonneg (by linarith [hy.1.2.2]) (le_of_lt hden),
          div_nonneg (by linarith) (le_of_lt hden),
          div_nonneg heq_side (le_of_lt hden),
          ?_, ?_, ?_⟩
        · field_simp [ne_of_gt hden]; ring
        · field_simp [ne_of_gt hden]; ring
        · field_simp [ne_of_gt hden]; ring
    · -- Subcase 2a: `e ∉ T₀` (`e₁ + e₂ > 1`)
      have hxstar_seg_ve : xstar ∈ segment ℝ (0, 0) (S ie) := by
        refine mem_segment_of_coords (1 / ((S ie).1 + (S ie).2))
          (div_nonneg zero_le_one (le_of_lt he_sum_pos))
          ((div_le_one he_sum_pos).mpr (le_of_lt he_gt1)) ?_ ?_
        · dsimp [xstar]; ring
        · dsimp [xstar]; ring
      have hvxstar : Sees P (0, 0) xstar :=
        sees_subsegment hve (left_mem_segment ℝ (0, 0) (S ie)) hxstar_seg_ve
      have hxstarp : Sees P xstar (0, 1) :=
        sees_subsegment hqp hxstar_seg_qp (right_mem_segment ℝ (1, 0) (0, 1))
      have htri : convexHull ℝ ({(0, 0), xstar, (0, 1)} : Set (ℝ × ℝ)) ⊆ P :=
        hE.triangle_enclosure (0, 0) (by rw [← hv_eq]; exact hE.w_in_P Tv)
          xstar hxstar_in_P (0, 1) (by rw [← hp_eq]; exact hE.s_in_P ip) hvxstar hxstarp hvp
      exact fun y hy => htri (hTa_sub_xstar y hy)

/-- Claim 5.3 (`coords`, `upper_9.tex` lines 520–543) in normalized coordinates. -/
private lemma claim_coords {n : ℕ} {P : Set (ℝ × ℝ)}
    {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ}
    (_hE : NormEnv P S w)
    {ia ic : Fin n}
    (hTa_sub : Ta (S ia) ⊆ P)
    (hva_not : ¬ Sees P (0, 0) (S ia))
    (ha1 : 0 < (S ia).1) (ha2 : 0 < (S ia).2)
    (hc1 : (S ic).1 < 0) (hc2 : 0 < (S ic).2)
    (hcross : SegmentsCross (0, 0) (0, 1) (S ia) (S ic)) :
    let a1 := (S ia).1; let a2 := (S ia).2
    let c1 := (S ic).1; let c2 := (S ic).2
    let z2 := c2 / (1 - c1)
    let lam := c2 / (c2 * a1 + (1 - c1) * a2)
    let d0 : ℝ × ℝ := (lam * a1, lam * a2)
    1 < a1 + a2 ∧
    c1 + c2 < 1 ∧
    -1 < (a2 - 1) / a1 ∧
    (a2 - 1) / a1 < (c2 - 1) / c1 ∧
    0 < z2 ∧ z2 < 1 ∧
    c2 < c2 * a1 + (1 - c1) * a2 ∧
    0 < lam ∧ lam < 1 ∧
    ((0 : ℝ), z2) ∈ segment ℝ ((0 : ℝ), (0 : ℝ)) ((0 : ℝ), (1 : ℝ)) ∧
    ((0 : ℝ), z2) ∈ segment ℝ ((1 : ℝ), (0 : ℝ)) (S ic) ∧
    d0 ∈ segment ℝ ((0 : ℝ), (0 : ℝ)) (S ia) ∧
    d0 ∈ segment ℝ ((1 : ℝ), (0 : ℝ)) (S ic) ∧
    d0 ∈ Ta (S ia) := by
  intro a1 a2 c1 c2 z2 lam d0
  have ha_sum : 1 < a1 + a2 := by
    by_contra hle
    have ha_mem : S ia ∈ Ta (S ia) := ⟨⟨le_of_lt ha1, le_of_lt ha2, not_lt.mp hle⟩, by ring_nf; rfl⟩
    have hv_mem : ((0 : ℝ), (0 : ℝ)) ∈ Ta (S ia) := ⟨⟨le_rfl, le_rfl, by norm_num⟩, by norm_num⟩
    exact hva_not (sees_of_convex_subset hTa_sub (Ta_convex (S ia)) hv_mem ha_mem)
  have hoacv : 0 < orient2D (S ia) (S ic) (0, 0) := by
    unfold orient2D
    nlinarith
  have hoacp : orient2D (S ia) (S ic) (0, 1) < 0 := by
    have hmul := hcross.2
    nlinarith
  have hapc : 0 < a1 * (1 - c2) - c1 * (1 - a2) := by
    have : orient2D (S ia) (S ic) (0, 1) = -(a1 * (1 - c2) - c1 * (1 - a2)) := by
      unfold orient2D; ring
    linarith
  have h1c1 : 0 < 1 - c1 := by linarith
  have hc_sum : c1 + c2 < 1 := by nlinarith
  have hsa_gt : -1 < (a2 - 1) / a1 := (lt_div_iff₀ ha1).mpr (by linarith)
  have hsa_lt_sc : (a2 - 1) / a1 < (c2 - 1) / c1 := by
    rw [← neg_div_neg_eq (c2 - 1) c1, div_lt_div_iff₀ ha1 (neg_pos.mpr hc1)]
    linarith
  have hz0 : 0 < z2 := div_pos hc2 h1c1
  have hz1 : z2 < 1 := (div_lt_one h1c1).mpr (by linarith)
  have ha_above : c2 < c2 * a1 + (1 - c1) * a2 := by nlinarith
  have hlam0 : 0 < lam := div_pos hc2 (lt_trans hc2 ha_above)
  have hlam1 : lam < 1 := (div_lt_one (lt_trans hc2 ha_above)).mpr ha_above
  have hz_vp : ((0 : ℝ), z2) ∈ segment ℝ ((0 : ℝ), (0 : ℝ)) ((0 : ℝ), (1 : ℝ)) :=
    mem_segment_of_coords z2 (le_of_lt hz0) (le_of_lt hz1) (by ring) (by ring)
  have hz_qc : ((0 : ℝ), z2) ∈ segment ℝ ((1 : ℝ), (0 : ℝ)) (S ic) := by
    refine mem_segment_of_coords (1 / (1 - c1))
      (div_nonneg zero_le_one (le_of_lt h1c1))
      ((div_le_one h1c1).mpr (by linarith)) ?_ ?_
    · change (0 : ℝ) = (1 - 1 / (1 - c1)) * 1 + (1 / (1 - c1)) * c1
      field_simp [ne_of_gt h1c1]; ring
    · change z2 = (1 - 1 / (1 - c1)) * 0 + (1 / (1 - c1)) * c2
      dsimp [z2]; ring
  have hd0_va : d0 ∈ segment ℝ ((0 : ℝ), (0 : ℝ)) (S ia) :=
    mem_segment_of_coords lam (le_of_lt hlam0) (le_of_lt hlam1)
      (by dsimp [d0]; ring) (by dsimp [d0]; ring)
  have hd0_qc : d0 ∈ segment ℝ ((1 : ℝ), (0 : ℝ)) (S ic) := by
    have hden : 0 < c2 * a1 + (1 - c1) * a2 := lt_trans hc2 ha_above
    have ht0 : 0 ≤ a2 / (c2 * a1 + (1 - c1) * a2) := div_nonneg (le_of_lt ha2) (le_of_lt hden)
    have ht1 : a2 / (c2 * a1 + (1 - c1) * a2) ≤ 1 :=
      (div_le_one hden).mpr (by nlinarith)
    refine mem_segment_of_coords (a2 / (c2 * a1 + (1 - c1) * a2)) ht0 ht1 ?_ ?_
    · dsimp [d0, lam]; field_simp [ne_of_gt hden]; ring
    · dsimp [d0, lam]; field_simp [ne_of_gt hden]; ring
  have hd0_Ta : d0 ∈ Ta (S ia) := by
    have hden : 0 < c2 * a1 + (1 - c1) * a2 := lt_trans hc2 ha_above
    have hd0_sum : d0.1 + d0.2 ≤ 1 := by
      dsimp [d0, lam]
      rw [← mul_add, div_mul_eq_mul_div, div_le_one hden]
      nlinarith
    refine ⟨⟨mul_nonneg (le_of_lt hlam0) (le_of_lt ha1),
      mul_nonneg (le_of_lt hlam0) (le_of_lt ha2), hd0_sum⟩, ?_⟩
    show 0 ≤ (S ia).1 * (lam * a2) - (S ia).2 * (lam * a1)
    dsimp [a1, a2]; ring_nf; rfl
  exact ⟨ha_sum, hc_sum, hsa_gt, hsa_lt_sc, hz0, hz1, ha_above, hlam0, hlam1,
    hz_vp, hz_qc, hd0_va, hd0_qc, hd0_Ta⟩

/-- Claim 5.4 (`witness-pos`, `upper_9.tex` lines 545–568) in normalized coordinates. -/
private lemma claim_witness_pos {n : ℕ} {P : Set (ℝ × ℝ)}
    {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ}
    (hE : NormEnv P S w)
    {Tv Tq : Finset (Fin n)} {ia ip ic : Fin n}
    (hv_eq : w Tv = (0, 0)) (hq_eq : w Tq = (1, 0)) (hp_eq : S ip = (0, 1))
    (hvp : Sees P (0, 0) (0, 1)) (hva_not : ¬ Sees P (0, 0) (S ia))
    (hvc_not : ¬ Sees P (0, 0) (S ic))
    (hqa : Sees P (1, 0) (S ia)) (hqc : Sees P (1, 0) (S ic)) (hqp : Sees P (1, 0) (0, 1))
    (hTa_sub : Ta (S ia) ⊆ P)
    (ha1 : 0 < (S ia).1) (ha2 : 0 < (S ia).2) (ha_sum : 1 < (S ia).1 + (S ia).2)
    (hc1 : (S ic).1 < 0) (hc2 : 0 < (S ic).2) (hc_sum : (S ic).1 + (S ic).2 < 1)
    {Tx : Finset (Fin n)} (hxa : Sees P (w Tx) (S ia)) (hxc : Sees P (w Tx) (S ic)) :
    orient2D (0, 0) (S ia) (w Tx) < 0 ∧
    0 < (w Tx).1 ∧
    (Sees P (w Tx) (0, 1) → ((w Tx).2 - 1) / (w Tx).1 < ((S ia).2 - 1) / (S ia).1) := by
  let a := S ia
  let c := S ic
  let x := w Tx
  have hxa' : Sees P x a := hxa
  have hxc' : Sees P x c := hxc
  have hv_mem : ((0 : ℝ), (0 : ℝ)) ∈ Ta a := ⟨⟨le_rfl, le_rfl, by norm_num⟩, by norm_num⟩
  have hden_pos : 0 < c.2 * a.1 + (1 - c.1) * a.2 := by nlinarith
  let lam := c.2 / (c.2 * a.1 + (1 - c.1) * a.2)
  have hlam0 : 0 < lam := div_pos hc2 hden_pos
  have hlam1 : lam < 1 := (div_lt_one hden_pos).mpr (by nlinarith)
  let d0 : ℝ × ℝ := (lam * a.1, lam * a.2)
  have hd0_va : d0 ∈ segment ℝ (0, 0) a :=
    mem_segment_of_coords lam (le_of_lt hlam0) (le_of_lt hlam1) (by dsimp [d0]; ring) (by dsimp [d0]; ring)
  have hd0_qc : d0 ∈ segment ℝ (1, 0) c := by
    have ht0 : 0 ≤ a.2 / (c.2 * a.1 + (1 - c.1) * a.2) := div_nonneg (le_of_lt ha2) (le_of_lt hden_pos)
    have ht1 : a.2 / (c.2 * a.1 + (1 - c.1) * a.2) ≤ 1 := (div_le_one hden_pos).mpr (by nlinarith)
    refine mem_segment_of_coords (a.2 / (c.2 * a.1 + (1 - c.1) * a.2)) ht0 ht1 ?_ ?_
    · dsimp [d0, lam]; field_simp [ne_of_gt hden_pos]; ring
    · dsimp [d0, lam]; field_simp [ne_of_gt hden_pos]; ring
  have hd0_Ta : d0 ∈ Ta a := by
    have hd0_sum : d0.1 + d0.2 ≤ 1 := by
      dsimp [d0, lam]
      rw [← mul_add, div_mul_eq_mul_div, div_le_one hden_pos]
      nlinarith
    refine ⟨⟨mul_nonneg (le_of_lt hlam0) (le_of_lt ha1),
      mul_nonneg (le_of_lt hlam0) (le_of_lt ha2), hd0_sum⟩, ?_⟩
    show 0 ≤ a.1 * (lam * a.2) - a.2 * (lam * a.1)
    ring_nf; rfl
  have hvd0 : Sees P (0, 0) d0 := sees_of_convex_subset hTa_sub (Ta_convex a) hv_mem hd0_Ta
  have hqd0 : Sees P (1, 0) d0 := sees_subsegment hqc (left_mem_segment ℝ (1, 0) c) hd0_qc
  have hcd0 : Sees P c d0 := sees_subsegment (sees_symm hqc) (left_mem_segment ℝ c (1, 0))
    (by rw [segment_symm]; exact hd0_qc)
  -- (a) `orient2D (0, 0) a x < 0`
  have ha_part : orient2D (0, 0) a x < 0 := by
    by_contra hle
    have hge : 0 ≤ orient2D (0, 0) a x := not_lt.mp hle
    have hx_ne_v : x ≠ (0, 0) := by
      intro h; apply hva_not; rw [← h]; exact hxa'
    have hx_ne_a : x ≠ a := (hE.s_ne_w ia Tx).symm
    have hv_ne_a : (0, 0) ≠ a := by rw [← hv_eq]; exact (hE.s_ne_w ia Tv).symm
    have hne0 : orient2D (0, 0) a x ≠ 0 := by
      rw [← hv_eq]
      exact hE.no_three_collinear (w Tv) (S ia) (w Tx)
        (Or.inr (Set.mem_range_self _)) (Or.inl (Set.mem_range_self _))
        (Or.inr (Set.mem_range_self _)) (hE.s_ne_w ia Tv).symm (hE.s_ne_w ia Tx)
        (fun h => hx_ne_v (by rw [← hv_eq, h]))
    have hpos : 0 < orient2D (0, 0) a x := lt_of_le_of_ne hge (Ne.symm hne0)
    have ha_ne_d0 : a ≠ d0 := by
      intro h
      have := congrArg Prod.fst h
      dsimp [d0] at this
      nlinarith
    have ho_ad0_q : 0 < orient2D a d0 (1, 0) := by
      unfold orient2D; dsimp [d0]; nlinarith
    have ho_ad0_x : orient2D a d0 x < 0 := by
      have h1 : orient2D a d0 x = -(1 - lam) * orient2D (0, 0) a x := by
        unfold orient2D; dsimp [d0]; ring
      rw [h1]; nlinarith
    have ho_ad0_c : orient2D a d0 c < 0 := by
      have h1 : orient2D a d0 c = -(1 - lam) * (a.1 * c.2 - a.2 * c.1) := by
        unfold orient2D; dsimp [d0]; ring
      have hoac : 0 < a.1 * c.2 - a.2 * c.1 := by nlinarith
      have h1mlam : 0 < 1 - lam := by linarith
      rw [h1]; nlinarith
    have had0 : Sees P a d0 :=
      hE.two_path_enclosure a d0 [a, (1, 0), d0] [a, x, c, d0]
        ha_ne_d0
        (isPolygonalPathIn_three (sees_symm hqa) hqd0)
        (isPolygonalPathIn_four (sees_symm hxa') hxc' hcd0)
        (interiorOnLeft_three ho_ad0_q)
        (interiorOnRight_four ho_ad0_x ho_ad0_c)
    exact hva_not (sees_of_mem_segment hd0_va hvd0 (sees_symm had0))
  -- (b) `0 < x.1`
  have hb_part : 0 < x.1 := by
    have hx_ne_0 : x.1 ≠ 0 := by
      intro hx0
      have hx_ne_v : x ≠ (0, 0) := fun h => hva_not (by rw [← h]; exact hxa')
      have hx_ne_p : x ≠ (0, 1) := by rw [← hp_eq]; exact (hE.s_ne_w ip Tx).symm
      have hv_ne_p : (0, 0) ≠ (0, 1) := by intro h; have := congrArg Prod.snd h; norm_num at this
      have hne0 : orient2D (0, 0) (0, 1) x ≠ 0 := by
        rw [← hv_eq, ← hp_eq]
        exact hE.no_three_collinear (w Tv) (S ip) (w Tx)
          (Or.inr (Set.mem_range_self _)) (Or.inl (Set.mem_range_self _))
          (Or.inr (Set.mem_range_self _)) (hE.s_ne_w ip Tv).symm (hE.s_ne_w ip Tx)
          (fun h => hx_ne_v (by rw [← hv_eq, h]))
      apply hne0
      unfold orient2D
      rw [hx0]
      ring
    by_contra hle
    have hx1 : x.1 < 0 := lt_of_le_of_ne (not_lt.mp hle) hx_ne_0
    have ho_ax : a.1 * x.2 - a.2 * x.1 < 0 := by simpa [orient2D] using ha_part
    have hx2 : x.2 < 0 := by nlinarith
    have ha1_mx1 : 0 < a.1 - x.1 := by linarith
    let y : ℝ × ℝ := (0, (a.1 * x.2 - a.2 * x.1) / (a.1 - x.1))
    have hy2 : y.2 < 0 := div_neg_of_neg_of_pos ho_ax ha1_mx1
    have hy_ax : y ∈ segment ℝ x a := by
      refine mem_segment_of_coords (-x.1 / (a.1 - x.1))
        (div_nonneg (by linarith) (le_of_lt ha1_mx1))
        ((div_le_one ha1_mx1).mpr (by linarith)) ?_ ?_
      · dsimp [y]; field_simp [ne_of_gt ha1_mx1]; ring
      · dsimp [y]; field_simp [ne_of_gt ha1_mx1]; ring
    have hyx : Sees P y x :=
      sees_symm (sees_subsegment hxa' (left_mem_segment ℝ x a) hy_ax)
    have hya : Sees P y a := sees_subsegment hxa' hy_ax (right_mem_segment ℝ x a)
    let z2 := c.2 / (1 - c.1)
    have h1c1 : 0 < 1 - c.1 := by linarith
    have hz0 : 0 < z2 := div_pos hc2 h1c1
    have hz1 : z2 < 1 := (div_lt_one h1c1).mpr (by linarith)
    let z : ℝ × ℝ := (0, z2)
    have hz_vp : z ∈ segment ℝ (0, 0) (0, 1) :=
      mem_segment_of_coords z2 (le_of_lt hz0) (le_of_lt hz1) (by ring) (by ring)
    have hz_qc : z ∈ segment ℝ (1, 0) c := by
      refine mem_segment_of_coords (1 / (1 - c.1))
        (div_nonneg zero_le_one (le_of_lt h1c1))
        ((div_le_one h1c1).mpr (by linarith)) ?_ ?_
      · change (0 : ℝ) = (1 - 1 / (1 - c.1)) * 1 + (1 / (1 - c.1)) * c.1
        field_simp [ne_of_gt h1c1]; ring
      · change z2 = (1 - 1 / (1 - c.1)) * 0 + (1 / (1 - c.1)) * c.2
        dsimp [z2]; ring
    have hcz : Sees P c z := sees_subsegment (sees_symm hqc) (left_mem_segment ℝ c (1, 0))
      (by rw [segment_symm]; exact hz_qc)
    have hqz : Sees P (1, 0) z := sees_subsegment hqc (left_mem_segment ℝ (1, 0) c) hz_qc
    have hvz : Sees P (0, 0) z := sees_subsegment hvp (left_mem_segment ℝ (0, 0) (0, 1)) hz_vp
    have hy_ne_z : y ≠ z := by
      intro h; have := congrArg Prod.snd h; dsimp [y, z] at this; linarith
    have hoyz_x : 0 < orient2D y z x := by
      unfold orient2D; dsimp [y, z]; nlinarith
    have hoyz_c : 0 < orient2D y z c := by
      unfold orient2D; dsimp [y, z]; nlinarith
    have hoyz_a : orient2D y z a < 0 := by
      unfold orient2D; dsimp [y, z]; nlinarith
    have hoyz_q : orient2D y z (1, 0) < 0 := by
      unfold orient2D; dsimp [y, z]; nlinarith
    have hyz : Sees P y z :=
      hE.two_path_enclosure y z [y, x, c, z] [y, a, (1, 0), z]
        hy_ne_z
        (isPolygonalPathIn_four hyx hxc' hcz)
        (isPolygonalPathIn_four hya (sees_symm hqa) hqz)
        (interiorOnLeft_four hoyz_x hoyz_c)
        (interiorOnRight_four hoyz_a hoyz_q)
    have hv_yz : (0, 0) ∈ segment ℝ y z := by
      have hden : 0 < z.2 - y.2 := by dsimp [z]; linarith
      have hlin : (1 - (-y.2 / (z.2 - y.2))) * y.2 + (-y.2 / (z.2 - y.2)) * z.2 = 0 := by
        field_simp [ne_of_gt hden]; ring
      refine mem_segment_of_coords (-y.2 / (z.2 - y.2))
        (div_nonneg (by linarith) (le_of_lt hden))
        ((div_le_one hden).mpr (by dsimp [z]; linarith))
        (by dsimp [y, z]; ring) hlin.symm
    have hyv : Sees P y (0, 0) :=
      sees_subsegment hyz (left_mem_segment ℝ y z) hv_yz
    have hc_ne_v : c ≠ (0, 0) := by
      rw [← hv_eq]; exact hE.s_ne_w ic Tv
    have hocv_x : orient2D c (0, 0) x < 0 := by
      unfold orient2D; nlinarith
    have hocv_y : orient2D c (0, 0) y < 0 := by
      unfold orient2D; dsimp [y]; nlinarith
    have hocv_z : 0 < orient2D c (0, 0) z := by
      unfold orient2D; dsimp [z]; nlinarith
    have hcv : Sees P c (0, 0) :=
      hE.two_path_enclosure c (0, 0) [c, z, (0, 0)] [c, x, y, (0, 0)]
        hc_ne_v
        (isPolygonalPathIn_three hcz (sees_symm hvz))
        (isPolygonalPathIn_four (sees_symm hxc') (sees_symm hyx) hyv)
        (interiorOnLeft_three hocv_z)
        (interiorOnRight_four hocv_x hocv_y)
    exact hvc_not (sees_symm hcv)
  -- (c) `Sees P x (0, 1) → s(x) < s_a`
  refine ⟨ha_part, hb_part, fun hxp => ?_⟩
  rw [div_lt_div_iff₀ hb_part ha1]
  by_contra hle
  have hge : 0 ≤ (x.2 - 1) * a.1 - (a.2 - 1) * x.1 := by linarith
  have hne0 : orient2D (0, 1) a x ≠ 0 := by
    rw [← hp_eq]
    have hp_ne_a : S ip ≠ S ia := fun h =>
      hva_not (by rw [← h, hp_eq]; exact hvp)
    exact hE.no_three_collinear (S ip) (S ia) (w Tx)
      (Or.inl (Set.mem_range_self _)) (Or.inl (Set.mem_range_self _))
      (Or.inr (Set.mem_range_self _)) hp_ne_a (hE.s_ne_w ia Tx) (hE.s_ne_w ip Tx)
  have hopax : 0 < orient2D (0, 1) a x := by
    have : orient2D (0, 1) a x = a.1 * (x.2 - 1) - (a.2 - 1) * x.1 := by unfold orient2D; ring
    have hne : a.1 * (x.2 - 1) - (a.2 - 1) * x.1 ≠ 0 := by rw [← this]; exact hne0
    rw [this]; exact lt_of_le_of_ne (by linarith) (Ne.symm hne)
  have hopaq : orient2D (0, 1) a (1, 0) < 0 := by
    have : orient2D (0, 1) a (1, 0) = 1 - (a.1 + a.2) := by unfold orient2D; ring
    linarith
  have hp_ne_a : (0, 1) ≠ a := fun h => by
    have := congrArg Prod.fst h; linarith
  have hpa : Sees P (0, 1) a :=
    hE.two_path_enclosure (0, 1) a [(0, 1), x, a] [(0, 1), (1, 0), a]
      hp_ne_a
      (isPolygonalPathIn_three (sees_symm hxp) hxa')
      (isPolygonalPathIn_three (sees_symm hqp) hqa)
      (interiorOnLeft_three hopax)
      (interiorOnRight_three hopaq)
  have htri_pqa : convexHull ℝ ({(0, 1), (1, 0), a} : Set (ℝ × ℝ)) ⊆ P :=
    hE.triangle_enclosure (0, 1) (by rw [← hp_eq]; exact hE.s_in_P ip)
      (1, 0) (by rw [← hq_eq]; exact hE.w_in_P Tq)
      a (hE.s_in_P ia) (sees_symm hqp) hqa hpa
  let m : ℝ × ℝ := (a.1 / (a.1 + a.2), a.2 / (a.1 + a.2))
  have hm_va : m ∈ segment ℝ (0, 0) a :=
    mem_segment_of_coords (1 / (a.1 + a.2))
      (div_nonneg zero_le_one (by linarith))
      ((div_le_one (by linarith)).mpr (by linarith))
      (by dsimp [m]; ring) (by dsimp [m]; ring)
  have hm_Ta : m ∈ Ta a := by
    refine ⟨⟨div_nonneg (le_of_lt ha1) (by linarith), div_nonneg (le_of_lt ha2) (by linarith),
      ?_⟩, ?_⟩
    · dsimp [m]; field_simp [ne_of_gt (by linarith : 0 < a.1 + a.2)]; linarith
    · dsimp [m]; field_simp [ne_of_gt (by linarith : 0 < a.1 + a.2)]; ring_nf; norm_num
  have hvm : Sees P (0, 0) m := sees_of_convex_subset hTa_sub (Ta_convex a) hv_mem hm_Ta
  have hm_tri : m ∈ convexHull ℝ ({(0, 1), (1, 0), a} : Set (ℝ × ℝ)) := by
    rw [← inClosedTri_iff_mem_convexHull]
    refine ⟨a.2 / (a.1 + a.2), a.1 / (a.1 + a.2), 0,
      div_nonneg (le_of_lt ha2) (by linarith),
      div_nonneg (le_of_lt ha1) (by linarith), le_rfl,
      ?_, ?_, ?_⟩
    · field_simp [ne_of_gt (by linarith : 0 < a.1 + a.2)]; ring
    · dsimp [m]; field_simp [ne_of_gt (by linarith : 0 < a.1 + a.2)]; ring
    · dsimp [m]; field_simp [ne_of_gt (by linarith : 0 < a.1 + a.2)]; ring
  have ha_tri : a ∈ convexHull ℝ ({(0, 1), (1, 0), a} : Set (ℝ × ℝ)) :=
    subset_convexHull ℝ _ (by simp)
  have hma : Sees P m a := sees_of_convex_subset htri_pqa (convex_convexHull ℝ _) hm_tri ha_tri
  exact hva_not (sees_of_mem_segment hm_va hvm hma)

/-- Claim 5.5 (`monotone-slope`, `upper_9.tex` lines 570–583) in normalized coordinates. -/
private lemma claim_monotone_slope {n : ℕ} {P : Set (ℝ × ℝ)}
    {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ}
    (hE : NormEnv P S w)
    {ia ic : Fin n}
    (hvp : Sees P (0, 0) (0, 1))
    (hqa : Sees P (1, 0) (S ia)) (hqc : Sees P (1, 0) (S ic)) (hqp : Sees P (1, 0) (0, 1))
    (ha1 : 0 < (S ia).1) (hc1 : (S ic).1 < 0) (hc2 : 0 < (S ic).2)
    (hc_sum : (S ic).1 + (S ic).2 < 1)
    (hsa_gt : -1 < ((S ia).2 - 1) / (S ia).1)
    (hsa_lt_sc : ((S ia).2 - 1) / (S ia).1 < ((S ic).2 - 1) / (S ic).1)
    {u : ℝ × ℝ} (hu1 : 0 < u.1) (hup : Sees P u (0, 1)) (hua : Sees P u (S ia))
    (hsu_lt_sa : (u.2 - 1) / u.1 < ((S ia).2 - 1) / (S ia).1)
    {x : ℝ × ℝ} (hx1 : 0 < x.1) (hxa : Sees P x (S ia)) (hxc : Sees P x (S ic))
    (hsx_lt_su : (x.2 - 1) / x.1 < (u.2 - 1) / u.1)
    (hsx_ne : (x.2 - 1) / x.1 ≠ -1) :
    Sees P x (0, 1) := by
  let a := S ia
  let c := S ic
  have hp_ne_x : (0, 1) ≠ x := fun h => by
    have := congrArg Prod.fst h; linarith
  rcases lt_or_gt_of_ne hsx_ne with hsx_lt | hsx_gt
  · -- Case 1: `s(x) < -1`
    let z2 := c.2 / (1 - c.1)
    have h1c1 : 0 < 1 - c.1 := by linarith
    have hz0 : 0 < z2 := div_pos hc2 h1c1
    have hz1 : z2 < 1 := (div_lt_one h1c1).mpr (by linarith)
    let z : ℝ × ℝ := (0, z2)
    have hz_vp : z ∈ segment ℝ (0, 0) (0, 1) :=
      mem_segment_of_coords z2 (le_of_lt hz0) (le_of_lt hz1) (by ring) (by ring)
    have hz_qc : z ∈ segment ℝ (1, 0) c := by
      refine mem_segment_of_coords (1 / (1 - c.1))
        (div_nonneg zero_le_one (le_of_lt h1c1))
        ((div_le_one h1c1).mpr (by linarith)) ?_ ?_
      · change (0 : ℝ) = (1 - 1 / (1 - c.1)) * 1 + (1 / (1 - c.1)) * c.1
        field_simp [ne_of_gt h1c1]; ring
      · change z2 = (1 - 1 / (1 - c.1)) * 0 + (1 / (1 - c.1)) * c.2
        dsimp [z2]; ring
    have hpz : Sees P (0, 1) z :=
      sees_subsegment (sees_symm hvp) (left_mem_segment ℝ (0, 1) (0, 0))
        (by rw [segment_symm]; exact hz_vp)
    have hzc : Sees P z c :=
      sees_subsegment hqc hz_qc (right_mem_segment ℝ (1, 0) c)
    have ho_q : 0 < orient2D (0, 1) x (1, 0) := by
      have hmx : x.2 - 1 < -1 * x.1 := (div_lt_iff₀ hx1).mp hsx_lt
      unfold orient2D; linarith
    have ho_a : 0 < orient2D (0, 1) x a := by
      have hlt : (x.2 - 1) / x.1 < (a.2 - 1) / a.1 := lt_trans hsx_lt hsa_gt
      have hmul : (x.2 - 1) * a.1 < (a.2 - 1) * x.1 := (div_lt_div_iff₀ hx1 ha1).mp hlt
      unfold orient2D; linarith
    have ho_z : orient2D (0, 1) x z < 0 := by
      unfold orient2D; dsimp [z]; nlinarith
    have ho_c : orient2D (0, 1) x c < 0 := by
      have hlt : (x.2 - 1) / x.1 < (c.2 - 1) / c.1 := lt_trans hsx_lt (lt_trans hsa_gt hsa_lt_sc)
      rw [← neg_div_neg_eq (c.2 - 1) c.1, div_lt_div_iff₀ hx1 (neg_pos.mpr hc1)] at hlt
      unfold orient2D; linarith
    exact sees_symm <|
      hE.two_path_enclosure (0, 1) x [(0, 1), (1, 0), a, x] [(0, 1), z, c, x]
        hp_ne_x
        (isPolygonalPathIn_four (sees_symm hqp) hqa (sees_symm hxa))
        (isPolygonalPathIn_four hpz hzc (sees_symm hxc))
        (interiorOnLeft_four ho_q ho_a)
        (interiorOnRight_four ho_z ho_c)
  · -- Case 2: `-1 < s(x) < s(u)`
    have ho_u : 0 < orient2D (0, 1) x u := by
      have hmul : (x.2 - 1) * u.1 < (u.2 - 1) * x.1 := (div_lt_div_iff₀ hx1 hu1).mp hsx_lt_su
      unfold orient2D; linarith
    have ho_a : 0 < orient2D (0, 1) x a := by
      have hlt : (x.2 - 1) / x.1 < (a.2 - 1) / a.1 := lt_trans hsx_lt_su hsu_lt_sa
      have hmul : (x.2 - 1) * a.1 < (a.2 - 1) * x.1 := (div_lt_div_iff₀ hx1 ha1).mp hlt
      unfold orient2D; linarith
    have ho_q : orient2D (0, 1) x (1, 0) < 0 := by
      have hmx : -1 * x.1 < x.2 - 1 := (lt_div_iff₀ hx1).mp hsx_gt
      unfold orient2D; linarith
    have ho_c : orient2D (0, 1) x c < 0 := by
      have hlt : (x.2 - 1) / x.1 < (c.2 - 1) / c.1 :=
        lt_trans (lt_trans hsx_lt_su hsu_lt_sa) hsa_lt_sc
      rw [← neg_div_neg_eq (c.2 - 1) c.1, div_lt_div_iff₀ hx1 (neg_pos.mpr hc1)] at hlt
      unfold orient2D; linarith
    exact sees_symm <|
      hE.two_path_enclosure (0, 1) x [(0, 1), u, a, x] [(0, 1), (1, 0), c, x]
        hp_ne_x
        (isPolygonalPathIn_four (sees_symm hup) hua (sees_symm hxa))
        (isPolygonalPathIn_four (sees_symm hqp) hqc (sees_symm hxc))
        (interiorOnLeft_four ho_u ho_a)
        (interiorOnRight_four ho_q ho_c)

/-! ## 5. Complete Half-Plane Lemma (`upper_9.tex`, Lemma 5.1) -/

/-- Normalized proof of Lemma 5.1 inside `NormEnv`. -/
private lemma half_plane_lemma_norm {n : ℕ} {P : Set (ℝ × ℝ)}
    {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ}
    (hE : NormEnv P S w)
    {Tv Tq : Finset (Fin n)} {ia ip ic : Fin n}
    (hv_eq : w Tv = (0, 0)) (hq_eq : w Tq = (1, 0)) (hp_eq : S ip = (0, 1))
    (hvp : Sees P (0, 0) (0, 1))
    (hva_not : ¬ Sees P (0, 0) (S ia)) (hvc_not : ¬ Sees P (0, 0) (S ic))
    (hqa : Sees P (1, 0) (S ia)) (hqp : Sees P (1, 0) (0, 1)) (hqc : Sees P (1, 0) (S ic))
    (ha1 : 0 < (S ia).1) (ha2 : 0 < (S ia).2)
    (hc1 : (S ic).1 < 0) (hc2 : 0 < (S ic).2)
    (hcross : SegmentsCross (0, 0) (0, 1) (S ia) (S ic))
    (hiv : Sees P (0, 0) (1, 0) ∨
      ∃ ie : Fin n, Sees P (0, 0) (S ie) ∧ Sees P (1, 0) (S ie) ∧
        0 < (S ie).2 ∧ 0 < (S ie).1 * (S ia).2 - (S ie).2 * (S ia).1) :
    ∃ H : OpenHalfPlane,
      IsHalfPlaneTest P (WitnessSet {ia, ic} ∅ w) (0, 1) H ∧
      H.n.1 * 0 + H.n.2 * 1 + H.c = 0 ∧
      H.MemPos (0, 0) ∧
      H.MemPos (1, 0) ∧
      H.MemNeg (S ia) ∧
      H.MemPos (S ic) ∧
      (∀ x ∈ WitnessSet {ia, ic} ∅ w, 0 < x.1 ∧ orient2D (0, 0) (S ia) x < 0) := by
  have hTa_sub : Ta (S ia) ⊆ P :=
    claim_Ta_subset_P hE hv_eq hq_eq hp_eq hvp hqp ha1 ha2 hiv
  have hcoords := claim_coords hE hTa_sub hva_not ha1 ha2 hc1 hc2 hcross
  rcases hcoords with ⟨ha_sum, hc_sum, hsa_gt, hsa_lt_sc, _, _, _, _, _, _, _, _, _, _⟩
  let sa : ℝ := ((S ia).2 - 1) / (S ia).1
  let sc : ℝ := ((S ic).2 - 1) / (S ic).1
  let slope : ℝ × ℝ → ℝ := fun x => (x.2 - 1) / x.1
  have hW_ac : ∀ T : Finset (Fin n), {ia, ic} ⊆ T →
      orient2D (0, 0) (S ia) (w T) < 0 ∧ 0 < (w T).1 ∧
      (Sees P (w T) (0, 1) → slope (w T) < sa) := by
    intro T hT
    have hxa : Sees P (w T) (S ia) := (hE.shatters T ia).mpr (hT (by simp))
    have hxc : Sees P (w T) (S ic) := (hE.shatters T ic).mpr (hT (by simp))
    exact claim_witness_pos hE hv_eq hq_eq hp_eq hvp hva_not hvc_not hqa hqc hqp hTa_sub
      ha1 ha2 ha_sum hc1 hc2 hc_sum hxa hxc
  let Wacp : Finset (Finset (Fin n)) :=
    Finset.univ.filter (fun T => {ia, ic, ip} ⊆ T)
  have hTq_mem : Tq ∈ Wacp := by
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, fun i hi => ?_⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with h | h | h
    · rw [h]; exact (hE.shatters Tq ia).mp (by rwa [hq_eq])
    · rw [h]; exact (hE.shatters Tq ic).mp (by rwa [hq_eq])
    · rw [h]; exact (hE.shatters Tq ip).mp (by rwa [hq_eq, hp_eq])
  obtain ⟨Tcirc, hTcirc_mem, hTcirc_max⟩ :=
    Finset.exists_max_image Wacp (fun T => slope (w T)) ⟨Tq, hTq_mem⟩
  have hTcirc_sub : {ia, ic} ⊆ Tcirc := by
    rw [Finset.mem_filter] at hTcirc_mem
    intro i hi; apply hTcirc_mem.2; simp only [Finset.mem_insert, Finset.mem_singleton] at hi ⊢
    rcases hi with rfl | rfl <;> simp
  have hTcirc_p : ip ∈ Tcirc := by
    rw [Finset.mem_filter] at hTcirc_mem
    exact hTcirc_mem.2 (by simp)
  have hxcirc_pos : 0 < (w Tcirc).1 := (hW_ac Tcirc hTcirc_sub).2.1
  have hxcirc_lt_sa : slope (w Tcirc) < sa :=
    (hW_ac Tcirc hTcirc_sub).2.2 (by rw [← hp_eq]; exact (hE.shatters Tcirc ip).mpr hTcirc_p)
  have hxcirc_ge_m1 : -1 ≤ slope (w Tcirc) := by
    have h := hTcirc_max Tq hTq_mem
    have hsq : slope (w Tq) = -1 := by dsimp [slope]; rw [hq_eq]; norm_num
    linarith
  let Wac : Finset (Finset (Fin n)) :=
    Finset.univ.filter (fun T => {ia, ic} ⊆ T)
  let Sgt : Finset ℝ :=
    (Wac.filter (fun T => slope (w Tcirc) < slope (w T))).image (fun T => slope (w T))
  let mup : ℝ := (insert sa Sgt).min' (Finset.insert_nonempty sa Sgt)
  have hmup_gt : slope (w Tcirc) < mup := by
    rw [Finset.lt_min'_iff]
    intro r hr
    rw [Finset.mem_insert] at hr
    rcases hr with rfl | hr
    · exact hxcirc_lt_sa
    · rw [Finset.mem_image] at hr
      rcases hr with ⟨T, hT, rfl⟩
      rw [Finset.mem_filter] at hT
      exact hT.2
  have hmup_le_sa : mup ≤ sa := Finset.min'_le _ _ (Finset.mem_insert_self sa Sgt)
  obtain ⟨ε, hε, hnbhd⟩ := hE.open_vis_nbhd Tcirc ⟨ip, hTcirc_p⟩
  let η : ℝ := min (ε / 2) ((w Tcirc).1 * (mup - slope (w Tcirc)) / 2)
  have hη_pos : 0 < η := lt_min (by linarith) (div_pos (mul_pos hxcirc_pos (sub_pos.mpr hmup_gt)) two_pos)
  let u : ℝ × ℝ := ((w Tcirc).1, (w Tcirc).2 + η)
  have hu_dist : dist u (w Tcirc) < ε := by
    rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
    dsimp [u]
    simp only [sub_self, abs_zero, add_sub_cancel_left, abs_of_pos hη_pos]
    exact max_lt hε (lt_of_le_of_lt (min_le_left _ _) (by linarith))
  obtain ⟨_, hu_sees⟩ := hnbhd u hu_dist
  have hu1 : 0 < u.1 := hxcirc_pos
  have hua : Sees P u (S ia) := hu_sees ia (hTcirc_sub (by simp))
  have hup : Sees P u (0, 1) := by rw [← hp_eq]; exact hu_sees ip hTcirc_p
  have hsu_eq : slope u = slope (w Tcirc) + η / (w Tcirc).1 := by
    dsimp [slope, u]
    field_simp [ne_of_gt hxcirc_pos]
    ring
  have hsu_gt_xcirc : slope (w Tcirc) < slope u := by
    rw [hsu_eq]
    linarith [div_pos hη_pos hxcirc_pos]
  have hsu_lt_mup : slope u < mup := by
    rw [hsu_eq]
    have hη_le : η ≤ (w Tcirc).1 * (mup - slope (w Tcirc)) / 2 := min_le_right _ _
    have hdiv : η / (w Tcirc).1 ≤ (mup - slope (w Tcirc)) / 2 :=
      (div_le_iff₀ hxcirc_pos).mpr (by linarith)
    linarith [sub_pos.mpr hmup_gt]
  have hsu_lt_sa : slope u < sa := lt_of_lt_of_le hsu_lt_mup hmup_le_sa
  have hsu_gt_m1 : -1 < slope u := lt_of_le_of_lt hxcirc_ge_m1 hsu_gt_xcirc
  let H : OpenHalfPlane :=
    { n := (slope u, -1)
      c := 1
      hn := Or.inr (by norm_num) }
  refine ⟨H, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    rcases hx with ⟨T, hT, _, rfl⟩
    have hT' : {ia, ic} ⊆ T := hT
    have hx1 : 0 < (w T).1 := (hW_ac T hT').2.1
    have hpos_iff : H.MemPos (w T) ↔ slope (w T) < slope u := by
      dsimp [OpenHalfPlane.MemPos, H, slope]
      rw [div_lt_iff₀ hx1]
      constructor <;> intro h <;> linarith
    have hneg_iff : H.MemNeg (w T) ↔ slope u < slope (w T) := by
      dsimp [OpenHalfPlane.MemNeg, H, slope]
      rw [lt_div_iff₀ hx1]
      constructor <;> intro h <;> linarith
    have h_ne : slope (w T) ≠ slope u := by
      rcases le_or_gt (slope (w T)) (slope (w Tcirc)) with hle | hgt
      · exact ne_of_lt (lt_of_le_of_lt hle hsu_gt_xcirc)
      · have hmem_Sgt : slope (w T) ∈ Sgt := by
          rw [Finset.mem_image]
          refine ⟨T, ?_, rfl⟩
          rw [Finset.mem_filter]
          exact ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hT'⟩, hgt⟩
        have hmup_le : mup ≤ slope (w T) := Finset.min'_le _ _ (Finset.mem_insert_of_mem hmem_Sgt)
        exact ne_of_gt (lt_of_lt_of_le hsu_lt_mup hmup_le)
    constructor
    · rw [hpos_iff, hneg_iff]
      exact lt_or_gt_of_ne h_ne
    · rw [hpos_iff]
      constructor
      · intro hxp
        have hT_acp : T ∈ Wacp := by
          rw [Finset.mem_filter]
          refine ⟨Finset.mem_univ _, fun i hi => ?_⟩
          simp only [Finset.mem_insert, Finset.mem_singleton] at hi
          rcases hi with h | h | h
          · rw [h]; exact hT' (by simp)
          · rw [h]; exact hT' (by simp)
          · rw [h]
            rw [← hp_eq] at hxp
            exact (hE.shatters T ip).mp hxp
        exact lt_of_le_of_lt (hTcirc_max T hT_acp) hsu_gt_xcirc
      · intro hsx_lt
        by_cases hsx_m1 : slope (w T) = -1
        · have hx_eq_q : w T = w Tq := by
            by_contra hne_q
            have hx_ne_p : w T ≠ S ip := (hE.s_ne_w ip T).symm
            have hq_ne_p : w Tq ≠ S ip := (hE.s_ne_w ip Tq).symm
            have hcol := hE.no_three_collinear (S ip) (w Tq) (w T)
              (Or.inl (Set.mem_range_self _)) (Or.inr (Set.mem_range_self _))
              (Or.inr (Set.mem_range_self _)) hq_ne_p.symm (Ne.symm hne_q) hx_ne_p.symm
            apply hcol
            rw [hp_eq, hq_eq]
            have heq : (w T).2 - 1 = -(w T).1 := by
              dsimp [slope] at hsx_m1; rw [div_eq_iff (ne_of_gt hx1)] at hsx_m1; linarith
            unfold orient2D; linarith
          rwa [hx_eq_q, hq_eq]
        · exact claim_monotone_slope hE hvp hqa hqc hqp ha1 hc1 hc2 hc_sum hsa_gt hsa_lt_sc
            hu1 hup hua hsu_lt_sa hx1 ((hE.shatters T ia).mpr (hT' (by simp)))
            ((hE.shatters T ic).mpr (hT' (by simp))) hsx_lt hsx_m1
  · dsimp [H]; ring
  · dsimp [OpenHalfPlane.MemPos, H]; norm_num
  · dsimp [OpenHalfPlane.MemPos, H]; linarith
  · dsimp [OpenHalfPlane.MemNeg, H]
    have hmul : slope u * (S ia).1 < (S ia).2 - 1 := (lt_div_iff₀ ha1).mp hsu_lt_sa
    linarith
  · dsimp [OpenHalfPlane.MemPos, H]
    have hlt : slope u < sc := lt_trans hsu_lt_sa hsa_lt_sc
    dsimp [sc] at hlt
    rw [lt_div_iff_of_neg hc1] at hlt
    linarith
  · intro x hx
    rcases hx with ⟨T, hT, _, rfl⟩
    exact ⟨(hW_ac T hT).2.1, (hW_ac T hT).1⟩

/-- **Half-Plane Lemma (`upper_9.tex`, Lemma 5.1) in `orient2D` form.**
    Given `v = w Tv`, `q = w Tq`, and `a = S ia`, `p = S ip`, `c = S ic` satisfying:
    (i) `v` sees `p` and misses `a, c`, while `q` sees `a, p, c`;
    (ii) `a, p, c` lie on the same open side of line `vq` with `θ(a) < θ(p) < θ(c)` (in `orient2D` form);
    (iii) segments `vp` and `ac` cross;
    (iv) `v` sees `q`, or some `e = S ie` is seen by both `v` and `q` on the same side of `vq` with `θ(e) < θ(a)`.
    Then there exists `H : OpenHalfPlane` that is a half-plane test for `S ip` on `W({ia, ic})`
    whose boundary passes through `S ip`, with `v, q, c ∈ H⁺`, `a ∈ H⁻`, and every witness in `W({ia, ic})`
    on the `q`-side of `vp` and of `va`. -/
theorem half_plane_lemma_orient {n : ℕ} {P : Set (ℝ × ℝ)}
    {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ}
    (hP : ShatteredSimplePolygon P S w)
    (Tv Tq : Finset (Fin n)) (ia ip ic : Fin n)
    -- (i) visibility of v and q on {a, p, c}
    (hvp : Sees P (w Tv) (S ip))
    (hva_not : ¬ Sees P (w Tv) (S ia))
    (hvc_not : ¬ Sees P (w Tv) (S ic))
    (hqa : Sees P (w Tq) (S ia))
    (hqp : Sees P (w Tq) (S ip))
    (hqc : Sees P (w Tq) (S ic))
    -- (ii) a, p, c on same side of line vq with θ(a) < θ(p) < θ(c)
    (hsame_ap : SameSideOfLine (w Tv) (w Tq) (S ia) (S ip))
    (hsame_cp : SameSideOfLine (w Tv) (w Tq) (S ic) (S ip))
    (htheta_ap : 0 < orient2D (w Tv) (S ia) (S ip) * orient2D (w Tv) (w Tq) (S ip))
    (htheta_pc : 0 < orient2D (w Tv) (S ip) (S ic) * orient2D (w Tv) (w Tq) (S ip))
    -- (iii) segments vp and ac cross
    (hcross : SegmentsCross (w Tv) (S ip) (S ia) (S ic))
    -- (iv) v sees q, or witness e seen by both v and q with θ(e) < θ(a)
    (hiv : Sees P (w Tv) (w Tq) ∨
      ∃ ie : Fin n, Sees P (w Tv) (S ie) ∧ Sees P (w Tq) (S ie) ∧
        SameSideOfLine (w Tv) (w Tq) (S ie) (S ia) ∧
        0 < orient2D (w Tv) (S ie) (S ia) * orient2D (w Tv) (w Tq) (S ip)) :
    ∃ H : OpenHalfPlane,
      IsHalfPlaneTest P (WitnessSet {ia, ic} ∅ w) (S ip) H ∧
      H.n.1 * (S ip).1 + H.n.2 * (S ip).2 + H.c = 0 ∧
      H.MemPos (w Tv) ∧
      H.MemPos (w Tq) ∧
      H.MemNeg (S ia) ∧
      H.MemPos (S ic) ∧
      (∀ x ∈ WitnessSet {ia, ic} ∅ w,
        0 < orient2D (w Tv) (S ip) x * orient2D (w Tv) (S ip) (w Tq) ∧
        0 < orient2D (w Tv) (S ia) x * orient2D (w Tv) (S ia) (w Tq)) := by
  let v := w Tv
  let q := w Tq
  let a := S ia
  let p := S ip
  let c := S ic
  have hD : orient2D v q p ≠ 0 := by
    intro h0
    rw [SameSideOfLine, h0, mul_zero] at hsame_ap
    exact lt_irrefl 0 hsame_ap
  let Φ := toNormCoords v q p
  let Ψ := fromNormCoords v q p
  have hΦΨ : ∀ x, Φ (Ψ x) = x := fun x => toNormCoords_fromNormCoords v q p x hD
  have hΨΦ : ∀ y, Ψ (Φ y) = y := fun y => fromNormCoords_toNormCoords v q p y hD
  let P' := Φ '' P
  let S' := fun i => Φ (S i)
  let w' := fun T => Φ (w T)
  have hE := normEnv_of_shattered hP v q p hD
  have hv_eq : w' Tv = (0, 0) := toNormCoords_v v q p
  have hq_eq : w' Tq = (1, 0) := toNormCoords_q v q p hD
  have hp_eq : S' ip = (0, 1) := toNormCoords_p v q p hD
  have hsees_iff : ∀ x y, Sees P' (Φ x) (Φ y) ↔ Sees P x y := fun x y => by
    rw [sees_fromNormCoords_iff hD]
    change Sees P (Ψ (Φ x)) (Ψ (Φ y)) ↔ Sees P x y
    rw [hΨΦ, hΨΦ]
  have hvp' : Sees P' (0, 0) (0, 1) := by rw [← hv_eq, ← hp_eq]; exact (hsees_iff v p).mpr hvp
  have hva_not' : ¬ Sees P' (0, 0) (S' ia) := by rw [← hv_eq]; rwa [hsees_iff v a]
  have hvc_not' : ¬ Sees P' (0, 0) (S' ic) := by rw [← hv_eq]; rwa [hsees_iff v c]
  have hqa' : Sees P' (1, 0) (S' ia) := by rw [← hq_eq]; exact (hsees_iff q a).mpr hqa
  have hqp' : Sees P' (1, 0) (0, 1) := by rw [← hq_eq, ← hp_eq]; exact (hsees_iff q p).mpr hqp
  have hqc' : Sees P' (1, 0) (S' ic) := by rw [← hq_eq]; exact (hsees_iff q c).mpr hqc
  have ha1 : 0 < (S' ia).1 := by
    dsimp [S', Φ, toNormCoords]
    rw [div_pos_iff]
    rcases lt_or_gt_of_ne hD with hDn | hDp
    · right; exact ⟨by nlinarith, hDn⟩
    · left; exact ⟨by nlinarith, hDp⟩
  have ha2 : 0 < (S' ia).2 := by
    dsimp [S', Φ, toNormCoords, SameSideOfLine] at hsame_ap ⊢
    rw [div_pos_iff]
    rcases lt_or_gt_of_ne hD with hDn | hDp
    · right; exact ⟨by nlinarith, hDn⟩
    · left; exact ⟨by nlinarith, hDp⟩
  have hc1 : (S' ic).1 < 0 := by
    dsimp [S', Φ, toNormCoords]
    have hor : orient2D v c p = -orient2D v p c := orient2D_swap23 v p c
    dsimp [v, q, p, c] at htheta_pc hD ⊢
    rw [hor, div_neg_iff]
    rcases lt_or_gt_of_ne hD with hDn | hDp
    · left; exact ⟨by nlinarith, hDn⟩
    · right; exact ⟨by nlinarith, hDp⟩
  have hc2 : 0 < (S' ic).2 := by
    dsimp [S', Φ, toNormCoords, SameSideOfLine] at hsame_cp ⊢
    rw [div_pos_iff]
    rcases lt_or_gt_of_ne hD with hDn | hDp
    · right; exact ⟨by nlinarith, hDn⟩
    · left; exact ⟨by nlinarith, hDp⟩
  have hcross' : SegmentsCross (0, 0) (0, 1) (S' ia) (S' ic) := by
    rw [← hv_eq, ← hp_eq]
    constructor
    · change orient2D (Φ v) (Φ p) (Φ a) * orient2D (Φ v) (Φ p) (Φ c) < 0
      rw [orient2D_toNormCoords v q p v p a hD, orient2D_toNormCoords v q p v p c hD,
          div_mul_div_comm]
      exact div_neg_of_neg_of_pos hcross.1 (mul_self_pos.mpr hD)
    · change orient2D (Φ a) (Φ c) (Φ v) * orient2D (Φ a) (Φ c) (Φ p) < 0
      rw [orient2D_toNormCoords v q p a c v hD, orient2D_toNormCoords v q p a c p hD,
          div_mul_div_comm]
      exact div_neg_of_neg_of_pos hcross.2 (mul_self_pos.mpr hD)
  have hiv' : Sees P' (0, 0) (1, 0) ∨
      ∃ ie : Fin n, Sees P' (0, 0) (S' ie) ∧ Sees P' (1, 0) (S' ie) ∧
        0 < (S' ie).2 ∧ 0 < (S' ie).1 * (S' ia).2 - (S' ie).2 * (S' ia).1 := by
    rcases hiv with hvq | ⟨ie, hve, hqe, he_same, he_theta⟩
    · left; rw [← hv_eq, ← hq_eq]; exact (hsees_iff v q).mpr hvq
    · right
      refine ⟨ie, by rw [← hv_eq]; exact (hsees_iff v (S ie)).mpr hve,
        by rw [← hq_eq]; exact (hsees_iff q (S ie)).mpr hqe, ?_, ?_⟩
      · have hsame_ep : 0 < orient2D v q (S ie) * orient2D v q p := by
          dsimp [SameSideOfLine] at he_same hsame_ap
          have ha_ne0 : orient2D v q a ≠ 0 := by
            intro h0; rw [h0, zero_mul] at hsame_ap; exact lt_irrefl 0 hsame_ap
          have hmul : (orient2D v q a) ^ 2 * (orient2D v q (S ie) * orient2D v q p) =
              (orient2D v q (S ie) * orient2D v q a) * (orient2D v q a * orient2D v q p) := by ring
          have hrhs : 0 < (orient2D v q (S ie) * orient2D v q a) * (orient2D v q a * orient2D v q p) :=
            mul_pos he_same hsame_ap
          nlinarith [sq_pos_of_ne_zero ha_ne0]
        dsimp [S', Φ, toNormCoords]
        rw [div_pos_iff]
        rcases lt_or_gt_of_ne hD with hDn | hDp
        · right; exact ⟨by nlinarith, hDn⟩
        · left; exact ⟨by nlinarith, hDp⟩
      · have hdet : (S' ie).1 * (S' ia).2 - (S' ie).2 * (S' ia).1 =
            orient2D (0, 0) (S' ie) (S' ia) := by unfold orient2D; ring
        rw [hdet, ← hv_eq]
        change 0 < orient2D (Φ v) (Φ (S ie)) (Φ a)
        rw [orient2D_toNormCoords v q p v (S ie) a hD, div_pos_iff]
        dsimp [v, q, a, p] at he_theta hD ⊢
        rcases lt_or_gt_of_ne hD with hDn | hDp
        · right; exact ⟨by nlinarith, hDn⟩
        · left; exact ⟨by nlinarith, hDp⟩
  obtain ⟨H', hH'_test, hH'_bdry, hH'_v, hH'_q, hH'_a, hH'_c, hH'_pos⟩ :=
    half_plane_lemma_norm hE hv_eq hq_eq hp_eq hvp' hva_not' hvc_not' hqa' hqp' hqc'
      ha1 ha2 hc1 hc2 hcross' hiv'
  let H := pullbackHalfPlane v q p hD H'
  have hmem_pos_iff : ∀ u, H.MemPos u ↔ H'.MemPos (Φ u) := fun u => by
    dsimp [OpenHalfPlane.MemPos, H, Φ]
    rw [pullbackHalfPlane_eval]
  have hmem_neg_iff : ∀ u, H.MemNeg u ↔ H'.MemNeg (Φ u) := fun u => by
    dsimp [OpenHalfPlane.MemNeg, H, Φ]
    rw [pullbackHalfPlane_eval]
  refine ⟨H, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    rcases hx with ⟨T, hT, hdisj, rfl⟩
    have hx' : w' T ∈ WitnessSet {ia, ic} ∅ w' := ⟨T, hT, hdisj, rfl⟩
    obtain ⟨hsides, hsees⟩ := hH'_test (w' T) hx'
    rw [hmem_pos_iff, hmem_neg_iff]
    constructor
    · exact hsides
    · rw [← hsees_iff (w T) p]
      change Sees P' (w' T) (Φ p) ↔ H'.MemPos (w' T)
      rw [← hp_eq] at hsees
      exact hsees
  · change H.n.1 * p.1 + H.n.2 * p.2 + H.c = 0
    rw [pullbackHalfPlane_eval v q p hD H' p]
    change H'.n.1 * (Φ p).1 + H'.n.2 * (Φ p).2 + H'.c = 0
    rw [show Φ p = (0, 1) from hp_eq]
    exact hH'_bdry
  · rw [hmem_pos_iff]; change H'.MemPos (Φ v); rw [show Φ v = (0, 0) from hv_eq]; exact hH'_v
  · rw [hmem_pos_iff]; change H'.MemPos (Φ q); rw [show Φ q = (1, 0) from hq_eq]; exact hH'_q
  · rw [hmem_neg_iff]; exact hH'_a
  · rw [hmem_pos_iff]; exact hH'_c
  · intro x hx
    rcases hx with ⟨T, hT, hdisj, rfl⟩
    obtain ⟨hx1, hoa_x⟩ := hH'_pos (w' T) ⟨T, hT, hdisj, rfl⟩
    constructor
    · have h1 : orient2D (0, 0) (0, 1) (w' T) = -(w' T).1 := by unfold orient2D; ring
      have h2 : orient2D (0, 0) (0, 1) (1, 0) = -1 := by unfold orient2D; ring
      have hmul : orient2D (Φ v) (Φ p) (Φ (w T)) * orient2D (Φ v) (Φ p) (Φ q) = (w' T).1 := by
        change orient2D (w' Tv) (S' ip) (w' T) * orient2D (w' Tv) (S' ip) (w' Tq) = (w' T).1
        rw [hv_eq, hp_eq, hq_eq, h1, h2]; ring
      rw [orient2D_toNormCoords v q p v p (w T) hD,
          orient2D_toNormCoords v q p v p q hD, div_mul_div_comm] at hmul
      have hD2 : 0 < orient2D v q p * orient2D v q p := mul_self_pos.mpr hD
      rw [← hmul] at hx1
      have hmul_pos := mul_pos hx1 hD2
      rw [div_mul_cancel₀ _ (ne_of_gt hD2)] at hmul_pos
      exact hmul_pos
    · have hq_a : orient2D (0, 0) (S' ia) (1, 0) = -(S' ia).2 := by unfold orient2D; ring
      have hmul : orient2D (Φ v) (Φ a) (Φ (w T)) * orient2D (Φ v) (Φ a) (Φ q) =
          orient2D (0, 0) (S' ia) (w' T) * (-(S' ia).2) := by
        change orient2D (w' Tv) (S' ia) (w' T) * orient2D (w' Tv) (S' ia) (w' Tq) = _
        rw [hv_eq, hq_eq, hq_a]
      rw [orient2D_toNormCoords v q p v a (w T) hD,
          orient2D_toNormCoords v q p v a q hD, div_mul_div_comm] at hmul
      have hD2 : 0 < orient2D v q p * orient2D v q p := mul_self_pos.mpr hD
      have hpos : 0 < orient2D (0, 0) (S' ia) (w' T) * (-(S' ia).2) :=
        mul_pos_of_neg_of_neg hoa_x (neg_neg_of_pos ha2)
      rw [← hmul] at hpos
      have hmul_pos := mul_pos hpos hD2
      rw [div_mul_cancel₀ _ (ne_of_gt hD2)] at hmul_pos
      exact hmul_pos

/-- **Half-Plane Lemma (`upper_9.tex`, Lemma 5.1, lines 440–449)** with exact `rayAngle` `θ(y)`. -/
theorem half_plane_lemma {n : ℕ} {P : Set (ℝ × ℝ)}
    {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ}
    (hP : ShatteredSimplePolygon P S w)
    (Tv Tq : Finset (Fin n)) (ia ip ic : Fin n)
    (hvp : Sees P (w Tv) (S ip))
    (hva_not : ¬ Sees P (w Tv) (S ia))
    (hvc_not : ¬ Sees P (w Tv) (S ic))
    (hqa : Sees P (w Tq) (S ia))
    (hqp : Sees P (w Tq) (S ip))
    (hqc : Sees P (w Tq) (S ic))
    (hsame_ap : SameSideOfLine (w Tv) (w Tq) (S ia) (S ip))
    (hsame_cp : SameSideOfLine (w Tv) (w Tq) (S ic) (S ip))
    (htheta_ap : rayAngle (w Tv) (w Tq) (S ia) < rayAngle (w Tv) (w Tq) (S ip))
    (htheta_pc : rayAngle (w Tv) (w Tq) (S ip) < rayAngle (w Tv) (w Tq) (S ic))
    (hcross : SegmentsCross (w Tv) (S ip) (S ia) (S ic))
    (hiv : Sees P (w Tv) (w Tq) ∨
      ∃ ie : Fin n, Sees P (w Tv) (S ie) ∧ Sees P (w Tq) (S ie) ∧
        SameSideOfLine (w Tv) (w Tq) (S ie) (S ia) ∧
        rayAngle (w Tv) (w Tq) (S ie) < rayAngle (w Tv) (w Tq) (S ia)) :
    ∃ H : OpenHalfPlane,
      IsHalfPlaneTest P (WitnessSet {ia, ic} ∅ w) (S ip) H ∧
      H.n.1 * (S ip).1 + H.n.2 * (S ip).2 + H.c = 0 ∧
      H.MemPos (w Tv) ∧
      H.MemPos (w Tq) ∧
      H.MemNeg (S ia) ∧
      H.MemPos (S ic) ∧
      (∀ x ∈ WitnessSet {ia, ic} ∅ w,
        0 < orient2D (w Tv) (S ip) x * orient2D (w Tv) (S ip) (w Tq) ∧
        0 < orient2D (w Tv) (S ia) x * orient2D (w Tv) (S ia) (w Tq)) := by
  have hor_ap : 0 < orient2D (w Tv) (S ia) (S ip) * orient2D (w Tv) (w Tq) (S ip) := by
    have h1 := (rayAngle_lt_iff_orient hsame_ap).mp htheta_ap
    have ha_ne0 : orient2D (w Tv) (w Tq) (S ia) ≠ 0 := by
      intro h0; rw [SameSideOfLine, h0, zero_mul] at hsame_ap; exact lt_irrefl 0 hsame_ap
    have hmul : (orient2D (w Tv) (w Tq) (S ia)) ^ 2 *
        (orient2D (w Tv) (S ia) (S ip) * orient2D (w Tv) (w Tq) (S ip)) =
        (orient2D (w Tv) (S ia) (S ip) * orient2D (w Tv) (w Tq) (S ia)) *
        (orient2D (w Tv) (w Tq) (S ia) * orient2D (w Tv) (w Tq) (S ip)) := by ring
    have hrhs := mul_pos h1 hsame_ap
    nlinarith [sq_pos_of_ne_zero ha_ne0]
  have hor_pc : 0 < orient2D (w Tv) (S ip) (S ic) * orient2D (w Tv) (w Tq) (S ip) :=
    (rayAngle_lt_iff_orient (by rw [SameSideOfLine, mul_comm]; exact hsame_cp)).mp htheta_pc
  have hiv' : Sees P (w Tv) (w Tq) ∨
      ∃ ie : Fin n, Sees P (w Tv) (S ie) ∧ Sees P (w Tq) (S ie) ∧
        SameSideOfLine (w Tv) (w Tq) (S ie) (S ia) ∧
        0 < orient2D (w Tv) (S ie) (S ia) * orient2D (w Tv) (w Tq) (S ip) := by
    rcases hiv with hvq | ⟨ie, hve, hqe, he_same, he_ang⟩
    · exact Or.inl hvq
    · right
      refine ⟨ie, hve, hqe, he_same, ?_⟩
      have h1 := (rayAngle_lt_iff_orient he_same).mp he_ang
      have he_ne0 : orient2D (w Tv) (w Tq) (S ie) ≠ 0 := by
        intro h0; rw [SameSideOfLine, h0, zero_mul] at he_same; exact lt_irrefl 0 he_same
      have hsame_ep : 0 < orient2D (w Tv) (w Tq) (S ie) * orient2D (w Tv) (w Tq) (S ip) := by
        dsimp [SameSideOfLine] at he_same hsame_ap
        have ha_ne0 : orient2D (w Tv) (w Tq) (S ia) ≠ 0 := by
          intro h0; rw [h0, zero_mul] at hsame_ap; exact lt_irrefl 0 hsame_ap
        have hmul : (orient2D (w Tv) (w Tq) (S ia)) ^ 2 *
            (orient2D (w Tv) (w Tq) (S ie) * orient2D (w Tv) (w Tq) (S ip)) =
            (orient2D (w Tv) (w Tq) (S ie) * orient2D (w Tv) (w Tq) (S ia)) *
            (orient2D (w Tv) (w Tq) (S ia) * orient2D (w Tv) (w Tq) (S ip)) := by ring
        nlinarith [sq_pos_of_ne_zero ha_ne0, mul_pos he_same hsame_ap]
      have hmul : (orient2D (w Tv) (w Tq) (S ie)) ^ 2 *
          (orient2D (w Tv) (S ie) (S ia) * orient2D (w Tv) (w Tq) (S ip)) =
          (orient2D (w Tv) (S ie) (S ia) * orient2D (w Tv) (w Tq) (S ie)) *
          (orient2D (w Tv) (w Tq) (S ie) * orient2D (w Tv) (w Tq) (S ip)) := by ring
      nlinarith [sq_pos_of_ne_zero he_ne0, mul_pos h1 hsame_ep]
  exact half_plane_lemma_orient hP Tv Tq ia ip ic hvp hva_not hvc_not hqa hqp hqc
    hsame_ap hsame_cp hor_ap hor_pc hcross hiv'

end Sec5HP

end
