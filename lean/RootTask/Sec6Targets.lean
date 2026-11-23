import Mathlib
import RootTask.PolygonDefs

open scoped Classical BigOperators
open Finset

noncomputable section

/-!
# Section 6: Alternating Sources, Targets, and Interior Anchors (`upper_9.tex` Section 6)

Formalizes Section 6 of `upper_9.tex` (`lines 593–789`) over `RootTask.PolygonDefs`'s
`ShatteredSimplePolygon P S w`, taking the outputs of Sections 2.3–5 cleanly through
`Sec2To5Interface P S w`.
-/

/-! ## Part 1: Planar Primitives (`InIntTri`, `SegmentsCross`, `OnSameSide`, `AngleLt`) -/

/-- Strict interior of triangle `△(a, b, c)` via positive barycentric coordinates. -/
def InIntTri (a b c z : ℝ × ℝ) : Prop :=
  ∃ μ₁ μ₂ μ₃ : ℝ, 0 < μ₁ ∧ 0 < μ₂ ∧ 0 < μ₃ ∧ μ₁ + μ₂ + μ₃ = 1 ∧
    z.1 = μ₁ * a.1 + μ₂ * b.1 + μ₃ * c.1 ∧
    z.2 = μ₁ * a.2 + μ₂ * b.2 + μ₃ * c.2

lemma InIntTri.to_inClosedTri {a b c z : ℝ × ℝ} (h : InIntTri a b c z) :
    InClosedTri a b c z := by
  rcases h with ⟨μ₁, μ₂, μ₃, h1, h2, h3, hsum, hz1, hz2⟩
  exact ⟨μ₁, μ₂, μ₃, le_of_lt h1, le_of_lt h2, le_of_lt h3, hsum, hz1, hz2⟩

lemma InIntTri.to_convexHull {a b c z : ℝ × ℝ} (h : InIntTri a b c z) :
    z ∈ convexHull ℝ ({a, b, c} : Set (ℝ × ℝ)) :=
  (inClosedTri_iff_mem_convexHull a b c z).mp h.to_inClosedTri

lemma InIntTri.symm12 {a b c z : ℝ × ℝ} (h : InIntTri a b c z) : InIntTri b a c z := by
  rcases h with ⟨μ₁, μ₂, μ₃, h1, h2, h3, hsum, hz1, hz2⟩
  exact ⟨μ₂, μ₁, μ₃, h2, h1, h3, by linarith, by linarith, by linarith⟩

lemma InIntTri.cycle {a b c z : ℝ × ℝ} (h : InIntTri a b c z) : InIntTri b c a z := by
  rcases h with ⟨μ₁, μ₂, μ₃, h1, h2, h3, hsum, hz1, hz2⟩
  exact ⟨μ₂, μ₃, μ₁, h2, h3, h1, by linarith, by linarith, by linarith⟩

lemma InIntTri.symm23 {a b c z : ℝ × ℝ} (h : InIntTri a b c z) : InIntTri a c b z :=
  h.symm12.cycle

lemma orient2D_barycentric_sum (a b c z : ℝ × ℝ) :
    orient2D b c z + orient2D c a z + orient2D a b z = orient2D a b c := by
  unfold orient2D; ring

lemma orient2D_barycentric_x (a b c z : ℝ × ℝ) :
    orient2D a b c * z.1 =
      orient2D b c z * a.1 + orient2D c a z * b.1 + orient2D a b z * c.1 := by
  unfold orient2D; ring

lemma orient2D_barycentric_y (a b c z : ℝ × ℝ) :
    orient2D a b c * z.2 =
      orient2D b c z * a.2 + orient2D c a z * b.2 + orient2D a b z * c.2 := by
  unfold orient2D; ring

lemma orient2D_convex_comb3 (p q v a b f : ℝ × ℝ) (μ₁ μ₂ μ₃ : ℝ)
    (hsum : μ₁ + μ₂ + μ₃ = 1)
    (hf1 : f.1 = μ₁ * v.1 + μ₂ * a.1 + μ₃ * b.1)
    (hf2 : f.2 = μ₁ * v.2 + μ₂ * a.2 + μ₃ * b.2) :
    orient2D p q f = μ₁ * orient2D p q v + μ₂ * orient2D p q a + μ₃ * orient2D p q b := by
  unfold orient2D; rw [hf1, hf2]
  linear_combination (p.2 * q.1 - p.1 * q.2) * hsum

lemma inIntTri_iff_orient_pos {a b c z : ℝ × ℝ} (hccw : 0 < orient2D a b c) :
    InIntTri a b c z ↔ 0 < orient2D a b z ∧ 0 < orient2D b c z ∧ 0 < orient2D c a z := by
  constructor
  · rintro ⟨μ₁, μ₂, μ₃, h1, h2, h3, hsum, hz1, hz2⟩
    have hid1 : orient2D a b z = μ₃ * orient2D a b c := by
      unfold orient2D; rw [hz1, hz2]
      linear_combination (a.2 * b.1 - a.1 * b.2) * hsum
    have hid2 : orient2D b c z = μ₁ * orient2D a b c := by
      unfold orient2D; rw [hz1, hz2]
      linear_combination (b.2 * c.1 - b.1 * c.2) * hsum
    have hid3 : orient2D c a z = μ₂ * orient2D a b c := by
      unfold orient2D; rw [hz1, hz2]
      linear_combination (c.2 * a.1 - c.1 * a.2) * hsum
    exact ⟨by rw [hid1]; exact mul_pos h3 hccw,
           by rw [hid2]; exact mul_pos h1 hccw,
           by rw [hid3]; exact mul_pos h2 hccw⟩
  · rintro ⟨hab, hbc, hca⟩
    let det := orient2D a b c
    have hdet : det ≠ 0 := ne_of_gt hccw
    refine ⟨orient2D b c z / det, orient2D c a z / det, orient2D a b z / det,
      div_pos hbc hccw, div_pos hca hccw, div_pos hab hccw, ?_, ?_, ?_⟩
    · rw [← add_div, ← add_div, orient2D_barycentric_sum, div_self hdet]
    · have hx := orient2D_barycentric_x a b c z
      field_simp [hdet]; linarith
    · have hy := orient2D_barycentric_y a b c z
      field_simp [hdet]; linarith

lemma oppositeConeWedge_memOpen_iff (a b c x : ℝ × ℝ) (hccw : 0 < orient2D a b c) :
    (oppositeConeWedge a b c hccw).MemOpen x ↔ orient2D c a x < 0 ∧ orient2D a b x < 0 := by
  dsimp [oppositeConeWedge, OpenWedge.MemOpen]
  have h1 : (a.2 - c.2) * (x.1 - a.1) + -(a.1 - c.1) * (x.2 - a.2) = -orient2D c a x := by
    unfold orient2D; ring
  have h2 : (b.2 - a.2) * (x.1 - a.1) + -(b.1 - a.1) * (x.2 - a.2) = -orient2D a b x := by
    unfold orient2D; ring
  rw [h1, h2]
  constructor <;> rintro ⟨u, v⟩ <;> exact ⟨by linarith, by linarith⟩

lemma oppositeConeWedge_memOpen_iff_inIntTri (a b c x : ℝ × ℝ) (hccw : 0 < orient2D a b c) :
    (oppositeConeWedge a b c hccw).MemOpen x ↔ InIntTri x b c a := by
  rw [oppositeConeWedge_memOpen_iff a b c x hccw]
  constructor
  · rintro ⟨hcax, habx⟩
    have hxbc : 0 < orient2D x b c := by
      have hid := orient2D_barycentric_sum a b c x
      unfold orient2D at hid hcax habx hccw ⊢
      linarith
    rw [inIntTri_iff_orient_pos hxbc]
    refine ⟨?_, ?_, ?_⟩
    · unfold orient2D at habx ⊢; linarith
    · unfold orient2D at hccw ⊢; linarith
    · unfold orient2D at hcax ⊢; linarith
  · intro hin
    rcases hin with ⟨μ₁, μ₂, μ₃, h1, h2, h3, hsum, ha1, ha2⟩
    have hcax : orient2D c a x = -(μ₂ / μ₁) * orient2D a b c := by
      have hid : μ₁ * orient2D c a x = -μ₂ * orient2D a b c := by
        have h0 : orient2D c a a = 0 := orient2D_self_right c a
        have hcc : orient2D c a c = 0 := orient2D_self_outer c a
        have hcab : orient2D c a b = orient2D a b c := by rw [orient2D_cycle, orient2D_cycle]
        have hcomb := orient2D_convex_comb3 c a x b c a μ₁ μ₂ μ₃ hsum ha1 ha2
        rw [h0, hcc, hcab, mul_zero, add_zero] at hcomb
        linarith
      have h1ne : μ₁ ≠ 0 := ne_of_gt h1
      calc orient2D c a x = (μ₁ * orient2D c a x) / μ₁ := by field_simp [h1ne]
        _ = (-μ₂ * orient2D a b c) / μ₁ := by rw [hid]
        _ = -(μ₂ / μ₁) * orient2D a b c := by ring
    have habx : orient2D a b x = -(μ₃ / μ₁) * orient2D a b c := by
      have hid : μ₁ * orient2D a b x = -μ₃ * orient2D a b c := by
        have h0 : orient2D a b a = 0 := orient2D_self_outer a b
        have hbb : orient2D a b b = 0 := orient2D_self_right a b
        have hcomb := orient2D_convex_comb3 a b x b c a μ₁ μ₂ μ₃ hsum ha1 ha2
        rw [h0, hbb, mul_zero, add_zero] at hcomb
        linarith
      have h1ne : μ₁ ≠ 0 := ne_of_gt h1
      calc orient2D a b x = (μ₁ * orient2D a b x) / μ₁ := by field_simp [h1ne]
        _ = (-μ₃ * orient2D a b c) / μ₁ := by rw [hid]
        _ = -(μ₃ / μ₁) * orient2D a b c := by ring
    exact ⟨by rw [hcax]; exact mul_neg_of_neg_of_pos (neg_lt_zero.mpr (div_pos h2 h1)) hccw,
           by rw [habx]; exact mul_neg_of_neg_of_pos (neg_lt_zero.mpr (div_pos h3 h1)) hccw⟩

lemma oppositeConeWedge_separates (a b c x : ℝ × ℝ) (hccw : 0 < orient2D a b c)
    (hx : (oppositeConeWedge a b c hccw).MemOpen x) :
    orient2D a x b * orient2D a x c < 0 := by
  rw [oppositeConeWedge_memOpen_iff] at hx
  have h1 : 0 < orient2D a x b := by unfold orient2D at *; linarith [hx.2]
  have h2 : orient2D a x c < 0 := by unfold orient2D at *; linarith [hx.1]
  exact mul_neg_of_pos_of_neg h1 h2

/-- Open segments `ab` and `cd` cross strictly. -/
def SegmentsCross (a b c d : ℝ × ℝ) : Prop :=
  orient2D a b c * orient2D a b d < 0 ∧ orient2D c d a * orient2D c d b < 0

lemma SegmentsCross.symm12 {a b c d : ℝ × ℝ} (h : SegmentsCross a b c d) :
    SegmentsCross b a c d := by
  rcases h with ⟨h1, h2⟩
  refine ⟨?_, ?_⟩
  · have : orient2D b a c * orient2D b a d = orient2D a b c * orient2D a b d := by
      unfold orient2D; ring
    linarith
  · have : orient2D c d b * orient2D c d a = orient2D c d a * orient2D c d b := by ring
    linarith

lemma SegmentsCross.symm34 {a b c d : ℝ × ℝ} (h : SegmentsCross a b c d) :
    SegmentsCross a b d c := by
  rcases h with ⟨h1, h2⟩
  refine ⟨?_, ?_⟩
  · linarith [show orient2D a b d * orient2D a b c = orient2D a b c * orient2D a b d by ring]
  · have : orient2D d c a * orient2D d c b = orient2D c d a * orient2D c d b := by
      unfold orient2D; ring
    linarith

lemma SegmentsCross.swap {a b c d : ℝ × ℝ} (h : SegmentsCross a b c d) :
    SegmentsCross c d a b :=
  ⟨h.2, h.1⟩

/-- Points `a, b` lie on the same open side of the directed line `v q`. -/
def OnSameSide (v q a b : ℝ × ℝ) : Prop :=
  0 < orient2D v q a * orient2D v q b

lemma OnSameSide.symm {v q a b : ℝ × ℝ} (h : OnSameSide v q a b) : OnSameSide v q b a := by
  unfold OnSameSide at *; linarith

lemma OnSameSide.trans {v q a b c : ℝ × ℝ}
    (hab : OnSameSide v q a b) (hbc : OnSameSide v q b c) : OnSameSide v q a c := by
  unfold OnSameSide at *
  have hsq : 0 < orient2D v q b * orient2D v q b := by
    rcases lt_trichotomy (orient2D v q b) 0 with hb | hb | hb
    · exact mul_pos_of_neg_of_neg hb hb
    · rw [hb, mul_zero] at hab; linarith
    · exact mul_pos hb hb
  nlinarith [mul_pos hab hbc]

/-- Angular ordering `θ(a) < θ(b)` around `v` relative to ray `v q`, on one open side of `v q`. -/
def AngleLt (v q a b : ℝ × ℝ) : Prop :=
  OnSameSide v q a b ∧ 0 < orient2D v q a * orient2D v a b

lemma orient2D_angle_trans_id (v q a b c : ℝ × ℝ) :
    orient2D v q b * orient2D v a c =
      orient2D v q a * orient2D v b c + orient2D v q c * orient2D v a b := by
  unfold orient2D; ring

lemma AngleLt.trans {v q a b c : ℝ × ℝ}
    (hab : AngleLt v q a b) (hbc : AngleLt v q b c) : AngleLt v q a c := by
  rcases hab with ⟨hs1, ha1⟩
  rcases hbc with ⟨hs2, ha2⟩
  refine ⟨hs1.trans hs2, ?_⟩
  have hid := orient2D_angle_trans_id v q a b c
  unfold OnSameSide at hs1 hs2
  rcases lt_trichotomy (orient2D v q a) 0 with ha | ha | ha
  · have hb : orient2D v q b < 0 := by nlinarith
    have hc : orient2D v q c < 0 := by nlinarith
    have h1 : orient2D v a b < 0 := by nlinarith
    have h2 : orient2D v b c < 0 := by nlinarith
    have hac : orient2D v a c < 0 := by nlinarith
    exact mul_pos_of_neg_of_neg ha hac
  · rw [ha, zero_mul] at ha1; linarith
  · have hb : 0 < orient2D v q b := by nlinarith
    have hc : 0 < orient2D v q c := by nlinarith
    have h1 : 0 < orient2D v a b := by nlinarith
    have h2 : 0 < orient2D v b c := by nlinarith
    have hac : 0 < orient2D v a c := by nlinarith
    exact mul_pos ha hac

lemma AngleLt.irrefl (v q a : ℝ × ℝ) : ¬ AngleLt v q a a := by
  rintro ⟨_, h⟩
  rw [orient2D_self_right, mul_zero] at h
  linarith

lemma AngleLt.asymm {v q a b : ℝ × ℝ} (hab : AngleLt v q a b) : ¬ AngleLt v q b a := by
  intro hba
  exact AngleLt.irrefl v q a (hab.trans hba)

lemma AngleLt.not_sameSide_opp {v q a b : ℝ × ℝ} (hab : AngleLt v q a b) :
    OnSameSide v q a b := hab.1

lemma angleLt_of_orient_sameSide {v q a b : ℝ × ℝ}
    (hs : OnSameSide v q a b)
    (hpos : 0 < orient2D v q a → 0 < orient2D v a b)
    (hneg : orient2D v q a < 0 → orient2D v a b < 0) :
    AngleLt v q a b := by
  refine ⟨hs, ?_⟩
  rcases lt_trichotomy (orient2D v q a) 0 with h | h | h
  · exact mul_pos_of_neg_of_neg h (hneg h)
  · unfold OnSameSide at hs; rw [h, zero_mul] at hs; linarith
  · exact mul_pos h (hpos h)

lemma angleLt_iff_pos_of_pos {v q a b : ℝ × ℝ}
    (ha : 0 < orient2D v q a) (hb : 0 < orient2D v q b) :
    AngleLt v q a b ↔ 0 < orient2D v a b := by
  unfold AngleLt OnSameSide
  constructor
  · rintro ⟨_, h⟩; nlinarith
  · intro h; exact ⟨mul_pos ha hb, mul_pos ha h⟩

lemma angleLt_iff_neg_of_neg {v q a b : ℝ × ℝ}
    (ha : orient2D v q a < 0) (hb : orient2D v q b < 0) :
    AngleLt v q a b ↔ orient2D v a b < 0 := by
  unfold AngleLt OnSameSide
  constructor
  · rintro ⟨_, h⟩; nlinarith
  · intro h; exact ⟨mul_pos_of_neg_of_neg ha hb, mul_pos_of_neg_of_neg ha h⟩

lemma universal_crossing_angles {v q a c z : ℝ × ℝ}
    (hac : AngleLt v q a c)
    (hcross : SegmentsCross v z a c) :
    AngleLt v q a z ∧ AngleLt v q z c := by
  rcases hac with ⟨hsac, hoac⟩
  rcases hcross with ⟨hvz, hac_v⟩
  have hsame : 0 < orient2D v q a * orient2D v q c := hsac
  -- Express `orient2D v a c * (z - v)` via `orient2D v z c` and `orient2D v a z`:
  have hid_x : orient2D v a c * (z.1 - v.1) =
      orient2D v z c * (a.1 - v.1) + orient2D v a z * (c.1 - v.1) := by
    unfold orient2D; ring
  have hid_y : orient2D v a c * (z.2 - v.2) =
      orient2D v z c * (a.2 - v.2) + orient2D v a z * (c.2 - v.2) := by
    unfold orient2D; ring
  have hid_q : orient2D v a c * orient2D v q z =
      orient2D v z c * orient2D v q a + orient2D v a z * orient2D v q c := by
    unfold orient2D; ring
  have hid_ac : orient2D a c z = orient2D a c v - (orient2D v a z + orient2D v z c) := by
    unfold orient2D; ring
  have hac_eq : orient2D v a c = orient2D a c v := by unfold orient2D; ring
  have hv_opp : 0 < orient2D v a z * orient2D v z c := by
    have h1 : orient2D v z a = -orient2D v a z := by unfold orient2D; ring
    rw [h1] at hvz
    linarith
  have hac_z_opp : orient2D a c v * orient2D a c z < 0 := hac_v
  -- Both `orient2D v a z` and `orient2D v z c` must have the same sign as `orient2D v a c`!
  rcases lt_trichotomy (orient2D v q a) 0 with hqa | hqa | hqa
  · have hqc : orient2D v q c < 0 := by nlinarith
    have ho : orient2D v a c < 0 := by nlinarith
    have hacv : orient2D a c v < 0 := by linarith
    have hacz : 0 < orient2D a c z := by nlinarith
    have hsum_pos : orient2D v a z + orient2D v z c < 0 := by linarith [hid_ac]
    have haz_neg : orient2D v a z < 0 := by
      by_contra hge
      replace hge : 0 ≤ orient2D v a z := not_lt.mp hge
      have hzc_gt : 0 < orient2D v z c := by
        rcases eq_or_lt_of_le hge with h0 | hpos
        · rw [← h0, zero_mul] at hv_opp; linarith
        · nlinarith
      linarith
    have hzc_neg : orient2D v z c < 0 := by nlinarith
    have hqz : orient2D v q z < 0 := by nlinarith
    exact ⟨⟨mul_pos_of_neg_of_neg hqa hqz, mul_pos_of_neg_of_neg hqa haz_neg⟩,
           ⟨mul_pos_of_neg_of_neg hqz hqc, mul_pos_of_neg_of_neg hqz hzc_neg⟩⟩
  · rw [hqa, zero_mul] at hoac; linarith
  · have hqc : 0 < orient2D v q c := by nlinarith
    have ho : 0 < orient2D v a c := by nlinarith
    have hacv : 0 < orient2D a c v := by linarith
    have hacz : orient2D a c z < 0 := by nlinarith
    have hsum_pos : 0 < orient2D v a z + orient2D v z c := by linarith [hid_ac]
    have haz_pos : 0 < orient2D v a z := by
      by_contra hle
      replace hle : orient2D v a z ≤ 0 := not_lt.mp hle
      have hzc_neg : orient2D v z c < 0 := by
        rcases eq_or_lt_of_le hle with h0 | hneg
        · rw [h0, zero_mul] at hv_opp; linarith
        · nlinarith
      linarith
    have hzc_pos : 0 < orient2D v z c := by nlinarith
    have hqz : 0 < orient2D v q z := by nlinarith
    exact ⟨⟨mul_pos hqa hqz, mul_pos hqa haz_pos⟩,
           ⟨mul_pos hqz hqc, mul_pos hqz hzc_pos⟩⟩

/-! ## Part 2: Hull Vertices, Convex Position, Cyclic Order, and Counting -/

/-- Extreme hull vertices `B` of `S`. -/
def hullVertices {n : ℕ} (S : Fin n → ℝ × ℝ) : Finset (Fin n) :=
  Finset.univ.filter (fun i => S i ∉ convexHull ℝ (((Finset.univ.erase i).image S) : Set (ℝ × ℝ)))

/-- Interior points `A = S \ B`. -/
def interiorPoints {n : ℕ} (S : Fin n → ℝ × ℝ) : Finset (Fin n) :=
  Finset.univ \ hullVertices S

/-- Convex position predicate for a subset `C ⊆ Fin n`. -/
def IsConvexPos {n : ℕ} (S : Fin n → ℝ × ℝ) (C : Finset (Fin n)) : Prop :=
  ∀ i ∈ C, S i ∉ convexHull ℝ (((C.erase i).image S) : Set (ℝ × ℝ))

lemma hullVertices_convexPos {n : ℕ} (S : Fin n → ℝ × ℝ) {C : Finset (Fin n)}
    (hC : C ⊆ hullVertices S) : IsConvexPos S C := by
  intro i hi hmem
  have hiB := (Finset.mem_filter.mp (hC hi)).2
  apply hiB
  refine convexHull_mono ?_ hmem
  intro x hx
  rcases Finset.mem_image.mp hx with ⟨j, hj, rfl⟩
  exact Finset.mem_image.mpr ⟨j, Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hj).1, Finset.mem_univ _⟩, rfl⟩

/-- Directed counterclockwise boundary edge `(a, b)` of `conv C`. -/
def IsCCWEdge {n : ℕ} (S : Fin n → ℝ × ℝ) (C : Finset (Fin n)) (a b : Fin n) : Prop :=
  a ∈ C ∧ b ∈ C ∧ a ≠ b ∧ ∀ r ∈ C, r ≠ a → r ≠ b → 0 < orient2D (S a) (S b) (S r)

/-- Front vertex of `C` from `v`: both incident edges of `conv C` face `v`. -/
def IsFrontVertexOf {n : ℕ} (S : Fin n → ℝ × ℝ) (C : Finset (Fin n)) (f : Fin n) (v : ℝ × ℝ) : Prop :=
  f ∈ C ∧ ∀ a b : Fin n, IsCCWEdge S C a b → (a = f ∨ b = f) → orient2D (S a) (S b) v < 0

/-- Back vertex of `C` from `v`: neither incident edge of `conv C` faces `v`. -/
def IsBackVertexOf {n : ℕ} (S : Fin n → ℝ × ℝ) (C : Finset (Fin n)) (p : Fin n) (v : ℝ × ℝ) : Prop :=
  p ∈ C ∧ ∀ a b : Fin n, IsCCWEdge S C a b → (a = p ∨ b = p) → 0 < orient2D (S a) (S b) v

/-- Certified hull vertices `H ⊆ B`. -/
def certifiedVertices {n : ℕ} (S : Fin n → ℝ × ℝ) (w : Finset (Fin n) → ℝ × ℝ) : Finset (Fin n) :=
  let B := hullVertices S
  B.filter (fun f => ∃ T : Finset (Fin n), f ∉ T ∧
    (∀ b : Fin n, IsCCWEdge S B b f → b ∈ T) ∧
    (∀ c : Fin n, IsCCWEdge S B f c → c ∈ T) ∧
    IsFrontVertexOf S B f (w T))

/-- Explicit CCW cyclic enumeration of a convex `(k + 3)`-gon `C`. -/
structure CCWCycle {n : ℕ} (S : Fin n → ℝ × ℝ) (C : Finset (Fin n)) (k : ℕ) where
  toFun : Fin (k + 3) → Fin n
  inj : Function.Injective toFun
  image_eq : Finset.univ.image toFun = C
  ccw : StrictConvexCCWPoly (S ∘ toFun)
  ccw_tri : ∀ a b c : Fin (k + 3), a < b → b < c →
    0 < orient2D (S (toFun a)) (S (toFun b)) (S (toFun c))

lemma ccwCycle_mem {n k : ℕ} {S : Fin n → ℝ × ℝ} {C : Finset (Fin n)}
    (cyc : CCWCycle S C k) (i : Fin (k + 3)) : cyc.toFun i ∈ C := by
  have h := Finset.mem_image_of_mem cyc.toFun (Finset.mem_univ i)
  rwa [cyc.image_eq] at h

lemma ccwCycle_exists_index {n k : ℕ} {S : Fin n → ℝ × ℝ} {C : Finset (Fin n)}
    (cyc : CCWCycle S C k) {x : Fin n} (hx : x ∈ C) : ∃ i : Fin (k + 3), cyc.toFun i = x := by
  rw [← cyc.image_eq] at hx
  rcases Finset.mem_image.mp hx with ⟨i, _, hi⟩
  exact ⟨i, hi⟩

lemma ccwCycle_isCCWEdge {n k : ℕ} {S : Fin n → ℝ × ℝ} {C : Finset (Fin n)}
    (cyc : CCWCycle S C k) (i : Fin (k + 3)) :
    IsCCWEdge S C (cyc.toFun i) (cyc.toFun (i + 1)) := by
  have hi1_ne : i ≠ i + 1 := by
    intro h
    nth_rw 1 [← add_zero i] at h
    have h01 : (0 : Fin (k + 3)) = 1 := add_left_cancel h
    have hv := congrArg Fin.val h01
    simp [Nat.mod_eq_of_lt (by omega : 1 < k + 3)] at hv
  refine ⟨ccwCycle_mem cyc i, ccwCycle_mem cyc (i + 1), fun h => hi1_ne (cyc.inj h), ?_⟩
  intro r hr hri hri1
  obtain ⟨j, rfl⟩ := ccwCycle_exists_index cyc hr
  have hji : j ≠ i := fun h => hri (congrArg cyc.toFun h)
  have hji1 : j ≠ i + 1 := fun h => hri1 (congrArg cyc.toFun h)
  exact cyc.ccw i j hji hji1

lemma isCCWEdge_iff_ccwCycle {n k : ℕ} {S : Fin n → ℝ × ℝ} {C : Finset (Fin n)}
    (cyc : CCWCycle S C k) (a b : Fin n) :
    IsCCWEdge S C a b ↔ ∃ i : Fin (k + 3), a = cyc.toFun i ∧ b = cyc.toFun (i + 1) := by
  constructor
  · rintro ⟨ha, hb, hab, hall⟩
    obtain ⟨i, rfl⟩ := ccwCycle_exists_index cyc ha
    obtain ⟨j, rfl⟩ := ccwCycle_exists_index cyc hb
    have hij : i ≠ j := fun h => hab (congrArg cyc.toFun h)
    by_cases hji1 : j = i + 1
    · exact ⟨i, rfl, hji1 ▸ rfl⟩
    · have hi1_ne_i : i + 1 ≠ i := by
        intro h
        nth_rw 2 [← add_zero i] at h
        have h10 : (1 : Fin (k + 3)) = 0 := add_left_cancel h
        have hv := congrArg Fin.val h10
        simp [Nat.mod_eq_of_lt (by omega : 1 < k + 3)] at hv
      have hi1_ne_j : i + 1 ≠ j := Ne.symm hji1
      have hpos := hall (cyc.toFun (i + 1)) (ccwCycle_mem cyc (i + 1))
        (fun h => hi1_ne_i (cyc.inj h)) (fun h => hi1_ne_j (cyc.inj h))
      have hccw := cyc.ccw i j hij.symm (Ne.symm hi1_ne_j)
      have hopp : orient2D (S (cyc.toFun i)) (S (cyc.toFun j)) (S (cyc.toFun (i + 1))) =
          -orient2D (S (cyc.toFun i)) (S (cyc.toFun (i + 1))) (S (cyc.toFun j)) :=
        orient2D_swap23 _ _ _
      dsimp at hccw
      linarith
  · rintro ⟨i, rfl, rfl⟩
    exact ccwCycle_isCCWEdge cyc i

/-- `IsCCWEdge` uniquely determines the successor/predecessor along `C`. -/
lemma isCCWEdge_unique_succ {n k : ℕ} {S : Fin n → ℝ × ℝ} {C : Finset (Fin n)}
    (cyc : CCWCycle S C k) {a b b' : Fin n}
    (hb : IsCCWEdge S C a b) (hb' : IsCCWEdge S C a b') : b = b' := by
  rw [isCCWEdge_iff_ccwCycle cyc] at hb hb'
  rcases hb with ⟨i, hi, rfl⟩
  rcases hb' with ⟨j, hj, rfl⟩
  rw [cyc.inj (hi.symm.trans hj)]

lemma isCCWEdge_unique_pred {n k : ℕ} {S : Fin n → ℝ × ℝ} {C : Finset (Fin n)}
    (cyc : CCWCycle S C k) {a a' b : Fin n}
    (ha : IsCCWEdge S C a b) (ha' : IsCCWEdge S C a' b) : a = a' := by
  rw [isCCWEdge_iff_ccwCycle cyc] at ha ha'
  rcases ha with ⟨i, rfl, hi⟩
  rcases ha' with ⟨j, rfl, hj⟩
  have hij : i + 1 = j + 1 := cyc.inj (hi.symm.trans hj)
  rw [add_right_cancel hij]

lemma isFrontVertexOf_iff_ccwCycle {n k : ℕ} {S : Fin n → ℝ × ℝ} {C : Finset (Fin n)}
    (cyc : CCWCycle S C k) (i : Fin (k + 3)) (v : ℝ × ℝ) :
    IsFrontVertexOf S C (cyc.toFun i) v ↔
      orient2D (S (cyc.toFun (i - 1))) (S (cyc.toFun i)) v < 0 ∧
      orient2D (S (cyc.toFun i)) (S (cyc.toFun (i + 1))) v < 0 := by
  constructor
  · rintro ⟨_, hall⟩
    have e1 := ccwCycle_isCCWEdge cyc (i - 1)
    rw [sub_add_cancel] at e1
    have e2 := ccwCycle_isCCWEdge cyc i
    exact ⟨hall _ _ e1 (Or.inr rfl), hall _ _ e2 (Or.inl rfl)⟩
  · rintro ⟨h1, h2⟩
    refine ⟨ccwCycle_mem cyc i, ?_⟩
    intro a b hab heq
    rw [isCCWEdge_iff_ccwCycle cyc] at hab
    rcases hab with ⟨j, rfl, rfl⟩
    rcases heq with hja | hjb
    · have hj : j = i := cyc.inj hja
      subst hj; exact h2
    · have hj1 : j + 1 = i := cyc.inj hjb
      have hj : j = i - 1 := eq_sub_of_add_eq hj1
      subst hj; rw [sub_add_cancel]; exact h1

lemma isBackVertexOf_iff_ccwCycle {n k : ℕ} {S : Fin n → ℝ × ℝ} {C : Finset (Fin n)}
    (cyc : CCWCycle S C k) (i : Fin (k + 3)) (v : ℝ × ℝ) :
    IsBackVertexOf S C (cyc.toFun i) v ↔
      0 < orient2D (S (cyc.toFun (i - 1))) (S (cyc.toFun i)) v ∧
      0 < orient2D (S (cyc.toFun i)) (S (cyc.toFun (i + 1))) v := by
  constructor
  · rintro ⟨_, hall⟩
    have e1 := ccwCycle_isCCWEdge cyc (i - 1)
    rw [sub_add_cancel] at e1
    have e2 := ccwCycle_isCCWEdge cyc i
    exact ⟨hall _ _ e1 (Or.inr rfl), hall _ _ e2 (Or.inl rfl)⟩
  · rintro ⟨h1, h2⟩
    refine ⟨ccwCycle_mem cyc i, ?_⟩
    intro a b hab heq
    rw [isCCWEdge_iff_ccwCycle cyc] at hab
    rcases hab with ⟨j, rfl, rfl⟩
    rcases heq with hja | hjb
    · have hj : j = i := cyc.inj hja
      subst hj; exact h2
    · have hj1 : j + 1 = i := cyc.inj hjb
      have hj : j = i - 1 := eq_sub_of_add_eq hj1
      subst hj; rw [sub_add_cancel]; exact h1

lemma isFrontVertexOf_iff_inIntTri {n k : ℕ} {S : Fin n → ℝ × ℝ} {C : Finset (Fin n)}
    (cyc : CCWCycle S C k) (i : Fin (k + 3)) (v : ℝ × ℝ)
    (_hne : orient2D (S (cyc.toFun (i - 1))) (S (cyc.toFun (i + 1))) v ≠ 0) :
    IsFrontVertexOf S C (cyc.toFun i) v ↔
      InIntTri v (S (cyc.toFun (i - 1))) (S (cyc.toFun (i + 1))) (S (cyc.toFun i)) := by
  rw [isFrontVertexOf_iff_ccwCycle cyc i v]
  have h1_ne_0 : (1 : Fin (k + 3)) ≠ 0 := by
    intro h; have hv := congrArg Fin.val h; simp [Nat.mod_eq_of_lt (by omega : 1 < k + 3)] at hv
  have h2_ne_0 : (2 : Fin (k + 3)) ≠ 0 := by
    intro h; have hv := congrArg Fin.val h; simp [Nat.mod_eq_of_lt (by omega : 2 < k + 3)] at hv
  have him1_ne_ip1 : i - 1 ≠ i + 1 := by
    intro h
    have h' := congrArg (· + (1 : Fin (k + 3))) h
    rw [sub_add_cancel, add_assoc] at h'
    nth_rw 1 [← add_zero i] at h'
    exact h2_ne_0 (add_left_cancel h').symm
  have hi_ne_im1 : i ≠ i - 1 := by
    intro h
    have h' := congrArg (· + (1 : Fin (k + 3))) h
    rw [sub_add_cancel] at h'
    nth_rw 2 [← add_zero i] at h'
    exact h1_ne_0 (add_left_cancel h')
  have hi1_ne_i : i + 1 ≠ i := by
    intro h
    nth_rw 2 [← add_zero i] at h
    exact h1_ne_0 (add_left_cancel h)
  have hccw : 0 < orient2D (S (cyc.toFun (i - 1))) (S (cyc.toFun i)) (S (cyc.toFun (i + 1))) := by
    have h := cyc.ccw (i - 1) (i + 1) him1_ne_ip1.symm (by rw [sub_add_cancel]; exact hi1_ne_i)
    rwa [sub_add_cancel] at h
  let p_ := S (cyc.toFun (i - 1))
  let p := S (cyc.toFun i)
  let p' := S (cyc.toFun (i + 1))
  change orient2D p_ p v < 0 ∧ orient2D p p' v < 0 ↔ InIntTri v p_ p' p
  constructor
  · rintro ⟨h1, h2⟩
    have hv_pos : 0 < orient2D v p' p_ := by
      have hid : orient2D v p' p_ = orient2D p_ p p' - orient2D p_ p v - orient2D p p' v := by
        unfold orient2D; ring
      linarith
    have hin_rot : InIntTri v p' p_ p := by
      rw [inIntTri_iff_orient_pos hv_pos]
      refine ⟨?_, ?_, ?_⟩
      · unfold orient2D at h2 ⊢; linarith
      · unfold orient2D at hccw ⊢; linarith
      · unfold orient2D at h1 ⊢; linarith
    exact hin_rot.symm23
  · intro hin
    rcases hin with ⟨μ₁, μ₂, μ₃, hm1, hm2, hm3, hsum, hp1, hp2⟩
    have hid := orient2D_convex_comb3 p_ p' v p_ p' p μ₁ μ₂ μ₃ hsum hp1 hp2
    rw [orient2D_self_outer, orient2D_self_right, mul_zero, add_zero, mul_zero, add_zero] at hid
    have hpc : orient2D p_ p' p < 0 := by unfold orient2D at hccw ⊢; linarith
    have hv_neg : orient2D p_ p' v < 0 := by nlinarith
    have hv_pos : 0 < orient2D v p' p_ := by unfold orient2D at hv_neg ⊢; linarith
    have hin_rot : InIntTri v p' p_ p := ⟨μ₁, μ₃, μ₂, hm1, hm3, hm2, by linarith, by linarith, by linarith⟩
    rw [inIntTri_iff_orient_pos hv_pos] at hin_rot
    exact ⟨by unfold orient2D at hin_rot ⊢; linarith [hin_rot.2.2],
           by unfold orient2D at hin_rot ⊢; linarith [hin_rot.1]⟩

/-- Existence of a `CCWCycle` for any convex-position `C` of size `k + 3`. -/
theorem exists_ccwCycle {n k : ℕ} (S : Fin n → ℝ × ℝ) (C : Finset (Fin n))
    (h_inj : ∀ a ∈ C, ∀ b ∈ C, S a = S b → a = b)
    (h_noncol : ∀ a ∈ C, ∀ b ∈ C, ∀ c ∈ C, a ≠ b → b ≠ c → a ≠ c → orient2D (S a) (S b) (S c) ≠ 0)
    (h_conv : IsConvexPos S C) (hcard : C.card = k + 3) :
    Nonempty (CCWCycle S C k) := by
  have hCne : C.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨i_x, hi_x_mem, hi_x_min⟩ := Finset.exists_min_image C (fun i => (S i).1) hCne
  let Xmin : Finset (Fin n) := C.filter (fun i => (S i).1 = (S i_x).1)
  have hXne : Xmin.Nonempty := ⟨i_x, Finset.mem_filter.mpr ⟨hi_x_mem, rfl⟩⟩
  obtain ⟨i0, hi0_X, hi0_ymin⟩ := Finset.exists_min_image Xmin (fun i => (S i).2) hXne
  have hi0 : i0 ∈ C := (Finset.mem_filter.mp hi0_X).1
  have hi0_x : (S i0).1 = (S i_x).1 := (Finset.mem_filter.mp hi0_X).2
  have hi0_lex : ∀ j ∈ C, j ≠ i0 →
      (S i0).1 < (S j).1 ∨ ((S i0).1 = (S j).1 ∧ (S i0).2 < (S j).2) := by
    intro j hj hj0
    have hle : (S i0).1 ≤ (S j).1 := hi0_x ▸ hi_x_min j hj
    rcases lt_or_eq_of_le hle with hlt | heq
    · exact Or.inl hlt
    · right
      refine ⟨heq, ?_⟩
      have hjX : j ∈ Xmin := Finset.mem_filter.mpr ⟨hj, heq.symm.trans hi0_x⟩
      have hyle : (S i0).2 ≤ (S j).2 := hi0_ymin j hjX
      rcases lt_or_eq_of_le hyle with hylt | hyeq
      · exact hylt
      · exfalso; apply hj0; apply h_inj j hj i0 hi0
        ext <;> [exact heq.symm; exact hyeq.symm]
  let R : Finset (Fin n) := C.erase i0
  have hRcard : R.card = k + 2 := by rw [Finset.card_erase_of_mem hi0, hcard]; omega
  let r : {x // x ∈ R} → {x // x ∈ R} → Prop :=
    fun a b => a = b ∨ 0 < orient2D (S i0) (S a.1) (S b.1)
  have hr_trans : IsTrans {x // x ∈ R} r := ⟨by
    intro a b c hab hbc
    rcases hab with rfl | hab
    · exact hbc
    · rcases hbc with rfl | hbc
      · exact Or.inr hab
      · right
        have haC : a.1 ∈ C := Finset.mem_of_mem_erase a.2
        have hbC : b.1 ∈ C := Finset.mem_of_mem_erase b.2
        have hcC : c.1 ∈ C := Finset.mem_of_mem_erase c.2
        have ha0 : a.1 ≠ i0 := (Finset.mem_erase.mp a.2).1
        have hb0 : b.1 ≠ i0 := (Finset.mem_erase.mp b.2).1
        have hc0 : c.1 ≠ i0 := (Finset.mem_erase.mp c.2).1
        have hla := hi0_lex a.1 haC ha0
        have hlb := hi0_lex b.1 hbC hb0
        have hlc := hi0_lex c.1 hcC hc0
        unfold orient2D at hab hbc ⊢
        have hax_pos : (S i0).1 < (S a.1).1 := by
          rcases hla with hlt | ⟨heq, hlt⟩
          · exact hlt
          · exfalso
            have hb_ge : (S i0).1 ≤ (S b.1).1 := by rcases hlb with h | ⟨h, _⟩ <;> linarith
            rw [← heq] at hab
            nlinarith
        have hbx_pos : (S i0).1 < (S b.1).1 := by
          rcases hlb with hlt | ⟨heq, hlt⟩
          · exact hlt
          · exfalso
            have hc_ge : (S i0).1 ≤ (S c.1).1 := by rcases hlc with h | ⟨h, _⟩ <;> linarith
            rw [← heq] at hbc
            nlinarith
        rcases hlc with hcx | ⟨hcx, hcy⟩
        · nlinarith [mul_pos (sub_pos.mpr hcx) hab, mul_pos (sub_pos.mpr hax_pos) hbc]
        · rw [← hcx]; nlinarith [mul_pos (sub_pos.mpr hax_pos) (sub_pos.mpr hcy)]⟩
  have hr_anti : Std.Antisymm r := ⟨by
    intro a b hab hba
    rcases hab with rfl | hab
    · rfl
    · rcases hba with rfl | hba
      · rfl
      · exfalso
        have : orient2D (S i0) (S b.1) (S a.1) = -orient2D (S i0) (S a.1) (S b.1) :=
          orient2D_swap23 _ _ _
        linarith⟩
  have hr_tot : Std.Total r := ⟨by
    intro a b
    by_cases hab : a = b
    · exact Or.inl (Or.inl hab)
    · have haC : a.1 ∈ C := Finset.mem_of_mem_erase a.2
      have hbC : b.1 ∈ C := Finset.mem_of_mem_erase b.2
      have ha0 : a.1 ≠ i0 := (Finset.mem_erase.mp a.2).1
      have hb0 : b.1 ≠ i0 := (Finset.mem_erase.mp b.2).1
      have hab1 : a.1 ≠ b.1 := fun h => hab (Subtype.ext h)
      have hne := h_noncol i0 hi0 a.1 haC b.1 hbC ha0.symm hab1 hb0.symm
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · right; right; have := orient2D_swap23 (S i0) (S a.1) (S b.1); linarith
      · left; right; exact hgt⟩
  let L : List {x // x ∈ R} := Finset.univ.sort r
  have hL_len : L.length = k + 2 := by
    rw [Finset.length_sort, Finset.card_univ, Fintype.card_coe, hRcard]
  have hL_nodup : L.Nodup := Finset.sort_nodup Finset.univ r
  have hL_pair : L.Pairwise r := Finset.pairwise_sort Finset.univ r
  let fullList : List (Fin n) := i0 :: L.map Subtype.val
  have hfull_len : fullList.length = k + 3 := by
    simp [fullList, hL_len]
  have hfull_nodup : fullList.Nodup := by
    rw [List.nodup_cons]
    refine ⟨?_, List.Nodup.map Subtype.val_injective hL_nodup⟩
    intro hmem
    rcases List.mem_map.mp hmem with ⟨x, _, hx⟩
    exact (Finset.mem_erase.mp x.2).1 hx
  let toFun : Fin (k + 3) → Fin n := fun i => fullList.get (i.cast hfull_len.symm)
  have h_inj_fun : Function.Injective toFun := by
    intro i j hij
    have hij' : fullList.get (i.cast hfull_len.symm) = fullList.get (j.cast hfull_len.symm) := hij
    have heq := (List.nodup_iff_injective_get.mp hfull_nodup) hij'
    exact Fin.ext (by simpa using congrArg Fin.val heq)
  have himg : Finset.univ.image toFun = C := by
    ext x
    constructor
    · intro hx
      rcases Finset.mem_image.mp hx with ⟨i, _, rfl⟩
      have hmem : fullList.get (i.cast hfull_len.symm) ∈ fullList := List.get_mem _ _
      simp only [fullList, List.mem_cons, List.mem_map] at hmem
      rcases hmem with hxi | ⟨y, _, hyx⟩
      · change toFun i ∈ C; dsimp only [toFun, fullList]; rw [hxi]; exact hi0
      · change toFun i ∈ C; dsimp only [toFun, fullList]; rw [← hyx]; exact Finset.mem_of_mem_erase y.2
    · intro hx
      have hmem : x ∈ fullList := by
        simp only [fullList, List.mem_cons, List.mem_map]
        by_cases hx0 : x = i0
        · exact Or.inl hx0
        · right
          refine ⟨⟨x, Finset.mem_erase.mpr ⟨hx0, hx⟩⟩, ?_, rfl⟩
          exact (Finset.mem_sort r).mpr (Finset.mem_univ _)
      rcases List.mem_iff_get.mp hmem with ⟨i, hi⟩
      exact Finset.mem_image.mpr ⟨i.cast hfull_len, Finset.mem_univ _, hi⟩
  have hinc : ∀ a b c : Fin (k + 3), a < b → b < c →
      0 < orient2D (S (toFun a)) (S (toFun b)) (S (toFun c)) := by
    have hL_pair' : ∀ {p q : ℕ} (hp : p < L.length) (hq : q < L.length), p < q →
        0 < orient2D (S i0) (S (L.get ⟨p, hp⟩).1) (S (L.get ⟨q, hq⟩).1) := by
      intro p q hp hq hpq
      have hrel := List.pairwise_iff_get.mp hL_pair ⟨p, hp⟩ ⟨q, hq⟩ hpq
      rcases hrel with heq | hpos
      · exfalso
        have := (List.nodup_iff_injective_get.mp hL_nodup) heq
        have : p = q := congrArg Fin.val this
        omega
      · exact hpos
    intro a b c hab hbc
    rcases a with ⟨av, ha⟩
    rcases b with ⟨bv, hb⟩
    rcases c with ⟨cv, hc⟩
    change av < bv at hab
    change bv < cv at hbc
    by_cases ha0 : av = 0
    · subst ha0
      have hb_pos : 0 < bv := hab
      have hc_pos : 0 < cv := by omega
      have hb' : bv - 1 < L.length := by omega
      have hc' : cv - 1 < L.length := by omega
      have h0eq : toFun ⟨0, ha⟩ = i0 := rfl
      have hbeq : toFun ⟨bv, hb⟩ = (L.get ⟨bv - 1, hb'⟩).1 := by
        dsimp [toFun, fullList]
        rcases Nat.exists_eq_succ_of_ne_zero (by omega : bv ≠ 0) with ⟨m, rfl⟩
        simp
      have hceq : toFun ⟨cv, hc⟩ = (L.get ⟨cv - 1, hc'⟩).1 := by
        dsimp [toFun, fullList]
        rcases Nat.exists_eq_succ_of_ne_zero (by omega : cv ≠ 0) with ⟨m, rfl⟩
        simp
      rw [h0eq, hbeq, hceq]
      exact hL_pair' hb' hc' (by omega)
    · have ha' : av - 1 < L.length := by omega
      have hb' : bv - 1 < L.length := by omega
      have hc' : cv - 1 < L.length := by omega
      have haeq : toFun ⟨av, ha⟩ = (L.get ⟨av - 1, ha'⟩).1 := by
        dsimp [toFun, fullList]
        rcases Nat.exists_eq_succ_of_ne_zero ha0 with ⟨m, rfl⟩
        simp
      have hbeq : toFun ⟨bv, hb⟩ = (L.get ⟨bv - 1, hb'⟩).1 := by
        dsimp [toFun, fullList]
        rcases Nat.exists_eq_succ_of_ne_zero (by omega : bv ≠ 0) with ⟨m, rfl⟩
        simp
      have hceq : toFun ⟨cv, hc⟩ = (L.get ⟨cv - 1, hc'⟩).1 := by
        dsimp [toFun, fullList]
        rcases Nat.exists_eq_succ_of_ne_zero (by omega : cv ≠ 0) with ⟨m, rfl⟩
        simp
      rw [haeq, hbeq, hceq]
      have ho1 := hL_pair' ha' hb' (by omega)
      have ho2 := hL_pair' hb' hc' (by omega)
      have ho3 := hL_pair' ha' hc' (by omega)
      have hmem_a : toFun ⟨av, ha⟩ ∈ C := by rw [← himg]; exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
      have hmem_b : toFun ⟨bv, hb⟩ ∈ C := by rw [← himg]; exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
      have hmem_c : toFun ⟨cv, hc⟩ ∈ C := by rw [← himg]; exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
      have hne_ab : toFun ⟨av, ha⟩ ≠ toFun ⟨bv, hb⟩ := fun h => by
        have hv := congrArg Fin.val (h_inj_fun h); simp at hv; omega
      have hne_bc : toFun ⟨bv, hb⟩ ≠ toFun ⟨cv, hc⟩ := fun h => by
        have hv := congrArg Fin.val (h_inj_fun h); simp at hv; omega
      have hne_ac : toFun ⟨av, ha⟩ ≠ toFun ⟨cv, hc⟩ := fun h => by
        have hv := congrArg Fin.val (h_inj_fun h); simp at hv; omega
      rw [← haeq, ← hbeq, ← hceq]
      have hne_abc := h_noncol _ hmem_a _ hmem_b _ hmem_c hne_ab hne_bc hne_ac
      rcases lt_or_gt_of_ne hne_abc with hneg | hpos
      · exfalso
        have hin : InIntTri (S i0) (S (toFun ⟨av, ha⟩)) (S (toFun ⟨cv, hc⟩)) (S (toFun ⟨bv, hb⟩)) := by
          rw [inIntTri_iff_orient_pos (by rw [haeq, hceq]; exact ho3)]
          refine ⟨?_, ?_, ?_⟩
          · rw [haeq, hbeq]; exact ho1
          · unfold orient2D at hneg ⊢; linarith
          · rw [hbeq, hceq]; unfold orient2D at ho2 ⊢; linarith
        apply h_conv (toFun ⟨bv, hb⟩) hmem_b
        refine convexHull_mono ?_ hin.to_convexHull
        intro z hz
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
        rcases hz with rfl | rfl | rfl
        · exact Finset.mem_image.mpr ⟨i0, Finset.mem_erase.mpr ⟨fun h => by
            have hv := congrArg Fin.val (h_inj_fun (h.symm.trans (show i0 = toFun ⟨0, by omega⟩ from rfl)))
            simp at hv; omega, hi0⟩, rfl⟩
        · exact Finset.mem_image.mpr ⟨toFun ⟨av, ha⟩, Finset.mem_erase.mpr ⟨hne_ab, hmem_a⟩, rfl⟩
        · exact Finset.mem_image.mpr ⟨toFun ⟨cv, hc⟩, Finset.mem_erase.mpr ⟨hne_bc.symm, hmem_c⟩, rfl⟩
      · exact hpos
  refine ⟨⟨toFun, h_inj_fun, himg, ?_, hinc⟩⟩
  intro i j hij1 hij2
  have h1_val : (1 : Fin (k + 3)).val = 1 := by
    change 1 % (k + 3) = 1
    exact Nat.mod_eq_of_lt (by omega)
  by_cases hi_last : i.val + 1 = k + 3
  · have hi1 : i + 1 = ⟨0, by omega⟩ := by
      ext; rw [Fin.val_add, h1_val, hi_last, Nat.mod_self]
    have hj0 : ⟨0, by omega⟩ < j := Fin.pos_of_ne_zero (fun h => hij2 (hi1 ▸ h))
    have hi_last' : i = Fin.last (k + 2) := Fin.ext (by change i.val = k + 2; omega)
    have hji : j < i := by
      rw [hi_last'] at hij1 ⊢
      exact lt_of_le_of_ne (Fin.le_last j) hij1
    have h := hinc ⟨0, by omega⟩ j i hj0 hji
    dsimp [Function.comp]
    rw [hi1, ← orient2D_cycle]
    exact h
  · have hi1_val : (i + 1).val = i.val + 1 := by
      rw [Fin.val_add, h1_val, Nat.mod_eq_of_lt (by omega)]
    have hi_lt_i1 : i < i + 1 := Fin.lt_def.mpr (by rw [hi1_val]; omega)
    rcases lt_trichotomy j i with hji | rfl | hij
    · have h := hinc j i (i + 1) hji hi_lt_i1
      dsimp [Function.comp]
      rw [orient2D_cycle]; exact h
    · exact False.elim (hij1 rfl)
    · have hi1_lt_j : i + 1 < j :=
        lt_of_le_of_ne (Fin.le_def.mpr (by rw [hi1_val]; exact Fin.lt_def.mp hij)) (Ne.symm hij2)
      exact hinc i (i + 1) j hi_lt_i1 hi1_lt_j

/-! ## Part 3: Witness Counting & Half-Plane-to-Wedge Conversion on Finite Witness Sets -/

lemma witnessSet_mono {n : ℕ} {F F' N N' : Finset (Fin n)} {w : Finset (Fin n) → ℝ × ℝ}
    (hF : F ⊆ F') (hN : N ⊆ N') :
    WitnessSet F' N' w ⊆ WitnessSet F N w := by
  rintro x ⟨T, hFT, hTN, rfl⟩
  exact ⟨T, hF.trans hFT, disjoint_of_subset_right hN hTN, rfl⟩

lemma isHalfPlaneTest_mono {P : Set (ℝ × ℝ)} {W₁ W₂ : Set (ℝ × ℝ)} {a : ℝ × ℝ} {H : OpenHalfPlane}
    (hsub : W₁ ⊆ W₂) (h : IsHalfPlaneTest P W₂ a H) : IsHalfPlaneTest P W₁ a H :=
  fun x hx => h x (hsub hx)

lemma isWedgeTest_mono {P : Set (ℝ × ℝ)} {W₁ W₂ : Set (ℝ × ℝ)} {a : ℝ × ℝ} {R : OpenWedge}
    (hsub : W₁ ⊆ W₂) (h : IsWedgeTest P W₂ a R) : IsWedgeTest P W₁ a R :=
  fun x hx => h x (hsub hx)

lemma witnessSet_finite {n : ℕ} (F N : Finset (Fin n)) (w : Finset (Fin n) → ℝ × ℝ) :
    (WitnessSet F N w).Finite :=
  (Set.finite_range w).subset (by rintro _ ⟨T, _, _, rfl⟩; exact Set.mem_range_self T)

/-- On any finite witness set `W'`, an open half-plane test can be replaced by an open wedge test
    (`upper_9.tex` line 150). -/
lemma halfPlaneTest_to_wedgeTest_on_finite
    (P : Set (ℝ × ℝ)) (W' : Set (ℝ × ℝ)) (hfin : W'.Finite) (a : ℝ × ℝ) (H : OpenHalfPlane)
    (hH : IsHalfPlaneTest P W' a H) :
    ∃ R : OpenWedge, IsWedgeTest P W' a R := by
  have hs_pos : 0 < H.n.1 ^ 2 + H.n.2 ^ 2 := by
    rcases H.hn with h1 | h2
    · exact add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero h1) (sq_nonneg _)
    · exact add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_ne_zero h2)
  have hs_ne : H.n.1 ^ 2 + H.n.2 ^ 2 ≠ 0 := ne_of_gt hs_pos
  let s := H.n.1 ^ 2 + H.n.2 ^ 2
  let y0 : ℝ × ℝ := (-H.c * H.n.1 / s, -H.c * H.n.2 / s)
  have hy0_eq : ∀ x : ℝ × ℝ,
      H.n.1 * (x.1 - y0.1) + H.n.2 * (x.2 - y0.2) = H.n.1 * x.1 + H.n.2 * x.2 + H.c := by
    intro x; dsimp [y0, s]; field_simp [hs_ne]; ring
  let val : ℝ × ℝ → ℝ := fun x => H.n.1 * x.1 + H.n.2 * x.2 + H.c
  let tan : ℝ × ℝ → ℝ := fun x => -H.n.2 * (x.1 - y0.1) + H.n.1 * (x.2 - y0.2)
  let S_fin : Finset (ℝ × ℝ) := hfin.toFinset
  let Mtan : ℝ := 1 + ∑ x ∈ S_fin, |tan x|
  let invEps : ℝ := 1 + Mtan * (∑ x ∈ S_fin, 1 / |val x|)
  have hMtan_pos : 0 < Mtan := by
    have : 0 ≤ ∑ x ∈ S_fin, |tan x| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
    dsimp [Mtan]; linarith
  have hsum_nonneg : 0 ≤ ∑ x ∈ S_fin, 1 / |val x| :=
    Finset.sum_nonneg (fun _ _ => div_nonneg zero_le_one (abs_nonneg _))
  have hinv_pos : 0 < invEps := by dsimp [invEps]; nlinarith
  let ε : ℝ := 1 / invEps
  have hε_pos : 0 < ε := div_pos zero_lt_one hinv_pos
  let u₁ : ℝ × ℝ := (H.n.1 + ε * H.n.2, H.n.2 - ε * H.n.1)
  let u₂ : ℝ × ℝ := (H.n.1 - ε * H.n.2, H.n.2 + ε * H.n.1)
  let R : OpenWedge :=
    { y := y0
      u₁ := u₁
      u₂ := u₂
      h_nondeg := by
        have hdet : u₁.1 * u₂.2 - u₁.2 * u₂.1 = 2 * ε * (H.n.1 ^ 2 + H.n.2 ^ 2) := by
          dsimp [u₁, u₂]; ring
        rw [hdet]
        exact mul_pos (mul_pos two_pos hε_pos) hs_pos }
  refine ⟨R, fun x hx => ?_⟩
  have hxS : x ∈ S_fin := hfin.mem_toFinset.mpr hx
  have hval_ne : val x ≠ 0 := by
    rcases (hH x hx).1 with hp | hn
    · exact ne_of_gt hp
    · exact ne_of_lt hn
  have hval_abs_pos : 0 < |val x| := abs_pos.mpr hval_ne
  have hle_tan : |tan x| ≤ Mtan := by
    have h1 := Finset.single_le_sum (f := fun z => |tan z|) (fun _ _ => abs_nonneg _) hxS
    dsimp [Mtan]; linarith
  have hle_inv : 1 / |val x| ≤ ∑ z ∈ S_fin, 1 / |val z| :=
    Finset.single_le_sum (f := fun z => 1 / |val z|) (fun _ _ => div_nonneg zero_le_one (abs_nonneg _)) hxS
  have hmargin : ε * |tan x| < |val x| := by
    have h1 : Mtan * (1 / |val x|) < invEps := by
      dsimp [invEps]; nlinarith
    have h2 : |tan x| / |val x| < invEps := by
      have : |tan x| * (1 / |val x|) ≤ Mtan * (1 / |val x|) :=
        mul_le_mul_of_nonneg_right hle_tan (div_nonneg zero_le_one (le_of_lt hval_abs_pos))
      rw [div_eq_mul_one_div]; linarith
    have h3 : |tan x| / invEps < |val x| := (div_lt_comm₀ hval_abs_pos hinv_pos).mp h2
    have h4 : ε * |tan x| = |tan x| / invEps := by dsimp [ε]; ring
    linarith
  have hid1 : R.u₁.1 * (x.1 - R.y.1) + R.u₁.2 * (x.2 - R.y.2) = val x - ε * tan x := by
    dsimp [R, u₁, val, tan]; rw [← hy0_eq x]; ring
  have hid2 : R.u₂.1 * (x.1 - R.y.1) + R.u₂.2 * (x.2 - R.y.2) = val x + ε * tan x := by
    dsimp [R, u₂, val, tan]; rw [← hy0_eq x]; ring
  have hbound : -|val x| < ε * tan x ∧ ε * tan x < |val x| := by
    have := neg_le_abs (tan x)
    have := le_abs_self (tan x)
    exact ⟨by nlinarith, by nlinarith⟩
  rcases (hH x hx).1 with hp | hn
  · have hvp : 0 < val x := hp
    have hpos : val x = |val x| := (abs_of_pos hvp).symm
    have h1 : 0 < R.u₁.1 * (x.1 - R.y.1) + R.u₁.2 * (x.2 - R.y.2) := by
      rw [hid1]; linarith [hbound.2, hpos]
    have h2 : 0 < R.u₂.1 * (x.1 - R.y.1) + R.u₂.2 * (x.2 - R.y.2) := by
      rw [hid2]; linarith [hbound.1, hpos]
    have hopen : R.MemOpen x := ⟨h1, h2⟩
    refine ⟨Or.inl hopen, ?_⟩
    rw [(hH x hx).2]
    exact ⟨fun _ => hopen, fun _ => hp⟩
  · have hvn : val x < 0 := hn
    have hneg : -val x = |val x| := (abs_of_neg hvn).symm
    have h1 : R.u₁.1 * (x.1 - R.y.1) + R.u₁.2 * (x.2 - R.y.2) < 0 := by
      rw [hid1]; linarith [hbound.1, hneg]
    have h2 : R.u₂.1 * (x.1 - R.y.1) + R.u₂.2 * (x.2 - R.y.2) < 0 := by
      rw [hid2]; linarith [hbound.2, hneg]
    have hext : R.MemExt x := Or.inl h1
    refine ⟨Or.inr hext, ?_⟩
    rw [(hH x hx).2]
    constructor
    · intro hp; exfalso; dsimp [OpenHalfPlane.MemPos] at hp; dsimp [val] at hvn; linarith
    · intro hopen; exfalso; linarith [hopen.1, h1]

/-- Counting lemma (`Lemma 2.5`) realizing all bitmasks on `WitnessSet F N w`. -/
lemma witness_counting_realizes {n kH kW : ℕ} {P : Set (ℝ × ℝ)}
    {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ}
    (hPoly : ShatteredSimplePolygon P S w)
    {F N : Finset (Fin n)} (hdisj : Disjoint F N)
    (aH : Fin kH → Fin n) (aW : Fin kW → Fin n)
    (ha_inj : Function.Injective (Sum.elim aH aW))
    (haH_out : ∀ i, aH i ∉ F ∧ aH i ∉ N)
    (haW_out : ∀ j, aW j ∉ F ∧ aW j ∉ N)
    (H : Fin kH → OpenHalfPlane) (R : Fin kW → OpenWedge)
    (hH : ∀ i, IsHalfPlaneTest P (WitnessSet F N w) (S (aH i)) (H i))
    (hR : ∀ j, IsWedgeTest P (WitnessSet F N w) (S (aW j)) (R j))
    (mH : Fin kH → Bool) (mW : Fin kW → Bool) :
    ∃ p ∈ WitnessSet F N w,
      (∀ i, if mH i then (H i).MemPos p else (H i).MemNeg p) ∧
      (∀ j, if mW j then (R j).MemOpen p else (R j).MemExt p) := by
  let T : Finset (Fin n) := F ∪
    ((Finset.univ.filter (fun i => mH i = true)).image aH) ∪
    ((Finset.univ.filter (fun j => mW j = true)).image aW)
  have hFT : F ⊆ T := by intro x hx; simp [T, hx]
  have hTN : Disjoint T N := by
    rw [Finset.disjoint_left]
    intro x hx hxN
    simp only [T, Finset.mem_union, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    rcases hx with (hxF | ⟨i, _, rfl⟩) | ⟨j, _, rfl⟩
    · exact Finset.disjoint_left.mp hdisj hxF hxN
    · exact (haH_out i).2 hxN
    · exact (haW_out j).2 hxN
  refine ⟨w T, ⟨T, hFT, hTN, rfl⟩, ?_, ?_⟩
  · intro i
    have hi_T : aH i ∈ T ↔ mH i = true := by
      simp only [T, Finset.mem_union, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ((hF | ⟨i', hi', heq⟩) | ⟨j', _, heq⟩)
        · exact False.elim ((haH_out i).1 hF)
        · have : Sum.inl i' = Sum.inl i := ha_inj heq
          cases this; exact hi'
        · have : Sum.inr j' = Sum.inl i := ha_inj heq
          cases this
      · intro hm; left; right; exact ⟨i, hm, rfl⟩
    have htest := hH i (w T) ⟨T, hFT, hTN, rfl⟩
    have hsees : Sees P (w T) (S (aH i)) ↔ aH i ∈ T := hPoly.shatters T (aH i)
    cases hm : mH i
    · simp only [Bool.false_eq_true, ↓reduceIte]
      rcases htest.1 with hp | hn
      · exfalso
        have : aH i ∈ T := hsees.mp (htest.2.mpr hp)
        rw [hi_T, hm] at this; contradiction
      · exact hn
    · simp only [↓reduceIte]
      exact htest.2.mp (hsees.mpr (hi_T.mpr hm))
  · intro j
    have hj_T : aW j ∈ T ↔ mW j = true := by
      simp only [T, Finset.mem_union, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ((hF | ⟨i', _, heq⟩) | ⟨j', hj', heq⟩)
        · exact False.elim ((haW_out j).1 hF)
        · have : Sum.inl i' = Sum.inr j := ha_inj heq
          cases this
        · have : Sum.inr j' = Sum.inr j := ha_inj heq
          cases this; exact hj'
      · intro hm; right; exact ⟨j, hm, rfl⟩
    have htest := hR j (w T) ⟨T, hFT, hTN, rfl⟩
    have hsees : Sees P (w T) (S (aW j)) ↔ aW j ∈ T := hPoly.shatters T (aW j)
    cases hm : mW j
    · simp only [Bool.false_eq_true, ↓reduceIte]
      rcases htest.1 with ho | he
      · exfalso
        have : aW j ∈ T := hsees.mp (htest.2.mpr ho)
        rw [hj_T, hm] at this; contradiction
      · exact he
    · simp only [↓reduceIte]
      exact htest.2.mp (hsees.mpr (hj_T.mpr hm))

/-! ## Part 4: Clean Sections 2.3–5 Interface (`Sec2To5Interface`) -/

/-- Exact interface of Sections 2.3–5 (`upper_9.tex` lines 201–591) over
    `ShatteredSimplePolygon P S w`. -/
structure Sec2To5Interface {n : ℕ} (P : Set (ℝ × ℝ))
    (S : Fin n → ℝ × ℝ) (w : Finset (Fin n) → ℝ × ℝ) : Prop where
  three_halfplanes : ∀ H : Fin 3 → OpenHalfPlane,
    ¬ (∀ m : Fin 3 → Bool, ∃ p : ℝ × ℝ, ∀ i : Fin 3,
      if m i then (H i).MemPos p else (H i).MemNeg p)
  two_hp_three_wedges : ∀ (H : Fin 2 → OpenHalfPlane) (R : Fin 3 → OpenWedge),
    ¬ (∀ (mH : Fin 2 → Bool) (mW : Fin 3 → Bool), ∃ p : ℝ × ℝ,
      (∀ i : Fin 2, if mH i then (H i).MemPos p else (H i).MemNeg p) ∧
      (∀ j : Fin 3, if mW j then (R j).MemOpen p else (R j).MemExt p))
  cone_lemma : ∀ (a b c w0 x : ℝ × ℝ),
    a ∈ P → b ∈ P → c ∈ P → w0 ∈ P → x ∈ P →
    Sees P w0 b → Sees P w0 c → ¬ Sees P w0 a →
    InIntTri w0 b c a → Sees P x b → Sees P x c →
    orient2D a b x ≠ 0 → orient2D a c x ≠ 0 → orient2D w0 a x ≠ 0 →
    InIntTri x b c a
  wedge_extraction : ∀ (a b c : Fin n) (W' : Set (ℝ × ℝ)) (U : OpenWedge),
    a ≠ b → a ≠ c → b ≠ c →
    W' ⊆ WitnessSet {b, c} ∅ w →
    U.y = S a →
    (∀ x : ℝ × ℝ, U.MemOpen x → orient2D (S a) x (S b) * orient2D (S a) x (S c) < 0) →
    (∀ x ∈ W', Sees P x (S a) → U.MemOpen x) →
    ∃ R : OpenWedge, R.y = S a ∧ (∀ z : ℝ × ℝ, R.MemOpen z → U.MemOpen z) ∧
      IsWedgeTest P W' (S a) R
  fan_corollary : ∀ (Tw F : Finset (Fin n)) (a : Fin n),
    F ⊆ Tw → a ∉ Tw →
    S a ∈ convexHull ℝ (((F.image S) : Set (ℝ × ℝ)) ∪ {w Tw}) →
    ∃ R : OpenWedge, IsWedgeTest P (WitnessSet F ∅ w) (S a) R
  hidden_targets : ∀ (T : Finset (Fin n)),
    T ⊆ hullVertices S →
    (∀ t ∈ T, ∃ (b c : Fin n) (Tv : Finset (Fin n)),
      b ∈ hullVertices S \ T ∧ c ∈ hullVertices S \ T ∧ b ≠ c ∧
      b ∈ Tv ∧ c ∈ Tv ∧ t ∉ Tv ∧ InIntTri (w Tv) (S b) (S c) (S t)) →
    (interiorPoints S).card + T.card ≤ 5
  hidden_front : ∀ (C : Finset (Fin n)) (Tv : Finset (Fin n)) (f b c : Fin n),
    C ⊆ hullVertices S → 3 ≤ C.card →
    f ∈ C → IsCCWEdge S C b f → IsCCWEdge S C f c →
    b ∈ Tv → c ∈ Tv → f ∉ Tv →
    IsFrontVertexOf S C f (w Tv) →
    InIntTri (w Tv) (S b) (S c) (S f) ∧
    ∀ Tx : Finset (Fin n), b ∈ Tx → c ∈ Tx →
      InIntTri (w Tx) (S b) (S c) (S f) ∧ IsFrontVertexOf S C f (w Tx)
  front_restoration : ∀ (C D' : Finset (Fin n)) (f : Fin n) (v : ℝ × ℝ),
    C ⊆ D' → IsConvexPos S D' → 3 ≤ C.card →
    v ∈ Set.range w →
    IsFrontVertexOf S C f v →
    IsFrontVertexOf S D' f v
  certified_structure :
    let B := hullVertices S
    let H := certifiedVertices S w
    let D := B \ H
    (interiorPoints S).card + H.card ≤ 5 ∧
    (H.Nonempty → ∃ l r : Fin n, l ∈ D ∧ r ∈ D ∧ l ≠ r ∧
      (3 ≤ D.card → IsCCWEdge S D l r) ∧
      (∀ h ∈ H, orient2D (S l) (S r) (S h) < 0) ∧
      (∀ d ∈ D, d ≠ l → d ≠ r → 0 < orient2D (S l) (S r) (S d)) ∧
      (∀ (h : Fin n) (T : Finset (Fin n)), h ∈ H → l ∈ T → r ∈ T →
        InIntTri (w T) (S l) (S r) (S h)) ∧
      (∀ d ∈ D, d ≠ l → d ≠ r → ∀ x ∈ B,
        (IsCCWEdge S B x d ↔ IsCCWEdge S D x d) ∧
        (IsCCWEdge S B d x ↔ IsCCWEdge S D d x)) ∧
      (H.card = 1 → ∀ h ∈ H, IsCCWEdge S B l h ∧ IsCCWEdge S B h r) ∧
      (2 ≤ H.card → ∃ h1 h2 : Fin n, h1 ∈ H ∧ h2 ∈ H ∧ h1 ≠ h2 ∧
        IsCCWEdge S B l h1 ∧ IsCCWEdge S B h1 h2))
  side_preservation :
    let B := hullVertices S
    let H := certifiedVertices S w
    let D := B \ H
    let M := Finset.univ \ D
    H.Nonempty → 5 ≤ D.card →
    ∀ (Q M0 : Finset (Fin n)), Q ⊆ D → Q.card ≤ 2 → M0 ⊆ M →
    (∀ p ∈ Q, ∃ O : Finset (Fin n), p ∉ O ∧
      (∀ a ∈ O ∩ D, ∀ b ∈ O ∩ D, ¬ IsCCWEdge S B a b) ∧
      IsBackVertexOf S B p (w (Finset.univ \ O))) →
    let F := (D \ Q) ∪ M0
    ∀ h ∈ H \ M0, ∃ a b : Fin n, a ∈ F ∧ b ∈ F ∧ a ≠ b ∧
      ∀ x ∈ WitnessSet {a, b} ∅ w, InIntTri x (S a) (S b) (S h)
  exit_edge_lemma :
    let B := hullVertices S
    let H := certifiedVertices S w
    let D := B \ H
    let M := Finset.univ \ D
    3 ≤ D.card →
    ∀ y ∈ M, ∃ u v : Fin n, IsCCWEdge S D u v ∧
      0 < orient2D (S u) (S v) (w D) ∧
      InIntTri (w D) (S u) (S v) (S y) ∧
      (∀ l r : Fin n, H.Nonempty → IsCCWEdge S D l r →
        (∀ h ∈ H, orient2D (S l) (S r) (S h) < 0) → (u, v) ≠ (l, r)) ∧
      (∀ x ∈ WitnessSet {u, v} ∅ w, InIntTri x (S u) (S v) (S y)) ∧
      (∀ u' v' : Fin n, IsCCWEdge S D u' v' →
        0 < orient2D (S u') (S v') (w D) →
        S y ∈ convexHull ℝ ({w D, S u', S v'} : Set (ℝ × ℝ)) →
        u' = u ∧ v' = v)
  endpoint_back_criterion :
    let B := hullVertices S
    let H := certifiedVertices S w
    let D := B \ H
    H.Nonempty → 5 ≤ D.card →
    ∀ l r p y : Fin n,
      l ∈ D → r ∈ D → l ≠ r → IsCCWEdge S D l r →
      (∀ h ∈ H, orient2D (S l) (S r) (S h) < 0) →
      (p = l ∧ y = r ∨ p = r ∧ y = l) →
      (∃ O : Finset (Fin n), p ∉ O ∧
        (∀ a ∈ O ∩ D, ∀ b ∈ O ∩ D, ¬ IsCCWEdge S B a b) ∧
        IsBackVertexOf S B p (w (Finset.univ \ O))) →
      (∀ h ∈ H, ∀ u v : Fin n, IsCCWEdge S D u v →
        InIntTri (w D) (S u) (S v) (S h) →
        (u = y ∨ v = y)) ∧
      ¬ (∃ O' : Finset (Fin n), y ∉ O' ∧
        (∀ a ∈ O' ∩ D, ∀ b ∈ O' ∩ D, ¬ IsCCWEdge S B a b) ∧
        IsBackVertexOf S B y (w (Finset.univ \ O')))
  half_plane_lemma :
    ∀ (Tv Tq : Finset (Fin n)) (a p c : Fin n),
      p ∈ Tv → a ∉ Tv → c ∉ Tv →
      a ∈ Tq → p ∈ Tq → c ∈ Tq →
      AngleLt (w Tv) (w Tq) (S a) (S p) →
      AngleLt (w Tv) (w Tq) (S p) (S c) →
      SegmentsCross (w Tv) (S p) (S a) (S c) →
      (Sees P (w Tv) (w Tq) ∨
        ∃ e : Fin n, e ∈ Tv ∧ e ∈ Tq ∧ AngleLt (w Tv) (w Tq) (S e) (S a)) →
      ∃ H_hp : OpenHalfPlane, IsHalfPlaneTest P (WitnessSet {a, c} ∅ w) (S p) H_hp

/-- No 3 half-plane tests on `WitnessSet F N w` for distinct points outside `F ∪ N`. -/
lemma no_three_halfplanes_on_witnessSet {n : ℕ} {P : Set (ℝ × ℝ)}
    {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ}
    (hPoly : ShatteredSimplePolygon P S w) (h25 : Sec2To5Interface P S w)
    {F N : Finset (Fin n)} (hdisj : Disjoint F N)
    (a : Fin 3 → Fin n) (hainj : Function.Injective a)
    (ha_out : ∀ i, a i ∉ F ∧ a i ∉ N)
    (H : Fin 3 → OpenHalfPlane)
    (hH : ∀ i, IsHalfPlaneTest P (WitnessSet F N w) (S (a i)) (H i)) :
    False := by
  apply h25.three_halfplanes H
  intro m
  obtain ⟨p, _, hm, _⟩ := witness_counting_realizes hPoly hdisj a Fin.elim0
    (fun x y h => by
      rcases x with x | x <;> rcases y with y | y
      · exact congrArg Sum.inl (hainj h)
      · exact Fin.elim0 y
      · exact Fin.elim0 x
      · exact Fin.elim0 x)
    ha_out (fun j => Fin.elim0 j) H (fun j => Fin.elim0 j) hH (fun j => Fin.elim0 j)
    m (fun j => Fin.elim0 j)
  exact ⟨p, hm⟩

/-- No 2 half-plane tests + 3 wedge tests on `WitnessSet F N w`. -/
lemma no_two_hp_three_wedges_on_witnessSet {n : ℕ} {P : Set (ℝ × ℝ)}
    {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ}
    (hPoly : ShatteredSimplePolygon P S w) (h25 : Sec2To5Interface P S w)
    {F N : Finset (Fin n)} (hdisj : Disjoint F N)
    (aH : Fin 2 → Fin n) (aW : Fin 3 → Fin n)
    (ha_inj : Function.Injective (Sum.elim aH aW))
    (haH_out : ∀ i, aH i ∉ F ∧ aH i ∉ N)
    (haW_out : ∀ j, aW j ∉ F ∧ aW j ∉ N)
    (H : Fin 2 → OpenHalfPlane) (R : Fin 3 → OpenWedge)
    (hH : ∀ i, IsHalfPlaneTest P (WitnessSet F N w) (S (aH i)) (H i))
    (hR : ∀ j, IsWedgeTest P (WitnessSet F N w) (S (aW j)) (R j)) :
    False := by
  apply h25.two_hp_three_wedges H R
  intro mH mW
  obtain ⟨p, _, hmH, hmW⟩ := witness_counting_realizes hPoly hdisj aH aW ha_inj haH_out haW_out
    H R hH hR mH mW
  exact ⟨p, hmH, hmW⟩

/-- No 6 wedge (or half-plane) tests on `WitnessSet F N w`. -/
lemma no_six_wedges_on_witnessSet {n : ℕ} {P : Set (ℝ × ℝ)}
    {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ}
    (hPoly : ShatteredSimplePolygon P S w)
    {F N : Finset (Fin n)} (hdisj : Disjoint F N)
    (aW : Fin 6 → Fin n) (ha_inj : Function.Injective aW)
    (haW_out : ∀ j, aW j ∉ F ∧ aW j ∉ N)
    (R : Fin 6 → OpenWedge)
    (hR : ∀ j, IsWedgeTest P (WitnessSet F N w) (S (aW j)) (R j)) :
    False := by
  apply hPoly.isler_six_wedges R
  intro mW
  obtain ⟨p, _, _, hmW⟩ := witness_counting_realizes hPoly hdisj Fin.elim0 aW
    (fun x y h => by
      rcases x with x | x <;> rcases y with y | y
      · exact Fin.elim0 x
      · exact Fin.elim0 x
      · exact Fin.elim0 y
      · exact congrArg Sum.inr (ha_inj h))
    (fun i => Fin.elim0 i) haW_out (fun i => Fin.elim0 i) R (fun i => Fin.elim0 i) hR
    (fun i => Fin.elim0 i) mW
  exact ⟨p, hmW⟩

/-! ## Part 5: Far Chain, Contiguous Facing Arcs, and Monotone Angles -/

lemma poly_facing_arc_step {k : ℕ} (c : Fin (k + 3) → ℝ × ℝ) (_hc : StrictConvexCCWPoly c)
    (v : ℝ × ℝ) (_hv_noncol : ∀ i j : Fin (k + 3), i ≠ j → orient2D (c i) (c j) v ≠ 0) :
    ∀ p q r s : Fin (k + 3), p ≠ q → q ≠ r → r ≠ s → s ≠ p →
      -- `p, q, r, s` strictly convex CCW 4-gon:
      0 < orient2D (c q) (c r) (c s) →
      0 < orient2D (c r) (c s) (c p) →
      0 < orient2D (c s) (c p) (c q) →
      0 < orient2D (c p) (c q) (c r) →
      orient2D (c p) (c q) v < 0 → orient2D (c r) (c s) v < 0 →
      orient2D (c q) (c r) v < 0 ∨ orient2D (c s) (c p) v < 0 := by
  intro p q r s _ _ _ _ hα hβ hγ hδ hpq hrs
  let α := orient2D (c q) (c r) (c s)
  let β := orient2D (c r) (c s) (c p)
  let γ := orient2D (c s) (c p) (c q)
  let δ := orient2D (c p) (c q) (c r)
  have hid : α * β * orient2D (c p) (c q) v + γ * δ * orient2D (c r) (c s) v =
      β * γ * orient2D (c q) (c r) v + α * δ * orient2D (c s) (c p) v := by
    dsimp [α, β, γ, δ]; unfold orient2D; ring
  have hlhs : α * β * orient2D (c p) (c q) v + γ * δ * orient2D (c r) (c s) v < 0 := by
    have h1 : α * β * orient2D (c p) (c q) v < 0 :=
      mul_neg_of_pos_of_neg (mul_pos hα hβ) hpq
    have h2 : γ * δ * orient2D (c r) (c s) v < 0 :=
      mul_neg_of_pos_of_neg (mul_pos hγ hδ) hrs
    linarith
  have hrhs : β * γ * orient2D (c q) (c r) v + α * δ * orient2D (c s) (c p) v < 0 := by
    linarith
  by_contra hnot
  push Not at hnot
  have h1 : 0 ≤ β * γ * orient2D (c q) (c r) v := mul_nonneg (le_of_lt (mul_pos hβ hγ)) hnot.1
  have h2 : 0 ≤ α * δ * orient2D (c s) (c p) v := mul_nonneg (le_of_lt (mul_pos hα hδ)) hnot.2
  linarith

/-- Total signed area `∑ i, orient2D (c i) (c (i + 1)) v` is independent of `v` and strictly positive. -/
lemma poly_sum_orient_pos {k : ℕ} (c : Fin (k + 3) → ℝ × ℝ) (hc : StrictConvexCCWPoly c)
    (v : ℝ × ℝ) :
    0 < ∑ i : Fin (k + 3), orient2D (c i) (c (i + 1)) v := by
  have hconst : ∑ i : Fin (k + 3), orient2D (c i) (c (i + 1)) v =
      ∑ i : Fin (k + 3), orient2D (c i) (c (i + 1)) (c 0) := by
    have hdiff : ∑ i : Fin (k + 3), (orient2D (c i) (c (i + 1)) v -
        orient2D (c i) (c (i + 1)) (c 0)) = 0 := by
      have hid : ∀ i : Fin (k + 3), orient2D (c i) (c (i + 1)) v -
          orient2D (c i) (c (i + 1)) (c 0) =
          ((c (i + 1)).1 * (v.2 - (c 0).2) - (c (i + 1)).2 * (v.1 - (c 0).1)) -
          ((c i).1 * (v.2 - (c 0).2) - (c i).2 * (v.1 - (c 0).1)) := by
        intro i; unfold orient2D; ring
      have hid_sum : ∑ i : Fin (k + 3), (orient2D (c i) (c (i + 1)) v -
            orient2D (c i) (c (i + 1)) (c 0)) =
          (∑ i : Fin (k + 3), ((c (i + 1)).1 * (v.2 - (c 0).2) - (c (i + 1)).2 * (v.1 - (c 0).1))) -
          (∑ i : Fin (k + 3), ((c i).1 * (v.2 - (c 0).2) - (c i).2 * (v.1 - (c 0).1))) := by
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl (fun i _ => hid i)
      have hshift : ∑ i : Fin (k + 3), ((c (i + 1)).1 * (v.2 - (c 0).2) -
            (c (i + 1)).2 * (v.1 - (c 0).1)) =
          ∑ i : Fin (k + 3), ((c i).1 * (v.2 - (c 0).2) - (c i).2 * (v.1 - (c 0).1)) :=
        Equiv.sum_comp (Equiv.addRight (1 : Fin (k + 3)))
          (fun i => (c i).1 * (v.2 - (c 0).2) - (c i).2 * (v.1 - (c 0).1))
      rw [hid_sum, hshift, sub_self]
    rw [Finset.sum_sub_distrib] at hdiff
    linarith
  rw [hconst]
  have h2_ne_0 : (2 : Fin (k + 3)) ≠ 0 := by
    intro h; have := congrArg Fin.val h; simp [Nat.mod_eq_of_lt (by omega : 2 < k + 3)] at this
  have h0_pos : 0 < orient2D (c 1) (c (1 + 1)) (c 0) := by
    apply hc 1 0
    · intro h; have := congrArg Fin.val h; simp [Nat.mod_eq_of_lt (by omega : 1 < k + 3)] at this
    · have h11 : (1 + 1 : Fin (k + 3)) = 2 := by
        ext; rw [Fin.val_add]
        simp [Nat.mod_eq_of_lt (by omega : 1 < k + 3), Nat.mod_eq_of_lt (by omega : 2 < k + 3)]
      rw [h11]
      exact h2_ne_0.symm
  have h_nn : ∀ i : Fin (k + 3), 0 ≤ orient2D (c i) (c (i + 1)) (c 0) := by
    intro i
    by_cases hi0 : i = 0
    · subst hi0; rw [orient2D_self_outer]
    · by_cases hi1 : i + 1 = 0
      · rw [hi1, orient2D_self_right]
      · exact le_of_lt (hc i 0 (Ne.symm hi0) (Ne.symm hi1))
  exact Finset.sum_pos' (fun i _ => h_nn i) ⟨1, Finset.mem_univ 1, h0_pos⟩

/-- Every edge-pair on a `CCWCycle` where `v` is non-collinear has at least one non-facing edge. -/
lemma exists_nonfacing_edge {k : ℕ} (c : Fin (k + 3) → ℝ × ℝ) (hc : StrictConvexCCWPoly c)
    (v : ℝ × ℝ) :
    ∃ i : Fin (k + 3), 0 < orient2D (c i) (c (i + 1)) v := by
  by_contra h
  push Not at h
  have hsum_le : ∑ i : Fin (k + 3), orient2D (c i) (c (i + 1)) v ≤ 0 :=
    Finset.sum_nonpos (fun i _ => h i)
  linarith [poly_sum_orient_pos c hc v]

/-! ## Part 6: Lemmas 6.1–6.5 (`no_odd_front`, `targets_halfplane`, `consecutive_odd`, `good_targets`, `gap_lemma`) -/

lemma inIntTri_implies_isFrontVertexOf_tri {n : ℕ} (S : Fin n → ℝ × ℝ)
    {a b f : Fin n} (haf : a ≠ f) (hbf : b ≠ f) (hab : a ≠ b) (v : ℝ × ℝ)
    (hin : InIntTri v (S a) (S b) (S f)) :
    IsFrontVertexOf S {a, f, b} f v := by
  refine ⟨by simp, ?_⟩
  rcases hin with ⟨μ₁, μ₂, μ₃, hμ1, hμ2, hμ3, hsum, hf1, hf2⟩
  intro x y hxy heq
  have hmem_x := hxy.1
  have hmem_y := hxy.2.1
  have hne_xy := hxy.2.2.1
  have hccw := hxy.2.2.2
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem_x hmem_y
  rcases heq with hxf | hyf
  · rcases hmem_y with hy | hy | hy
    · have hz := hccw b (by simp) (by rw [hxf]; exact hbf) (by rw [hy]; exact hab.symm)
      have hid := orient2D_convex_comb3 (S x) (S y) v (S a) (S b) (S f) μ₁ μ₂ μ₃ hsum hf1 hf2
      rw [hxf, hy, orient2D_self_outer, orient2D_self_right, mul_zero, add_zero] at hid
      rw [hxf, hy] at hz ⊢
      nlinarith
    · exfalso; exact hne_xy (hxf.trans hy.symm)
    · have hz := hccw a (by simp) (by rw [hxf]; exact haf) (by rw [hy]; exact hab)
      have hid := orient2D_convex_comb3 (S x) (S y) v (S a) (S b) (S f) μ₁ μ₂ μ₃ hsum hf1 hf2
      rw [hxf, hy, orient2D_self_outer, orient2D_self_right, mul_zero, add_zero] at hid
      rw [hxf, hy] at hz ⊢
      nlinarith
  · rcases hmem_x with hx | hx | hx
    · have hz := hccw b (by simp) (by rw [hx]; exact hab.symm) (by rw [hyf]; exact hbf)
      have hid := orient2D_convex_comb3 (S x) (S y) v (S a) (S b) (S f) μ₁ μ₂ μ₃ hsum hf1 hf2
      rw [hx, hyf, orient2D_self_right, orient2D_self_outer, mul_zero, add_zero] at hid
      rw [hx, hyf] at hz ⊢
      nlinarith
    · exfalso; exact hne_xy (hx.trans hyf.symm)
    · have hz := hccw a (by simp) (by rw [hx]; exact hab) (by rw [hyf]; exact haf)
      have hid := orient2D_convex_comb3 (S x) (S y) v (S a) (S b) (S f) μ₁ μ₂ μ₃ hsum hf1 hf2
      rw [hx, hyf, orient2D_self_right, orient2D_self_outer, mul_zero, add_zero] at hid
      rw [hx, hyf] at hz ⊢
      nlinarith

/-- Lemma 6.1 (`no-odd-front`, `upper_9.tex` lines 601–607):
    If `C ⊆ D` has `|C| ≥ 3`, and `w_wit = w T_wit` misses `o ∈ C` and sees both neighbors
    of `o` in `C`, then `o` is not a front vertex of `C` from `w_wit`. -/
theorem no_odd_front {n : ℕ} {P : Set (ℝ × ℝ)}
    {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ}
    (hPoly : ShatteredSimplePolygon P S w) (h25 : Sec2To5Interface P S w)
    {C : Finset (Fin n)} (hCD : C ⊆ hullVertices S \ certifiedVertices S w)
    (hC3 : 3 ≤ C.card) {T_wit : Finset (Fin n)} {o : Fin n}
    (hoC : o ∈ C) (ho_miss : o ∉ T_wit)
    (ho_nbrs : ∀ x ∈ C, (IsCCWEdge S C x o ∨ IsCCWEdge S C o x) → x ∈ T_wit) :
    ¬ IsFrontVertexOf S C o (w T_wit) := by
  intro hfront
  have hCB : C ⊆ hullVertices S := hCD.trans Finset.sdiff_subset
  have hC_conv : IsConvexPos S C := hullVertices_convexPos S hCB
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hC3
  have hk' : C.card = k + 3 := by omega
  obtain ⟨cyc⟩ := exists_ccwCycle S C
    (fun a _ b _ hab => hPoly.s_inj hab)
    (fun a _ b _ c _ hab hbc hac => hPoly.no_three_collinear (S a) (S b) (S c)
      (Or.inl (Set.mem_range_self a)) (Or.inl (Set.mem_range_self b)) (Or.inl (Set.mem_range_self c))
      (hPoly.s_inj.ne hab) (hPoly.s_inj.ne hbc) (hPoly.s_inj.ne hac))
    hC_conv hk'
  obtain ⟨io, hio⟩ := ccwCycle_exists_index cyc hoC
  rw [← hio] at hoC ho_miss ho_nbrs hfront
  let o_prev := cyc.toFun (io - 1)
  let o_next := cyc.toFun (io + 1)
  have e_prev : IsCCWEdge S C o_prev (cyc.toFun io) := by
    have := ccwCycle_isCCWEdge cyc (io - 1)
    rwa [sub_add_cancel] at this
  have e_next : IsCCWEdge S C (cyc.toFun io) o_next := ccwCycle_isCCWEdge cyc io
  have hp_in : o_prev ∈ T_wit := ho_nbrs o_prev (ccwCycle_mem cyc (io - 1)) (Or.inl e_prev)
  have hn_in : o_next ∈ T_wit := ho_nbrs o_next (ccwCycle_mem cyc (io + 1)) (Or.inr e_next)
  have ho_in_tri : InIntTri (w T_wit) (S o_prev) (S o_next) (S (cyc.toFun io)) :=
    (h25.hidden_front C T_wit (cyc.toFun io) o_prev o_next hCB hC3 hoC e_prev e_next
      hp_in hn_in ho_miss hfront).1
  let B := hullVertices S
  let Tz := Finset.univ.erase (cyc.toFun io)
  have hoB : cyc.toFun io ∈ B := hCB hoC
  have hne_prev : o_prev ≠ cyc.toFun io := e_prev.2.2.1
  have hne_next : o_next ≠ cyc.toFun io := e_next.2.2.1.symm
  have hprev_Tz : o_prev ∈ Tz := Finset.mem_erase.mpr ⟨hne_prev, Finset.mem_univ _⟩
  have hnext_Tz : o_next ∈ Tz := Finset.mem_erase.mpr ⟨hne_next, Finset.mem_univ _⟩
  have h_prev_ne_next : o_prev ≠ o_next := by
    intro heq
    have h2_ne_0 : (2 : Fin (k + 3)) ≠ 0 := by
      intro h; have := congrArg Fin.val h; simp [Nat.mod_eq_of_lt (by omega : 2 < k + 3)] at this
    have h1 : io - 1 = io + 1 := cyc.inj heq
    have h2 := congrArg (· + (1 : Fin (k + 3))) h1
    rw [sub_add_cancel, add_assoc] at h2
    nth_rw 1 [← add_zero io] at h2
    exact h2_ne_0 (add_left_cancel h2).symm
  have hcone : InIntTri (w Tz) (S o_prev) (S o_next) (S (cyc.toFun io)) := by
    by_cases hTT : T_wit = Tz
    · rwa [← hTT]
    · apply h25.cone_lemma (S (cyc.toFun io)) (S o_prev) (S o_next) (w T_wit) (w Tz)
        (hPoly.s_in_P _) (hPoly.s_in_P _) (hPoly.s_in_P _) (hPoly.w_in_P _) (hPoly.w_in_P _)
      · exact (hPoly.shatters T_wit o_prev).mpr hp_in
      · exact (hPoly.shatters T_wit o_next).mpr hn_in
      · intro hs; exact ho_miss ((hPoly.shatters T_wit _).mp hs)
      · exact ho_in_tri
      · exact (hPoly.shatters Tz o_prev).mpr hprev_Tz
      · exact (hPoly.shatters Tz o_next).mpr hnext_Tz
      · apply hPoly.no_three_collinear _ _ _
          (Or.inl (Set.mem_range_self _)) (Or.inl (Set.mem_range_self _)) (Or.inr (Set.mem_range_self _))
        · exact hPoly.s_inj.ne hne_prev.symm
        · exact hPoly.s_ne_w _ _
        · exact hPoly.s_ne_w _ _
      · apply hPoly.no_three_collinear _ _ _
          (Or.inl (Set.mem_range_self _)) (Or.inl (Set.mem_range_self _)) (Or.inr (Set.mem_range_self _))
        · exact hPoly.s_inj.ne hne_next.symm
        · exact hPoly.s_ne_w _ _
        · exact hPoly.s_ne_w _ _
      · apply hPoly.no_three_collinear _ _ _
          (Or.inr (Set.mem_range_self _)) (Or.inl (Set.mem_range_self _)) (Or.inr (Set.mem_range_self _))
        · exact (hPoly.s_ne_w _ _).symm
        · exact hPoly.s_ne_w _ _
        · exact hPoly.w_inj.ne hTT
  let C3 : Finset (Fin n) := {o_prev, cyc.toFun io, o_next}
  have hC3_sub : C3 ⊆ B := by
    intro x hx
    simp only [C3, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact hCB (ccwCycle_mem cyc (io - 1))
    · exact hoB
    · exact hCB (ccwCycle_mem cyc (io + 1))
  have hC3_card : 3 ≤ C3.card := by
    have h1 : o_prev ∉ ({cyc.toFun io, o_next} : Finset (Fin n)) := by
      simp [hne_prev, h_prev_ne_next]
    have h2 : cyc.toFun io ∉ ({o_next} : Finset (Fin n)) := by
      simp [hne_next.symm]
    rw [Finset.card_insert_of_notMem h1, Finset.card_insert_of_notMem h2, Finset.card_singleton]
  have hfront_C3 : IsFrontVertexOf S C3 (cyc.toFun io) (w Tz) :=
    inIntTri_implies_isFrontVertexOf_tri S hne_prev hne_next h_prev_ne_next (w Tz) hcone
  have hfront_B : IsFrontVertexOf S B (cyc.toFun io) (w Tz) :=
    h25.front_restoration C3 B (cyc.toFun io) (w Tz) hC3_sub (hullVertices_convexPos S Subset.rfl)
      hC3_card (Set.mem_range_self Tz) hfront_C3
  have hcert : cyc.toFun io ∈ certifiedVertices S w := by
    refine Finset.mem_filter.mpr ⟨hoB, Tz, Finset.notMem_erase _ _, ?_, ?_, hfront_B⟩
    · intro b hb; exact Finset.mem_erase.mpr ⟨hb.2.2.1, Finset.mem_univ _⟩
    · intro c hc; exact Finset.mem_erase.mpr ⟨hc.2.2.1.symm, Finset.mem_univ _⟩
  exact (Finset.mem_sdiff.mp (hCD hoC)).2 hcert

/-! ## Part 5b: Convex Hull Extremality, Crossing Sectors, and Contiguous Far Chain -/

lemma convexHull_erase_subset_of_mem {α : Type*} [DecidableEq α] (f : α → ℝ × ℝ)
    {R : Finset α} {j : α}
    (hj_conv : f j ∈ convexHull ℝ ((R.erase j).image f : Set (ℝ × ℝ))) :
    convexHull ℝ (R.image f : Set (ℝ × ℝ)) ⊆ convexHull ℝ ((R.erase j).image f : Set (ℝ × ℝ)) := by
  apply convexHull_min _ (convex_convexHull ℝ _)
  intro x hx
  rcases Finset.mem_image.mp hx with ⟨r, hr, rfl⟩
  by_cases hrj : r = j
  · subst hrj; exact hj_conv
  · exact subset_convexHull ℝ _ (Finset.mem_image.mpr ⟨r, Finset.mem_erase.mpr ⟨hrj, hr⟩, rfl⟩)

lemma mem_convexHull_hullVertices_aux {n : ℕ} (S : Fin n → ℝ × ℝ) (hinj : Function.Injective S) :
    ∀ (m : ℕ) (R : Finset (Fin n)), R.card = m →
      (∀ i : Fin n, S i ∈ convexHull ℝ (R.image S : Set (ℝ × ℝ))) →
      ∀ i : Fin n, S i ∈ convexHull ℝ ((hullVertices S).image S : Set (ℝ × ℝ)) := by
  intro m
  induction m with
  | zero =>
    intro R hR hcov i
    rw [Finset.card_eq_zero] at hR
    subst hR
    have := hcov i
    simp at this
  | succ m ih =>
    intro R hR hcov i
    by_cases hsub : R ⊆ hullVertices S
    · exact convexHull_mono (Finset.image_subset_image hsub) (hcov i)
    · obtain ⟨j, hjR, hjB⟩ := Finset.not_subset.mp hsub
      have hj_univ : S j ∈ convexHull ℝ (((Finset.univ.erase j).image S) : Set (ℝ × ℝ)) := by
        by_contra hnot
        exact hjB (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hnot⟩)
      rw [mem_convexHull_iff_exists_fintype] at hj_univ
      rcases hj_univ with ⟨ι, _, w_j, p_j, hw_nn, hw_sum, hp_mem, hp_eq⟩
      have h_each : ∀ k : ι, ∃ x : Fin n, x ≠ j ∧ p_j k = S x ∧
          ∃ (μ : Fin n → ℝ), (∀ r ∈ R, 0 ≤ μ r) ∧ (∑ r ∈ R, μ r = 1) ∧
            S x = ∑ r ∈ R, μ r • S r := by
        intro k
        rcases Finset.mem_image.mp (hp_mem k) with ⟨x, hx, hpx⟩
        have hxj : x ≠ j := (Finset.mem_erase.mp hx).1
        have hsx : S x ∈ convexHull ℝ (R.image S : Set (ℝ × ℝ)) := hcov x
        rw [Finset.convexHull_eq] at hsx
        rcases hsx with ⟨μ, hμ_nn, hμ_sum, hμ_eq⟩
        refine ⟨x, hxj, hpx.symm, fun r => μ (S r), fun r hr => hμ_nn (S r) (Finset.mem_image_of_mem S hr), ?_, ?_⟩
        · change ∑ r ∈ R, (fun y => μ y) (S r) = 1
          rw [← Finset.sum_image (f := fun r => μ r) (g := S) (fun a _ b _ h => hinj h)]
          exact hμ_sum
        · rw [Finset.centerMass, hμ_sum, inv_one, one_smul] at hμ_eq
          rw [← hμ_eq]
          change ∑ y ∈ R.image S, (fun y => μ y • y) y = ∑ r ∈ R, (fun y => μ y • y) (S r)
          exact Finset.sum_image (f := fun y => μ y • y) (g := S) (fun a _ b _ h => hinj h)
      choose xk hxk_ne hpk μk hμk_nn hμk_sum hμk_eq using h_each
      let c : ℝ := ∑ k : ι, w_j k * μk k j
      have hc_lt_one : c < 1 := by
        have hle : ∀ k : ι, w_j k * μk k j ≤ w_j k := by
          intro k
          have hμ_le1 : μk k j ≤ 1 := by
            have := Finset.single_le_sum (fun r hr => hμk_nn k r hr) hjR
            linarith [hμk_sum k]
          exact mul_le_of_le_one_right (hw_nn k) hμ_le1
        have hex : ∃ k₀ : ι, 0 < w_j k₀ := by
          by_contra h0
          push Not at h0
          have : ∑ k : ι, w_j k ≤ 0 := Finset.sum_nonpos (fun k _ => h0 k)
          linarith
        rcases hex with ⟨k₀, hk₀⟩
        have hμ_lt1 : μk k₀ j < 1 := by
          by_contra hge
          replace hge : 1 ≤ μk k₀ j := not_lt.mp hge
          have hμ_le1 : μk k₀ j ≤ 1 := by
            have := Finset.single_le_sum (fun r hr => hμk_nn k₀ r hr) hjR
            linarith [hμk_sum k₀]
          have hμ1 : μk k₀ j = 1 := le_antisymm hμ_le1 hge
          have hrest : ∀ r ∈ R, r ≠ j → μk k₀ r = 0 := by
            intro r hr hrj
            have hsum_er : ∑ r' ∈ R.erase j, μk k₀ r' = 0 := by
              have hsp := Finset.add_sum_erase R (fun r' => μk k₀ r') hjR
              linarith [hμk_sum k₀]
            exact (Finset.sum_eq_zero_iff_of_nonneg (fun r' hr' =>
              hμk_nn k₀ r' (Finset.mem_of_mem_erase hr'))).mp hsum_er r (Finset.mem_erase.mpr ⟨hrj, hr⟩)
          have hSx : S (xk k₀) = S j := by
            rw [hμk_eq k₀]
            have hsp := Finset.add_sum_erase R (fun r => μk k₀ r • S r) hjR
            have hsum0 : ∑ r ∈ R.erase j, μk k₀ r • S r = 0 :=
              Finset.sum_eq_zero (fun r hr => by
                rw [hrest r (Finset.mem_of_mem_erase hr) (Finset.mem_erase.mp hr).1, zero_smul])
            rw [← hsp, hsum0, add_zero, hμ1, one_smul]
          exact hxk_ne k₀ (hinj hSx)
        have hk₀_lt : w_j k₀ * μk k₀ j < w_j k₀ := mul_lt_of_lt_one_right hk₀ hμ_lt1
        have hsum_lt := Finset.sum_lt_sum (fun k _ => hle k) ⟨k₀, Finset.mem_univ k₀, hk₀_lt⟩
        linarith
      have h1c_pos : 0 < 1 - c := sub_pos.mpr hc_lt_one
      let ν : Fin n → ℝ := fun r => (∑ k : ι, w_j k * μk k r) / (1 - c)
      have hj_er : S j ∈ convexHull ℝ (((R.erase j).image S) : Set (ℝ × ℝ)) := by
        rw [mem_convexHull_iff_exists_fintype]
        refine ⟨{r : Fin n // r ∈ R.erase j}, inferInstance, fun r => ν r.1, fun r => S r.1, ?_, ?_, ?_, ?_⟩
        · intro r
          exact div_nonneg (Finset.sum_nonneg fun k _ =>
            mul_nonneg (hw_nn k) (hμk_nn k r.1 (Finset.mem_of_mem_erase r.2))) (le_of_lt h1c_pos)
        · have hsum_all : ∑ r ∈ R, (∑ k : ι, w_j k * μk k r) = 1 := by
            rw [Finset.sum_comm]
            trans ∑ k : ι, w_j k * (∑ r ∈ R, μk k r)
            · refine Finset.sum_congr rfl (fun k _ => (Finset.mul_sum R (fun r => μk k r) (w_j k)).symm)
            · simp_rw [hμk_sum, mul_one, hw_sum]
          have hsp := Finset.add_sum_erase R (fun r => ∑ k : ι, w_j k * μk k r) hjR
          have hc_eq : ∑ k : ι, w_j k * μk k j = c := rfl
          rw [hc_eq] at hsp
          have hsum_er : ∑ r ∈ R.erase j, (∑ k : ι, w_j k * μk k r) = 1 - c := by linarith
          rw [Finset.sum_coe_sort (R.erase j) (fun r => ν r)]
          dsimp [ν]
          rw [← Finset.sum_div, hsum_er, div_self (ne_of_gt h1c_pos)]
        · intro r
          exact Finset.mem_coe.mpr (Finset.mem_image_of_mem S r.2)
        · have hsum_vec : S j = ∑ r ∈ R, (∑ k : ι, w_j k * μk k r) • S r := by
            rw [← hp_eq]
            have h1 : ∑ k : ι, w_j k • p_j k = ∑ k : ι, w_j k • ∑ r ∈ R, μk k r • S r :=
              Finset.sum_congr rfl (fun k _ => by rw [hpk k, hμk_eq k])
            rw [h1]
            simp_rw [Finset.smul_sum, smul_smul]
            rw [Finset.sum_comm]
            exact Finset.sum_congr rfl (fun r _ =>
              (Finset.sum_smul (s := Finset.univ) (f := fun k => w_j k * μk k r) (x := S r)).symm)
          have hsp := Finset.add_sum_erase R (fun r => (∑ k : ι, w_j k * μk k r) • S r) hjR
          have hc_eq : ∑ k : ι, w_j k * μk k j = c := rfl
          rw [hc_eq] at hsp
          have hdiff : (1 - c) • S j = ∑ r ∈ R.erase j, (∑ k : ι, w_j k * μk k r) • S r := by
            rw [sub_smul, one_smul]
            calc S j - c • S j = (c • S j + ∑ r ∈ R.erase j, (∑ k : ι, w_j k * μk k r) • S r) - c • S j := by
                  rw [hsp, ← hsum_vec]
              _ = ∑ r ∈ R.erase j, (∑ k : ι, w_j k * μk k r) • S r := add_sub_cancel_left _ _
          rw [Finset.sum_coe_sort (R.erase j) (fun r => ν r • S r)]
          dsimp [ν]
          simp_rw [div_eq_inv_mul, ← smul_smul, ← Finset.smul_sum]
          rw [← hdiff, smul_smul, inv_mul_cancel₀ (ne_of_gt h1c_pos), one_smul]
      have hcard_er : (R.erase j).card = m := by
        rw [Finset.card_erase_of_mem hjR, hR]; omega
      refine ih (R.erase j) hcard_er ?_ i
      intro x
      exact convexHull_erase_subset_of_mem S hj_er (hcov x)

lemma mem_convexHull_hullVertices {n : ℕ} (S : Fin n → ℝ × ℝ) (hinj : Function.Injective S)
    (i : Fin n) : S i ∈ convexHull ℝ ((hullVertices S).image S : Set (ℝ × ℝ)) := by
  refine mem_convexHull_hullVertices_aux S hinj Finset.univ.card Finset.univ rfl (fun x => ?_) i
  exact subset_convexHull ℝ _ (Finset.mem_image_of_mem S (Finset.mem_univ x))

lemma three_le_hullVertices_card {n : ℕ} (S : Fin n → ℝ × ℝ)
    (hinj : Function.Injective S)
    (hnoncol : ∀ a b c : Fin n, a ≠ b → b ≠ c → a ≠ c → orient2D (S a) (S b) (S c) ≠ 0)
    (hn : 3 ≤ n) : 3 ≤ (hullVertices S).card := by
  haveI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  let B := hullVertices S
  have hcov : ∀ i : Fin n, S i ∈ convexHull ℝ (B.image S : Set (ℝ × ℝ)) :=
    mem_convexHull_hullVertices S hinj
  by_contra hlt
  have hle : B.card ≤ 2 := by change (hullVertices S).card ≤ 2; omega
  have h2 : ∃ b1 b2 : Fin n, B ⊆ {b1, b2} := by
    rcases Nat.le_succ_iff.mp hle with hle1 | hcard2
    · rcases Finset.card_le_one_iff_subset_singleton.mp hle1 with ⟨b1, hb1⟩
      exact ⟨b1, b1, hb1.trans (fun x hx => by simp at hx ⊢; exact hx)⟩
    · obtain ⟨b1, b2, _, hb_eq⟩ := Finset.card_eq_two.mp hcard2
      exact ⟨b1, b2, hb_eq ▸ Subset.rfl⟩
  rcases h2 with ⟨b1, b2, hb_sub⟩
  have hin_seg : ∀ i : Fin n, ∃ t : ℝ,
      (S i).1 = (1 - t) * (S b1).1 + t * (S b2).1 ∧
      (S i).2 = (1 - t) * (S b1).2 + t * (S b2).2 := by
    intro i
    have hi_mem : S i ∈ convexHull ℝ (({S b1, S b2} : Finset (ℝ × ℝ)) : Set (ℝ × ℝ)) := by
      refine convexHull_mono ?_ (hcov i)
      intro x hx
      rcases Finset.mem_image.mp hx with ⟨r, hr, rfl⟩
      have hr12 := hb_sub hr
      simp only [Finset.mem_insert, Finset.mem_singleton] at hr12
      rcases hr12 with rfl | rfl <;> simp
    rw [Finset.convexHull_eq] at hi_mem
    rcases hi_mem with ⟨μ, _, hμ_sum, hμ_eq⟩
    by_cases h12 : S b1 = S b2
    · have hs1 : ({S b1, S b2} : Finset (ℝ × ℝ)) = {S b1} := by ext x; simp [h12]
      rw [hs1] at hμ_sum hμ_eq
      rw [Finset.centerMass, hμ_sum, inv_one, one_smul, Finset.sum_singleton] at hμ_eq
      rw [Finset.sum_singleton] at hμ_sum
      refine ⟨0, ?_, ?_⟩
      · rw [← hμ_eq, hμ_sum]; simp
      · rw [← hμ_eq, hμ_sum]; simp
    · rw [Finset.sum_pair h12] at hμ_sum
      rw [Finset.centerMass, show ∑ y ∈ {S b1, S b2}, μ y = 1 by rw [Finset.sum_pair h12]; exact hμ_sum,
        inv_one, one_smul, Finset.sum_pair h12] at hμ_eq
      refine ⟨μ (S b2), ?_, ?_⟩
      · have h1 := congrArg Prod.fst hμ_eq
        dsimp at h1
        rw [show 1 - μ (S b2) = μ (S b1) by linarith]; linarith
      · have h2 := congrArg Prod.snd hμ_eq
        dsimp at h2
        rw [show 1 - μ (S b2) = μ (S b1) by linarith]; linarith
  obtain ⟨t0, ht01, ht02⟩ := hin_seg ⟨0, by omega⟩
  obtain ⟨t1, ht11, ht12⟩ := hin_seg ⟨1, by omega⟩
  obtain ⟨t2, ht21, ht22⟩ := hin_seg ⟨2, by omega⟩
  have hzero : orient2D (S ⟨0, by omega⟩) (S ⟨1, by omega⟩) (S ⟨2, by omega⟩) = 0 := by
    unfold orient2D; rw [ht01, ht02, ht11, ht12, ht21, ht22]; ring
  exact hnoncol ⟨0, by omega⟩ ⟨1, by omega⟩ ⟨2, by omega⟩
    (by intro h; have := congrArg Fin.val h; simp at this)
    (by intro h; have := congrArg Fin.val h; simp at this)
    (by intro h; have := congrArg Fin.val h; simp at this) hzero

/-- From `ap_leaves/leaf71_universal_crossing_back_vertex.proved.lean` (`orient2D` version). -/
lemma crossing_anchor_implies_back_vertex
    (p_prev p p_next ap cp v : ℝ × ℝ)
    (hcorner : 0 < orient2D p_prev p p_next)
    (hap1 : 0 ≤ orient2D p_prev p ap) (hap2 : 0 ≤ orient2D p p_next ap)
    (hcp1 : 0 ≤ orient2D p_prev p cp) (hcp2 : 0 ≤ orient2D p p_next cp)
    (hpac : 0 < orient2D p ap cp)
    (hva : 0 < orient2D p ap v)
    (hvc : orient2D p cp v < 0) :
    0 < orient2D p_prev p v ∧ 0 < orient2D p p_next v := by
  push_cast [orient2D, lt_iff_le_and_ne] at *
  have : 0 < (ap.1 - p.1) * (cp.2 - p.2) - (ap.2 - p.2) * (cp.1 - p.1) :=
    Ne.lt_of_le (by bound) (by bound)
  have' := hcorner.1.lt_of_ne hcorner.2
  repeat' constructor
  · cases em ((ap.1 - p.1) * (v.1 - p.1) - (ap.2 - p.2) * (v.2 - p.2) > 0) with nlinarith
  · cases hap1.eq_or_lt with nlinarith [hva.1.lt_of_ne hva.2, hvc.1.lt_of_ne hvc.2]
  · cases em ((ap.1 - p.1) * (v.1 - p.1) - (ap.2 - p.2) * (v.2 - p.2) > 0) with
      nlinarith [hva.2.lt_of_le hva.1, hvc.2.lt_of_le hvc.1]
  · use (by cases hcp2.eq_or_lt with nlinarith [hva.2.lt_of_le hva.1, hvc.2.lt_of_le hvc.1])

/-- From `ap_leaves/leaf70_section6_anchor_splitting.proved.lean` (`orient2D` version). -/
lemma anchor_splitting_orient
    (w u v y1 y2 : ℝ × ℝ)
    (hwuv : 0 < orient2D w u v)
    (hy1_uv : 0 < orient2D u v y1) (hy1_vw : 0 < orient2D v w y1) (hy1_wu : 0 < orient2D w u y1)
    (hy2_uv : 0 < orient2D u v y2) (hy2_vw : 0 < orient2D v w y2) (hy2_wu : 0 < orient2D w u y2)
    (hnot_cap : ¬ (0 ≤ orient2D u v y2 ∧ 0 ≤ orient2D v y1 y2 ∧ 0 ≤ orient2D y1 u y2))
    (hne : orient2D w y1 y2 ≠ 0) :
    (0 < orient2D w u y2 ∧ 0 < orient2D u y1 y2 ∧ 0 < orient2D y1 w y2) ∨
    (0 < orient2D w y1 y2 ∧ 0 < orient2D y1 v y2 ∧ 0 < orient2D v w y2) := by
  simp_all [orient2D, le_of_lt]
  exact (lt_or_gt_of_ne (by bound)).imp
    (⟨not_le.1 fun and => by nlinarith [hnot_cap (by nlinarith), .], by nlinarith⟩)
    (⟨., not_le.1 fun and => by nlinarith [hnot_cap (by nlinarith)]⟩)

/-- From `ap_leaves/leaf98_prop_good_targets_combinatorics.proved.lean`. -/
lemma prop_good_targets_counting
    (k j : ℕ)
    (hk : k = 3 ∨ k = 4)
    (hj : j ≤ k) :
    k - 2 ≤ (j - 1) + (k - j - 1) ∧
    ∀ outside : Finset (Fin (2 * k)),
      (∀ x ∈ outside, x.val % 2 = 1) → outside.card ≤ k ∧
      ((∀ x ∈ outside, ∀ y ∈ outside, x ≠ y → (x.val + 1) % (2 * k) ≠ y.val) →
        (outside.card ≥ 2 → ∃ x ∈ outside, ∃ y ∈ outside, (x.val + 1) % (2 * k) = y.val) →
        outside.card ≤ 1) := by
  use (by valid), fun R M =>
    ⟨(R.card_mono (Finset.mem_filter.mpr ⟨Finset.mem_univ _, M · ·⟩)).trans (by bound),
      fun a s => not_lt.mp (s · |>.elim fun and ⟨A, B, S, _⟩ => absurd (a and A B S) ?_)⟩
  exact (. (absurd (M and A) ∘ by match k with | 3 | 4 => omega) (by valid))

/-- Convexity of the crossing sector: any point `z ∈ conv(Gpts)` off the three lines
    `v a`, `v c`, `a c` crosses `a c` from `v`, provided every generator of `Gpts` is
    either `a`, `c`, or inside the closed crossing sector. -/
lemma cap_convex_crossing {v q a c : ℝ × ℝ}
    (hac : AngleLt v q a c)
    (Gpts : Set (ℝ × ℝ))
    (hG : ∀ g ∈ Gpts, g = a ∨ g = c ∨
      (OnSameSide v q a g ∧
        (0 < orient2D v q a → 0 ≤ orient2D v a g ∧ 0 ≤ orient2D v g c ∧ orient2D a c v * orient2D a c g ≤ 0) ∧
        (orient2D v q a < 0 → orient2D v a g ≤ 0 ∧ orient2D v g c ≤ 0 ∧ orient2D a c v * orient2D a c g ≤ 0)))
    {z : ℝ × ℝ} (hz : z ∈ convexHull ℝ Gpts)
    (hz_va : orient2D v a z ≠ 0) (hz_vc : orient2D v c z ≠ 0) (hz_ac : orient2D a c z ≠ 0) :
    SegmentsCross v z a c := by
  rcases hac with ⟨hsac, hoac⟩
  have hG_closed : ∀ g ∈ Gpts,
      (0 < orient2D v q a → 0 < orient2D v q g ∧ 0 ≤ orient2D v a g ∧ 0 ≤ orient2D v g c ∧
        orient2D a c v * orient2D a c g ≤ 0) ∧
      (orient2D v q a < 0 → orient2D v q g < 0 ∧ orient2D v a g ≤ 0 ∧ 0 ≥ orient2D v g c ∧
        orient2D a c v * orient2D a c g ≤ 0) := by
    intro g hg
    rcases hG g hg with rfl | rfl | ⟨hss, hp, hn⟩
    · constructor
      · intro hqa
        refine ⟨hqa, by rw [orient2D_self_right], by nlinarith [hoac], ?_⟩
        rw [orient2D_self_outer, mul_zero]
      · intro hqa
        refine ⟨hqa, by rw [orient2D_self_right], by nlinarith [hoac], ?_⟩
        rw [orient2D_self_outer, mul_zero]
    · constructor
      · intro hqa
        refine ⟨by nlinarith [show 0 < orient2D v q a * orient2D v q g from hsac],
          by nlinarith [hoac], by rw [orient2D_self_right], ?_⟩
        rw [orient2D_self_right, mul_zero]
      · intro hqa
        refine ⟨by nlinarith [show 0 < orient2D v q a * orient2D v q g from hsac],
          by nlinarith [hoac], by rw [orient2D_self_right], ?_⟩
        rw [orient2D_self_right, mul_zero]
    · constructor
      · intro hqa; exact ⟨by nlinarith [show 0 < orient2D v q a * orient2D v q g from hss], (hp hqa).1, (hp hqa).2.1, (hp hqa).2.2⟩
      · intro hqa; exact ⟨by nlinarith [show 0 < orient2D v q a * orient2D v q g from hss], (hn hqa).1, (hn hqa).2.1, (hn hqa).2.2⟩
  rcases lt_trichotomy (orient2D v q a) 0 with hqa | hqa | hqa
  · let K : Set (ℝ × ℝ) := {x | orient2D v q x < 0 ∧ orient2D v a x ≤ 0 ∧
        orient2D v x c ≤ 0 ∧ orient2D a c v * orient2D a c x ≤ 0}
    have hK_conv : Convex ℝ K := by
      intro x hx y hy α β hα hβ hαβ
      have hL : ∀ (p r : ℝ × ℝ),
          orient2D p r (α • x + β • y) = α * orient2D p r x + β * orient2D p r y := by
        intro p r; unfold orient2D; dsimp
        linear_combination (p.2 * r.1 - p.1 * r.2) * hαβ
      have hL2 : orient2D v (α • x + β • y) c = α * orient2D v x c + β * orient2D v y c := by
        have hα' : α = 1 - β := by linarith
        subst hα'; unfold orient2D; dsimp; ring
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [hL]
        rcases eq_or_lt_of_le hα with rfl | hαp
        · have : β = 1 := by linarith
          subst this; simpa using hy.1
        · nlinarith [hx.1, hy.1]
      · rw [hL]; nlinarith [hx.2.1, hy.2.1]
      · rw [hL2]; nlinarith [hx.2.2.1, hy.2.2.1]
      · rw [hL]; nlinarith [hx.2.2.2, hy.2.2.2]
    have hzK : z ∈ K := convexHull_min (fun g hg => (hG_closed g hg).2 hqa) hK_conv hz
    have haz_lt : orient2D v a z < 0 := lt_of_le_of_ne hzK.2.1 hz_va
    have hzc_lt : orient2D v z c < 0 := lt_of_le_of_ne hzK.2.2.1 (by
      intro h; apply hz_vc; unfold orient2D at h ⊢; linarith)
    have hacz_lt : orient2D a c v * orient2D a c z < 0 := by
      refine lt_of_le_of_ne hzK.2.2.2 ?_
      intro h
      rcases mul_eq_zero.mp h with h1 | h2
      · have hacv : orient2D v a c = orient2D a c v := by unfold orient2D; ring
        rw [← hacv] at h1
        rw [h1, mul_zero] at hoac; linarith
      · exact hz_ac h2
    refine ⟨?_, hacz_lt⟩
    have h1 : orient2D v z a = -orient2D v a z := orient2D_swap23 v a z
    rw [h1]; exact mul_neg_of_pos_of_neg (by linarith) hzc_lt
  · rw [hqa, zero_mul] at hoac; linarith
  · let K : Set (ℝ × ℝ) := {x | 0 < orient2D v q x ∧ 0 ≤ orient2D v a x ∧
        0 ≤ orient2D v x c ∧ orient2D a c v * orient2D a c x ≤ 0}
    have hK_conv : Convex ℝ K := by
      intro x hx y hy α β hα hβ hαβ
      have hL : ∀ (p r : ℝ × ℝ),
          orient2D p r (α • x + β • y) = α * orient2D p r x + β * orient2D p r y := by
        intro p r; unfold orient2D; dsimp
        linear_combination (p.2 * r.1 - p.1 * r.2) * hαβ
      have hL2 : orient2D v (α • x + β • y) c = α * orient2D v x c + β * orient2D v y c := by
        have hα' : α = 1 - β := by linarith
        subst hα'; unfold orient2D; dsimp; ring
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [hL]
        rcases eq_or_lt_of_le hα with rfl | hαp
        · have : β = 1 := by linarith
          subst this; simpa using hy.1
        · nlinarith [hx.1, hy.1]
      · rw [hL]; nlinarith [hx.2.1, hy.2.1]
      · rw [hL2]; nlinarith [hx.2.2.1, hy.2.2.1]
      · rw [hL]; nlinarith [hx.2.2.2, hy.2.2.2]
    have hzK : z ∈ K := convexHull_min (fun g hg => (hG_closed g hg).1 hqa) hK_conv hz
    have haz_gt : 0 < orient2D v a z := lt_of_le_of_ne hzK.2.1 (Ne.symm hz_va)
    have hzc_gt : 0 < orient2D v z c := lt_of_le_of_ne hzK.2.2.1 (fun h => by
      apply hz_vc; unfold orient2D at h ⊢; linarith)
    have hacz_lt : orient2D a c v * orient2D a c z < 0 := by
      refine lt_of_le_of_ne hzK.2.2.2 ?_
      intro h
      rcases mul_eq_zero.mp h with h1 | h2
      · have hacv : orient2D v a c = orient2D a c v := by unfold orient2D; ring
        rw [← hacv] at h1
        rw [h1, mul_zero] at hoac; linarith
      · exact hz_ac h2
    refine ⟨?_, hacz_lt⟩
    have h1 : orient2D v z a = -orient2D v a z := orient2D_swap23 v a z
    rw [h1]; exact mul_neg_of_neg_of_pos (by linarith) hzc_gt

/-! ## Part 5c: Contiguous Facing Edges (`facing_edges_contiguous`), Far Chain & Two-Path Side Separation -/

/-- Edge vector `c (i + 1) - c i` around a convex polygon. -/
def edgeVec {k : ℕ} (c : Fin (k + 3) → ℝ × ℝ) (i : Fin (k + 3)) : ℝ × ℝ :=
  ((c (i + 1)).1 - (c i).1, (c (i + 1)).2 - (c i).2)

/-- 2D cross product `u.1 * w.2 - u.2 * w.1`. -/
def det2 (u w : ℝ × ℝ) : ℝ := u.1 * w.2 - u.2 * w.1

lemma det2_edgeVec_succ {k : ℕ} (c : Fin (k + 3) → ℝ × ℝ) (m : Fin (k + 3)) :
    det2 (edgeVec c m) (edgeVec c (m + 1)) = orient2D (c m) (c (m + 1)) (c (m + 2)) := by
  have h2 : m + 1 + 1 = m + 2 := by abel
  unfold det2 edgeVec orient2D
  rw [h2]; ring

lemma det2_edgeVec_step {k : ℕ} (c : Fin (k + 3) → ℝ × ℝ) (a m : Fin (k + 3)) :
    det2 (edgeVec c a) (edgeVec c (m + 1)) * orient2D (c m) (c (m + 1)) (c a) =
      det2 (edgeVec c a) (edgeVec c m) * orient2D (c (m + 1)) (c (m + 2)) (c a) -
      det2 (edgeVec c m) (edgeVec c (m + 1)) * orient2D (c a) (c (a + 1)) (c (m + 1)) := by
  have h2 : m + 1 + 1 = m + 2 := by abel
  unfold det2 edgeVec orient2D
  rw [h2]; ring

lemma strictConvexCCW_orient_nonneg {k : ℕ} (c : Fin (k + 3) → ℝ × ℝ)
    (hc : StrictConvexCCWPoly c) (i j : Fin (k + 3)) :
    0 ≤ orient2D (c i) (c (i + 1)) (c j) := by
  by_cases h1 : j = i
  · subst h1; rw [orient2D_self_outer]
  · by_cases h2 : j = i + 1
    · subst h2; rw [orient2D_self_right]
    · exact le_of_lt (hc i j h1 h2)

lemma det2_edgeVec_unimodal {k : ℕ} (c : Fin (k + 3) → ℝ × ℝ)
    (hc : StrictConvexCCWPoly c) (a m : Fin (k + 3))
    (hma : m ≠ a) (hm1a : m + 1 ≠ a)
    (hle : det2 (edgeVec c a) (edgeVec c m) ≤ 0) :
    det2 (edgeVec c a) (edgeVec c (m + 1)) < 0 := by
  have hid := det2_edgeVec_step c a m
  have h_mca : 0 < orient2D (c m) (c (m + 1)) (c a) := hc m a hma.symm hm1a.symm
  have h_m1ca : 0 ≤ orient2D (c (m + 1)) (c (m + 2)) (c a) := by
    rw [show m + 2 = m + 1 + 1 by abel]
    exact strictConvexCCW_orient_nonneg c hc (m + 1) a
  have h_succ : 0 < det2 (edgeVec c m) (edgeVec c (m + 1)) := by
    rw [det2_edgeVec_succ]
    have hne1 : m + 2 ≠ m := by
      intro h
      have h20 : (2 : Fin (k + 3)) = 0 := by
        apply add_left_cancel (a := m); simpa using h
      have hv := congrArg Fin.val h20
      simp [Nat.mod_eq_of_lt (by omega : 2 < k + 3)] at hv
    have hne2 : m + 2 ≠ m + 1 := by
      intro h
      have h21 : m + 1 + (1 : Fin (k + 3)) = m + 1 + 0 := by
        calc m + 1 + 1 = m + 2 := by abel
          _ = m + 1 := h
          _ = m + 1 + 0 := by abel
      have h10 : (1 : Fin (k + 3)) = 0 := add_left_cancel h21
      have hv := congrArg Fin.val h10
      simp [Nat.mod_eq_of_lt (by omega : 1 < k + 3)] at hv
    have hm12 : m + 1 + 1 = m + 2 := by abel
    rw [← hm12] at hne1 hne2 ⊢
    exact hc m (m + 1 + 1) hne1 hne2
  have h_am1 : 0 < orient2D (c a) (c (a + 1)) (c (m + 1)) := by
    refine hc a (m + 1) hm1a ?_
    intro h; exact hma (add_right_cancel h)
  have ht1 : det2 (edgeVec c a) (edgeVec c m) * orient2D (c (m + 1)) (c (m + 2)) (c a) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg hle h_m1ca
  have ht2 : 0 < det2 (edgeVec c m) (edgeVec c (m + 1)) * orient2D (c a) (c (a + 1)) (c (m + 1)) :=
    mul_pos h_succ h_am1
  have hlhs : det2 (edgeVec c a) (edgeVec c (m + 1)) * orient2D (c m) (c (m + 1)) (c a) < 0 := by
    linarith
  by_contra hge
  replace hge : 0 ≤ det2 (edgeVec c a) (edgeVec c (m + 1)) := not_lt.mp hge
  have : 0 ≤ det2 (edgeVec c a) (edgeVec c (m + 1)) * orient2D (c m) (c (m + 1)) (c a) :=
    mul_nonneg hge (le_of_lt h_mca)
  linarith

lemma orient_edge_sandwich {k : ℕ} (c : Fin (k + 3) → ℝ × ℝ) (hc : StrictConvexCCWPoly c)
    (v : ℝ × ℝ) (a m b : Fin (k + 3))
    (hab : 0 < det2 (edgeVec c a) (edgeVec c b))
    (ham : 0 < det2 (edgeVec c a) (edgeVec c m))
    (hmb : 0 < det2 (edgeVec c m) (edgeVec c b))
    (hva : orient2D (c a) (c (a + 1)) v < 0)
    (hvb : orient2D (c b) (c (b + 1)) v < 0) :
    orient2D (c m) (c (m + 1)) v < 0 := by
  have hid : det2 (edgeVec c a) (edgeVec c b) * orient2D (c m) (c (m + 1)) v =
      det2 (edgeVec c m) (edgeVec c b) *
        (orient2D (c a) (c (a + 1)) v - orient2D (c a) (c (a + 1)) (c m)) +
      det2 (edgeVec c a) (edgeVec c m) *
        (orient2D (c b) (c (b + 1)) v - orient2D (c b) (c (b + 1)) (c m)) := by
    unfold det2 edgeVec orient2D; ring
  have h1 := strictConvexCCW_orient_nonneg c hc a m
  have h2 := strictConvexCCW_orient_nonneg c hc b m
  have ht1 : det2 (edgeVec c m) (edgeVec c b) *
      (orient2D (c a) (c (a + 1)) v - orient2D (c a) (c (a + 1)) (c m)) < 0 :=
    mul_neg_of_pos_of_neg hmb (by linarith)
  have ht2 : det2 (edgeVec c a) (edgeVec c m) *
      (orient2D (c b) (c (b + 1)) v - orient2D (c b) (c (b + 1)) (c m)) < 0 :=
    mul_neg_of_pos_of_neg ham (by linarith)
  have hlhs : det2 (edgeVec c a) (edgeVec c b) * orient2D (c m) (c (m + 1)) v < 0 := by linarith
  by_contra hge
  replace hge : 0 ≤ orient2D (c m) (c (m + 1)) v := not_lt.mp hge
  have : 0 ≤ det2 (edgeVec c a) (edgeVec c b) * orient2D (c m) (c (m + 1)) v :=
    mul_nonneg (le_of_lt hab) hge
  linarith

lemma facing_edges_det_ne_zero {k : ℕ} (c : Fin (k + 3) → ℝ × ℝ) (hc : StrictConvexCCWPoly c)
    (v : ℝ × ℝ) (a b : Fin (k + 3)) (hab : a ≠ b)
    (hva : orient2D (c a) (c (a + 1)) v < 0)
    (hvb : orient2D (c b) (c (b + 1)) v < 0) :
    det2 (edgeVec c a) (edgeVec c b) ≠ 0 := by
  intro hdet
  let u := edgeVec c a
  let w := edgeVec c b
  let s : ℝ := u.1 * w.1 + u.2 * w.2
  have hu_sq : u.1 ^ 2 + u.2 ^ 2 > 0 := by
    have hne : u.1 ≠ 0 ∨ u.2 ≠ 0 := by
      by_contra hc0
      push Not at hc0
      have ha1_ne : a + 1 ≠ a := by
        intro h; nth_rw 2 [← add_zero a] at h
        have h10 : (1 : Fin (k + 3)) = 0 := add_left_cancel h
        have hv := congrArg Fin.val h10
        simp [Nat.mod_eq_of_lt (by omega : 1 < k + 3)] at hv
      have : orient2D (c a) (c (a + 1)) v = 0 := by
        unfold orient2D; dsimp [u, edgeVec] at hc0; rw [hc0.1, hc0.2]; ring
      linarith
    rcases hne with h1 | h2
    · exact add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero h1) (sq_nonneg _)
    · exact add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_ne_zero h2)
  have hw_sq : w.1 ^ 2 + w.2 ^ 2 > 0 := by
    have hne : w.1 ≠ 0 ∨ w.2 ≠ 0 := by
      by_contra hc0
      push Not at hc0
      have : orient2D (c b) (c (b + 1)) v = 0 := by
        unfold orient2D; dsimp [w, edgeVec] at hc0; rw [hc0.1, hc0.2]; ring
      linarith
    rcases hne with h1 | h2
    · exact add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero h1) (sq_nonneg _)
    · exact add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_ne_zero h2)
  have hs_ne : s ≠ 0 := by
    have hid : s ^ 2 + (det2 u w) ^ 2 = (u.1 ^ 2 + u.2 ^ 2) * (w.1 ^ 2 + w.2 ^ 2) := by
      dsimp [s, det2]; ring
    have hdet' : det2 u w = 0 := hdet
    rw [hdet'] at hid
    intro hs0
    rw [hs0] at hid
    nlinarith [mul_pos hu_sq hw_sq]
  have hdet' : det2 u w = 0 := hdet
  have hdet_coord : u.1 * w.2 - u.2 * w.1 = 0 := hdet'
  have hid_ca : (u.1 ^ 2 + u.2 ^ 2) * orient2D (c b) (c (b + 1)) (c a) =
      -s * orient2D (c a) (c (a + 1)) (c b) := by
    dsimp [s, u, w, edgeVec] at hdet_coord ⊢; unfold orient2D
    linear_combination (-((c (a + 1)).2 - (c a).2) * ((c a).2 - (c b).2) -
      ((c (a + 1)).1 - (c a).1) * ((c a).1 - (c b).1)) * hdet_coord
  have hid_v : (u.1 ^ 2 + u.2 ^ 2) * orient2D (c b) (c (b + 1)) v =
      s * (orient2D (c a) (c (a + 1)) v - orient2D (c a) (c (a + 1)) (c b)) := by
    dsimp [s, u, w, edgeVec] at hdet_coord ⊢; unfold orient2D
    linear_combination (-((c (a + 1)).2 - (c a).2) * (v.2 - (c b).2) -
      ((c (a + 1)).1 - (c a).1) * (v.1 - (c b).1)) * hdet_coord
  have h1 := strictConvexCCW_orient_nonneg c hc a b
  have h2 := strictConvexCCW_orient_nonneg c hc b a
  have hsum_pos : 0 < orient2D (c a) (c (a + 1)) (c b) + orient2D (c b) (c (b + 1)) (c a) := by
    by_cases ha1b : a + 1 = b
    · have hb1a : b + 1 ≠ a := by
        intro h
        have h2a : a + (2 : Fin (k + 3)) = a + 0 := by
          calc a + 2 = a + 1 + 1 := by abel
            _ = b + 1 := by rw [ha1b]
            _ = a := h
            _ = a + 0 := by abel
        have h20 : (2 : Fin (k + 3)) = 0 := add_left_cancel h2a
        have hv := congrArg Fin.val h20
        simp [Nat.mod_eq_of_lt (by omega : 2 < k + 3)] at hv
      have hpos := hc b a hab hb1a.symm
      linarith
    · have hpos := hc a b hab.symm (Ne.symm ha1b)
      linarith
  have hs_neg : s < 0 := by
    rcases lt_or_gt_of_ne hs_ne with hlt | hgt
    · exact hlt
    · exfalso
      have hmul2 : 0 ≤ (u.1 ^ 2 + u.2 ^ 2) * orient2D (c b) (c (b + 1)) (c a) :=
        mul_nonneg (le_of_lt hu_sq) h2
      have hb_eq0 : orient2D (c b) (c (b + 1)) (c a) = 0 := by nlinarith
      have ha_eq0 : orient2D (c a) (c (a + 1)) (c b) = 0 := by nlinarith
      linarith
  have hlhs_pos : 0 < (u.1 ^ 2 + u.2 ^ 2) * orient2D (c b) (c (b + 1)) v := by
    rw [hid_v]
    exact mul_pos_of_neg_of_neg hs_neg (by linarith)
  have hlhs_neg : (u.1 ^ 2 + u.2 ^ 2) * orient2D (c b) (c (b + 1)) v < 0 :=
    mul_neg_of_pos_of_neg hu_sq hvb
  linarith

def finNat (N t : ℕ) [NeZero N] : Fin N := ⟨t % N, Nat.mod_lt t (NeZero.pos N)⟩

lemma finNat_zero (N : ℕ) [NeZero N] : finNat N 0 = 0 := by
  ext; simp [finNat]

lemma finNat_succ (N t : ℕ) [NeZero N] : finNat N (t + 1) = finNat N t + 1 := by
  ext; simp [finNat, Fin.val_add, Nat.add_mod]

lemma facing_arc_helper {k : ℕ} (c : Fin (k + 3) → ℝ × ℝ) (hc : StrictConvexCCWPoly c)
    (v : ℝ × ℝ) (a b : Fin (k + 3)) (hab_det : 0 < det2 (edgeVec c a) (edgeVec c b))
    (hva : orient2D (c a) (c (a + 1)) v < 0)
    (hvb : orient2D (c b) (c (b + 1)) v < 0) :
    ∀ t : ℕ, t < (b - a).val → orient2D (c (a + finNat (k + 3) t))
      (c (a + finNat (k + 3) t + 1)) v < 0 := by
  have ham_pos : ∀ t : ℕ, 0 < t → t < (b - a).val →
      0 < det2 (edgeVec c a) (edgeVec c (a + finNat (k + 3) t)) := by
    intro t ht0 htb
    by_contra hle
    replace hle : det2 (edgeVec c a) (edgeVec c (a + finNat (k + 3) t)) ≤ 0 := not_lt.mp hle
    have hprop : ∀ s : ℕ, t ≤ s → s ≤ (b - a).val →
        (s = t → det2 (edgeVec c a) (edgeVec c (a + finNat (k + 3) s)) ≤ 0) ∧
        (t < s → det2 (edgeVec c a) (edgeVec c (a + finNat (k + 3) s)) < 0) := by
      intro s hts hsb
      induction s, hts using Nat.le_induction with
      | base => exact ⟨fun _ => hle, fun h => absurd h (lt_irrefl _)⟩
      | succ s hts ih =>
        have ih' := ih (Nat.le_of_succ_le hsb)
        have hm_le : det2 (edgeVec c a) (edgeVec c (a + finNat (k + 3) s)) ≤ 0 := by
          rcases eq_or_lt_of_le hts with rfl | hlt
          · exact ih'.1 rfl
          · exact le_of_lt (ih'.2 hlt)
        have hs_lt : s < k + 3 := lt_trans (Nat.lt_of_succ_le hsb) (b - a).isLt
        have hm_ne : a + finNat (k + 3) s ≠ a := by
          intro h
          have h0 : finNat (k + 3) s = 0 := by
            apply add_left_cancel (a := a); simpa using h
          have hv := congrArg Fin.val h0
          change s % (k + 3) = 0 at hv
          rw [Nat.mod_eq_of_lt hs_lt] at hv
          omega
        have hm1_ne : a + finNat (k + 3) s + 1 ≠ a := by
          intro h
          have h0 : finNat (k + 3) (s + 1) = 0 := by
            rw [finNat_succ]; apply add_left_cancel (a := a); rw [← add_assoc]; simpa using h
          have hv := congrArg Fin.val h0
          change (s + 1) % (k + 3) = 0 at hv
          rw [Nat.mod_eq_of_lt (by omega : s + 1 < k + 3)] at hv
          omega
        have hstep := det2_edgeVec_unimodal c hc a _ hm_ne hm1_ne hm_le
        have hs1_eq : a + finNat (k + 3) (s + 1) = a + finNat (k + 3) s + 1 := by
          rw [finNat_succ, ← add_assoc]
        rw [hs1_eq]
        exact ⟨fun h => absurd h (by omega), fun _ => hstep⟩
    have hb_lt : det2 (edgeVec c a) (edgeVec c (a + finNat (k + 3) (b - a).val)) < 0 :=
      (hprop (b - a).val (Nat.le_of_lt htb) le_rfl).2 htb
    have hba_eq : a + finNat (k + 3) (b - a).val = b := by
      have : finNat (k + 3) (b - a).val = b - a := by
        ext; exact Nat.mod_eq_of_lt (b - a).isLt
      rw [this, add_sub_cancel]
    rw [hba_eq] at hb_lt
    linarith
  have hmb_pos : ∀ t : ℕ, 0 < t → t < (b - a).val →
      0 < det2 (edgeVec c (a + finNat (k + 3) t)) (edgeVec c b) := by
    intro t ht0 htb
    have hba_neg : det2 (edgeVec c b) (edgeVec c a) < 0 := by
      have hid : det2 (edgeVec c b) (edgeVec c a) = -det2 (edgeVec c a) (edgeVec c b) := by
        unfold det2; ring
      linarith
    have hprop : ∀ s : ℕ, s ≤ t →
        det2 (edgeVec c b) (edgeVec c (a + finNat (k + 3) s)) < 0 := by
      intro s hst
      induction s with
      | zero => simpa [finNat_zero] using hba_neg
      | succ s ih =>
        have ih' := ih (Nat.le_of_succ_le hst)
        have hs_lt : s < k + 3 := lt_trans (lt_trans (Nat.lt_of_succ_le hst) htb) (b - a).isLt
        have hm_ne : a + finNat (k + 3) s ≠ b := by
          intro h
          have hsub : finNat (k + 3) s = b - a := eq_sub_of_add_eq' h
          have hv := congrArg Fin.val hsub
          change s % (k + 3) = (b - a).val at hv
          rw [Nat.mod_eq_of_lt hs_lt] at hv
          omega
        have hm1_ne : a + finNat (k + 3) s + 1 ≠ b := by
          intro h
          have hsub : finNat (k + 3) (s + 1) = b - a := by
            rw [finNat_succ]; apply eq_sub_of_add_eq'; rwa [add_assoc] at h
          have hv := congrArg Fin.val hsub
          change (s + 1) % (k + 3) = (b - a).val at hv
          rw [Nat.mod_eq_of_lt (by omega : s + 1 < k + 3)] at hv
          omega
        have hstep := det2_edgeVec_unimodal c hc b _ hm_ne hm1_ne (le_of_lt ih')
        have hs1_eq : a + finNat (k + 3) (s + 1) = a + finNat (k + 3) s + 1 := by
          rw [finNat_succ, ← add_assoc]
        rwa [hs1_eq]
    have hlt := hprop t le_rfl
    have hid : det2 (edgeVec c (a + finNat (k + 3) t)) (edgeVec c b) =
        -det2 (edgeVec c b) (edgeVec c (a + finNat (k + 3) t)) := by
      unfold det2; ring
    linarith
  intro t htb
  by_cases ht0 : t = 0
  · subst ht0; simpa [finNat_zero] using hva
  · have ht_pos : 0 < t := Nat.pos_of_ne_zero ht0
    exact orient_edge_sandwich c hc v a _ b hab_det (ham_pos t ht_pos htb) (hmb_pos t ht_pos htb)
      hva hvb

/-- Contiguity of facing edges (`upper_9.tex` lines 601 & 611):
    For any two edges `a, b` of a strictly convex CCW polygon facing `v`, every edge on at
    least one of the two cyclic arcs `[a .. b]` or `[b .. a]` faces `v`. -/
theorem facing_edges_contiguous {k : ℕ} (c : Fin (k + 3) → ℝ × ℝ) (hc : StrictConvexCCWPoly c)
    (v : ℝ × ℝ) (a b : Fin (k + 3))
    (hva : orient2D (c a) (c (a + 1)) v < 0)
    (hvb : orient2D (c b) (c (b + 1)) v < 0) :
    (∀ m : Fin (k + 3), (m - a).val ≤ (b - a).val → orient2D (c m) (c (m + 1)) v < 0) ∨
    (∀ m : Fin (k + 3), (m - b).val ≤ (a - b).val → orient2D (c m) (c (m + 1)) v < 0) := by
  by_cases hab : a = b
  · subst hab
    left; intro m hm
    have h0 : (m - a).val = 0 := by simpa using hm
    have hm_eq : m = a := sub_eq_zero.mp (Fin.ext h0)
    subst hm_eq; exact hva
  · have hne := facing_edges_det_ne_zero c hc v a b hab hva hvb
    rcases lt_or_gt_of_ne hne with hneg | hpos
    · right
      have hpos' : 0 < det2 (edgeVec c b) (edgeVec c a) := by unfold det2 at *; linarith
      intro m hm
      rcases eq_or_lt_of_le hm with heq | hlt
      · have : m - b = a - b := Fin.ext heq
        have : m = a := by
          have := congrArg (· + b) this
          simpa [sub_add_cancel] using this
        subst this; exact hva
      · have h := facing_arc_helper c hc v b a hpos' hvb hva (m - b).val hlt
        have hm_eq : b + finNat (k + 3) (m - b).val = m := by
          have : finNat (k + 3) (m - b).val = m - b := by
            ext; exact Nat.mod_eq_of_lt (m - b).isLt
          rw [this, add_sub_cancel]
        rwa [hm_eq] at h
    · left
      intro m hm
      rcases eq_or_lt_of_le hm with heq | hlt
      · have : m - a = b - a := Fin.ext heq
        have : m = b := by
          have := congrArg (· + a) this
          simpa [sub_add_cancel] using this
        subst this; exact hvb
      · have h := facing_arc_helper c hc v a b hpos hva hvb (m - a).val hlt
        have hm_eq : a + finNat (k + 3) (m - a).val = m := by
          have : finNat (k + 3) (m - a).val = m - a := by
            ext; exact Nat.mod_eq_of_lt (m - a).isLt
          rw [this, add_sub_cancel]
        rwa [hm_eq] at h

/-- When `v` misses `q = w S`, all points of `S` seen by `v` lie on one open side of `G = v q`
    (via `hPoly.two_path_enclosure`). -/
lemma seen_same_side_of_misses_q {n : ℕ} {P : Set (ℝ × ℝ)}
    {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ}
    (hPoly : ShatteredSimplePolygon P S w)
    {Tv : Finset (Fin n)} (hmiss : ¬ Sees P (w Tv) (w Finset.univ)) :
    ∀ a b : Fin n, a ∈ Tv → b ∈ Tv → OnSameSide (w Tv) (w Finset.univ) (S a) (S b) := by
  intro a b ha hb
  have hv_ne_q : w Tv ≠ w Finset.univ := by
    intro heq
    apply hmiss
    rw [heq]
    exact sees_refl (hPoly.w_in_P Finset.univ)
  have hov_a : orient2D (w Tv) (w Finset.univ) (S a) ≠ 0 := by
    apply hPoly.no_three_collinear _ _ _
      (Or.inr (Set.mem_range_self _)) (Or.inr (Set.mem_range_self _)) (Or.inl (Set.mem_range_self _))
    · exact hv_ne_q
    · exact (hPoly.s_ne_w a Finset.univ).symm
    · exact (hPoly.s_ne_w a Tv).symm
  have hov_b : orient2D (w Tv) (w Finset.univ) (S b) ≠ 0 := by
    apply hPoly.no_three_collinear _ _ _
      (Or.inr (Set.mem_range_self _)) (Or.inr (Set.mem_range_self _)) (Or.inl (Set.mem_range_self _))
    · exact hv_ne_q
    · exact (hPoly.s_ne_w b Finset.univ).symm
    · exact (hPoly.s_ne_w b Tv).symm
  by_contra hnot
  have hmul_le : orient2D (w Tv) (w Finset.univ) (S a) * orient2D (w Tv) (w Finset.univ) (S b) ≤ 0 :=
    not_lt.mp hnot
  have hmul_lt : orient2D (w Tv) (w Finset.univ) (S a) * orient2D (w Tv) (w Finset.univ) (S b) < 0 :=
    lt_of_le_of_ne hmul_le (mul_ne_zero hov_a hov_b)
  have hva : Sees P (w Tv) (S a) := (hPoly.shatters Tv a).mpr ha
  have hqa : Sees P (S a) (w Finset.univ) := sees_symm ((hPoly.shatters Finset.univ a).mpr (Finset.mem_univ a))
  have hvb : Sees P (w Tv) (S b) := (hPoly.shatters Tv b).mpr hb
  have hqb : Sees P (S b) (w Finset.univ) := sees_symm ((hPoly.shatters Finset.univ b).mpr (Finset.mem_univ b))
  let π₁ : List (ℝ × ℝ) := [w Tv, S a, w Finset.univ]
  let π₂ : List (ℝ × ℝ) := [w Tv, S b, w Finset.univ]
  have hpath1 : IsPolygonalPathIn P (w Tv) (w Finset.univ) π₁ := by
    refine ⟨by simp [π₁], rfl, rfl, ?_, ?_⟩
    · intro x hx
      simp only [π₁, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact hPoly.w_in_P Tv
      · exact hPoly.s_in_P a
      · exact hPoly.w_in_P Finset.univ
    · exact List.isChain_cons_cons.mpr ⟨hva, List.isChain_cons_cons.mpr ⟨hqa, List.isChain_singleton _⟩⟩
  have hpath2 : IsPolygonalPathIn P (w Tv) (w Finset.univ) π₂ := by
    refine ⟨by simp [π₂], rfl, rfl, ?_, ?_⟩
    · intro x hx
      simp only [π₂, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact hPoly.w_in_P Tv
      · exact hPoly.s_in_P b
      · exact hPoly.w_in_P Finset.univ
    · exact List.isChain_cons_cons.mpr ⟨hvb, List.isChain_cons_cons.mpr ⟨hqb, List.isChain_singleton _⟩⟩
  rcases lt_or_gt_of_ne hov_a with ha_neg | ha_pos
  · have hb_pos : 0 < orient2D (w Tv) (w Finset.univ) (S b) := by nlinarith
    have hL : InteriorOnLeft (w Tv) (w Finset.univ) π₂ := by
      refine ⟨by simp [π₂], fun k hk hk0 hk1 => ?_⟩
      have hk_eq : k = 1 := by simp [π₂] at hk hk1; omega
      subst hk_eq; exact hb_pos
    have hR : InteriorOnRight (w Tv) (w Finset.univ) π₁ := by
      refine ⟨by simp [π₁], fun k hk hk0 hk1 => ?_⟩
      have hk_eq : k = 1 := by simp [π₁] at hk hk1; omega
      subst hk_eq; exact ha_neg
    exact hmiss (hPoly.two_path_enclosure (w Tv) (w Finset.univ) π₂ π₁ hv_ne_q hpath2 hpath1 hL hR)
  · have hb_neg : orient2D (w Tv) (w Finset.univ) (S b) < 0 := by nlinarith
    have hL : InteriorOnLeft (w Tv) (w Finset.univ) π₁ := by
      refine ⟨by simp [π₁], fun k hk hk0 hk1 => ?_⟩
      have hk_eq : k = 1 := by simp [π₁] at hk hk1; omega
      subst hk_eq; exact ha_pos
    have hR : InteriorOnRight (w Tv) (w Finset.univ) π₂ := by
      refine ⟨by simp [π₂], fun k hk hk0 hk1 => ?_⟩
      have hk_eq : k = 1 := by simp [π₂] at hk hk1; omega
      subst hk_eq; exact hb_neg
    exact hmiss (hPoly.two_path_enclosure (w Tv) (w Finset.univ) π₁ π₂ hv_ne_q hpath1 hpath2 hL hR)

/-! ## Part 7: Lemma 6.8 (`universal_crossing`) and Lemma 6.9 (`anchor_splitting`) -/

/-- Lemma 6.8 (`universal-crossing`, `upper_9.tex` lines 761–767). -/
theorem universal_crossing {n : ℕ} {P : Set (ℝ × ℝ)}
    {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ}
    (hPoly : ShatteredSimplePolygon P S w) (h25 : Sec2To5Interface P S w)
    {Tv Tq : Finset (Fin n)} {a_p c_p : Fin n}
    (ha_miss : a_p ∉ Tv) (hc_miss : c_p ∉ Tv)
    (ha_Tq : a_p ∈ Tq) (hc_Tq : c_p ∈ Tq)
    (hac_ang : AngleLt (w Tv) (w Tq) (S a_p) (S c_p))
    (hcond4 : Sees P (w Tv) (w Tq) ∨
      ∃ e : Fin n, e ∈ Tv ∧ e ∈ Tq ∧ AngleLt (w Tv) (w Tq) (S e) (S a_p))
    {z : Fin n} (hz_seen : z ∈ Tv) (hz_Tq : z ∈ Tq)
    (hcross : SegmentsCross (w Tv) (S z) (S a_p) (S c_p)) :
    (∃ H_hp : OpenHalfPlane, IsHalfPlaneTest P (WitnessSet {a_p, c_p} ∅ w) (S z) H_hp) ∧
    (z ∈ hullVertices S → IsBackVertexOf S (hullVertices S) z (w Tv)) := by
  have ⟨ha_ang, hc_ang⟩ := universal_crossing_angles hac_ang hcross
  refine ⟨h25.half_plane_lemma Tv Tq a_p z c_p hz_seen ha_miss hc_miss ha_Tq hz_Tq hc_Tq
    ha_ang hc_ang hcross hcond4, ?_⟩
  intro hzB
  have hne_az : a_p ≠ z := fun h => ha_miss (h ▸ hz_seen)
  have hne_cz : c_p ≠ z := fun h => hc_miss (h ▸ hz_seen)
  have hne_ac : a_p ≠ c_p := by
    intro h; subst h; exact AngleLt.irrefl (w Tv) (w Tq) (S a_p) hac_ang
  have hn3 : 3 ≤ n := by
    have h1 : a_p ∉ ({c_p, z} : Finset (Fin n)) := by simp [hne_ac, hne_az]
    have h2 : c_p ∉ ({z} : Finset (Fin n)) := by simp [hne_cz]
    have hcard : ({a_p, c_p, z} : Finset (Fin n)).card = 3 := by
      rw [Finset.card_insert_of_notMem h1, Finset.card_insert_of_notMem h2, Finset.card_singleton]
    have hle : ({a_p, c_p, z} : Finset (Fin n)).card ≤ n :=
      (Finset.card_le_univ _).trans_eq (Fintype.card_fin n)
    omega
  let B := hullVertices S
  have hB3 : 3 ≤ B.card := three_le_hullVertices_card S hPoly.s_inj
    (fun a b c hab hbc hac => hPoly.no_three_collinear _ _ _
      (Or.inl (Set.mem_range_self _)) (Or.inl (Set.mem_range_self _)) (Or.inl (Set.mem_range_self _))
      (hPoly.s_inj.ne hab) (hPoly.s_inj.ne hbc) (hPoly.s_inj.ne hac)) hn3
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hB3
  have hk' : B.card = k + 3 := by omega
  obtain ⟨cyc⟩ := exists_ccwCycle S B
    (fun a _ b _ h => hPoly.s_inj h)
    (fun a _ b _ c _ hab hbc hac => hPoly.no_three_collinear _ _ _
      (Or.inl (Set.mem_range_self _)) (Or.inl (Set.mem_range_self _)) (Or.inl (Set.mem_range_self _))
      (hPoly.s_inj.ne hab) (hPoly.s_inj.ne hbc) (hPoly.s_inj.ne hac))
    (hullVertices_convexPos S Subset.rfl) hk'
  obtain ⟨iz, hiz⟩ := ccwCycle_exists_index cyc hzB
  rw [← hiz, isBackVertexOf_iff_ccwCycle cyc iz (w Tv)]
  have hap_conv : S a_p ∈ convexHull ℝ (B.image S : Set (ℝ × ℝ)) :=
    mem_convexHull_hullVertices S hPoly.s_inj a_p
  have hcp_conv : S c_p ∈ convexHull ℝ (B.image S : Set (ℝ × ℝ)) :=
    mem_convexHull_hullVertices S hPoly.s_inj c_p
  have hcone_mem : ∀ x ∈ convexHull ℝ (B.image S : Set (ℝ × ℝ)),
      0 ≤ orient2D (S (cyc.toFun (iz - 1))) (S (cyc.toFun iz)) x ∧
      0 ≤ orient2D (S (cyc.toFun iz)) (S (cyc.toFun (iz + 1))) x := by
    intro x hx
    have hL1 : ∀ p q : ℝ × ℝ, Convex ℝ {y : ℝ × ℝ | 0 ≤ orient2D p q y} := by
      intro p q y1 hy1 y2 hy2 α β hα hβ hαβ
      have hα' : α = 1 - β := by linarith
      subst hα'
      have hid : orient2D p q ((1 - β) • y1 + β • y2) = (1 - β) * orient2D p q y1 + β * orient2D p q y2 := by
        unfold orient2D; dsimp; ring
      dsimp at hy1 hy2 ⊢
      rw [hid]
      exact add_nonneg (mul_nonneg hα hy1) (mul_nonneg hβ hy2)
    constructor
    · refine convexHull_min ?_ (hL1 _ _) hx
      intro y hy
      rcases Finset.mem_image.mp hy with ⟨r, hr, rfl⟩
      obtain ⟨ir, rfl⟩ := ccwCycle_exists_index cyc hr
      simpa [sub_add_cancel] using strictConvexCCW_orient_nonneg (S ∘ cyc.toFun) cyc.ccw (iz - 1) ir
    · refine convexHull_min ?_ (hL1 _ _) hx
      intro y hy
      rcases Finset.mem_image.mp hy with ⟨r, hr, rfl⟩
      obtain ⟨ir, rfl⟩ := ccwCycle_exists_index cyc hr
      exact strictConvexCCW_orient_nonneg (S ∘ cyc.toFun) cyc.ccw iz ir
  have hcorner : 0 < orient2D (S (cyc.toFun (iz - 1))) (S (cyc.toFun iz)) (S (cyc.toFun (iz + 1))) := by
    have him1_ne_ip1 : iz - 1 ≠ iz + 1 := by
      intro h
      have h' := congrArg (· + (1 : Fin (k + 3))) h
      rw [sub_add_cancel, add_assoc] at h'
      nth_rw 1 [← add_zero iz] at h'
      have h20 : (0 : Fin (k + 3)) = 2 := add_left_cancel h'
      have hv := congrArg Fin.val h20
      simp [Nat.mod_eq_of_lt (by omega : 2 < k + 3)] at hv
    have hi1_ne_i : iz + 1 ≠ iz := by
      intro h; nth_rw 2 [← add_zero iz] at h
      have h10 : (1 : Fin (k + 3)) = 0 := add_left_cancel h
      have hv := congrArg Fin.val h10
      simp [Nat.mod_eq_of_lt (by omega : 1 < k + 3)] at hv
    simpa [sub_add_cancel] using cyc.ccw (iz - 1) (iz + 1) him1_ne_ip1.symm
      (by rw [sub_add_cancel]; exact hi1_ne_i)
  have hne_zac : orient2D (S z) (S a_p) (S c_p) ≠ 0 :=
    hPoly.no_three_collinear _ _ _
      (Or.inl (Set.mem_range_self _)) (Or.inl (Set.mem_range_self _)) (Or.inl (Set.mem_range_self _))
      (hPoly.s_inj.ne hne_az.symm) (hPoly.s_inj.ne hne_ac) (hPoly.s_inj.ne hne_cz.symm)
  have h_helper : ∀ u₁ u₂ : Fin n, u₁ ≠ z → u₂ ≠ z → u₁ ≠ u₂ →
      0 < orient2D (S z) (S u₁) (S u₂) →
      SegmentsCross (w Tv) (S z) (S u₁) (S u₂) →
      0 ≤ orient2D (S (cyc.toFun (iz - 1))) (S (cyc.toFun iz)) (S u₁) →
      0 ≤ orient2D (S (cyc.toFun iz)) (S (cyc.toFun (iz + 1))) (S u₁) →
      0 ≤ orient2D (S (cyc.toFun (iz - 1))) (S (cyc.toFun iz)) (S u₂) →
      0 ≤ orient2D (S (cyc.toFun iz)) (S (cyc.toFun (iz + 1))) (S u₂) →
      0 < orient2D (S (cyc.toFun (iz - 1))) (S (cyc.toFun iz)) (w Tv) ∧
      0 < orient2D (S (cyc.toFun iz)) (S (cyc.toFun (iz + 1))) (w Tv) := by
    intro u₁ u₂ hu1z hu2z hu12 hpos_u hcr hu1a hu1b hu2a hu2b
    have hu12_z : orient2D (S u₁) (S u₂) (S z) = orient2D (S z) (S u₁) (S u₂) := orient2D_cycle _ _ _
    have huc_v : orient2D (S u₁) (S u₂) (w Tv) < 0 := by
      have h := hcr.2
      rw [hu12_z] at h
      nlinarith
    have hopp : orient2D (S z) (S u₁) (w Tv) * orient2D (S z) (S u₂) (w Tv) < 0 := by
      have hid : orient2D (S z) (S u₁) (w Tv) * orient2D (S z) (S u₂) (w Tv) =
          orient2D (w Tv) (S z) (S u₁) * orient2D (w Tv) (S z) (S u₂) := by
        unfold orient2D; ring
      rw [hid]; exact hcr.1
    have hsum : (-orient2D (S z) (S u₂) (w Tv)) + orient2D (S z) (S u₁) (w Tv) =
        orient2D (S z) (S u₁) (S u₂) - orient2D (S u₁) (S u₂) (w Tv) := by
      unfold orient2D; ring
    have hv1 : 0 < orient2D (S z) (S u₁) (w Tv) := by
      by_contra hle
      replace hle : orient2D (S z) (S u₁) (w Tv) ≤ 0 := not_lt.mp hle
      have hne0 : orient2D (S z) (S u₁) (w Tv) ≠ 0 := by
        intro h0; rw [h0, zero_mul] at hopp; linarith
      have hlt0 : orient2D (S z) (S u₁) (w Tv) < 0 := lt_of_le_of_ne hle hne0
      have hv2 : 0 < orient2D (S z) (S u₂) (w Tv) := by nlinarith
      linarith
    have hv2 : orient2D (S z) (S u₂) (w Tv) < 0 := by nlinarith
    rw [← hiz] at hpos_u hcr hv1 hv2
    exact crossing_anchor_implies_back_vertex (S (cyc.toFun (iz - 1))) (S (cyc.toFun iz))
      (S (cyc.toFun (iz + 1))) (S u₁) (S u₂) (w Tv) hcorner hu1a hu1b hu2a hu2b hpos_u hv1 hv2
  rcases lt_or_gt_of_ne hne_zac with hneg | hpos
  · have hpos' : 0 < orient2D (S z) (S c_p) (S a_p) := by
      rw [orient2D_swap23]; linarith
    exact h_helper c_p a_p hne_cz hne_az hne_ac.symm hpos' hcross.symm34
      (hcone_mem _ hcp_conv).1 (hcone_mem _ hcp_conv).2
      (hcone_mem _ hap_conv).1 (hcone_mem _ hap_conv).2
  · exact h_helper a_p c_p hne_az hne_cz hne_ac hpos hcross
      (hcone_mem _ hap_conv).1 (hcone_mem _ hap_conv).2
      (hcone_mem _ hcp_conv).1 (hcone_mem _ hcp_conv).2

/-- Lemma 6.9 (`anchor-splitting`, `upper_9.tex` lines 769–775). -/
theorem anchor_splitting {n : ℕ} {P : Set (ℝ × ℝ)}
    {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ}
    (hPoly : ShatteredSimplePolygon P S w) (h25 : Sec2To5Interface P S w)
    (hD3 : 3 ≤ (hullVertices S \ certifiedVertices S w).card)
    {y' y'' u v : Fin n} (hyne : y' ≠ y'')
    (hy'M : y' ∈ Finset.univ \ (hullVertices S \ certifiedVertices S w))
    (hy''M : y'' ∈ Finset.univ \ (hullVertices S \ certifiedVertices S w))
    (huv : IsCCWEdge S (hullVertices S \ certifiedVertices S w) u v)
    (hpos : 0 < orient2D (S u) (S v) (w (hullVertices S \ certifiedVertices S w)))
    (hy'_fan : InIntTri (w (hullVertices S \ certifiedVertices S w)) (S u) (S v) (S y'))
    (hy''_fan : InIntTri (w (hullVertices S \ certifiedVertices S w)) (S u) (S v) (S y''))
    (hnot_in : S y'' ∉ convexHull ℝ ({S u, S v, S y'} : Set (ℝ × ℝ))) :
    (∀ x ∈ WitnessSet {u, y'} ∅ w, InIntTri x (S u) (S y') (S y'')) ∨
    (∀ x ∈ WitnessSet {y', v} ∅ w, InIntTri x (S y') (S v) (S y'')) := by
  let D := hullVertices S \ certifiedVertices S w
  have huD : u ∈ D := huv.1
  have hvD : v ∈ D := huv.2.1
  have hy''_ne_u : y'' ≠ u := fun h => by
    rw [Finset.mem_sdiff] at hy''M; exact hy''M.2 (h ▸ huD)
  have hy''_ne_v : y'' ≠ v := fun h => by
    rw [Finset.mem_sdiff] at hy''M; exact hy''M.2 (h ▸ hvD)
  obtain ⟨u1, v1, _, _, _, _, hy'W, huniq1⟩ := h25.exit_edge_lemma hD3 y' hy'M
  have ⟨hu1, hv1⟩ := huniq1 u v huv hpos hy'_fan.to_convexHull
  rw [← hu1, ← hv1] at hy'W
  obtain ⟨u2, v2, _, _, _, _, hy''W, huniq2⟩ := h25.exit_edge_lemma hD3 y'' hy''M
  have ⟨hu2, hv2⟩ := huniq2 u v huv hpos hy''_fan.to_convexHull
  rw [← hu2, ← hv2] at hy''W
  let Tw := Finset.univ.erase y''
  have hTw_wit : w Tw ∈ WitnessSet {u, v} ∅ w := by
    refine ⟨Tw, ?_, Finset.disjoint_empty_right _, rfl⟩
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact Finset.mem_erase.mpr ⟨hy''_ne_u.symm, Finset.mem_univ _⟩
    · exact Finset.mem_erase.mpr ⟨hy''_ne_v.symm, Finset.mem_univ _⟩
  have hy'_Tw : InIntTri (w Tw) (S u) (S v) (S y') := hy'W (w Tw) hTw_wit
  have hy''_Tw : InIntTri (w Tw) (S u) (S v) (S y'') := hy''W (w Tw) hTw_wit
  have hw0_pos : 0 < orient2D (S u) (S v) (w Tw) := by
    have hy'_uv : 0 < orient2D (S u) (S v) (S y') :=
      ((inIntTri_iff_orient_pos hpos).mp hy'_fan.cycle).1
    rcases hy'_Tw with ⟨μ₁, μ₂, μ₃, h1, _, _, hsum, heq1, heq2⟩
    have hid := orient2D_convex_comb3 (S u) (S v) (w Tw) (S u) (S v) (S y') μ₁ μ₂ μ₃ hsum heq1 heq2
    rw [orient2D_self_outer, orient2D_self_right, mul_zero, mul_zero, add_zero] at hid
    by_contra hle
    replace hle : orient2D (S u) (S v) (w Tw) ≤ 0 := not_lt.mp hle
    have : μ₁ * orient2D (S u) (S v) (w Tw) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (le_of_lt h1) hle
    linarith
  have ho1 := (inIntTri_iff_orient_pos hw0_pos).mp hy'_Tw.cycle
  have ho2 := (inIntTri_iff_orient_pos hw0_pos).mp hy''_Tw.cycle
  have hy'_uv_pos : 0 < orient2D (S u) (S v) (S y') := ho1.1
  have hnot_cap : ¬ (0 ≤ orient2D (S u) (S v) (S y'') ∧ 0 ≤ orient2D (S v) (S y') (S y'') ∧
      0 ≤ orient2D (S y') (S u) (S y'')) := by
    rintro ⟨a1, a2, a3⟩
    apply hnot_in
    rw [← inClosedTri_iff_mem_convexHull]
    let det := orient2D (S u) (S v) (S y')
    have hdet : det ≠ 0 := ne_of_gt hy'_uv_pos
    refine ⟨orient2D (S v) (S y') (S y'') / det, orient2D (S y') (S u) (S y'') / det,
      orient2D (S u) (S v) (S y'') / det,
      div_nonneg a2 (le_of_lt hy'_uv_pos), div_nonneg a3 (le_of_lt hy'_uv_pos),
      div_nonneg a1 (le_of_lt hy'_uv_pos), ?_, ?_, ?_⟩
    · rw [← add_div, ← add_div, orient2D_barycentric_sum, div_self hdet]
    · have hx := orient2D_barycentric_x (S u) (S v) (S y') (S y'')
      field_simp [hdet]; linarith
    · have hy := orient2D_barycentric_y (S u) (S v) (S y') (S y'')
      field_simp [hdet]; linarith
  have hne_w0 : orient2D (w Tw) (S y') (S y'') ≠ 0 :=
    hPoly.no_three_collinear _ _ _
      (Or.inr (Set.mem_range_self _)) (Or.inl (Set.mem_range_self _)) (Or.inl (Set.mem_range_self _))
      (hPoly.s_ne_w _ _).symm (hPoly.s_inj.ne hyne) (hPoly.s_ne_w _ _).symm
  have hsplit := anchor_splitting_orient (w Tw) (S u) (S v) (S y') (S y'')
    (orient2D_cycle (w Tw) (S u) (S v) ▸ hw0_pos)
    ho1.1 ho1.2.1 ho1.2.2 ho2.1 ho2.2.1 ho2.2.2 hnot_cap hne_w0
  rcases hsplit with ⟨s1, s2, s3⟩ | ⟨s1, s2, s3⟩
  · left
    have h_base : InIntTri (w Tw) (S u) (S y') (S y'') :=
      (inIntTri_iff_orient_pos ho1.2.2).mpr ⟨s1, s2, s3⟩
    rintro x ⟨T, hFT, _, rfl⟩
    by_cases hTTw : T = Tw
    · rwa [hTTw]
    · have huT : u ∈ T := hFT (by simp)
      have hy'T : y' ∈ T := hFT (by simp)
      apply h25.cone_lemma (S y'') (S u) (S y') (w Tw) (w T)
        (hPoly.s_in_P _) (hPoly.s_in_P _) (hPoly.s_in_P _) (hPoly.w_in_P _) (hPoly.w_in_P _)
      · exact (hPoly.shatters Tw u).mpr (Finset.mem_erase.mpr ⟨hy''_ne_u.symm, Finset.mem_univ _⟩)
      · exact (hPoly.shatters Tw y').mpr (Finset.mem_erase.mpr ⟨hyne, Finset.mem_univ _⟩)
      · intro hs; exact Finset.notMem_erase y'' Finset.univ ((hPoly.shatters Tw y'').mp hs)
      · exact h_base
      · exact (hPoly.shatters T u).mpr huT
      · exact (hPoly.shatters T y').mpr hy'T
      · exact hPoly.no_three_collinear _ _ _
          (Or.inl (Set.mem_range_self _)) (Or.inl (Set.mem_range_self _)) (Or.inr (Set.mem_range_self _))
          (hPoly.s_inj.ne hy''_ne_u) (hPoly.s_ne_w _ _) (hPoly.s_ne_w _ _)
      · exact hPoly.no_three_collinear _ _ _
          (Or.inl (Set.mem_range_self _)) (Or.inl (Set.mem_range_self _)) (Or.inr (Set.mem_range_self _))
          (hPoly.s_inj.ne hyne.symm) (hPoly.s_ne_w _ _) (hPoly.s_ne_w _ _)
      · exact hPoly.no_three_collinear _ _ _
          (Or.inr (Set.mem_range_self _)) (Or.inl (Set.mem_range_self _)) (Or.inr (Set.mem_range_self _))
          (hPoly.s_ne_w _ _).symm (hPoly.s_ne_w _ _) (hPoly.w_inj.ne (Ne.symm hTTw))

  · right
    have h_base : InIntTri (w Tw) (S y') (S v) (S y'') :=
      (inIntTri_iff_orient_pos (by unfold orient2D at *; linarith [ho1.2.1])).mpr ⟨s1, s2, s3⟩
    rintro x ⟨T, hFT, _, rfl⟩
    by_cases hTTw : T = Tw
    · rwa [hTTw]
    · have hy'T : y' ∈ T := hFT (by simp)
      have hvT : v ∈ T := hFT (by simp)
      apply h25.cone_lemma (S y'') (S y') (S v) (w Tw) (w T)
        (hPoly.s_in_P _) (hPoly.s_in_P _) (hPoly.s_in_P _) (hPoly.w_in_P _) (hPoly.w_in_P _)
      · exact (hPoly.shatters Tw y').mpr (Finset.mem_erase.mpr ⟨hyne, Finset.mem_univ _⟩)
      · exact (hPoly.shatters Tw v).mpr (Finset.mem_erase.mpr ⟨hy''_ne_v.symm, Finset.mem_univ _⟩)
      · intro hs; exact Finset.notMem_erase y'' Finset.univ ((hPoly.shatters Tw y'').mp hs)
      · exact h_base
      · exact (hPoly.shatters T y').mpr hy'T
      · exact (hPoly.shatters T v).mpr hvT
      · exact hPoly.no_three_collinear _ _ _
          (Or.inl (Set.mem_range_self _)) (Or.inl (Set.mem_range_self _)) (Or.inr (Set.mem_range_self _))
          (hPoly.s_inj.ne hyne.symm) (hPoly.s_ne_w _ _) (hPoly.s_ne_w _ _)
      · exact hPoly.no_three_collinear _ _ _
          (Or.inl (Set.mem_range_self _)) (Or.inl (Set.mem_range_self _)) (Or.inr (Set.mem_range_self _))
          (hPoly.s_inj.ne hy''_ne_v) (hPoly.s_ne_w _ _) (hPoly.s_ne_w _ _)
      · exact hPoly.no_three_collinear _ _ _
          (Or.inr (Set.mem_range_self _)) (Or.inl (Set.mem_range_self _)) (Or.inr (Set.mem_range_self _))
          (hPoly.s_ne_w _ _).symm (hPoly.s_ne_w _ _) (hPoly.w_inj.ne (Ne.symm hTTw))

/-! ## Part 5d: Far Chain Contiguous Arcs, Angle Monotonicity, and Cap Slicing -/

lemma convex_fourgon_no_alternating_line (a b c d v q : ℝ × ℝ)
    (h1 : 0 < orient2D b c d) (h2 : 0 < orient2D c d a)
    (h3 : 0 < orient2D d a b) (h4 : 0 < orient2D a b c) :
    ¬ (0 < orient2D v q a ∧ orient2D v q b < 0 ∧ 0 < orient2D v q c ∧ orient2D v q d < 0) ∧
    ¬ (orient2D v q a < 0 ∧ 0 < orient2D v q b ∧ orient2D v q c < 0 ∧ 0 < orient2D v q d) := by
  have hid : orient2D b c d * orient2D v q a + orient2D d a b * orient2D v q c =
      orient2D c d a * orient2D v q b + orient2D a b c * orient2D v q d := by
    unfold orient2D; ring
  constructor
  · rintro ⟨ha, hb, hc, hd⟩
    have hl : 0 < orient2D b c d * orient2D v q a + orient2D d a b * orient2D v q c :=
      add_pos (mul_pos h1 ha) (mul_pos h3 hc)
    have hr : orient2D c d a * orient2D v q b + orient2D a b c * orient2D v q d < 0 :=
      add_neg (mul_neg_of_pos_of_neg h2 hb) (mul_neg_of_pos_of_neg h4 hd)
    linarith
  · rintro ⟨ha, hb, hc, hd⟩
    have hl : orient2D b c d * orient2D v q a + orient2D d a b * orient2D v q c < 0 :=
      add_neg (mul_neg_of_pos_of_neg h1 ha) (mul_neg_of_pos_of_neg h3 hc)
    have hr : 0 < orient2D c d a * orient2D v q b + orient2D a b c * orient2D v q d :=
      add_pos (mul_pos h2 hb) (mul_pos h4 hd)
    linarith

private lemma fin_val_sub_eq {N : ℕ} [NeZero N] (x y : Fin N) :
    (x - y).val = if y ≤ x then x.val - y.val else N + x.val - y.val := by
  have hN : 0 < N := NeZero.pos N
  by_cases hy0 : y = 0
  · subst hy0; simp
  · have hy_pos : 0 < y.val := Nat.pos_of_ne_zero (fun h => hy0 (Fin.ext h))
    have heq : x - y = x + (-y) := sub_eq_add_neg x y
    rw [heq, Fin.val_add, Fin.val_neg]
    simp only [if_neg hy0]
    split_ifs with hle
    · have h1 : x.val + (N - y.val) = (x.val - y.val) + N := by omega
      rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    · have hlt : x.val < y.val := Nat.lt_of_not_le hle
      have h1 : x.val + (N - y.val) = N + x.val - y.val := by omega
      rw [h1, Nat.mod_eq_of_lt (by omega)]

lemma fin_sub_add_compl {N : ℕ} [NeZero N] {a b : Fin N} (hab : a ≠ b) :
    (b - a).val + (a - b).val = N := by
  rw [fin_val_sub_eq b a, fin_val_sub_eq a b]
  rcases lt_or_gt_of_ne hab with h | h
  · have h1 : a ≤ b := le_of_lt h
    have h2 : ¬ b ≤ a := not_le.mpr h
    simp [h1, h2]; omega
  · have h1 : ¬ a ≤ b := not_le.mpr h
    have h2 : b ≤ a := le_of_lt h
    simp [h1, h2]; omega

private lemma fin_sub_split_lt {N : ℕ} [NeZero N] {x y z : Fin N}
    (hxy : 0 < (y - x).val) (hyz : (y - x).val < (z - x).val) :
    (z - y).val + (y - x).val = (z - x).val ∧ 0 < (z - y).val := by
  have heq : z - x = (z - y) + (y - x) := by abel
  have hv := congrArg Fin.val heq
  rw [Fin.val_add] at hv
  have hsum_lt : (z - y).val + (y - x).val < N := by
    by_contra hge
    replace hge : N ≤ (z - y).val + (y - x).val := not_lt.mp hge
    have hlt2N : (z - y).val + (y - x).val - N < N := by
      have := (z - y).isLt; have := (y - x).isLt; omega
    have hmod : ((z - y).val + (y - x).val) % N = (z - y).val + (y - x).val - N := by
      have h1 : (z - y).val + (y - x).val = ((z - y).val + (y - x).val - N) + N := by omega
      conv_lhs => rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt hlt2N]
    rw [hmod] at hv
    have := (z - y).isLt
    omega
  rw [Nat.mod_eq_of_lt hsum_lt] at hv
  exact ⟨hv.symm, by omega⟩

private lemma fin_sub_one_val_lt {N : ℕ} [NeZero N] (hN : 1 < N) {x : Fin N} (hx : 0 < x.val) :
    (x - 1).val < x.val := by
  rw [fin_val_sub_eq]
  have h1val : (1 : Fin N).val = 1 := Nat.mod_eq_of_lt hN
  have h1 : (1 : Fin N) ≤ x := Fin.le_def.mpr (by rw [h1val]; omega)
  rw [if_pos h1, h1val]; omega

lemma ccwCycle_ccw3 {n k : ℕ} {S : Fin n → ℝ × ℝ} {C : Finset (Fin n)}
    (cyc : CCWCycle S C k) {a b c : Fin (k + 3)}
    (h1 : 0 < (b - a).val) (h2 : (b - a).val < (c - a).val) :
    0 < orient2D (S (cyc.toFun a)) (S (cyc.toFun b)) (S (cyc.toFun c)) := by
  have hba := fin_val_sub_eq b a
  have hca := fin_val_sub_eq c a
  rw [hba] at h1 h2
  rw [hca] at h2
  have hab : a ≠ b := fun h => by subst h; simp at h1
  have hbc : b ≠ c := fun h => by subst h; omega
  have hac : a ≠ c := fun h => by subst h; simp at h2
  rcases lt_or_gt_of_ne hab with h_ab | h_ba
  · rcases lt_or_gt_of_ne hbc with h_bc | h_cb
    · exact cyc.ccw_tri a b c h_ab h_bc
    · rcases lt_or_gt_of_ne hac with h_ac | h_ca
      · exfalso; simp only [le_of_lt h_ab, le_of_lt h_ac, ↓reduceIte] at h2
        have h1' : b.val < c.val := by omega
        exact absurd h_cb (not_lt.mpr (le_of_lt h1'))
      · rw [orient2D_cycle]
        exact cyc.ccw_tri c a b h_ca h_ab
  · rcases lt_or_gt_of_ne hbc with h_bc | h_cb
    · rcases lt_or_gt_of_ne hac with h_ac | h_ca
      · exfalso
        have hna : ¬ a ≤ b := not_le.mpr h_ba
        simp only [hna, le_of_lt h_ac, ↓reduceIte] at h2
        omega
      · rw [orient2D_cycle, orient2D_cycle]
        exact cyc.ccw_tri b c a h_bc h_ca
    · exfalso
      have hna : ¬ a ≤ b := not_le.mpr h_ba
      rcases le_or_gt a c with h_ac | h_ca
      · simp only [hna, h_ac, ↓reduceIte] at h2; omega
      · simp only [hna, not_le.mpr h_ca, ↓reduceIte] at h2
        have hcb_val : c.val < b.val := Fin.lt_def.mp h_cb
        omega

lemma ccwCycle_fourgon_orient {n k : ℕ} {S : Fin n → ℝ × ℝ} {C : Finset (Fin n)}
    (cyc : CCWCycle S C k) (i₀ i₁ i₂ i₃ : Fin (k + 3))
    (h01 : 0 < (i₁ - i₀).val) (h12 : (i₁ - i₀).val < (i₂ - i₀).val)
    (h23 : (i₂ - i₀).val < (i₃ - i₀).val) :
    0 < orient2D (S (cyc.toFun i₁)) (S (cyc.toFun i₂)) (S (cyc.toFun i₃)) ∧
    0 < orient2D (S (cyc.toFun i₂)) (S (cyc.toFun i₃)) (S (cyc.toFun i₀)) ∧
    0 < orient2D (S (cyc.toFun i₃)) (S (cyc.toFun i₀)) (S (cyc.toFun i₁)) ∧
    0 < orient2D (S (cyc.toFun i₀)) (S (cyc.toFun i₁)) (S (cyc.toFun i₂)) := by
  have h012 := ccwCycle_ccw3 cyc h01 h12
  have h023 := ccwCycle_ccw3 cyc (lt_trans h01 h12) h23
  have h013 := ccwCycle_ccw3 cyc h01 (lt_trans h12 h23)
  have ⟨hs21, h1_lt⟩ := fin_sub_split_lt h01 h12
  have ⟨hs31, _⟩ := fin_sub_split_lt h01 (lt_trans h12 h23)
  have h2_lt : (i₂ - i₁).val < (i₃ - i₁).val := by omega
  have h123 := ccwCycle_ccw3 cyc h1_lt h2_lt
  refine ⟨h123, ?_, ?_, h012⟩
  · rw [orient2D_cycle]; exact h023
  · rw [orient2D_cycle, orient2D_cycle]; exact h013

lemma convex_crossing_both_sides_in_conv {k : ℕ} (c : Fin (k + 3) → ℝ × ℝ)
    (hc : StrictConvexCCWPoly c) (v q : ℝ × ℝ)
    (hv_noncol : ∀ i j : Fin (k + 3), i ≠ j → orient2D (c i) (c j) v ≠ 0)
    (m0 m1 : Fin (k + 3))
    (hnf0 : 0 < orient2D (c m0) (c (m0 + 1)) v)
    (hnf1 : 0 < orient2D (c m1) (c (m1 + 1)) v)
    (hd0 : 0 < orient2D v q (c m0)) (hd1 : orient2D v q (c (m0 + 1)) < 0)
    (he0 : orient2D v q (c m1) < 0) (he1 : 0 < orient2D v q (c (m1 + 1))) :
    ∀ m : Fin (k + 3), 0 < orient2D (c m) (c (m + 1)) v := by
  let d0 := orient2D v q (c m0)
  let d1 := orient2D v q (c (m0 + 1))
  let e0 := orient2D v q (c m1)
  let e1 := orient2D v q (c (m1 + 1))
  have hD : 0 < d0 - d1 := by dsimp [d0, d1]; linarith
  have hE : 0 < e1 - e0 := by dsimp [e0, e1]; linarith
  have hDne : d0 - d1 ≠ 0 := ne_of_gt hD
  have hEne : e1 - e0 ≠ 0 := ne_of_gt hE
  let x0 : ℝ × ℝ := ((-d1) / (d0 - d1)) • c m0 + (d0 / (d0 - d1)) • c (m0 + 1)
  let x1 : ℝ × ℝ := (e1 / (e1 - e0)) • c m1 + ((-e0) / (e1 - e0)) • c (m1 + 1)
  have hx0_conv : x0 ∈ convexHull ℝ (Set.range c) :=
    (convex_convexHull ℝ (Set.range c))
      (subset_convexHull ℝ (Set.range c) (Set.mem_range_self m0))
      (subset_convexHull ℝ (Set.range c) (Set.mem_range_self (m0 + 1)))
      (div_nonneg (by dsimp [d1]; linarith) (le_of_lt hD))
      (div_nonneg (by dsimp [d0]; linarith) (le_of_lt hD))
      (by field_simp [hDne]; ring)
  have hx1_conv : x1 ∈ convexHull ℝ (Set.range c) :=
    (convex_convexHull ℝ (Set.range c))
      (subset_convexHull ℝ (Set.range c) (Set.mem_range_self m1))
      (subset_convexHull ℝ (Set.range c) (Set.mem_range_self (m1 + 1)))
      (div_nonneg (by dsimp [e1]; linarith) (le_of_lt hE))
      (div_nonneg (by dsimp [e0]; linarith) (le_of_lt hE))
      (by field_simp [hEne]; ring)
  let N0 : ℝ := orient2D (c m0) (c (m0 + 1)) v / (d0 - d1)
  let N1 : ℝ := orient2D (c m1) (c (m1 + 1)) v / (e1 - e0)
  have hN0 : 0 < N0 := div_pos hnf0 hD
  have hN1 : 0 < N1 := div_pos hnf1 hE
  have hNsum : 0 < N0 + N1 := add_pos hN0 hN1
  have hNsum_ne : N0 + N1 ≠ 0 := ne_of_gt hNsum
  have hid0_1 : (d0 - d1) * (x0.1 - v.1) = -orient2D (c m0) (c (m0 + 1)) v * (q.1 - v.1) := by
    have hDne' : (q.1 - v.1) * ((c m0).2 - v.2) - (q.2 - v.2) * ((c m0).1 - v.1) -
        ((q.1 - v.1) * ((c (m0 + 1)).2 - v.2) - (q.2 - v.2) * ((c (m0 + 1)).1 - v.1)) ≠ 0 := by
      change orient2D v q (c m0) - orient2D v q (c (m0 + 1)) ≠ 0; exact hDne
    dsimp [x0, d0, d1]; unfold orient2D; field_simp [hDne']; ring
  have hid0_2 : (d0 - d1) * (x0.2 - v.2) = -orient2D (c m0) (c (m0 + 1)) v * (q.2 - v.2) := by
    have hDne' : (q.1 - v.1) * ((c m0).2 - v.2) - (q.2 - v.2) * ((c m0).1 - v.1) -
        ((q.1 - v.1) * ((c (m0 + 1)).2 - v.2) - (q.2 - v.2) * ((c (m0 + 1)).1 - v.1)) ≠ 0 := by
      change orient2D v q (c m0) - orient2D v q (c (m0 + 1)) ≠ 0; exact hDne
    dsimp [x0, d0, d1]; unfold orient2D; field_simp [hDne']; ring
  have hid1_1 : (e1 - e0) * (x1.1 - v.1) = orient2D (c m1) (c (m1 + 1)) v * (q.1 - v.1) := by
    have hEne' : (q.1 - v.1) * ((c (m1 + 1)).2 - v.2) - (q.2 - v.2) * ((c (m1 + 1)).1 - v.1) -
        ((q.1 - v.1) * ((c m1).2 - v.2) - (q.2 - v.2) * ((c m1).1 - v.1)) ≠ 0 := by
      change orient2D v q (c (m1 + 1)) - orient2D v q (c m1) ≠ 0; exact hEne
    dsimp [x1, e0, e1]; unfold orient2D; field_simp [hEne']; ring
  have hid1_2 : (e1 - e0) * (x1.2 - v.2) = orient2D (c m1) (c (m1 + 1)) v * (q.2 - v.2) := by
    have hEne' : (q.1 - v.1) * ((c (m1 + 1)).2 - v.2) - (q.2 - v.2) * ((c (m1 + 1)).1 - v.1) -
        ((q.1 - v.1) * ((c m1).2 - v.2) - (q.2 - v.2) * ((c m1).1 - v.1)) ≠ 0 := by
      change orient2D v q (c (m1 + 1)) - orient2D v q (c m1) ≠ 0; exact hEne
    dsimp [x1, e0, e1]; unfold orient2D; field_simp [hEne']; ring
  have hx0_1 : x0.1 - v.1 = -N0 * (q.1 - v.1) := by
    have hne : d0 - d1 ≠ 0 := hDne
    dsimp [N0]; field_simp [hne]; linear_combination hid0_1
  have hx0_2 : x0.2 - v.2 = -N0 * (q.2 - v.2) := by
    have hne : d0 - d1 ≠ 0 := hDne
    dsimp [N0]; field_simp [hne]; linear_combination hid0_2
  have hx1_1 : x1.1 - v.1 = N1 * (q.1 - v.1) := by
    have hne : e1 - e0 ≠ 0 := hEne
    dsimp [N1]; field_simp [hne]; linear_combination hid1_1
  have hx1_2 : x1.2 - v.2 = N1 * (q.2 - v.2) := by
    have hne : e1 - e0 ≠ 0 := hEne
    dsimp [N1]; field_simp [hne]; linear_combination hid1_2
  have hv_eq : (N1 / (N0 + N1)) • x0 + (N0 / (N0 + N1)) • x1 = v := by
    have hs1 : (N1 / (N0 + N1)) * (x0.1 - v.1) + (N0 / (N0 + N1)) * (x1.1 - v.1) = 0 := by
      rw [hx0_1, hx1_1]; ring
    have hs2 : (N1 / (N0 + N1)) * (x0.2 - v.2) + (N0 / (N0 + N1)) * (x1.2 - v.2) = 0 := by
      rw [hx0_2, hx1_2]; ring
    have hsum1 : N1 / (N0 + N1) + N0 / (N0 + N1) = 1 := by field_simp [hNsum_ne]; ring
    ext <;> dsimp
    · linear_combination hs1 + v.1 * hsum1
    · linear_combination hs2 + v.2 * hsum1
  have hv_conv : v ∈ convexHull ℝ (Set.range c) := by
    rw [← hv_eq]
    exact (convex_convexHull ℝ (Set.range c)) hx0_conv hx1_conv
      (div_nonneg (le_of_lt hN1) (le_of_lt hNsum))
      (div_nonneg (le_of_lt hN0) (le_of_lt hNsum))
      (by field_simp [hNsum_ne]; ring)
  intro m
  have hle : 0 ≤ orient2D (c m) (c (m + 1)) v := by
    have hK : Convex ℝ {z : ℝ × ℝ | 0 ≤ orient2D (c m) (c (m + 1)) z} := by
      intro a ha b hb α β hα hβ hαβ
      dsimp at ha hb ⊢
      have hid : orient2D (c m) (c (m + 1)) (α • a + β • b) =
          α * orient2D (c m) (c (m + 1)) a + β * orient2D (c m) (c (m + 1)) b := by
        unfold orient2D; dsimp; linear_combination ((c m).2 * (c (m + 1)).1 - (c m).1 * (c (m + 1)).2) * hαβ
      rw [hid]; exact add_nonneg (mul_nonneg hα ha) (mul_nonneg hβ hb)
    exact convexHull_min (fun p hp => by rcases hp with ⟨i, rfl⟩; exact strictConvexCCW_orient_nonneg c hc m i)
      hK hv_conv
  have hm1_ne : m ≠ m + 1 := by
    intro h; nth_rw 1 [← add_zero m] at h
    have hv := congrArg Fin.val (add_left_cancel h)
    simp [Nat.mod_eq_of_lt (by omega : 1 < k + 3)] at hv
  exact lt_of_le_of_ne hle (Ne.symm (hv_noncol m (m + 1) hm1_ne))

lemma farChain_path_between {n k : ℕ} {S : Fin n → ℝ × ℝ} {C : Finset (Fin n)}
    (cyc : CCWCycle S C k) (v q : ℝ × ℝ)
    (hv_noncol : ∀ i j : Fin (k + 3), i ≠ j → orient2D (S (cyc.toFun i)) (S (cyc.toFun j)) v ≠ 0)
    (hvq : ∀ i : Fin (k + 3), orient2D v q (S (cyc.toFun i)) ≠ 0)
    (a b : Fin (k + 3)) (hab : a ≠ b)
    (hss : OnSameSide v q (S (cyc.toFun a)) (S (cyc.toFun b)))
    (hna : 0 < orient2D (S (cyc.toFun (a - 1))) (S (cyc.toFun a)) v ∨
           0 < orient2D (S (cyc.toFun a)) (S (cyc.toFun (a + 1))) v)
    (hnb : 0 < orient2D (S (cyc.toFun (b - 1))) (S (cyc.toFun b)) v ∨
           0 < orient2D (S (cyc.toFun b)) (S (cyc.toFun (b + 1))) v) :
    ((∀ t : ℕ, t < (b - a).val →
        0 < orient2D (S (cyc.toFun (a + finNat (k + 3) t)))
                     (S (cyc.toFun (a + finNat (k + 3) t + 1))) v) ∧
     (∀ t : ℕ, t ≤ (b - a).val →
        OnSameSide v q (S (cyc.toFun a)) (S (cyc.toFun (a + finNat (k + 3) t))))) ∨
    ((∀ t : ℕ, t < (a - b).val →
        0 < orient2D (S (cyc.toFun (b + finNat (k + 3) t)))
                     (S (cyc.toFun (b + finNat (k + 3) t + 1))) v) ∧
     (∀ t : ℕ, t ≤ (a - b).val →
        OnSameSide v q (S (cyc.toFun a)) (S (cyc.toFun (b + finNat (k + 3) t))))) := by
  let c : Fin (k + 3) → ℝ × ℝ := fun i => S (cyc.toFun i)
  have hc : StrictConvexCCWPoly c := cyc.ccw
  have hedge_ne0 : ∀ m : Fin (k + 3), orient2D (c m) (c (m + 1)) v ≠ 0 := by
    intro m
    refine hv_noncol m (m + 1) (fun h => ?_)
    nth_rw 1 [← add_zero m] at h
    have hv := congrArg Fin.val (add_left_cancel h)
    simp [Nat.mod_eq_of_lt (by omega : 1 < k + 3)] at hv
  have hf_arc :
      (∀ t : ℕ, t < (b - a).val → 0 < orient2D (c (a + finNat (k + 3) t)) (c (a + finNat (k + 3) t + 1)) v) ∨
      (∀ t : ℕ, t < (a - b).val → 0 < orient2D (c (b + finNat (k + 3) t)) (c (b + finNat (k + 3) t + 1)) v) := by
    by_contra hboth
    push Not at hboth
    obtain ⟨⟨t1, ht1, hf1⟩, ⟨t2, ht2, hf2⟩⟩ := hboth
    have hf1_lt : orient2D (c (a + finNat (k + 3) t1)) (c (a + finNat (k + 3) t1 + 1)) v < 0 :=
      lt_of_le_of_ne hf1 (hedge_ne0 _)
    have hf2_lt : orient2D (c (b + finNat (k + 3) t2)) (c (b + finNat (k + 3) t2 + 1)) v < 0 :=
      lt_of_le_of_ne hf2 (hedge_ne0 _)
    let m1 := a + finNat (k + 3) t1
    let m2 := b + finNat (k + 3) t2
    have hm1_val : (m1 - a).val = t1 := by
      have : finNat (k + 3) t1 = (⟨t1, lt_trans ht1 (b - a).isLt⟩ : Fin (k + 3)) := by
        ext; exact Nat.mod_eq_of_lt (lt_trans ht1 (b - a).isLt)
      change (a + finNat (k + 3) t1 - a).val = t1
      rw [add_sub_cancel_left, this]
    have hm2_val : (m2 - b).val = t2 := by
      have : finNat (k + 3) t2 = (⟨t2, lt_trans ht2 (a - b).isLt⟩ : Fin (k + 3)) := by
        ext; exact Nat.mod_eq_of_lt (lt_trans ht2 (a - b).isLt)
      change (b + finNat (k + 3) t2 - b).val = t2
      rw [add_sub_cancel_left, this]
    have hm1_b : (b - m1).val = (b - a).val - t1 := by
      rcases Nat.eq_zero_or_pos t1 with rfl | ht1_pos
      · have : m1 = a := by dsimp [m1]; rw [finNat_zero, add_zero]
        rw [this]; simp
      · have ht1' : 0 < (m1 - a).val := by rw [hm1_val]; exact ht1_pos
        have hm1_lt : (m1 - a).val < (b - a).val := by rw [hm1_val]; exact ht1
        have hsp := (fin_sub_split_lt ht1' hm1_lt).1
        omega
    have hm2_a : (a - m2).val = (a - b).val - t2 := by
      rcases Nat.eq_zero_or_pos t2 with rfl | ht2_pos
      · have : m2 = b := by dsimp [m2]; rw [finNat_zero, add_zero]
        rw [this]; simp
      · have ht2' : 0 < (m2 - b).val := by rw [hm2_val]; exact ht2_pos
        have hm2_lt : (m2 - b).val < (a - b).val := by rw [hm2_val]; exact ht2
        have hsp := (fin_sub_split_lt ht2' hm2_lt).1
        omega
    have hm12_sum : (b - m1).val + (m2 - b).val < k + 3 := by
      have hN := fin_sub_add_compl hab; omega
    have hm21_sum : (a - m2).val + (m1 - a).val < k + 3 := by
      have hN := fin_sub_add_compl hab; omega
    have hm21_val : (m2 - m1).val = (b - m1).val + (m2 - b).val := by
      have heq : m2 - m1 = (b - m1) + (m2 - b) := by abel
      have hval := congrArg Fin.val heq
      rw [Fin.val_add, Nat.mod_eq_of_lt hm12_sum] at hval; exact hval
    have hm12_val : (m1 - m2).val = (a - m2).val + (m1 - a).val := by
      have heq : m1 - m2 = (a - m2) + (m1 - a) := by abel
      have hval := congrArg Fin.val heq
      rw [Fin.val_add, Nat.mod_eq_of_lt hm21_sum] at hval; exact hval
    rcases facing_edges_contiguous c hc v m1 m2 hf1_lt hf2_lt with h_m12 | h_m21
    · have hb_le : (b - m1).val ≤ (m2 - m1).val := by rw [hm21_val]; omega
      have hb1_le : (b - 1 - m1).val ≤ (m2 - m1).val := by
        have hb_pos : 0 < (b - m1).val := by omega
        have heq : b - 1 - m1 = (b - m1) - 1 := by abel
        rw [heq]
        exact le_trans (le_of_lt (fin_sub_one_val_lt (by omega : 1 < k + 3) hb_pos)) hb_le
      have hbm : orient2D (c (b - 1)) (c b) v < 0 := by
        simpa [sub_add_cancel] using h_m12 (b - 1) hb1_le
      have hbp : orient2D (c b) (c (b + 1)) v < 0 := h_m12 b hb_le
      rcases hnb with h | h <;> linarith
    · have ha_le : (a - m2).val ≤ (m1 - m2).val := by rw [hm12_val]; omega
      have ha1_le : (a - 1 - m2).val ≤ (m1 - m2).val := by
        have ha_pos : 0 < (a - m2).val := by omega
        have heq : a - 1 - m2 = (a - m2) - 1 := by abel
        rw [heq]
        exact le_trans (le_of_lt (fin_sub_one_val_lt (by omega : 1 < k + 3) ha_pos)) ha_le
      have ham : orient2D (c (a - 1)) (c a) v < 0 := by
        simpa [sub_add_cancel] using h_m21 (a - 1) ha1_le
      have hap : orient2D (c a) (c (a + 1)) v < 0 := h_m21 a ha_le
      rcases hna with h | h <;> linarith
  have hcross_both :
      ∀ (u w : Fin (k + 3)), u ≠ w → OnSameSide v q (c u) (c w) →
      (∀ t : ℕ, t < (w - u).val → 0 < orient2D (c (u + finNat (k + 3) t)) (c (u + finNat (k + 3) t + 1)) v) →
      (∀ t : ℕ, t ≤ (w - u).val → OnSameSide v q (c u) (c (u + finNat (k + 3) t))) ∨
      ((∀ m : Fin (k + 3), 0 < orient2D (c m) (c (m + 1)) v) ∧
       (∀ s : ℕ, s ≤ (u - w).val → OnSameSide v q (c u) (c (w + finNat (k + 3) s)))) := by
    intro u w huw hss_uw hall_nf
    by_cases hsame : ∀ t : ℕ, t ≤ (w - u).val → OnSameSide v q (c u) (c (u + finNat (k + 3) t))
    · exact Or.inl hsame
    · right
      push Not at hsame
      obtain ⟨t_star, ht_star_le, ht_star_opp⟩ := hsame
      have ht_star_pos : 0 < t_star := by
        by_contra h0; have : t_star = 0 := by omega
        subst this; rw [finNat_zero, add_zero] at ht_star_opp
        unfold OnSameSide at ht_star_opp
        exact ht_star_opp (mul_self_pos.mpr (hvq u))
      have ht_star_lt : t_star < (w - u).val := by
        rcases eq_or_lt_of_le ht_star_le with heq | hlt
        · subst heq
          have : u + finNat (k + 3) (w - u).val = w := by
            have : finNat (k + 3) (w - u).val = w - u := by ext; exact Nat.mod_eq_of_lt (w - u).isLt
            rw [this, add_sub_cancel]
          rw [this] at ht_star_opp; exact absurd hss_uw ht_star_opp
        · exact hlt
      let S1 := (Finset.range (t_star + 1)).filter
        (fun t => ¬ OnSameSide v q (c u) (c (u + finNat (k + 3) t)))
      have hS1_ne : S1.Nonempty := ⟨t_star, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), ht_star_opp⟩⟩
      let t0 := S1.min' hS1_ne
      have ht0_mem := Finset.mem_filter.mp (Finset.min'_mem S1 hS1_ne)
      have ht0_le : t0 ≤ t_star := Nat.lt_succ_iff.mp (Finset.mem_range.mp ht0_mem.1)
      have ht0_pos : 0 < t0 := by
        by_contra h0; have : t0 = 0 := by omega
        have ht0_opp := ht0_mem.2
        change ¬ OnSameSide v q (c u) (c (u + finNat (k + 3) t0)) at ht0_opp
        rw [this, finNat_zero, add_zero] at ht0_opp
        unfold OnSameSide at ht0_opp
        exact ht0_opp (mul_self_pos.mpr (hvq u))
      have ht0_prev : OnSameSide v q (c u) (c (u + finNat (k + 3) (t0 - 1))) := by
        by_contra hnot
        have hmem : t0 - 1 ∈ S1 := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hnot⟩
        have hmin := Finset.min'_le S1 (t0 - 1) hmem
        omega
      let S2 := (Finset.Ioc t_star (w - u).val).filter
        (fun t => OnSameSide v q (c u) (c (u + finNat (k + 3) t)))
      have hS2_ne : S2.Nonempty := by
        refine ⟨(w - u).val, Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨ht_star_lt, le_rfl⟩, ?_⟩⟩
        have : finNat (k + 3) (w - u).val = w - u := by ext; exact Nat.mod_eq_of_lt (w - u).isLt
        rw [this, add_sub_cancel]; exact hss_uw
      let t1 := S2.min' hS2_ne
      have ht1_mem := Finset.mem_filter.mp (Finset.min'_mem S2 hS2_ne)
      have ht1_bounds := Finset.mem_Ioc.mp ht1_mem.1
      have ht1_prev : ¬ OnSameSide v q (c u) (c (u + finNat (k + 3) (t1 - 1))) := by
        rcases eq_or_lt_of_le (Nat.succ_le_of_lt ht1_bounds.1) with heq | hlt
        · have heq' : t1 - 1 = t_star := by omega
          rw [heq']; exact ht_star_opp
        · intro hok
          have hmem : t1 - 1 ∈ S2 := Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨by omega, by omega⟩, hok⟩
          have hmin := Finset.min'_le S2 (t1 - 1) hmem
          omega
      let m_leave := u + finNat (k + 3) (t0 - 1)
      let m_enter := u + finNat (k + 3) (t1 - 1)
      have hm_leave_succ : u + finNat (k + 3) t0 = m_leave + 1 := by
        have : t0 = (t0 - 1) + 1 := by omega
        rw [this, finNat_succ, ← add_assoc]
      have hm_enter_succ : u + finNat (k + 3) t1 = m_enter + 1 := by
        have : t1 = (t1 - 1) + 1 := by omega
        rw [this, finNat_succ, ← add_assoc]
      have hnf_leave : 0 < orient2D (c m_leave) (c (m_leave + 1)) v := hall_nf (t0 - 1) (by omega)
      have hnf_enter : 0 < orient2D (c m_enter) (c (m_enter + 1)) v := hall_nf (t1 - 1) (by omega)
      have hall_all_nf : ∀ m : Fin (k + 3), 0 < orient2D (c m) (c (m + 1)) v := by
        rcases lt_or_gt_of_ne (hvq u) with hu_neg | hu_pos
        · have hl0 : orient2D v q (c m_leave) < 0 := by
            have h := ht0_prev; dsimp [OnSameSide, m_leave] at h ⊢; nlinarith
          have hl1 : 0 < orient2D v q (c (m_leave + 1)) := by
            have hle := not_lt.mp ht0_mem.2
            unfold OnSameSide at hle
            rw [hm_leave_succ] at hle
            have hne := hvq (m_leave + 1)
            have hlt : orient2D v q (c u) * orient2D v q (c (m_leave + 1)) < 0 :=
              lt_of_le_of_ne hle (mul_ne_zero (ne_of_lt hu_neg) hne)
            nlinarith
          have he0 : 0 < orient2D v q (c m_enter) := by
            have hle := not_lt.mp ht1_prev
            unfold OnSameSide at hle
            have hne := hvq m_enter
            have hlt : orient2D v q (c u) * orient2D v q (c m_enter) < 0 :=
              lt_of_le_of_ne hle (mul_ne_zero (ne_of_lt hu_neg) hne)
            dsimp [m_enter]; nlinarith
          have he1 : orient2D v q (c (m_enter + 1)) < 0 := by
            have h := ht1_mem.2; dsimp [OnSameSide] at h; rw [hm_enter_succ] at h; nlinarith
          exact convex_crossing_both_sides_in_conv c hc v q hv_noncol m_enter m_leave
            hnf_enter hnf_leave he0 he1 hl0 hl1
        · have hl0 : 0 < orient2D v q (c m_leave) := by
            have h := ht0_prev; dsimp [OnSameSide, m_leave] at h ⊢; nlinarith
          have hl1 : orient2D v q (c (m_leave + 1)) < 0 := by
            have hle := not_lt.mp ht0_mem.2
            unfold OnSameSide at hle
            rw [hm_leave_succ] at hle
            have hne := hvq (m_leave + 1)
            have hlt : orient2D v q (c u) * orient2D v q (c (m_leave + 1)) < 0 :=
              lt_of_le_of_ne hle (mul_ne_zero (ne_of_gt hu_pos) hne)
            nlinarith
          have he0 : orient2D v q (c m_enter) < 0 := by
            have hle := not_lt.mp ht1_prev
            unfold OnSameSide at hle
            have hne := hvq m_enter
            have hlt : orient2D v q (c u) * orient2D v q (c m_enter) < 0 :=
              lt_of_le_of_ne hle (mul_ne_zero (ne_of_gt hu_pos) hne)
            dsimp [m_enter]; nlinarith
          have he1 : 0 < orient2D v q (c (m_enter + 1)) := by
            have h := ht1_mem.2; dsimp [OnSameSide] at h; rw [hm_enter_succ] at h; nlinarith
          exact convex_crossing_both_sides_in_conv c hc v q hv_noncol m_leave m_enter
            hnf_leave hnf_enter hl0 hl1 he0 he1
      refine ⟨hall_all_nf, fun s hs => ?_⟩
      by_contra hnot
      have hs_pos : 0 < s := by
        by_contra h0; have : s = 0 := by omega
        subst this; simp [finNat_zero] at hnot; exact hnot hss_uw
      have hs_lt : s < (u - w).val := by
        rcases eq_or_lt_of_le hs with heq | hlt
        · subst heq
          have : w + finNat (k + 3) (u - w).val = u := by
            have : finNat (k + 3) (u - w).val = u - w := by ext; exact Nat.mod_eq_of_lt (u - w).isLt
            rw [this, add_sub_cancel]
          rw [this] at hnot
          unfold OnSameSide at hnot
          exact absurd (mul_self_pos.mpr (hvq u)) hnot
        · exact hlt
      let i1 := u + finNat (k + 3) t_star
      let i3 := w + finNat (k + 3) s
      have h01 : 0 < (i1 - u).val := by
        have : finNat (k + 3) t_star = ⟨t_star, lt_trans ht_star_lt (w - u).isLt⟩ := by
          ext; exact Nat.mod_eq_of_lt (lt_trans ht_star_lt (w - u).isLt)
        change 0 < (u + finNat (k + 3) t_star - u).val
        rw [add_sub_cancel_left, this]; exact ht_star_pos
      have h12 : (i1 - u).val < (w - u).val := by
        have : finNat (k + 3) t_star = ⟨t_star, lt_trans ht_star_lt (w - u).isLt⟩ := by
          ext; exact Nat.mod_eq_of_lt (lt_trans ht_star_lt (w - u).isLt)
        change (u + finNat (k + 3) t_star - u).val < (w - u).val
        rw [add_sub_cancel_left, this]; exact ht_star_lt
      have h23 : (w - u).val < (i3 - u).val := by
        have hN := fin_sub_add_compl huw
        have : finNat (k + 3) s = ⟨s, lt_trans hs_lt (u - w).isLt⟩ := by
          ext; exact Nat.mod_eq_of_lt (lt_trans hs_lt (u - w).isLt)
        have hi3w : (i3 - w).val = s := by
          change (w + finNat (k + 3) s - w).val = s
          rw [add_sub_cancel_left, this]
        have hi3_eq : i3 - u = (w - u) + (i3 - w) := by abel
        have hval := congrArg Fin.val hi3_eq
        rw [Fin.val_add, hi3w, Nat.mod_eq_of_lt (by omega)] at hval
        omega
      have ⟨ho1, ho2, ho3, ho4⟩ := ccwCycle_fourgon_orient cyc u i1 w i3 h01 h12 h23
      have halt := convex_fourgon_no_alternating_line (c u) (c i1) (c w) (c i3) v q ho1 ho2 ho3 ho4
      rcases lt_or_gt_of_ne (hvq u) with hu_neg | hu_pos
      · have hw_neg : orient2D v q (c w) < 0 := by unfold OnSameSide at hss_uw; nlinarith
        have hi1_pos : 0 < orient2D v q (c i1) := by
          unfold OnSameSide at ht_star_opp
          have hle := not_lt.mp ht_star_opp
          rcases lt_or_gt_of_ne (hvq i1) with h1 | h1
          · exact False.elim (by nlinarith [mul_pos_of_neg_of_neg hu_neg h1])
          · exact h1
        have hi3_pos : 0 < orient2D v q (c i3) := by
          unfold OnSameSide at hnot
          have hle := not_lt.mp hnot
          rcases lt_or_gt_of_ne (hvq i3) with h3 | h3
          · exact False.elim (by nlinarith [mul_pos_of_neg_of_neg hu_neg h3])
          · exact h3
        exact halt.2 ⟨hu_neg, hi1_pos, hw_neg, hi3_pos⟩
      · have hw_pos : 0 < orient2D v q (c w) := by unfold OnSameSide at hss_uw; nlinarith
        have hi1_neg : orient2D v q (c i1) < 0 := by
          unfold OnSameSide at ht_star_opp
          rcases lt_or_gt_of_ne (hvq i1) with h1 | h1
          · exact h1
          · exact False.elim (ht_star_opp (mul_pos hu_pos h1))
        have hi3_neg : orient2D v q (c i3) < 0 := by
          unfold OnSameSide at hnot
          rcases lt_or_gt_of_ne (hvq i3) with h3 | h3
          · exact h3
          · exact False.elim (hnot (mul_pos hu_pos h3))
        exact halt.1 ⟨hu_pos, hi1_neg, hw_pos, hi3_neg⟩
  rcases hf_arc with h1 | h2
  · rcases hcross_both a b hab hss h1 with h_ok | ⟨hall_nf, h_opp⟩
    · exact Or.inl ⟨h1, h_ok⟩
    · exact Or.inr ⟨fun t _ => hall_nf _, h_opp⟩
  · rcases hcross_both b a hab.symm hss.symm h2 with h_ok | ⟨hall_nf, h_opp⟩
    · refine Or.inr ⟨h2, fun t ht => ?_⟩
      exact hss.trans (h_ok t ht)
    · exact Or.inl ⟨fun t _ => hall_nf _, fun t ht => hss.trans (h_opp t ht)⟩

lemma farChain_arc_angle_monotone {n k : ℕ} {S : Fin n → ℝ × ℝ} {C : Finset (Fin n)}
    (cyc : CCWCycle S C k) (v q : ℝ × ℝ) (u w : Fin (k + 3))
    (hnf : ∀ t : ℕ, t < (w - u).val →
      0 < orient2D (S (cyc.toFun (u + finNat (k + 3) t)))
                   (S (cyc.toFun (u + finNat (k + 3) t + 1))) v)
    (hss : ∀ t : ℕ, t ≤ (w - u).val →
      OnSameSide v q (S (cyc.toFun u)) (S (cyc.toFun (u + finNat (k + 3) t)))) :
    (0 < orient2D v q (S (cyc.toFun u)) →
      ∀ s t : ℕ, s < t → t ≤ (w - u).val →
        AngleLt v q (S (cyc.toFun (u + finNat (k + 3) s)))
                    (S (cyc.toFun (u + finNat (k + 3) t)))) ∧
    (orient2D v q (S (cyc.toFun u)) < 0 →
      ∀ s t : ℕ, s < t → t ≤ (w - u).val →
        AngleLt v q (S (cyc.toFun (u + finNat (k + 3) t)))
                    (S (cyc.toFun (u + finNat (k + 3) s)))) := by
  have hstep : ∀ m : ℕ, m < (w - u).val →
      (0 < orient2D v q (S (cyc.toFun u)) →
        AngleLt v q (S (cyc.toFun (u + finNat (k + 3) m)))
                    (S (cyc.toFun (u + finNat (k + 3) (m + 1))))) ∧
      (orient2D v q (S (cyc.toFun u)) < 0 →
        AngleLt v q (S (cyc.toFun (u + finNat (k + 3) (m + 1))))
                    (S (cyc.toFun (u + finNat (k + 3) m)))) := by
    intro m hm
    have hs1 := hss m (Nat.le_of_lt hm)
    have hs2 := hss (m + 1) hm
    have hss_step : OnSameSide v q (S (cyc.toFun (u + finNat (k + 3) m)))
                                   (S (cyc.toFun (u + finNat (k + 3) (m + 1)))) :=
      hs1.symm.trans hs2
    have hnf_m := hnf m hm
    have hv_ccw : 0 < orient2D v (S (cyc.toFun (u + finNat (k + 3) m)))
                                 (S (cyc.toFun (u + finNat (k + 3) (m + 1)))) := by
      have hm_eq : u + finNat (k + 3) (m + 1) = u + finNat (k + 3) m + 1 := by
        rw [finNat_succ, ← add_assoc]
      rw [hm_eq, ← orient2D_cycle]
      exact hnf_m
    constructor
    · intro hu_pos
      have hm_pos : 0 < orient2D v q (S (cyc.toFun (u + finNat (k + 3) m))) := by
        unfold OnSameSide at hs1; nlinarith
      have hm1_pos : 0 < orient2D v q (S (cyc.toFun (u + finNat (k + 3) (m + 1)))) := by
        unfold OnSameSide at hs2; nlinarith
      exact (angleLt_iff_pos_of_pos hm_pos hm1_pos).mpr hv_ccw
    · intro hu_neg
      have hm_neg : orient2D v q (S (cyc.toFun (u + finNat (k + 3) m))) < 0 := by
        unfold OnSameSide at hs1; nlinarith
      have hm1_neg : orient2D v q (S (cyc.toFun (u + finNat (k + 3) (m + 1)))) < 0 := by
        unfold OnSameSide at hs2; nlinarith
      refine (angleLt_iff_neg_of_neg hm1_neg hm_neg).mpr ?_
      rw [orient2D_swap23]; linarith
  constructor
  · intro hu_pos s t hst htw
    induction t with
    | zero => omega
    | succ t ih =>
      rcases eq_or_lt_of_le (Nat.lt_succ_iff.mp hst) with rfl | hlt
      · exact (hstep s (Nat.lt_of_succ_le htw)).1 hu_pos
      · exact (ih hlt (Nat.le_of_lt htw)).trans ((hstep t (Nat.lt_of_succ_le htw)).1 hu_pos)
  · intro hu_neg s t hst htw
    induction t with
    | zero => omega
    | succ t ih =>
      rcases eq_or_lt_of_le (Nat.lt_succ_iff.mp hst) with rfl | hlt
      · exact (hstep s (Nat.lt_of_succ_le htw)).2 hu_neg
      · exact ((hstep t (Nat.lt_of_succ_le htw)).2 hu_neg).trans (ih hlt (Nat.le_of_lt htw))

private lemma mem_convexHull_image_weights {n : ℕ} (S : Fin n → ℝ × ℝ)
    (hinj : Function.Injective S) (R : Finset (Fin n)) {z : ℝ × ℝ}
    (hz : z ∈ convexHull ℝ (R.image S : Set (ℝ × ℝ))) :
    ∃ μ : R → ℝ, (∀ r : R, 0 ≤ μ r) ∧ (∑ r : R, μ r = 1) ∧ ∑ r : R, μ r • S r.1 = z := by
  rw [Finset.convexHull_eq] at hz
  rcases hz with ⟨μ, hμ_nn, hμ_sum, hμ_eq⟩
  refine ⟨fun r => μ (S r.1), fun r => hμ_nn (S r.1) (Finset.mem_image_of_mem S r.2), ?_, ?_⟩
  · calc ∑ r : R, μ (S r.1)
        = ∑ r ∈ R, μ (S r) := Finset.sum_coe_sort R (fun r => μ (S r))
      _ = ∑ y ∈ R.image S, μ y := (Finset.sum_image (fun a _ b _ h => hinj h)).symm
      _ = 1 := hμ_sum
  · rw [Finset.centerMass, hμ_sum, inv_one, one_smul] at hμ_eq
    calc ∑ r : R, μ (S r.1) • S r.1
        = ∑ r ∈ R, μ (S r) • S r := Finset.sum_coe_sort R (fun r => μ (S r) • S r)
      _ = ∑ y ∈ R.image S, μ y • y := (Finset.sum_image (f := fun y => μ y • y) (fun a _ b _ h => hinj h)).symm
      _ = z := hμ_eq

lemma extreme_not_on_ray_outside {n : ℕ} (S : Fin n → ℝ × ℝ) (hinj : Function.Injective S)
    {B : Finset (Fin n)} (hB_conv : IsConvexPos S B)
    {a c : Fin n} (ha : a ∈ B) (hc : c ∈ B) (hac : a ≠ c)
    {z : ℝ × ℝ} (hz : z ∈ convexHull ℝ (B.image S : Set (ℝ × ℝ)))
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    (heq : S a = t • z + (1 - t) • S c) : False := by
  obtain ⟨ν, hν_nn, hν_sum, hν_eq⟩ := mem_convexHull_image_weights S hinj B hz
  have ha_weight_le : t * ν ⟨a, ha⟩ ≤ t := by
    have h1 : ν ⟨a, ha⟩ ≤ 1 := by
      have hle : ν ⟨a, ha⟩ ≤ ∑ i : B, ν i :=
        Finset.single_le_sum (fun i _ => hν_nn i) (Finset.mem_univ _)
      linarith
    nlinarith
  have hdenom_pos : 0 < 1 - t * ν ⟨a, ha⟩ := by linarith
  have hdenom_ne : 1 - t * ν ⟨a, ha⟩ ≠ 0 := ne_of_gt hdenom_pos
  let μ : B.erase a → ℝ := fun i =>
    (t * ν ⟨i.1, Finset.mem_of_mem_erase i.2⟩ + if i.1 = c then (1 - t) else 0) /
    (1 - t * ν ⟨a, ha⟩)
  have hμ_nn : ∀ i : B.erase a, 0 ≤ μ i := by
    intro i
    dsimp [μ]
    refine div_nonneg ?_ (le_of_lt hdenom_pos)
    refine add_nonneg (mul_nonneg (le_of_lt ht0) (hν_nn _)) ?_
    split_ifs <;> linarith
  have hν_split : ∑ i : B, ν i = ν ⟨a, ha⟩ + ∑ i : B.erase a, ν ⟨i.1, Finset.mem_of_mem_erase i.2⟩ := by
    have h1 := Finset.add_sum_erase (Finset.univ : Finset B) ν (Finset.mem_univ ⟨a, ha⟩)
    rw [← h1]
    congr 1
    refine (Finset.sum_nbij (fun i : {x // x ∈ B.erase a} => (⟨i.1, Finset.mem_of_mem_erase i.2⟩ : B))
      ?_ ?_ ?_ ?_).symm
    · intro i _; exact Finset.mem_erase.mpr ⟨fun he => (Finset.mem_erase.mp i.2).1 (congrArg Subtype.val he), Finset.mem_univ _⟩
    · rintro ⟨x, _⟩ _ ⟨y, _⟩ _ hxy; exact Subtype.ext (by simpa using congrArg Subtype.val hxy)
    · intro b hb
      have hba : b.1 ≠ a := fun h => (Finset.mem_erase.mp hb).1 (Subtype.ext h)
      exact ⟨⟨b.1, Finset.mem_erase.mpr ⟨hba, b.2⟩⟩, Finset.mem_univ _, rfl⟩
    · intro _ _; rfl
  have hν_vec_split : ∑ i : B, ν i • S i.1 =
      ν ⟨a, ha⟩ • S a + ∑ i : B.erase a, ν ⟨i.1, Finset.mem_of_mem_erase i.2⟩ • S i.1 := by
    have h1 := Finset.add_sum_erase (Finset.univ : Finset B) (fun i => ν i • S i.1) (Finset.mem_univ ⟨a, ha⟩)
    rw [← h1]
    congr 1
    refine (Finset.sum_nbij (fun i : {x // x ∈ B.erase a} => (⟨i.1, Finset.mem_of_mem_erase i.2⟩ : B))
      ?_ ?_ ?_ ?_).symm
    · intro i _; exact Finset.mem_erase.mpr ⟨fun he => (Finset.mem_erase.mp i.2).1 (congrArg Subtype.val he), Finset.mem_univ _⟩
    · rintro ⟨x, _⟩ _ ⟨y, _⟩ _ hxy; exact Subtype.ext (by simpa using congrArg Subtype.val hxy)
    · intro b hb
      have hba : b.1 ≠ a := fun h => (Finset.mem_erase.mp hb).1 (Subtype.ext h)
      exact ⟨⟨b.1, Finset.mem_erase.mpr ⟨hba, b.2⟩⟩, Finset.mem_univ _, rfl⟩
    · intro _ _; rfl
  have hc_er : c ∈ B.erase a := Finset.mem_erase.mpr ⟨hac.symm, hc⟩
  have hif_sum : ∑ i : B.erase a, (if i.1 = c then (1 - t) else 0) = 1 - t := by
    have : ∀ i : B.erase a, (if i.1 = c then (1 - t) else 0) =
        (if i = ⟨c, hc_er⟩ then (1 - t) else 0) := by
      intro i; by_cases h : i.1 = c <;> simp [h, Subtype.ext_iff]
    simp_rw [this]; simp
  have hif_vec : ∑ i : B.erase a, (if i.1 = c then (1 - t) else 0) • S i.1 = (1 - t) • S c := by
    have : ∀ i : B.erase a, (if i.1 = c then (1 - t) else 0) • S i.1 =
        (if i = ⟨c, hc_er⟩ then (1 - t) • S c else 0) := by
      intro i
      by_cases h : i.1 = c
      · have hi : i = ⟨c, hc_er⟩ := Subtype.ext h
        simp [hi]
      · have hi : i ≠ ⟨c, hc_er⟩ := fun h' => h (congrArg Subtype.val h')
        simp [h, hi]
    simp_rw [this]; simp
  have hμ_sum : ∑ i : B.erase a, μ i = 1 := by
    change ∑ i : B.erase a, (t * ν ⟨i.1, Finset.mem_of_mem_erase i.2⟩ + if i.1 = c then (1 - t) else 0) /
        (1 - t * ν ⟨a, ha⟩) = 1
    rw [← Finset.sum_div, Finset.sum_add_distrib, ← Finset.mul_sum, hif_sum]
    have hs : ∑ i : B.erase a, ν ⟨i.1, Finset.mem_of_mem_erase i.2⟩ = 1 - ν ⟨a, ha⟩ := by linarith
    rw [hs]
    field_simp [hdenom_ne]; ring
  have hμ_vec : Finset.univ.centerMass μ (fun i : B.erase a => S i.1) = S a := by
    rw [Finset.centerMass_eq_of_sum_1 _ _ hμ_sum]
    have h1 : ∑ i : B.erase a, μ i • S i.1 =
        (1 - t * ν ⟨a, ha⟩)⁻¹ •
          (t • (∑ i : B.erase a, ν ⟨i.1, Finset.mem_of_mem_erase i.2⟩ • S i.1) +
           ∑ i : B.erase a, (if i.1 = c then (1 - t) else 0) • S i.1) := by
      rw [smul_add, smul_smul, Finset.smul_sum, Finset.smul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      dsimp [μ]
      ext <;> dsimp <;> ring
    rw [h1, hif_vec]
    have hz_eq : z = ν ⟨a, ha⟩ • S a + ∑ i : B.erase a, ν ⟨i.1, Finset.mem_of_mem_erase i.2⟩ • S i.1 := by
      rw [← hν_eq, hν_vec_split]
    have hsub_eq : (1 - t * ν ⟨a, ha⟩) • S a =
        t • (∑ i : B.erase a, ν ⟨i.1, Finset.mem_of_mem_erase i.2⟩ • S i.1) + (1 - t) • S c := by
      have h' : S a = t • (ν ⟨a, ha⟩ • S a + ∑ i : B.erase a, ν ⟨i.1, Finset.mem_of_mem_erase i.2⟩ • S i.1) + (1 - t) • S c := by
        rw [← hz_eq]; exact heq
      ext <;> dsimp
      · have h1 := congrArg Prod.fst h'; dsimp at h1 ⊢; linarith
      · have h2 := congrArg Prod.snd h'; dsimp at h2 ⊢; linarith
    rw [← hsub_eq, inv_smul_smul₀ hdenom_ne]
  apply hB_conv a ha
  rw [← hμ_vec]
  refine Finset.centerMass_mem_convexHull _ (fun i _ => hμ_nn i) (by rw [hμ_sum]; exact zero_lt_one)
    (fun i _ => Finset.mem_image.mpr ⟨i.1, i.2, rfl⟩)

lemma convexHull_subset_arc_of_line {n k : ℕ} (S : Fin n → ℝ × ℝ) (hinj : Function.Injective S)
    {B : Finset (Fin n)} (hB_conv : IsConvexPos S B) (cyc : CCWCycle S B k)
    (ia ic : Fin (k + 3)) (h_iac : ia ≠ ic) (hS_ac : S (cyc.toFun ia) ≠ S (cyc.toFun ic))
    {z : ℝ × ℝ} (hz : z ∈ convexHull ℝ (B.image S : Set (ℝ × ℝ)))
    (hz_side : orient2D (S (cyc.toFun ia)) (S (cyc.toFun ic)) z < 0) :
    let Arc := Finset.univ.filter (fun x => ∃ m : Fin (k + 3), cyc.toFun m = x ∧ (m - ia).val ≤ (ic - ia).val)
    z ∈ convexHull ℝ (Arc.image S : Set (ℝ × ℝ)) := by
  intro Arc
  let a := cyc.toFun ia
  let c := cyc.toFun ic
  have haB : a ∈ B := ccwCycle_mem cyc ia
  have hcB : c ∈ B := ccwCycle_mem cyc ic
  have hac : a ≠ c := fun h => h_iac (cyc.inj h)
  have haArc : a ∈ Arc := Finset.mem_filter.mpr ⟨Finset.mem_univ _, ia, rfl, by simp⟩
  have hcArc : c ∈ Arc := Finset.mem_filter.mpr ⟨Finset.mem_univ _, ic, rfl, le_rfl⟩
  have hrest_pos : ∀ x ∈ B, x ∉ Arc → 0 < orient2D (S a) (S c) (S x) := by
    intro x hxB hxArc
    obtain ⟨ix, rfl⟩ := ccwCycle_exists_index cyc hxB
    have hgt : (ic - ia).val < (ix - ia).val := by
      by_contra hle; exact hxArc (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ix, rfl, not_lt.mp hle⟩)
    have hic_pos : 0 < (ic - ia).val := by
      by_contra h0
      have h0' : (ic - ia).val = 0 := by omega
      exact h_iac (sub_eq_zero.mp (Fin.ext h0')).symm
    exact ccwCycle_ccw3 cyc hic_pos hgt
  obtain ⟨μ, hμ_nn, hμ_sum, hμ_eq⟩ := mem_convexHull_image_weights S hinj B hz
  let s1 : ℝ := ∑ i : B, if i.1 ∈ Arc then μ i else 0
  let s2 : ℝ := ∑ i : B, if i.1 ∉ Arc then μ i else 0
  let p1 : ℝ × ℝ := ∑ i : B, if i.1 ∈ Arc then μ i • S i.1 else 0
  let p2 : ℝ × ℝ := ∑ i : B, if i.1 ∉ Arc then μ i • S i.1 else 0
  have hs12 : s1 + s2 = 1 := by
    dsimp [s1, s2]; rw [← Finset.sum_add_distrib]
    trans ∑ i : B, μ i
    · exact Finset.sum_congr rfl (fun i _ => by by_cases h : i.1 ∈ Arc <;> simp [h])
    · exact hμ_sum
  have hp12 : p1 + p2 = z := by
    dsimp [p1, p2]; rw [← Finset.sum_add_distrib]
    trans ∑ i : B, μ i • S i.1
    · exact Finset.sum_congr rfl (fun i _ => by by_cases h : i.1 ∈ Arc <;> simp [h])
    · exact hμ_eq
  have hs1_nn : 0 ≤ s1 := Finset.sum_nonneg (fun i _ => by by_cases h : i.1 ∈ Arc <;> simp [h, hμ_nn i])
  have hs2_nn : 0 ≤ s2 := Finset.sum_nonneg (fun i _ => by by_cases h : i.1 ∈ Arc <;> simp [h, hμ_nn i])
  have hor_sum1 : ∀ (f : B → ℝ) (v : B → ℝ × ℝ), ∑ i : B, f i = 1 →
      orient2D (S a) (S c) (∑ i : B, f i • v i) = ∑ i : B, f i * orient2D (S a) (S c) (v i) := by
    intro f v hs
    have hid : ∀ P : ℝ × ℝ, orient2D (S a) (S c) P =
        ((S c).1 - (S a).1) * (P.2 - (S a).2) - ((S c).2 - (S a).2) * (P.1 - (S a).1) := fun _ => rfl
    have h_p : (∑ i : B, f i • v i).1 - (S a).1 = ∑ i : B, f i * ((v i).1 - (S a).1) := by
      simp only [Prod.fst_sum, Prod.smul_fst, smul_eq_mul, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hs]
      ring
    have h_q : (∑ i : B, f i • v i).2 - (S a).2 = ∑ i : B, f i * ((v i).2 - (S a).2) := by
      simp only [Prod.snd_sum, Prod.smul_snd, smul_eq_mul, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hs]
      ring
    rw [hid, h_p, h_q, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_); unfold orient2D; ring
  have harc_le : ∀ x ∈ Arc, orient2D (S a) (S c) (S x) ≤ 0 := by
    intro x hx
    rcases Finset.mem_filter.mp hx with ⟨_, m, rfl, hm⟩
    by_cases hma : m = ia
    · rw [hma]; change orient2D (S a) (S c) (S a) ≤ 0; rw [orient2D_self_outer]
    · by_cases hmc : m = ic
      · rw [hmc]; change orient2D (S a) (S c) (S c) ≤ 0; rw [orient2D_self_right]
      · have h1 : 0 < (m - ia).val := Nat.pos_of_ne_zero (fun h => hma (sub_eq_zero.mp (Fin.ext h)))
        have h2 : (m - ia).val < (ic - ia).val := lt_of_le_of_ne hm (fun h => hmc (by
          have hsub : m - ia = ic - ia := Fin.ext h
          have := congrArg (· + ia) hsub
          simpa [sub_add_cancel] using this))
        have hccw := ccwCycle_ccw3 cyc h1 h2
        rw [orient2D_swap23]; change -orient2D (S (cyc.toFun ia)) (S (cyc.toFun m)) (S (cyc.toFun ic)) ≤ 0
        linarith
  have hs1_pos : 0 < s1 := by
    by_contra hle
    have hs1_0 : s1 = 0 := le_antisymm (not_lt.mp hle) hs1_nn
    have hs2_1 : s2 = 1 := by linarith
    have hp1_0 : p1 = 0 := Finset.sum_eq_zero (fun i _ => by
      by_cases h : i.1 ∈ Arc
      · have hi_0 : μ i = 0 := le_antisymm (by
          have := Finset.single_le_sum (fun j _ => show 0 ≤ if j.1 ∈ Arc then μ j else 0
            by split_ifs <;> [exact hμ_nn j; exact le_rfl]) (Finset.mem_univ i)
          simp only [h, ↓reduceIte] at this; linarith) (hμ_nn i)
        simp [h, hi_0]
      · simp [h])
    have hz_eq : z = p2 := by rw [← hp12, hp1_0, zero_add]
    have hμ_notArc : ∀ i : B, i.1 ∈ Arc → μ i = 0 := fun i hi => by
      have := Finset.single_le_sum (fun j _ => show 0 ≤ if j.1 ∈ Arc then μ j else 0
        by split_ifs <;> [exact hμ_nn j; exact le_rfl]) (Finset.mem_univ i)
      simp only [hi, ↓reduceIte] at this; exact le_antisymm (by linarith) (hμ_nn i)
    have hz_pos : 0 ≤ orient2D (S a) (S c) z := by
      rw [← hμ_eq, hor_sum1 μ (fun i => S i.1) hμ_sum]
      exact Finset.sum_nonneg (fun i _ => by
        by_cases h : i.1 ∈ Arc
        · simp [hμ_notArc i h]
        · exact mul_nonneg (hμ_nn i) (le_of_lt (hrest_pos i.1 i.2 h)))
    linarith
  have hx1_conv : (s1⁻¹ • p1) ∈ convexHull ℝ (Arc.image S : Set (ℝ × ℝ)) := by
    let μA : Fin n → ℝ := fun x => if hx : x ∈ B then (if x ∈ Arc then μ ⟨x, hx⟩ / s1 else 0) else 0
    have hμA_sum : ∑ x ∈ Arc, μA x = 1 := by
      have hid : ∑ x ∈ Arc, μA x = (∑ i : B, if i.1 ∈ Arc then μ i else 0) / s1 := by
        rw [Finset.sum_div]
        have hsub : Arc ⊆ B := fun x hx => by
          rcases Finset.mem_filter.mp hx with ⟨_, m, rfl, _⟩; exact ccwCycle_mem cyc m
        refine Finset.sum_bij_ne_zero (fun x _ _ => ⟨x, hsub ‹_›⟩) ?_ ?_ ?_ ?_
        · intro x hx _; exact Finset.mem_univ _
        · intro x _ y _ _ _ h; exact congrArg Subtype.val h
        · intro i _ hni
          have hiA : i.1 ∈ Arc := by
            by_contra hna; simp [hna] at hni
          refine ⟨i.1, hiA, ?_, by simp [hiA]⟩
          intro h0
          dsimp [μA] at h0
          simp only [i.2, ↓reduceDIte, hiA, ↓reduceIte, div_eq_zero_iff, ne_of_gt hs1_pos, or_false] at h0
          simp [hiA, h0] at hni
        · intro x hx _; dsimp [μA]
          simp only [hsub hx, ↓reduceDIte, hx, ↓reduceIte]
      rw [hid]; change s1 / s1 = 1; exact div_self (ne_of_gt hs1_pos)
    have hcm : Arc.centerMass μA S = s1⁻¹ • p1 := by
      rw [Finset.centerMass_eq_of_sum_1 _ _ hμA_sum, Finset.smul_sum]
      dsimp [p1]
      have hsub : Arc ⊆ B := fun x hx => by
        rcases Finset.mem_filter.mp hx with ⟨_, m, rfl, _⟩; exact ccwCycle_mem cyc m
      refine Finset.sum_bij_ne_zero (fun x _ _ => ⟨x, hsub ‹_›⟩) ?_ ?_ ?_ ?_
      · intro x hx _; exact Finset.mem_univ _
      · intro x _ y _ _ _ h; exact congrArg Subtype.val h
      · intro i _ hni
        have hiA : i.1 ∈ Arc := by
          by_contra hna; simp [hna] at hni
        refine ⟨i.1, hiA, ?_, by simp [hiA]⟩
        intro h0; dsimp [μA] at h0
        simp only [i.2, ↓reduceDIte, hiA, ↓reduceIte] at h0
        apply hni
        simp only [hiA, ↓reduceIte]
        rw [smul_smul]
        simpa [div_eq_inv_mul, mul_comm s1⁻¹] using h0
      · intro x hx _; dsimp [μA]
        simp only [hsub hx, ↓reduceDIte, hx, ↓reduceIte, div_eq_inv_mul, smul_smul]
    rw [← hcm]
    exact Finset.centerMass_mem_convexHull _ (fun x _ => by
      dsimp [μA]
      by_cases hxB : x ∈ B <;> by_cases hxA : x ∈ Arc <;> simp [hxB, hxA]
      exact div_nonneg (hμ_nn _) (le_of_lt hs1_pos))
      (by rw [hμA_sum]; exact zero_lt_one)
      (fun x hx => Finset.mem_image.mpr ⟨x, hx, rfl⟩)
  by_cases hs2_0 : s2 = 0
  · have hp2_0 : p2 = 0 := Finset.sum_eq_zero (fun i _ => by
      by_cases h : i.1 ∈ Arc
      · simp [h]
      · have hi_0 : μ i = 0 := le_antisymm (by
          have := Finset.single_le_sum (fun j _ => show 0 ≤ if j.1 ∉ Arc then μ j else 0 from by
            by_cases hj : j.1 ∈ Arc <;> simp [hj, hμ_nn j]) (Finset.mem_univ i)
          simp only [h, not_false_eq_true, ↓reduceIte] at this
          change μ i ≤ s2 at this
          linarith) (hμ_nn i)
        simp [h, hi_0])
    have hs1_1 : s1 = 1 := by linarith
    have hz_eq : z = s1⁻¹ • p1 := by rw [← hp12, hp2_0, add_zero, hs1_1, inv_one, one_smul]
    rwa [hz_eq]
  · have hs2_pos : 0 < s2 := lt_of_le_of_ne hs2_nn (Ne.symm hs2_0)
    let x1 := s1⁻¹ • p1
    let x2 := s2⁻¹ • p2
    have hx2_conv : x2 ∈ convexHull ℝ (B.image S : Set (ℝ × ℝ)) := by
      let μB : Fin n → ℝ := fun x => if hx : x ∈ B then (if x ∉ Arc then μ ⟨x, hx⟩ / s2 else 0) else 0
      have hμB_sum : ∑ x ∈ B, μB x = 1 := by
        have hid : ∑ x ∈ B, μB x = (∑ i : B, if i.1 ∉ Arc then μ i else 0) / s2 := by
          rw [Finset.sum_div]
          refine (Finset.sum_coe_sort B (fun x => μB x)).symm.trans ?_
          refine Finset.sum_congr rfl (fun i _ => ?_)
          dsimp [μB]; simp only [i.2, ↓reduceDIte]; split_ifs <;> simp
        rw [hid]; change s2 / s2 = 1; exact div_self (ne_of_gt hs2_pos)
      have hcm : B.centerMass μB S = x2 := by
        dsimp [x2, p2]
        rw [Finset.centerMass_eq_of_sum_1 _ _ hμB_sum, Finset.smul_sum]
        refine (Finset.sum_coe_sort B (fun x => μB x • S x)).symm.trans ?_
        refine Finset.sum_congr rfl (fun i _ => ?_)
        dsimp [μB]
        by_cases h : i.1 ∈ Arc
        · simp [i.2, h]
        · simp only [i.2, ↓reduceDIte, h, not_false_eq_true, ↓reduceIte, div_eq_inv_mul, smul_smul]
      rw [← hcm]
      exact Finset.centerMass_mem_convexHull _ (fun x _ => by
        dsimp [μB]
        by_cases hxB : x ∈ B <;> by_cases hxA : x ∈ Arc <;> simp [hxB, hxA]
        exact div_nonneg (hμ_nn _) (le_of_lt hs2_pos))
        (by rw [hμB_sum]; exact zero_lt_one)
        (fun x hx => Finset.mem_image.mpr ⟨x, hx, rfl⟩)
    let d1 := orient2D (S a) (S c) x1
    let d2 := orient2D (S a) (S c) x2
    have hx1_sum : x1 = ∑ i : B, (if i.1 ∈ Arc then μ i / s1 else 0) • S i.1 := by
      dsimp [x1, p1]; rw [Finset.smul_sum]
      refine Finset.sum_congr rfl (fun i _ => by
        by_cases h : i.1 ∈ Arc <;> simp [h, div_eq_inv_mul, smul_smul])
    have hx1_wsum : ∑ i : B, (if i.1 ∈ Arc then μ i / s1 else 0) = 1 := by
      have hid : ∑ i : B, (if i.1 ∈ Arc then μ i / s1 else 0) = s1 / s1 := by
        dsimp [s1]; rw [Finset.sum_div]
        exact Finset.sum_congr rfl (fun i _ => by split_ifs <;> simp)
      rw [hid, div_self (ne_of_gt hs1_pos)]
    have hx2_sum : x2 = ∑ i : B, (if i.1 ∉ Arc then μ i / s2 else 0) • S i.1 := by
      dsimp [x2, p2]; rw [Finset.smul_sum]
      refine Finset.sum_congr rfl (fun i _ => by
        by_cases h : i.1 ∈ Arc <;> simp [h, div_eq_inv_mul, smul_smul])
    have hx2_wsum : ∑ i : B, (if i.1 ∉ Arc then μ i / s2 else 0) = 1 := by
      have hid : ∑ i : B, (if i.1 ∉ Arc then μ i / s2 else 0) = s2 / s2 := by
        dsimp [s2]; rw [Finset.sum_div]
        exact Finset.sum_congr rfl (fun i _ => by split_ifs <;> simp)
      rw [hid, div_self (ne_of_gt hs2_pos)]
    have hd1_le : d1 ≤ 0 := by
      dsimp [d1]; rw [hx1_sum, hor_sum1 _ _ hx1_wsum]
      exact Finset.sum_nonpos (fun i _ => by
        by_cases h : i.1 ∈ Arc
        · simp only [h, ↓reduceIte]
          exact mul_nonpos_of_nonneg_of_nonpos (div_nonneg (hμ_nn i) (le_of_lt hs1_pos)) (harc_le i.1 h)
        · simp [h])
    have hd2_pos : 0 < d2 := by
      have hex : ∃ i : B, i.1 ∉ Arc ∧ 0 < μ i := by
        by_contra hnone; push Not at hnone
        have h0 : s2 = 0 := Finset.sum_eq_zero (fun i _ => by
          by_cases h : i.1 ∉ Arc
          · simp [h, le_antisymm (hnone i h) (hμ_nn i)]
          · simp [h])
        linarith
      rcases hex with ⟨i0, hi0_nArc, hi0_pos⟩
      dsimp [d2]; rw [hx2_sum, hor_sum1 _ _ hx2_wsum]
      refine Finset.sum_pos' (fun i _ => by
        by_cases h : i.1 ∉ Arc
        · simp only [h, ↓reduceIte]
          exact mul_nonneg (div_nonneg (hμ_nn i) (le_of_lt hs2_pos)) (le_of_lt (hrest_pos i.1 i.2 h))
        · simp [h]) ⟨i0, Finset.mem_univ _, ?_⟩
      simp only [hi0_nArc, ↓reduceIte]
      exact mul_pos (div_pos hi0_pos hs2_pos) (hrest_pos i0.1 i0.2 hi0_nArc)
    have hz_eq_comb : z = s1 • x1 + s2 • x2 := by
      dsimp [x1, x2]
      rw [smul_inv_smul₀ (ne_of_gt hs1_pos), smul_inv_smul₀ (ne_of_gt hs2_pos), hp12]
    have hzd : orient2D (S a) (S c) z = s1 * d1 + s2 * d2 := by
      rw [hz_eq_comb]; dsimp [d1, d2]; unfold orient2D; dsimp
      linear_combination ((S a).2 * (S c).1 - (S a).1 * (S c).2) * hs12
    have hd1_neg : d1 < 0 := by nlinarith [mul_pos hs2_pos hd2_pos]
    let D := d2 - d1
    have hD_pos : 0 < D := by dsimp [D]; linarith
    have hD_ne : D ≠ 0 := ne_of_gt hD_pos
    let z_star : ℝ × ℝ := (d2 / D) • x1 + ((-d1) / D) • x2
    have hz_star_conv : z_star ∈ convexHull ℝ (B.image S : Set (ℝ × ℝ)) := by
      have hDne' : d2 - d1 ≠ 0 := hD_ne
      refine (convex_convexHull ℝ (B.image S : Set (ℝ × ℝ)))
        (convexHull_mono (Finset.image_subset_image (fun x hx => by
          rcases Finset.mem_filter.mp hx with ⟨_, m, rfl, _⟩; exact ccwCycle_mem cyc m)) hx1_conv)
        hx2_conv (div_nonneg (le_of_lt hd2_pos) (le_of_lt hD_pos))
        (div_nonneg (by linarith) (le_of_lt hD_pos))
        (by dsimp [D]; field_simp [hDne']; ring)
    have hz_star_line : orient2D (S a) (S c) z_star = 0 := by
      have hDne' : d2 - d1 ≠ 0 := hD_ne
      have : d2 / D + (-d1) / D = 1 := by dsimp [D]; field_simp [hDne']; ring
      have h1 : orient2D (S a) (S c) ((d2 / D) • x1 + ((-d1) / D) • x2) =
          (d2 / D) * orient2D (S a) (S c) x1 + ((-d1) / D) * orient2D (S a) (S c) x2 := by
        unfold orient2D; dsimp
        linear_combination ((S a).2 * (S c).1 - (S a).1 * (S c).2) * this
      change orient2D (S a) (S c) ((d2 / D) • x1 + ((-d1) / D) • x2) = 0
      rw [h1]; change (d2 / D) * d1 + ((-d1) / D) * d2 = 0; ring
    let sqLen := ((S c).1 - (S a).1) ^ 2 + ((S c).2 - (S a).2) ^ 2
    have hsq_pos : 0 < sqLen := by
      have hne : (S c).1 - (S a).1 ≠ 0 ∨ (S c).2 - (S a).2 ≠ 0 := by
        by_contra hc0; push Not at hc0
        exact hS_ac (Prod.ext (by linarith) (by linarith))
      rcases hne with h1 | h2
      · exact add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero h1) (sq_nonneg _)
      · exact add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_ne_zero h2)
    have hsq_ne : sqLen ≠ 0 := ne_of_gt hsq_pos
    let lam := (((S c).1 - (S a).1) * (z_star.1 - (S a).1) +
                ((S c).2 - (S a).2) * (z_star.2 - (S a).2)) / sqLen
    have hz_star_param : z_star = (1 - lam) • S a + lam • S c := by
      have h1 : orient2D (S a) (S c) z_star = 0 := hz_star_line
      unfold orient2D at h1
      have hsq_ne' : ((S c).1 - (S a).1) ^ 2 + ((S c).2 - (S a).2) ^ 2 ≠ 0 := hsq_ne
      ext <;> dsimp [lam, sqLen] <;> field_simp [hsq_ne']
      · linear_combination -((S c).2 - (S a).2) * h1
      · linear_combination ((S c).1 - (S a).1) * h1
    have hlam0 : 0 ≤ lam := by
      by_contra hlt
      have hneg := not_le.mp hlt
      have ht_den : 0 < 1 - lam := by linarith
      have ht0 : 0 < 1 / (1 - lam) := div_pos zero_lt_one ht_den
      have ht1 : 1 / (1 - lam) < 1 := by
        rw [div_lt_one ht_den]; linarith
      have heq : S a = (1 / (1 - lam)) • z_star + (1 - 1 / (1 - lam)) • S c := by
        rw [hz_star_param, smul_add, smul_smul, smul_smul]
        have h1 : (1 / (1 - lam)) * (1 - lam) = 1 := div_mul_cancel₀ _ (ne_of_gt ht_den)
        have h2 : (1 / (1 - lam)) * lam + (1 - 1 / (1 - lam)) = 0 := by
          field_simp [ne_of_gt ht_den]; ring
        ext <;> dsimp
        · linear_combination -((S a).1 * h1 + (S c).1 * h2)
        · linear_combination -((S a).2 * h1 + (S c).2 * h2)
      exact extreme_not_on_ray_outside S hinj hB_conv haB hcB hac hz_star_conv ht0 ht1 heq
    have hlam1 : lam ≤ 1 := by
      by_contra hlt
      have hgt := not_le.mp hlt
      have ht0 : 0 < 1 / lam := div_pos zero_lt_one (by linarith)
      have ht1 : 1 / lam < 1 := by rw [div_lt_one (by linarith)]; exact hgt
      have heq : S c = (1 / lam) • z_star + (1 - 1 / lam) • S a := by
        rw [hz_star_param, smul_add, smul_smul, smul_smul]
        have h1 : (1 / lam) * lam = 1 := div_mul_cancel₀ _ (by linarith)
        have h2 : (1 / lam) * (1 - lam) + (1 - 1 / lam) = 0 := by
          field_simp [show lam ≠ 0 by linarith]; ring
        ext <;> dsimp
        · linear_combination -((S c).1 * h1 + (S a).1 * h2)
        · linear_combination -((S c).2 * h1 + (S a).2 * h2)
      exact extreme_not_on_ray_outside S hinj hB_conv hcB haB hac.symm hz_star_conv ht0 ht1 heq
    have hz_star_arc : z_star ∈ convexHull ℝ (Arc.image S : Set (ℝ × ℝ)) := by
      rw [hz_star_param]
      exact (convex_convexHull ℝ (Arc.image S : Set (ℝ × ℝ)))
        (subset_convexHull ℝ _ (Finset.mem_image.mpr ⟨a, haArc, rfl⟩))
        (subset_convexHull ℝ _ (Finset.mem_image.mpr ⟨c, hcArc, rfl⟩))
        (by linarith) hlam0 (by ring)
    let α := (-orient2D (S a) (S c) z) / (-d1)
    let β := (s2 * D) / (-d1)
    have hd1_neg_pos : 0 < -d1 := by linarith
    have hd1_neg_ne : -d1 ≠ 0 := ne_of_gt hd1_neg_pos
    have hα_nn : 0 ≤ α := div_nonneg (by linarith) (le_of_lt hd1_neg_pos)
    have hβ_nn : 0 ≤ β := div_nonneg (mul_nonneg hs2_nn (le_of_lt hD_pos)) (le_of_lt hd1_neg_pos)
    have hαβ : α + β = 1 := by
      have hd1_ne : d1 ≠ 0 := ne_of_lt hd1_neg
      dsimp [α, β, D]; rw [hzd]; field_simp [hd1_ne]; linear_combination d1 * hs12
    have hz_arc_comb : α • x1 + β • z_star = z := by
      have hα_mul : (-d1) * α = -(s1 * d1 + s2 * d2) := by
        dsimp [α]; rw [hzd]; exact mul_div_cancel₀ _ hd1_neg_ne
      have hβ_mul : (-d1) * β = s2 * D := by
        dsimp [β]; exact mul_div_cancel₀ _ hd1_neg_ne
      have hz1_mul : D * z_star.1 = d2 * x1.1 + (-d1) * x2.1 := by
        dsimp [z_star]; field_simp [hD_ne]
      have hz2_mul : D * z_star.2 = d2 * x1.2 + (-d1) * x2.2 := by
        dsimp [z_star]; field_simp [hD_ne]
      have hnz : (-d1) * D ≠ 0 := mul_ne_zero hd1_neg_ne hD_ne
      rw [hz_eq_comb]
      ext <;> apply mul_left_cancel₀ hnz <;> dsimp
      · calc ((-d1) * D) * (α * x1.1 + β * z_star.1)
            = D * (((-d1) * α) * x1.1) + ((-d1) * β) * (D * z_star.1) := by ring
          _ = D * (-(s1 * d1 + s2 * d2) * x1.1) + (s2 * D) * (d2 * x1.1 + (-d1) * x2.1) := by
              rw [hα_mul, hβ_mul, hz1_mul]
          _ = ((-d1) * D) * (s1 * x1.1 + s2 * x2.1) := by dsimp [D]; ring
      · calc ((-d1) * D) * (α * x1.2 + β * z_star.2)
            = D * (((-d1) * α) * x1.2) + ((-d1) * β) * (D * z_star.2) := by ring
          _ = D * (-(s1 * d1 + s2 * d2) * x1.2) + (s2 * D) * (d2 * x1.2 + (-d1) * x2.2) := by
              rw [hα_mul, hβ_mul, hz2_mul]
          _ = ((-d1) * D) * (s1 * x1.2 + s2 * x2.2) := by dsimp [D]; ring
    rw [← hz_arc_comb]
    exact (convex_convexHull ℝ (Arc.image S : Set (ℝ × ℝ))) hx1_conv hz_star_arc hα_nn hβ_nn hαβ

/-! ## Part 6b: Lemma 6.2 (`targets_halfplane`), Lemma 6.3 (`consecutive_odd`), Prop 6.4 (`good_targets`), Prop 6.5 (`gap_lemma`) -/

lemma orient2D_swap12 (a b c : ℝ × ℝ) : orient2D b a c = -orient2D a b c := by
  unfold orient2D; ring

lemma fin_sub_one_ne_self {m : ℕ} (i : Fin (m + 3)) : i - 1 ≠ i := by
  intro h
  have h' := congrArg (· + (1 : Fin (m + 3))) h
  rw [sub_add_cancel] at h'
  nth_rw 1 [← add_zero i] at h'
  have h10 : (0 : Fin (m + 3)) = 1 := add_left_cancel h'
  have hv := congrArg Fin.val h10
  simp [Nat.mod_eq_of_lt (by omega : 1 < m + 3)] at hv

lemma fin_add_one_ne_self {m : ℕ} (i : Fin (m + 3)) : i ≠ i + 1 := by
  intro h
  nth_rw 1 [← add_zero i] at h
  have h01 : (0 : Fin (m + 3)) = 1 := add_left_cancel h
  have hv := congrArg Fin.val h01
  simp [Nat.mod_eq_of_lt (by omega : 1 < m + 3)] at hv

lemma fin_succ_val_parity {m : ℕ} (hm : (m + 3) % 2 = 0) (x : Fin (m + 3)) :
    (x + 1 : Fin (m + 3)).val % 2 = (x.val + 1) % 2 := by
  rw [Fin.val_add]
  have h1 : (1 : Fin (m + 3)).val = 1 := Nat.mod_eq_of_lt (show 1 < m + 3 by omega)
  rw [h1]
  rcases Nat.lt_or_eq_of_le (show x.val + 1 ≤ m + 3 from x.isLt) with hlt | heq
  · rw [Nat.mod_eq_of_lt hlt]
  · rw [heq, Nat.mod_self, hm]

/-- If `x ∈ C ⊆ B` and `(x, y)` is a CCW edge of `B` with `y ∈ C`, then `(x, y)` is a CCW edge of `C`. -/
lemma isCCWEdge_subset {n : ℕ} {S : Fin n → ℝ × ℝ} {C B : Finset (Fin n)}
    (hCB : C ⊆ B) {x y : Fin n} (hxC : x ∈ C) (hyC : y ∈ C) (hB : IsCCWEdge S B x y) :
    IsCCWEdge S C x y :=
  ⟨hxC, hyC, hB.2.2.1, fun r hr hrx hry => hB.2.2.2 r (hCB hr) hrx hry⟩

/-- Hull edge helper: from `IsConvexPos S B` and `S`-injectivity + non-collinearity, construct `CCWCycle` for `B`. -/
lemma exists_ccwCycle_hullVertices {n : ℕ} {P : Set (ℝ × ℝ)} {S : Fin n → ℝ × ℝ}
    {w : Finset (Fin n) → ℝ × ℝ} (hPoly : ShatteredSimplePolygon P S w) (hn3 : 3 ≤ n) :
    ∃ k : ℕ, (hullVertices S).card = k + 3 ∧ Nonempty (CCWCycle S (hullVertices S) k) := by
  let B := hullVertices S
  have hB3 : 3 ≤ B.card := three_le_hullVertices_card S hPoly.s_inj
    (fun a b c hab hbc hac => hPoly.no_three_collinear _ _ _
      (Or.inl (Set.mem_range_self _)) (Or.inl (Set.mem_range_self _)) (Or.inl (Set.mem_range_self _))
      (hPoly.s_inj.ne hab) (hPoly.s_inj.ne hbc) (hPoly.s_inj.ne hac)) hn3
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hB3
  have hk' : B.card = k + 3 := by omega
  refine ⟨k, hk', exists_ccwCycle S B
    (fun a _ b _ h => hPoly.s_inj h)
    (fun a _ b _ c _ hab hbc hac => hPoly.no_three_collinear _ _ _
      (Or.inl (Set.mem_range_self _)) (Or.inl (Set.mem_range_self _)) (Or.inl (Set.mem_range_self _))
      (hPoly.s_inj.ne hab) (hPoly.s_inj.ne hbc) (hPoly.s_inj.ne hac))
    (hullVertices_convexPos S Subset.rfl) hk'⟩

/-- In `D` with `O ⊆ D` pairwise non-adjacent in `D` (or neighbors of `a ∈ D` in `B` seen by `w Tv`),
    every `a ∈ O` is not a front vertex of `B` from `w Tv`. -/
lemma nonfront_hullVertices_of_nbrs_seen {n : ℕ} {P : Set (ℝ × ℝ)}
    {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ}
    (hPoly : ShatteredSimplePolygon P S w) (h25 : Sec2To5Interface P S w)
    (hn3 : 3 ≤ n) {Tv : Finset (Fin n)} {o : Fin n}
    (hoD : o ∈ hullVertices S \ certifiedVertices S w) (ho_miss : o ∉ Tv)
    (ho_nbrs : ∀ x ∈ hullVertices S, (IsCCWEdge S (hullVertices S) x o ∨ IsCCWEdge S (hullVertices S) o x) → x ∈ Tv) :
    ¬ IsFrontVertexOf S (hullVertices S) o (w Tv) := by
  have hB3 : 3 ≤ (hullVertices S).card := three_le_hullVertices_card S hPoly.s_inj
    (fun a b c hab hbc hac => hPoly.no_three_collinear _ _ _
      (Or.inl (Set.mem_range_self _)) (Or.inl (Set.mem_range_self _)) (Or.inl (Set.mem_range_self _))
      (hPoly.s_inj.ne hab) (hPoly.s_inj.ne hbc) (hPoly.s_inj.ne hac)) hn3
  -- Direct certification contradiction identical to `no_odd_front` with `C = B`?
  -- Wait: `no_odd_front` requires `C ⊆ D`, whereas here `o ∈ D` and `C = B`!
  intro hfront
  let B := hullVertices S
  obtain ⟨k, hk, ⟨cyc⟩⟩ := exists_ccwCycle_hullVertices hPoly hn3
  obtain ⟨io, rfl⟩ := ccwCycle_exists_index cyc (Finset.mem_sdiff.mp hoD).1
  let o_prev := cyc.toFun (io - 1)
  let o_next := cyc.toFun (io + 1)
  have e_prev : IsCCWEdge S B o_prev (cyc.toFun io) := by
    have := ccwCycle_isCCWEdge cyc (io - 1); rwa [sub_add_cancel] at this
  have e_next : IsCCWEdge S B (cyc.toFun io) o_next := ccwCycle_isCCWEdge cyc io
  have hp_in : o_prev ∈ Tv := ho_nbrs o_prev (ccwCycle_mem cyc (io - 1)) (Or.inl e_prev)
  have hn_in : o_next ∈ Tv := ho_nbrs o_next (ccwCycle_mem cyc (io + 1)) (Or.inr e_next)
  have ho_in_tri : InIntTri (w Tv) (S o_prev) (S o_next) (S (cyc.toFun io)) :=
    (h25.hidden_front B Tv (cyc.toFun io) o_prev o_next Subset.rfl hB3 (ccwCycle_mem cyc io)
      e_prev e_next hp_in hn_in ho_miss hfront).1
  let Tz := Finset.univ.erase (cyc.toFun io)
  have hoB : cyc.toFun io ∈ B := ccwCycle_mem cyc io
  have hne_prev : o_prev ≠ cyc.toFun io := e_prev.2.2.1
  have hne_next : o_next ≠ cyc.toFun io := e_next.2.2.1.symm
  have hprev_Tz : o_prev ∈ Tz := Finset.mem_erase.mpr ⟨hne_prev, Finset.mem_univ _⟩
  have hnext_Tz : o_next ∈ Tz := Finset.mem_erase.mpr ⟨hne_next, Finset.mem_univ _⟩
  have h_prev_ne_next : o_prev ≠ o_next := by
    intro heq
    have h2_ne_0 : (2 : Fin (k + 3)) ≠ 0 := by
      intro h; have := congrArg Fin.val h; simp [Nat.mod_eq_of_lt (by omega : 2 < k + 3)] at this
    have h1 : io - 1 = io + 1 := cyc.inj heq
    have h2 := congrArg (· + (1 : Fin (k + 3))) h1
    rw [sub_add_cancel, add_assoc] at h2
    nth_rw 1 [← add_zero io] at h2
    exact h2_ne_0 (add_left_cancel h2).symm
  have hcone : InIntTri (w Tz) (S o_prev) (S o_next) (S (cyc.toFun io)) := by
    by_cases hTT : Tv = Tz
    · rwa [← hTT]
    · apply h25.cone_lemma (S (cyc.toFun io)) (S o_prev) (S o_next) (w Tv) (w Tz)
        (hPoly.s_in_P _) (hPoly.s_in_P _) (hPoly.s_in_P _) (hPoly.w_in_P _) (hPoly.w_in_P _)
      · exact (hPoly.shatters Tv o_prev).mpr hp_in
      · exact (hPoly.shatters Tv o_next).mpr hn_in
      · intro hs; exact ho_miss ((hPoly.shatters Tv _).mp hs)
      · exact ho_in_tri
      · exact (hPoly.shatters Tz o_prev).mpr hprev_Tz
      · exact (hPoly.shatters Tz o_next).mpr hnext_Tz
      · exact hPoly.no_three_collinear _ _ _
          (Or.inl (Set.mem_range_self _)) (Or.inl (Set.mem_range_self _)) (Or.inr (Set.mem_range_self _))
          (hPoly.s_inj.ne hne_prev.symm) (hPoly.s_ne_w _ _) (hPoly.s_ne_w _ _)
      · exact hPoly.no_three_collinear _ _ _
          (Or.inl (Set.mem_range_self _)) (Or.inl (Set.mem_range_self _)) (Or.inr (Set.mem_range_self _))
          (hPoly.s_inj.ne hne_next.symm) (hPoly.s_ne_w _ _) (hPoly.s_ne_w _ _)
      · exact hPoly.no_three_collinear _ _ _
          (Or.inr (Set.mem_range_self _)) (Or.inl (Set.mem_range_self _)) (Or.inr (Set.mem_range_self _))
          (hPoly.s_ne_w _ _).symm (hPoly.s_ne_w _ _) (hPoly.w_inj.ne hTT)
  let C3 : Finset (Fin n) := {o_prev, cyc.toFun io, o_next}
  have hC3_sub : C3 ⊆ B := fun x hx => by
    simp only [C3, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact ccwCycle_mem cyc (io - 1)
    · exact hoB
    · exact ccwCycle_mem cyc (io + 1)
  have hC3_card : 3 ≤ C3.card := by
    have h1 : o_prev ∉ ({cyc.toFun io, o_next} : Finset (Fin n)) := by simp [hne_prev, h_prev_ne_next]
    have h2 : cyc.toFun io ∉ ({o_next} : Finset (Fin n)) := by simp [hne_next.symm]
    rw [Finset.card_insert_of_notMem h1, Finset.card_insert_of_notMem h2, Finset.card_singleton]
  have hfront_B : IsFrontVertexOf S B (cyc.toFun io) (w Tz) :=
    h25.front_restoration C3 B (cyc.toFun io) (w Tz) hC3_sub (hullVertices_convexPos S Subset.rfl)
      hC3_card (Set.mem_range_self Tz) (inIntTri_implies_isFrontVertexOf_tri S hne_prev hne_next h_prev_ne_next (w Tz) hcone)
  have hcert : cyc.toFun io ∈ certifiedVertices S w := by
    refine Finset.mem_filter.mpr ⟨hoB, Tz, Finset.notMem_erase _ _, ?_, ?_, hfront_B⟩
    · intro b hb; exact Finset.mem_erase.mpr ⟨hb.2.2.1, Finset.mem_univ _⟩
    · intro c hc; exact Finset.mem_erase.mpr ⟨hc.2.2.1.symm, Finset.mem_univ _⟩
  exact (Finset.mem_sdiff.mp hoD).2 hcert

/-- Lemma 6.2 (`targets-halfplane`, `upper_9.tex` lines 619–642). -/
theorem targets_halfplane {n : ℕ} {P : Set (ℝ × ℝ)}
    {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ}
    (hPoly : ShatteredSimplePolygon P S w) (h25 : Sec2To5Interface P S w)
    {Tv O_miss : Finset (Fin n)} {a p c : Fin n}
    (haB : a ∈ hullVertices S) (hpB : p ∈ hullVertices S) (hcB : c ∈ hullVertices S)
    (hap : a ≠ p) (hpc : p ≠ c) (hac : a ≠ c)
    (hp_seen : p ∈ Tv) (ha_miss : a ∉ Tv) (hc_miss : c ∉ Tv)
    (hO_Tv : ∀ x : Fin n, x ∉ O_miss → x ∈ Tv)
    (ha_nf : ¬ IsFrontVertexOf S (hullVertices S) a (w Tv))
    (hc_nf : ¬ IsFrontVertexOf S (hullVertices S) c (w Tv))
    (h_cone_v :
      (0 < orient2D (S a) (S p) (S c) ∧ 0 < orient2D (S a) (S p) (w Tv) ∧ 0 < orient2D (S p) (S c) (w Tv)) ∨
      (0 < orient2D (S c) (S p) (S a) ∧ 0 < orient2D (S c) (S p) (w Tv) ∧ 0 < orient2D (S p) (S a) (w Tv)))
    (hap_ang : AngleLt (w Tv) (w Finset.univ) (S a) (S p))
    (hpc_ang : AngleLt (w Tv) (w Finset.univ) (S p) (S c))
    (hcond4 : Sees P (w Tv) (w Finset.univ) ∨
      ∃ e : Fin n, e ∈ Tv ∧ AngleLt (w Tv) (w Finset.univ) (S e) (S a)) :
    IsBackVertexOf S (hullVertices S) p (w Tv) ∧
    (SegmentsCross (w Tv) (S p) (S a) (S c) ∧
      ∃ H_hp : OpenHalfPlane, IsHalfPlaneTest P (WitnessSet {a, c} ∅ w) (S p) H_hp) ∧
    (∀ z : Fin n, z ≠ a → z ≠ c → z ∉ O_miss →
      S z ∈ convexHull ℝ ((hullVertices S).image S : Set (ℝ × ℝ)) →
      0 < orient2D (S a) (S c) (S p) * orient2D (S a) (S c) (S z) →
      SegmentsCross (w Tv) (S z) (S a) (S c) ∧
      (∃ H_hp : OpenHalfPlane, IsHalfPlaneTest P (WitnessSet {a, c} ∅ w) (S z) H_hp) ∧
      (z ∈ hullVertices S → IsBackVertexOf S (hullVertices S) z (w Tv))) := by
  let B := hullVertices S
  let v := w Tv
  let q := w Finset.univ
  have hn3 : 3 ≤ n := by
    have h1 : a ∉ ({p, c} : Finset (Fin n)) := by simp [hap, hac]
    have h2 : p ∉ ({c} : Finset (Fin n)) := by simp [hpc]
    have hcard : ({a, p, c} : Finset (Fin n)).card = 3 := by
      rw [Finset.card_insert_of_notMem h1, Finset.card_insert_of_notMem h2, Finset.card_singleton]
    have hle := (Finset.card_le_univ ({a, p, c} : Finset (Fin n))).trans_eq (Fintype.card_fin n)
    omega
  obtain ⟨kB, hkB, ⟨cycB⟩⟩ := exists_ccwCycle_hullVertices hPoly hn3
  obtain ⟨ia, hia⟩ := ccwCycle_exists_index cycB haB
  obtain ⟨ip, hip⟩ := ccwCycle_exists_index cycB hpB
  obtain ⟨ic, hic⟩ := ccwCycle_exists_index cycB hcB
  have hp_back : IsBackVertexOf S B p v := by
    rw [← hip, isBackVertexOf_iff_ccwCycle cycB ip v]
    have hpm1_ne_pp1 : ip - 1 ≠ ip + 1 := by
      intro h
      have h' := congrArg (· + (1 : Fin (kB + 3))) h
      rw [sub_add_cancel, add_assoc] at h'
      nth_rw 1 [← add_zero ip] at h'
      have h20 : (0 : Fin (kB + 3)) = 2 := add_left_cancel h'
      have hv := congrArg Fin.val h20
      simp [Nat.mod_eq_of_lt (by omega : 2 < kB + 3)] at hv
    have hp1_ne_p : ip + 1 ≠ ip := by
      intro h; nth_rw 2 [← add_zero ip] at h
      have h10 : (1 : Fin (kB + 3)) = 0 := add_left_cancel h
      have hv := congrArg Fin.val h10
      simp [Nat.mod_eq_of_lt (by omega : 1 < kB + 3)] at hv
    have hcorner : 0 < orient2D (S (cycB.toFun (ip - 1))) (S (cycB.toFun ip)) (S (cycB.toFun (ip + 1))) := by
      simpa [sub_add_cancel] using cycB.ccw (ip - 1) (ip + 1) hpm1_ne_pp1.symm
        (by rw [sub_add_cancel]; exact hp1_ne_p)
    have h_sides : ∀ x ∈ B, 0 ≤ orient2D (S (cycB.toFun (ip - 1))) (S (cycB.toFun ip)) (S x) ∧
        0 ≤ orient2D (S (cycB.toFun ip)) (S (cycB.toFun (ip + 1))) (S x) := by
      intro x hxB
      obtain ⟨ix, rfl⟩ := ccwCycle_exists_index cycB hxB
      exact ⟨by simpa [sub_add_cancel] using strictConvexCCW_orient_nonneg (S ∘ cycB.toFun) cycB.ccw (ip - 1) ix,
             strictConvexCCW_orient_nonneg (S ∘ cycB.toFun) cycB.ccw ip ix⟩
    rcases h_cone_v with ⟨ho1, ho2, ho3⟩ | ⟨ho1, ho2, ho3⟩
    · rw [← hip] at ho1 ho2 ho3
      exact crossing_anchor_implies_back_vertex (S (cycB.toFun (ip - 1))) (S (cycB.toFun ip))
        (S (cycB.toFun (ip + 1))) (S c) (S a) v hcorner
        (h_sides c hcB).1 (h_sides c hcB).2 (h_sides a haB).1 (h_sides a haB).2
        (by unfold orient2D at ho1 ⊢; linarith) (by unfold orient2D at ho3 ⊢; linarith)
        (by unfold orient2D at ho2 ⊢; linarith)
    · rw [← hip] at ho1 ho2 ho3
      exact crossing_anchor_implies_back_vertex (S (cycB.toFun (ip - 1))) (S (cycB.toFun ip))
        (S (cycB.toFun (ip + 1))) (S a) (S c) v hcorner
        (h_sides a haB).1 (h_sides a haB).2 (h_sides c hcB).1 (h_sides c hcB).2
        (by unfold orient2D at ho1 ⊢; linarith) (by unfold orient2D at ho3 ⊢; linarith)
        (by unfold orient2D at ho2 ⊢; linarith)
  have hcross_p : SegmentsCross v (S p) (S a) (S c) := by
    have hac_ang := hap_ang.trans hpc_ang
    rcases hap_ang with ⟨hs_ap, ho_ap⟩
    rcases hpc_ang with ⟨hs_pc, ho_pc⟩
    have hvqa_ne : orient2D v q (S a) ≠ 0 := by
      intro h0; rw [h0, zero_mul] at ho_ap; linarith
    rcases lt_or_gt_of_ne hvqa_ne with hqa_neg | hqa_pos
    · have hqp_neg : orient2D v q (S p) < 0 := by unfold OnSameSide at hs_ap; nlinarith
      have hapv : orient2D (S a) (S p) v < 0 := by
        have h1 : orient2D v (S a) (S p) < 0 := by nlinarith
        unfold orient2D at h1 ⊢; linarith
      have hpcv : orient2D (S p) (S c) v < 0 := by
        have h1 : orient2D v (S p) (S c) < 0 := by nlinarith
        unfold orient2D at h1 ⊢; linarith
      rcases h_cone_v with ⟨_, h_pos, _⟩ | ⟨hcpa, hcpv, hpav⟩
      · exfalso; linarith
      · have hacv : orient2D (S a) (S c) v < 0 := by
          have hss_ac := hac_ang.1; have ho_ac := hac_ang.2
          unfold OnSameSide at hss_ac
          have h1 : orient2D v (S a) (S c) < 0 := by nlinarith
          unfold orient2D at h1 ⊢; linarith
        have hacp : 0 < orient2D (S a) (S c) (S p) := by
          unfold orient2D at hcpa ⊢; linarith
        refine ⟨?_, mul_neg_of_neg_of_pos hacv hacp⟩
        have h1 : 0 < orient2D v (S p) (S a) := by unfold orient2D at hpav ⊢; linarith
        have h2 : orient2D v (S p) (S c) < 0 := by unfold orient2D at hpcv ⊢; linarith
        exact mul_neg_of_pos_of_neg h1 h2
    · have hqp_pos : 0 < orient2D v q (S p) := by unfold OnSameSide at hs_ap; nlinarith
      have hapv : 0 < orient2D (S a) (S p) v := by
        have h1 : 0 < orient2D v (S a) (S p) := by nlinarith
        unfold orient2D at h1 ⊢; linarith
      have hpcv : 0 < orient2D (S p) (S c) v := by
        have h1 : 0 < orient2D v (S p) (S c) := by nlinarith
        unfold orient2D at h1 ⊢; linarith
      rcases h_cone_v with ⟨hapc, _, _⟩ | ⟨_, hcpv, _⟩
      · have hacv : 0 < orient2D (S a) (S c) v := by
          have hss_ac := hac_ang.1; have ho_ac := hac_ang.2
          unfold OnSameSide at hss_ac
          have h1 : 0 < orient2D v (S a) (S c) := by nlinarith
          unfold orient2D at h1 ⊢; linarith
        have hacp : orient2D (S a) (S c) (S p) < 0 := by
          unfold orient2D at hapc ⊢; linarith
        refine ⟨?_, mul_neg_of_pos_of_neg hacv hacp⟩
        have h1 : orient2D v (S p) (S a) < 0 := by unfold orient2D at hapv ⊢; linarith
        have h2 : 0 < orient2D v (S p) (S c) := by unfold orient2D at hpcv ⊢; linarith
        exact mul_neg_of_neg_of_pos h1 h2
      · exfalso; unfold orient2D at hcpv hpcv; linarith
  have hcond4_full : Sees P v q ∨ ∃ e : Fin n, e ∈ Tv ∧ e ∈ Finset.univ ∧ AngleLt v q (S e) (S a) := by
    rcases hcond4 with h | ⟨e, he, hlt⟩
    · exact Or.inl h
    · exact Or.inr ⟨e, he, Finset.mem_univ _, hlt⟩
  have hhp_p := (universal_crossing hPoly h25 ha_miss hc_miss (Finset.mem_univ a) (Finset.mem_univ c)
    (hap_ang.trans hpc_ang) hcond4_full hp_seen (Finset.mem_univ p) hcross_p).1
  refine ⟨hp_back, ⟨hcross_p, hhp_p⟩, ?_⟩
  intro z hza hzc hzO hz_conv hz_side
  have hzv_col : orient2D v (S a) (S z) ≠ 0 ∧ orient2D v (S c) (S z) ≠ 0 ∧ orient2D (S a) (S c) (S z) ≠ 0 := by
    refine ⟨?_, ?_, ?_⟩
    · exact hPoly.no_three_collinear _ _ _
        (Or.inr (Set.mem_range_self _)) (Or.inl (Set.mem_range_self _)) (Or.inl (Set.mem_range_self _))
        (hPoly.s_ne_w _ _).symm (hPoly.s_inj.ne hza.symm) (hPoly.s_ne_w _ _).symm
    · exact hPoly.no_three_collinear _ _ _
        (Or.inr (Set.mem_range_self _)) (Or.inl (Set.mem_range_self _)) (Or.inl (Set.mem_range_self _))
        (hPoly.s_ne_w _ _).symm (hPoly.s_inj.ne hzc.symm) (hPoly.s_ne_w _ _).symm
    · exact hPoly.no_three_collinear _ _ _
        (Or.inl (Set.mem_range_self _)) (Or.inl (Set.mem_range_self _)) (Or.inl (Set.mem_range_self _))
        (hPoly.s_inj.ne hac) (hPoly.s_inj.ne hzc.symm) (hPoly.s_inj.ne hza.symm)
  have hv_noncolB : ∀ i j : Fin (kB + 3), i ≠ j →
      orient2D (S (cycB.toFun i)) (S (cycB.toFun j)) v ≠ 0 := by
    intro i j hij
    exact hPoly.no_three_collinear _ _ _
      (Or.inl (Set.mem_range_self _)) (Or.inl (Set.mem_range_self _)) (Or.inr (Set.mem_range_self _))
      (hPoly.s_inj.ne (cycB.inj.ne hij)) (hPoly.s_ne_w _ _) (hPoly.s_ne_w _ _)
  have hvqB : ∀ i : Fin (kB + 3), orient2D v q (S (cycB.toFun i)) ≠ 0 := by
    intro i
    exact hPoly.no_three_collinear _ _ _
      (Or.inr (Set.mem_range_self _)) (Or.inr (Set.mem_range_self _)) (Or.inl (Set.mem_range_self _))
      (hPoly.w_inj.ne (fun h => by
        have hTv_mem : p ∈ Tv := hp_seen
        have hTv_ne : Tv ≠ Finset.univ := fun heq => ha_miss (heq ▸ Finset.mem_univ a)
        exact hTv_ne h))
      (hPoly.s_ne_w _ _).symm (hPoly.s_ne_w _ _).symm
  have ha_nf_cyc : 0 < orient2D (S (cycB.toFun (ia - 1))) (S (cycB.toFun ia)) v ∨
      0 < orient2D (S (cycB.toFun ia)) (S (cycB.toFun (ia + 1))) v := by
    by_contra hboth; push Not at hboth
    apply ha_nf
    rw [← hia, isFrontVertexOf_iff_ccwCycle cycB ia v]
    have h1 := hv_noncolB (ia - 1) ia (fin_sub_one_ne_self ia)
    have h2 := hv_noncolB ia (ia + 1) (fin_add_one_ne_self ia)
    exact ⟨lt_of_le_of_ne hboth.1 h1, lt_of_le_of_ne hboth.2 h2⟩
  have hc_nf_cyc : 0 < orient2D (S (cycB.toFun (ic - 1))) (S (cycB.toFun ic)) v ∨
      0 < orient2D (S (cycB.toFun ic)) (S (cycB.toFun (ic + 1))) v := by
    by_contra hboth; push Not at hboth
    apply hc_nf
    rw [← hic, isFrontVertexOf_iff_ccwCycle cycB ic v]
    have h1 := hv_noncolB (ic - 1) ic (fin_sub_one_ne_self ic)
    have h2 := hv_noncolB ic (ic + 1) (fin_add_one_ne_self ic)
    exact ⟨lt_of_le_of_ne hboth.1 h1, lt_of_le_of_ne hboth.2 h2⟩
  have hiac : ia ≠ ic := fun h => hac (hia.symm.trans (congrArg cycB.toFun h |>.trans hic))
  have hss_ac : OnSameSide v q (S (cycB.toFun ia)) (S (cycB.toFun ic)) := by
    rw [hia, hic]; exact (hap_ang.trans hpc_ang).1
  have hfar := farChain_path_between cycB v q hv_noncolB hvqB ia ic hiac hss_ac ha_nf_cyc hc_nf_cyc
  have hac_ang := hap_ang.trans hpc_ang
  have hcross_z : SegmentsCross v (S z) (S a) (S c) := by
    have hac_ne0 : orient2D (S a) (S c) (S p) ≠ 0 :=
      hPoly.no_three_collinear _ _ _
        (Or.inl (Set.mem_range_self _)) (Or.inl (Set.mem_range_self _)) (Or.inl (Set.mem_range_self _))
        (hPoly.s_inj.ne hac) (hPoly.s_inj.ne hpc.symm) (hPoly.s_inj.ne hap)
    rcases lt_or_gt_of_ne hac_ne0 with hacp_neg | hacp_pos
    · have hz_side' : orient2D (S (cycB.toFun ia)) (S (cycB.toFun ic)) (S z) < 0 := by
        rw [hia, hic]; nlinarith
      have hzp_neg : orient2D (S a) (S c) v > 0 := by
        have := hcross_p.2; nlinarith
      have hqa_pos : 0 < orient2D v q (S a) := by
        have h1 : 0 < orient2D v (S a) (S c) := by unfold orient2D at hzp_neg ⊢; linarith
        have h2 := hac_ang.2
        nlinarith
      have hfar_ac : (∀ t : ℕ, t < (ic - ia).val →
            0 < orient2D (S (cycB.toFun (ia + finNat (kB + 3) t)))
                         (S (cycB.toFun (ia + finNat (kB + 3) t + 1))) v) ∧
          (∀ t : ℕ, t ≤ (ic - ia).val →
            OnSameSide v q (S (cycB.toFun ia)) (S (cycB.toFun (ia + finNat (kB + 3) t)))) := by
        rcases hfar with h1 | h2
        · exact h1
        · exfalso
          have hmono := (farChain_arc_angle_monotone cycB v q ic ia h2.1 (fun t ht =>
            hss_ac.symm.trans (h2.2 t ht))).1 (by
              have hss_v : OnSameSide v q (S a) (S c) := hac_ang.1
              have hqa_pos' : 0 < orient2D v q (S (cycB.toFun ia)) := by rwa [hia]
              rw [← hia, ← hic] at hss_v; unfold OnSameSide at hss_v; nlinarith)
          have hca_pos : 0 < (ia - ic).val := by
            by_contra h0; have h0' : (ia - ic).val = 0 := by omega
            exact hiac (sub_eq_zero.mp (Fin.ext h0'))
          have hca_ang : AngleLt v q (S c) (S a) := by
            have := hmono 0 (ia - ic).val hca_pos le_rfl
            have heq : ic + finNat (kB + 3) (ia - ic).val = ia := by
              have : finNat (kB + 3) (ia - ic).val = ia - ic := by
                ext; exact Nat.mod_eq_of_lt (ia - ic).isLt
              rw [this, add_sub_cancel]
            rwa [finNat_zero, add_zero, heq, hia, hic] at this
          exact hac_ang.asymm hca_ang
      have hz_arc := convexHull_subset_arc_of_line S hPoly.s_inj (hullVertices_convexPos S Subset.rfl)
        cycB ia ic hiac (hPoly.s_inj.ne (fun h => hac (hia.symm.trans (h.trans hic)))) hz_conv hz_side'
      have hmono := (farChain_arc_angle_monotone cycB v q ia ic hfar_ac.1 hfar_ac.2).1
        (by rwa [hia])
      refine cap_convex_crossing hac_ang _ (fun g hg => ?_) hz_arc hzv_col.1 hzv_col.2.1 hzv_col.2.2
      rcases Finset.mem_image.mp hg with ⟨x, hxArc, rfl⟩
      rcases Finset.mem_filter.mp hxArc with ⟨_, m, rfl, hm⟩
      by_cases hma : m = ia
      · left; rw [hma, hia]
      · by_cases hmc : m = ic
        · right; left; rw [hmc, hic]
        · right; right
          have hm_pos : 0 < (m - ia).val := Nat.pos_of_ne_zero (fun h => hma (sub_eq_zero.mp (Fin.ext h)))
          have hm_lt : (m - ia).val < (ic - ia).val := lt_of_le_of_ne hm (fun h => hmc (by
            have := congrArg (· + ia) (Fin.ext h); simpa [sub_add_cancel] using this))
          have hm_eq : ia + finNat (kB + 3) (m - ia).val = m := by
            have : finNat (kB + 3) (m - ia).val = m - ia := by ext; exact Nat.mod_eq_of_lt (m - ia).isLt
            rw [this, add_sub_cancel]
          have h_am := hmono 0 (m - ia).val hm_pos (Nat.le_of_lt hm_lt)
          have h_mc := hmono (m - ia).val (ic - ia).val hm_lt le_rfl
          have heq_ic : ia + finNat (kB + 3) (ic - ia).val = ic := by
            have : finNat (kB + 3) (ic - ia).val = ic - ia := by ext; exact Nat.mod_eq_of_lt (ic - ia).isLt
            rw [this, add_sub_cancel]
          rw [finNat_zero, add_zero, hm_eq, hia] at h_am
          rw [hm_eq, heq_ic, hic] at h_mc
          have h_ccw := ccwCycle_ccw3 cycB hm_pos hm_lt
          rw [hia, hic] at h_ccw
          have hx_ac_neg : orient2D (S a) (S c) (S (cycB.toFun m)) < 0 := by
            unfold orient2D at h_ccw ⊢; linarith
          refine ⟨h_am.1, fun _ => ?_, fun hbad => False.elim (by linarith)⟩
          have hvam : 0 < orient2D v (S a) (S (cycB.toFun m)) := by
            have h1 := h_am.1; have h2 := h_am.2; unfold OnSameSide at h1; nlinarith
          have hvmc : 0 < orient2D v (S (cycB.toFun m)) (S c) := by
            have h1 := h_mc.1; have h2 := h_mc.2; have ha1 := h_am.1
            unfold OnSameSide at h1 ha1; nlinarith
          exact ⟨le_of_lt hvam, le_of_lt hvmc, mul_nonpos_of_nonneg_of_nonpos (le_of_lt hzp_neg) (le_of_lt hx_ac_neg)⟩
    · have hz_side' : orient2D (S (cycB.toFun ic)) (S (cycB.toFun ia)) (S z) < 0 := by
        rw [hia, hic, orient2D_swap12]; nlinarith
      have hzp_neg : orient2D (S a) (S c) v < 0 := by
        have := hcross_p.2; nlinarith
      have hqa_neg : orient2D v q (S a) < 0 := by
        have h1 : orient2D v (S a) (S c) < 0 := by unfold orient2D at hzp_neg ⊢; linarith
        have h2 := hac_ang.2
        nlinarith
      have hfar_ca : (∀ t : ℕ, t < (ia - ic).val →
            0 < orient2D (S (cycB.toFun (ic + finNat (kB + 3) t)))
                         (S (cycB.toFun (ic + finNat (kB + 3) t + 1))) v) ∧
          (∀ t : ℕ, t ≤ (ia - ic).val →
            OnSameSide v q (S (cycB.toFun ic)) (S (cycB.toFun (ic + finNat (kB + 3) t)))) := by
        rcases hfar with h1 | h2
        · exfalso
          have hmono := (farChain_arc_angle_monotone cycB v q ia ic h1.1 h1.2).2 (by rwa [hia])
          have hac_pos : 0 < (ic - ia).val := by
            by_contra h0; have h0' : (ic - ia).val = 0 := by omega
            exact hiac (sub_eq_zero.mp (Fin.ext h0')).symm
          have hca_ang : AngleLt v q (S c) (S a) := by
            have := hmono 0 (ic - ia).val hac_pos le_rfl
            have heq : ia + finNat (kB + 3) (ic - ia).val = ic := by
              have : finNat (kB + 3) (ic - ia).val = ic - ia := by ext; exact Nat.mod_eq_of_lt (ic - ia).isLt
              rw [this, add_sub_cancel]
            rwa [finNat_zero, add_zero, heq, hia, hic] at this
          exact hac_ang.asymm hca_ang
        · exact ⟨h2.1, fun t ht => hss_ac.symm.trans (h2.2 t ht)⟩
      have hz_arc := convexHull_subset_arc_of_line S hPoly.s_inj (hullVertices_convexPos S Subset.rfl)
        cycB ic ia hiac.symm (hPoly.s_inj.ne (fun h => hac.symm (hic.symm.trans (h.trans hia)))) hz_conv hz_side'
      have hqc_neg : orient2D v q (S c) < 0 := by
        have := hac_ang.1; unfold OnSameSide at this; nlinarith
      have hmono := (farChain_arc_angle_monotone cycB v q ic ia hfar_ca.1 hfar_ca.2).2
        (by rwa [hic])
      refine cap_convex_crossing hac_ang _ (fun g hg => ?_) hz_arc hzv_col.1 hzv_col.2.1 hzv_col.2.2
      rcases Finset.mem_image.mp hg with ⟨x, hxArc, rfl⟩
      rcases Finset.mem_filter.mp hxArc with ⟨_, m, rfl, hm⟩
      by_cases hma : m = ia
      · left; rw [hma, hia]
      · by_cases hmc : m = ic
        · right; left; rw [hmc, hic]
        · right; right
          have hm_pos : 0 < (m - ic).val := Nat.pos_of_ne_zero (fun h => hmc (sub_eq_zero.mp (Fin.ext h)))
          have hm_lt : (m - ic).val < (ia - ic).val := lt_of_le_of_ne hm (fun h => hma (by
            have := congrArg (· + ic) (Fin.ext h); simpa [sub_add_cancel] using this))
          have hm_eq : ic + finNat (kB + 3) (m - ic).val = m := by
            have : finNat (kB + 3) (m - ic).val = m - ic := by ext; exact Nat.mod_eq_of_lt (m - ic).isLt
            rw [this, add_sub_cancel]
          have h_mc := hmono 0 (m - ic).val hm_pos (Nat.le_of_lt hm_lt)
          have h_am := hmono (m - ic).val (ia - ic).val hm_lt le_rfl
          have heq_ia : ic + finNat (kB + 3) (ia - ic).val = ia := by
            have : finNat (kB + 3) (ia - ic).val = ia - ic := by ext; exact Nat.mod_eq_of_lt (ia - ic).isLt
            rw [this, add_sub_cancel]
          rw [finNat_zero, add_zero, hm_eq, hic] at h_mc
          rw [hm_eq, heq_ia, hia] at h_am
          have h_ccw := ccwCycle_ccw3 cycB hm_pos hm_lt
          rw [hia, hic] at h_ccw
          have hx_ac_pos : 0 < orient2D (S a) (S c) (S (cycB.toFun m)) := by
            unfold orient2D at h_ccw ⊢; linarith
          refine ⟨h_am.1, fun hbad => False.elim (by linarith), fun _ => ?_⟩
          have hvam : orient2D v (S a) (S (cycB.toFun m)) < 0 := by
            have h1 := h_am.1; have h2 := h_am.2; unfold OnSameSide at h1; nlinarith
          have hvmc : orient2D v (S (cycB.toFun m)) (S c) < 0 := by
            have h1 := h_mc.1; have h2 := h_mc.2; have hc1 := h_mc.1
            unfold OnSameSide at h1 hc1; nlinarith
          exact ⟨le_of_lt hvam, le_of_lt hvmc, mul_nonpos_of_nonpos_of_nonneg (le_of_lt hzp_neg) (le_of_lt hx_ac_pos)⟩
  have huc := universal_crossing hPoly h25 ha_miss hc_miss (Finset.mem_univ a) (Finset.mem_univ c)
    hac_ang hcond4_full (hO_Tv z hzO) (Finset.mem_univ z) hcross_z
  exact ⟨hcross_z, huc.1, huc.2⟩

/-- Lemma 6.3 (`consecutive-odd`, `upper_9.tex` lines 646–652):
    Two consecutive-angle odd vertices `io, io'` on the same side of `G = v q`
    along a strictly convex alternating `(m + 3)`-gon enclose a unique even back vertex `ig`
    with `a = io, c = io'` (or swapped) forming a target with anchors `{io, io'}`. -/
theorem consecutive_odd {n m : ℕ} {P : Set (ℝ × ℝ)}
    {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ}
    {C : Finset (Fin n)} (hm : m % 2 = 1) (hm1 : 1 ≤ m)
    (cyc : CCWCycle S C m)
    (v q : ℝ × ℝ)
    (hv_noncol : ∀ i j : Fin (m + 3), i ≠ j → orient2D (S (cyc.toFun i)) (S (cyc.toFun j)) v ≠ 0)
    (hvq : ∀ i : Fin (m + 3), orient2D v q (S (cyc.toFun i)) ≠ 0)
    (h_odd_nf : ∀ i : Fin (m + 3), i.val % 2 = 1 → ¬ IsFrontVertexOf S C (cyc.toFun i) v)
    (io io' : Fin (m + 3)) (ho : io.val % 2 = 1) (ho' : io'.val % 2 = 1)
    (h_ang : AngleLt v q (S (cyc.toFun io)) (S (cyc.toFun io')))
    (h_consec : ∀ i'' : Fin (m + 3), i''.val % 2 = 1 → OnSameSide v q (S (cyc.toFun io)) (S (cyc.toFun i'')) →
      ¬ (AngleLt v q (S (cyc.toFun io)) (S (cyc.toFun i'')) ∧ AngleLt v q (S (cyc.toFun i'')) (S (cyc.toFun io')))) :
    ∃ ig : Fin (m + 3), ig.val % 2 = 0 ∧
      ((io + 1 = ig ∧ ig + 1 = io') ∨ (io' + 1 = ig ∧ ig + 1 = io)) ∧
      IsBackVertexOf S C (cyc.toFun ig) v ∧
      AngleLt v q (S (cyc.toFun io)) (S (cyc.toFun ig)) ∧
      AngleLt v q (S (cyc.toFun ig)) (S (cyc.toFun io')) ∧
      ((0 < orient2D (S (cyc.toFun io)) (S (cyc.toFun ig)) (S (cyc.toFun io')) ∧
        0 < orient2D (S (cyc.toFun io)) (S (cyc.toFun ig)) v ∧
        0 < orient2D (S (cyc.toFun ig)) (S (cyc.toFun io')) v) ∨
       (0 < orient2D (S (cyc.toFun io')) (S (cyc.toFun ig)) (S (cyc.toFun io)) ∧
        0 < orient2D (S (cyc.toFun io')) (S (cyc.toFun ig)) v ∧
        0 < orient2D (S (cyc.toFun ig)) (S (cyc.toFun io)) v)) := by
  have hoo' : io ≠ io' := fun h => by subst h; exact AngleLt.irrefl v q _ h_ang
  have h_even_size : (m + 3) % 2 = 0 := by omega
  have hnf_io : 0 < orient2D (S (cyc.toFun (io - 1))) (S (cyc.toFun io)) v ∨
      0 < orient2D (S (cyc.toFun io)) (S (cyc.toFun (io + 1))) v := by
    by_contra hboth; push Not at hboth
    apply h_odd_nf io ho
    rw [isFrontVertexOf_iff_ccwCycle cyc io v]
    have h1 := hv_noncol (io - 1) io (fin_sub_one_ne_self io)
    have h2 := hv_noncol io (io + 1) (fin_add_one_ne_self io)
    exact ⟨lt_of_le_of_ne hboth.1 h1, lt_of_le_of_ne hboth.2 h2⟩
  have hnf_io' : 0 < orient2D (S (cyc.toFun (io' - 1))) (S (cyc.toFun io')) v ∨
      0 < orient2D (S (cyc.toFun io')) (S (cyc.toFun (io' + 1))) v := by
    by_contra hboth; push Not at hboth
    apply h_odd_nf io' ho'
    rw [isFrontVertexOf_iff_ccwCycle cyc io' v]
    have h1 := hv_noncol (io' - 1) io' (fin_sub_one_ne_self io')
    have h2 := hv_noncol io' (io' + 1) (fin_add_one_ne_self io')
    exact ⟨lt_of_le_of_ne hboth.1 h1, lt_of_le_of_ne hboth.2 h2⟩
  have hfar := farChain_path_between cyc v q hv_noncol hvq io io' hoo' h_ang.1 hnf_io hnf_io'
  have h_even_sub : ∀ (u w : Fin (m + 3)), u.val % 2 = 1 → w.val % 2 = 1 → (w - u).val % 2 = 0 := by
    intro u w hu hw
    rw [fin_val_sub_eq]
    split_ifs with hle
    · have : u.val ≤ w.val := Fin.le_def.mp hle; omega
    · have : w.val < u.val := Fin.lt_def.mp (lt_of_not_ge hle); omega
  -- Split on `orient2D v q (S (cyc.toFun io))` sign:
  rcases lt_or_gt_of_ne (hvq io) with hq_neg | hq_pos
  · have hq_neg' : orient2D v q (S (cyc.toFun io')) < 0 := by
      have := h_ang.1; unfold OnSameSide at this; nlinarith
    have h_arc_o'o : (∀ t : ℕ, t < (io - io').val →
          0 < orient2D (S (cyc.toFun (io' + finNat (m + 3) t)))
                       (S (cyc.toFun (io' + finNat (m + 3) t + 1))) v) ∧
        (∀ t : ℕ, t ≤ (io - io').val →
          OnSameSide v q (S (cyc.toFun io')) (S (cyc.toFun (io' + finNat (m + 3) t)))) := by
      rcases hfar with h1 | h2
      · exfalso
        have hmono := (farChain_arc_angle_monotone cyc v q io io' h1.1 h1.2).2 hq_neg
        have hpos : 0 < (io' - io).val := Nat.pos_of_ne_zero (fun h => hoo' (sub_eq_zero.mp (Fin.ext h)).symm)
        have hbad := hmono 0 (io' - io).val hpos le_rfl
        have heq : io + finNat (m + 3) (io' - io).val = io' := by
          have : finNat (m + 3) (io' - io).val = io' - io := by ext; exact Nat.mod_eq_of_lt (io' - io).isLt
          rw [this, add_sub_cancel]
        rw [finNat_zero, add_zero, heq] at hbad
        exact h_ang.asymm hbad
      · exact ⟨h2.1, fun t ht => h_ang.1.symm.trans (h2.2 t ht)⟩
    have hdiff_pos : 0 < (io - io').val := Nat.pos_of_ne_zero (fun h => hoo' (sub_eq_zero.mp (Fin.ext h)))
    have hdiff_even := h_even_sub io' io ho' ho
    have hdiff_ge2 : 2 ≤ (io - io').val := by omega
    have hdiff_eq2 : (io - io').val = 2 := by
      by_contra hne2
      have hge4 : 4 ≤ (io - io').val := by omega
      let i'' := io' + finNat (m + 3) 2
      have h2_lt : 2 < (io - io').val := by omega
      have h_mono := (farChain_arc_angle_monotone cyc v q io' io h_arc_o'o.1 h_arc_o'o.2).2 hq_neg'
      have h_lt1 := h_mono 2 (io - io').val h2_lt le_rfl
      have h_lt2 := h_mono 0 2 (by omega) (Nat.le_of_lt h2_lt)
      have heq_io : io' + finNat (m + 3) (io - io').val = io := by
        have : finNat (m + 3) (io - io').val = io - io' := by ext; exact Nat.mod_eq_of_lt (io - io').isLt
        rw [this, add_sub_cancel]
      rw [heq_io] at h_lt1
      rw [finNat_zero, add_zero] at h_lt2
      have hi''_odd : i''.val % 2 = 1 := by
        have h2fin : (finNat (m + 3) 2).val = 2 := by
          dsimp [finNat]; exact Nat.mod_eq_of_lt (by omega)
        have hi''_val : i''.val = (io'.val + 2) % (m + 3) := by
          dsimp [i'']; rw [Fin.val_add, h2fin]
        rw [hi''_val]
        rcases Nat.lt_or_ge (io'.val + 2) (m + 3) with hlt | hge
        · rw [Nat.mod_eq_of_lt hlt]; omega
        · have hsub : io'.val + 2 - (m + 3) < m + 3 := by
            have := io'.isLt; omega
          rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt hsub]; omega
      have hss_i'' : OnSameSide v q (S (cyc.toFun io)) (S (cyc.toFun i'')) :=
        h_ang.1.trans (h_arc_o'o.2 2 (Nat.le_of_lt h2_lt))
      exact h_consec i'' hi''_odd hss_i'' ⟨h_lt1, h_lt2⟩
    let ig := io' + 1
    have h1_lt : 1 < (io - io').val := by omega
    have hig_eq : io' + finNat (m + 3) 1 = ig := by
      have : finNat (m + 3) 1 = 1 := by ext; simp [finNat, Nat.mod_eq_of_lt (by omega : 1 < m + 3)]
      rw [this]
    have h2_eq : io' + finNat (m + 3) 2 = io := by
      have hfn : finNat (m + 3) 2 = io - io' := by
        ext; simp [finNat, Nat.mod_eq_of_lt (by omega : 2 < m + 3), hdiff_eq2]
      rw [hfn, add_sub_cancel]
    have h_next : ig + 1 = io := by
      have h12 : finNat (m + 3) 2 = 1 + 1 := by
        ext; simp [finNat, Fin.val_add, Nat.mod_eq_of_lt (by omega : 1 < m + 3), Nat.mod_eq_of_lt (by omega : 2 < m + 3)]
      rwa [h12, ← add_assoc] at h2_eq
    have hig_even : ig.val % 2 = 0 := by
      dsimp [ig]; rw [fin_succ_val_parity h_even_size io']; omega
    have hnf0 : 0 < orient2D (S (cyc.toFun io')) (S (cyc.toFun ig)) v := by
      simpa [finNat_zero, add_zero, hig_eq] using h_arc_o'o.1 0 hdiff_pos
    have hnf1 : 0 < orient2D (S (cyc.toFun ig)) (S (cyc.toFun io)) v := by
      have := h_arc_o'o.1 1 h1_lt
      rwa [hig_eq, h_next] at this
    have hback : IsBackVertexOf S C (cyc.toFun ig) v := by
      rw [isBackVertexOf_iff_ccwCycle cyc ig v]
      have hgm1 : ig - 1 = io' := by dsimp [ig]; abel
      rw [hgm1, h_next]; exact ⟨hnf0, hnf1⟩
    have h_mono := (farChain_arc_angle_monotone cyc v q io' io h_arc_o'o.1 h_arc_o'o.2).2 hq_neg'
    have hlt1 := h_mono 1 2 (by omega) (by omega)
    have hlt2 := h_mono 0 1 (by omega) (by omega)
    rw [hig_eq, h2_eq] at hlt1
    rw [hig_eq, finNat_zero, add_zero] at hlt2
    have hig_diff : (ig - io').val = 1 := by
      dsimp [ig]; rw [add_sub_cancel_left]
      exact Nat.mod_eq_of_lt (show 1 < m + 3 by omega)
    have hccw := ccwCycle_ccw3 cyc (by omega : 0 < (ig - io').val) (by omega : (ig - io').val < (io - io').val)
    exact ⟨ig, hig_even, Or.inr ⟨rfl, h_next⟩, hback, hlt1, hlt2, Or.inr ⟨hccw, hnf0, hnf1⟩⟩
  · have h_arc_oo' : (∀ t : ℕ, t < (io' - io).val →
          0 < orient2D (S (cyc.toFun (io + finNat (m + 3) t)))
                       (S (cyc.toFun (io + finNat (m + 3) t + 1))) v) ∧
        (∀ t : ℕ, t ≤ (io' - io).val →
          OnSameSide v q (S (cyc.toFun io)) (S (cyc.toFun (io + finNat (m + 3) t)))) := by
      rcases hfar with h1 | h2
      · exact h1
      · exfalso
        have hq_pos' : 0 < orient2D v q (S (cyc.toFun io')) := by
          have := h_ang.1; unfold OnSameSide at this; nlinarith
        have hmono := (farChain_arc_angle_monotone cyc v q io' io h2.1 (fun t ht => h_ang.1.symm.trans (h2.2 t ht))).1 hq_pos'
        have hpos : 0 < (io - io').val := Nat.pos_of_ne_zero (fun h => hoo' (sub_eq_zero.mp (Fin.ext h)))
        have hbad := hmono 0 (io - io').val hpos le_rfl
        have heq : io' + finNat (m + 3) (io - io').val = io := by
          have : finNat (m + 3) (io - io').val = io - io' := by ext; exact Nat.mod_eq_of_lt (io - io').isLt
          rw [this, add_sub_cancel]
        rw [finNat_zero, add_zero, heq] at hbad
        exact h_ang.asymm hbad
    have hdiff_pos : 0 < (io' - io).val := Nat.pos_of_ne_zero (fun h => hoo' (sub_eq_zero.mp (Fin.ext h)).symm)
    have hdiff_even := h_even_sub io io' ho ho'
    have hdiff_ge2 : 2 ≤ (io' - io).val := by omega
    have hdiff_eq2 : (io' - io).val = 2 := by
      by_contra hne2
      have hge4' : 4 ≤ (io' - io).val := by omega
      let i'' := io + finNat (m + 3) 2
      have h2_lt : 2 < (io' - io).val := by omega
      have h_mono := (farChain_arc_angle_monotone cyc v q io io' h_arc_oo'.1 h_arc_oo'.2).1 hq_pos
      have h_lt1 := h_mono 0 2 (by omega) (Nat.le_of_lt h2_lt)
      have h_lt2 := h_mono 2 (io' - io).val h2_lt le_rfl
      have heq_io' : io + finNat (m + 3) (io' - io).val = io' := by
        have : finNat (m + 3) (io' - io).val = io' - io := by ext; exact Nat.mod_eq_of_lt (io' - io).isLt
        rw [this, add_sub_cancel]
      rw [finNat_zero, add_zero] at h_lt1
      rw [heq_io'] at h_lt2
      have hi''_odd : i''.val % 2 = 1 := by
        have h2fin : (finNat (m + 3) 2).val = 2 := by
          dsimp [finNat]; exact Nat.mod_eq_of_lt (by omega)
        have hi''_val : i''.val = (io.val + 2) % (m + 3) := by
          dsimp [i'']; rw [Fin.val_add, h2fin]
        rw [hi''_val]
        rcases Nat.lt_or_ge (io.val + 2) (m + 3) with hlt | hge
        · rw [Nat.mod_eq_of_lt hlt]; omega
        · have hsub : io.val + 2 - (m + 3) < m + 3 := by
            have := io.isLt; omega
          rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt hsub]; omega
      have hss_i'' : OnSameSide v q (S (cyc.toFun io)) (S (cyc.toFun i'')) :=
        h_arc_oo'.2 2 (Nat.le_of_lt h2_lt)
      exact h_consec i'' hi''_odd hss_i'' ⟨h_lt1, h_lt2⟩
    let ig := io + 1
    have h1_lt : 1 < (io' - io).val := by omega
    have hig_eq : io + finNat (m + 3) 1 = ig := by
      have : finNat (m + 3) 1 = 1 := by ext; simp [finNat, Nat.mod_eq_of_lt (by omega : 1 < m + 3)]
      rw [this]
    have h2_eq : io + finNat (m + 3) 2 = io' := by
      have hfn : finNat (m + 3) 2 = io' - io := by
        ext; simp [finNat, Nat.mod_eq_of_lt (by omega : 2 < m + 3), hdiff_eq2]
      rw [hfn, add_sub_cancel]
    have h_next : ig + 1 = io' := by
      have h12 : finNat (m + 3) 2 = 1 + 1 := by
        ext; simp [finNat, Fin.val_add, Nat.mod_eq_of_lt (by omega : 1 < m + 3), Nat.mod_eq_of_lt (by omega : 2 < m + 3)]
      rwa [h12, ← add_assoc] at h2_eq
    have hig_even : ig.val % 2 = 0 := by
      dsimp [ig]; rw [fin_succ_val_parity h_even_size io]; omega
    have hnf0 : 0 < orient2D (S (cyc.toFun io)) (S (cyc.toFun ig)) v := by
      simpa [finNat_zero, add_zero, hig_eq] using h_arc_oo'.1 0 hdiff_pos
    have hnf1 : 0 < orient2D (S (cyc.toFun ig)) (S (cyc.toFun io')) v := by
      have := h_arc_oo'.1 1 h1_lt
      rwa [hig_eq, h_next] at this
    have hback : IsBackVertexOf S C (cyc.toFun ig) v := by
      rw [isBackVertexOf_iff_ccwCycle cyc ig v]
      have hgm1 : ig - 1 = io := by dsimp [ig]; abel
      rw [hgm1, h_next]; exact ⟨hnf0, hnf1⟩
    have h_mono := (farChain_arc_angle_monotone cyc v q io io' h_arc_oo'.1 h_arc_oo'.2).1 hq_pos
    have hlt1 := h_mono 0 1 (by omega) (by omega)
    have hlt2 := h_mono 1 2 (by omega) (by omega)
    rw [hig_eq, finNat_zero, add_zero] at hlt1
    rw [hig_eq, h2_eq] at hlt2
    have hig_diff : (ig - io).val = 1 := by
      dsimp [ig]; rw [add_sub_cancel_left]
      exact Nat.mod_eq_of_lt (show 1 < m + 3 by omega)
    have hccw := ccwCycle_ccw3 cyc (by omega : 0 < (ig - io).val) (by omega : (ig - io).val < (io' - io).val)
    exact ⟨ig, hig_even, Or.inl ⟨rfl, h_next⟩, hback, hlt1, hlt2, Or.inl ⟨hccw, hnf0, hnf1⟩⟩








/-! ## Part 6c: Subcycle Construction, `GoodAnchorPair`, Prop 6.4 (`good_targets`), and Prop 6.5 (`gap_lemma`) -/

/-- Any subsequence of indices strictly increasing in cyclic offset `(idx r - idx 0).val`
    on a `CCWCycle S D kD` forms a `CCWCycle S C m`. -/
def ccwCycle_of_subseq {n kD m : ℕ} {S : Fin n → ℝ × ℝ} {D : Finset (Fin n)}
    (cycD : CCWCycle S D kD) (idx : Fin (m + 3) → Fin (kD + 3))
    (h_strict : ∀ a b : Fin (m + 3), a < b → (idx a - idx 0).val < (idx b - idx 0).val) :
    CCWCycle S (Finset.univ.image (fun r => cycD.toFun (idx r))) m := by
  have h_inj_idx : Function.Injective idx := by
    intro a b hab
    rcases lt_trichotomy a b with h | rfl | h
    · exfalso; have := h_strict a b h; rw [hab] at this; exact Nat.lt_irrefl _ this
    · rfl
    · exfalso; have := h_strict b a h; rw [hab] at this; exact Nat.lt_irrefl _ this
  have h_inj : Function.Injective (fun r => cycD.toFun (idx r)) := cycD.inj.comp h_inj_idx
  have h_tri : ∀ a b c : Fin (m + 3), a < b → b < c →
      0 < orient2D (S (cycD.toFun (idx a))) (S (cycD.toFun (idx b))) (S (cycD.toFun (idx c))) := by
    intro a b c hab hbc
    by_cases ha0 : a = 0
    · subst ha0
      have hb_pos : 0 < (idx b - idx 0).val := by
        have := h_strict 0 b hab; simpa using this
      have hbc_lt : (idx b - idx 0).val < (idx c - idx 0).val := h_strict b c hbc
      exact ccwCycle_ccw3 cycD hb_pos hbc_lt
    · have ha_pos : 0 < (idx a - idx 0).val := by
        have := h_strict 0 a (Fin.pos_of_ne_zero ha0); simpa using this
      have hab_lt : (idx a - idx 0).val < (idx b - idx 0).val := h_strict a b hab
      have hac_lt : (idx a - idx 0).val < (idx c - idx 0).val := h_strict a c (lt_trans hab hbc)
      have ⟨hsba, hba_pos⟩ := fin_sub_split_lt ha_pos hab_lt
      have ⟨hsca, _⟩ := fin_sub_split_lt ha_pos hac_lt
      have hbc_lt_idx : (idx b - idx a).val < (idx c - idx a).val := by
        have := h_strict b c hbc; omega
      exact ccwCycle_ccw3 cycD hba_pos hbc_lt_idx
  refine ⟨fun r => cycD.toFun (idx r), h_inj, rfl, ?_, h_tri⟩
  intro i j hij1 hij2
  have h1_val : (1 : Fin (m + 3)).val = 1 := Nat.mod_eq_of_lt (show 1 < m + 3 by omega)
  by_cases hi_last : i.val + 1 = m + 3
  · have hi1 : i + 1 = 0 := by
      ext; rw [Fin.val_add, h1_val, hi_last, Nat.mod_self]; rfl
    have hj0 : 0 < j := Fin.pos_of_ne_zero (fun h => hij2 (hi1 ▸ h))
    have hji : j < i := by
      have : i.val = m + 2 := by omega
      exact lt_of_le_of_ne (Fin.le_def.mpr (by rw [this]; exact Nat.le_of_lt_succ j.isLt)) hij1
    have h := h_tri 0 j i hj0 hji
    dsimp [Function.comp]
    rw [hi1, ← orient2D_cycle]; exact h
  · have hi1_val : (i + 1).val = i.val + 1 := by
      rw [Fin.val_add, h1_val, Nat.mod_eq_of_lt (by omega)]
    have hi_lt : i < i + 1 := Fin.lt_def.mpr (by rw [hi1_val]; omega)
    rcases lt_trichotomy j i with hji | rfl | hij
    · have h := h_tri j i (i + 1) hji hi_lt
      dsimp [Function.comp]; rw [orient2D_cycle]; exact h
    · exact False.elim (hij1 rfl)
    · have hi1_lt_j : i + 1 < j :=
        lt_of_le_of_ne (Fin.le_def.mpr (by rw [hi1_val]; exact Fin.lt_def.mp hij)) hij2.symm
      exact h_tri i (i + 1) j hi_lt hi1_lt_j

/-- Good anchor cone condition for `O_miss` and anchors `{a_p, c_p}`:
    `a_p, c_p ∈ O_miss` lie on one open side of `G = v q` with `cond4` for `half_plane_lemma`. -/
def GoodAnchorPair {n : ℕ} (P : Set (ℝ × ℝ)) (S : Fin n → ℝ × ℝ)
    (w : Finset (Fin n) → ℝ × ℝ) (O_miss : Finset (Fin n)) (a_p c_p : Fin n) : Prop :=
  let v := w (Finset.univ \ O_miss)
  let q := w Finset.univ
  a_p ∈ O_miss ∧ c_p ∈ O_miss ∧ a_p ≠ c_p ∧
  ((AngleLt v q (S a_p) (S c_p) ∧
    (Sees P v q ∨ ∃ e : Fin n, e ∉ O_miss ∧ AngleLt v q (S e) (S a_p))) ∨
   (AngleLt v q (S c_p) (S a_p) ∧
    (Sees P v q ∨ ∃ e : Fin n, e ∉ O_miss ∧ AngleLt v q (S e) (S c_p))))

lemma goodAnchorPair_symm {n : ℕ} {P : Set (ℝ × ℝ)} {S : Fin n → ℝ × ℝ}
    {w : Finset (Fin n) → ℝ × ℝ} {O_miss : Finset (Fin n)} {a_p c_p : Fin n}
    (h : GoodAnchorPair P S w O_miss a_p c_p) : GoodAnchorPair P S w O_miss c_p a_p := by
  rcases h with ⟨ha, hc, hne, hdir⟩
  refine ⟨hc, ha, hne.symm, ?_⟩
  rcases hdir with h1 | h2
  · exact Or.inr h1
  · exact Or.inl h2

/-- Universal crossing application from a `GoodAnchorPair`. -/
lemma goodAnchorPair_universal_crossing {n : ℕ} {P : Set (ℝ × ℝ)}
    {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ}
    (hPoly : ShatteredSimplePolygon P S w) (h25 : Sec2To5Interface P S w)
    {O_miss : Finset (Fin n)} {a_p c_p : Fin n}
    (hgap : GoodAnchorPair P S w O_miss a_p c_p)
    {z : Fin n} (hz : z ∉ O_miss)
    (hcross : SegmentsCross (w (Finset.univ \ O_miss)) (S z) (S a_p) (S c_p)) :
    (∃ H_hp : OpenHalfPlane, IsHalfPlaneTest P (WitnessSet {a_p, c_p} ∅ w) (S z) H_hp) ∧
    (z ∈ hullVertices S → IsBackVertexOf S (hullVertices S) z (w (Finset.univ \ O_miss))) := by
  rcases hgap with ⟨haO, hcO, _, ⟨hang, hcond4⟩ | ⟨hang, hcond4⟩⟩
  · have haT : a_p ∉ Finset.univ \ O_miss := fun h => (Finset.mem_sdiff.mp h).2 haO
    have hcT : c_p ∉ Finset.univ \ O_miss := fun h => (Finset.mem_sdiff.mp h).2 hcO
    have hzT : z ∈ Finset.univ \ O_miss := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hz⟩
    have h4 : Sees P (w (Finset.univ \ O_miss)) (w Finset.univ) ∨
        ∃ e : Fin n, e ∈ Finset.univ \ O_miss ∧ e ∈ Finset.univ ∧
          AngleLt (w (Finset.univ \ O_miss)) (w Finset.univ) (S e) (S a_p) := by
      rcases hcond4 with h | ⟨e, he, hlt⟩
      · exact Or.inl h
      · exact Or.inr ⟨e, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, he⟩, Finset.mem_univ _, hlt⟩
    exact universal_crossing hPoly h25 haT hcT (Finset.mem_univ a_p) (Finset.mem_univ c_p)
      hang h4 hzT (Finset.mem_univ z) hcross
  · have haT : a_p ∉ Finset.univ \ O_miss := fun h => (Finset.mem_sdiff.mp h).2 haO
    have hcT : c_p ∉ Finset.univ \ O_miss := fun h => (Finset.mem_sdiff.mp h).2 hcO
    have hzT : z ∈ Finset.univ \ O_miss := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hz⟩
    have h4 : Sees P (w (Finset.univ \ O_miss)) (w Finset.univ) ∨
        ∃ e : Fin n, e ∈ Finset.univ \ O_miss ∧ e ∈ Finset.univ ∧
          AngleLt (w (Finset.univ \ O_miss)) (w Finset.univ) (S e) (S c_p) := by
      rcases hcond4 with h | ⟨e, he, hlt⟩
      · exact Or.inl h
      · exact Or.inr ⟨e, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, he⟩, Finset.mem_univ _, hlt⟩
    have hres := universal_crossing hPoly h25 hcT haT (Finset.mem_univ c_p) (Finset.mem_univ a_p)
      hang h4 hzT (Finset.mem_univ z) hcross.symm34
    have hset : ({c_p, a_p} : Finset (Fin n)) = {a_p, c_p} := by ext x; simp [or_comm]
    rwa [hset] at hres

/-- If `GoodAnchorPair P S w O_miss a_p c_p` holds and every vertex `g ∈ CapPts` either equals
    `a_p`, `c_p`, or satisfies `SegmentsCross v (S g) (S a_p) (S c_p)`, then every `z ∉ O_miss`
    in `conv(CapPts)` (`z ≠ a_p, z ≠ c_p`) satisfies `SegmentsCross` and hence gets a half-plane test
    on `WitnessSet {a_p, c_p} ∅ w` (and back vertex of `B` if `z ∈ B`). -/
lemma cap_crossing_of_vertices_cross {n : ℕ} {P : Set (ℝ × ℝ)}
    {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ}
    (hPoly : ShatteredSimplePolygon P S w) (h25 : Sec2To5Interface P S w)
    {O_miss : Finset (Fin n)} {a_p c_p : Fin n}
    (hgap : GoodAnchorPair P S w O_miss a_p c_p)
    (CapPts : Finset (Fin n))
    (hCap : ∀ g ∈ CapPts, g = a_p ∨ g = c_p ∨
      SegmentsCross (w (Finset.univ \ O_miss)) (S g) (S a_p) (S c_p))
    {z : Fin n} (hz : z ∉ O_miss) (hza : z ≠ a_p) (hzc : z ≠ c_p)
    (hz_conv : S z ∈ convexHull ℝ (CapPts.image S : Set (ℝ × ℝ))) :
    SegmentsCross (w (Finset.univ \ O_miss)) (S z) (S a_p) (S c_p) ∧
    (∃ H_hp : OpenHalfPlane, IsHalfPlaneTest P (WitnessSet {a_p, c_p} ∅ w) (S z) H_hp) ∧
    (z ∈ hullVertices S → IsBackVertexOf S (hullVertices S) z (w (Finset.univ \ O_miss))) := by
  let v := w (Finset.univ \ O_miss)
  let q := w Finset.univ
  have hac : a_p ≠ c_p := hgap.2.2.1
  have hzv_col : orient2D v (S a_p) (S z) ≠ 0 ∧ orient2D v (S c_p) (S z) ≠ 0 ∧
      orient2D (S a_p) (S c_p) (S z) ≠ 0 :=
    ⟨hPoly.no_three_collinear _ _ _
        (Or.inr (Set.mem_range_self _)) (Or.inl (Set.mem_range_self _)) (Or.inl (Set.mem_range_self _))
        (hPoly.s_ne_w _ _).symm (hPoly.s_inj.ne hza.symm) (hPoly.s_ne_w _ _).symm,
     hPoly.no_three_collinear _ _ _
        (Or.inr (Set.mem_range_self _)) (Or.inl (Set.mem_range_self _)) (Or.inl (Set.mem_range_self _))
        (hPoly.s_ne_w _ _).symm (hPoly.s_inj.ne hzc.symm) (hPoly.s_ne_w _ _).symm,
     hPoly.no_three_collinear _ _ _
        (Or.inl (Set.mem_range_self _)) (Or.inl (Set.mem_range_self _)) (Or.inl (Set.mem_range_self _))
        (hPoly.s_inj.ne hac) (hPoly.s_inj.ne hzc.symm) (hPoly.s_inj.ne hza.symm)⟩
  have haux : ∀ {ap cp : Fin n}, ap ≠ cp → AngleLt v q (S ap) (S cp) →
      (∀ g ∈ CapPts, g = ap ∨ g = cp ∨ SegmentsCross v (S g) (S ap) (S cp)) →
      orient2D v (S ap) (S z) ≠ 0 → orient2D v (S cp) (S z) ≠ 0 → orient2D (S ap) (S cp) (S z) ≠ 0 →
      SegmentsCross v (S z) (S ap) (S cp) := by
    intro ap cp _ hang hC haz hcz hacz
    refine cap_convex_crossing hang (CapPts.image S : Set (ℝ × ℝ)) (fun y hy => ?_) hz_conv haz hcz hacz
    rcases Finset.mem_image.mp hy with ⟨g, hgC, rfl⟩
    rcases hC g hgC with rfl | rfl | hcross
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · right; right
      rcases hang with ⟨hsac, hoac⟩
      rcases hcross with ⟨h1, h2⟩
      have hid := orient2D_barycentric_sum v (S ap) (S cp) (S g)
      have h_eq1 : orient2D (S ap) (S cp) v = orient2D v (S ap) (S cp) := by unfold orient2D; ring
      have h_eq2 : orient2D v (S g) (S ap) = -orient2D v (S ap) (S g) := by unfold orient2D; ring
      have h_eq3 : orient2D v (S g) (S cp) = orient2D (S cp) v (S g) := by unfold orient2D; ring
      have hvq_ne : orient2D v q (S ap) ≠ 0 := fun h => by rw [h, zero_mul] at hoac; linarith
      rcases lt_or_gt_of_ne hvq_ne with hqa | hqa
      · have hvapcp : orient2D v (S ap) (S cp) < 0 := by nlinarith
        have hv_pos : orient2D (S ap) (S cp) v < 0 := by linarith
        have hg_pos : 0 < orient2D (S ap) (S cp) (S g) := by nlinarith
        have h_opp : orient2D v (S ap) (S g) < 0 ∧ orient2D (S cp) v (S g) < 0 := by
          by_contra hnot
          have hpos_one : 0 ≤ orient2D v (S ap) (S g) ∨ 0 ≤ orient2D (S cp) v (S g) := by
            by_contra hneg; push Not at hneg; exact hnot ⟨hneg.1, hneg.2⟩
          rcases hpos_one with ha1 | hc1
          · have hneq : orient2D v (S g) (S ap) ≤ 0 := by linarith
            have hc2 : 0 ≤ orient2D v (S g) (S cp) := by
              by_contra hc_lt
              have hc_neg : orient2D v (S g) (S cp) < 0 := not_le.mp hc_lt
              rcases eq_or_lt_of_le ha1 with ha0 | ha_pos
              · have : orient2D v (S g) (S ap) = 0 := by linarith [h_eq2, ha0]
                rw [this, zero_mul] at h1; linarith
              · have : 0 < orient2D v (S g) (S ap) * orient2D v (S g) (S cp) :=
                  mul_pos_of_neg_of_neg (by linarith) hc_neg
                linarith
            linarith [show orient2D (S ap) (S cp) (S g) + orient2D (S cp) v (S g) + orient2D v (S ap) (S g) =
              orient2D v (S ap) (S cp) from hid]
          · have hneq : 0 ≤ orient2D v (S g) (S cp) := by linarith
            rcases eq_or_lt_of_le hc1 with hc0 | hc_pos
            · have : orient2D v (S g) (S cp) = 0 := by linarith [h_eq3, hc0]
              rw [this, mul_zero] at h1; linarith
            · have ha2 : orient2D v (S g) (S ap) < 0 := by
                by_contra ha_ge
                have := mul_nonneg (not_lt.mp ha_ge) (le_of_lt (by linarith : 0 < orient2D v (S g) (S cp)))
                linarith
              have ha_pos : 0 < orient2D v (S ap) (S g) := by linarith
              linarith [show orient2D (S ap) (S cp) (S g) + orient2D (S cp) v (S g) + orient2D v (S ap) (S g) =
                orient2D v (S ap) (S cp) from hid]
        have hvgcp : orient2D v (S g) (S cp) < 0 := by unfold orient2D at h_opp ⊢; linarith [h_opp.2]
        have hqg : orient2D v q (S g) < 0 := by
          have hidq := orient2D_angle_trans_id v q (S ap) (S g) (S cp)
          have hqc : orient2D v q (S cp) < 0 := by unfold OnSameSide at hsac; nlinarith
          have h1' : 0 < orient2D v q (S ap) * orient2D v (S g) (S cp) :=
            mul_pos_of_neg_of_neg hqa hvgcp
          have h2' : 0 < orient2D v q (S cp) * orient2D v (S ap) (S g) :=
            mul_pos_of_neg_of_neg hqc h_opp.1
          by_contra hge
          have hge' : 0 ≤ orient2D v q (S g) := not_lt.mp hge
          have : 0 ≤ orient2D v q (S g) * orient2D v (S ap) (S cp) := by
            have := mul_nonneg hge' (by linarith : 0 ≤ -orient2D v (S ap) (S cp))
            nlinarith
          nlinarith [mul_nonneg hge' (le_of_lt (by linarith : 0 < -orient2D v (S ap) (S cp)))]
        refine ⟨by unfold OnSameSide; exact mul_pos_of_neg_of_neg hqa hqg,
          fun hbad => False.elim (by linarith),
          fun _ => ⟨le_of_lt h_opp.1, le_of_lt hvgcp, le_of_lt h2⟩⟩
      · have hvapcp : 0 < orient2D v (S ap) (S cp) := by nlinarith
        have hv_pos : 0 < orient2D (S ap) (S cp) v := by linarith
        have hg_neg : orient2D (S ap) (S cp) (S g) < 0 := by nlinarith
        have h_opp : 0 < orient2D v (S ap) (S g) ∧ 0 < orient2D (S cp) v (S g) := by
          by_contra hnot
          have hneg_one : orient2D v (S ap) (S g) ≤ 0 ∨ orient2D (S cp) v (S g) ≤ 0 := by
            by_contra hpos; push Not at hpos; exact hnot ⟨hpos.1, hpos.2⟩
          rcases hneg_one with ha1 | hc1
          · rcases eq_or_lt_of_le ha1 with ha0 | ha_neg
            · have : orient2D v (S g) (S ap) = 0 := by linarith [h_eq2, ha0]
              rw [this, zero_mul] at h1; linarith
            · have : orient2D v (S g) (S cp) < 0 := by
                by_contra hc_ge
                have := mul_nonneg (le_of_lt (by linarith : 0 < orient2D v (S g) (S ap))) (not_lt.mp hc_ge)
                linarith
              linarith [show orient2D (S ap) (S cp) (S g) + orient2D (S cp) v (S g) + orient2D v (S ap) (S g) =
                orient2D v (S ap) (S cp) from hid]
          · rcases eq_or_lt_of_le hc1 with hc0 | hc_neg
            · rw [hc0] at h_eq3; rw [h_eq3, mul_zero] at h1; linarith
            · have : 0 < orient2D v (S g) (S ap) := by
                by_contra ha_le
                have := mul_nonneg (by linarith : 0 ≤ -orient2D v (S g) (S ap)) (by linarith : 0 ≤ -orient2D v (S g) (S cp))
                nlinarith
              linarith [show orient2D (S ap) (S cp) (S g) + orient2D (S cp) v (S g) + orient2D v (S ap) (S g) =
                orient2D v (S ap) (S cp) from hid]
        have hvgcp : 0 < orient2D v (S g) (S cp) := by unfold orient2D at h_opp ⊢; linarith [h_opp.2]
        have hqg : 0 < orient2D v q (S g) := by
          have hidq := orient2D_angle_trans_id v q (S ap) (S g) (S cp)
          have hqc : 0 < orient2D v q (S cp) := by unfold OnSameSide at hsac; nlinarith
          have h1' : 0 < orient2D v q (S ap) * orient2D v (S g) (S cp) := mul_pos hqa hvgcp
          have h2' : 0 < orient2D v q (S cp) * orient2D v (S ap) (S g) := mul_pos hqc h_opp.1
          by_contra hle
          have hle' : orient2D v q (S g) ≤ 0 := not_lt.mp hle
          nlinarith [mul_nonpos_of_nonpos_of_nonneg hle' (le_of_lt hvapcp)]
        refine ⟨by unfold OnSameSide; exact mul_pos hqa hqg,
          fun _ => ⟨le_of_lt h_opp.1, le_of_lt hvgcp, le_of_lt h2⟩,
          fun hbad => False.elim (by linarith)⟩
  have hcross_z : SegmentsCross v (S z) (S a_p) (S c_p) := by
    rcases hgap with ⟨_, _, _, ⟨hang, _⟩ | ⟨hang, _⟩⟩
    · exact haux hac hang hCap hzv_col.1 hzv_col.2.1 hzv_col.2.2
    · exact (haux hac.symm hang (fun g hg => by
        rcases hCap g hg with rfl | rfl | hc
        · exact Or.inr (Or.inl rfl)
        · exact Or.inl rfl
        · exact Or.inr (Or.inr hc.symm34)) hzv_col.2.1 hzv_col.1 (by unfold orient2D at hzv_col ⊢; exact fun h => hzv_col.2.2 (by linarith))).symm34
  exact ⟨hcross_z, goodAnchorPair_universal_crossing hPoly h25 hgap hz hcross_z⟩

/-- Helper for certifying an even front vertex `f ∈ D` from odd `o1, o2 ∈ B` when `¬ Sees P v q`
    and `v ∈ IntTri(q, o1, o2)` and `v ∈ IntTri(o1, o2, f)`. -/
lemma contradict_cert_even_front {n : ℕ} {P : Set (ℝ × ℝ)}
    {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ}
    (hPoly : ShatteredSimplePolygon P S w) (h25 : Sec2To5Interface P S w)
    {O_miss : Finset (Fin n)} {f o1 o2 : Fin n}
    (hfD : f ∈ hullVertices S \ certifiedVertices S w)
    (ho1B : o1 ∈ hullVertices S) (ho2B : o2 ∈ hullVertices S)
    (ho1f : o1 ≠ f) (ho2f : o2 ≠ f) (ho12 : o1 ≠ o2)
    (hf_Tv : f ∉ O_miss)
    (hq_miss : ¬ Sees P (w (Finset.univ \ O_miss)) (w Finset.univ))
    (hf_tri : InIntTri (w (Finset.univ \ O_miss)) (S o1) (S o2) (S f))
    (hv_tri : InIntTri (w Finset.univ) (S o1) (S o2) (w (Finset.univ \ O_miss))) :
    False := by
  let B := hullVertices S
  let Tv := Finset.univ \ O_miss
  let v := w Tv
  let q := w Finset.univ
  let Tz := Finset.univ.erase f
  have hTTz : Tv ≠ Tz := by
    intro h
    have hf1 : f ∈ Tv := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hf_Tv⟩
    rw [h] at hf1
    exact Finset.notMem_erase f Finset.univ hf1
  have ho1_Tz : o1 ∈ Tz := Finset.mem_erase.mpr ⟨ho1f, Finset.mem_univ _⟩
  have ho2_Tz : o2 ∈ Tz := Finset.mem_erase.mpr ⟨ho2f, Finset.mem_univ _⟩
  have hqv_miss : ¬ Sees P q v := fun h => hq_miss (sees_symm h)
  have hv_cone : InIntTri (w Tz) (S o1) (S o2) v := by
    by_cases hqTz : Finset.univ = Tz
    · exfalso; exact Finset.notMem_erase f Finset.univ (by
        change f ∈ Finset.univ.erase f
        change f ∈ Tz
        rw [← hqTz]; exact Finset.mem_univ f)
    · apply h25.cone_lemma v (S o1) (S o2) q (w Tz)
        (hPoly.w_in_P _) (hPoly.s_in_P _) (hPoly.s_in_P _) (hPoly.w_in_P _) (hPoly.w_in_P _)
      · exact (hPoly.shatters Finset.univ o1).mpr (Finset.mem_univ _)
      · exact (hPoly.shatters Finset.univ o2).mpr (Finset.mem_univ _)
      · exact hqv_miss
      · exact hv_tri
      · exact (hPoly.shatters Tz o1).mpr ho1_Tz
      · exact (hPoly.shatters Tz o2).mpr ho2_Tz
      · exact hPoly.no_three_collinear _ _ _
          (Or.inr (Set.mem_range_self _)) (Or.inl (Set.mem_range_self _)) (Or.inr (Set.mem_range_self _))
          (hPoly.s_ne_w _ _).symm (hPoly.s_ne_w _ _) (hPoly.w_inj.ne hTTz)
      · exact hPoly.no_three_collinear _ _ _
          (Or.inr (Set.mem_range_self _)) (Or.inl (Set.mem_range_self _)) (Or.inr (Set.mem_range_self _))
          (hPoly.s_ne_w _ _).symm (hPoly.s_ne_w _ _) (hPoly.w_inj.ne hTTz)
      · exact hPoly.no_three_collinear _ _ _
          (Or.inr (Set.mem_range_self _)) (Or.inr (Set.mem_range_self _)) (Or.inr (Set.mem_range_self _))
          (hPoly.w_inj.ne (fun h => hq_miss (by
            have hw_eq : w (Finset.univ \ O_miss) = w Finset.univ := congrArg w h.symm
            rw [hw_eq]
            exact sees_refl (hPoly.w_in_P Finset.univ))))
          (hPoly.w_inj.ne hTTz) (hPoly.w_inj.ne hqTz)
  have hf_cone : InIntTri (w Tz) (S o1) (S o2) (S f) := by
    rcases hv_cone with ⟨a1, a2, a3, ha1, ha2, ha3, hasum, hv1, hv2⟩
    rcases hf_tri with ⟨b1, b2, b3, hb1, hb2, hb3, hbsum, hf1, hf2⟩
    refine ⟨b1 * a1, b2 + b1 * a2, b3 + b1 * a3, mul_pos hb1 ha1, by linarith [mul_pos hb1 ha2],
      by linarith [mul_pos hb1 ha3], ?_, ?_, ?_⟩
    · calc b1 * a1 + (b2 + b1 * a2) + (b3 + b1 * a3) = b1 * (a1 + a2 + a3) + b2 + b3 := by ring
        _ = 1 := by rw [hasum]; linarith
    · rw [hf1, hv1]; ring
    · rw [hf2, hv2]; ring
  let C3 : Finset (Fin n) := {o1, f, o2}
  have hC3_sub : C3 ⊆ B := fun x hx => by
    simp only [C3, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact ho1B
    · exact (Finset.mem_sdiff.mp hfD).1
    · exact ho2B
  have hC3_card : 3 ≤ C3.card := by
    have h1 : o1 ∉ ({f, o2} : Finset (Fin n)) := by simp [ho1f, ho12]
    have h2 : f ∉ ({o2} : Finset (Fin n)) := by simp [ho2f.symm]
    rw [Finset.card_insert_of_notMem h1, Finset.card_insert_of_notMem h2, Finset.card_singleton]
  have hfront_B : IsFrontVertexOf S B f (w Tz) :=
    h25.front_restoration C3 B f (w Tz) hC3_sub (hullVertices_convexPos S Subset.rfl)
      hC3_card (Set.mem_range_self Tz) (inIntTri_implies_isFrontVertexOf_tri S ho1f ho2f ho12 (w Tz) hf_cone)
  have hcert : f ∈ certifiedVertices S w := by
    refine Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hfD).1, Tz, Finset.notMem_erase _ _, ?_, ?_, hfront_B⟩
    · intro b hb; exact Finset.mem_erase.mpr ⟨hb.2.2.1, Finset.mem_univ _⟩
    · intro c hc; exact Finset.mem_erase.mpr ⟨hc.2.2.1.symm, Finset.mem_univ _⟩
  exact (Finset.mem_sdiff.mp hfD).2 hcert

/-- Enumerate all `X.card - 1` targets produced by an odd-index subset `X` lying on one open side of `vq`. -/
lemma targets_of_oddSide {n m : ℕ}
    {S : Fin n → ℝ × ℝ}
    {C : Finset (Fin n)} (hm : m % 2 = 1) (hm1 : 1 ≤ m)
    (cyc : CCWCycle S C m)
    (v q : ℝ × ℝ)
    (hv_noncol : ∀ i j : Fin (m + 3), i ≠ j → orient2D (S (cyc.toFun i)) (S (cyc.toFun j)) v ≠ 0)
    (hvq : ∀ i : Fin (m + 3), orient2D v q (S (cyc.toFun i)) ≠ 0)
    (h_odd_nf : ∀ i : Fin (m + 3), i.val % 2 = 1 → ¬ IsFrontVertexOf S C (cyc.toFun i) v)
    (X : Finset (Fin (m + 3)))
    (hX_odd : ∀ i ∈ X, i.val % 2 = 1)
    (hX_all : ∀ i : Fin (m + 3), i.val % 2 = 1 →
      (∃ o0 ∈ X, OnSameSide v q (S (cyc.toFun o0)) (S (cyc.toFun i))) → i ∈ X)
    (hX_ss : ∀ i ∈ X, ∀ j ∈ X, OnSameSide v q (S (cyc.toFun i)) (S (cyc.toFun j))) :
    ∃ f : Fin (X.card - 1) → Fin (m + 3),
      Function.Injective f ∧
      (∀ t : Fin (X.card - 1),
        (f t).val % 2 = 0 ∧
        f t - 1 ∈ X ∧ f t + 1 ∈ X ∧
        (f t - 1).val % 2 = 1 ∧ (f t + 1).val % 2 = 1 ∧
        IsBackVertexOf S C (cyc.toFun (f t)) v ∧
        OnSameSide v q (S (cyc.toFun (f t - 1))) (S (cyc.toFun (f t + 1))) ∧
        (1 ≤ t.val → ∃ t0 : Fin (X.card - 1), t0.val < t.val ∧
          AngleLt v q (S (cyc.toFun (f t0))) (S (cyc.toFun (f t - 1))) ∧
          AngleLt v q (S (cyc.toFun (f t0))) (S (cyc.toFun (f t + 1)))) ∧
        ((AngleLt v q (S (cyc.toFun (f t - 1))) (S (cyc.toFun (f t))) ∧
          AngleLt v q (S (cyc.toFun (f t))) (S (cyc.toFun (f t + 1))) ∧
          0 < orient2D (S (cyc.toFun (f t - 1))) (S (cyc.toFun (f t))) (S (cyc.toFun (f t + 1))) ∧
          0 < orient2D (S (cyc.toFun (f t - 1))) (S (cyc.toFun (f t))) v ∧
          0 < orient2D (S (cyc.toFun (f t))) (S (cyc.toFun (f t + 1))) v) ∨
         (AngleLt v q (S (cyc.toFun (f t + 1))) (S (cyc.toFun (f t))) ∧
          AngleLt v q (S (cyc.toFun (f t))) (S (cyc.toFun (f t - 1))) ∧
          0 < orient2D (S (cyc.toFun (f t - 1))) (S (cyc.toFun (f t))) (S (cyc.toFun (f t + 1))) ∧
          0 < orient2D (S (cyc.toFun (f t - 1))) (S (cyc.toFun (f t))) v ∧
          0 < orient2D (S (cyc.toFun (f t))) (S (cyc.toFun (f t + 1))) v))) ∧
      (∀ t : Fin (X.card - 1), ∀ o ∈ X, t.val = 0 →
        o = f t - 1 ∨ o = f t + 1 ∨
        (AngleLt v q (S (cyc.toFun (f t - 1))) (S (cyc.toFun o)) ∧
         AngleLt v q (S (cyc.toFun (f t + 1))) (S (cyc.toFun o)))) := by
  let r : {i : Fin (m + 3) // i ∈ X} → {i : Fin (m + 3) // i ∈ X} → Prop :=
    fun a b => a = b ∨ AngleLt v q (S (cyc.toFun a.1)) (S (cyc.toFun b.1))
  have hr_trans : IsTrans {i : Fin (m + 3) // i ∈ X} r := ⟨by
    intro a b c hab hbc
    rcases hab with rfl | hab
    · exact hbc
    · rcases hbc with rfl | hbc
      · exact Or.inr hab
      · exact Or.inr (hab.trans hbc)⟩
  have hr_anti : Std.Antisymm r := ⟨by
    intro a b hab hba
    rcases hab with rfl | hab
    · rfl
    · rcases hba with rfl | hba
      · rfl
      · exact False.elim (hab.asymm hba)⟩
  have hr_tot : Std.Total r := ⟨by
    intro a b
    by_cases hab : a = b
    · exact Or.inl (Or.inl hab)
    · have hab1 : a.1 ≠ b.1 := fun h => hab (Subtype.ext h)
      have hss := hX_ss a.1 a.2 b.1 b.2
      have hne := hv_noncol a.1 b.1 hab1
      have hne' : orient2D v (S (cyc.toFun a.1)) (S (cyc.toFun b.1)) ≠ 0 := by
        unfold orient2D at hne ⊢; intro h; apply hne; linarith
      rcases lt_or_gt_of_ne hne' with hneg | hpos
      · rcases lt_or_gt_of_ne (hvq a.1) with hqa | hqa
        · left; right; exact angleLt_of_orient_sameSide hss (fun h => False.elim (by linarith)) (fun _ => hneg)
        · right; right; refine angleLt_of_orient_sameSide hss.symm (fun _ => ?_) (fun h => ?_)
          · unfold orient2D at hneg ⊢; linarith
          · have : orient2D v q (S (cyc.toFun b.1)) < 0 := h
            unfold OnSameSide at hss; nlinarith
      · rcases lt_or_gt_of_ne (hvq a.1) with hqa | hqa
        · right; right; refine angleLt_of_orient_sameSide hss.symm (fun h => ?_) (fun _ => ?_)
          · unfold OnSameSide at hss; nlinarith
          · unfold orient2D at hpos ⊢; linarith
        · left; right; exact angleLt_of_orient_sameSide hss (fun _ => hpos) (fun h => False.elim (by linarith))⟩
  let lst : List {i : Fin (m + 3) // i ∈ X} := Finset.univ.sort r
  have hlen : lst.length = X.card := by
    rw [Finset.length_sort, Finset.card_univ, Fintype.card_coe]
  have hnodup : lst.Nodup := Finset.sort_nodup Finset.univ r
  have hpair : lst.Pairwise r := Finset.pairwise_sort Finset.univ r
  have hconsec_step : ∀ (t : ℕ) (ht : t + 1 < lst.length),
      ∃ ig : Fin (m + 3), ig.val % 2 = 0 ∧
        ((lst[t]'(by omega)).1 + 1 = ig ∧ ig + 1 = (lst[t + 1]'ht).1 ∨
         (lst[t + 1]'ht).1 + 1 = ig ∧ ig + 1 = (lst[t]'(by omega)).1) ∧
        IsBackVertexOf S C (cyc.toFun ig) v ∧
        AngleLt v q (S (cyc.toFun (lst[t]'(by omega)).1)) (S (cyc.toFun ig)) ∧
        AngleLt v q (S (cyc.toFun ig)) (S (cyc.toFun (lst[t + 1]'ht).1)) ∧
        ((0 < orient2D (S (cyc.toFun (lst[t]'(by omega)).1)) (S (cyc.toFun ig)) (S (cyc.toFun (lst[t + 1]'ht).1)) ∧
          0 < orient2D (S (cyc.toFun (lst[t]'(by omega)).1)) (S (cyc.toFun ig)) v ∧
          0 < orient2D (S (cyc.toFun ig)) (S (cyc.toFun (lst[t + 1]'ht).1)) v) ∨
         (0 < orient2D (S (cyc.toFun (lst[t + 1]'ht).1)) (S (cyc.toFun ig)) (S (cyc.toFun (lst[t]'(by omega)).1)) ∧
          0 < orient2D (S (cyc.toFun (lst[t + 1]'ht).1)) (S (cyc.toFun ig)) v ∧
          0 < orient2D (S (cyc.toFun ig)) (S (cyc.toFun (lst[t]'(by omega)).1)) v)) := by
    intro t ht
    let o1 := lst[t]'(by omega)
    let o2 := lst[t + 1]'ht
    have ho12 : AngleLt v q (S (cyc.toFun o1.1)) (S (cyc.toFun o2.1)) := by
      have hr := List.pairwise_iff_get.mp hpair ⟨t, by omega⟩ ⟨t + 1, ht⟩ (by simp)
      rcases hr with heq | hlt
      · exfalso
        have := (List.nodup_iff_injective_get.mp hnodup) heq
        have : t = t + 1 := congrArg Fin.val this
        omega
      · exact hlt
    refine consecutive_odd (P := (∅ : Set (ℝ × ℝ))) (w := fun _ => (0, 0)) hm hm1 cyc v q hv_noncol hvq h_odd_nf o1.1 o2.1
      (hX_odd o1.1 o1.2) (hX_odd o2.1 o2.2) ho12 (fun o'' ho''_odd hss ⟨hlt1, hlt2⟩ => ?_)
    have ho''X : o'' ∈ X := hX_all o'' ho''_odd ⟨o1.1, o1.2, hss⟩
    have ho''_mem : (⟨o'', ho''X⟩ : {i // i ∈ X}) ∈ lst :=
      (Finset.mem_sort r).mpr (Finset.mem_univ _)
    rcases List.mem_iff_get.mp ho''_mem with ⟨⟨s, hs⟩, hget⟩
    have hst : s ≠ t := fun h => by
      subst h
      have ho_eq : o1.1 = o'' := congrArg Subtype.val hget
      rw [ho_eq] at hlt1; exact AngleLt.irrefl v q _ hlt1
    have hst1 : s ≠ t + 1 := fun h => by
      subst h
      have ho_eq : o2.1 = o'' := congrArg Subtype.val hget
      rw [ho_eq] at hlt2; exact AngleLt.irrefl v q _ hlt2
    rcases lt_or_gt_of_ne hst with hlt | hgt
    · have hr := List.pairwise_iff_get.mp hpair ⟨s, hs⟩ ⟨t, by omega⟩ hlt
      rcases hr with heq | hlt_so
      · exfalso
        have := congrArg Fin.val ((List.nodup_iff_injective_get.mp hnodup) heq)
        simp at this; exact hst this
      · have hos : (lst.get ⟨s, hs⟩).1 = o'' := congrArg Subtype.val hget
        rw [hos] at hlt_so
        exact hlt1.asymm hlt_so
    · have hs_gt : t + 1 < s := by omega
      have hr := List.pairwise_iff_get.mp hpair ⟨t + 1, ht⟩ ⟨s, hs⟩ hs_gt
      rcases hr with heq | hlt_os
      · exact hst1 (by
          have := congrArg Fin.val ((List.nodup_iff_injective_get.mp hnodup) heq)
          simp at this; exact this.symm)
      · have hos : (lst.get ⟨s, hs⟩).1 = o'' := congrArg Subtype.val hget
        rw [hos] at hlt_os
        exact hlt2.asymm hlt_os
  choose g hg_spec using fun (t : Fin (X.card - 1)) => hconsec_step t.val (by omega)
  have hg_ang : ∀ (t : Fin (X.card - 1)),
      AngleLt v q (S (cyc.toFun (lst[t.val]'(by omega)).1)) (S (cyc.toFun (g t))) ∧
      AngleLt v q (S (cyc.toFun (g t))) (S (cyc.toFun (lst[t.val + 1]'(by omega)).1)) :=
    fun t => ⟨(hg_spec t).2.2.2.1, (hg_spec t).2.2.2.2.1⟩
  have hg_mono : ∀ (a b : Fin (X.card - 1)), a.val < b.val →
      AngleLt v q (S (cyc.toFun (g a))) (S (cyc.toFun (g b))) := by
    intro a b hab
    have hblt : b.val < lst.length := by rw [hlen]; have := b.isLt; omega
    have ha1lt : a.val + 1 < lst.length := by rw [hlen]; have := b.isLt; omega
    have ha2 := (hg_ang a).2
    have hb1 := (hg_ang b).1
    rcases eq_or_lt_of_le (Nat.succ_le_of_lt hab) with h_eq | h_lt
    · have heq : a.val + 1 = b.val := h_eq
      have : (lst[a.val + 1]'ha1lt).1 = (lst[b.val]'hblt).1 := by simp [heq]
      rw [this] at ha2
      exact ha2.trans hb1
    · have hpair_ab : AngleLt v q (S (cyc.toFun (lst[a.val + 1]'ha1lt).1))
          (S (cyc.toFun (lst[b.val]'hblt).1)) := by
        have hr := List.pairwise_iff_get.mp hpair ⟨a.val + 1, ha1lt⟩ ⟨b.val, hblt⟩ h_lt
        rcases hr with heq | hlt
        · exfalso
          have := congrArg Fin.val ((List.nodup_iff_injective_get.mp hnodup) heq)
          simp at this; omega
        · exact hlt
      exact (ha2.trans hpair_ab).trans hb1
  refine ⟨g, fun a b hab => ?_, fun t => ?_, fun t o hoX ht0 => ?_⟩
  · rcases lt_trichotomy a.val b.val with h | h | h
    · exfalso; exact AngleLt.irrefl v q _ (hab ▸ hg_mono a b h)
    · exact Fin.ext h
    · exfalso; exact AngleLt.irrefl v q _ (hab ▸ hg_mono b a h)
  · rcases hg_spec t with ⟨hg_even, hadj, hback, hlt_in, hlt_out, htri⟩
    have ho1X : (lst[t.val]'(by omega)).1 ∈ X := (lst[t.val]'(by omega)).2
    have ho2X : (lst[t.val + 1]'(by omega)).1 ∈ X := (lst[t.val + 1]'(by omega)).2
    have hm1_X : g t - 1 ∈ X := by
      rcases hadj with ⟨h1, _⟩ | ⟨h1, _⟩
      · have : g t - 1 = (lst[t.val]'(by omega)).1 := (eq_sub_of_add_eq h1).symm
        rwa [this]
      · have : g t - 1 = (lst[t.val + 1]'(by omega)).1 := (eq_sub_of_add_eq h1).symm
        rwa [this]
    have hp1_X : g t + 1 ∈ X := by
      rcases hadj with ⟨_, h2⟩ | ⟨_, h2⟩
      · rwa [h2]
      · rwa [h2]
    refine ⟨hg_even, hm1_X, hp1_X, hX_odd _ hm1_X, hX_odd _ hp1_X, hback, ?_, ?_, ?_⟩
    · rcases hadj with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have hm1_eq : g t - 1 = (lst[t.val]'(by omega)).1 := (eq_sub_of_add_eq h1).symm
        rw [hm1_eq, h2]; exact (hlt_in.trans hlt_out).1
      · have hm1_eq : g t - 1 = (lst[t.val + 1]'(by omega)).1 := (eq_sub_of_add_eq h1).symm
        rw [hm1_eq, h2]; exact (hlt_in.trans hlt_out).1.symm
    · intro ht1
      let t0 : Fin (X.card - 1) := ⟨t.val - 1, by omega⟩
      refine ⟨t0, by dsimp [t0]; omega, ?_⟩
      have heq_idx : (lst[t0.val + 1]'(by omega)).1 = (lst[t.val]'(by omega)).1 := by
        have : t0.val + 1 = t.val := by dsimp [t0]; omega
        simp [this]
      have hlt_t0_o1 : AngleLt v q (S (cyc.toFun (g t0))) (S (cyc.toFun (lst[t.val]'(by omega)).1)) := by
        rw [← heq_idx]; exact (hg_ang t0).2
      have hlt_o1_o2 : AngleLt v q (S (cyc.toFun (lst[t.val]'(by omega)).1))
          (S (cyc.toFun (lst[t.val + 1]'(by omega)).1)) := hlt_in.trans hlt_out
      rcases hadj with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have hm1_eq : g t - 1 = (lst[t.val]'(by omega)).1 := (eq_sub_of_add_eq h1).symm
        rw [hm1_eq, h2]
        exact ⟨hlt_t0_o1, hlt_t0_o1.trans hlt_o1_o2⟩
      · have hm1_eq : g t - 1 = (lst[t.val + 1]'(by omega)).1 := (eq_sub_of_add_eq h1).symm
        rw [hm1_eq, h2]
        exact ⟨hlt_t0_o1.trans hlt_o1_o2, hlt_t0_o1⟩
    · rcases hadj with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have hm1_eq : g t - 1 = (lst[t.val]'(by omega)).1 := (eq_sub_of_add_eq h1).symm
        rcases htri with ⟨a1, a2, a3⟩ | ⟨a1, a2, a3⟩
        · rw [hm1_eq, h2]
          exact Or.inl ⟨hm1_eq.symm ▸ hlt_in, h2 ▸ hlt_out, a1, a2, a3⟩
        · exfalso
          have hne13 : (lst[t.val]'(by omega)).1 ≠ (lst[t.val + 1]'(by omega)).1 := by
            intro h
            have heq := List.nodup_iff_injective_get.mp hnodup (Subtype.ext h : lst.get ⟨t.val, by omega⟩ = lst.get ⟨t.val + 1, by omega⟩)
            have hv := congrArg Fin.val heq; simp at hv
          have h1p : (lst[t.val]'(by omega)).1 + 1 ≠ (lst[t.val + 1]'(by omega)).1 := by
            rw [h1]; exact fun h => (fin_add_one_ne_self (g t)) (h.trans h2.symm)
          have hccw := cyc.ccw (lst[t.val]'(by omega)).1 (lst[t.val + 1]'(by omega)).1 hne13.symm h1p.symm
          dsimp only [Function.comp] at hccw
          rw [h1] at hccw
          unfold orient2D at a1 hccw; linarith
      · have hm1_eq : g t - 1 = (lst[t.val + 1]'(by omega)).1 := (eq_sub_of_add_eq h1).symm
        rcases htri with ⟨a1, a2, a3⟩ | ⟨a1, a2, a3⟩
        · exfalso
          have hne13 : (lst[t.val + 1]'(by omega)).1 ≠ (lst[t.val]'(by omega)).1 := by
            intro h
            have heq := List.nodup_iff_injective_get.mp hnodup (Subtype.ext h : lst.get ⟨t.val + 1, by omega⟩ = lst.get ⟨t.val, by omega⟩)
            have hv := congrArg Fin.val heq; simp at hv
          have h1p : (lst[t.val + 1]'(by omega)).1 + 1 ≠ (lst[t.val]'(by omega)).1 := by
            rw [h1]; exact fun h => (fin_add_one_ne_self (g t)) (h.trans h2.symm)
          have hccw := cyc.ccw (lst[t.val + 1]'(by omega)).1 (lst[t.val]'(by omega)).1 hne13.symm h1p.symm
          dsimp only [Function.comp] at hccw
          rw [h1] at hccw
          unfold orient2D at a1 hccw; linarith
        · rw [hm1_eq, h2]
          exact Or.inr ⟨h2.symm ▸ hlt_in, hm1_eq.symm ▸ hlt_out, a1, a2, a3⟩
  · rcases hg_spec t with ⟨_, hadj, _, _, _, _⟩
    have htlt : t.val + 1 < lst.length := by rw [hlen]; have := t.isLt; omega
    have ho_mem : (⟨o, hoX⟩ : {i // i ∈ X}) ∈ lst := (Finset.mem_sort r).mpr (Finset.mem_univ _)
    rcases List.mem_iff_get.mp ho_mem with ⟨⟨s, hs⟩, hget⟩
    have hos : o = (lst.get ⟨s, hs⟩).1 := congrArg Subtype.val hget.symm
    have h0_eq : (lst.get ⟨0, by omega⟩).1 = (lst[t.val]'(by omega)).1 := by simp [ht0]
    have h1_eq : (lst.get ⟨1, by omega⟩).1 = (lst[t.val + 1]'htlt).1 := by simp [ht0]
    by_cases hs0 : s = 0
    · have ho_eq : o = (lst[t.val]'(by omega)).1 := by
        rw [hos, ← h0_eq]; congr 1; congr 1; exact Fin.ext hs0
      rcases hadj with ⟨h1, _⟩ | ⟨_, h2⟩
      · left; exact ho_eq.trans (eq_sub_of_add_eq h1)
      · right; left; exact ho_eq.trans h2.symm
    · by_cases hs1 : s = 1
      · have ho_eq : o = (lst[t.val + 1]'htlt).1 := by
          rw [hos, ← h1_eq]; congr 1; congr 1; exact Fin.ext hs1
        rcases hadj with ⟨_, h2⟩ | ⟨h1, _⟩
        · right; left; exact ho_eq.trans h2.symm
        · left; exact ho_eq.trans (eq_sub_of_add_eq h1)
      · have hs2 : 1 < s := by omega
        have hr0 : AngleLt v q (S (cyc.toFun (lst.get ⟨0, by omega⟩).1)) (S (cyc.toFun o)) := by
          have hr := List.pairwise_iff_get.mp hpair ⟨0, by omega⟩ ⟨s, hs⟩ (by simp [Fin.lt_def]; omega)
          rcases hr with heq | hlt
          · exfalso; have := congrArg Fin.val ((List.nodup_iff_injective_get.mp hnodup) heq); simp at this; omega
          · rwa [← hos] at hlt
        have hr1 : AngleLt v q (S (cyc.toFun (lst.get ⟨1, by omega⟩).1)) (S (cyc.toFun o)) := by
          have hr := List.pairwise_iff_get.mp hpair ⟨1, by omega⟩ ⟨s, hs⟩ (by simp [Fin.lt_def]; exact hs2)
          rcases hr with heq | hlt
          · exfalso; have := congrArg Fin.val ((List.nodup_iff_injective_get.mp hnodup) heq); simp at this; omega
          · rwa [← hos] at hlt
        rw [h0_eq] at hr0; rw [h1_eq] at hr1
        right; right
        rcases hadj with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · have hm1_eq : g t - 1 = (lst[t.val]'(by omega)).1 := (eq_sub_of_add_eq h1).symm
          rw [hm1_eq, h2]; exact ⟨hr0, hr1⟩
        · have hm1_eq : g t - 1 = (lst[t.val + 1]'htlt).1 := (eq_sub_of_add_eq h1).symm
          rw [hm1_eq, h2]; exact ⟨hr1, hr0⟩

private lemma good_targets_core_min_contradict {n m : ℕ} {P : Set (ℝ × ℝ)}
    {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ}
    {C O_miss : Finset (Fin n)} (hm : m = 3 ∨ m = 5)
    (cyc : CCWCycle S C m)
    (h_odd_nf : ∀ i : Fin (m + 3), i.val % 2 = 1 →
      ¬ IsFrontVertexOf S C (cyc.toFun i) (w (Finset.univ \ O_miss)))
    (h_no_cert : ¬ ∃ (io_min io_star ig : Fin (m + 3)),
      io_min.val % 2 = 1 ∧ io_star.val % 2 = 1 ∧ ig.val % 2 = 0 ∧
      ((io_star + 1 = ig ∧ ig + 1 = io_min) ∨ (io_min + 1 = ig ∧ ig + 1 = io_star)) ∧
      ¬ Sees P (w (Finset.univ \ O_miss)) (w Finset.univ) ∧
      IsFrontVertexOf S C (cyc.toFun ig) (w (Finset.univ \ O_miss)) ∧
      InIntTri (w Finset.univ) (S (cyc.toFun io_min)) (S (cyc.toFun io_star)) (w (Finset.univ \ O_miss)))
    (hv_noncol : ∀ i j : Fin (m + 3), i ≠ j →
      orient2D (S (cyc.toFun i)) (S (cyc.toFun j)) (w (Finset.univ \ O_miss)) ≠ 0)
    (hvq : ∀ i : Fin (m + 3),
      orient2D (w (Finset.univ \ O_miss)) (w Finset.univ) (S (cyc.toFun i)) ≠ 0)
    (h_inTri_nonfacing : ∀ (a b c : Fin (m + 3)),
      InIntTri (S (cyc.toFun a)) (S (cyc.toFun b)) (S (cyc.toFun c)) (w (Finset.univ \ O_miss)) →
      ∀ j : Fin (m + 3), 0 ≤ orient2D (S (cyc.toFun j)) (S (cyc.toFun (j + 1))) (w (Finset.univ \ O_miss)))
    (hsee : ¬ Sees P (w (Finset.univ \ O_miss)) (w Finset.univ))
    (heven_ss : ∀ i j : Fin (m + 3), i.val % 2 = 0 → j.val % 2 = 0 →
      OnSameSide (w (Finset.univ \ O_miss)) (w Finset.univ) (S (cyc.toFun i)) (S (cyc.toFun j)))
    {io_min io_star : Fin (m + 3)}
    (hmin_odd : io_min.val % 2 = 1) (hio_star_odd : io_star.val % 2 = 1)
    (hmin_L : 0 < orient2D (w (Finset.univ \ O_miss)) (w Finset.univ) (S (cyc.toFun 0)) *
      orient2D (w (Finset.univ \ O_miss)) (w Finset.univ) (S (cyc.toFun io_min)))
    (hio_star_opp : orient2D (w (Finset.univ \ O_miss)) (w Finset.univ) (S (cyc.toFun 0)) *
      orient2D (w (Finset.univ \ O_miss)) (w Finset.univ) (S (cyc.toFun io_star)) < 0)
    (h_even_gt : ∀ ie : Fin (m + 3), ie.val % 2 = 0 →
      AngleLt (w (Finset.univ \ O_miss)) (w Finset.univ) (S (cyc.toFun io_min)) (S (cyc.toFun ie))) :
    False := by
  let v := w (Finset.univ \ O_miss)
  let q := w Finset.univ
  have h_even_size : (m + 3) % 2 = 0 := by rcases hm with rfl | rfl <;> decide
  have hm1_lt : 1 < m + 3 := by rcases hm with rfl | rfl <;> omega
  have hm2_lt : 2 < m + 3 := by rcases hm with rfl | rfl <;> omega
  have h1_val : (1 : Fin (m + 3)).val = 1 := by rcases hm with rfl | rfl <;> decide
  have h2_val : (2 : Fin (m + 3)).val = 2 := by rcases hm with rfl | rfl <;> decide
  have h11 : (1 + 1 : Fin (m + 3)) = 2 := Fin.ext (by
    rw [Fin.val_add, h1_val, h2_val, Nat.mod_eq_of_lt hm2_lt])
  have h_adj_ne : ∀ i : Fin (m + 3), i - 1 ≠ i + 1 := by
    intro i h
    have h' := congrArg (· + (1 : Fin (m + 3))) h
    rw [sub_add_cancel, add_assoc] at h'
    nth_rw 1 [← add_zero i] at h'
    have h02 : (0 : Fin (m + 3)) = 2 := add_left_cancel h'
    have hv := congrArg Fin.val h02
    rw [Fin.val_zero, h2_val] at hv
    omega
  have hmin_neq_star : io_min ≠ io_star := fun h => by
    rw [h] at hmin_L; linarith only [hmin_L, hio_star_opp]
  have hdiff_star_ev : (io_star - io_min).val % 2 = 0 := by
    rw [fin_val_sub_eq]; split_ifs with hle
    · have := Fin.le_def.mp hle; omega
    · have := Fin.lt_def.mp (lt_of_not_ge hle); omega
  have hdiff_min_ev : (io_min - io_star).val % 2 = 0 := by
    rw [fin_val_sub_eq]; split_ifs with hle
    · have := Fin.le_def.mp hle; omega
    · have := Fin.lt_def.mp (lt_of_not_ge hle); omega
  have hstar_m1_ev : (io_star - 1).val % 2 = 0 := by
    have h1 : io_star = (io_star - 1) + 1 := by abel
    have hp := fin_succ_val_parity h_even_size (io_star - 1)
    rw [← h1] at hp; omega
  have hstar_p1_ev : (io_star + 1).val % 2 = 0 := by
    rw [fin_succ_val_parity h_even_size io_star]; omega
  have hmin_m1_ev : (io_min - 1).val % 2 = 0 := by
    have h1 : io_min = (io_min - 1) + 1 := by abel
    have hp := fin_succ_val_parity h_even_size (io_min - 1)
    rw [← h1] at hp; omega
  have hmin_p1_ev : (io_min + 1).val % 2 = 0 := by
    rw [fin_succ_val_parity h_even_size io_min]; omega
  have hnf_min := h_odd_nf io_min hmin_odd
  have hnf_star := h_odd_nf io_star hio_star_odd
  rw [isFrontVertexOf_iff_ccwCycle cyc io_min v] at hnf_min
  rw [isFrontVertexOf_iff_ccwCycle cyc io_star v] at hnf_star
  rcases lt_or_gt_of_ne (hvq 0) with h0n | h0p
  · have hmin_q : orient2D v q (S (cyc.toFun io_min)) < 0 := by nlinarith only [hmin_L, h0n]
    have hstar_q : 0 < orient2D v q (S (cyc.toFun io_star)) := by nlinarith only [hio_star_opp, h0n]
    have h_ang_p1 := h_even_gt (io_min + 1) hmin_p1_ev
    have he_min_p1 : orient2D (S (cyc.toFun io_min)) (S (cyc.toFun (io_min + 1))) v < 0 := by
      have h2 := h_ang_p1.2
      have hv_lt : orient2D v (S (cyc.toFun io_min)) (S (cyc.toFun (io_min + 1))) < 0 := by
        nlinarith only [hmin_q, h2]
      unfold orient2D at hv_lt ⊢; linarith
    have he_min_m1 : 0 < orient2D (S (cyc.toFun (io_min - 1))) (S (cyc.toFun io_min)) v := by
      rcases lt_or_gt_of_ne (hv_noncol (io_min - 1) io_min (fin_sub_one_ne_self io_min)) with hl | hg
      · exact False.elim (hnf_min ⟨hl, he_min_p1⟩)
      · exact hg
    have he_star_p1 : 0 < orient2D (S (cyc.toFun io_star)) (S (cyc.toFun (io_star + 1))) v := by
      by_contra hle
      have hneg : orient2D (S (cyc.toFun io_star)) (S (cyc.toFun (io_star + 1))) v < 0 :=
        lt_of_le_of_ne (not_lt.mp hle) (hv_noncol io_star (io_star + 1) (fin_add_one_ne_self io_star))
      have harc := facing_edges_contiguous (S ∘ cyc.toFun) cyc.ccw v io_min io_star he_min_p1 hneg
      rcases harc with h1 | h2
      · have h_le : (io_star - 1 - io_min).val ≤ (io_star - io_min).val := by
          have hpos : 0 < (io_star - io_min).val :=
            Nat.pos_of_ne_zero (fun h => hmin_neq_star (sub_eq_zero.mp (Fin.ext h)).symm)
          have heq : io_star - 1 - io_min = (io_star - io_min) - 1 := by abel
          rw [heq, fin_val_sub_eq, if_pos (Fin.le_def.mpr (by rw [h1_val]; omega)), h1_val]
          omega
        have he1 := h1 (io_star - 1) h_le
        dsimp only [Function.comp] at he1
        rw [sub_add_cancel] at he1
        exact hnf_star ⟨he1, hneg⟩
      · have h_le : (io_min - 1 - io_star).val ≤ (io_min - io_star).val := by
          have hpos : 0 < (io_min - io_star).val :=
            Nat.pos_of_ne_zero (fun h => hmin_neq_star (sub_eq_zero.mp (Fin.ext h)))
          have heq : io_min - 1 - io_star = (io_min - io_star) - 1 := by abel
          rw [heq, fin_val_sub_eq, if_pos (Fin.le_def.mpr (by rw [h1_val]; omega)), h1_val]
          omega
        have he1 := h2 (io_min - 1) h_le
        dsimp only [Function.comp] at he1
        rw [sub_add_cancel] at he1
        exact hnf_min ⟨he1, he_min_p1⟩
    have he_star_m1 : orient2D (S (cyc.toFun (io_star - 1))) (S (cyc.toFun io_star)) v < 0 := by
      by_contra hge
      have hpos : 0 < orient2D (S (cyc.toFun (io_star - 1))) (S (cyc.toFun io_star)) v :=
        lt_of_le_of_ne (not_lt.mp hge) (hv_noncol (io_star - 1) io_star (fin_sub_one_ne_self io_star)).symm
      have hsm1_q : orient2D v q (S (cyc.toFun (io_star - 1))) < 0 := by
        have h1 := heven_ss 0 (io_star - 1) (by rw [Fin.val_zero]) hstar_m1_ev
        unfold OnSameSide at h1; nlinarith only [h1, h0n]
      have hsp1_q : orient2D v q (S (cyc.toFun (io_star + 1))) < 0 := by
        have h1 := heven_ss 0 (io_star + 1) (by rw [Fin.val_zero]) hstar_p1_ev
        unfold OnSameSide at h1; nlinarith only [h1, h0n]
      have hid := orient2D_angle_trans_id v q (S (cyc.toFun (io_star - 1)))
        (S (cyc.toFun io_star)) (S (cyc.toFun (io_star + 1)))
      have ho_1 : orient2D v (S (cyc.toFun io_star)) (S (cyc.toFun (io_star + 1))) > 0 := by
        unfold orient2D at he_star_p1 ⊢; linarith
      have ho_2 : orient2D v (S (cyc.toFun (io_star - 1))) (S (cyc.toFun io_star)) > 0 := by
        unfold orient2D at hpos ⊢; linarith
      have h_tri_3 : 0 < orient2D (S (cyc.toFun (io_star + 1))) (S (cyc.toFun (io_star - 1))) v := by
        have : orient2D v (S (cyc.toFun (io_star - 1))) (S (cyc.toFun (io_star + 1))) < 0 := by
          nlinarith only [hid, hmin_q, hstar_q, hsm1_q, hsp1_q, ho_1, ho_2]
        unfold orient2D at this ⊢; linarith
      have hccw_star : 0 < orient2D (S (cyc.toFun (io_star - 1))) (S (cyc.toFun io_star))
          (S (cyc.toFun (io_star + 1))) := by
        simpa [sub_add_cancel] using cyc.ccw (io_star - 1) (io_star + 1)
          (h_adj_ne io_star).symm (by rw [sub_add_cancel]; exact (fin_add_one_ne_self io_star).symm)
      have hin_star : InIntTri (S (cyc.toFun (io_star - 1))) (S (cyc.toFun io_star))
          (S (cyc.toFun (io_star + 1))) v :=
        (inIntTri_iff_orient_pos hccw_star).mpr ⟨hpos, he_star_p1, h_tri_3⟩
      have hnf0 := h_inTri_nonfacing (io_star - 1) io_star (io_star + 1) hin_star io_min
      linarith only [hnf0, he_min_p1]
    have harc := facing_edges_contiguous (S ∘ cyc.toFun) cyc.ccw v io_min (io_star - 1)
      he_min_p1 (by dsimp [Function.comp]; rw [sub_add_cancel]; exact he_star_m1)
    have harc1 : ∀ x : Fin (m + 3), (x - io_min).val ≤ (io_star - 1 - io_min).val →
        orient2D (S (cyc.toFun x)) (S (cyc.toFun (x + 1))) v < 0 := by
      rcases harc with h1 | h2
      · exact h1
      · exfalso
        have hne_sm1 : io_min ≠ io_star - 1 := fun h => by rw [h] at hmin_odd; omega
        have hpos : 0 < (io_min - (io_star - 1)).val :=
          Nat.pos_of_ne_zero (fun h => hne_sm1 (sub_eq_zero.mp (Fin.ext h)))
        have h1_lt : (io_star - (io_star - 1)).val ≤ (io_min - (io_star - 1)).val := by
          have h_eq1 : (io_star - (io_star - 1) : Fin (m + 3)) = 1 := by abel
          rw [h_eq1, h1_val]; omega
        have he1 := h2 io_star h1_lt
        dsimp only [Function.comp] at he1
        linarith only [he1, he_star_p1]
    have hdiff_pos : 0 < (io_star - io_min).val :=
      Nat.pos_of_ne_zero (fun h => hmin_neq_star (sub_eq_zero.mp (Fin.ext h)).symm)
    have hdiff_ge2 : 2 ≤ (io_star - io_min).val := by omega
    have hdiff_eq2 : (io_star - io_min).val = 2 := by
      by_contra hne2
      have hge4 : 4 ≤ (io_star - io_min).val := by omega
      have hsm1_val : (io_star - 1 - io_min).val = (io_star - io_min).val - 1 := by
        have heq : io_star - 1 - io_min = (io_star - io_min) - 1 := by abel
        rw [heq, fin_val_sub_eq, if_pos (Fin.le_def.mpr (by rw [h1_val]; omega)), h1_val]
      have h_o2_front : IsFrontVertexOf S C (cyc.toFun (io_min + 2)) v := by
        rw [isFrontVertexOf_iff_ccwCycle cyc (io_min + 2) v]
        have he1 := harc1 (io_min + 1) (by rw [add_sub_cancel_left, h1_val]; omega)
        have he2 := harc1 (io_min + 2) (by rw [add_sub_cancel_left, h2_val]; omega)
        have hp1m : io_min + 2 - 1 = io_min + 1 := by rw [← h11]; abel
        have hp1p : io_min + 1 + 1 = io_min + 2 := by rw [← h11]; abel
        rw [hp1m]; rw [hp1p] at he1
        exact ⟨he1, he2⟩
      have ho2_odd : (io_min + 2).val % 2 = 1 := by
        rw [Fin.val_add, h2_val]
        rcases Nat.lt_or_ge (io_min.val + 2) (m + 3) with hlt | hge
        · rw [Nat.mod_eq_of_lt hlt]; omega
        · have hsub : io_min.val + 2 - (m + 3) < m + 3 := by have := io_min.isLt; omega
          rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt hsub]; omega
      exact h_odd_nf (io_min + 2) ho2_odd h_o2_front
    let ig := io_min + 1
    have hig_even : ig.val % 2 = 0 := by
      dsimp [ig]; rw [fin_succ_val_parity h_even_size io_min]; omega
    have h2_eq : io_min + 2 = io_star := by
      have hfn : (2 : Fin (m + 3)) = io_star - io_min := by
        ext; rw [h2_val, ← hdiff_eq2]
      rw [hfn, add_sub_cancel]
    have hig_next : ig + 1 = io_star := by
      dsimp [ig]; rw [add_assoc, h11, h2_eq]
    have hig_front : IsFrontVertexOf S C (cyc.toFun ig) v := by
      rw [isFrontVertexOf_iff_ccwCycle cyc ig v]
      have hm1 : ig - 1 = io_min := by dsimp [ig]; abel
      have h_e2 : orient2D (S (cyc.toFun ig)) (S (cyc.toFun io_star)) v < 0 := by
        have : ig = io_star - 1 := by rw [← hig_next]; abel
        rwa [← this] at he_star_m1
      rw [hm1, hig_next]; exact ⟨he_min_p1, h_e2⟩
    let b := io_star + 1
    have hb_even : b.val % 2 = 0 := by dsimp [b]; rw [fin_succ_val_parity h_even_size io_star]; omega
    have h_ang_b := h_even_gt b hb_even
    have hvb_min : 0 < orient2D v (S (cyc.toFun b)) (S (cyc.toFun io_min)) := by
      have h2 := h_ang_b.2
      have hv_lt : orient2D v (S (cyc.toFun io_min)) (S (cyc.toFun b)) < 0 := by
        nlinarith only [hmin_q, h2]
      unfold orient2D at hv_lt ⊢; linarith
    have hstar_b_ccw : 0 < orient2D (S (cyc.toFun io_star)) (S (cyc.toFun b)) (S (cyc.toFun io_min)) := by
      have h1 : (b - io_star).val = 1 := by dsimp [b]; rw [add_sub_cancel_left, h1_val]
      have h2 : (io_min - io_star).val = m + 1 := by
        have := fin_sub_add_compl hmin_neq_star; omega
      exact ccwCycle_ccw3 cyc (by rw [h1]; omega) (by rw [h1, h2]; omega)
    have h_star_min_pos : 0 < orient2D v (S (cyc.toFun io_star)) (S (cyc.toFun io_min)) := by
      by_contra hle
      have hne0 : orient2D v (S (cyc.toFun io_star)) (S (cyc.toFun io_min)) ≠ 0 := by
        have hnc := hv_noncol io_star io_min hmin_neq_star.symm
        unfold orient2D at hnc ⊢; intro h; apply hnc; linarith
      have hlt' : orient2D v (S (cyc.toFun io_star)) (S (cyc.toFun io_min)) < 0 :=
        lt_of_le_of_ne (not_lt.mp hle) hne0
      have h3 : 0 < orient2D (S (cyc.toFun io_min)) (S (cyc.toFun io_star)) v := by
        unfold orient2D at hlt' ⊢; linarith
      have h1 : 0 < orient2D (S (cyc.toFun io_star)) (S (cyc.toFun b)) v := he_star_p1
      have h2 : 0 < orient2D (S (cyc.toFun b)) (S (cyc.toFun io_min)) v := by
        unfold orient2D at hvb_min ⊢; linarith
      have hin := (inIntTri_iff_orient_pos hstar_b_ccw).mpr ⟨h1, h2, h3⟩
      have hnf0 := h_inTri_nonfacing io_star b io_min hin io_min
      linarith only [hnf0, he_min_p1]
    have hq_ccw : 0 < orient2D q (S (cyc.toFun io_star)) (S (cyc.toFun io_min)) := by
      have hid : orient2D q (S (cyc.toFun io_star)) (S (cyc.toFun io_min)) =
          orient2D v (S (cyc.toFun io_star)) (S (cyc.toFun io_min)) +
          orient2D v q (S (cyc.toFun io_star)) - orient2D v q (S (cyc.toFun io_min)) := by
        unfold orient2D; ring
      linarith only [hid, h_star_min_pos, hstar_q, hmin_q]
    have hv_tri : InIntTri q (S (cyc.toFun io_min)) (S (cyc.toFun io_star)) v := by
      refine ((inIntTri_iff_orient_pos hq_ccw).mpr ⟨?_, ?_, ?_⟩).symm23
      · unfold orient2D at hstar_q ⊢; linarith
      · unfold orient2D at h_star_min_pos ⊢; linarith
      · unfold orient2D at hmin_q ⊢; linarith
    exact h_no_cert ⟨io_min, io_star, ig, hmin_odd, hio_star_odd, hig_even,
      Or.inr ⟨rfl, hig_next⟩, hsee, hig_front, hv_tri⟩
  · have hmin_q : 0 < orient2D v q (S (cyc.toFun io_min)) := by nlinarith only [hmin_L, h0p]
    have hstar_q : orient2D v q (S (cyc.toFun io_star)) < 0 := by nlinarith only [hio_star_opp, h0p]
    have h_ang_m1 := h_even_gt (io_min - 1) hmin_m1_ev
    have he_min_m1 : orient2D (S (cyc.toFun (io_min - 1))) (S (cyc.toFun io_min)) v < 0 := by
      have h2 := h_ang_m1.2
      have hv_pos : 0 < orient2D v (S (cyc.toFun io_min)) (S (cyc.toFun (io_min - 1))) := by
        nlinarith only [hmin_q, h2]
      unfold orient2D at hv_pos ⊢; linarith
    have he_min_p1 : 0 < orient2D (S (cyc.toFun io_min)) (S (cyc.toFun (io_min + 1))) v := by
      rcases lt_or_gt_of_ne (hv_noncol io_min (io_min + 1) (fin_add_one_ne_self io_min)) with hl | hg
      · exact False.elim (hnf_min ⟨he_min_m1, hl⟩)
      · exact hg
    have he_star_m1 : 0 < orient2D (S (cyc.toFun (io_star - 1))) (S (cyc.toFun io_star)) v := by
      by_contra hle
      have hneg : orient2D (S (cyc.toFun (io_star - 1))) (S (cyc.toFun io_star)) v < 0 :=
        lt_of_le_of_ne (not_lt.mp hle) (hv_noncol (io_star - 1) io_star (fin_sub_one_ne_self io_star))
      have harc := facing_edges_contiguous (S ∘ cyc.toFun) cyc.ccw v (io_min - 1) (io_star - 1)
        (by dsimp [Function.comp]; rw [sub_add_cancel]; exact he_min_m1)
        (by dsimp [Function.comp]; rw [sub_add_cancel]; exact hneg)
      rcases harc with h1 | h2
      · have h_le : (io_min - (io_min - 1)).val ≤ (io_star - 1 - (io_min - 1)).val := by
          have h_eq1 : (io_min - (io_min - 1) : Fin (m + 3)) = 1 := by abel
          have h_eq2 : io_star - 1 - (io_min - 1) = io_star - io_min := by abel
          rw [h_eq1, h1_val, h_eq2]
          exact Nat.pos_of_ne_zero (fun h => hmin_neq_star (sub_eq_zero.mp (Fin.ext h)).symm)
        have he1 := h1 io_min h_le
        dsimp only [Function.comp] at he1
        linarith only [he1, he_min_p1]
      · have h_le : (io_star - (io_star - 1)).val ≤ (io_min - 1 - (io_star - 1)).val := by
          have h_eq1 : (io_star - (io_star - 1) : Fin (m + 3)) = 1 := by abel
          have h_eq2 : io_min - 1 - (io_star - 1) = io_min - io_star := by abel
          rw [h_eq1, h1_val, h_eq2]
          exact Nat.pos_of_ne_zero (fun h => hmin_neq_star (sub_eq_zero.mp (Fin.ext h)))
        have he1 := h2 io_star h_le
        dsimp only [Function.comp] at he1
        exact False.elim (hnf_star ⟨hneg, he1⟩)
    have he_star_p1 : orient2D (S (cyc.toFun io_star)) (S (cyc.toFun (io_star + 1))) v < 0 := by
      by_contra hge
      have hpos : 0 < orient2D (S (cyc.toFun io_star)) (S (cyc.toFun (io_star + 1))) v :=
        lt_of_le_of_ne (not_lt.mp hge) (hv_noncol io_star (io_star + 1) (fin_add_one_ne_self io_star)).symm
      have hsm1_q : 0 < orient2D v q (S (cyc.toFun (io_star - 1))) := by
        have h1 := heven_ss 0 (io_star - 1) (by rw [Fin.val_zero]) hstar_m1_ev
        unfold OnSameSide at h1; nlinarith only [h1, h0p]
      have hsp1_q : 0 < orient2D v q (S (cyc.toFun (io_star + 1))) := by
        have h1 := heven_ss 0 (io_star + 1) (by rw [Fin.val_zero]) hstar_p1_ev
        unfold OnSameSide at h1; nlinarith only [h1, h0p]
      have hid := orient2D_angle_trans_id v q (S (cyc.toFun (io_star + 1)))
        (S (cyc.toFun io_star)) (S (cyc.toFun (io_star - 1)))
      have ho_1 : orient2D v (S (cyc.toFun io_star)) (S (cyc.toFun (io_star - 1))) < 0 := by
        unfold orient2D at he_star_m1 ⊢; linarith
      have ho_2 : orient2D v (S (cyc.toFun (io_star + 1))) (S (cyc.toFun io_star)) < 0 := by
        unfold orient2D at hpos ⊢; linarith
      have h_tri_3 : 0 < orient2D (S (cyc.toFun (io_star + 1))) (S (cyc.toFun (io_star - 1))) v := by
        have : 0 < orient2D v (S (cyc.toFun (io_star + 1))) (S (cyc.toFun (io_star - 1))) := by
          nlinarith only [hid, hstar_q, hsm1_q, hsp1_q, ho_1, ho_2]
        unfold orient2D at this ⊢; linarith
      have hccw_star : 0 < orient2D (S (cyc.toFun (io_star - 1))) (S (cyc.toFun io_star))
          (S (cyc.toFun (io_star + 1))) := by
        simpa [sub_add_cancel] using cyc.ccw (io_star - 1) (io_star + 1)
          (h_adj_ne io_star).symm (by rw [sub_add_cancel]; exact (fin_add_one_ne_self io_star).symm)
      have hin_star : InIntTri (S (cyc.toFun (io_star - 1))) (S (cyc.toFun io_star))
          (S (cyc.toFun (io_star + 1))) v :=
        (inIntTri_iff_orient_pos hccw_star).mpr ⟨he_star_m1, hpos, h_tri_3⟩
      have hnf0 := h_inTri_nonfacing (io_star - 1) io_star (io_star + 1) hin_star (io_min - 1)
      rw [sub_add_cancel] at hnf0
      linarith only [hnf0, he_min_m1]
    have harc := facing_edges_contiguous (S ∘ cyc.toFun) cyc.ccw v io_star (io_min - 1)
      he_star_p1 (by dsimp [Function.comp]; rw [sub_add_cancel]; exact he_min_m1)
    have harc1 : ∀ x : Fin (m + 3), (x - io_star).val ≤ (io_min - 1 - io_star).val →
        orient2D (S (cyc.toFun x)) (S (cyc.toFun (x + 1))) v < 0 := by
      rcases harc with h1 | h2
      · exact h1
      · exfalso
        have hne_mm1 : io_star ≠ io_min - 1 := fun h => by rw [h] at hio_star_odd; omega
        have hpos : 0 < (io_star - (io_min - 1)).val :=
          Nat.pos_of_ne_zero (fun h => hne_mm1 (sub_eq_zero.mp (Fin.ext h)))
        have h1_lt : (io_min - (io_min - 1)).val ≤ (io_star - (io_min - 1)).val := by
          have h_eq1 : (io_min - (io_min - 1) : Fin (m + 3)) = 1 := by abel
          rw [h_eq1, h1_val]; omega
        have he1 := h2 io_min h1_lt
        dsimp only [Function.comp] at he1
        linarith only [he1, he_min_p1]
    have hdiff_pos : 0 < (io_min - io_star).val :=
      Nat.pos_of_ne_zero (fun h => hmin_neq_star (sub_eq_zero.mp (Fin.ext h)))
    have hdiff_ge2 : 2 ≤ (io_min - io_star).val := by omega
    have hdiff_eq2 : (io_min - io_star).val = 2 := by
      by_contra hne2
      have hge4 : 4 ≤ (io_min - io_star).val := by omega
      have hmm1_val : (io_min - 1 - io_star).val = (io_min - io_star).val - 1 := by
        have heq : io_min - 1 - io_star = (io_min - io_star) - 1 := by abel
        rw [heq, fin_val_sub_eq, if_pos (Fin.le_def.mpr (by rw [h1_val]; omega)), h1_val]
      have h_o2_front : IsFrontVertexOf S C (cyc.toFun (io_star + 2)) v := by
        rw [isFrontVertexOf_iff_ccwCycle cyc (io_star + 2) v]
        have he1 := harc1 (io_star + 1) (by rw [add_sub_cancel_left, h1_val]; omega)
        have he2 := harc1 (io_star + 2) (by rw [add_sub_cancel_left, h2_val]; omega)
        have hp1m : io_star + 2 - 1 = io_star + 1 := by rw [← h11]; abel
        have hp1p : io_star + 1 + 1 = io_star + 2 := by rw [← h11]; abel
        rw [hp1m]; rw [hp1p] at he1
        exact ⟨he1, he2⟩
      have ho2_odd : (io_star + 2).val % 2 = 1 := by
        rw [Fin.val_add, h2_val]
        rcases Nat.lt_or_ge (io_star.val + 2) (m + 3) with hlt | hge
        · rw [Nat.mod_eq_of_lt hlt]; omega
        · have hsub : io_star.val + 2 - (m + 3) < m + 3 := by have := io_star.isLt; omega
          rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt hsub]; omega
      exact h_odd_nf (io_star + 2) ho2_odd h_o2_front
    let ig := io_star + 1
    have hig_even : ig.val % 2 = 0 := by
      dsimp [ig]; rw [fin_succ_val_parity h_even_size io_star]; omega
    have h2_eq : io_star + 2 = io_min := by
      have hfn : (2 : Fin (m + 3)) = io_min - io_star := by
        ext; rw [h2_val, ← hdiff_eq2]
      rw [hfn, add_sub_cancel]
    have hig_next : ig + 1 = io_min := by
      dsimp [ig]; rw [add_assoc, h11, h2_eq]
    have hig_front : IsFrontVertexOf S C (cyc.toFun ig) v := by
      rw [isFrontVertexOf_iff_ccwCycle cyc ig v]
      have hm1 : ig - 1 = io_star := by dsimp [ig]; abel
      have h_e2 : orient2D (S (cyc.toFun ig)) (S (cyc.toFun io_min)) v < 0 := by
        have : ig = io_min - 1 := by rw [← hig_next]; abel
        rwa [← this] at he_min_m1
      rw [hm1, hig_next]; exact ⟨he_star_p1, h_e2⟩
    let b := io_star - 1
    have hb_even : b.val % 2 = 0 := hstar_m1_ev
    have h_ang_b := h_even_gt b hb_even
    have hvb_min : 0 < orient2D v (S (cyc.toFun io_min)) (S (cyc.toFun b)) := by
      have h2 := h_ang_b.2; nlinarith only [hmin_q, h2]
    have hmin_b_ccw : 0 < orient2D (S (cyc.toFun io_min)) (S (cyc.toFun b)) (S (cyc.toFun io_star)) := by
      have h1 : (b - io_min).val = m := by
        have hbe : b - io_min = (io_star - io_min) - 1 := by dsimp [b]; abel
        have h_star_min : (io_star - io_min).val = m + 1 := by
          have := fin_sub_add_compl hmin_neq_star; omega
        rw [hbe, fin_val_sub_eq, if_pos (Fin.le_def.mpr (by rw [h1_val]; omega)), h1_val, h_star_min]
        omega
      have h2 : (io_star - io_min).val = m + 1 := by
        have := fin_sub_add_compl hmin_neq_star; omega
      exact ccwCycle_ccw3 cyc (by rw [h1]; omega) (by rw [h1, h2]; omega)
    have h_min_star_pos : 0 < orient2D v (S (cyc.toFun io_min)) (S (cyc.toFun io_star)) := by
      by_contra hle
      have hne0 : orient2D v (S (cyc.toFun io_min)) (S (cyc.toFun io_star)) ≠ 0 := by
        have hnc := hv_noncol io_min io_star hmin_neq_star
        unfold orient2D at hnc ⊢; intro h; apply hnc; linarith
      have hlt' : orient2D v (S (cyc.toFun io_min)) (S (cyc.toFun io_star)) < 0 :=
        lt_of_le_of_ne (not_lt.mp hle) hne0
      have h1 : 0 < orient2D (S (cyc.toFun io_min)) (S (cyc.toFun b)) v := by
        unfold orient2D at hvb_min ⊢; linarith
      have h2 : 0 < orient2D (S (cyc.toFun b)) (S (cyc.toFun io_star)) v := he_star_m1
      have h3 : 0 < orient2D (S (cyc.toFun io_star)) (S (cyc.toFun io_min)) v := by
        unfold orient2D at hlt' ⊢; linarith
      have hin := (inIntTri_iff_orient_pos hmin_b_ccw).mpr ⟨h1, h2, h3⟩
      have hnf0 := h_inTri_nonfacing io_min b io_star hin (io_min - 1)
      rw [sub_add_cancel] at hnf0
      linarith only [hnf0, he_min_m1]
    have hq_ccw : 0 < orient2D q (S (cyc.toFun io_min)) (S (cyc.toFun io_star)) := by
      have hid : orient2D q (S (cyc.toFun io_min)) (S (cyc.toFun io_star)) =
          orient2D v (S (cyc.toFun io_min)) (S (cyc.toFun io_star)) +
          orient2D v q (S (cyc.toFun io_min)) - orient2D v q (S (cyc.toFun io_star)) := by
        unfold orient2D; ring
      linarith only [hid, h_min_star_pos, hmin_q, hstar_q]
    have hv_tri : InIntTri q (S (cyc.toFun io_min)) (S (cyc.toFun io_star)) v :=
      (inIntTri_iff_orient_pos hq_ccw).mpr ⟨by unfold orient2D at hmin_q ⊢; linarith,
        by unfold orient2D at h_min_star_pos ⊢; linarith,
        by unfold orient2D at hstar_q ⊢; linarith⟩
    exact h_no_cert ⟨io_min, io_star, ig, hmin_odd, hio_star_odd, hig_even,
      Or.inl ⟨rfl, hig_next⟩, hsee, hig_front, hv_tri⟩

/-- Core Proposition 6.4 (`good_targets_core`, `upper_9.tex` lines 659–691):
    For `m ∈ {3, 5}` (`2*k = 6` or `8`), any `CCWCycle S C m` with odd set in `O_miss`,
    even set outside `O_miss`, no odd front vertices, and no certified even front obstruction
    yields `k - 2` distinct good targets (`1` for `m = 3`, `2` for `m = 5`). -/
theorem good_targets_core {n m : ℕ} {P : Set (ℝ × ℝ)}
    {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ}
    (hPoly : ShatteredSimplePolygon P S w)
    {C O_miss : Finset (Fin n)} (hm : m = 3 ∨ m = 5)
    (cyc : CCWCycle S C m)
    (hO_odd : ∀ i : Fin (m + 3), i.val % 2 = 1 → cyc.toFun i ∈ O_miss)
    (hO_even : ∀ i : Fin (m + 3), i.val % 2 = 0 → cyc.toFun i ∉ O_miss)
    (h_odd_nf : ∀ i : Fin (m + 3), i.val % 2 = 1 →
      ¬ IsFrontVertexOf S C (cyc.toFun i) (w (Finset.univ \ O_miss)))
    (h_no_cert : ¬ ∃ (io_min io_star ig : Fin (m + 3)),
      io_min.val % 2 = 1 ∧ io_star.val % 2 = 1 ∧ ig.val % 2 = 0 ∧
      ((io_star + 1 = ig ∧ ig + 1 = io_min) ∨ (io_min + 1 = ig ∧ ig + 1 = io_star)) ∧
      ¬ Sees P (w (Finset.univ \ O_miss)) (w Finset.univ) ∧
      IsFrontVertexOf S C (cyc.toFun ig) (w (Finset.univ \ O_miss)) ∧
      InIntTri (w Finset.univ) (S (cyc.toFun io_min)) (S (cyc.toFun io_star)) (w (Finset.univ \ O_miss))) :
    ∃ Tgt : Finset (Fin (m + 3)), Tgt.card = (if m = 3 then 1 else 2) ∧
      ∀ ig ∈ Tgt, ig.val % 2 = 0 ∧
        IsBackVertexOf S C (cyc.toFun ig) (w (Finset.univ \ O_miss)) ∧
        GoodAnchorPair P S w O_miss (cyc.toFun (ig - 1)) (cyc.toFun (ig + 1)) ∧
        ((AngleLt (w (Finset.univ \ O_miss)) (w Finset.univ) (S (cyc.toFun (ig - 1))) (S (cyc.toFun ig)) ∧
          AngleLt (w (Finset.univ \ O_miss)) (w Finset.univ) (S (cyc.toFun ig)) (S (cyc.toFun (ig + 1))) ∧
          0 < orient2D (S (cyc.toFun (ig - 1))) (S (cyc.toFun ig)) (S (cyc.toFun (ig + 1))) ∧
          0 < orient2D (S (cyc.toFun (ig - 1))) (S (cyc.toFun ig)) (w (Finset.univ \ O_miss)) ∧
          0 < orient2D (S (cyc.toFun ig)) (S (cyc.toFun (ig + 1))) (w (Finset.univ \ O_miss))) ∨
         (AngleLt (w (Finset.univ \ O_miss)) (w Finset.univ) (S (cyc.toFun (ig + 1))) (S (cyc.toFun ig)) ∧
          AngleLt (w (Finset.univ \ O_miss)) (w Finset.univ) (S (cyc.toFun ig)) (S (cyc.toFun (ig - 1))) ∧
          0 < orient2D (S (cyc.toFun (ig - 1))) (S (cyc.toFun ig)) (S (cyc.toFun (ig + 1))) ∧
          0 < orient2D (S (cyc.toFun (ig - 1))) (S (cyc.toFun ig)) (w (Finset.univ \ O_miss)) ∧
          0 < orient2D (S (cyc.toFun ig)) (S (cyc.toFun (ig + 1))) (w (Finset.univ \ O_miss)))) := by
  let Tv := Finset.univ \ O_miss
  let v := w Tv
  let q := w Finset.univ
  have hm_odd : m % 2 = 1 := by rcases hm with rfl | rfl <;> decide
  have hm1 : 1 ≤ m := by rcases hm with rfl | rfl <;> omega
  have hk_val : (m + 3) = 2 * (if m = 3 then 3 else 4) := by
    rcases hm with rfl | rfl <;> decide
  let k := if m = 3 then 3 else 4
  have hk : k = 3 ∨ k = 4 := by dsimp [k]; split_ifs <;> [exact Or.inl rfl; exact Or.inr rfl]
  have hv_ne_q : v ≠ q := by
    intro h
    have hmem : cyc.toFun 1 ∈ O_miss := hO_odd 1 (by
      have : (1 : Fin (m + 3)).val = 1 := Nat.mod_eq_of_lt (show 1 < m + 3 by omega)
      rw [this])
    have h1_Tv : cyc.toFun 1 ∈ Tv := by
      have hs : Sees P v (S (cyc.toFun 1)) := by
        rw [h]; exact (hPoly.shatters Finset.univ (cyc.toFun 1)).mpr (Finset.mem_univ _)
      exact (hPoly.shatters Tv (cyc.toFun 1)).mp hs
    exact (Finset.mem_sdiff.mp h1_Tv).2 hmem
  have hv_noncol : ∀ i j : Fin (m + 3), i ≠ j → orient2D (S (cyc.toFun i)) (S (cyc.toFun j)) v ≠ 0 :=
    fun i j hij => hPoly.no_three_collinear _ _ _
      (Or.inl (Set.mem_range_self _)) (Or.inl (Set.mem_range_self _)) (Or.inr (Set.mem_range_self _))
      (hPoly.s_inj.ne (cyc.inj.ne hij)) (hPoly.s_ne_w _ _) (hPoly.s_ne_w _ _)
  have hvq : ∀ i : Fin (m + 3), orient2D v q (S (cyc.toFun i)) ≠ 0 :=
    fun i => hPoly.no_three_collinear _ _ _
      (Or.inr (Set.mem_range_self _)) (Or.inr (Set.mem_range_self _)) (Or.inl (Set.mem_range_self _))
      (hPoly.w_inj.ne (fun heq => hv_ne_q (congrArg w heq)))
      (hPoly.s_ne_w _ _).symm (hPoly.s_ne_w _ _).symm
  let oddIdx := (Finset.univ : Finset (Fin (m + 3))).filter (fun i => i.val % 2 = 1)
  let oddPos := oddIdx.filter (fun i => 0 < orient2D v q (S (cyc.toFun i)))
  let oddNeg := oddIdx.filter (fun i => orient2D v q (S (cyc.toFun i)) < 0)
  have hodd_card : oddIdx.card = k := by
    rcases hm with rfl | rfl <;> decide
  have hdisj : Disjoint oddPos oddNeg := by
    rw [Finset.disjoint_left]
    intro x hx hy
    have hp := (Finset.mem_filter.mp hx).2
    have hn := (Finset.mem_filter.mp hy).2
    linarith
  have hunion : oddPos ∪ oddNeg = oddIdx := by
    ext x
    simp only [Finset.mem_union, oddPos, oddNeg, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
    · intro hx
      rcases lt_or_gt_of_ne (hvq x) with hn | hp
      · exact Or.inr ⟨hx, hn⟩
      · exact Or.inl ⟨hx, hp⟩
  have hsum_card : oddPos.card + oddNeg.card = k := by
    rw [← Finset.card_union_of_disjoint hdisj, hunion, hodd_card]
  have h_even_size : (m + 3) % 2 = 0 := by rcases hm with rfl | rfl <;> decide
  have h_inTri_nonfacing : ∀ (a b c : Fin (m + 3)),
      InIntTri (S (cyc.toFun a)) (S (cyc.toFun b)) (S (cyc.toFun c)) v →
      ∀ j : Fin (m + 3), 0 ≤ orient2D (S (cyc.toFun j)) (S (cyc.toFun (j + 1))) v := by
    intro a b c hin j
    rcases hin with ⟨μ₁, μ₂, μ₃, h1, h2, h3, hsum, hv1, hv2⟩
    have hid := orient2D_convex_comb3 (S (cyc.toFun j)) (S (cyc.toFun (j + 1)))
      (S (cyc.toFun a)) (S (cyc.toFun b)) (S (cyc.toFun c)) v μ₁ μ₂ μ₃ hsum hv1 hv2
    rw [hid]
    have ha := strictConvexCCW_orient_nonneg (S ∘ cyc.toFun) cyc.ccw j a
    have hb := strictConvexCCW_orient_nonneg (S ∘ cyc.toFun) cyc.ccw j b
    have hc := strictConvexCCW_orient_nonneg (S ∘ cyc.toFun) cyc.ccw j c
    exact add_nonneg (add_nonneg (mul_nonneg (le_of_lt h1) ha) (mul_nonneg (le_of_lt h2) hb))
      (mul_nonneg (le_of_lt h3) hc)
  have h_adj_ne : ∀ i : Fin (m + 3), i - 1 ≠ i + 1 := by
    intro i h
    have h' := congrArg (· + (1 : Fin (m + 3))) h
    rw [sub_add_cancel, add_assoc] at h'
    nth_rw 1 [← add_zero i] at h'
    have h02 : (0 : Fin (m + 3)) = 2 := add_left_cancel h'
    have hv := congrArg Fin.val h02
    simp [Nat.mod_eq_of_lt (by omega : 2 < m + 3)] at hv
  by_cases hsee : Sees P v q
  · -- Case 1: `v` sees `q`: all targets from `oddPos` and `oddNeg` are good!
    obtain ⟨fP, hfP_inj, hfP, _⟩ := targets_of_oddSide hm_odd hm1 cyc v q hv_noncol hvq h_odd_nf oddPos
      (fun i hi => (Finset.mem_filter.mp (Finset.mem_filter.mp hi).1).2)
      (fun i hi ⟨o0, ho0, hss⟩ => by
        refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩, ?_⟩
        have h0 := (Finset.mem_filter.mp ho0).2
        unfold OnSameSide at hss; nlinarith)
      (fun i hi j hj => by
        have h1 := (Finset.mem_filter.mp hi).2
        have h2 := (Finset.mem_filter.mp hj).2
        exact mul_pos h1 h2)
    obtain ⟨fN, hfN_inj, hfN, _⟩ := targets_of_oddSide hm_odd hm1 cyc v q hv_noncol hvq h_odd_nf oddNeg
      (fun i hi => (Finset.mem_filter.mp (Finset.mem_filter.mp hi).1).2)
      (fun i hi ⟨o0, ho0, hss⟩ => by
        refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩, ?_⟩
        have h0 := (Finset.mem_filter.mp ho0).2
        unfold OnSameSide at hss; nlinarith)
      (fun i hi j hj => by
        have h1 := (Finset.mem_filter.mp hi).2
        have h2 := (Finset.mem_filter.mp hj).2
        exact mul_pos_of_neg_of_neg h1 h2)
    let Tpos := Finset.univ.image fP
    let Tneg := Finset.univ.image fN
    have hdisj_pn : Disjoint Tpos Tneg := by
      rw [Finset.disjoint_left]
      intro ig h1 h2
      rcases Finset.mem_image.mp h1 with ⟨t1, _, rfl⟩
      rcases Finset.mem_image.mp h2 with ⟨t2, _, heq⟩
      have hpos1 := (Finset.mem_filter.mp (hfP t1).2.1).2
      have hneg1 := (Finset.mem_filter.mp (hfN t2).2.1).2
      rw [heq] at hneg1
      linarith
    have hT_all : ∀ ig ∈ Tpos ∪ Tneg, ig.val % 2 = 0 ∧
        IsBackVertexOf S C (cyc.toFun ig) v ∧
        GoodAnchorPair P S w O_miss (cyc.toFun (ig - 1)) (cyc.toFun (ig + 1)) ∧
        ((AngleLt v q (S (cyc.toFun (ig - 1))) (S (cyc.toFun ig)) ∧
          AngleLt v q (S (cyc.toFun ig)) (S (cyc.toFun (ig + 1))) ∧
          0 < orient2D (S (cyc.toFun (ig - 1))) (S (cyc.toFun ig)) (S (cyc.toFun (ig + 1))) ∧
          0 < orient2D (S (cyc.toFun (ig - 1))) (S (cyc.toFun ig)) v ∧
          0 < orient2D (S (cyc.toFun ig)) (S (cyc.toFun (ig + 1))) v) ∨
         (AngleLt v q (S (cyc.toFun (ig + 1))) (S (cyc.toFun ig)) ∧
          AngleLt v q (S (cyc.toFun ig)) (S (cyc.toFun (ig - 1))) ∧
          0 < orient2D (S (cyc.toFun (ig - 1))) (S (cyc.toFun ig)) (S (cyc.toFun (ig + 1))) ∧
          0 < orient2D (S (cyc.toFun (ig - 1))) (S (cyc.toFun ig)) v ∧
          0 < orient2D (S (cyc.toFun ig)) (S (cyc.toFun (ig + 1))) v)) := by
      intro ig hig
      have h_from : ∀ {X : Finset (Fin (m + 3))} {f : Fin (X.card - 1) → Fin (m + 3)},
          (∀ t, (f t).val % 2 = 0 ∧ f t - 1 ∈ X ∧ f t + 1 ∈ X ∧
            (f t - 1).val % 2 = 1 ∧ (f t + 1).val % 2 = 1 ∧
            IsBackVertexOf S C (cyc.toFun (f t)) v ∧
            OnSameSide v q (S (cyc.toFun (f t - 1))) (S (cyc.toFun (f t + 1))) ∧
            (1 ≤ t.val → ∃ t0, t0.val < t.val ∧
              AngleLt v q (S (cyc.toFun (f t0))) (S (cyc.toFun (f t - 1))) ∧
              AngleLt v q (S (cyc.toFun (f t0))) (S (cyc.toFun (f t + 1)))) ∧
            ((AngleLt v q (S (cyc.toFun (f t - 1))) (S (cyc.toFun (f t))) ∧
              AngleLt v q (S (cyc.toFun (f t))) (S (cyc.toFun (f t + 1))) ∧
              0 < orient2D (S (cyc.toFun (f t - 1))) (S (cyc.toFun (f t))) (S (cyc.toFun (f t + 1))) ∧
              0 < orient2D (S (cyc.toFun (f t - 1))) (S (cyc.toFun (f t))) v ∧
              0 < orient2D (S (cyc.toFun (f t))) (S (cyc.toFun (f t + 1))) v) ∨
             (AngleLt v q (S (cyc.toFun (f t + 1))) (S (cyc.toFun (f t))) ∧
              AngleLt v q (S (cyc.toFun (f t))) (S (cyc.toFun (f t - 1))) ∧
              0 < orient2D (S (cyc.toFun (f t - 1))) (S (cyc.toFun (f t))) (S (cyc.toFun (f t + 1))) ∧
              0 < orient2D (S (cyc.toFun (f t - 1))) (S (cyc.toFun (f t))) v ∧
              0 < orient2D (S (cyc.toFun (f t))) (S (cyc.toFun (f t + 1))) v))) →
          ∀ t,
            (f t).val % 2 = 0 ∧
            IsBackVertexOf S C (cyc.toFun (f t)) v ∧
            GoodAnchorPair P S w O_miss (cyc.toFun (f t - 1)) (cyc.toFun (f t + 1)) ∧
            ((AngleLt v q (S (cyc.toFun (f t - 1))) (S (cyc.toFun (f t))) ∧
              AngleLt v q (S (cyc.toFun (f t))) (S (cyc.toFun (f t + 1))) ∧
              0 < orient2D (S (cyc.toFun (f t - 1))) (S (cyc.toFun (f t))) (S (cyc.toFun (f t + 1))) ∧
              0 < orient2D (S (cyc.toFun (f t - 1))) (S (cyc.toFun (f t))) v ∧
              0 < orient2D (S (cyc.toFun (f t))) (S (cyc.toFun (f t + 1))) v) ∨
             (AngleLt v q (S (cyc.toFun (f t + 1))) (S (cyc.toFun (f t))) ∧
              AngleLt v q (S (cyc.toFun (f t))) (S (cyc.toFun (f t - 1))) ∧
              0 < orient2D (S (cyc.toFun (f t - 1))) (S (cyc.toFun (f t))) (S (cyc.toFun (f t + 1))) ∧
              0 < orient2D (S (cyc.toFun (f t - 1))) (S (cyc.toFun (f t))) v ∧
              0 < orient2D (S (cyc.toFun (f t))) (S (cyc.toFun (f t + 1))) v)) := by
        intro X f hf t
        rcases hf t with ⟨heven, _, _, hm1, hp1, hback, _, _, htri⟩
        refine ⟨heven, hback, ⟨hO_odd _ hm1, hO_odd _ hp1, fun h => h_adj_ne _ (cyc.inj h), ?_⟩, htri⟩
        rcases htri with ⟨a1, a2, _⟩ | ⟨a1, a2, _⟩
        · exact Or.inl ⟨a1.trans a2, Or.inl hsee⟩
        · exact Or.inr ⟨a1.trans a2, Or.inl hsee⟩
      rcases Finset.mem_union.mp hig with h | h
      · rcases Finset.mem_image.mp h with ⟨t, _, rfl⟩; exact h_from hfP t
      · rcases Finset.mem_image.mp h with ⟨t, _, rfl⟩; exact h_from hfN t
    have hcount : (if m = 3 then 1 else 2) ≤ (Tpos ∪ Tneg).card := by
      have hcP : Tpos.card = oddPos.card - 1 := by
        rw [Finset.card_image_of_injective _ hfP_inj, Finset.card_fin]
      have hcN : Tneg.card = oddNeg.card - 1 := by
        rw [Finset.card_image_of_injective _ hfN_inj, Finset.card_fin]
      rw [Finset.card_union_of_disjoint hdisj_pn, hcP, hcN]
      have hcnt := (prop_good_targets_counting k oddPos.card hk (by omega)).1
      have hN : oddNeg.card = k - oddPos.card := by omega
      rw [hN]
      refine le_trans ?_ hcnt
      rcases hm with rfl | rfl <;> dsimp [k] <;> decide
    obtain ⟨Tgt, hsub, hcard⟩ := Finset.exists_subset_card_eq hcount
    exact ⟨Tgt, hcard, fun ig hig => hT_all _ (hsub hig)⟩
  · -- Case 2: `¬ Sees P v q`: all even vertices lie on one open side `L` of `G = v q`.
    have hseen_ss := seen_same_side_of_misses_q hPoly hsee
    have heven_ss : ∀ i j : Fin (m + 3), i.val % 2 = 0 → j.val % 2 = 0 →
        0 < orient2D v q (S (cyc.toFun i)) * orient2D v q (S (cyc.toFun j)) := by
      intro i j hi hj
      have hiTv : cyc.toFun i ∈ Tv := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hO_even i hi⟩
      have hjTv : cyc.toFun j ∈ Tv := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hO_even j hj⟩
      exact hseen_ss (cyc.toFun i) (cyc.toFun j) hiTv hjTv
    -- Common lemma: at most 1 odd vertex can lie strictly opposite to `S (cyc.toFun 0)`:
    have hR_le_one : ∀ R : Finset (Fin (m + 3)),
        (∀ i ∈ R, i.val % 2 = 1 ∧ orient2D v q (S (cyc.toFun 0)) * orient2D v q (S (cyc.toFun i)) < 0) →
        R.card ≤ 1 := by
      intro R hR
      refine Finset.card_le_one.mpr (fun x hx y hy => ?_)
      by_contra hxy
      have hx_odd := (hR x hx).1
      have hy_odd := (hR y hy).1
      have hxp1_even : (x + 1).val % 2 = 0 := by
        rw [fin_succ_val_parity h_even_size x]; omega
      have hyp1_even : (y + 1).val % 2 = 0 := by
        rw [fin_succ_val_parity h_even_size y]; omega
      have hdiff_ev : (y - x).val % 2 = 0 := by
        rw [fin_val_sub_eq]; split_ifs with hle
        · have : x.val ≤ y.val := Fin.le_def.mp hle; omega
        · have : y.val < x.val := Fin.lt_def.mp (lt_of_not_ge hle); omega
      have hxy_pos : 0 < (y - x).val := Nat.pos_of_ne_zero (fun h => hxy (sub_eq_zero.mp (Fin.ext h)).symm)
      have hxy_ge2 : 2 ≤ (y - x).val := by omega
      have hxy_lt_m1 : (y - x).val ≤ m + 1 := by
        have hcomp := fin_sub_add_compl hxy
        have hyx_pos : 0 < (x - y).val := Nat.pos_of_ne_zero (fun h => hxy (sub_eq_zero.mp (Fin.ext h)))
        have hyx_ev : (x - y).val % 2 = 0 := by
          rw [fin_val_sub_eq]; split_ifs with hle
          · have : y.val ≤ x.val := Fin.le_def.mp hle; omega
          · have : x.val < y.val := Fin.lt_def.mp (lt_of_not_ge hle); omega
        omega
      have h1_val : (1 : Fin (m + 3)).val = 1 := by
        rcases hm with rfl | rfl <;> decide
      have hx1_val : (x + 1 - x).val = 1 := by
        rw [add_sub_cancel_left]; exact h1_val
      have hy1_val : (y + 1 - x).val = (y - x).val + 1 := by
        have heq : y + 1 - x = (y - x) + 1 := by abel
        rw [heq, Fin.val_add, h1_val]
        exact Nat.mod_eq_of_lt (by omega)
      have ⟨ho1, ho2, ho3, ho4⟩ := ccwCycle_fourgon_orient cyc x (x + 1) y (y + 1)
        (by rw [hx1_val]; omega) (by rw [hx1_val]; omega) (by rw [hy1_val]; omega)
      have halt := convex_fourgon_no_alternating_line
        (S (cyc.toFun x)) (S (cyc.toFun (x + 1))) (S (cyc.toFun y)) (S (cyc.toFun (y + 1))) v q
        ho1 ho2 ho3 ho4
      have hx_opp := (hR x hx).2
      have hy_opp := (hR y hy).2
      have hxp1_ss := heven_ss 0 (x + 1) (by rw [Fin.val_zero]) hxp1_even
      have hyp1_ss := heven_ss 0 (y + 1) (by rw [Fin.val_zero]) hyp1_even
      rcases lt_or_gt_of_ne (hvq 0) with h0n | h0p
      · exact halt.1 ⟨by nlinarith only [hx_opp, h0n], by nlinarith only [hxp1_ss, h0n],
          by nlinarith only [hy_opp, h0n], by nlinarith only [hyp1_ss, h0n]⟩
      · exact halt.2 ⟨by nlinarith only [hx_opp, h0p], by nlinarith only [hxp1_ss, h0p],
          by nlinarith only [hy_opp, h0p], by nlinarith only [hyp1_ss, h0p]⟩
    -- Partition `oddIdx` into `L_odd` (same side as `0`) and `R_odd` (opposite to `0`):
    let L_odd := oddIdx.filter (fun i => 0 < orient2D v q (S (cyc.toFun 0)) * orient2D v q (S (cyc.toFun i)))
    let R_odd := oddIdx.filter (fun i => orient2D v q (S (cyc.toFun 0)) * orient2D v q (S (cyc.toFun i)) < 0)
    have hdisj_LR : Disjoint L_odd R_odd := by
      rw [Finset.disjoint_left]; intro x h1 h2
      have hp := (Finset.mem_filter.mp h1).2
      have hn := (Finset.mem_filter.mp h2).2
      linarith
    have hunion_LR : L_odd ∪ R_odd = oddIdx := by
      ext x
      simp only [Finset.mem_union, L_odd, R_odd, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
      · intro hx
        have hne : orient2D v q (S (cyc.toFun 0)) * orient2D v q (S (cyc.toFun x)) ≠ 0 :=
          mul_ne_zero (hvq 0) (hvq x)
        rcases lt_or_gt_of_ne hne with hn | hp
        · exact Or.inr ⟨hx, hn⟩
        · exact Or.inl ⟨hx, hp⟩
    have hLR_sum : L_odd.card + R_odd.card = k := by
      rw [← Finset.card_union_of_disjoint hdisj_LR, hunion_LR, hodd_card]
    have hR_card : R_odd.card ≤ 1 :=
      hR_le_one R_odd (fun i hi => ⟨(Finset.mem_filter.mp (Finset.mem_filter.mp hi).1).2, (Finset.mem_filter.mp hi).2⟩)
    have hL_ge : k - 1 ≤ L_odd.card := by omega
    obtain ⟨fL, hfL_inj, hfL, hfL_first⟩ := targets_of_oddSide hm_odd hm1 cyc v q hv_noncol hvq h_odd_nf L_odd
      (fun i hi => (Finset.mem_filter.mp (Finset.mem_filter.mp hi).1).2)
      (fun i hi ⟨o0, ho0, hss⟩ => by
        refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩, ?_⟩
        have h0 := (Finset.mem_filter.mp ho0).2
        unfold OnSameSide at hss
        have hsq : 0 < orient2D v q (S (cyc.toFun o0)) ^ 2 := sq_pos_of_ne_zero (hvq o0)
        nlinarith)
      (fun i hi j hj => by
        have h1 := (Finset.mem_filter.mp hi).2
        have h2 := (Finset.mem_filter.mp hj).2
        have hsq : 0 < orient2D v q (S (cyc.toFun 0)) ^ 2 := sq_pos_of_ne_zero (hvq 0)
        unfold OnSameSide; nlinarith)
    have h_t_ge1_good : ∀ t : Fin (L_odd.card - 1), 1 ≤ t.val →
        (fL t).val % 2 = 0 ∧
        IsBackVertexOf S C (cyc.toFun (fL t)) v ∧
        GoodAnchorPair P S w O_miss (cyc.toFun (fL t - 1)) (cyc.toFun (fL t + 1)) ∧
        ((AngleLt v q (S (cyc.toFun (fL t - 1))) (S (cyc.toFun (fL t))) ∧
          AngleLt v q (S (cyc.toFun (fL t))) (S (cyc.toFun (fL t + 1))) ∧
          0 < orient2D (S (cyc.toFun (fL t - 1))) (S (cyc.toFun (fL t))) (S (cyc.toFun (fL t + 1))) ∧
          0 < orient2D (S (cyc.toFun (fL t - 1))) (S (cyc.toFun (fL t))) v ∧
          0 < orient2D (S (cyc.toFun (fL t))) (S (cyc.toFun (fL t + 1))) v) ∨
         (AngleLt v q (S (cyc.toFun (fL t + 1))) (S (cyc.toFun (fL t))) ∧
          AngleLt v q (S (cyc.toFun (fL t))) (S (cyc.toFun (fL t - 1))) ∧
          0 < orient2D (S (cyc.toFun (fL t - 1))) (S (cyc.toFun (fL t))) (S (cyc.toFun (fL t + 1))) ∧
          0 < orient2D (S (cyc.toFun (fL t - 1))) (S (cyc.toFun (fL t))) v ∧
          0 < orient2D (S (cyc.toFun (fL t))) (S (cyc.toFun (fL t + 1))) v)) := by
      intro t ht1
      rcases hfL t with ⟨heven, _, _, hm1, hp1, hback, _, h_e, htri⟩
      obtain ⟨t0, _, hlt_m1, hlt_p1⟩ := h_e ht1
      have ht0_even : cyc.toFun (fL t0) ∉ O_miss := hO_even _ (hfL t0).1
      refine ⟨heven, hback, ⟨hO_odd _ hm1, hO_odd _ hp1, fun h => h_adj_ne _ (cyc.inj h), ?_⟩, htri⟩
      rcases htri with ⟨a1, a2, _⟩ | ⟨a1, a2, _⟩
      · exact Or.inl ⟨a1.trans a2, Or.inr ⟨cyc.toFun (fL t0), ht0_even, hlt_m1⟩⟩
      · exact Or.inr ⟨a1.trans a2, Or.inr ⟨cyc.toFun (fL t0), ht0_even, hlt_p1⟩⟩
    by_cases hLk : L_odd.card = k
    · -- All `k - 2` targets `t = 1 .. k - 2` are good!
      let Tgt := (Finset.univ.filter (fun t : Fin (L_odd.card - 1) => 1 ≤ t.val)).image fL
      have hcard_flt : (Finset.univ.filter (fun t : Fin (L_odd.card - 1) => 1 ≤ t.val)).card =
          if m = 3 then 1 else 2 := by
        have hlen_sub : L_odd.card - 1 = k - 1 := by omega
        have h1 : ∀ N : ℕ, 1 ≤ N →
            ((Finset.univ : Finset (Fin N)).filter (fun t => 1 ≤ t.val)).card = N - 1 := by
          intro N hN
          have heq : (Finset.univ : Finset (Fin N)).filter (fun t => 1 ≤ t.val) =
              Finset.univ.erase ⟨0, hN⟩ := by
            ext t; simp [Fin.ext_iff]; omega
          rw [heq, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
        rw [h1 (L_odd.card - 1) (by dsimp [k] at hLk ⊢; split_ifs at * <;> omega)]
        rcases hm with rfl | rfl <;> dsimp [k] at hLk ⊢ <;> omega
      have hcard_T : Tgt.card = if m = 3 then 1 else 2 := by
        rw [Finset.card_image_of_injective _ hfL_inj, hcard_flt]
      refine ⟨Tgt, hcard_T, fun ig hig => ?_⟩
      rcases Finset.mem_image.mp hig with ⟨t, ht, rfl⟩
      exact h_t_ge1_good t (Finset.mem_filter.mp ht).2
    · -- `L_odd.card = k - 1` and `R_odd.card = 1`: show `t = 0` is ALSO good!
      have hLk1 : L_odd.card = k - 1 := by omega
      have hRk1 : R_odd.card = 1 := by omega
      obtain ⟨io_star, hio_star_mem⟩ := Finset.card_eq_one.mp hRk1
      have hio_star_R : io_star ∈ R_odd := by rw [hio_star_mem]; simp
      have hio_star_odd : io_star.val % 2 = 1 :=
        (Finset.mem_filter.mp (Finset.mem_filter.mp hio_star_R).1).2
      have hio_star_opp : orient2D v q (S (cyc.toFun 0)) * orient2D v q (S (cyc.toFun io_star)) < 0 :=
        (Finset.mem_filter.mp hio_star_R).2
      have hL_ge2 : 2 ≤ L_odd.card := by rcases hm with rfl | rfl <;> dsimp [k] at hLk1 <;> omega
      let t0 : Fin (L_odd.card - 1) := ⟨0, by omega⟩
      have h0_good : GoodAnchorPair P S w O_miss (cyc.toFun (fL t0 - 1)) (cyc.toFun (fL t0 + 1)) := by
        by_contra hnot_good
        rcases hfL t0 with ⟨heven0, hm1L, hp1L, hm1_odd, hp1_odd, _, _, _, htri0⟩
        have h_tot_lt : ∀ a b : Fin (m + 3), a ≠ b → OnSameSide v q (S (cyc.toFun a)) (S (cyc.toFun b)) →
            AngleLt v q (S (cyc.toFun a)) (S (cyc.toFun b)) ∨
            AngleLt v q (S (cyc.toFun b)) (S (cyc.toFun a)) := by
          intro a b hab hss
          have hne := hv_noncol a b hab
          rcases lt_or_gt_of_ne (by unfold orient2D at hne ⊢; intro h; apply hne; linarith :
              orient2D v (S (cyc.toFun a)) (S (cyc.toFun b)) ≠ 0) with hneg | hpos
          · rcases lt_or_gt_of_ne (hvq a) with hqa | hqa
            · left; exact angleLt_of_orient_sameSide hss (fun h => False.elim (by linarith)) (fun _ => hneg)
            · right; refine angleLt_of_orient_sameSide hss.symm (fun _ => ?_) (fun h => ?_)
              · unfold orient2D at hneg ⊢; linarith
              · unfold OnSameSide at hss; nlinarith only [hss, hqa, h]
          · rcases lt_or_gt_of_ne (hvq a) with hqa | hqa
            · right; refine angleLt_of_orient_sameSide hss.symm (fun h => ?_) (fun _ => ?_)
              · unfold OnSameSide at hss; nlinarith only [hss, hqa, h]
              · unfold orient2D at hpos ⊢; linarith
            · left; exact angleLt_of_orient_sameSide hss (fun _ => hpos) (fun h => False.elim (by linarith))
        have h_even_anchor_gt : ∀ (io : Fin (m + 3)), io ∈ L_odd →
            (∀ y : Fin (m + 3), y.val % 2 = 0 → ¬ AngleLt v q (S (cyc.toFun y)) (S (cyc.toFun io))) →
            ∀ y : Fin (m + 3), y.val % 2 = 0 → AngleLt v q (S (cyc.toFun io)) (S (cyc.toFun y)) := by
          intro io hioL hno y hy_even
          have hss : OnSameSide v q (S (cyc.toFun io)) (S (cyc.toFun y)) := by
            have h1 := (Finset.mem_filter.mp hioL).2
            have h2 := heven_ss 0 y (by rw [Fin.val_zero]) hy_even
            have hsq : 0 < orient2D v q (S (cyc.toFun 0)) ^ 2 := sq_pos_of_ne_zero (hvq 0)
            unfold OnSameSide; nlinarith only [h1, h2, hsq]
          have hne : io ≠ y := fun h => by
            have ho := (Finset.mem_filter.mp (Finset.mem_filter.mp hioL).1).2
            rw [h] at ho; omega
          rcases h_tot_lt io y hne hss with h | h
          · exact h
          · exact False.elim (hno y hy_even h)
        rcases hfL t0 with ⟨_, hm1L, hp1L, hm1_odd, hp1_odd, _, _, _, htri0⟩
        rcases htri0 with ⟨a1, a2, _⟩ | ⟨a1, a2, _⟩
        · exact good_targets_core_min_contradict hm cyc h_odd_nf h_no_cert hv_noncol hvq
            h_inTri_nonfacing hsee heven_ss hm1_odd hio_star_odd
            (Finset.mem_filter.mp hm1L).2 hio_star_opp
            (h_even_anchor_gt _ hm1L (fun y hy hlt => hnot_good
              ⟨hO_odd _ hm1_odd, hO_odd _ hp1_odd, fun he => h_adj_ne _ (cyc.inj he),
               Or.inl ⟨a1.trans a2, Or.inr ⟨cyc.toFun y, hO_even y hy, hlt⟩⟩⟩))
        · exact good_targets_core_min_contradict hm cyc h_odd_nf h_no_cert hv_noncol hvq
            h_inTri_nonfacing hsee heven_ss hp1_odd hio_star_odd
            (Finset.mem_filter.mp hp1L).2 hio_star_opp
            (h_even_anchor_gt _ hp1L (fun y hy hlt => hnot_good
              ⟨hO_odd _ hm1_odd, hO_odd _ hp1_odd, fun he => h_adj_ne _ (cyc.inj he),
               Or.inr ⟨a1.trans a2, Or.inr ⟨cyc.toFun y, hO_even y hy, hlt⟩⟩⟩))
      -- Now select `t = 0` (for `m = 3`) or `t ∈ {0, 1}` (for `m = 5`):
      let Tgt := (Finset.univ.filter (fun t : Fin (L_odd.card - 1) => t.val < if m = 3 then 1 else 2)).image fL
      have hcard_flt : (Finset.univ.filter (fun t : Fin (L_odd.card - 1) => t.val < if m = 3 then 1 else 2)).card =
          if m = 3 then 1 else 2 := by
        rcases hm with rfl | rfl <;> dsimp [k] at hLk1
        · have heq : L_odd.card - 1 = 1 := by omega
          simp only [↓reduceIte]
          have : Finset.univ.filter (fun t : Fin (L_odd.card - 1) => t.val < 1) = Finset.univ := by
            ext t; simp; omega
          rw [this, Finset.card_univ, Fintype.card_fin, heq]
        · have heq : L_odd.card - 1 = 2 := by omega
          simp only [show ¬ (5 = 3) by decide, ↓reduceIte]
          have : Finset.univ.filter (fun t : Fin (L_odd.card - 1) => t.val < 2) = Finset.univ := by
            ext t; simp; omega
          rw [this, Finset.card_univ, Fintype.card_fin, heq]
      refine ⟨Tgt, by rw [Finset.card_image_of_injective _ hfL_inj, hcard_flt], fun ig hig => ?_⟩
      rcases Finset.mem_image.mp hig with ⟨t, ht, rfl⟩
      by_cases ht0' : t = t0
      · subst ht0'
        rcases hfL t0 with ⟨heven, _, _, _, _, hback, _, _, htri⟩
        exact ⟨heven, hback, h0_good, htri⟩
      · have ht1 : 1 ≤ t.val := by
          have : t.val ≠ 0 := fun h => ht0' (Fin.ext h)
          omega
        exact h_t_ge1_good t ht1

/-- Proposition 6.4 (`good-targets`, `upper_9.tex` lines 659–691) for `C ⊆ D` of size 6 or 8. -/
theorem good_targets {n m : ℕ} {P : Set (ℝ × ℝ)}
    {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ}
    (hPoly : ShatteredSimplePolygon P S w) (h25 : Sec2To5Interface P S w)
    {C : Finset (Fin n)} (hm : m = 3 ∨ m = 5)
    (hCD : C ⊆ hullVertices S \ certifiedVertices S w)
    (cyc : CCWCycle S C m) :
    let O_miss := C.filter (fun x => ∃ i : Fin (m + 3), i.val % 2 = 1 ∧ cyc.toFun i = x)
    ∃ Tgt : Finset (Fin (m + 3)), Tgt.card = (if m = 3 then 1 else 2) ∧
      ∀ ig ∈ Tgt, ig.val % 2 = 0 ∧
        IsBackVertexOf S C (cyc.toFun ig) (w (Finset.univ \ O_miss)) ∧
        IsBackVertexOf S (hullVertices S) (cyc.toFun ig) (w (Finset.univ \ O_miss)) ∧
        GoodAnchorPair P S w O_miss (cyc.toFun (ig - 1)) (cyc.toFun (ig + 1)) ∧
        SegmentsCross (w (Finset.univ \ O_miss)) (S (cyc.toFun ig))
          (S (cyc.toFun (ig - 1))) (S (cyc.toFun (ig + 1))) ∧
        (∃ H_hp : OpenHalfPlane, IsHalfPlaneTest P
          (WitnessSet {cyc.toFun (ig - 1), cyc.toFun (ig + 1)} ∅ w) (S (cyc.toFun ig)) H_hp) ∧
        (∀ z : Fin n, z ≠ cyc.toFun (ig - 1) → z ≠ cyc.toFun (ig + 1) → z ∉ O_miss →
          S z ∈ convexHull ℝ ((hullVertices S).image S : Set (ℝ × ℝ)) →
          0 < orient2D (S (cyc.toFun (ig - 1))) (S (cyc.toFun (ig + 1))) (S (cyc.toFun ig)) *
              orient2D (S (cyc.toFun (ig - 1))) (S (cyc.toFun (ig + 1))) (S z) →
          SegmentsCross (w (Finset.univ \ O_miss)) (S z)
            (S (cyc.toFun (ig - 1))) (S (cyc.toFun (ig + 1))) ∧
          (∃ H_hp : OpenHalfPlane, IsHalfPlaneTest P
            (WitnessSet {cyc.toFun (ig - 1), cyc.toFun (ig + 1)} ∅ w) (S z) H_hp) ∧
          (z ∈ hullVertices S → IsBackVertexOf S (hullVertices S) z (w (Finset.univ \ O_miss)))) := by
  intro O_miss
  let Tv := Finset.univ \ O_miss
  have hC3 : 3 ≤ C.card := by
    have hcard : C.card = m + 3 := by
      rw [← cyc.image_eq, Finset.card_image_of_injective Finset.univ cyc.inj, Finset.card_fin]
    omega
  have hO_odd : ∀ i : Fin (m + 3), i.val % 2 = 1 → cyc.toFun i ∈ O_miss :=
    fun i hi => Finset.mem_filter.mpr ⟨ccwCycle_mem cyc i, i, hi, rfl⟩
  have hO_even : ∀ i : Fin (m + 3), i.val % 2 = 0 → cyc.toFun i ∉ O_miss := by
    intro i hi hmem
    rcases (Finset.mem_filter.mp hmem).2 with ⟨j, hj, heq⟩
    have := cyc.inj heq
    rw [this] at hj; omega
  have h_odd_nf : ∀ i : Fin (m + 3), i.val % 2 = 1 → ¬ IsFrontVertexOf S C (cyc.toFun i) (w Tv) := by
    intro i hi
    apply no_odd_front hPoly h25 hCD hC3 (ccwCycle_mem cyc i)
      (fun h => (Finset.mem_sdiff.mp h).2 (hO_odd i hi))
    intro x hxC hadj
    obtain ⟨ix, rfl⟩ := ccwCycle_exists_index cyc hxC
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun hxO => ?_⟩
    rcases (Finset.mem_filter.mp hxO).2 with ⟨j, hj, heq⟩
    have hix_odd : ix.val % 2 = 1 := by rw [← cyc.inj heq]; exact hj
    have h_even_size : (m + 3) % 2 = 0 := by rcases hm with rfl | rfl <;> decide
    rcases hadj with e1 | e2
    · rw [isCCWEdge_iff_ccwCycle cyc] at e1
      rcases e1 with ⟨r, hr1, hr2⟩
      have hr : r = ix := cyc.inj hr1.symm
      have hrp1 : r + 1 = i := cyc.inj hr2.symm
      have hp := fin_succ_val_parity h_even_size r
      rw [hrp1, hr] at hp; omega
    · rw [isCCWEdge_iff_ccwCycle cyc] at e2
      rcases e2 with ⟨r, hr1, hr2⟩
      have hr : r = i := cyc.inj hr1.symm
      have hrp1 : r + 1 = ix := cyc.inj hr2.symm
      have hp := fin_succ_val_parity h_even_size r
      rw [hrp1, hr] at hp; omega
  have h_odd_B_nf : ∀ i : Fin (m + 3), i.val % 2 = 1 →
      ¬ IsFrontVertexOf S (hullVertices S) (cyc.toFun i) (w Tv) := by
    intro i hi
    have hn3 : 3 ≤ n := by
      have hcard : C.card ≤ n := (Finset.card_le_univ C).trans_eq (Fintype.card_fin n)
      omega
    have h_even_size : (m + 3) % 2 = 0 := by rcases hm with rfl | rfl <;> decide
    apply nonfront_hullVertices_of_nbrs_seen hPoly h25 hn3 (hCD (ccwCycle_mem cyc i))
      (fun h => (Finset.mem_sdiff.mp h).2 (hO_odd i hi))
    intro x hxB hadj
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun hxO => ?_⟩
    rcases (Finset.mem_filter.mp hxO).2 with ⟨ix, hix_odd, rfl⟩
    have hix_ne : ix ≠ i := by
      intro h; rw [h] at hadj
      rcases hadj with h1 | h2
      · exact h1.2.2.1 rfl
      · exact h2.2.2.1 rfl
    have hdiff_pos : 0 < (ix - i).val := Nat.pos_of_ne_zero (fun h => hix_ne (sub_eq_zero.mp (Fin.ext h)))
    have hdiff_ev : (ix - i).val % 2 = 0 := by
      rw [fin_val_sub_eq]; split_ifs with hle
      · have := Fin.le_def.mp hle; omega
      · have := Fin.lt_def.mp (lt_of_not_ge hle); omega
    have h1_lt : 1 < (ix - i).val := by omega
    have hm1_lt : 0 < (i - 1 - ix).val ∧ (i - 1 - ix).val < (i - ix).val := by
      have hcomp := fin_sub_add_compl hix_ne
      have him_pos : 0 < (i - ix).val := by omega
      have him_ev : (i - ix).val % 2 = 0 := by omega
      have him_ge2 : 2 ≤ (i - ix).val := by omega
      have hval := fin_sub_one_val_lt (show 1 < m + 3 by omega) him_pos
      have heq : (i - ix) - 1 = i - 1 - ix := by abel
      have h1v : (1 : Fin (m + 3)).val = 1 := by rcases hm with rfl | rfl <;> decide
      have heq_val : ((i - ix) - 1).val = (i - ix).val - 1 := by
        rw [fin_val_sub_eq, if_pos (Fin.le_def.mpr (by rw [h1v]; omega)), h1v]
      rw [← heq]
      refine ⟨?_, hval⟩
      rw [heq_val]; omega
    have hccw1 : 0 < orient2D (S (cyc.toFun i)) (S (cyc.toFun (i + 1))) (S (cyc.toFun ix)) := by
      have h1 : (i + 1 - i).val = 1 := by
        rw [add_sub_cancel_left]; exact Nat.mod_eq_of_lt (show 1 < m + 3 by omega)
      exact ccwCycle_ccw3 cyc (by rw [h1]; omega) (by rw [h1]; exact h1_lt)
    have hccw2 : 0 < orient2D (S (cyc.toFun ix)) (S (cyc.toFun (i - 1))) (S (cyc.toFun i)) :=
      ccwCycle_ccw3 cyc hm1_lt.1 hm1_lt.2
    rcases hadj with e1 | e2
    · have hmem1 : cyc.toFun (i - 1) ∈ hullVertices S := (Finset.mem_sdiff.mp (hCD (ccwCycle_mem cyc (i - 1)))).1
      have hne1 : cyc.toFun (i - 1) ≠ cyc.toFun ix := fun h => by
        have := cyc.inj h
        have hp := fin_succ_val_parity h_even_size (i - 1)
        rw [sub_add_cancel, this] at hp; omega
      have hne2 : cyc.toFun (i - 1) ≠ cyc.toFun i := cyc.inj.ne (fin_sub_one_ne_self i)
      have hpos := e1.2.2.2 _ hmem1 hne1 hne2
      unfold orient2D at hccw2 hpos; linarith
    · have hmem1 : cyc.toFun (i + 1) ∈ hullVertices S := (Finset.mem_sdiff.mp (hCD (ccwCycle_mem cyc (i + 1)))).1
      have hne1 : cyc.toFun (i + 1) ≠ cyc.toFun i := fun h => by
        have := cyc.inj h
        have hp := fin_succ_val_parity h_even_size i; rw [this] at hp; omega
      have hne2 : cyc.toFun (i + 1) ≠ cyc.toFun ix := fun h => by
        have := cyc.inj h
        have hp := fin_succ_val_parity h_even_size i; rw [this] at hp; omega
      have hpos := e2.2.2.2 _ hmem1 hne1 hne2
      unfold orient2D at hccw1 hpos; linarith
  have h_no_cert : ¬ ∃ (io_min io_star ig : Fin (m + 3)),
      io_min.val % 2 = 1 ∧ io_star.val % 2 = 1 ∧ ig.val % 2 = 0 ∧
      ((io_star + 1 = ig ∧ ig + 1 = io_min) ∨ (io_min + 1 = ig ∧ ig + 1 = io_star)) ∧
      ¬ Sees P (w Tv) (w Finset.univ) ∧
      IsFrontVertexOf S C (cyc.toFun ig) (w Tv) ∧
      InIntTri (w Finset.univ) (S (cyc.toFun io_min)) (S (cyc.toFun io_star)) (w Tv) := by
    rintro ⟨io_min, io_star, ig, hmin, hstar, hig, hadj, hq_miss, hfront, hv_tri⟩
    have hfD : cyc.toFun ig ∈ hullVertices S \ certifiedVertices S w := hCD (ccwCycle_mem cyc ig)
    have ho1B : cyc.toFun io_min ∈ hullVertices S := (Finset.mem_sdiff.mp (hCD (ccwCycle_mem cyc io_min))).1
    have ho2B : cyc.toFun io_star ∈ hullVertices S := (Finset.mem_sdiff.mp (hCD (ccwCycle_mem cyc io_star))).1
    have hmin_ne : io_min ≠ ig := fun h => by rw [h] at hmin; omega
    have hstar_ne : io_star ≠ ig := fun h => by rw [h] at hstar; omega
    have h12_ne : io_min ≠ io_star := by
      intro heq
      rcases hadj with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have h02 : ig + 1 = io_star := heq ▸ h2
        have h' : io_star + (2 : Fin (m + 3)) = io_star := by
          calc io_star + 2 = (io_star + 1) + 1 := by abel
            _ = ig + 1 := by rw [h1]
            _ = io_star := h02
        nth_rw 2 [← add_zero io_star] at h'
        have hv := congrArg Fin.val (add_left_cancel h')
        simp [Nat.mod_eq_of_lt (show 2 < m + 3 by omega)] at hv
      · have h02 : io_min + (2 : Fin (m + 3)) = io_min := by
          calc io_min + 2 = (io_min + 1) + 1 := by abel
            _ = ig + 1 := by rw [h1]
            _ = io_min := heq ▸ h2
        nth_rw 2 [← add_zero io_min] at h02
        have hv := congrArg Fin.val (add_left_cancel h02)
        simp [Nat.mod_eq_of_lt (show 2 < m + 3 by omega)] at hv
    have hf_tri : InIntTri (w Tv) (S (cyc.toFun io_min)) (S (cyc.toFun io_star)) (S (cyc.toFun ig)) := by
      rw [isFrontVertexOf_iff_ccwCycle cyc ig (w Tv)] at hfront
      have h_adj_ne : ig - 1 ≠ ig + 1 := by
        intro h
        rcases hadj with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · have hm1 : ig - 1 = io_star := (eq_sub_of_add_eq h1).symm
          exact h12_ne (h2.symm.trans (h.symm.trans hm1))
        · have hm1 : ig - 1 = io_min := (eq_sub_of_add_eq h1).symm
          exact h12_ne (hm1.symm.trans (h.trans h2))
      have h_noncol : orient2D (S (cyc.toFun (ig - 1))) (S (cyc.toFun (ig + 1))) (w Tv) ≠ 0 :=
        hPoly.no_three_collinear _ _ _
          (Or.inl (Set.mem_range_self _)) (Or.inl (Set.mem_range_self _)) (Or.inr (Set.mem_range_self _))
          (hPoly.s_inj.ne (cyc.inj.ne h_adj_ne)) (hPoly.s_ne_w _ _) (hPoly.s_ne_w _ _)
      have h_in := (isFrontVertexOf_iff_inIntTri cyc ig (w Tv) h_noncol).mp
        ((isFrontVertexOf_iff_ccwCycle cyc ig (w Tv)).mpr hfront)
      rcases hadj with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have hm1 : ig - 1 = io_star := (eq_sub_of_add_eq h1).symm
        rw [hm1, h2] at h_in; exact h_in.symm23
      · have hm1 : ig - 1 = io_min := (eq_sub_of_add_eq h1).symm
        rw [hm1, h2] at h_in; exact h_in
    exact contradict_cert_even_front hPoly h25 hfD ho1B ho2B (cyc.inj.ne hmin_ne)
      (cyc.inj.ne hstar_ne) (cyc.inj.ne h12_ne) (hO_even ig hig) hq_miss hf_tri hv_tri
  obtain ⟨Tgt, hcard, hTgt⟩ := good_targets_core hPoly hm cyc hO_odd hO_even h_odd_nf h_no_cert
  refine ⟨Tgt, hcard, fun ig hig => ?_⟩
  rcases hTgt ig hig with ⟨hig_ev, hbackC, hgap, htri⟩
  have h_even_size : (m + 3) % 2 = 0 := by rcases hm with rfl | rfl <;> decide
  have hm3 : 1 < m + 3 := by rcases hm with rfl | rfl <;> omega
  have hm1_odd : (ig - 1).val % 2 = 1 := by
    have hp := fin_succ_val_parity h_even_size (ig - 1)
    rw [sub_add_cancel] at hp; omega
  have hp1_odd : (ig + 1).val % 2 = 1 := by
    rw [fin_succ_val_parity h_even_size ig]; omega
  have haB : cyc.toFun (ig - 1) ∈ hullVertices S := (Finset.mem_sdiff.mp (hCD (ccwCycle_mem cyc (ig - 1)))).1
  have hpB : cyc.toFun ig ∈ hullVertices S := (Finset.mem_sdiff.mp (hCD (ccwCycle_mem cyc ig))).1
  have hcB : cyc.toFun (ig + 1) ∈ hullVertices S := (Finset.mem_sdiff.mp (hCD (ccwCycle_mem cyc (ig + 1)))).1
  have hap : cyc.toFun (ig - 1) ≠ cyc.toFun ig := cyc.inj.ne (fin_sub_one_ne_self ig)
  have hpc : cyc.toFun ig ≠ cyc.toFun (ig + 1) := cyc.inj.ne (fin_add_one_ne_self ig)
  have hac : cyc.toFun (ig - 1) ≠ cyc.toFun (ig + 1) := cyc.inj.ne (fun h => by
    have h' := congrArg (· + (1 : Fin (m + 3))) h
    rw [sub_add_cancel, add_assoc] at h'
    nth_rw 1 [← add_zero ig] at h'
    have h2 : (1 + 1 : Fin (m + 3)).val = 2 := by
      have h1 : (1 : Fin (m + 3)).val = 1 := Nat.mod_eq_of_lt hm3
      rw [Fin.val_add, h1]
      exact Nat.mod_eq_of_lt (by rcases hm with rfl | rfl <;> omega)
    have hv := congrArg Fin.val (add_left_cancel h')
    rw [h2] at hv
    simp at hv)
  have hp_seen : cyc.toFun ig ∈ Tv := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hO_even ig hig_ev⟩
  have ha_miss : cyc.toFun (ig - 1) ∉ Tv := fun h => (Finset.mem_sdiff.mp h).2 (hO_odd _ hm1_odd)
  have hc_miss : cyc.toFun (ig + 1) ∉ Tv := fun h => (Finset.mem_sdiff.mp h).2 (hO_odd _ hp1_odd)
  have hO_Tv : ∀ x : Fin n, x ∉ O_miss → x ∈ Tv := fun x hx => Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hx⟩
  have ha_nf := h_odd_B_nf (ig - 1) hm1_odd
  have hc_nf := h_odd_B_nf (ig + 1) hp1_odd
  rcases htri with ⟨h1, h2, h3, h4, h5⟩ | ⟨h1, h2, h3, h4, h5⟩
  · have hcond4 : Sees P (w Tv) (w Finset.univ) ∨
        ∃ e : Fin n, e ∈ Tv ∧ AngleLt (w Tv) (w Finset.univ) (S e) (S (cyc.toFun (ig - 1))) := by
      rcases hgap with ⟨_, _, _, ⟨_, h⟩ | ⟨hang, _⟩⟩
      · rcases h with hsee | ⟨e, he, hlt⟩
        · exact Or.inl hsee
        · exact Or.inr ⟨e, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, he⟩, hlt⟩
      · exact False.elim ((h1.trans h2).asymm hang)
    have hthp := targets_halfplane hPoly h25 haB hpB hcB hap hpc hac hp_seen ha_miss hc_miss hO_Tv
      ha_nf hc_nf (Or.inl ⟨h3, h4, h5⟩) h1 h2 hcond4
    exact ⟨hig_ev, hbackC, hthp.1, hgap, hthp.2.1.1, hthp.2.1.2, hthp.2.2⟩
  · have hcond4 : Sees P (w Tv) (w Finset.univ) ∨
        ∃ e : Fin n, e ∈ Tv ∧ AngleLt (w Tv) (w Finset.univ) (S e) (S (cyc.toFun (ig + 1))) := by
      rcases hgap with ⟨_, _, _, ⟨hang, _⟩ | ⟨_, h⟩⟩
      · exact False.elim ((h1.trans h2).asymm hang)
      · rcases h with hsee | ⟨e, he, hlt⟩
        · exact Or.inl hsee
        · exact Or.inr ⟨e, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, he⟩, hlt⟩
    have hthp := targets_halfplane hPoly h25 hcB hpB haB hpc.symm hap.symm hac.symm hp_seen hc_miss ha_miss hO_Tv
      hc_nf ha_nf (Or.inr ⟨h3, h4, h5⟩) h1 h2 hcond4
    have hset : ({cyc.toFun (ig + 1), cyc.toFun (ig - 1)} : Finset (Fin n)) =
        {cyc.toFun (ig - 1), cyc.toFun (ig + 1)} := by ext x; simp [or_comm]
    refine ⟨hig_ev, hbackC, hthp.1, hgap, hthp.2.1.1.symm34, ?_, fun z hza hzc hzO hz_conv hz_side => ?_⟩
    · rcases hthp.2.1.2 with ⟨H_hp, hH⟩; exact ⟨H_hp, hset ▸ hH⟩
    · have h_side' : 0 < orient2D (S (cyc.toFun (ig + 1))) (S (cyc.toFun (ig - 1))) (S (cyc.toFun ig)) *
          orient2D (S (cyc.toFun (ig + 1))) (S (cyc.toFun (ig - 1))) (S z) := by
        have ha := orient2D_swap12 (S (cyc.toFun (ig - 1))) (S (cyc.toFun (ig + 1))) (S (cyc.toFun ig))
        have hb := orient2D_swap12 (S (cyc.toFun (ig - 1))) (S (cyc.toFun (ig + 1))) (S z)
        rw [ha, hb]; linarith
      obtain ⟨hc, ⟨H_hp, hH⟩, hbk⟩ := hthp.2.2 z hzc hza hzO hz_conv h_side'
      exact ⟨hc.symm34, ⟨H_hp, hset ▸ hH⟩, hbk⟩

/-- Proposition 6.5 (`gap`, `upper_9.tex` lines 695–701):
    For any pairwise non-adjacent triple `O = {o1, o2, o3} ⊆ D` (ordered by `0 < (i2 - i1).val < (i3 - i1).val`
    along `cycD : CCWCycle S D kD`, with `1 < (i2 - i1).val`, `1 < (i3 - i2).val`, `1 < (i1 - i3).val`),
    at least one of the three full cyclic `D`-gaps `Γ_m` is good for `v = w (S \ O)`. -/
theorem gap_lemma {n kD : ℕ} {P : Set (ℝ × ℝ)}
    {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ}
    (hPoly : ShatteredSimplePolygon P S w) (h25 : Sec2To5Interface P S w)
    {D : Finset (Fin n)} (hD_sub : D ⊆ hullVertices S \ certifiedVertices S w)
    (cycD : CCWCycle S D kD)
    (i1 i2 i3 : Fin (kD + 3))
    (h12 : 1 < (i2 - i1).val) (h23 : 1 < (i3 - i2).val) (h31 : 1 < (i1 - i3).val)
    (hsum : (i2 - i1).val + (i3 - i2).val + (i1 - i3).val = kD + 3) :
    let o1 := cycD.toFun i1
    let o2 := cycD.toFun i2
    let o3 := cycD.toFun i3
    let O_miss : Finset (Fin n) := {o1, o2, o3}
    let gap1 := D.filter (fun p => ∃ m : Fin (kD + 3), cycD.toFun m = p ∧
      0 < (m - i1).val ∧ (m - i1).val < (i2 - i1).val)
    let gap2 := D.filter (fun p => ∃ m : Fin (kD + 3), cycD.toFun m = p ∧
      0 < (m - i2).val ∧ (m - i2).val < (i3 - i2).val)
    let gap3 := D.filter (fun p => ∃ m : Fin (kD + 3), cycD.toFun m = p ∧
      0 < (m - i3).val ∧ (m - i3).val < (i1 - i3).val)
    ∃ (oa ob : Fin n) (Γ : Finset (Fin n)),
      ((oa = o1 ∧ ob = o2 ∧ Γ = gap1) ∨
       (oa = o2 ∧ ob = o3 ∧ Γ = gap2) ∨
       (oa = o3 ∧ ob = o1 ∧ Γ = gap3)) ∧
      GoodAnchorPair P S w O_miss oa ob ∧
      ∀ p ∈ Γ,
        IsBackVertexOf S (hullVertices S) p (w (Finset.univ \ O_miss)) ∧
        SegmentsCross (w (Finset.univ \ O_miss)) (S p) (S oa) (S ob) ∧
        (∃ H_hp : OpenHalfPlane, IsHalfPlaneTest P (WitnessSet {oa, ob} ∅ w) (S p) H_hp) ∧
        (∀ z : Fin n, z ≠ oa → z ≠ ob → z ∉ O_miss →
          S z ∈ convexHull ℝ ((hullVertices S).image S : Set (ℝ × ℝ)) →
          0 < orient2D (S oa) (S ob) (S p) * orient2D (S oa) (S ob) (S z) →
          SegmentsCross (w (Finset.univ \ O_miss)) (S z) (S oa) (S ob) ∧
          (∃ H_hp : OpenHalfPlane, IsHalfPlaneTest P (WitnessSet {oa, ob} ∅ w) (S z) H_hp) ∧
          (z ∈ hullVertices S → IsBackVertexOf S (hullVertices S) z (w (Finset.univ \ O_miss)))) := by
  intro o1 o2 o3 O_miss gap1 gap2 gap3
  let j0 : Fin (kD + 3) := i3 + 1
  let j1 : Fin (kD + 3) := i1
  let j2 : Fin (kD + 3) := i1 + 1
  let j3 : Fin (kD + 3) := i2
  let j4 : Fin (kD + 3) := i2 + 1
  let j5 : Fin (kD + 3) := i3
  let idx : Fin 6 → Fin (kD + 3)
    | 0 => j0
    | 1 => j1
    | 2 => j2
    | 3 => j3
    | 4 => j4
    | 5 => j5
  have hj_vals :
      (j0 - j0).val = 0 ∧
      (j1 - j0).val = (i1 - i3).val - 1 ∧
      (j2 - j0).val = (i1 - i3).val ∧
      (j3 - j0).val = (i1 - i3).val + (i2 - i1).val - 1 ∧
      (j4 - j0).val = (i1 - i3).val + (i2 - i1).val ∧
      (j5 - j0).val = kD + 2 := by
    have h1_val : (1 : Fin (kD + 3)).val = 1 := Nat.mod_eq_of_lt (show 1 < kD + 3 by omega)
    have h_j1 : j1 - j0 = (i1 - i3) - 1 := by dsimp [j1, j0]; abel
    have hj1_v : (j1 - j0).val = (i1 - i3).val - 1 := by
      rw [h_j1, fin_val_sub_eq, if_pos (Fin.le_def.mpr (by rw [h1_val]; omega)), h1_val]
    have h_j2 : j2 - j0 = i1 - i3 := by dsimp [j2, j0]; abel
    have h_j3 : j3 - j0 = (i2 - i1) + (j1 - j0) := by dsimp [j3, j1]; abel
    have hj3_v : (j3 - j0).val = (i1 - i3).val + (i2 - i1).val - 1 := by
      rw [h_j3, Fin.val_add, hj1_v, Nat.mod_eq_of_lt (by omega)]; omega
    have h_j4 : j4 - j0 = (i2 - i1) + (j2 - j0) := by dsimp [j4, j2]; abel
    have hj4_v : (j4 - j0).val = (i1 - i3).val + (i2 - i1).val := by
      rw [h_j4, Fin.val_add, h_j2, Nat.mod_eq_of_lt (by omega)]; omega
    have h1_ne : (1 : Fin (kD + 3)) ≠ 0 := by
      intro h; have := congrArg Fin.val h; rw [h1_val] at this; simp at this
    have hj5_v : (j5 - j0).val = kD + 2 := by
      have heq : j5 - j0 = -1 := by dsimp [j5, j0]; abel
      rw [heq, Fin.val_neg, if_neg h1_ne, h1_val]
      omega
    exact ⟨by simp, hj1_v, by rw [h_j2], hj3_v, hj4_v, hj5_v⟩
  have h_strict : ∀ a b : Fin 6, a < b → (idx a - idx 0).val < (idx b - idx 0).val := by
    intro a b hab
    rcases hj_vals with ⟨hv0, hv1, hv2, hv3, hv4, hv5⟩
    fin_cases a <;> fin_cases b <;> simp at hab <;> dsimp [idx] <;> omega
  let C := Finset.univ.image (fun r : Fin 6 => cycD.toFun (idx r))
  let cycC : CCWCycle S C 3 := ccwCycle_of_subseq cycD idx h_strict
  have hCD : C ⊆ D := by
    intro x hx; rcases Finset.mem_image.mp hx with ⟨r, _, rfl⟩; exact ccwCycle_mem cycD (idx r)
  obtain ⟨Tgt, hTcard, hTgt⟩ := good_targets hPoly h25 (Or.inl rfl) (hCD.trans hD_sub) cycC
  have hTne : Tgt.Nonempty := Finset.card_pos.mp (by rw [hTcard]; simp)
  obtain ⟨ig, hig⟩ := hTne
  rcases hTgt ig hig with ⟨hig_ev, _, _, hgap, hcross_ig, hhp_ig, hcap_ig⟩
  have hO_eq : C.filter (fun x => ∃ i : Fin 6, i.val % 2 = 1 ∧ cycC.toFun i = x) = O_miss := by
    ext x; simp only [C, Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨_, i, hi, rfl⟩
      fin_cases i <;> simp at hi <;> simp [O_miss, cycC, ccwCycle_of_subseq, idx, j1, j3, j5, o1, o2, o3]
    · intro hx
      simp only [O_miss, Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · exact ⟨⟨1, rfl⟩, 1, by decide, rfl⟩
      · exact ⟨⟨3, rfl⟩, 3, by decide, rfl⟩
      · exact ⟨⟨5, rfl⟩, 5, by decide, rfl⟩
  rw [hO_eq] at hgap hcross_ig hcap_ig
  have h12_id : i2 - i3 = (i2 - i1) + (i1 - i3) := by abel
  have h23_id : i3 - i1 = (i3 - i2) + (i2 - i1) := by abel
  have h31_id : i1 - i2 = (i1 - i3) + (i3 - i2) := by abel
  have h12_v : (i2 - i3).val = (i2 - i1).val + (i1 - i3).val := by
    rw [h12_id, Fin.val_add, Nat.mod_eq_of_lt (by omega)]
  have h23_v : (i3 - i1).val = (i3 - i2).val + (i2 - i1).val := by
    rw [h23_id, Fin.val_add, Nat.mod_eq_of_lt (by omega)]
  have h31_v : (i1 - i2).val = (i1 - i3).val + (i3 - i2).val := by
    rw [h31_id, Fin.val_add, Nat.mod_eq_of_lt (by omega)]
  have h_for_gap : ∀ (ig_idx a_idx c_idx : Fin (kD + 3)) (Γ : Finset (Fin n)),
      (0 < (ig_idx - a_idx).val ∧ (ig_idx - a_idx).val < (c_idx - a_idx).val) →
      (Γ = D.filter (fun p => ∃ m : Fin (kD + 3), cycD.toFun m = p ∧
        0 < (m - a_idx).val ∧ (m - a_idx).val < (c_idx - a_idx).val)) →
      GoodAnchorPair P S w O_miss (cycD.toFun a_idx) (cycD.toFun c_idx) →
      (∀ z : Fin n, z ≠ cycD.toFun a_idx → z ≠ cycD.toFun c_idx → z ∉ O_miss →
        S z ∈ convexHull ℝ ((hullVertices S).image S : Set (ℝ × ℝ)) →
        0 < orient2D (S (cycD.toFun a_idx)) (S (cycD.toFun c_idx)) (S (cycD.toFun ig_idx)) *
            orient2D (S (cycD.toFun a_idx)) (S (cycD.toFun c_idx)) (S z) →
        SegmentsCross (w (Finset.univ \ O_miss)) (S z) (S (cycD.toFun a_idx)) (S (cycD.toFun c_idx)) ∧
        (∃ H_hp, IsHalfPlaneTest P (WitnessSet {cycD.toFun a_idx, cycD.toFun c_idx} ∅ w) (S z) H_hp) ∧
        (z ∈ hullVertices S → IsBackVertexOf S (hullVertices S) z (w (Finset.univ \ O_miss)))) →
      (cycD.toFun a_idx ∉ O_miss → False) →
      (∀ p ∈ Γ, p ∉ O_miss) →
      ∀ p ∈ Γ,
        IsBackVertexOf S (hullVertices S) p (w (Finset.univ \ O_miss)) ∧
        SegmentsCross (w (Finset.univ \ O_miss)) (S p) (S (cycD.toFun a_idx)) (S (cycD.toFun c_idx)) ∧
        (∃ H_hp : OpenHalfPlane, IsHalfPlaneTest P (WitnessSet {cycD.toFun a_idx, cycD.toFun c_idx} ∅ w) (S p) H_hp) ∧
        (∀ z : Fin n, z ≠ cycD.toFun a_idx → z ≠ cycD.toFun c_idx → z ∉ O_miss →
          S z ∈ convexHull ℝ ((hullVertices S).image S : Set (ℝ × ℝ)) →
          0 < orient2D (S (cycD.toFun a_idx)) (S (cycD.toFun c_idx)) (S p) *
              orient2D (S (cycD.toFun a_idx)) (S (cycD.toFun c_idx)) (S z) →
          SegmentsCross (w (Finset.univ \ O_miss)) (S z) (S (cycD.toFun a_idx)) (S (cycD.toFun c_idx)) ∧
          (∃ H_hp : OpenHalfPlane, IsHalfPlaneTest P (WitnessSet {cycD.toFun a_idx, cycD.toFun c_idx} ∅ w) (S z) H_hp) ∧
          (z ∈ hullVertices S → IsBackVertexOf S (hullVertices S) z (w (Finset.univ \ O_miss)))) := by
    intro ig_idx a_idx c_idx Γ h_ig hΓ _ hcap _ hΓ_notO p hp
    rcases (hΓ ▸ hp |> Finset.mem_filter.mp).2 with ⟨mp, rfl, hm1, hm2⟩
    have h_same_sign : 0 < orient2D (S (cycD.toFun a_idx)) (S (cycD.toFun c_idx)) (S (cycD.toFun ig_idx)) *
        orient2D (S (cycD.toFun a_idx)) (S (cycD.toFun c_idx)) (S (cycD.toFun mp)) := by
      have ho1 := ccwCycle_ccw3 cycD h_ig.1 h_ig.2
      have ho2 := ccwCycle_ccw3 cycD hm1 hm2
      unfold orient2D at ho1 ho2 ⊢
      exact mul_pos_of_neg_of_neg (by linarith) (by linarith)
    have hpa : cycD.toFun mp ≠ cycD.toFun a_idx := cycD.inj.ne (fun h => by subst h; simp at hm1)
    have hpc : cycD.toFun mp ≠ cycD.toFun c_idx := cycD.inj.ne (fun h => by subst h; omega)
    have hpB : cycD.toFun mp ∈ hullVertices S := (Finset.mem_sdiff.mp (hD_sub (hΓ ▸ hp |> Finset.mem_filter.mp).1)).1
    have hp_conv : S (cycD.toFun mp) ∈ convexHull ℝ ((hullVertices S).image S : Set (ℝ × ℝ)) :=
      subset_convexHull ℝ _ (Finset.mem_image.mpr ⟨_, hpB, rfl⟩)
    obtain ⟨hcross_p, hhp_p, hback_p⟩ := hcap (cycD.toFun mp) hpa hpc (hΓ_notO _ hp) hp_conv h_same_sign
    refine ⟨hback_p hpB, hcross_p, hhp_p, fun z hza hzc hzO hz_conv hside => ?_⟩
    have h_sign_z : 0 < orient2D (S (cycD.toFun a_idx)) (S (cycD.toFun c_idx)) (S (cycD.toFun ig_idx)) *
        orient2D (S (cycD.toFun a_idx)) (S (cycD.toFun c_idx)) (S z) := by
      have ho1 := ccwCycle_ccw3 cycD h_ig.1 h_ig.2
      have ho2 := ccwCycle_ccw3 cycD hm1 hm2
      have h_ig_neg : orient2D (S (cycD.toFun a_idx)) (S (cycD.toFun c_idx)) (S (cycD.toFun ig_idx)) < 0 := by
        unfold orient2D at ho1 ⊢; linarith
      have h_mp_neg : orient2D (S (cycD.toFun a_idx)) (S (cycD.toFun c_idx)) (S (cycD.toFun mp)) < 0 := by
        unfold orient2D at ho2 ⊢; linarith
      nlinarith [mul_pos_of_neg_of_neg h_ig_neg h_mp_neg]
    exact hcap z hza hzc hzO hz_conv h_sign_z
  have hg_cases : ig = 0 ∨ ig = 2 ∨ ig = 4 := by
    fin_cases ig <;> simp at hig_ev <;> tauto
  rcases hg_cases with rfl | rfl | rfl
  · refine ⟨o3, o1, gap3, Or.inr (Or.inr ⟨rfl, rfl, rfl⟩), hgap, ?_⟩
    apply h_for_gap j0 i3 i1 gap3
    · have : j0 - i3 = 1 := by dsimp [j0]; abel
      rw [this, show (1 : Fin (kD + 3)).val = 1 from Nat.mod_eq_of_lt (show 1 < kD + 3 by omega)]
      exact ⟨by omega, h31⟩
    · rfl
    · exact hgap
    · exact hcap_ig
    · intro h; exact False.elim (h (Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr rfl))))))
    · intro p hp hpO
      rcases (Finset.mem_filter.mp hp).2 with ⟨mp, rfl, hm1, hm2⟩
      simp only [O_miss, Finset.mem_insert, Finset.mem_singleton] at hpO
      rcases hpO with h | h | h
      · have heq := cycD.inj h; subst heq; omega
      · have heq := cycD.inj h; subst heq; rw [h12_v] at hm2; omega
      · have heq := cycD.inj h; subst heq; simp at hm1
  · refine ⟨o1, o2, gap1, Or.inl ⟨rfl, rfl, rfl⟩, hgap, ?_⟩
    apply h_for_gap j2 i1 i2 gap1
    · have : j2 - i1 = 1 := by dsimp [j2]; abel
      rw [this, show (1 : Fin (kD + 3)).val = 1 from Nat.mod_eq_of_lt (show 1 < kD + 3 by omega)]
      exact ⟨by omega, h12⟩
    · rfl
    · exact hgap
    · exact hcap_ig
    · intro h; exact False.elim (h (Finset.mem_insert_self _ _))
    · intro p hp hpO
      rcases (Finset.mem_filter.mp hp).2 with ⟨mp, rfl, hm1, hm2⟩
      simp only [O_miss, Finset.mem_insert, Finset.mem_singleton] at hpO
      rcases hpO with h | h | h
      · have heq := cycD.inj h; subst heq; simp at hm1
      · have heq := cycD.inj h; subst heq; omega
      · have heq := cycD.inj h; subst heq; rw [h23_v] at hm2; omega
  · refine ⟨o2, o3, gap2, Or.inr (Or.inl ⟨rfl, rfl, rfl⟩), hgap, ?_⟩
    apply h_for_gap j4 i2 i3 gap2
    · have : j4 - i2 = 1 := by dsimp [j4]; abel
      rw [this, show (1 : Fin (kD + 3)).val = 1 from Nat.mod_eq_of_lt (show 1 < kD + 3 by omega)]
      exact ⟨by omega, h23⟩
    · rfl
    · exact hgap
    · exact hcap_ig
    · intro h; exact False.elim (h (Finset.mem_insert.mpr (Or.inr (Finset.mem_insert_self _ _))))
    · intro p hp hpO
      rcases (Finset.mem_filter.mp hp).2 with ⟨mp, rfl, hm1, hm2⟩
      simp only [O_miss, Finset.mem_insert, Finset.mem_singleton] at hpO
      rcases hpO with h | h | h
      · have heq := cycD.inj h; subst heq; rw [h31_v] at hm2; omega
      · have heq := cycD.inj h; subst heq; simp at hm1
      · have heq := cycD.inj h; subst heq; omega

/-! ## Part 6d: Prop 6.6 (`interior_anchor`), Lemma 6.7 (`pairs_in_M`), and Lemma 6.10 (`adjacent_exits`) -/

lemma isCCWEdge_B_of_D_ne_lr {n : ℕ} {P : Set (ℝ × ℝ)}
    {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ}
    (h25 : Sec2To5Interface P S w)
    {u v : Fin n} (h3D : 3 ≤ (hullVertices S \ certifiedVertices S w).card)
    (huv_D : IsCCWEdge S (hullVertices S \ certifiedVertices S w) u v)
    (h_not_lr : ∀ l r : Fin n, (certifiedVertices S w).Nonempty →
      l ∈ hullVertices S \ certifiedVertices S w →
      r ∈ hullVertices S \ certifiedVertices S w →
      l ≠ r → IsCCWEdge S (hullVertices S \ certifiedVertices S w) l r →
      (∀ h ∈ certifiedVertices S w, orient2D (S l) (S r) (S h) < 0) →
      (u, v) ≠ (l, r)) :
    IsCCWEdge S (hullVertices S) u v := by
  let B := hullVertices S
  let H := certifiedVertices S w
  let D := B \ H
  by_cases hH : H.Nonempty
  · obtain ⟨l, r, hlD, hrD, hlr, hlr_edge', hH_neg, hD_pos, _, h_edge_eq, _, _⟩ :=
      h25.certified_structure.2 hH
    have hlr_edge : IsCCWEdge S D l r := hlr_edge' h3D
    have hne_lr : (u, v) ≠ (l, r) := h_not_lr l r hH hlD hrD hlr hlr_edge hH_neg
    have huD : u ∈ D := huv_D.1
    have hvD : v ∈ D := huv_D.2.1
    have huv_ne : u ≠ v := huv_D.2.2.1
    have huB : u ∈ B := (Finset.mem_sdiff.mp huD).1
    have hvB : v ∈ B := (Finset.mem_sdiff.mp hvD).1
    by_cases hu_lr : u ≠ l ∧ u ≠ r
    · exact (h_edge_eq u huD hu_lr.1 hu_lr.2 v hvB).2.mpr huv_D
    · push Not at hu_lr
      by_cases hul : u = l
      · have hvr : v ≠ r := fun h => hne_lr (Prod.ext hul h)
        have hvl : v ≠ l := fun h => huv_ne (hul.trans h.symm)
        exact (h_edge_eq v hvD hvl hvr u huB).1.mpr huv_D
      · have hur : u = r := hu_lr hul
        have hvr : v ≠ r := fun h => huv_ne (hur.trans h.symm)
        have hvl : v ≠ l := by
          intro hvl
          change 3 ≤ D.card at h3D
          have hsub : ({l, r} : Finset (Fin n)).card < D.card := by
            have hc2 : ({l, r} : Finset (Fin n)).card = 2 := by
              rw [Finset.card_insert_of_notMem (by simp [hlr]), Finset.card_singleton]
            omega
          obtain ⟨d, hdD, hd_not⟩ := Finset.exists_mem_notMem_of_card_lt_card hsub
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hd_not
          have hpos1 : 0 < orient2D (S l) (S r) (S d) := hD_pos d hdD hd_not.1 hd_not.2
          have hpos2 : 0 < orient2D (S r) (S l) (S d) := by
            have := huv_D.2.2.2 d hdD (fun h => hd_not.2 (h.trans hur)) (fun h => hd_not.1 (h.trans hvl))
            rwa [hur, hvl] at this
          rw [orient2D_swap12] at hpos2
          linarith
        exact (h_edge_eq v hvD hvl hvr u huB).1.mpr huv_D
  · have hHe : H = ∅ := Finset.not_nonempty_iff_eq_empty.mp hH
    have hDB : D = B := by dsimp [D]; rw [hHe, Finset.sdiff_empty]
    change IsCCWEdge S D u v at huv_D
    rwa [hDB] at huv_D

lemma orient2D_pos_of_isCCWEdge_B {n : ℕ} {P : Set (ℝ × ℝ)}
    {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ}
    (hPoly : ShatteredSimplePolygon P S w)
    {u v : Fin n} (huv : IsCCWEdge S (hullVertices S) u v)
    {z : Fin n} (hzu : z ≠ u) (hzv : z ≠ v) :
    0 < orient2D (S u) (S v) (S z) := by
  have hz_conv : S z ∈ convexHull ℝ ((hullVertices S).image S : Set (ℝ × ℝ)) :=
    mem_convexHull_hullVertices S hPoly.s_inj z
  have hK : Convex ℝ {x : ℝ × ℝ | 0 ≤ orient2D (S u) (S v) x} := by
    intro a ha b hb α β hα hβ hαβ
    dsimp at ha hb ⊢
    have hid : orient2D (S u) (S v) (α • a + β • b) =
        α * orient2D (S u) (S v) a + β * orient2D (S u) (S v) b := by
      unfold orient2D; dsimp
      linear_combination ((S u).2 * (S v).1 - (S u).1 * (S v).2) * hαβ
    rw [hid]
    exact add_nonneg (mul_nonneg hα ha) (mul_nonneg hβ hb)
  have hsub : ((hullVertices S).image S : Set (ℝ × ℝ)) ⊆ {x | 0 ≤ orient2D (S u) (S v) x} := by
    intro x hx
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hx
    rcases hx with ⟨b, hbB, rfl⟩
    dsimp
    by_cases hbu : b = u
    · rw [hbu, orient2D_self_outer]
    · by_cases hbv : b = v
      · rw [hbv, orient2D_self_right]
      · exact le_of_lt (huv.2.2.2 b hbB hbu hbv)
  have hle : 0 ≤ orient2D (S u) (S v) (S z) := convexHull_min hsub hK hz_conv
  have hne : orient2D (S u) (S v) (S z) ≠ 0 :=
    hPoly.no_three_collinear _ _ _
      (Or.inl (Set.mem_range_self _)) (Or.inl (Set.mem_range_self _)) (Or.inl (Set.mem_range_self _))
      (hPoly.s_inj.ne huv.2.2.1) (hPoly.s_inj.ne hzv.symm) (hPoly.s_inj.ne hzu.symm)
  exact lt_of_le_of_ne hle hne.symm

lemma chain_facing_end_orient {k : ℕ} (c : Fin (k + 3) → ℝ × ℝ)
    (hccw3 : ∀ x y z : Fin (k + 3), 0 < (y - x).val → (y - x).val < (z - x).val →
      0 < orient2D (c x) (c y) (c z))
    (v : ℝ × ℝ) (a : Fin (k + 3)) (m : ℕ)
    (hm1 : 1 ≤ m) (hmN : m < k + 3)
    (hface : ∀ t : ℕ, t < m → orient2D (c (a + finNat (k + 3) t)) (c (a + finNat (k + 3) t + 1)) v < 0) :
    0 < orient2D v (c (a + finNat (k + 3) m)) (c a) := by
  induction m with
  | zero => omega
  | succ t ih =>
    rcases Nat.eq_zero_or_pos t with rfl | ht_pos
    · have h1 : finNat (k + 3) 1 = 1 := by
        ext; simp [finNat, Nat.mod_eq_of_lt (by omega : 1 < k + 3)]
      have h0 := hface 0 (by omega)
      rw [finNat_zero, add_zero] at h0
      rw [h1]
      unfold orient2D at h0 ⊢; linarith
    · have h_ih := ih ht_pos (by omega) (fun s hs => hface s (by omega))
      have ht := hface t (by omega)
      have h1_val : (1 : Fin (k + 3)).val = 1 := by simp [Nat.mod_eq_of_lt (by omega : 1 < k + 3)]
      have h_fin_succ : finNat (k + 3) t + 1 = finNat (k + 3) (t + 1) := by
        ext; simp only [Fin.val_add, finNat, h1_val, Nat.mod_eq_of_lt (by omega : t < k + 3),
          Nat.mod_eq_of_lt hmN]
      have hstep : a + finNat (k + 3) t + 1 = a + finNat (k + 3) (t + 1) := by
        rw [add_assoc, h_fin_succ]
      rw [hstep] at ht
      have ht1 : (a + finNat (k + 3) t - a).val = t := by
        rw [add_sub_cancel_left]; exact Nat.mod_eq_of_lt (by omega)
      have ht2 : (a + finNat (k + 3) (t + 1) - a).val = t + 1 := by
        rw [add_sub_cancel_left]; exact Nat.mod_eq_of_lt hmN
      have hccw : 0 < orient2D (c a) (c (a + finNat (k + 3) t)) (c (a + finNat (k + 3) (t + 1))) :=
        hccw3 a (a + finNat (k + 3) t) (a + finNat (k + 3) (t + 1)) (by rw [ht1]; exact ht_pos) (by rw [ht1, ht2]; omega)
      have hsum := orient2D_barycentric_sum (c a) (c (a + finNat (k + 3) t)) (c (a + finNat (k + 3) (t + 1))) v
      unfold orient2D at h_ih ht hccw hsum ⊢
      linarith

/-- Contiguous far-chain extraction and strict angle ordering on `cyc` when at least one edge faces `v`. -/
lemma facing_arc_complement_order {n k : ℕ} {S : Fin n → ℝ × ℝ} {C : Finset (Fin n)}
    (cyc : CCWCycle S C k) (v : ℝ × ℝ)
    (hv_noncol : ∀ i j : Fin (k + 3), i ≠ j → orient2D (S (cyc.toFun i)) (S (cyc.toFun j)) v ≠ 0)
    (h_ex : ∃ j0 : Fin (k + 3), orient2D (S (cyc.toFun j0)) (S (cyc.toFun (j0 + 1))) v < 0) :
    ∃ (e_start e_end : Fin (k + 3)) (L : ℕ),
      1 ≤ L ∧ L ≤ k + 2 ∧
      e_end = e_start + finNat (k + 3) L ∧
      (∀ m : Fin (k + 3), (m - e_start).val < L →
        orient2D (S (cyc.toFun m)) (S (cyc.toFun (m + 1))) v < 0) ∧
      (∀ m : Fin (k + 3), L ≤ (m - e_start).val →
        0 < orient2D (S (cyc.toFun m)) (S (cyc.toFun (m + 1))) v) ∧
      (∀ p : Fin (k + 3), ¬ (0 < (p - e_start).val ∧ (p - e_start).val < L) ↔
        (p - e_end).val ≤ (e_start - e_end).val) ∧
      0 < orient2D v (S (cyc.toFun e_end)) (S (cyc.toFun e_start)) ∧
      let q0 : ℝ × ℝ :=
        (v.1 + (S (cyc.toFun e_end)).1 - (S (cyc.toFun e_start)).1,
         v.2 + (S (cyc.toFun e_end)).2 - (S (cyc.toFun e_start)).2)
      (∀ p : Fin (k + 3), (p - e_end).val ≤ (e_start - e_end).val →
        0 < orient2D v q0 (S (cyc.toFun p))) ∧
      (∀ a b : Fin (k + 3), (a - e_end).val < (b - e_end).val →
        (b - e_end).val ≤ (e_start - e_end).val →
        AngleLt v q0 (S (cyc.toFun a)) (S (cyc.toFun b)) ∧
        0 < orient2D v (S (cyc.toFun a)) (S (cyc.toFun b))) := by
  let c : Fin (k + 3) → ℝ × ℝ := fun i => S (cyc.toFun i)
  obtain ⟨j_nf, hj_nf⟩ := exists_nonfacing_edge c cyc.ccw v
  let F : Finset (Fin (k + 3)) :=
    Finset.univ.filter (fun j => orient2D (c j) (c (j + 1)) v < 0)
  have hF_ne : F.Nonempty := by
    rcases h_ex with ⟨j0, hj0⟩
    exact ⟨j0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj0⟩⟩
  let Off : Finset ℕ := F.image (fun j => (j - j_nf).val)
  have hOff_ne : Off.Nonempty := Finset.Nonempty.image hF_ne _
  let t_min := Off.min' hOff_ne
  let t_max := Off.max' hOff_ne
  have ht_min_mem : t_min ∈ Off := Finset.min'_mem Off hOff_ne
  have ht_max_mem : t_max ∈ Off := Finset.max'_mem Off hOff_ne
  have ht_le : t_min ≤ t_max := Finset.min'_le Off t_max ht_max_mem
  obtain ⟨j_min, hj_min_F, hj_min_eq⟩ := Finset.mem_image.mp ht_min_mem
  obtain ⟨j_max, hj_max_F, hj_max_eq⟩ := Finset.mem_image.mp ht_max_mem
  have hj_nf_not_F : j_nf ∉ F := fun h => by
    have := (Finset.mem_filter.mp h).2; linarith
  have ht_min_pos : 1 ≤ t_min := by
    by_contra h0
    have hz : t_min = 0 := by omega
    rw [hz] at hj_min_eq
    have heq : j_min = j_nf := sub_eq_zero.mp (Fin.ext hj_min_eq)
    rw [heq] at hj_min_F; exact hj_nf_not_F hj_min_F
  have ht_max_lt : t_max < k + 3 := by
    rw [← hj_max_eq]; exact (j_max - j_nf).isLt
  let L := t_max - t_min + 1
  have hL1 : 1 ≤ L := by omega
  have hL_le : L ≤ k + 2 := by omega
  let e_start := j_min
  let e_end := j_max + 1
  have he_end_eq : e_end = e_start + finNat (k + 3) L := by
    have hjm_eq : j_min = j_nf + finNat (k + 3) t_min := by
      have : finNat (k + 3) t_min = j_min - j_nf := by
        ext; simp [finNat, Nat.mod_eq_of_lt (by omega : t_min < k + 3), hj_min_eq]
      rw [this, add_sub_cancel]
    have hjM_eq : j_max = j_nf + finNat (k + 3) t_max := by
      have : finNat (k + 3) t_max = j_max - j_nf := by
        ext; simp [finNat, Nat.mod_eq_of_lt (by omega : t_max < k + 3), hj_max_eq]
      rw [this, add_sub_cancel]
    have h1_val : (1 : Fin (k + 3)).val = 1 := by simp [Nat.mod_eq_of_lt (by omega : 1 < k + 3)]
    have hfin_eq : finNat (k + 3) t_min + finNat (k + 3) L = finNat (k + 3) t_max + 1 := by
      ext
      simp only [Fin.val_add, finNat, h1_val,
        Nat.mod_eq_of_lt (by omega : t_min < k + 3),
        Nat.mod_eq_of_lt (by omega : L < k + 3),
        Nat.mod_eq_of_lt ht_max_lt]
      congr 1; omega
    dsimp [e_start, e_end]
    rw [hjm_eq, hjM_eq, add_assoc, ← hfin_eq]
    abel
  have harc := facing_edges_contiguous c cyc.ccw v j_min j_max
    (Finset.mem_filter.mp hj_min_F).2 (Finset.mem_filter.mp hj_max_F).2
  have hjM_m_jm : (j_max - j_min).val = t_max - t_min := by
    have h1 : j_max - j_min = (j_max - j_nf) - (j_min - j_nf) := by abel
    rw [h1, fin_val_sub_eq, if_pos (Fin.le_def.mpr (by omega)), hj_max_eq, hj_min_eq]
  have h_face_lt : ∀ m : Fin (k + 3), (m - e_start).val < L →
      orient2D (c m) (c (m + 1)) v < 0 := by
    by_cases hmm : j_min = j_max
    · intro m hm
      have ht_eq : t_min = t_max := by rw [← hj_min_eq, ← hj_max_eq, hmm]
      have hL1' : L = 1 := by dsimp [L]; omega
      have hm0 : m - e_start = 0 := Fin.ext (by change (m - e_start).val = 0; omega)
      have hme : m = j_min := sub_eq_zero.mp hm0
      rw [hme]; exact (Finset.mem_filter.mp hj_min_F).2
    · rcases harc with h1 | h2
      · intro m hm; exact h1 m (by dsimp [e_start] at hm ⊢; rw [hjM_m_jm]; omega)
      · exfalso
        have hj_le : (j_nf - j_max).val ≤ (j_min - j_max).val := by
          have h_ne : j_nf ≠ j_max := fun h => hj_nf_not_F (h ▸ hj_max_F)
          have hc1 := fin_sub_add_compl h_ne
          have hj_nf_val : (j_nf - j_max).val = k + 3 - t_max := by omega
          have hc2 := fin_sub_add_compl hmm
          rw [hj_nf_val]; omega
        have hbad := h2 j_nf hj_le
        linarith
  have h_nonface_ge : ∀ m : Fin (k + 3), L ≤ (m - e_start).val →
      0 < orient2D (c m) (c (m + 1)) v := by
    intro m hm
    have hm_not_F : m ∉ F := by
      intro hmF
      have ht_mem : (m - j_nf).val ∈ Off := Finset.mem_image_of_mem _ hmF
      have hge := Finset.min'_le Off _ ht_mem
      have hle := Finset.le_max' Off _ ht_mem
      have hdiff : (m - e_start).val = (m - j_nf).val - t_min := by
        have h1 : m - e_start = (m - j_nf) - (j_min - j_nf) := by abel
        change t_min ≤ (m - j_nf).val at hge
        rw [← hj_min_eq] at hge
        rw [h1, fin_val_sub_eq, if_pos (Fin.le_def.mpr hge), hj_min_eq]
      dsimp [t_min, t_max, L] at hm hge hle
      omega
    have hnn : 0 ≤ orient2D (c m) (c (m + 1)) v := by
      by_contra hlt
      exact hm_not_F (Finset.mem_filter.mpr ⟨Finset.mem_univ _, not_le.mp hlt⟩)
    have hne : m ≠ m + 1 := fin_add_one_ne_self m
    exact lt_of_le_of_ne hnn (hv_noncol m (m + 1) hne).symm
  have h_end_diff : (e_end - e_start).val = L := by
    rw [he_end_eq, add_sub_cancel_left]; exact Nat.mod_eq_of_lt (by omega)
  have h_se_diff : (e_start - e_end).val = k + 3 - L := by
    have hne : e_start ≠ e_end := fun h => by rw [h, sub_self, Fin.val_zero] at h_end_diff; omega
    have := fin_sub_add_compl hne
    omega
  have h_far_iff : ∀ p : Fin (k + 3), ¬ (0 < (p - e_start).val ∧ (p - e_start).val < L) ↔
      (p - e_end).val ≤ (e_start - e_end).val := by
    intro p
    have h1 : p - e_end = (p - e_start) - (e_end - e_start) := by abel
    rw [h1, fin_val_sub_eq (p - e_start) (e_end - e_start), h_end_diff, h_se_diff]
    split_ifs with hle
    · have hp_ge : L ≤ (p - e_start).val := by rwa [Fin.le_def, h_end_diff] at hle
      have := (p - e_start).isLt
      constructor <;> intro _ <;> omega
    · have hp_lt : (p - e_start).val < L := by
        have := Fin.lt_def.mp (lt_of_not_ge hle); rwa [h_end_diff] at this
      constructor
      · intro hnot
        have hp0 : (p - e_start).val = 0 := by omega
        rw [hp0]
      · intro hle' ⟨hpos, _⟩
        omega
  have h_orient_end : 0 < orient2D v (c e_end) (c e_start) := by
    rw [he_end_eq]
    refine chain_facing_end_orient c (fun x y z h1 h2 => ccwCycle_ccw3 cyc h1 h2) v e_start L hL1 (by omega) ?_
    intro t ht
    refine h_face_lt (e_start + finNat (k + 3) t) ?_
    rw [add_sub_cancel_left]; rw [show (finNat (k + 3) t).val = t from Nat.mod_eq_of_lt (by omega)]
    exact ht
  let q0 : ℝ × ℝ := (v.1 + (c e_end).1 - (c e_start).1, v.2 + (c e_end).2 - (c e_start).2)
  have hq0_pos : ∀ p : Fin (k + 3), (p - e_end).val ≤ (e_start - e_end).val →
      0 < orient2D v q0 (c p) := by
    intro p hp
    have hid : orient2D v q0 (c p) =
        orient2D (c e_end) (c e_start) v - orient2D (c e_end) (c e_start) (c p) := by
      dsimp [q0]; unfold orient2D; ring
    have h1 : 0 < orient2D (c e_end) (c e_start) v := by
      unfold orient2D at h_orient_end ⊢; linarith
    have h2 : orient2D (c e_end) (c e_start) (c p) ≤ 0 := by
      by_cases hpe : p = e_end
      · rw [hpe, orient2D_self_outer]
      · by_cases hps : p = e_start
        · rw [hps, orient2D_self_right]
        · have hpos1 : 0 < (p - e_end).val := Nat.pos_of_ne_zero (fun h => hpe (sub_eq_zero.mp (Fin.ext h)))
          have hlt1 : (p - e_end).val < (e_start - e_end).val :=
            lt_of_le_of_ne hp (fun h => hps (by
              have := sub_left_inj.mp (Fin.ext h); exact this))
          have hccw := ccwCycle_ccw3 cyc hpos1 hlt1
          dsimp [c] at hccw ⊢
          unfold orient2D at hccw ⊢; linarith
    linarith
  have h_ang : ∀ a b : Fin (k + 3), (a - e_end).val < (b - e_end).val →
      (b - e_end).val ≤ (e_start - e_end).val →
      AngleLt v q0 (c a) (c b) ∧ 0 < orient2D v (c a) (c b) := by
    have h1_val : (1 : Fin (k + 3)).val = 1 := by
      simp [Nat.mod_eq_of_lt (by omega : 1 < k + 3)]
    have h_step1 : ∀ a : Fin (k + 3), (a + 1 - e_end).val ≤ (e_start - e_end).val →
        (a - e_end).val < (a + 1 - e_end).val →
        AngleLt v q0 (c a) (c (a + 1)) := by
      intro a hle hlt
      have hqa := hq0_pos a (le_trans (le_of_lt hlt) hle)
      have hqb := hq0_pos (a + 1) hle
      have hm_ge : L ≤ (a - e_start).val := by
        have h1 : a - e_start = (a - e_end) + (e_end - e_start) := by abel
        rw [h1, Fin.val_add, h_end_diff]
        have := hlt
        rw [Nat.mod_eq_of_lt (by omega : (a - e_end).val + L < k + 3)]
        omega
      have hnf := h_nonface_ge a hm_ge
      have hpos_v : 0 < orient2D v (c a) (c (a + 1)) := by
        unfold orient2D at hnf ⊢; linarith
      exact ⟨by unfold OnSameSide; exact mul_pos hqa hqb, mul_pos hqa hpos_v⟩
    have hstep : ∀ d : ℕ, ∀ a b : Fin (k + 3), (b - e_end).val - (a - e_end).val = d →
        (a - e_end).val < (b - e_end).val → (b - e_end).val ≤ (e_start - e_end).val →
        AngleLt v q0 (c a) (c b) := by
      intro d
      induction d with
      | zero => intro a b hd hlt _; omega
      | succ d ih =>
        intro a b hd hlt hle
        by_cases hd0 : d = 0
        · have hba1 : b = a + 1 := by
            have h1 : (b - e_end) - (a - e_end) = 1 := by
              ext; rw [fin_val_sub_eq (b - e_end) (a - e_end),
                if_pos (Fin.le_def.mpr (le_of_lt hlt)), h1_val]
              omega
            have h2 : b - a = 1 := by rw [← h1]; abel
            exact eq_add_of_sub_eq' h2
          subst hba1
          exact h_step1 a hle hlt
        · have hbt : (b - e_end).val < k + 3 := (b - e_end).isLt
          have ha1_diff : (a - e_end).val < (a + 1 - e_end).val := by
            have h1 : a + 1 - e_end = (a - e_end) + 1 := by abel
            rw [h1, Fin.val_add, h1_val, Nat.mod_eq_of_lt (by omega)]
            omega
          have ha1_val : (a + 1 - e_end).val = (a - e_end).val + 1 := by
            have h1 : a + 1 - e_end = (a - e_end) + 1 := by abel
            rw [h1, Fin.val_add, h1_val, Nat.mod_eq_of_lt (by omega)]
          have ha1_lt : (a + 1 - e_end).val < (b - e_end).val := by omega
          have h1 := h_step1 a (le_trans (le_of_lt ha1_lt) hle) ha1_diff
          have h2 := ih (a + 1) b (by omega) ha1_lt hle
          exact h1.trans h2
    intro a b hab hb
    have hang := hstep ((b - e_end).val - (a - e_end).val) a b rfl hab hb
    refine ⟨hang, ?_⟩
    have hqa := hq0_pos a (le_trans (le_of_lt hab) hb)
    have hmul := hang.2
    nlinarith only [hqa, hmul]
  exact ⟨e_start, e_end, L, hL1, hL_le, he_end_eq, h_face_lt, h_nonface_ge, h_far_iff,
    h_orient_end, hq0_pos, h_ang⟩

lemma segmentsCross_inIntTri_left {v y u0 v0 b' p : ℝ × ℝ}
    (hy : InIntTri v u0 v0 y)
    (h1 : 0 < orient2D v b' p) (h2 : 0 < orient2D v p y) (h3 : 0 < orient2D v b' y)
    (hpu : 0 ≤ orient2D b' p u0) (hpv : 0 < orient2D b' p v0) :
    SegmentsCross v p b' y := by
  rcases hy with ⟨μ₁, μ₂, μ₃, hm1, hm2, hm3, hsum, hy1, hy2⟩
  have hid := orient2D_convex_comb3 b' p v u0 v0 y μ₁ μ₂ μ₃ hsum hy1 hy2
  have hv_pos : 0 < orient2D b' p v := by unfold orient2D at h1 ⊢; linarith
  have hbpy : 0 < orient2D b' p y := by
    rw [hid]
    exact add_pos (add_pos_of_pos_of_nonneg (mul_pos hm1 hv_pos) (mul_nonneg (le_of_lt hm2) hpu)) (mul_pos hm3 hpv)
  have hbyv : 0 < orient2D b' y v := by unfold orient2D at h3 ⊢; linarith
  have hbyp : orient2D b' y p < 0 := by unfold orient2D at hbpy ⊢; linarith
  have hvpb : orient2D v p b' < 0 := by unfold orient2D at h1 ⊢; linarith
  exact ⟨mul_neg_of_neg_of_pos hvpb h2, mul_neg_of_pos_of_neg hbyv hbyp⟩

lemma segmentsCross_inIntTri_right {v y u0 v0 b p : ℝ × ℝ}
    (hy : InIntTri v u0 v0 y)
    (h1 : 0 < orient2D v y p) (h2 : 0 < orient2D v p b) (h3 : 0 < orient2D v y b)
    (hpu : 0 < orient2D u0 p b) (hpv : 0 ≤ orient2D v0 p b) :
    SegmentsCross v p y b := by
  rcases hy with ⟨μ₁, μ₂, μ₃, hm1, hm2, hm3, hsum, hy1, hy2⟩
  have hid := orient2D_convex_comb3 p b v u0 v0 y μ₁ μ₂ μ₃ hsum hy1 hy2
  have hv_pos : 0 < orient2D p b v := by unfold orient2D at h2 ⊢; linarith
  have hu_pos : 0 < orient2D p b u0 := by unfold orient2D at hpu ⊢; linarith
  have hvo_nn : 0 ≤ orient2D p b v0 := by unfold orient2D at hpv ⊢; linarith
  have hpby : 0 < orient2D p b y := by
    rw [hid]
    exact add_pos_of_pos_of_nonneg (add_pos (mul_pos hm1 hv_pos) (mul_pos hm2 hu_pos)) (mul_nonneg (le_of_lt hm3) hvo_nn)
  have hybv : 0 < orient2D y b v := by unfold orient2D at h3 ⊢; linarith
  have hybp : orient2D y b p < 0 := by unfold orient2D at hpby ⊢; linarith
  have hvpy : orient2D v p y < 0 := by unfold orient2D at h1 ⊢; linarith
  exact ⟨mul_neg_of_neg_of_pos hvpy h2, mul_neg_of_pos_of_neg hybv hybp⟩

lemma segmentsCross_gapMid_of_convex {v b p b' : ℝ × ℝ}
    (h1 : 0 < orient2D v b p) (h2 : 0 < orient2D v p b') (h3 : 0 < orient2D v b b')
    (hconv : 0 < orient2D b p b') :
    SegmentsCross v p b b' := by
  have hvpb : orient2D v p b < 0 := by unfold orient2D at h1 ⊢; linarith
  have hbb'v : 0 < orient2D b b' v := by unfold orient2D at h3 ⊢; linarith
  have hbb'p : orient2D b b' p < 0 := by unfold orient2D at hconv ⊢; linarith
  exact ⟨mul_neg_of_neg_of_pos hvpb h2, mul_neg_of_pos_of_neg hbb'v hbb'p⟩

lemma segmentsCross_between_exits_shared {v u0 v0 u1 y0 y1 : ℝ × ℝ}
    (hy0 : InIntTri v u0 v0 y0)
    (h1 : 0 < orient2D v y0 v0) (h2 : 0 < orient2D v v0 y1) (h3 : 0 < orient2D v y0 y1)
    (h_edge : 0 < orient2D u0 v0 y1) :
    SegmentsCross v v0 y0 y1 := by
  rcases hy0 with ⟨μ₁, μ₂, μ₃, hm1, hm2, hm3, hsum, hy1, hy2⟩
  have hid := orient2D_convex_comb3 v0 y1 v u0 v0 y0 μ₁ μ₂ μ₃ hsum hy1 hy2
  have hv_pos : 0 < orient2D v0 y1 v := by unfold orient2D at h2 ⊢; linarith
  have hu_pos : 0 < orient2D v0 y1 u0 := by unfold orient2D at h_edge ⊢; linarith
  rw [orient2D_self_outer, mul_zero, add_zero] at hid
  have hv0_y1_y0 : 0 < orient2D v0 y1 y0 := by rw [hid]; exact add_pos (mul_pos hm1 hv_pos) (mul_pos hm2 hu_pos)
  have hy0y1_v : 0 < orient2D y0 y1 v := by unfold orient2D at h3 ⊢; linarith
  have hy0y1_v0 : orient2D y0 y1 v0 < 0 := by unfold orient2D at hv0_y1_y0 ⊢; linarith
  have hvv0_y0 : orient2D v v0 y0 < 0 := by unfold orient2D at h1 ⊢; linarith
  exact ⟨mul_neg_of_neg_of_pos hvv0_y0 h2, mul_neg_of_pos_of_neg hy0y1_v hy0y1_v0⟩

lemma segmentsCross_between_exits_shared_right {v u1 v1 y0 y1 : ℝ × ℝ}
    (hy1 : InIntTri v u1 v1 y1)
    (h1 : 0 < orient2D v y0 u1) (h2 : 0 < orient2D v u1 y1) (h3 : 0 < orient2D v y0 y1)
    (h_edge : 0 < orient2D u1 v1 y0) :
    SegmentsCross v u1 y0 y1 := by
  rcases hy1 with ⟨ν₁, ν₂, ν₃, hn1, hn2, hn3, hsum, hy1x, hy1y⟩
  have hid := orient2D_convex_comb3 y0 u1 v u1 v1 y1 ν₁ ν₂ ν₃ hsum hy1x hy1y
  have hv_pos : 0 < orient2D y0 u1 v := by unfold orient2D at h1 ⊢; linarith
  have hv1_pos : 0 < orient2D y0 u1 v1 := by unfold orient2D at h_edge ⊢; linarith
  rw [orient2D_self_right, mul_zero, add_zero] at hid
  have hy0u1_y1 : 0 < orient2D y0 u1 y1 := by rw [hid]; exact add_pos (mul_pos hn1 hv_pos) (mul_pos hn3 hv1_pos)
  have hy0y1_v : 0 < orient2D y0 y1 v := by unfold orient2D at h3 ⊢; linarith
  have hy0y1_u1 : orient2D y0 y1 u1 < 0 := by unfold orient2D at hy0u1_y1 ⊢; linarith
  have hvu1_y0 : orient2D v u1 y0 < 0 := by unfold orient2D at h1 ⊢; linarith
  exact ⟨mul_neg_of_neg_of_pos hvu1_y0 h2, mul_neg_of_pos_of_neg hy0y1_v hy0y1_u1⟩

private lemma good_gap_of_all_cross {n : ℕ} {P : Set (ℝ × ℝ)}
    {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ}
    (hPoly : ShatteredSimplePolygon P S w) (h25 : Sec2To5Interface P S w)
    {O_miss Γ : Finset (Fin n)} {oa ob : Fin n}
    (hgap : GoodAnchorPair P S w O_miss oa ob)
    (hΓ_cross : ∀ p ∈ Γ, p ≠ oa ∧ p ≠ ob ∧ p ∉ O_miss ∧
      p ∈ hullVertices S ∧ SegmentsCross (w (Finset.univ \ O_miss)) (S p) (S oa) (S ob)) :
    (∀ p ∈ Γ,
      IsBackVertexOf S (hullVertices S) p (w (Finset.univ \ O_miss)) ∧
      SegmentsCross (w (Finset.univ \ O_miss)) (S p) (S oa) (S ob) ∧
      (∃ H_hp : OpenHalfPlane, IsHalfPlaneTest P (WitnessSet {oa, ob} ∅ w) (S p) H_hp)) ∧
    (∀ z : Fin n, z ≠ oa → z ≠ ob → z ∉ O_miss →
      S z ∈ convexHull ℝ ((Γ ∪ {oa, ob}).image S : Set (ℝ × ℝ)) →
      SegmentsCross (w (Finset.univ \ O_miss)) (S z) (S oa) (S ob) ∧
      (∃ H_hp : OpenHalfPlane, IsHalfPlaneTest P (WitnessSet {oa, ob} ∅ w) (S z) H_hp) ∧
      (z ∈ hullVertices S → IsBackVertexOf S (hullVertices S) z (w (Finset.univ \ O_miss)))) := by
  refine ⟨fun p hp => ?_, fun z hza hzc hzO hz_conv => ?_⟩
  · rcases hΓ_cross p hp with ⟨_, _, hpO, hpB, hcr⟩
    obtain ⟨hhp, hbk⟩ := goodAnchorPair_universal_crossing hPoly h25 hgap hpO hcr
    exact ⟨hbk hpB, hcr, hhp⟩
  · refine cap_crossing_of_vertices_cross hPoly h25 hgap (Γ ∪ {oa, ob}) (fun g hg => ?_) hzO hza hzc hz_conv
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hg
    rcases hg with hgΓ | rfl | rfl
    · exact Or.inr (Or.inr (hΓ_cross g hgΓ).2.2.2.2)
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)

private lemma goodAnchorPair_of_see {n : ℕ} {P : Set (ℝ × ℝ)}
    {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ}
    {O_miss : Finset (Fin n)} {oa ob : Fin n}
    (hao : oa ∈ O_miss) (hbo : ob ∈ O_miss) (hne : oa ≠ ob)
    (hsee : Sees P (w (Finset.univ \ O_miss)) (w Finset.univ))
    (hss : OnSameSide (w (Finset.univ \ O_miss)) (w Finset.univ) (S oa) (S ob))
    (hnc : orient2D (w (Finset.univ \ O_miss)) (S oa) (S ob) ≠ 0) :
    GoodAnchorPair P S w O_miss oa ob := by
  let v := w (Finset.univ \ O_miss)
  let q := w Finset.univ
  refine ⟨hao, hbo, hne, ?_⟩
  have hqa : orient2D v q (S oa) ≠ 0 := fun h => by
    unfold OnSameSide at hss; rw [h, zero_mul] at hss; linarith
  rcases lt_or_gt_of_ne hnc with hneg | hpos <;> rcases lt_or_gt_of_ne hqa with hqn | hqp
  · left
    exact ⟨⟨hss, mul_pos_of_neg_of_neg hqn hneg⟩, Or.inl hsee⟩
  · right
    have hpos' : 0 < orient2D v (S ob) (S oa) := by unfold orient2D at hneg ⊢; linarith
    have hqb_pos : 0 < orient2D v q (S ob) := by unfold OnSameSide at hss; nlinarith
    exact ⟨⟨hss.symm, mul_pos hqb_pos hpos'⟩, Or.inl hsee⟩
  · right
    have hqb : orient2D v q (S ob) < 0 := by unfold OnSameSide at hss; nlinarith
    have hneg' : orient2D v (S ob) (S oa) < 0 := by unfold orient2D at hpos ⊢; linarith
    exact ⟨⟨hss.symm, mul_pos_of_neg_of_neg hqb hneg'⟩, Or.inl hsee⟩
  · left
    exact ⟨⟨hss, mul_pos hqp hpos⟩, Or.inl hsee⟩

private lemma goodAnchorPair_of_cone_ends {n : ℕ} {P : Set (ℝ × ℝ)}
    {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ}
    {O_miss : Finset (Fin n)} {oa ob : Fin n}
    (hao : oa ∈ O_miss) (hbo : ob ∈ O_miss) (hne : oa ≠ ob)
    (hss : OnSameSide (w (Finset.univ \ O_miss)) (w Finset.univ) (S oa) (S ob))
    (ho : 0 < orient2D (w (Finset.univ \ O_miss)) (S oa) (S ob))
    (he1 : 0 < orient2D (w (Finset.univ \ O_miss)) (w Finset.univ) (S oa) →
      ∃ e1 : Fin n, e1 ∉ O_miss ∧
        0 < orient2D (w (Finset.univ \ O_miss)) (w Finset.univ) (S e1) ∧
        0 < orient2D (w (Finset.univ \ O_miss)) (S e1) (S oa))
    (he2 : orient2D (w (Finset.univ \ O_miss)) (w Finset.univ) (S oa) < 0 →
      ∃ e2 : Fin n, e2 ∉ O_miss ∧
        orient2D (w (Finset.univ \ O_miss)) (w Finset.univ) (S e2) < 0 ∧
        0 < orient2D (w (Finset.univ \ O_miss)) (S ob) (S e2)) :
    GoodAnchorPair P S w O_miss oa ob := by
  let v := w (Finset.univ \ O_miss)
  let q := w Finset.univ
  refine ⟨hao, hbo, hne, ?_⟩
  have hqa : orient2D v q (S oa) ≠ 0 := fun h => by
    unfold OnSameSide at hss; rw [h, zero_mul] at hss; linarith
  rcases lt_or_gt_of_ne hqa with hqn | hqp
  · have hqb : orient2D v q (S ob) < 0 := by unfold OnSameSide at hss; nlinarith
    obtain ⟨e2, he2O, he2q, he2o⟩ := he2 hqn
    right
    refine ⟨⟨hss.symm, mul_pos_of_neg_of_neg hqb (by unfold orient2D at ho ⊢; linarith)⟩, ?_⟩
    right
    refine ⟨e2, he2O, ⟨by unfold OnSameSide; exact mul_pos_of_neg_of_neg he2q hqb, ?_⟩⟩
    exact mul_pos_of_neg_of_neg he2q (by unfold orient2D at he2o ⊢; linarith)
  · obtain ⟨e1, he1O, he1q, he1o⟩ := he1 hqp
    left
    refine ⟨⟨hss, mul_pos hqp ho⟩, Or.inr ⟨e1, he1O, ⟨by unfold OnSameSide; exact mul_pos he1q hqp, ?_⟩⟩⟩
    exact mul_pos he1q he1o

private lemma three_missed_in_cone_pigeonhole (v q m1 m2 m3 : ℝ × ℝ)
    (hq1 : orient2D v q m1 ≠ 0) (hq2 : orient2D v q m2 ≠ 0) (hq3 : orient2D v q m3 ≠ 0)
    (h12 : 0 < orient2D v m1 m2) (h23 : 0 < orient2D v m2 m3) (h13 : 0 < orient2D v m1 m3) :
    OnSameSide v q m1 m2 ∨ OnSameSide v q m2 m3 := by
  by_contra hnot
  push Not at hnot
  have h12_neg : orient2D v q m1 * orient2D v q m2 < 0 :=
    lt_of_le_of_ne (not_lt.mp hnot.1) (mul_ne_zero hq1 hq2)
  have h23_neg : orient2D v q m2 * orient2D v q m3 < 0 :=
    lt_of_le_of_ne (not_lt.mp hnot.2) (mul_ne_zero hq2 hq3)
  have hid := orient2D_angle_trans_id v q m1 m2 m3
  rcases lt_or_gt_of_ne hq2 with h2n | h2p
  · have h1p : 0 < orient2D v q m1 := by nlinarith
    have h3p : 0 < orient2D v q m3 := by nlinarith
    have hL : orient2D v q m2 * orient2D v m1 m3 < 0 := mul_neg_of_neg_of_pos h2n h13
    have hR1 : 0 < orient2D v q m1 * orient2D v m2 m3 := mul_pos h1p h23
    have hR2 : 0 < orient2D v q m3 * orient2D v m1 m2 := mul_pos h3p h12
    linarith
  · have h1n : orient2D v q m1 < 0 := by nlinarith
    have h3n : orient2D v q m3 < 0 := by nlinarith
    have hL : 0 < orient2D v q m2 * orient2D v m1 m3 := mul_pos h2p h13
    have hR1 : orient2D v q m1 * orient2D v m2 m3 < 0 := mul_neg_of_neg_of_pos h1n h23
    have hR2 : orient2D v q m3 * orient2D v m1 m2 < 0 := mul_neg_of_neg_of_pos h3n h12
    linarith

private lemma fourgon_diag_cramer (v q u0 d b' b : ℝ × ℝ) :
    (orient2D b' b d * orient2D v q u0 + (-orient2D b' b u0) * orient2D v q d =
      (-orient2D u0 d b) * orient2D v q b' + orient2D u0 d b' * orient2D v q b) ∧
    (orient2D b' b d * orient2D v d u0 =
      (-orient2D u0 d b) * orient2D v d b' + orient2D u0 d b' * orient2D v d b) := by
  unfold orient2D
  constructor <;> ring

private lemma farChain_all_nonfacing_lt_pi_subchain {n k : ℕ} {S : Fin n → ℝ × ℝ} {C : Finset (Fin n)}
    (cyc : CCWCycle S C k) (v q : ℝ × ℝ)
    (h_all_nf : ∀ m : Fin (k + 3), 0 < orient2D (S (cyc.toFun m)) (S (cyc.toFun (m + 1))) v)
    (a b : Fin (k + 3)) (hab : a ≠ b)
    (h_arc_ss : ∀ t : ℕ, t ≤ (b - a).val →
      OnSameSide v q (S (cyc.toFun a)) (S (cyc.toFun (a + finNat (k + 3) t)))) :
    ∀ x z : Fin (k + 3), (x - a).val < (z - a).val → (z - a).val ≤ (b - a).val →
      0 < orient2D v (S (cyc.toFun x)) (S (cyc.toFun z)) ∧
      (0 < orient2D v q (S (cyc.toFun a)) → AngleLt v q (S (cyc.toFun x)) (S (cyc.toFun z))) ∧
      (orient2D v q (S (cyc.toFun a)) < 0 → AngleLt v q (S (cyc.toFun z)) (S (cyc.toFun x))) := by
  have hmono := farChain_arc_angle_monotone cyc v q a b (fun t _ => h_all_nf _) h_arc_ss
  have hqa_ne : orient2D v q (S (cyc.toFun a)) ≠ 0 := by
    have h0 := h_arc_ss 0 (Nat.zero_le _)
    rw [finNat_zero, add_zero] at h0
    unfold OnSameSide at h0
    intro hz; rw [hz, mul_zero] at h0; linarith
  intro x z hxz hzb
  have htx : a + finNat (k + 3) (x - a).val = x := by
    have : finNat (k + 3) (x - a).val = x - a := by ext; exact Nat.mod_eq_of_lt (x - a).isLt
    rw [this, add_sub_cancel]
  have htz : a + finNat (k + 3) (z - a).val = z := by
    have : finNat (k + 3) (z - a).val = z - a := by ext; exact Nat.mod_eq_of_lt (z - a).isLt
    rw [this, add_sub_cancel]
  rcases lt_or_gt_of_ne hqa_ne with hqn | hqp
  · have hang := hmono.2 hqn (x - a).val (z - a).val hxz hzb
    rw [htx, htz] at hang
    have hqx : orient2D v q (S (cyc.toFun x)) < 0 := by
      have hxss := h_arc_ss (x - a).val (le_trans (le_of_lt hxz) hzb)
      rw [htx] at hxss; unfold OnSameSide at hxss; nlinarith
    have hpos : 0 < orient2D v (S (cyc.toFun x)) (S (cyc.toFun z)) := by
      have h2 := hang.2
      have hlt : orient2D v (S (cyc.toFun z)) (S (cyc.toFun x)) < 0 := by
        have hqz : orient2D v q (S (cyc.toFun z)) < 0 := by
          have hzss := h_arc_ss (z - a).val hzb
          rw [htz] at hzss; unfold OnSameSide at hzss; nlinarith
        nlinarith only [hqz, h2]
      unfold orient2D at hlt ⊢; linarith
    exact ⟨hpos, fun h => False.elim (by linarith), fun _ => hang⟩
  · have hang := hmono.1 hqp (x - a).val (z - a).val hxz hzb
    rw [htx, htz] at hang
    have hqx : 0 < orient2D v q (S (cyc.toFun x)) := by
      have hxss := h_arc_ss (x - a).val (le_trans (le_of_lt hxz) hzb)
      rw [htx] at hxss; unfold OnSameSide at hxss; nlinarith
    have hpos : 0 < orient2D v (S (cyc.toFun x)) (S (cyc.toFun z)) := by
      have h2 := hang.2; nlinarith only [hqx, h2]
    exact ⟨hpos, fun _ => hang, fun h => False.elim (by linarith)⟩

private lemma isPolygonalPathIn_three {P : Set (ℝ × ℝ)} {s a t : ℝ × ℝ}
    (h1 : Sees P s a) (h2 : Sees P a t) :
    IsPolygonalPathIn P s t [s, a, t] := by
  refine ⟨by simp, rfl, rfl, fun x hx => ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | hxa | hxt
    · exact h1 (left_mem_segment ℝ x a)
    · exact hxa ▸ h1 (right_mem_segment ℝ s a)
    · exact hxt ▸ h2 (right_mem_segment ℝ a t)
  · exact List.isChain_cons_cons.mpr ⟨h1, List.isChain_cons_cons.mpr ⟨h2, List.isChain_singleton _⟩⟩

private lemma fin_val_one_of_gt {N : ℕ} [NeZero N] (hN : 1 < N) : (1 : Fin N).val = 1 := by
  simp [Nat.mod_eq_of_lt hN]

private lemma fin_sub_split_le {N : ℕ} [NeZero N] {x y z : Fin N}
    (hyz : (y - x).val ≤ (z - x).val) :
    (z - y).val + (y - x).val = (z - x).val := by
  by_cases hxy : x = y
  · subst hxy; simp
  · by_cases hyz' : (y - x).val = (z - x).val
    · have hyz_eq : y = z := sub_left_inj.mp (Fin.ext hyz')
      subst hyz_eq; simp
    · exact (fin_sub_split_lt
        (Nat.pos_of_ne_zero (fun h => hxy (sub_eq_zero.mp (Fin.ext h)).symm))
        (lt_of_le_of_ne hyz hyz')).1

private lemma facing_arc_subchain_order {n k : ℕ} {S : Fin n → ℝ × ℝ} {C : Finset (Fin n)}
    (cyc : CCWCycle S C k) (v : ℝ × ℝ) (e_start e_end : Fin (k + 3))
    (h_ang : ∀ a b : Fin (k + 3), (a - e_end).val < (b - e_end).val →
      (b - e_end).val ≤ (e_start - e_end).val →
      0 < orient2D v (S (cyc.toFun a)) (S (cyc.toFun b)))
    {a c : Fin (k + 3)}
    (ha_far : (a - e_end).val ≤ (e_start - e_end).val)
    (hc_le : (c - a).val ≤ (e_start - a).val) :
    (∀ m : Fin (k + 3), (m - a).val ≤ (c - a).val →
      (m - e_end).val = (m - a).val + (a - e_end).val ∧
      (m - e_end).val ≤ (e_start - e_end).val) ∧
    (∀ x z : Fin (k + 3), (x - a).val < (z - a).val → (z - a).val ≤ (c - a).val →
      0 < orient2D v (S (cyc.toFun x)) (S (cyc.toFun z))) := by
  have h_tot := fin_sub_split_le ha_far
  have h_eq : ∀ m : Fin (k + 3), (m - a).val ≤ (c - a).val →
      (m - e_end).val = (m - a).val + (a - e_end).val ∧
      (m - e_end).val ≤ (e_start - e_end).val := by
    intro m hm
    have hlt : (m - a).val + (a - e_end).val < k + 3 := by
      have := (e_start - e_end).isLt; omega
    have heq : m - e_end = (m - a) + (a - e_end) := by abel
    have hv : (m - e_end).val = (m - a).val + (a - e_end).val := by
      rw [heq, Fin.val_add, Nat.mod_eq_of_lt hlt]
    exact ⟨hv, by omega⟩
  refine ⟨h_eq, fun x z hxz hzc => ?_⟩
  have hx := h_eq x (le_trans (le_of_lt hxz) hzc)
  have hz := h_eq z hzc
  exact h_ang x z (by omega) hz.2

private def InteriorAnchorGoal {n kD : ℕ} (P : Set (ℝ × ℝ))
    (S : Fin n → ℝ × ℝ) (w : Finset (Fin n) → ℝ × ℝ) (D : Finset (Fin n))
    (cycD : CCWCycle S D kD) (y : Fin n) (ib' iu0 iv0 ib : Fin (kD + 3)) : Prop :=
  let b' := cycD.toFun ib'
  let u0 := cycD.toFun iu0
  let v0 := cycD.toFun iv0
  let b := cycD.toFun ib
  let O_star : Finset (Fin n) := {b', y, b}
  let v := w (Finset.univ \ O_star)
  let gapL := D.filter (fun p => ∃ m : Fin (kD + 3), cycD.toFun m = p ∧
    0 < (m - ib').val ∧ (m - ib').val ≤ (iu0 - ib').val)
  let gapR := D.filter (fun p => ∃ m : Fin (kD + 3), cycD.toFun m = p ∧
    (iv0 - ib').val ≤ (m - ib').val ∧ (m - ib').val < (ib - ib').val)
  let gapMid := D.filter (fun p => ∃ m : Fin (kD + 3), cycD.toFun m = p ∧
    0 < (m - ib).val ∧ (m - ib).val < (ib' - ib).val)
  ∃ (oa ob : Fin n) (Γ : Finset (Fin n)),
    ((oa = b' ∧ ob = y ∧ Γ = gapL) ∨
     (oa = y ∧ ob = b ∧ Γ = gapR) ∨
     (oa = b ∧ ob = b' ∧ Γ = gapMid)) ∧
    GoodAnchorPair P S w O_star oa ob ∧
    (∀ p ∈ Γ,
      IsBackVertexOf S (hullVertices S) p v ∧
      SegmentsCross v (S p) (S oa) (S ob) ∧
      (∃ H_hp : OpenHalfPlane, IsHalfPlaneTest P (WitnessSet {oa, ob} ∅ w) (S p) H_hp)) ∧
    (∀ z : Fin n, z ≠ oa → z ≠ ob → z ∉ O_star →
      S z ∈ convexHull ℝ ((Γ ∪ {oa, ob}).image S : Set (ℝ × ℝ)) →
      SegmentsCross v (S z) (S oa) (S ob) ∧
      (∃ H_hp : OpenHalfPlane, IsHalfPlaneTest P (WitnessSet {oa, ob} ∅ w) (S z) H_hp) ∧
      (z ∈ hullVertices S → IsBackVertexOf S (hullVertices S) z v))

private lemma interior_anchor_buildL {n kD : ℕ} {P : Set (ℝ × ℝ)}
    {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ}
    (hPoly : ShatteredSimplePolygon P S w) (h25 : Sec2To5Interface P S w)
    {D : Finset (Fin n)} (hDB : D = hullVertices S \ certifiedVertices S w)
    (cycD : CCWCycle S D kD) {y : Fin n} (hy_notD : y ∉ D)
    {ib' iu0 iv0 ib : Fin (kD + 3)} (hb_gt : (iu0 - ib').val < (ib - ib').val)
    (hy_tri : InIntTri (w (Finset.univ \ {cycD.toFun ib', y, cycD.toFun ib})) (S (cycD.toFun iu0)) (S (cycD.toFun iv0)) (S y))
    (hord2 : (iu0 - ib').val < (iv0 - ib').val)
    (hgap : GoodAnchorPair P S w {cycD.toFun ib', y, cycD.toFun ib} (cycD.toFun ib') y)
    (hb'y : 0 < orient2D (w (Finset.univ \ {cycD.toFun ib', y, cycD.toFun ib})) (S (cycD.toFun ib')) (S y))
    (hp_ord : ∀ m : Fin (kD + 3), 0 < (m - ib').val → (m - ib').val ≤ (iu0 - ib').val →
      0 < orient2D (w (Finset.univ \ {cycD.toFun ib', y, cycD.toFun ib})) (S (cycD.toFun ib')) (S (cycD.toFun m)) ∧
      0 < orient2D (w (Finset.univ \ {cycD.toFun ib', y, cycD.toFun ib})) (S (cycD.toFun m)) (S y)) :
    InteriorAnchorGoal P S w D cycD y ib' iu0 iv0 ib := by
  refine ⟨cycD.toFun ib', y, _, Or.inl ⟨rfl, rfl, rfl⟩, hgap, ?_⟩
  refine good_gap_of_all_cross hPoly h25 hgap (fun p hp => ?_)
  rcases (Finset.mem_filter.mp hp).2 with ⟨mp, rfl, hm1, hm2⟩
  have hmp_b' : mp ≠ ib' := fun h => by rw [h, sub_self, Fin.val_zero] at hm1; omega
  have hmp_b : mp ≠ ib := fun h => by rw [h] at hm2; omega
  have hmO : cycD.toFun mp ∉ ({cycD.toFun ib', y, cycD.toFun ib} : Finset (Fin n)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rintro (h | h | h)
    · exact hmp_b' (cycD.inj h)
    · exact hy_notD (h ▸ ccwCycle_mem cycD mp)
    · exact hmp_b (cycD.inj h)
  have hmB : cycD.toFun mp ∈ hullVertices S :=
    (Finset.mem_sdiff.mp (by rw [← hDB]; exact ccwCycle_mem cycD mp)).1
  have ho := hp_ord mp hm1 hm2
  have hpu : 0 ≤ orient2D (S (cycD.toFun ib')) (S (cycD.toFun mp)) (S (cycD.toFun iu0)) := by
    by_cases hmu : mp = iu0
    · rw [hmu, orient2D_self_right]
    · exact le_of_lt (ccwCycle_ccw3 cycD hm1 (lt_of_le_of_ne hm2 (fun h => hmu (sub_left_inj.mp (Fin.ext h)))))
  have hpv : 0 < orient2D (S (cycD.toFun ib')) (S (cycD.toFun mp)) (S (cycD.toFun iv0)) :=
    ccwCycle_ccw3 cycD hm1 (lt_of_le_of_lt hm2 hord2)
  exact ⟨cycD.inj.ne hmp_b', fun h => hy_notD (h ▸ ccwCycle_mem cycD mp), hmO, hmB,
    segmentsCross_inIntTri_left hy_tri ho.1 ho.2 hb'y hpu hpv⟩

private lemma interior_anchor_buildR {n kD : ℕ} {P : Set (ℝ × ℝ)}
    {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ}
    (hPoly : ShatteredSimplePolygon P S w) (h25 : Sec2To5Interface P S w)
    {D : Finset (Fin n)} (hDB : D = hullVertices S \ certifiedVertices S w)
    (cycD : CCWCycle S D kD) {y : Fin n} (hy_notD : y ∉ D)
    {ib' iu0 iv0 ib : Fin (kD + 3)}
    (hy_tri : InIntTri (w (Finset.univ \ {cycD.toFun ib', y, cycD.toFun ib})) (S (cycD.toFun iu0)) (S (cycD.toFun iv0)) (S y))
    (hord1 : 0 < (iu0 - ib').val) (hord2 : (iu0 - ib').val < (iv0 - ib').val) (hord3 : (iv0 - ib').val < (ib - ib').val)
    (hgap : GoodAnchorPair P S w {cycD.toFun ib', y, cycD.toFun ib} y (cycD.toFun ib))
    (hyb : 0 < orient2D (w (Finset.univ \ {cycD.toFun ib', y, cycD.toFun ib})) (S y) (S (cycD.toFun ib)))
    (hp_ord : ∀ m : Fin (kD + 3), (iv0 - ib').val ≤ (m - ib').val → (m - ib').val < (ib - ib').val →
      0 < orient2D (w (Finset.univ \ {cycD.toFun ib', y, cycD.toFun ib})) (S y) (S (cycD.toFun m)) ∧
      0 < orient2D (w (Finset.univ \ {cycD.toFun ib', y, cycD.toFun ib})) (S (cycD.toFun m)) (S (cycD.toFun ib))) :
    InteriorAnchorGoal P S w D cycD y ib' iu0 iv0 ib := by
  refine ⟨y, cycD.toFun ib, _, Or.inr (Or.inl ⟨rfl, rfl, rfl⟩), hgap, ?_⟩
  refine good_gap_of_all_cross hPoly h25 hgap (fun p hp => ?_)
  rcases (Finset.mem_filter.mp hp).2 with ⟨mp, rfl, hm1, hm2⟩
  have hmp_b' : mp ≠ ib' := fun h => by rw [h, sub_self, Fin.val_zero] at hm1; omega
  have hmp_b : mp ≠ ib := fun h => by rw [h] at hm2; omega
  have hmO : cycD.toFun mp ∉ ({cycD.toFun ib', y, cycD.toFun ib} : Finset (Fin n)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rintro (h | h | h)
    · exact hmp_b' (cycD.inj h)
    · exact hy_notD (h ▸ ccwCycle_mem cycD mp)
    · exact hmp_b (cycD.inj h)
  have hmB : cycD.toFun mp ∈ hullVertices S :=
    (Finset.mem_sdiff.mp (by rw [← hDB]; exact ccwCycle_mem cycD mp)).1
  have ho := hp_ord mp hm1 hm2
  have hpu : 0 < orient2D (S (cycD.toFun iu0)) (S (cycD.toFun mp)) (S (cycD.toFun ib)) := by
    have ⟨_, h_pos1⟩ := fin_sub_split_lt hord1 (lt_of_lt_of_le hord2 hm1)
    have ⟨_, _⟩ := fin_sub_split_lt hord1 (lt_trans hord2 hord3)
    exact ccwCycle_ccw3 cycD h_pos1 (by omega)
  have hpv : 0 ≤ orient2D (S (cycD.toFun iv0)) (S (cycD.toFun mp)) (S (cycD.toFun ib)) := by
    by_cases hmv : mp = iv0
    · rw [hmv, orient2D_self_left]
    · have hgt : (iv0 - ib').val < (mp - ib').val :=
        lt_of_le_of_ne hm1 (fun h => hmv (sub_left_inj.mp (Fin.ext h)).symm)
      have ⟨hs1, hp1⟩ := fin_sub_split_lt (lt_trans hord1 hord2) hgt
      have ⟨hs2, _⟩ := fin_sub_split_lt (lt_trans hord1 hord2) hord3
      exact le_of_lt (ccwCycle_ccw3 cycD hp1 (by omega))
  exact ⟨fun h => hy_notD (h ▸ ccwCycle_mem cycD mp), cycD.inj.ne hmp_b, hmO, hmB,
    segmentsCross_inIntTri_right hy_tri ho.1 ho.2 hyb hpu hpv⟩

private lemma interior_anchor_buildMid {n kD : ℕ} {P : Set (ℝ × ℝ)}
    {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ}
    (hPoly : ShatteredSimplePolygon P S w) (h25 : Sec2To5Interface P S w)
    {D : Finset (Fin n)} (hDB : D = hullVertices S \ certifiedVertices S w)
    (cycD : CCWCycle S D kD) {y : Fin n} (hy_notD : y ∉ D)
    {ib' iu0 iv0 ib : Fin (kD + 3)}
    (hgap : GoodAnchorPair P S w {cycD.toFun ib', y, cycD.toFun ib} (cycD.toFun ib) (cycD.toFun ib'))
    (hbb' : 0 < orient2D (w (Finset.univ \ {cycD.toFun ib', y, cycD.toFun ib})) (S (cycD.toFun ib)) (S (cycD.toFun ib')))
    (hp_ord : ∀ m : Fin (kD + 3), 0 < (m - ib).val → (m - ib).val < (ib' - ib).val →
      0 < orient2D (w (Finset.univ \ {cycD.toFun ib', y, cycD.toFun ib})) (S (cycD.toFun ib)) (S (cycD.toFun m)) ∧
      0 < orient2D (w (Finset.univ \ {cycD.toFun ib', y, cycD.toFun ib})) (S (cycD.toFun m)) (S (cycD.toFun ib'))) :
    InteriorAnchorGoal P S w D cycD y ib' iu0 iv0 ib := by
  refine ⟨cycD.toFun ib, cycD.toFun ib', _, Or.inr (Or.inr ⟨rfl, rfl, rfl⟩), hgap, ?_⟩
  refine good_gap_of_all_cross hPoly h25 hgap (fun p hp => ?_)
  rcases (Finset.mem_filter.mp hp).2 with ⟨mp, rfl, hm1, hm2⟩
  have hmp_b : mp ≠ ib := fun h => by rw [h, sub_self, Fin.val_zero] at hm1; omega
  have hmp_b' : mp ≠ ib' := fun h => by rw [h] at hm2; omega
  have hmO : cycD.toFun mp ∉ ({cycD.toFun ib', y, cycD.toFun ib} : Finset (Fin n)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rintro (h | h | h)
    · exact hmp_b' (cycD.inj h)
    · exact hy_notD (h ▸ ccwCycle_mem cycD mp)
    · exact hmp_b (cycD.inj h)
  have hmB : cycD.toFun mp ∈ hullVertices S :=
    (Finset.mem_sdiff.mp (by rw [← hDB]; exact ccwCycle_mem cycD mp)).1
  have ho := hp_ord mp hm1 hm2
  exact ⟨cycD.inj.ne hmp_b, cycD.inj.ne hmp_b', hmO, hmB,
    segmentsCross_gapMid_of_convex ho.1 ho.2 hbb' (ccwCycle_ccw3 cycD hm1 hm2)⟩

private lemma interior_anchor_caseA_L {n kD : ℕ} {P : Set (ℝ × ℝ)}
    {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ}
    (hPoly : ShatteredSimplePolygon P S w) (h25 : Sec2To5Interface P S w)
    {D : Finset (Fin n)} (hDB : D = hullVertices S \ certifiedVertices S w)
    (cycD : CCWCycle S D kD) {y : Fin n} (hy_notD : y ∉ D)
    {ib' iu0 iv0 ib id_v : Fin (kD + 3)}
    (hord1 : 0 < (iu0 - ib').val) (hord2 : (iu0 - ib').val < (iv0 - ib').val)
    (hord3 : (iv0 - ib').val < (ib - ib').val) (hord4 : (ib - ib').val < (id_v - ib').val)
    (hy_tri : InIntTri (w (Finset.univ \ {cycD.toFun ib', y, cycD.toFun ib})) (S (cycD.toFun iu0)) (S (cycD.toFun iv0)) (S y))
    (hv_noncol : ∀ i j : Fin (kD + 3), i ≠ j →
      orient2D (S (cycD.toFun i)) (S (cycD.toFun j)) (w (Finset.univ \ {cycD.toFun ib', y, cycD.toFun ib})) ≠ 0)
    (hvq_D : ∀ i : Fin (kD + 3),
      orient2D (w (Finset.univ \ {cycD.toFun ib', y, cycD.toFun ib})) (w Finset.univ) (S (cycD.toFun i)) ≠ 0)
    (hvq_y : orient2D (w (Finset.univ \ {cycD.toFun ib', y, cycD.toFun ib})) (w Finset.univ) (S y) ≠ 0)
    (hv_noncol_y : ∀ x : Fin n, x ≠ y →
      orient2D (w (Finset.univ \ {cycD.toFun ib', y, cycD.toFun ib})) (S y) (S x) ≠ 0)
    (h_seen_ss : ∀ a b : Fin n, a ∉ ({cycD.toFun ib', y, cycD.toFun ib} : Finset (Fin n)) →
      b ∉ ({cycD.toFun ib', y, cycD.toFun ib} : Finset (Fin n)) →
      ¬ Sees P (w (Finset.univ \ {cycD.toFun ib', y, cycD.toFun ib})) (w Finset.univ) →
      OnSameSide (w (Finset.univ \ {cycD.toFun ib', y, cycD.toFun ib})) (w Finset.univ) (S a) (S b))
    (hy_cone_pos :
      0 < orient2D (w (Finset.univ \ {cycD.toFun ib', y, cycD.toFun ib})) (S (cycD.toFun iu0)) (S y) ∧
      0 < orient2D (w (Finset.univ \ {cycD.toFun ib', y, cycD.toFun ib})) (S y) (S (cycD.toFun iv0)) ∧
      0 < orient2D (w (Finset.univ \ {cycD.toFun ib', y, cycD.toFun ib})) (S (cycD.toFun iu0)) (S (cycD.toFun iv0)))
    (hy_orient_to_uv : ∀ x : ℝ × ℝ,
      0 < orient2D (w (Finset.univ \ {cycD.toFun ib', y, cycD.toFun ib})) (S (cycD.toFun iu0)) x →
      0 < orient2D (w (Finset.univ \ {cycD.toFun ib', y, cycD.toFun ib})) (S (cycD.toFun iv0)) x →
      0 < orient2D (w (Finset.univ \ {cycD.toFun ib', y, cycD.toFun ib})) (S y) x)
    (e_start e_end : Fin (kD + 3))
    (hiu0_far : (iu0 - e_end).val ≤ (e_start - e_end).val)
    (hs1 : (e_start - ib').val < (iu0 - ib').val)
    (h_u0_not_es : iu0 ≠ e_start)
    (h_ang : ∀ a b : Fin (kD + 3), (a - e_end).val < (b - e_end).val →
      (b - e_end).val ≤ (e_start - e_end).val →
      0 < orient2D (w (Finset.univ \ {cycD.toFun ib', y, cycD.toFun ib})) (S (cycD.toFun a)) (S (cycD.toFun b))) :
    InteriorAnchorGoal P S w D cycD y ib' iu0 iv0 ib := by
  let b' := cycD.toFun ib'
  let u0 := cycD.toFun iu0
  let v0 := cycD.toFun iv0
  let b := cycD.toFun ib
  let O_star : Finset (Fin n) := {b', y, b}
  let v := w (Finset.univ \ O_star)
  let q := w Finset.univ
  have hb'_ne_u0 : ib' ≠ iu0 := fun h => by rw [h, sub_self, Fin.val_zero] at hord1; omega
  have hb'_ne_v0 : ib' ≠ iv0 := fun h => by rw [h, sub_self, Fin.val_zero] at hord2; omega
  have hb'_ne_b : ib' ≠ ib := fun h => by rw [h, sub_self, Fin.val_zero] at hord3; omega
  have hb'_ne_d : ib' ≠ id_v := fun h => by rw [h, sub_self, Fin.val_zero] at hord4; omega
  have hu0_ne_b : iu0 ≠ ib := fun h => by rw [h] at hord2; omega
  have hv0_ne_b : iv0 ≠ ib := fun h => by rw [h] at hord3; omega
  have hb_ne_d : ib ≠ id_v := fun h => by rw [h] at hord4; omega
  have hb_ne_y : b ≠ y := fun h => hy_notD (h ▸ ccwCycle_mem cycD ib)
  have hb'_O : b' ∈ O_star := Finset.mem_insert_self _ _
  have hy_O : y ∈ O_star := Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  have hb_O : b ∈ O_star := Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  have hm_out : ∀ {m : Fin (kD + 3)}, m ≠ ib' → m ≠ ib → cycD.toFun m ∉ O_star := by
    intro m hm1 hm2 hmO
    simp only [O_star, Finset.mem_insert, Finset.mem_singleton] at hmO
    rcases hmO with h | h | h
    · exact hm1 (cycD.inj h)
    · exact hy_notD (h ▸ ccwCycle_mem cycD m)
    · exact hm2 (cycD.inj h)
  have h_le_es : (ib' - iu0).val ≤ (e_start - iu0).val := by
    by_cases hsb' : e_start = ib'
    · rw [hsb']
    · have hsp := fin_sub_split_le (le_of_lt hs1)
      have hc1 := fin_sub_add_compl h_u0_not_es.symm
      have hc2 := fin_sub_add_compl hb'_ne_u0.symm
      omega
  obtain ⟨_, h_sub⟩ := facing_arc_subchain_order cycD v e_start e_end h_ang hiu0_far h_le_es
  have hc_v0 : (iv0 - iu0).val < (ib - iu0).val := by
    have := fin_sub_split_lt hord1 hord2
    have := fin_sub_split_lt hord1 (lt_trans hord2 hord3)
    omega
  have hc_b : (ib - iu0).val < (id_v - iu0).val := by
    have := fin_sub_split_lt hord1 (lt_trans hord2 hord3)
    have := fin_sub_split_lt hord1 (lt_trans hord2 (lt_trans hord3 hord4))
    omega
  have hc_d : (id_v - iu0).val < (ib' - iu0).val := by
    have := fin_sub_split_lt hord1 (lt_trans hord2 (lt_trans hord3 hord4))
    have := fin_sub_add_compl hb'_ne_u0
    have := fin_sub_add_compl hb'_ne_d
    omega
  have hu0_pos : (iu0 - iu0).val < (ib - iu0).val := by
    rw [sub_self, Fin.val_zero]; exact Nat.pos_of_ne_zero (fun h => hu0_ne_b (sub_eq_zero.mp (Fin.ext h)).symm)
  have hu0_b := h_sub iu0 ib hu0_pos (le_of_lt (lt_trans hc_b hc_d))
  have hv0_b := h_sub iv0 ib hc_v0 (le_of_lt (lt_trans hc_b hc_d))
  have hb_d := h_sub ib id_v hc_b (le_of_lt hc_d)
  have hb_b' := h_sub ib ib' (lt_trans hc_b hc_d) le_rfl
  have hu0_d := h_sub iu0 id_v (by rw [sub_self, Fin.val_zero]; omega) (le_of_lt hc_d)
  have hv0_d := h_sub iv0 id_v (lt_trans hc_v0 hc_b) (le_of_lt hc_d)
  have hu0_b' := h_sub iu0 ib' (by rw [sub_self, Fin.val_zero]; exact Nat.pos_of_ne_zero (fun h => hb'_ne_u0 (sub_eq_zero.mp (Fin.ext h)))) le_rfl
  have hv0_b' := h_sub iv0 ib' (lt_trans hc_v0 (lt_trans hc_b hc_d)) le_rfl
  have hy_b : 0 < orient2D v (S y) (S b) := hy_orient_to_uv (S b) hu0_b hv0_b
  have hy_b' : 0 < orient2D v (S y) (S b') := hy_orient_to_uv (S b') hu0_b' hv0_b'
  have h_gapR_ord : ∀ m : Fin (kD + 3), (iv0 - ib').val ≤ (m - ib').val → (m - ib').val < (ib - ib').val →
      0 < orient2D v (S y) (S (cycD.toFun m)) ∧ 0 < orient2D v (S (cycD.toFun m)) (S b) := by
    intro m hm1 hm2
    have hm_val : (m - iu0).val = (m - ib').val - (iu0 - ib').val := by
      have h1 : m - iu0 = (m - ib') - (iu0 - ib') := by abel
      rw [h1, fin_val_sub_eq, if_pos (Fin.le_def.mpr (le_trans (le_of_lt hord2) hm1))]
    have hb_val : (ib - iu0).val = (ib - ib').val - (iu0 - ib').val := by
      have h1 : ib - iu0 = (ib - ib') - (iu0 - ib') := by abel
      rw [h1, fin_val_sub_eq, if_pos (Fin.le_def.mpr (le_of_lt (lt_trans hord2 hord3)))]
    have hv0_val : (iv0 - iu0).val = (iv0 - ib').val - (iu0 - ib').val := by
      have h1 : iv0 - iu0 = (iv0 - ib') - (iu0 - ib') := by abel
      rw [h1, fin_val_sub_eq, if_pos (Fin.le_def.mpr (le_of_lt hord2))]
    refine ⟨?_, h_sub m ib (by omega) (le_of_lt (lt_trans hc_b hc_d))⟩
    by_cases hmv : m = iv0
    · rw [hmv]; exact hy_cone_pos.2.1
    · have hmv_lt : (iv0 - ib').val < (m - ib').val :=
        lt_of_le_of_ne hm1 (fun h => hmv (sub_left_inj.mp (Fin.ext h)).symm)
      have hm_pos : (iu0 - iu0).val < (m - iu0).val := by rw [sub_self, Fin.val_zero]; omega
      have hvm_lt : (iv0 - iu0).val < (m - iu0).val := by omega
      have hm_le : (m - iu0).val ≤ (ib' - iu0).val := le_of_lt (lt_trans (by omega) (lt_trans hc_b hc_d))
      exact hy_orient_to_uv _ (h_sub iu0 m hm_pos hm_le) (h_sub iv0 m hvm_lt hm_le)
  by_cases hsee : Sees P v q
  · rcases three_missed_in_cone_pigeonhole v q (S y) (S b) (S b')
      hvq_y (hvq_D ib) (hvq_D ib') hy_b hb_b' hy_b' with hss_yb | hss_bb'
    · exact interior_anchor_buildR hPoly h25 hDB cycD hy_notD hy_tri hord1 hord2 hord3
        (goodAnchorPair_of_see hy_O hb_O hb_ne_y.symm hsee hss_yb (fun h => hv_noncol_y b hb_ne_y h))
        hy_b h_gapR_ord
    · refine interior_anchor_buildMid hPoly h25 hDB cycD hy_notD
        (goodAnchorPair_of_see hb_O hb'_O (cycD.inj.ne hb'_ne_b).symm hsee hss_bb' (ne_of_gt hb_b'))
        hb_b' (fun m hm1 hm2 => ?_)
      have h_ib'_split : (ib' - ib).val + (ib - iu0).val = (ib' - iu0).val :=
        fin_sub_split_le (le_of_lt (lt_trans hc_b hc_d))
      have hm_lt : (m - iu0).val = (ib - iu0).val + (m - ib).val := by
        have h1 : m - iu0 = (m - ib) + (ib - iu0) := by abel
        have hlt_tot := (ib' - iu0).isLt
        have hlt : (m - ib).val + (ib - iu0).val < kD + 3 := by omega
        rw [h1, Fin.val_add, Nat.mod_eq_of_lt hlt]; omega
      exact ⟨h_sub ib m (by omega) (by omega), h_sub m ib' (by omega) le_rfl⟩
  · have hss_u0_v0 := h_seen_ss u0 v0 (hm_out hb'_ne_u0.symm hu0_ne_b) (hm_out hb'_ne_v0.symm hv0_ne_b) hsee
    have hss_u0_d := h_seen_ss u0 (cycD.toFun id_v) (hm_out hb'_ne_u0.symm hu0_ne_b) (hm_out hb'_ne_d.symm hb_ne_d.symm) hsee
    have hy_same_u0 : OnSameSide v q (S u0) (S y) := by
      rcases hy_tri with ⟨_, _, _, _, hm2, hm3, hs, hy1, hy2⟩
      have hid := orient2D_convex_comb3 v q v (S u0) (S v0) (S y) _ _ _ hs hy1 hy2
      rw [orient2D_self_outer, mul_zero, zero_add] at hid
      unfold OnSameSide at hss_u0_v0 ⊢
      rcases lt_or_gt_of_ne (hvq_D iu0) with hqn | hqp
      · have hvp : orient2D v q (S v0) < 0 := by nlinarith only [hss_u0_v0, hqn]
        have hyp : orient2D v q (S y) < 0 := by rw [hid]; nlinarith only [hm2, hm3, hqn, hvp]
        exact mul_pos_of_neg_of_neg hqn hyp
      · have hvp : 0 < orient2D v q (S v0) := by nlinarith only [hss_u0_v0, hqp]
        have hyp : 0 < orient2D v q (S y) := by rw [hid]; nlinarith only [hm2, hm3, hqp, hvp]
        exact mul_pos hqp hyp
    have hb_same_u0 : OnSameSide v q (S u0) (S b) := by
      unfold OnSameSide at hss_u0_d ⊢
      have hid := orient2D_angle_trans_id v q (S u0) (S b) (S (cycD.toFun id_v))
      rcases lt_or_gt_of_ne (hvq_D iu0) with hqn | hqp
      · have hdn : orient2D v q (S (cycD.toFun id_v)) < 0 := by nlinarith only [hss_u0_d, hqn]
        by_contra hnot
        have hbp : 0 < orient2D v q (S b) := lt_of_le_of_ne (by
          by_contra hlt; exact hnot (mul_pos_of_neg_of_neg hqn (not_le.mp hlt))) (hvq_D ib).symm
        nlinarith only [hid, mul_pos hbp hu0_d, mul_neg_of_neg_of_pos hqn hb_d,
          mul_neg_of_neg_of_pos hdn hu0_b]
      · have hdp : 0 < orient2D v q (S (cycD.toFun id_v)) := by nlinarith only [hss_u0_d, hqp]
        by_contra hnot
        have hbn : orient2D v q (S b) < 0 := lt_of_le_of_ne (by
          by_contra hlt; exact hnot (mul_pos hqp (not_le.mp hlt))) (hvq_D ib)
        nlinarith only [hid, mul_neg_of_neg_of_pos hbn hu0_d, mul_pos hqp hb_d, mul_pos hdp hu0_b]
    have hss_yb : OnSameSide v q (S y) (S b) := hy_same_u0.symm.trans hb_same_u0
    exact interior_anchor_buildR hPoly h25 hDB cycD hy_notD hy_tri hord1 hord2 hord3
      (goodAnchorPair_of_cone_ends hy_O hb_O hb_ne_y.symm hss_yb hy_b
        (fun hqy => ⟨u0, hm_out hb'_ne_u0.symm hu0_ne_b,
          by unfold OnSameSide at hy_same_u0; nlinarith only [hy_same_u0, hqy], hy_cone_pos.1⟩)
        (fun hqy => ⟨cycD.toFun id_v, hm_out hb'_ne_d.symm hb_ne_d.symm,
          by unfold OnSameSide at hss_u0_d hy_same_u0; nlinarith only [hss_u0_d, hy_same_u0, hqy], hb_d⟩))
      hy_b h_gapR_ord

private lemma interior_anchor_caseA_R {n kD : ℕ} {P : Set (ℝ × ℝ)}
    {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ}
    (hPoly : ShatteredSimplePolygon P S w) (h25 : Sec2To5Interface P S w)
    {D : Finset (Fin n)} (hDB : D = hullVertices S \ certifiedVertices S w)
    (cycD : CCWCycle S D kD) {y : Fin n} (hy_notD : y ∉ D)
    {ib' iu0 iv0 ib id_v : Fin (kD + 3)}
    (hord1 : 0 < (iu0 - ib').val) (hord2 : (iu0 - ib').val < (iv0 - ib').val)
    (hord3 : (iv0 - ib').val < (ib - ib').val) (hord4 : (ib - ib').val < (id_v - ib').val)
    (hy_tri : InIntTri (w (Finset.univ \ {cycD.toFun ib', y, cycD.toFun ib})) (S (cycD.toFun iu0)) (S (cycD.toFun iv0)) (S y))
    (hv_noncol : ∀ i j : Fin (kD + 3), i ≠ j →
      orient2D (S (cycD.toFun i)) (S (cycD.toFun j)) (w (Finset.univ \ {cycD.toFun ib', y, cycD.toFun ib})) ≠ 0)
    (hvq_D : ∀ i : Fin (kD + 3),
      orient2D (w (Finset.univ \ {cycD.toFun ib', y, cycD.toFun ib})) (w Finset.univ) (S (cycD.toFun i)) ≠ 0)
    (hvq_y : orient2D (w (Finset.univ \ {cycD.toFun ib', y, cycD.toFun ib})) (w Finset.univ) (S y) ≠ 0)
    (hv_noncol_y : ∀ x : Fin n, x ≠ y →
      orient2D (w (Finset.univ \ {cycD.toFun ib', y, cycD.toFun ib})) (S y) (S x) ≠ 0)
    (h_seen_ss : ∀ a b : Fin n, a ∉ ({cycD.toFun ib', y, cycD.toFun ib} : Finset (Fin n)) →
      b ∉ ({cycD.toFun ib', y, cycD.toFun ib} : Finset (Fin n)) →
      ¬ Sees P (w (Finset.univ \ {cycD.toFun ib', y, cycD.toFun ib})) (w Finset.univ) →
      OnSameSide (w (Finset.univ \ {cycD.toFun ib', y, cycD.toFun ib})) (w Finset.univ) (S a) (S b))
    (hy_cone_pos :
      0 < orient2D (w (Finset.univ \ {cycD.toFun ib', y, cycD.toFun ib})) (S (cycD.toFun iu0)) (S y) ∧
      0 < orient2D (w (Finset.univ \ {cycD.toFun ib', y, cycD.toFun ib})) (S y) (S (cycD.toFun iv0)) ∧
      0 < orient2D (w (Finset.univ \ {cycD.toFun ib', y, cycD.toFun ib})) (S (cycD.toFun iu0)) (S (cycD.toFun iv0)))
    (hy_orient_from_uv : ∀ x : ℝ × ℝ,
      0 < orient2D (w (Finset.univ \ {cycD.toFun ib', y, cycD.toFun ib})) x (S (cycD.toFun iu0)) →
      0 < orient2D (w (Finset.univ \ {cycD.toFun ib', y, cycD.toFun ib})) x (S (cycD.toFun iv0)) →
      0 < orient2D (w (Finset.univ \ {cycD.toFun ib', y, cycD.toFun ib})) x (S y))
    (e_start e_end : Fin (kD + 3))
    (hib_far : (ib - e_end).val ≤ (e_start - e_end).val)
    (hs1 : (iv0 - ib').val ≤ (e_start - ib').val) (hs2 : (e_start - ib').val < (ib - ib').val)
    (h_ang : ∀ a b : Fin (kD + 3), (a - e_end).val < (b - e_end).val →
      (b - e_end).val ≤ (e_start - e_end).val →
      0 < orient2D (w (Finset.univ \ {cycD.toFun ib', y, cycD.toFun ib})) (S (cycD.toFun a)) (S (cycD.toFun b))) :
    InteriorAnchorGoal P S w D cycD y ib' iu0 iv0 ib := by
  let b' := cycD.toFun ib'
  let u0 := cycD.toFun iu0
  let v0 := cycD.toFun iv0
  let b := cycD.toFun ib
  let O_star : Finset (Fin n) := {b', y, b}
  let v := w (Finset.univ \ O_star)
  let q := w Finset.univ
  have hb'_ne_u0 : ib' ≠ iu0 := fun h => by rw [h, sub_self, Fin.val_zero] at hord1; omega
  have hb'_ne_v0 : ib' ≠ iv0 := fun h => by rw [h, sub_self, Fin.val_zero] at hord2; omega
  have hb'_ne_b : ib' ≠ ib := fun h => by rw [h, sub_self, Fin.val_zero] at hord3; omega
  have hb'_ne_d : ib' ≠ id_v := fun h => by rw [h, sub_self, Fin.val_zero] at hord4; omega
  have hu0_ne_b : iu0 ≠ ib := fun h => by rw [h] at hord2; omega
  have hv0_ne_b : iv0 ≠ ib := fun h => by rw [h] at hord3; omega
  have hb_ne_d : ib ≠ id_v := fun h => by rw [h] at hord4; omega
  have hb'_ne_y : b' ≠ y := fun h => hy_notD (h ▸ ccwCycle_mem cycD ib')
  have hb'_O : b' ∈ O_star := Finset.mem_insert_self _ _
  have hy_O : y ∈ O_star := Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  have hb_O : b ∈ O_star := Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  have hm_out : ∀ {m : Fin (kD + 3)}, m ≠ ib' → m ≠ ib → cycD.toFun m ∉ O_star := by
    intro m hm1 hm2 hmO
    simp only [O_star, Finset.mem_insert, Finset.mem_singleton] at hmO
    rcases hmO with h | h | h
    · exact hm1 (cycD.inj h)
    · exact hy_notD (h ▸ ccwCycle_mem cycD m)
    · exact hm2 (cycD.inj h)
  have h_le_es : (iv0 - ib).val ≤ (e_start - ib).val := by
    have hib_nes : ib ≠ e_start := fun h => by rw [← h] at hs2; omega
    have hsp1 := fin_sub_split_le (le_of_lt hs2)
    have hsp2 := fin_sub_split_le (le_trans hs1 (le_of_lt hs2))
    have hc1 := fin_sub_add_compl hib_nes.symm
    have hc2 := fin_sub_add_compl hv0_ne_b
    omega
  obtain ⟨_, h_sub⟩ := facing_arc_subchain_order cycD v e_start e_end h_ang hib_far h_le_es
  have hc_d : (id_v - ib).val < (ib' - ib).val := by
    have := fin_sub_split_lt (lt_trans hord1 (lt_trans hord2 hord3)) hord4
    have := fin_sub_add_compl hb'_ne_b
    omega
  have hc_b' : (ib' - ib).val < (iu0 - ib).val := by
    have := fin_sub_add_compl hb'_ne_b
    have := fin_sub_add_compl hu0_ne_b
    have := fin_sub_split_lt hord1 (lt_trans hord2 hord3)
    omega
  have hc_u0 : (iu0 - ib).val < (iv0 - ib).val := by
    have := fin_sub_add_compl hu0_ne_b
    have := fin_sub_add_compl hv0_ne_b
    have := fin_sub_split_lt hord1 hord2
    have := fin_sub_split_lt hord1 (lt_trans hord2 hord3)
    have := fin_sub_split_lt (lt_trans hord1 hord2) hord3
    omega
  have hd_pos : (ib - ib).val < (id_v - ib).val := by
    rw [sub_self, Fin.val_zero]; exact Nat.pos_of_ne_zero (fun h => hb_ne_d (sub_eq_zero.mp (Fin.ext h)).symm)
  have hb_d := h_sub ib id_v hd_pos (le_of_lt (lt_trans hc_d (lt_trans hc_b' hc_u0)))
  have hd_b' := h_sub id_v ib' hc_d (le_of_lt (lt_trans hc_b' hc_u0))
  have hb_b' := h_sub ib ib' (lt_trans hd_pos hc_d) (le_of_lt (lt_trans hc_b' hc_u0))
  have hb'_u0 := h_sub ib' iu0 hc_b' (le_of_lt hc_u0)
  have hb'_v0 := h_sub ib' iv0 (lt_trans hc_b' hc_u0) le_rfl
  have hd_u0 := h_sub id_v iu0 (lt_trans hc_d hc_b') (le_of_lt hc_u0)
  have hd_v0 := h_sub id_v iv0 (lt_trans hc_d (lt_trans hc_b' hc_u0)) le_rfl
  have hb'_y : 0 < orient2D v (S b') (S y) := hy_orient_from_uv (S b') hb'_u0 hb'_v0
  have hb_y : 0 < orient2D v (S b) (S y) := hy_orient_from_uv (S b)
    (h_sub ib iu0 (lt_trans (lt_trans hd_pos hc_d) hc_b') (le_of_lt hc_u0))
    (h_sub ib iv0 (lt_trans (lt_trans hd_pos hc_d) (lt_trans hc_b' hc_u0)) le_rfl)
  have h_gapL_ord : ∀ m : Fin (kD + 3), 0 < (m - ib').val → (m - ib').val ≤ (iu0 - ib').val →
      0 < orient2D v (S b') (S (cycD.toFun m)) ∧ 0 < orient2D v (S (cycD.toFun m)) (S y) := by
    intro m hm1 hm2
    have hm_val : (m - ib).val = (ib' - ib).val + (m - ib').val := by
      have h1 : m - ib = (m - ib') + (ib' - ib) := by abel
      have hc := fin_sub_add_compl hb'_ne_b
      have hlt : (m - ib').val + (ib' - ib).val < kD + 3 := by omega
      rw [h1, Fin.val_add, Nat.mod_eq_of_lt hlt]; omega
    have hu0_val : (iu0 - ib).val = (ib' - ib).val + (iu0 - ib').val := by
      have h1 : iu0 - ib = (iu0 - ib') + (ib' - ib) := by abel
      have hc := fin_sub_add_compl hb'_ne_b
      have hlt : (iu0 - ib').val + (ib' - ib).val < kD + 3 := by omega
      rw [h1, Fin.val_add, Nat.mod_eq_of_lt hlt]; omega
    refine ⟨h_sub ib' m (by omega) (by omega), ?_⟩
    by_cases hmu : m = iu0
    · rw [hmu]; exact hy_cone_pos.1
    · have hmu_lt : (m - ib').val < (iu0 - ib').val := lt_of_le_of_ne hm2 (fun h => hmu (sub_left_inj.mp (Fin.ext h)))
      exact hy_orient_from_uv _ (h_sub m iu0 (by omega) (le_of_lt hc_u0)) (h_sub m iv0 (by omega) le_rfl)
  by_cases hsee : Sees P v q
  · rcases three_missed_in_cone_pigeonhole v q (S b) (S b') (S y)
      (hvq_D ib) (hvq_D ib') hvq_y hb_b' hb'_y hb_y with hss_bb' | hss_b'y
    · refine interior_anchor_buildMid hPoly h25 hDB cycD hy_notD
        (goodAnchorPair_of_see hb_O hb'_O (cycD.inj.ne hb'_ne_b).symm hsee hss_bb' (ne_of_gt hb_b'))
        hb_b' (fun m hm1 hm2 => ?_)
      have hm_le : (m - ib).val < (ib' - ib).val := hm2
      exact ⟨h_sub ib m (by simpa using hm1) (le_of_lt (lt_trans hm_le (lt_trans hc_b' hc_u0))),
        h_sub m ib' hm_le (le_of_lt (lt_trans hc_b' hc_u0))⟩
    · exact interior_anchor_buildL hPoly h25 hDB cycD hy_notD (lt_trans hord2 hord3) hy_tri hord2
        (goodAnchorPair_of_see hb'_O hy_O hb'_ne_y hsee hss_b'y (fun h => hv_noncol_y b' hb'_ne_y (by
          unfold orient2D at h ⊢; linarith)))
        hb'_y h_gapL_ord
  · have hss_d_v0 := h_seen_ss (cycD.toFun id_v) v0 (hm_out hb'_ne_d.symm hb_ne_d.symm)
      (hm_out hb'_ne_v0.symm hv0_ne_b) hsee
    have hss_u0_v0 := h_seen_ss u0 v0 (hm_out hb'_ne_u0.symm hu0_ne_b) (hm_out hb'_ne_v0.symm hv0_ne_b) hsee
    have hb'_same_v0 : OnSameSide v q (S b') (S v0) := by
      unfold OnSameSide at hss_d_v0 ⊢
      have hid := orient2D_angle_trans_id v q (S (cycD.toFun id_v)) (S b') (S v0)
      rcases lt_or_gt_of_ne (hvq_D iv0) with hqn | hqp
      · have hdn : orient2D v q (S (cycD.toFun id_v)) < 0 := by nlinarith only [hss_d_v0, hqn]
        by_contra hnot
        have hb'p : 0 < orient2D v q (S b') := lt_of_le_of_ne (by
          by_contra hlt; exact hnot (mul_pos_of_neg_of_neg (not_le.mp hlt) hqn)) (hvq_D ib').symm
        nlinarith only [hid, mul_pos hb'p hd_v0, mul_neg_of_neg_of_pos hdn hb'_v0,
          mul_neg_of_neg_of_pos hqn hd_b']
      · have hdp : 0 < orient2D v q (S (cycD.toFun id_v)) := by nlinarith only [hss_d_v0, hqp]
        by_contra hnot
        have hb'n : orient2D v q (S b') < 0 := lt_of_le_of_ne (by
          by_contra hlt; exact hnot (mul_pos (not_le.mp hlt) hqp)) (hvq_D ib')
        nlinarith only [hid, mul_neg_of_neg_of_pos hb'n hd_v0, mul_pos hdp hb'_v0, mul_pos hqp hd_b']
    have hy_same_v0 : OnSameSide v q (S y) (S v0) := by
      rcases hy_tri with ⟨_, _, _, _, hm2, hm3, hs, hy1, hy2⟩
      have hid := orient2D_convex_comb3 v q v (S u0) (S v0) (S y) _ _ _ hs hy1 hy2
      rw [orient2D_self_outer, mul_zero, zero_add] at hid
      unfold OnSameSide at hss_u0_v0 ⊢
      rcases lt_or_gt_of_ne (hvq_D iv0) with hqn | hqp
      · have hun : orient2D v q (S u0) < 0 := by nlinarith only [hss_u0_v0, hqn]
        have hyn : orient2D v q (S y) < 0 := by rw [hid]; nlinarith only [hm2, hm3, hun, hqn]
        exact mul_pos_of_neg_of_neg hyn hqn
      · have hup : 0 < orient2D v q (S u0) := by nlinarith only [hss_u0_v0, hqp]
        have hyp : 0 < orient2D v q (S y) := by rw [hid]; nlinarith only [hm2, hm3, hup, hqp]
        exact mul_pos hyp hqp
    have hss_b'y : OnSameSide v q (S b') (S y) := hb'_same_v0.trans hy_same_v0.symm
    exact interior_anchor_buildL hPoly h25 hDB cycD hy_notD (lt_trans hord2 hord3) hy_tri hord2
      (goodAnchorPair_of_cone_ends hb'_O hy_O hb'_ne_y hss_b'y hb'_y
        (fun hqb' => ⟨cycD.toFun id_v, hm_out hb'_ne_d.symm hb_ne_d.symm,
          by unfold OnSameSide at hss_d_v0 hb'_same_v0; nlinarith only [hss_d_v0, hb'_same_v0, hqb'], hd_b'⟩)
        (fun hqb' => ⟨v0, hm_out hb'_ne_v0.symm hv0_ne_b,
          by unfold OnSameSide at hb'_same_v0; nlinarith only [hb'_same_v0, hqb'], hy_cone_pos.2.1⟩))
      hb'_y h_gapL_ord

private lemma interior_anchor_caseA_Mid {n kD : ℕ} {P : Set (ℝ × ℝ)}
    {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ}
    (hPoly : ShatteredSimplePolygon P S w) (h25 : Sec2To5Interface P S w)
    {D : Finset (Fin n)} (hDB : D = hullVertices S \ certifiedVertices S w)
    (cycD : CCWCycle S D kD) {y : Fin n} (hy_notD : y ∉ D)
    {ib' iu0 iv0 ib id_v : Fin (kD + 3)}
    (hord1 : 0 < (iu0 - ib').val) (hord2 : (iu0 - ib').val < (iv0 - ib').val)
    (hord3 : (iv0 - ib').val < (ib - ib').val) (hord4 : (ib - ib').val < (id_v - ib').val)
    (hy_tri : InIntTri (w (Finset.univ \ {cycD.toFun ib', y, cycD.toFun ib})) (S (cycD.toFun iu0)) (S (cycD.toFun iv0)) (S y))
    (hv_noncol : ∀ i j : Fin (kD + 3), i ≠ j →
      orient2D (S (cycD.toFun i)) (S (cycD.toFun j)) (w (Finset.univ \ {cycD.toFun ib', y, cycD.toFun ib})) ≠ 0)
    (hvq_D : ∀ i : Fin (kD + 3),
      orient2D (w (Finset.univ \ {cycD.toFun ib', y, cycD.toFun ib})) (w Finset.univ) (S (cycD.toFun i)) ≠ 0)
    (hvq_y : orient2D (w (Finset.univ \ {cycD.toFun ib', y, cycD.toFun ib})) (w Finset.univ) (S y) ≠ 0)
    (hv_noncol_y : ∀ x : Fin n, x ≠ y →
      orient2D (w (Finset.univ \ {cycD.toFun ib', y, cycD.toFun ib})) (S y) (S x) ≠ 0)
    (h_seen_ss : ∀ a b : Fin n, a ∉ ({cycD.toFun ib', y, cycD.toFun ib} : Finset (Fin n)) →
      b ∉ ({cycD.toFun ib', y, cycD.toFun ib} : Finset (Fin n)) →
      ¬ Sees P (w (Finset.univ \ {cycD.toFun ib', y, cycD.toFun ib})) (w Finset.univ) →
      OnSameSide (w (Finset.univ \ {cycD.toFun ib', y, cycD.toFun ib})) (w Finset.univ) (S a) (S b))
    (hy_cone_pos :
      0 < orient2D (w (Finset.univ \ {cycD.toFun ib', y, cycD.toFun ib})) (S (cycD.toFun iu0)) (S y) ∧
      0 < orient2D (w (Finset.univ \ {cycD.toFun ib', y, cycD.toFun ib})) (S y) (S (cycD.toFun iv0)) ∧
      0 < orient2D (w (Finset.univ \ {cycD.toFun ib', y, cycD.toFun ib})) (S (cycD.toFun iu0)) (S (cycD.toFun iv0)))
    (hy_orient_from_uv : ∀ x : ℝ × ℝ,
      0 < orient2D (w (Finset.univ \ {cycD.toFun ib', y, cycD.toFun ib})) x (S (cycD.toFun iu0)) →
      0 < orient2D (w (Finset.univ \ {cycD.toFun ib', y, cycD.toFun ib})) x (S (cycD.toFun iv0)) →
      0 < orient2D (w (Finset.univ \ {cycD.toFun ib', y, cycD.toFun ib})) x (S y))
    (hy_orient_to_uv : ∀ x : ℝ × ℝ,
      0 < orient2D (w (Finset.univ \ {cycD.toFun ib', y, cycD.toFun ib})) (S (cycD.toFun iu0)) x →
      0 < orient2D (w (Finset.univ \ {cycD.toFun ib', y, cycD.toFun ib})) (S (cycD.toFun iv0)) x →
      0 < orient2D (w (Finset.univ \ {cycD.toFun ib', y, cycD.toFun ib})) (S y) x)
    (e_start e_end : Fin (kD + 3))
    (hib'_far : (ib' - e_end).val ≤ (e_start - e_end).val)
    (hs1 : (ib - ib').val ≤ (e_start - ib').val)
    (h_ang : ∀ a b : Fin (kD + 3), (a - e_end).val < (b - e_end).val →
      (b - e_end).val ≤ (e_start - e_end).val →
      0 < orient2D (w (Finset.univ \ {cycD.toFun ib', y, cycD.toFun ib})) (S (cycD.toFun a)) (S (cycD.toFun b))) :
    InteriorAnchorGoal P S w D cycD y ib' iu0 iv0 ib := by
  let b' := cycD.toFun ib'
  let u0 := cycD.toFun iu0
  let v0 := cycD.toFun iv0
  let b := cycD.toFun ib
  let O_star : Finset (Fin n) := {b', y, b}
  let v := w (Finset.univ \ O_star)
  let q := w Finset.univ
  have hb'_ne_u0 : ib' ≠ iu0 := fun h => by rw [h, sub_self, Fin.val_zero] at hord1; omega
  have hb'_ne_v0 : ib' ≠ iv0 := fun h => by rw [h, sub_self, Fin.val_zero] at hord2; omega
  have hb'_ne_b : ib' ≠ ib := fun h => by rw [h, sub_self, Fin.val_zero] at hord3; omega
  have hb'_ne_d : ib' ≠ id_v := fun h => by rw [h, sub_self, Fin.val_zero] at hord4; omega
  have hu0_ne_b : iu0 ≠ ib := fun h => by rw [h] at hord2; omega
  have hv0_ne_b : iv0 ≠ ib := fun h => by rw [h] at hord3; omega
  have hb_ne_d : ib ≠ id_v := fun h => by rw [h] at hord4; omega
  have hu0_ne_d : iu0 ≠ id_v := fun h => by rw [h] at hord2; omega
  have hv0_ne_d : iv0 ≠ id_v := fun h => by rw [h] at hord3; omega
  have hb'_ne_y : b' ≠ y := fun h => hy_notD (h ▸ ccwCycle_mem cycD ib')
  have hb_ne_y : b ≠ y := fun h => hy_notD (h ▸ ccwCycle_mem cycD ib)
  have hb'D : b' ∈ D := ccwCycle_mem cycD ib'
  have hbD : b ∈ D := ccwCycle_mem cycD ib
  have hdD : cycD.toFun id_v ∈ D := ccwCycle_mem cycD id_v
  have hb'_O : b' ∈ O_star := Finset.mem_insert_self _ _
  have hy_O : y ∈ O_star := Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  have hb_O : b ∈ O_star := Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  have hm_out : ∀ {m : Fin (kD + 3)}, m ≠ ib' → m ≠ ib → cycD.toFun m ∉ O_star := by
    intro m hm1 hm2 hmO
    simp only [O_star, Finset.mem_insert, Finset.mem_singleton] at hmO
    rcases hmO with h | h | h
    · exact hm1 (cycD.inj h)
    · exact hy_notD (h ▸ ccwCycle_mem cycD m)
    · exact hm2 (cycD.inj h)
  obtain ⟨_, h_sub⟩ := facing_arc_subchain_order cycD v e_start e_end h_ang hib'_far hs1
  have hb'_u0 := h_sub ib' iu0 (by simpa using hord1) (le_of_lt (lt_trans hord2 hord3))
  have hb'_v0 := h_sub ib' iv0 (by simpa using lt_trans hord1 hord2) (le_of_lt hord3)
  have hb'_b := h_sub ib' ib (by simpa using lt_trans hord1 (lt_trans hord2 hord3)) le_rfl
  have hu0_b := h_sub iu0 ib (lt_trans hord2 hord3) le_rfl
  have hv0_b := h_sub iv0 ib hord3 le_rfl
  have hb'_y : 0 < orient2D v (S b') (S y) := hy_orient_from_uv (S b') hb'_u0 hb'_v0
  have hy_b : 0 < orient2D v (S y) (S b) := hy_orient_to_uv (S b) hu0_b hv0_b
  have h_gapL_ord : ∀ m : Fin (kD + 3), 0 < (m - ib').val → (m - ib').val ≤ (iu0 - ib').val →
      0 < orient2D v (S b') (S (cycD.toFun m)) ∧ 0 < orient2D v (S (cycD.toFun m)) (S y) := by
    intro m hm1 hm2
    refine ⟨h_sub ib' m (by simpa using hm1) (le_trans hm2 (le_of_lt (lt_trans hord2 hord3))), ?_⟩
    by_cases hmu : m = iu0
    · rw [hmu]; exact hy_cone_pos.1
    · have hmu_lt : (m - ib').val < (iu0 - ib').val := lt_of_le_of_ne hm2 (fun h => hmu (sub_left_inj.mp (Fin.ext h)))
      exact hy_orient_from_uv _ (h_sub m iu0 hmu_lt (le_of_lt (lt_trans hord2 hord3)))
        (h_sub m iv0 (lt_trans hmu_lt hord2) (le_of_lt hord3))
  have h_gapR_ord : ∀ m : Fin (kD + 3), (iv0 - ib').val ≤ (m - ib').val → (m - ib').val < (ib - ib').val →
      0 < orient2D v (S y) (S (cycD.toFun m)) ∧ 0 < orient2D v (S (cycD.toFun m)) (S b) := by
    intro m hm1 hm2
    refine ⟨?_, h_sub m ib hm2 le_rfl⟩
    by_cases hmv : m = iv0
    · rw [hmv]; exact hy_cone_pos.2.1
    · have hmv_lt : (iv0 - ib').val < (m - ib').val := lt_of_le_of_ne hm1 (fun h => hmv (sub_left_inj.mp (Fin.ext h)).symm)
      exact hy_orient_to_uv _ (h_sub iu0 m (lt_trans hord2 hmv_lt) (le_of_lt hm2))
        (h_sub iv0 m hmv_lt (le_of_lt hm2))
  by_cases hsee : Sees P v q
  · rcases three_missed_in_cone_pigeonhole v q (S b') (S y) (S b)
      (hvq_D ib') hvq_y (hvq_D ib) hb'_y hy_b hb'_b with hss_b'y | hss_yb
    · exact interior_anchor_buildL hPoly h25 hDB cycD hy_notD (lt_trans hord2 hord3) hy_tri hord2
        (goodAnchorPair_of_see hb'_O hy_O hb'_ne_y hsee hss_b'y (fun h => hv_noncol_y b' hb'_ne_y (by
          unfold orient2D at h ⊢; linarith)))
        hb'_y h_gapL_ord
    · exact interior_anchor_buildR hPoly h25 hDB cycD hy_notD hy_tri hord1 hord2 hord3
        (goodAnchorPair_of_see hy_O hb_O hb_ne_y.symm hsee hss_yb (fun h => hv_noncol_y b hb_ne_y h))
        hy_b h_gapR_ord
  · have hss_u0_v0 := h_seen_ss u0 v0 (hm_out hb'_ne_u0.symm hu0_ne_b) (hm_out hb'_ne_v0.symm hv0_ne_b) hsee
    have hss_u0_d := h_seen_ss u0 (cycD.toFun id_v) (hm_out hb'_ne_u0.symm hu0_ne_b) (hm_out hb'_ne_d.symm hb_ne_d.symm) hsee
    have hy_same_u0 : OnSameSide v q (S u0) (S y) := by
      rcases hy_tri with ⟨_, _, _, _, hm2, hm3, hs, hy1, hy2⟩
      have hid := orient2D_convex_comb3 v q v (S u0) (S v0) (S y) _ _ _ hs hy1 hy2
      rw [orient2D_self_outer, mul_zero, zero_add] at hid
      unfold OnSameSide at hss_u0_v0 ⊢
      rcases lt_or_gt_of_ne (hvq_D iu0) with hqn | hqp
      · have hvp : orient2D v q (S v0) < 0 := by nlinarith only [hss_u0_v0, hqn]
        have hyp : orient2D v q (S y) < 0 := by rw [hid]; nlinarith only [hm2, hm3, hqn, hvp]
        exact mul_pos_of_neg_of_neg hqn hyp
      · have hvp : 0 < orient2D v q (S v0) := by nlinarith only [hss_u0_v0, hqp]
        have hyp : 0 < orient2D v q (S y) := by rw [hid]; nlinarith only [hm2, hm3, hqp, hvp]
        exact mul_pos hqp hyp
    have ho1 : 0 < orient2D (S b') (S b) (S (cycD.toFun id_v)) :=
      ccwCycle_ccw3 cycD (lt_trans hord1 (lt_trans hord2 hord3)) hord4
    have ho2 : orient2D (S b') (S b) (S u0) < 0 := by
      have hcc := ccwCycle_ccw3 cycD hord1 (lt_trans hord2 hord3)
      unfold orient2D at hcc ⊢; linarith
    have ho3 : orient2D (S u0) (S (cycD.toFun id_v)) (S b) < 0 := by
      have ⟨hs1, hp1⟩ := fin_sub_split_lt hord1 (lt_trans hord2 hord3)
      have ⟨hs2, _⟩ := fin_sub_split_lt hord1 (lt_trans hord2 (lt_trans hord3 hord4))
      have hcc : 0 < orient2D (S u0) (S b) (S (cycD.toFun id_v)) := ccwCycle_ccw3 cycD hp1 (by omega)
      unfold orient2D at hcc ⊢; linarith
    have ho4 : 0 < orient2D (S u0) (S (cycD.toFun id_v)) (S b') := by
      have ⟨hs2, hp2⟩ := fin_sub_split_lt hord1 (lt_trans hord2 (lt_trans hord3 hord4))
      have h1 := fin_sub_add_compl hu0_ne_d
      have h2 := fin_sub_add_compl hb'_ne_u0
      have hlt_d := (id_v - ib').isLt
      have hcc : 0 < orient2D (S u0) (S (cycD.toFun id_v)) (S b') :=
        ccwCycle_ccw3 cycD hp2 (by omega : (id_v - iu0).val < (ib' - iu0).val)
      unfold orient2D at hcc ⊢; linarith
    have hb'_or_b_ss : OnSameSide v q (S u0) (S b') ∨ OnSameSide v q (S u0) (S b) := by
      have hfc := (fourgon_diag_cramer v q (S u0) (S (cycD.toFun id_v)) (S b') (S b)).1
      by_contra hnot; push Not at hnot; unfold OnSameSide at hnot
      have hbn1 : orient2D v q (S u0) * orient2D v q (S b') < 0 := lt_of_le_of_ne (not_lt.mp hnot.1) (mul_ne_zero (hvq_D iu0) (hvq_D ib'))
      have hbn2 : orient2D v q (S u0) * orient2D v q (S b) < 0 := lt_of_le_of_ne (not_lt.mp hnot.2) (mul_ne_zero (hvq_D iu0) (hvq_D ib))
      unfold OnSameSide at hss_u0_d
      rcases lt_or_gt_of_ne (hvq_D iu0) with hqn | hqp
      · have hdn : orient2D v q (S (cycD.toFun id_v)) < 0 := by nlinarith only [hss_u0_d, hqn]
        have hb'p : 0 < orient2D v q (S b') := by nlinarith only [hbn1, hqn]
        have hbp : 0 < orient2D v q (S b) := by nlinarith only [hbn2, hqn]
        nlinarith only [hfc, ho1, ho2, ho3, ho4, hqn, hdn, hb'p, hbp]
      · have hdp : 0 < orient2D v q (S (cycD.toFun id_v)) := by nlinarith only [hss_u0_d, hqp]
        have hb'n : orient2D v q (S b') < 0 := by nlinarith only [hbn1, hqp]
        have hbn : orient2D v q (S b) < 0 := by nlinarith only [hbn2, hqp]
        nlinarith only [hfc, ho1, ho2, ho3, ho4, hqp, hdp, hb'n, hbn]
    by_cases hb'_ss : OnSameSide v q (S u0) (S b')
    · by_cases hb_ss : OnSameSide v q (S u0) (S b)
      · have hss_b'y : OnSameSide v q (S b') (S y) := hb'_ss.symm.trans hy_same_u0
        have hss_yb : OnSameSide v q (S y) (S b) := hy_same_u0.symm.trans hb_ss
        rcases lt_or_gt_of_ne (hvq_D iu0) with hqn | hqp
        · exact interior_anchor_buildL hPoly h25 hDB cycD hy_notD (lt_trans hord2 hord3) hy_tri hord2
            (goodAnchorPair_of_cone_ends hb'_O hy_O hb'_ne_y hss_b'y hb'_y
              (fun h => False.elim (by unfold OnSameSide at hb'_ss; nlinarith only [hb'_ss, hqn, h]))
              (fun _ => ⟨v0, hm_out hb'_ne_v0.symm hv0_ne_b,
                by unfold OnSameSide at hss_u0_v0; nlinarith only [hss_u0_v0, hqn], hy_cone_pos.2.1⟩))
            hb'_y h_gapL_ord
        · exact interior_anchor_buildR hPoly h25 hDB cycD hy_notD hy_tri hord1 hord2 hord3
            (goodAnchorPair_of_cone_ends hy_O hb_O hb_ne_y.symm hss_yb hy_b
              (fun _ => ⟨u0, hm_out hb'_ne_u0.symm hu0_ne_b, hqp, hy_cone_pos.1⟩)
              (fun h => False.elim (by unfold OnSameSide at hy_same_u0; nlinarith only [hy_same_u0, hqp, h])))
            hy_b h_gapR_ord
      · have hss_b'y : OnSameSide v q (S b') (S y) := hb'_ss.symm.trans hy_same_u0
        have hb_opp : orient2D v q (S u0) * orient2D v q (S b) < 0 := lt_of_le_of_ne (by unfold OnSameSide at hb_ss; exact not_lt.mp hb_ss) (mul_ne_zero (hvq_D iu0) (hvq_D ib))
        refine interior_anchor_buildL hPoly h25 hDB cycD hy_notD (lt_trans hord2 hord3) hy_tri hord2
          (goodAnchorPair_of_cone_ends hb'_O hy_O hb'_ne_y hss_b'y hb'_y
            (fun hqb' => by
              have hqu0 : 0 < orient2D v q (S u0) := by unfold OnSameSide at hb'_ss; nlinarith only [hb'_ss, hqb']
              have hqd : 0 < orient2D v q (S (cycD.toFun id_v)) := by unfold OnSameSide at hss_u0_d; nlinarith only [hss_u0_d, hqu0]
              have hqb : orient2D v q (S b) < 0 := by nlinarith only [hb_opp, hqu0]
              by_cases hdb' : 0 < orient2D v (S (cycD.toFun id_v)) (S b')
              · exact ⟨cycD.toFun id_v, hm_out hb'_ne_d.symm hb_ne_d.symm, hqd, hdb'⟩
              · exfalso
                have hb'd : 0 < orient2D v (S b') (S (cycD.toFun id_v)) := by
                  have h1 := not_lt.mp hdb'
                  have hne := hv_noncol ib' id_v hb'_ne_d
                  exact lt_of_le_of_ne (by unfold orient2D at h1 ⊢; linarith)
                    (fun h => hne (by unfold orient2D at h ⊢; linarith))
                by_cases hdb : 0 < orient2D v (S (cycD.toFun id_v)) (S b)
                · have hb'bv : 0 < orient2D v (S b') (S b) := by
                    have hid := orient2D_barycentric_sum (S b') (S b) (S (cycD.toFun id_v)) v
                    unfold orient2D at hid hdb hb'd ho1 ⊢; linarith
                  have hd_tri : InIntTri v (S b') (S b) (S (cycD.toFun id_v)) := by
                    rw [inIntTri_iff_orient_pos hb'bv]
                    exact ⟨hb'd, ho1, by unfold orient2D at hdb ⊢; linarith⟩
                  have hq_ccw : 0 < orient2D q (S b') (S b) := by
                    have hid : orient2D q (S b') (S b) = orient2D v (S b') (S b) + orient2D v q (S b') - orient2D v q (S b) := by
                      unfold orient2D; ring
                    linarith
                  have hv_tri : InIntTri q (S b') (S b) v := by
                    rw [inIntTri_iff_orient_pos hq_ccw]
                    exact ⟨by unfold orient2D at hqb' ⊢; linarith,
                      by unfold orient2D at hb'bv ⊢; linarith,
                      by unfold orient2D at hqb ⊢; linarith⟩
                  exact contradict_cert_even_front hPoly h25 (by rw [← hDB]; exact hdD)
                    (Finset.mem_sdiff.mp (by rw [← hDB]; exact hb'D)).1
                    (Finset.mem_sdiff.mp (by rw [← hDB]; exact hbD)).1
                    (cycD.inj.ne hb'_ne_d) (cycD.inj.ne hb_ne_d) (cycD.inj.ne hb'_ne_b)
                    (hm_out hb'_ne_d.symm hb_ne_d.symm) hsee hd_tri hv_tri
                · have hbd : 0 < orient2D v (S b) (S (cycD.toFun id_v)) := by
                    have h1 := not_lt.mp hdb
                    have hne := hv_noncol ib id_v hb_ne_d
                    exact lt_of_le_of_ne (by unfold orient2D at h1 ⊢; linarith)
                      (fun h => hne (by unfold orient2D at h ⊢; linarith))
                  have hfc := (fourgon_diag_cramer v q (S v0) (S (cycD.toFun id_v)) (S b') (S b)).2
                  have ho2' : orient2D (S b') (S b) (S v0) < 0 := by
                    have hcc := ccwCycle_ccw3 cycD (lt_trans hord1 hord2) hord3
                    unfold orient2D at hcc ⊢; linarith
                  have ho3' : orient2D (S v0) (S (cycD.toFun id_v)) (S b) < 0 := by
                    have ⟨hs1, hp1⟩ := fin_sub_split_lt (lt_trans hord1 hord2) hord3
                    have ⟨hs2, _⟩ := fin_sub_split_lt (lt_trans hord1 hord2) (lt_trans hord3 hord4)
                    have hcc : 0 < orient2D (S v0) (S b) (S (cycD.toFun id_v)) := ccwCycle_ccw3 cycD hp1 (by omega)
                    unfold orient2D at hcc ⊢; linarith
                  have ho4' : 0 < orient2D (S v0) (S (cycD.toFun id_v)) (S b') := by
                    have ⟨hs2, hp2⟩ := fin_sub_split_lt (lt_trans hord1 hord2) (lt_trans hord3 hord4)
                    have h1 := fin_sub_add_compl hv0_ne_d
                    have h2 := fin_sub_add_compl hb'_ne_v0
                    have hlt_d := (id_v - ib').isLt
                    have hcc : 0 < orient2D (S v0) (S (cycD.toFun id_v)) (S b') :=
                      ccwCycle_ccw3 cycD hp2 (by omega : (id_v - iv0).val < (ib' - iv0).val)
                    unfold orient2D at hcc ⊢; linarith
                  have hv0d : 0 < orient2D v (S v0) (S (cycD.toFun id_v)) := by
                    have hdb'1 : orient2D v (S (cycD.toFun id_v)) (S b') < 0 := by unfold orient2D at hb'd ⊢; linarith
                    have hdb1 : orient2D v (S (cycD.toFun id_v)) (S b) < 0 := by unfold orient2D at hbd ⊢; linarith
                    have hrhs : orient2D (S b') (S b) (S (cycD.toFun id_v)) * orient2D v (S (cycD.toFun id_v)) (S v0) < 0 := by
                      rw [hfc]
                      nlinarith only [ho2', ho3', ho4', hdb'1, hdb1, orient2D_self_right v (S (cycD.toFun id_v))]
                    have hn : orient2D v (S (cycD.toFun id_v)) (S v0) < 0 := by nlinarith only [ho1, hrhs]
                    unfold orient2D at hn ⊢; linarith
                  have hid_tr := orient2D_angle_trans_id v q (S v0) (S (cycD.toFun id_v)) (S b)
                  have hqv0 : 0 < orient2D v q (S v0) := by unfold OnSameSide at hss_u0_v0; nlinarith only [hss_u0_v0, hqu0]
                  have hL := mul_pos hqd hv0_b
                  have hR1 : orient2D v q (S v0) * orient2D v (S (cycD.toFun id_v)) (S b) < 0 :=
                    mul_neg_of_pos_of_neg hqv0 (by unfold orient2D at hbd ⊢; linarith)
                  have hR2 : orient2D v q (S b) * orient2D v (S v0) (S (cycD.toFun id_v)) < 0 :=
                    mul_neg_of_neg_of_pos hqb hv0d
                  linarith)
            (fun hqb' => ⟨v0, hm_out hb'_ne_v0.symm hv0_ne_b,
              by unfold OnSameSide at hss_u0_v0 hb'_ss; nlinarith only [hss_u0_v0, hb'_ss, hqb'], hy_cone_pos.2.1⟩))
          hb'_y h_gapL_ord
    · have hb_ss' : OnSameSide v q (S u0) (S b) := hb'_or_b_ss.resolve_left hb'_ss
      have hss_yb : OnSameSide v q (S y) (S b) := hy_same_u0.symm.trans hb_ss'
      have hb'_opp : orient2D v q (S u0) * orient2D v q (S b') < 0 := lt_of_le_of_ne (by unfold OnSameSide at hb'_ss; exact not_lt.mp hb'_ss) (mul_ne_zero (hvq_D iu0) (hvq_D ib'))
      refine interior_anchor_buildR hPoly h25 hDB cycD hy_notD hy_tri hord1 hord2 hord3
        (goodAnchorPair_of_cone_ends hy_O hb_O hb_ne_y.symm hss_yb hy_b
          (fun hqy => ⟨u0, hm_out hb'_ne_u0.symm hu0_ne_b,
            by unfold OnSameSide at hy_same_u0; nlinarith only [hy_same_u0, hqy], hy_cone_pos.1⟩)
          (fun hqy => by
            have hqu0 : orient2D v q (S u0) < 0 := by unfold OnSameSide at hy_same_u0; nlinarith only [hy_same_u0, hqy]
            have hqd : orient2D v q (S (cycD.toFun id_v)) < 0 := by unfold OnSameSide at hss_u0_d; nlinarith only [hss_u0_d, hqu0]
            have hqb : orient2D v q (S b) < 0 := by unfold OnSameSide at hb_ss'; nlinarith only [hb_ss', hqu0]
            have hqb' : 0 < orient2D v q (S b') := by nlinarith only [hb'_opp, hqu0]
            by_cases hbd : 0 < orient2D v (S b) (S (cycD.toFun id_v))
            · exact ⟨cycD.toFun id_v, hm_out hb'_ne_d.symm hb_ne_d.symm, hqd, hbd⟩
            · exfalso
              have hdb : 0 < orient2D v (S (cycD.toFun id_v)) (S b) := by
                have h1 := not_lt.mp hbd
                have hne := hv_noncol ib id_v hb_ne_d
                exact lt_of_le_of_ne (by unfold orient2D at h1 ⊢; linarith)
                  (fun h => hne (by unfold orient2D at h ⊢; linarith))
              by_cases hb'd : 0 < orient2D v (S b') (S (cycD.toFun id_v))
              · have hb'bv : 0 < orient2D v (S b') (S b) := by
                  have hid := orient2D_barycentric_sum (S b') (S b) (S (cycD.toFun id_v)) v
                  unfold orient2D at hid hdb hb'd ho1 ⊢; linarith
                have hd_tri : InIntTri v (S b') (S b) (S (cycD.toFun id_v)) := by
                  rw [inIntTri_iff_orient_pos hb'bv]
                  exact ⟨hb'd, ho1, by unfold orient2D at hdb ⊢; linarith⟩
                have hq_ccw : 0 < orient2D q (S b') (S b) := by
                  have hid : orient2D q (S b') (S b) = orient2D v (S b') (S b) + orient2D v q (S b') - orient2D v q (S b) := by
                    unfold orient2D; ring
                  linarith
                have hv_tri : InIntTri q (S b') (S b) v := by
                  rw [inIntTri_iff_orient_pos hq_ccw]
                  exact ⟨by unfold orient2D at hqb' ⊢; linarith,
                    by unfold orient2D at hb'bv ⊢; linarith,
                    by unfold orient2D at hqb ⊢; linarith⟩
                exact contradict_cert_even_front hPoly h25 (by rw [← hDB]; exact hdD)
                  (Finset.mem_sdiff.mp (by rw [← hDB]; exact hb'D)).1
                  (Finset.mem_sdiff.mp (by rw [← hDB]; exact hbD)).1
                  (cycD.inj.ne hb'_ne_d) (cycD.inj.ne hb_ne_d) (cycD.inj.ne hb'_ne_b)
                  (hm_out hb'_ne_d.symm hb_ne_d.symm) hsee hd_tri hv_tri
              · have hdb' : 0 < orient2D v (S (cycD.toFun id_v)) (S b') := by
                  have h1 := not_lt.mp hb'd
                  have hne := hv_noncol ib' id_v hb'_ne_d
                  exact lt_of_le_of_ne (by unfold orient2D at h1 ⊢; linarith)
                    (fun h => hne (by unfold orient2D at h ⊢; linarith))
                have hfc := (fourgon_diag_cramer v q (S u0) (S (cycD.toFun id_v)) (S b') (S b)).2
                have hdu0 : 0 < orient2D v (S (cycD.toFun id_v)) (S u0) := by
                  have hlhs : 0 < orient2D (S b') (S b) (S (cycD.toFun id_v)) * orient2D v (S (cycD.toFun id_v)) (S u0) := by
                    rw [hfc]
                    nlinarith only [ho2, ho3, ho4, hdb', hdb, orient2D_self_right v (S (cycD.toFun id_v))]
                  nlinarith only [ho1, hlhs]
                have hid_tr := orient2D_angle_trans_id v q (S b') (S (cycD.toFun id_v)) (S u0)
                have hL : orient2D v q (S (cycD.toFun id_v)) * orient2D v (S b') (S u0) < 0 := mul_neg_of_neg_of_pos hqd hb'_u0
                have hR1 : 0 < orient2D v q (S b') * orient2D v (S (cycD.toFun id_v)) (S u0) := mul_pos hqb' hdu0
                have hR2 : 0 < orient2D v q (S u0) * orient2D v (S b') (S (cycD.toFun id_v)) :=
                  mul_pos_of_neg_of_neg hqu0 (by unfold orient2D at hdb' ⊢; linarith)
                linarith))
        hy_b h_gapR_ord

private lemma interior_anchor_caseB_see {n kD : ℕ} {P : Set (ℝ × ℝ)}
    {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ}
    (hPoly : ShatteredSimplePolygon P S w) (h25 : Sec2To5Interface P S w)
    {D : Finset (Fin n)} (hDB : D = hullVertices S \ certifiedVertices S w)
    (cycD : CCWCycle S D kD) {y : Fin n} (hy_notD : y ∉ D)
    {ib' iu0 iv0 ib : Fin (kD + 3)}
    (hord1 : 0 < (iu0 - ib').val) (hord2 : (iu0 - ib').val < (iv0 - ib').val)
    (hord3 : (iv0 - ib').val < (ib - ib').val)
    (hy_tri : InIntTri (w (Finset.univ \ {cycD.toFun ib', y, cycD.toFun ib})) (S (cycD.toFun iu0)) (S (cycD.toFun iv0)) (S y))
    (hv_noncol : ∀ i j : Fin (kD + 3), i ≠ j →
      orient2D (S (cycD.toFun i)) (S (cycD.toFun j)) (w (Finset.univ \ {cycD.toFun ib', y, cycD.toFun ib})) ≠ 0)
    (hvq_D : ∀ i : Fin (kD + 3),
      orient2D (w (Finset.univ \ {cycD.toFun ib', y, cycD.toFun ib})) (w Finset.univ) (S (cycD.toFun i)) ≠ 0)
    (hvq_y : orient2D (w (Finset.univ \ {cycD.toFun ib', y, cycD.toFun ib})) (w Finset.univ) (S y) ≠ 0)
    (hv_noncol_y : ∀ x : Fin n, x ≠ y →
      orient2D (w (Finset.univ \ {cycD.toFun ib', y, cycD.toFun ib})) (S y) (S x) ≠ 0)
    (hy_cone_pos :
      0 < orient2D (w (Finset.univ \ {cycD.toFun ib', y, cycD.toFun ib})) (S (cycD.toFun iu0)) (S y) ∧
      0 < orient2D (w (Finset.univ \ {cycD.toFun ib', y, cycD.toFun ib})) (S y) (S (cycD.toFun iv0)) ∧
      0 < orient2D (w (Finset.univ \ {cycD.toFun ib', y, cycD.toFun ib})) (S (cycD.toFun iu0)) (S (cycD.toFun iv0)))
    (hy_orient_from_uv : ∀ x : ℝ × ℝ,
      0 < orient2D (w (Finset.univ \ {cycD.toFun ib', y, cycD.toFun ib})) x (S (cycD.toFun iu0)) →
      0 < orient2D (w (Finset.univ \ {cycD.toFun ib', y, cycD.toFun ib})) x (S (cycD.toFun iv0)) →
      0 < orient2D (w (Finset.univ \ {cycD.toFun ib', y, cycD.toFun ib})) x (S y))
    (h_all_nf : ∀ m : Fin (kD + 3),
      0 < orient2D (S (cycD.toFun m)) (S (cycD.toFun (m + 1))) (w (Finset.univ \ {cycD.toFun ib', y, cycD.toFun ib})))
    (hsee : Sees P (w (Finset.univ \ {cycD.toFun ib', y, cycD.toFun ib})) (w Finset.univ)) :
    InteriorAnchorGoal P S w D cycD y ib' iu0 iv0 ib := by
  let b' := cycD.toFun ib'
  let u0 := cycD.toFun iu0
  let v0 := cycD.toFun iv0
  let b := cycD.toFun ib
  let O_star : Finset (Fin n) := {b', y, b}
  let v := w (Finset.univ \ O_star)
  let q := w Finset.univ
  have hb'_ne_u0 : ib' ≠ iu0 := fun h => by rw [h, sub_self, Fin.val_zero] at hord1; omega
  have hb'_ne_v0 : ib' ≠ iv0 := fun h => by rw [h, sub_self, Fin.val_zero] at hord2; omega
  have hb'_ne_b : ib' ≠ ib := fun h => by rw [h, sub_self, Fin.val_zero] at hord3; omega
  have hu0_ne_b : iu0 ≠ ib := fun h => by rw [h] at hord2; omega
  have hv0_ne_b : iv0 ≠ ib := fun h => by rw [h] at hord3; omega
  have hb'_ne_y : b' ≠ y := fun h => hy_notD (h ▸ ccwCycle_mem cycD ib')
  have hb_ne_y : b ≠ y := fun h => hy_notD (h ▸ ccwCycle_mem cycD ib)
  have hb'_O : b' ∈ O_star := Finset.mem_insert_self _ _
  have hy_O : y ∈ O_star := Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  have hb_O : b ∈ O_star := Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  have ha1 : ∀ a b_ : Fin (kD + 3), a ≠ b_ → OnSameSide v q (S (cycD.toFun a)) (S (cycD.toFun b_)) →
      ((∀ t : ℕ, t ≤ (b_ - a).val → OnSameSide v q (S (cycD.toFun a)) (S (cycD.toFun (a + finNat (kD + 3) t)))) ∨
       (∀ t : ℕ, t ≤ (a - b_).val → OnSameSide v q (S (cycD.toFun a)) (S (cycD.toFun (b_ + finNat (kD + 3) t))))) := by
    intro a b_ hab hss
    rcases farChain_path_between cycD v q hv_noncol hvq_D a b_ hab hss
      (Or.inl (by simpa [sub_add_cancel] using h_all_nf (a - 1))) (Or.inl (by simpa [sub_add_cancel] using h_all_nf (b_ - 1))) with h1 | h2
    · exact Or.inl h1.2
    · exact Or.inr h2.2
  by_cases hss_b'b : OnSameSide v q (S b') (S b)
  · rcases ha1 ib' ib hb'_ne_b hss_b'b with hL | hR
    · have hord := farChain_all_nonfacing_lt_pi_subchain cycD v q h_all_nf ib' ib hb'_ne_b hL
      have hu0 := hord ib' iu0 (by rw [sub_self, Fin.val_zero]; exact hord1) (le_of_lt (lt_trans hord2 hord3))
      have hv0 := hord ib' iv0 (by rw [sub_self, Fin.val_zero]; exact lt_trans hord1 hord2) (le_of_lt hord3)
      have hb'y : 0 < orient2D v (S b') (S y) := hy_orient_from_uv (S b') hu0.1 hv0.1
      have hss_b'y : OnSameSide v q (S b') (S y) := by
        have hu_ss := hL (iu0 - ib').val (le_of_lt (lt_trans hord2 hord3))
        have hv_ss := hL (iv0 - ib').val (le_of_lt hord3)
        have htu : ib' + finNat (kD + 3) (iu0 - ib').val = iu0 := by
          have : finNat (kD + 3) (iu0 - ib').val = iu0 - ib' := by ext; exact Nat.mod_eq_of_lt (iu0 - ib').isLt
          rw [this, add_sub_cancel]
        have htv : ib' + finNat (kD + 3) (iv0 - ib').val = iv0 := by
          have : finNat (kD + 3) (iv0 - ib').val = iv0 - ib' := by ext; exact Nat.mod_eq_of_lt (iv0 - ib').isLt
          rw [this, add_sub_cancel]
        rw [htu] at hu_ss; rw [htv] at hv_ss
        rcases hy_tri with ⟨_, _, _, _, hm2, hm3, hs, hy1, hy2⟩
        have hid := orient2D_convex_comb3 v q v (S u0) (S v0) (S y) _ _ _ hs hy1 hy2
        rw [orient2D_self_outer, mul_zero, zero_add] at hid
        unfold OnSameSide at hu_ss hv_ss ⊢
        rcases lt_or_gt_of_ne (hvq_D ib') with hqn | hqp
        · have h1 : orient2D v q (S u0) < 0 := by nlinarith only [hu_ss, hqn]
          have h2 : orient2D v q (S v0) < 0 := by nlinarith only [hv_ss, hqn]
          have h3 : orient2D v q (S y) < 0 := by rw [hid]; nlinarith only [hm2, hm3, h1, h2]
          exact mul_pos_of_neg_of_neg hqn h3
        · have h1 : 0 < orient2D v q (S u0) := by nlinarith only [hu_ss, hqp]
          have h2 : 0 < orient2D v q (S v0) := by nlinarith only [hv_ss, hqp]
          have h3 : 0 < orient2D v q (S y) := by rw [hid]; nlinarith only [hm2, hm3, h1, h2]
          exact mul_pos hqp h3
      exact interior_anchor_buildL hPoly h25 hDB cycD hy_notD (lt_trans hord2 hord3) hy_tri hord2
        (goodAnchorPair_of_see hb'_O hy_O hb'_ne_y hsee hss_b'y (fun h => hv_noncol_y b' hb'_ne_y (by
          unfold orient2D at h ⊢; linarith)))
        hb'y (fun m hm1 hm2 => ⟨(hord ib' m (by rw [sub_self, Fin.val_zero]; exact hm1) (le_trans hm2 (le_of_lt (lt_trans hord2 hord3)))).1, by
          by_cases hmu : m = iu0
          · rw [hmu]; exact hy_cone_pos.1
          · have hmu_lt : (m - ib').val < (iu0 - ib').val := lt_of_le_of_ne hm2 (fun h => hmu (sub_left_inj.mp (Fin.ext h)))
            exact hy_orient_from_uv _ (hord m iu0 hmu_lt (le_of_lt (lt_trans hord2 hord3))).1
              (hord m iv0 (lt_trans hmu_lt hord2) (le_of_lt hord3)).1⟩)
    · have hord := farChain_all_nonfacing_lt_pi_subchain cycD v q h_all_nf ib ib' hb'_ne_b.symm
        (fun t ht => hss_b'b.symm.trans (hR t ht))
      have hbb' : 0 < orient2D v (S b) (S b') :=
        (hord ib ib' (by rw [sub_self, Fin.val_zero]; exact Nat.pos_of_ne_zero (fun h => hb'_ne_b (sub_eq_zero.mp (Fin.ext h)))) le_rfl).1
      exact interior_anchor_buildMid hPoly h25 hDB cycD hy_notD
        (goodAnchorPair_of_see hb_O hb'_O (cycD.inj.ne hb'_ne_b).symm hsee hss_b'b.symm (ne_of_gt hbb'))
        hbb' (fun m hm1 hm2 => ⟨(hord ib m (by simpa using hm1) (le_of_lt hm2)).1, (hord m ib' hm2 le_rfl).1⟩)
  · have h_not_opp : ¬ OnSameSide v q (S b') (S b) := hss_b'b
    have h_opp_b'b : orient2D v q (S b') * orient2D v q (S b) < 0 :=
      lt_of_le_of_ne (not_lt.mp h_not_opp) (mul_ne_zero (hvq_D ib') (hvq_D ib))
    by_cases hss_b'y : OnSameSide v q (S b') (S y)
    · have hb'u0_or_v0 : OnSameSide v q (S b') (S u0) ∨ OnSameSide v q (S b') (S v0) := by
        rcases hy_tri with ⟨_, _, _, _, hm2, hm3, hs, hy1, hy2⟩
        have hid := orient2D_convex_comb3 v q v (S u0) (S v0) (S y) _ _ _ hs hy1 hy2
        rw [orient2D_self_outer, mul_zero, zero_add] at hid
        unfold OnSameSide at hss_b'y ⊢
        by_contra hnot; push Not at hnot
        rcases lt_or_gt_of_ne (hvq_D ib') with hqn | hqp
        · have hy_n : orient2D v q (S y) < 0 := by nlinarith only [hss_b'y, hqn]
          have hu_nn : 0 ≤ orient2D v q (S u0) := by nlinarith only [hnot.1, hqn]
          have hv_nn : 0 ≤ orient2D v q (S v0) := by nlinarith only [hnot.2, hqn]
          linarith [hid, mul_nonneg (le_of_lt hm2) hu_nn, mul_nonneg (le_of_lt hm3) hv_nn]
        · have hy_p : 0 < orient2D v q (S y) := by nlinarith only [hss_b'y, hqp]
          have hu_np : orient2D v q (S u0) ≤ 0 := by nlinarith only [hnot.1, hqp]
          have hv_np : orient2D v q (S v0) ≤ 0 := by nlinarith only [hnot.2, hqp]
          linarith [hid, mul_nonpos_of_nonneg_of_nonpos (le_of_lt hm2) hu_np,
            mul_nonpos_of_nonneg_of_nonpos (le_of_lt hm3) hv_np]
      by_cases hss_u0 : OnSameSide v q (S b') (S u0)
      · rcases ha1 ib' iu0 hb'_ne_u0 hss_u0 with hL | hbad
        · have hord := farChain_all_nonfacing_lt_pi_subchain cycD v q h_all_nf ib' iu0 hb'_ne_u0 hL
          have hmy_all : ∀ m : Fin (kD + 3), (m - ib').val ≤ (iu0 - ib').val →
              0 < orient2D v (S (cycD.toFun m)) (S y) := by
            intro m hm
            by_cases hmu : m = iu0
            · rw [hmu]; exact hy_cone_pos.1
            · have hmu_lt : (m - ib').val < (iu0 - ib').val := lt_of_le_of_ne hm (fun h => hmu (sub_left_inj.mp (Fin.ext h)))
              have hmu_o := (hord m iu0 hmu_lt le_rfl).1
              have hmss : OnSameSide v q (S b') (S (cycD.toFun m)) := by
                have := hL (m - ib').val hm
                have htm : ib' + finNat (kD + 3) (m - ib').val = m := by
                  have : finNat (kD + 3) (m - ib').val = m - ib' := by ext; exact Nat.mod_eq_of_lt (m - ib').isLt
                  rw [this, add_sub_cancel]
                rwa [htm] at this
              have hid := orient2D_angle_trans_id v q (S (cycD.toFun m)) (S u0) (S y)
              unfold OnSameSide at hmss hss_u0 hss_b'y
              rcases lt_or_gt_of_ne (hvq_D ib') with hqn | hqp
              · have hqm : orient2D v q (S (cycD.toFun m)) < 0 := by nlinarith only [hmss, hqn]
                have hqu : orient2D v q (S u0) < 0 := by nlinarith only [hss_u0, hqn]
                have hqy : orient2D v q (S y) < 0 := by nlinarith only [hss_b'y, hqn]
                nlinarith only [hid, hqm, hqu, hqy, hmu_o, hy_cone_pos.1]
              · have hqm : 0 < orient2D v q (S (cycD.toFun m)) := by nlinarith only [hmss, hqp]
                have hqu : 0 < orient2D v q (S u0) := by nlinarith only [hss_u0, hqp]
                have hqy : 0 < orient2D v q (S y) := by nlinarith only [hss_b'y, hqp]
                nlinarith only [hid, hqm, hqu, hqy, hmu_o, hy_cone_pos.1]
          have hb'y := hmy_all ib' (by rw [sub_self, Fin.val_zero]; exact Nat.zero_le _)
          exact interior_anchor_buildL hPoly h25 hDB cycD hy_notD (lt_trans hord2 hord3) hy_tri hord2
            (goodAnchorPair_of_see hb'_O hy_O hb'_ne_y hsee hss_b'y (fun h => hv_noncol_y b' hb'_ne_y (by
              unfold orient2D at h ⊢; linarith)))
            hb'y (fun m hm1 hm2 => ⟨(hord ib' m (by rw [sub_self, Fin.val_zero]; exact hm1) hm2).1, hmy_all m hm2⟩)
        · exfalso
          have h_b_val : (ib - iu0).val ≤ (ib' - iu0).val := by
            have hc1 := fin_sub_add_compl hb'_ne_u0
            have := fin_sub_split_lt hord1 (lt_trans hord2 hord3)
            omega
          have hss_b := hbad (ib - iu0).val h_b_val
          have htb : iu0 + finNat (kD + 3) (ib - iu0).val = ib := by
            have : finNat (kD + 3) (ib - iu0).val = ib - iu0 := by ext; exact Nat.mod_eq_of_lt (ib - iu0).isLt
            rw [this, add_sub_cancel]
          rw [htb] at hss_b
          exact h_not_opp hss_b
      · have hss_v0 := hb'u0_or_v0.resolve_left hss_u0
        exfalso
        have hno_u0 : ¬ OnSameSide v q (S b') (S u0) := hss_u0
        rcases ha1 iv0 ib' hb'_ne_v0.symm hss_v0.symm with hL | hR
        · have h_b_val : (ib - iv0).val ≤ (ib' - iv0).val := by
            have hc1 := fin_sub_add_compl hb'_ne_v0
            have := fin_sub_split_lt (lt_trans hord1 hord2) hord3
            omega
          have hss_b := hL (ib - iv0).val h_b_val
          have htb : iv0 + finNat (kD + 3) (ib - iv0).val = ib := by
            have : finNat (kD + 3) (ib - iv0).val = ib - iv0 := by ext; exact Nat.mod_eq_of_lt (ib - iv0).isLt
            rw [this, add_sub_cancel]
          rw [htb] at hss_b
          exact h_not_opp (hss_v0.trans hss_b)
        · have hss_u0' := hR (iu0 - ib').val (le_of_lt hord2)
          have htu : ib' + finNat (kD + 3) (iu0 - ib').val = iu0 := by
            have : finNat (kD + 3) (iu0 - ib').val = iu0 - ib' := by ext; exact Nat.mod_eq_of_lt (iu0 - ib').isLt
            rw [this, add_sub_cancel]
          rw [htu] at hss_u0'
          exact hno_u0 (hss_v0.trans hss_u0')
    · have hss_yb : OnSameSide v q (S y) (S b) := by
        unfold OnSameSide at hss_b'y h_opp_b'b ⊢
        have hb'y_neg : orient2D v q (S b') * orient2D v q (S y) < 0 :=
          lt_of_le_of_ne (not_lt.mp hss_b'y) (mul_ne_zero (hvq_D ib') hvq_y)
        have hsq : 0 < orient2D v q (S b') ^ 2 := sq_pos_of_ne_zero (hvq_D ib')
        nlinarith only [hb'y_neg, h_opp_b'b, hsq]
      have hbu0_or_v0 : OnSameSide v q (S b) (S v0) ∨ OnSameSide v q (S b) (S u0) := by
        rcases hy_tri with ⟨_, _, _, _, hm2, hm3, hs, hy1, hy2⟩
        have hid := orient2D_convex_comb3 v q v (S u0) (S v0) (S y) _ _ _ hs hy1 hy2
        rw [orient2D_self_outer, mul_zero, zero_add] at hid
        unfold OnSameSide at hss_yb ⊢
        by_contra hnot; push Not at hnot
        rcases lt_or_gt_of_ne (hvq_D ib) with hqn | hqp
        · have hy_n : orient2D v q (S y) < 0 := by nlinarith only [hss_yb, hqn]
          have hv_nn : 0 ≤ orient2D v q (S v0) := by nlinarith only [hnot.1, hqn]
          have hu_nn : 0 ≤ orient2D v q (S u0) := by nlinarith only [hnot.2, hqn]
          linarith [hid, mul_nonneg (le_of_lt hm2) hu_nn, mul_nonneg (le_of_lt hm3) hv_nn]
        · have hy_p : 0 < orient2D v q (S y) := by nlinarith only [hss_yb, hqp]
          have hv_np : orient2D v q (S v0) ≤ 0 := by nlinarith only [hnot.1, hqp]
          have hu_np : orient2D v q (S u0) ≤ 0 := by nlinarith only [hnot.2, hqp]
          linarith [hid, mul_nonpos_of_nonneg_of_nonpos (le_of_lt hm2) hu_np,
            mul_nonpos_of_nonneg_of_nonpos (le_of_lt hm3) hv_np]
      by_cases hss_v0 : OnSameSide v q (S b) (S v0)
      · rcases ha1 iv0 ib hv0_ne_b hss_v0.symm with hL | hbad
        · have hord := farChain_all_nonfacing_lt_pi_subchain cycD v q h_all_nf iv0 ib hv0_ne_b hL
          have hym_all : ∀ m : Fin (kD + 3), (iv0 - ib').val ≤ (m - ib').val → (m - ib').val < (ib - ib').val →
              0 < orient2D v (S y) (S (cycD.toFun m)) ∧ 0 < orient2D v (S (cycD.toFun m)) (S b) := by
            intro m hm1 hm2
            have hs_m := fin_sub_split_le hm1
            have hs_b := fin_sub_split_le (le_of_lt hord3)
            have hm_v0 : (m - iv0).val ≤ (ib - iv0).val := by omega
            have hmb : (m - iv0).val < (ib - iv0).val := by omega
            refine ⟨?_, (hord m ib hmb le_rfl).1⟩
            by_cases hmv : m = iv0
            · rw [hmv]; exact hy_cone_pos.2.1
            · have hmv_pos : 0 < (m - iv0).val := Nat.pos_of_ne_zero (fun h => hmv (sub_eq_zero.mp (Fin.ext h)))
              have hv0m := (hord iv0 m (by rw [sub_self, Fin.val_zero]; exact hmv_pos) hm_v0).1
              have hmss : OnSameSide v q (S b) (S (cycD.toFun m)) := by
                have h1 := hL (m - iv0).val hm_v0
                have htm : iv0 + finNat (kD + 3) (m - iv0).val = m := by
                  have : finNat (kD + 3) (m - iv0).val = m - iv0 := by ext; exact Nat.mod_eq_of_lt (m - iv0).isLt
                  rw [this, add_sub_cancel]
                rw [htm] at h1; exact hss_v0.trans h1
              have hid := orient2D_angle_trans_id v q (S y) (S v0) (S (cycD.toFun m))
              unfold OnSameSide at hss_yb hss_v0 hmss
              rcases lt_or_gt_of_ne (hvq_D ib) with hqn | hqp
              · have hqv : orient2D v q (S v0) < 0 := by nlinarith only [hss_v0, hqn]
                have hqy : orient2D v q (S y) < 0 := by nlinarith only [hss_yb, hqn]
                have hqm : orient2D v q (S (cycD.toFun m)) < 0 := by nlinarith only [hmss, hqn]
                nlinarith only [hid, hqv, hqy, hqm, hv0m, hy_cone_pos.2.1]
              · have hqv : 0 < orient2D v q (S v0) := by nlinarith only [hss_v0, hqp]
                have hqy : 0 < orient2D v q (S y) := by nlinarith only [hss_yb, hqp]
                have hqm : 0 < orient2D v q (S (cycD.toFun m)) := by nlinarith only [hmss, hqp]
                nlinarith only [hid, hqv, hqy, hqm, hv0m, hy_cone_pos.2.1]
          have hyb : 0 < orient2D v (S y) (S b) := by
            have hv0b := (hord iv0 ib (by rw [sub_self, Fin.val_zero]; exact Nat.pos_of_ne_zero (fun h => hv0_ne_b (sub_eq_zero.mp (Fin.ext h)).symm)) le_rfl).1
            have hid := orient2D_angle_trans_id v q (S y) (S v0) (S b)
            unfold OnSameSide at hss_yb hss_v0
            rcases lt_or_gt_of_ne (hvq_D ib) with hqn | hqp
            · have hqv : orient2D v q (S v0) < 0 := by nlinarith only [hss_v0, hqn]
              have hqy : orient2D v q (S y) < 0 := by nlinarith only [hss_yb, hqn]
              nlinarith only [hid, hqn, hqv, hqy, hv0b, hy_cone_pos.2.1]
            · have hqv : 0 < orient2D v q (S v0) := by nlinarith only [hss_v0, hqp]
              have hqy : 0 < orient2D v q (S y) := by nlinarith only [hss_yb, hqp]
              nlinarith only [hid, hqp, hqv, hqy, hv0b, hy_cone_pos.2.1]
          exact interior_anchor_buildR hPoly h25 hDB cycD hy_notD hy_tri hord1 hord2 hord3
            (goodAnchorPair_of_see hy_O hb_O hb_ne_y.symm hsee hss_yb (fun h => hv_noncol_y b hb_ne_y h))
            hyb hym_all
        · exfalso
          have h_b'_val : (ib' - ib).val ≤ (iv0 - ib).val := by
            have hc1 := fin_sub_add_compl hv0_ne_b
            have hc2 := fin_sub_add_compl hb'_ne_b
            have := fin_sub_split_lt (lt_trans hord1 hord2) hord3
            omega
          have hss_b' := hbad (ib' - ib).val h_b'_val
          have htb' : ib + finNat (kD + 3) (ib' - ib).val = ib' := by
            have : finNat (kD + 3) (ib' - ib).val = ib' - ib := by ext; exact Nat.mod_eq_of_lt (ib' - ib).isLt
            rw [this, add_sub_cancel]
          rw [htb'] at hss_b'
          exact h_not_opp (hss_b'.symm.trans hss_v0.symm)
      · have hss_u0 := hbu0_or_v0.resolve_left hss_v0
        exfalso
        have hno_v0 : ¬ OnSameSide v q (S b) (S v0) := hss_v0
        rcases ha1 ib iu0 hu0_ne_b.symm hss_u0 with hL | hR
        · have h_b'_val : (ib' - ib).val ≤ (iu0 - ib).val := by
            have hc1 := fin_sub_add_compl hu0_ne_b
            have hc2 := fin_sub_add_compl hb'_ne_b
            have := fin_sub_split_lt hord1 (lt_trans hord2 hord3)
            omega
          have hss_b' := hL (ib' - ib).val h_b'_val
          have htb' : ib + finNat (kD + 3) (ib' - ib).val = ib' := by
            have : finNat (kD + 3) (ib' - ib).val = ib' - ib := by ext; exact Nat.mod_eq_of_lt (ib' - ib).isLt
            rw [this, add_sub_cancel]
          rw [htb'] at hss_b'
          exact h_not_opp hss_b'.symm
        · have h_v0_val : (iv0 - iu0).val ≤ (ib - iu0).val := by
            have := fin_sub_split_lt hord1 hord2
            have := fin_sub_split_lt hord1 (lt_trans hord2 hord3)
            omega
          have hss_v0' := hR (iv0 - iu0).val h_v0_val
          have htv : iu0 + finNat (kD + 3) (iv0 - iu0).val = iv0 := by
            have : finNat (kD + 3) (iv0 - iu0).val = iv0 - iu0 := by ext; exact Nat.mod_eq_of_lt (iv0 - iu0).isLt
            rw [this, add_sub_cancel]
          rw [htv] at hss_v0'
          exact hno_v0 hss_v0'

private lemma interior_anchor_caseB_miss {n kD : ℕ} {P : Set (ℝ × ℝ)}
    {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ}
    (hPoly : ShatteredSimplePolygon P S w) (h25 : Sec2To5Interface P S w)
    {D : Finset (Fin n)} (hDB : D = hullVertices S \ certifiedVertices S w)
    (cycD : CCWCycle S D kD) {y : Fin n} (hy_notD : y ∉ D)
    {ib' iu0 iv0 ib id_v : Fin (kD + 3)}
    (hord1 : 0 < (iu0 - ib').val) (hord2 : (iu0 - ib').val < (iv0 - ib').val)
    (hord3 : (iv0 - ib').val < (ib - ib').val) (hord4 : (ib - ib').val < (id_v - ib').val)
    (hb'_nf : ¬ IsFrontVertexOf S D (cycD.toFun ib') (w (Finset.univ \ {cycD.toFun ib', y, cycD.toFun ib})))
    (hu0_nf : ¬ IsFrontVertexOf S D (cycD.toFun iu0) (w (Finset.univ \ {cycD.toFun ib', y, cycD.toFun ib})))
    (hv0_nf : ¬ IsFrontVertexOf S D (cycD.toFun iv0) (w (Finset.univ \ {cycD.toFun ib', y, cycD.toFun ib})))
    (hy_tri : InIntTri (w (Finset.univ \ {cycD.toFun ib', y, cycD.toFun ib})) (S (cycD.toFun iu0)) (S (cycD.toFun iv0)) (S y))
    (hv_noncol : ∀ i j : Fin (kD + 3), i ≠ j →
      orient2D (S (cycD.toFun i)) (S (cycD.toFun j)) (w (Finset.univ \ {cycD.toFun ib', y, cycD.toFun ib})) ≠ 0)
    (hvq_D : ∀ i : Fin (kD + 3),
      orient2D (w (Finset.univ \ {cycD.toFun ib', y, cycD.toFun ib})) (w Finset.univ) (S (cycD.toFun i)) ≠ 0)
    (h_seen_ss : ∀ a b : Fin n, a ∉ ({cycD.toFun ib', y, cycD.toFun ib} : Finset (Fin n)) →
      b ∉ ({cycD.toFun ib', y, cycD.toFun ib} : Finset (Fin n)) →
      ¬ Sees P (w (Finset.univ \ {cycD.toFun ib', y, cycD.toFun ib})) (w Finset.univ) →
      OnSameSide (w (Finset.univ \ {cycD.toFun ib', y, cycD.toFun ib})) (w Finset.univ) (S a) (S b))
    (hy_cone_pos :
      0 < orient2D (w (Finset.univ \ {cycD.toFun ib', y, cycD.toFun ib})) (S (cycD.toFun iu0)) (S y) ∧
      0 < orient2D (w (Finset.univ \ {cycD.toFun ib', y, cycD.toFun ib})) (S y) (S (cycD.toFun iv0)) ∧
      0 < orient2D (w (Finset.univ \ {cycD.toFun ib', y, cycD.toFun ib})) (S (cycD.toFun iu0)) (S (cycD.toFun iv0)))
    (hy_orient_from_uv : ∀ x : ℝ × ℝ,
      0 < orient2D (w (Finset.univ \ {cycD.toFun ib', y, cycD.toFun ib})) x (S (cycD.toFun iu0)) →
      0 < orient2D (w (Finset.univ \ {cycD.toFun ib', y, cycD.toFun ib})) x (S (cycD.toFun iv0)) →
      0 < orient2D (w (Finset.univ \ {cycD.toFun ib', y, cycD.toFun ib})) x (S y))
    (hy_orient_to_uv : ∀ x : ℝ × ℝ,
      0 < orient2D (w (Finset.univ \ {cycD.toFun ib', y, cycD.toFun ib})) (S (cycD.toFun iu0)) x →
      0 < orient2D (w (Finset.univ \ {cycD.toFun ib', y, cycD.toFun ib})) (S (cycD.toFun iv0)) x →
      0 < orient2D (w (Finset.univ \ {cycD.toFun ib', y, cycD.toFun ib})) (S y) x)
    (h_all_nf : ∀ m : Fin (kD + 3),
      0 < orient2D (S (cycD.toFun m)) (S (cycD.toFun (m + 1))) (w (Finset.univ \ {cycD.toFun ib', y, cycD.toFun ib})))
    (hsee : ¬ Sees P (w (Finset.univ \ {cycD.toFun ib', y, cycD.toFun ib})) (w Finset.univ)) :
    InteriorAnchorGoal P S w D cycD y ib' iu0 iv0 ib := by
  let b' := cycD.toFun ib'
  let u0 := cycD.toFun iu0
  let v0 := cycD.toFun iv0
  let b := cycD.toFun ib
  let O_star : Finset (Fin n) := {b', y, b}
  let v := w (Finset.univ \ O_star)
  let q := w Finset.univ
  have hb'_ne_u0 : ib' ≠ iu0 := fun h => by rw [h, sub_self, Fin.val_zero] at hord1; omega
  have hb'_ne_v0 : ib' ≠ iv0 := fun h => by rw [h, sub_self, Fin.val_zero] at hord2; omega
  have hb'_ne_b : ib' ≠ ib := fun h => by rw [h, sub_self, Fin.val_zero] at hord3; omega
  have hb'_ne_d : ib' ≠ id_v := fun h => by rw [h, sub_self, Fin.val_zero] at hord4; omega
  have hu0_ne_b : iu0 ≠ ib := fun h => by rw [h] at hord2; omega
  have hv0_ne_b : iv0 ≠ ib := fun h => by rw [h] at hord3; omega
  have hb_ne_d : ib ≠ id_v := fun h => by rw [h] at hord4; omega
  have hu0_ne_d : iu0 ≠ id_v := fun h => by rw [h] at hord2; omega
  have hv0_ne_d : iv0 ≠ id_v := fun h => by rw [h] at hord3; omega
  have hb'_ne_y : b' ≠ y := fun h => hy_notD (h ▸ ccwCycle_mem cycD ib')
  have hb_ne_y : b ≠ y := fun h => hy_notD (h ▸ ccwCycle_mem cycD ib)
  have hb'D : b' ∈ D := ccwCycle_mem cycD ib'
  have hbD : b ∈ D := ccwCycle_mem cycD ib
  have hb'_O : b' ∈ O_star := Finset.mem_insert_self _ _
  have hy_O : y ∈ O_star := Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  have hb_O : b ∈ O_star := Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  have hm_out : ∀ {m : Fin (kD + 3)}, m ≠ ib' → m ≠ ib → cycD.toFun m ∉ O_star := by
    intro m hm1 hm2 hmO
    simp only [O_star, Finset.mem_insert, Finset.mem_singleton] at hmO
    rcases hmO with h | h | h
    · exact hm1 (cycD.inj h)
    · exact hy_notD (h ▸ ccwCycle_mem cycD m)
    · exact hm2 (cycD.inj h)
  have h_caseB_front_contradict : ∀ x : Fin (kD + 3), ¬ IsFrontVertexOf S D (cycD.toFun x) v →
      0 < (x - ib').val → (x - ib').val < (ib - ib').val →
      0 < orient2D v (S b) (S b') → 0 < orient2D v (S b) (S (cycD.toFun x)) →
      0 < orient2D v (S (cycD.toFun x)) (S b') → False := by
    intro x hnf hx1 hx2 hbb' hbx hxb'
    have hccw_x : 0 < orient2D (S b) (S b') (S (cycD.toFun x)) := by
      have hccw := ccwCycle_ccw3 cycD hx1 hx2; unfold orient2D at hccw ⊢; linarith
    have hin : InIntTri v (S b) (S b') (S (cycD.toFun x)) := by
      rw [inIntTri_iff_orient_pos hbb']; exact ⟨hbx, hccw_x, by unfold orient2D at hxb' ⊢; linarith⟩
    have hx_ne_b : cycD.toFun x ≠ b := cycD.inj.ne (fun h => by rw [h] at hx2; exact hx2.ne rfl)
    have hx_ne_b' : cycD.toFun x ≠ b' := cycD.inj.ne (fun h => by rw [h, sub_self, Fin.val_zero] at hx1; omega)
    let C3 : Finset (Fin n) := {b, cycD.toFun x, b'}
    have hC3_sub : C3 ⊆ D := fun z hz => by
      simp only [C3, Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl | rfl <;> [exact hbD; exact ccwCycle_mem cycD x; exact hb'D]
    have hC3_card : 3 ≤ C3.card := by
      have h1 : b ∉ ({cycD.toFun x, b'} : Finset (Fin n)) := fun h => by
        simp only [Finset.mem_insert, Finset.mem_singleton] at h
        rcases h with h | h
        · exact hx_ne_b.symm h
        · exact (cycD.inj.ne hb'_ne_b).symm h
      have h2 : cycD.toFun x ∉ ({b'} : Finset (Fin n)) := by simp [hx_ne_b']
      rw [Finset.card_insert_of_notMem h1, Finset.card_insert_of_notMem h2, Finset.card_singleton]
    exact hnf (h25.front_restoration C3 D (cycD.toFun x) v hC3_sub (hullVertices_convexPos S (hDB ▸ Finset.sdiff_subset))
      hC3_card (Set.mem_range_self (Finset.univ \ O_star))
      (inIntTri_implies_isFrontVertexOf_tri S hx_ne_b.symm hx_ne_b'.symm (cycD.inj.ne hb'_ne_b).symm v hin))
  have hss_u0_v0 := h_seen_ss u0 v0 (hm_out hb'_ne_u0.symm hu0_ne_b) (hm_out hb'_ne_v0.symm hv0_ne_b) hsee
  have hss_u0_d := h_seen_ss u0 (cycD.toFun id_v) (hm_out hb'_ne_u0.symm hu0_ne_b) (hm_out hb'_ne_d.symm hb_ne_d.symm) hsee
  have hy_same_u0 : OnSameSide v q (S u0) (S y) := by
    rcases hy_tri with ⟨_, _, _, _, hm2, hm3, hs, hy1, hy2⟩
    have hid := orient2D_convex_comb3 v q v (S u0) (S v0) (S y) _ _ _ hs hy1 hy2
    rw [orient2D_self_outer, mul_zero, zero_add] at hid
    unfold OnSameSide at hss_u0_v0 ⊢
    rcases lt_or_gt_of_ne (hvq_D iu0) with hqn | hqp
    · have hvp : orient2D v q (S v0) < 0 := by nlinarith only [hss_u0_v0, hqn]
      have hyp : orient2D v q (S y) < 0 := by rw [hid]; nlinarith only [hm2, hm3, hqn, hvp]
      exact mul_pos_of_neg_of_neg hqn hyp
    · have hvp : 0 < orient2D v q (S v0) := by nlinarith only [hss_u0_v0, hqp]
      have hyp : 0 < orient2D v q (S y) := by rw [hid]; nlinarith only [hm2, hm3, hqp, hvp]
      exact mul_pos hqp hyp
  have hb'_or_b_ss : OnSameSide v q (S u0) (S b') ∨ OnSameSide v q (S u0) (S b) := by
    have hfc := (fourgon_diag_cramer v q (S u0) (S (cycD.toFun id_v)) (S b') (S b)).1
    have ho1 : 0 < orient2D (S b') (S b) (S (cycD.toFun id_v)) :=
      ccwCycle_ccw3 cycD (lt_trans hord1 (lt_trans hord2 hord3)) hord4
    have ho2 : orient2D (S b') (S b) (S u0) < 0 := by
      have hcc := ccwCycle_ccw3 cycD hord1 (lt_trans hord2 hord3); unfold orient2D at hcc ⊢; linarith
    have ho3 : orient2D (S u0) (S (cycD.toFun id_v)) (S b) < 0 := by
      have ⟨hs1, hp1⟩ := fin_sub_split_lt hord1 (lt_trans hord2 hord3)
      have ⟨hs2, _⟩ := fin_sub_split_lt hord1 (lt_trans hord2 (lt_trans hord3 hord4))
      have hcc : 0 < orient2D (S u0) (S b) (S (cycD.toFun id_v)) := ccwCycle_ccw3 cycD hp1 (by omega)
      unfold orient2D at hcc ⊢; linarith
    have ho4 : 0 < orient2D (S u0) (S (cycD.toFun id_v)) (S b') := by
      have ⟨hs2, hp2⟩ := fin_sub_split_lt hord1 (lt_trans hord2 (lt_trans hord3 hord4))
      have h1 := fin_sub_add_compl hu0_ne_d; have h2 := fin_sub_add_compl hb'_ne_u0
      have hlt_d := (id_v - ib').isLt
      have hcc : 0 < orient2D (S u0) (S (cycD.toFun id_v)) (S b') :=
        ccwCycle_ccw3 cycD hp2 (by omega : (id_v - iu0).val < (ib' - iu0).val)
      unfold orient2D at hcc ⊢; linarith
    by_contra hnot; push Not at hnot; unfold OnSameSide at hnot
    have hbn1 : orient2D v q (S u0) * orient2D v q (S b') < 0 := lt_of_le_of_ne (not_lt.mp hnot.1) (mul_ne_zero (hvq_D iu0) (hvq_D ib'))
    have hbn2 : orient2D v q (S u0) * orient2D v q (S b) < 0 := lt_of_le_of_ne (not_lt.mp hnot.2) (mul_ne_zero (hvq_D iu0) (hvq_D ib))
    unfold OnSameSide at hss_u0_d
    rcases lt_or_gt_of_ne (hvq_D iu0) with hqn | hqp
    · have hdn : orient2D v q (S (cycD.toFun id_v)) < 0 := by nlinarith only [hss_u0_d, hqn]
      have hb'p : 0 < orient2D v q (S b') := by nlinarith only [hbn1, hqn]
      have hbp : 0 < orient2D v q (S b) := by nlinarith only [hbn2, hqn]
      nlinarith only [hfc, ho1, ho2, ho3, ho4, hqn, hdn, hb'p, hbp]
    · have hdp : 0 < orient2D v q (S (cycD.toFun id_v)) := by nlinarith only [hss_u0_d, hqp]
      have hb'n : orient2D v q (S b') < 0 := by nlinarith only [hbn1, hqp]
      have hbn : orient2D v q (S b) < 0 := by nlinarith only [hbn2, hqp]
      nlinarith only [hfc, ho1, ho2, ho3, ho4, hqp, hdp, hb'n, hbn]
  have ha1 : ∀ a b_ : Fin (kD + 3), a ≠ b_ → OnSameSide v q (S (cycD.toFun a)) (S (cycD.toFun b_)) →
      ((∀ t : ℕ, t ≤ (b_ - a).val → OnSameSide v q (S (cycD.toFun a)) (S (cycD.toFun (a + finNat (kD + 3) t)))) ∨
       (∀ t : ℕ, t ≤ (a - b_).val → OnSameSide v q (S (cycD.toFun a)) (S (cycD.toFun (b_ + finNat (kD + 3) t))))) := by
    intro a b_ hab hss
    rcases farChain_path_between cycD v q hv_noncol hvq_D a b_ hab hss
      (Or.inl (by simpa [sub_add_cancel] using h_all_nf (a - 1))) (Or.inl (by simpa [sub_add_cancel] using h_all_nf (b_ - 1))) with h1 | h2
    · exact Or.inl h1.2
    · exact Or.inr h2.2
  by_cases hb'_ss : OnSameSide v q (S u0) (S b')
  · by_cases hb_ss : OnSameSide v q (S u0) (S b)
    · rcases ha1 ib' ib hb'_ne_b (hb'_ss.symm.trans hb_ss) with hL | hR
      · have hord := farChain_all_nonfacing_lt_pi_subchain cycD v q h_all_nf ib' ib hb'_ne_b hL
        have hu0 := hord ib' iu0 (by rw [sub_self, Fin.val_zero]; exact hord1) (le_of_lt (lt_trans hord2 hord3))
        have hv0 := hord ib' iv0 (by rw [sub_self, Fin.val_zero]; exact lt_trans hord1 hord2) (le_of_lt hord3)
        have hb'y : 0 < orient2D v (S b') (S y) := hy_orient_from_uv (S b') hu0.1 hv0.1
        have hyb : 0 < orient2D v (S y) (S b) :=
          hy_orient_to_uv (S b) (hord iu0 ib (by have := fin_sub_split_lt hord1 (lt_trans hord2 hord3); omega) le_rfl).1
            (hord iv0 ib (by have := fin_sub_split_lt (lt_trans hord1 hord2) hord3; omega) le_rfl).1
        have hss_b'y : OnSameSide v q (S b') (S y) := hb'_ss.symm.trans hy_same_u0
        have hss_yb : OnSameSide v q (S y) (S b) := hy_same_u0.symm.trans hb_ss
        rcases lt_or_gt_of_ne (hvq_D iu0) with hqn | hqp
        · exact interior_anchor_buildL hPoly h25 hDB cycD hy_notD (lt_trans hord2 hord3) hy_tri hord2
            (goodAnchorPair_of_cone_ends hb'_O hy_O hb'_ne_y hss_b'y hb'y
              (fun h => False.elim (by unfold OnSameSide at hb'_ss; nlinarith only [hb'_ss, hqn, h]))
              (fun _ => ⟨v0, hm_out hb'_ne_v0.symm hv0_ne_b,
                by unfold OnSameSide at hss_u0_v0; nlinarith only [hss_u0_v0, hqn], hy_cone_pos.2.1⟩))
            hb'y (fun m hm1 hm2 => ⟨(hord ib' m (by rw [sub_self, Fin.val_zero]; exact hm1) (le_trans hm2 (le_of_lt (lt_trans hord2 hord3)))).1, by
              by_cases hmu : m = iu0
              · rw [hmu]; exact hy_cone_pos.1
              · have hmu_lt : (m - ib').val < (iu0 - ib').val := lt_of_le_of_ne hm2 (fun h => hmu (sub_left_inj.mp (Fin.ext h)))
                exact hy_orient_from_uv _ (hord m iu0 hmu_lt (le_of_lt (lt_trans hord2 hord3))).1
                  (hord m iv0 (lt_trans hmu_lt hord2) (le_of_lt hord3)).1⟩)
        · exact interior_anchor_buildR hPoly h25 hDB cycD hy_notD hy_tri hord1 hord2 hord3
            (goodAnchorPair_of_cone_ends hy_O hb_O hb_ne_y.symm hss_yb hyb
              (fun _ => ⟨u0, hm_out hb'_ne_u0.symm hu0_ne_b, hqp, hy_cone_pos.1⟩)
              (fun h => False.elim (by unfold OnSameSide at hy_same_u0; nlinarith only [hy_same_u0, hqp, h])))
            hyb (fun m hm1 hm2 => ⟨by
              by_cases hmv : m = iv0
              · rw [hmv]; exact hy_cone_pos.2.1
              · have hmv_lt : (iv0 - ib').val < (m - ib').val := lt_of_le_of_ne hm1 (fun h => hmv (sub_left_inj.mp (Fin.ext h)).symm)
                exact hy_orient_to_uv _ (hord iu0 m (lt_trans hord2 hmv_lt) (le_of_lt hm2)).1 (hord iv0 m hmv_lt (le_of_lt hm2)).1,
              (hord m ib hm2 le_rfl).1⟩)
      · have hord := farChain_all_nonfacing_lt_pi_subchain cycD v q h_all_nf ib ib' hb'_ne_b.symm
          (fun t ht => (hb_ss.symm.trans hb'_ss).trans (hR t ht))
        have hbb' : 0 < orient2D v (S b) (S b') :=
          (hord ib ib' (by rw [sub_self, Fin.val_zero]; exact Nat.pos_of_ne_zero (fun h => hb'_ne_b (sub_eq_zero.mp (Fin.ext h)))) le_rfl).1
        have hbd : 0 < orient2D v (S b) (S (cycD.toFun id_v)) :=
          (hord ib id_v (by rw [sub_self, Fin.val_zero]; exact Nat.pos_of_ne_zero (fun h => hb_ne_d (sub_eq_zero.mp (Fin.ext h)).symm))
            (by have := fin_sub_split_lt (lt_trans hord1 (lt_trans hord2 hord3)) hord4
                have := fin_sub_add_compl hb'_ne_b; omega)).1
        have hdb' : 0 < orient2D v (S (cycD.toFun id_v)) (S b') :=
          (hord id_v ib' (by
            have := fin_sub_split_lt (lt_trans hord1 (lt_trans hord2 hord3)) hord4
            have := fin_sub_add_compl hb'_ne_b; omega) le_rfl).1
        have hss_bb' : OnSameSide v q (S b) (S b') := hb_ss.symm.trans hb'_ss
        rcases lt_or_gt_of_ne (hvq_D iu0) with hqn | hqp
        · by_cases hvb : 0 < orient2D v (S b') (S v0)
          · exact interior_anchor_buildMid hPoly h25 hDB cycD hy_notD
              (goodAnchorPair_of_cone_ends hb_O hb'_O (cycD.inj.ne hb'_ne_b).symm hss_bb' hbb'
                (fun h => False.elim (by unfold OnSameSide at hb_ss; nlinarith only [hb_ss, hqn, h]))
                (fun _ => ⟨v0, hm_out hb'_ne_v0.symm hv0_ne_b,
                  by unfold OnSameSide at hss_u0_v0; nlinarith only [hss_u0_v0, hqn], hvb⟩))
              hbb' (fun m hm1 hm2 => ⟨(hord ib m (by simpa using hm1) (le_of_lt hm2)).1, (hord m ib' hm2 le_rfl).1⟩)
          · have hv0b' : 0 < orient2D v (S v0) (S b') := by
              have hne := hv_noncol ib' iv0 hb'_ne_v0; have h1 := not_lt.mp hvb
              exact lt_of_le_of_ne (by unfold orient2D at h1 ⊢; linarith) (fun h => hne (by unfold orient2D at h ⊢; linarith))
            have hv0b : 0 < orient2D v (S v0) (S b) := by
              by_contra hnot
              have hbv0 : 0 < orient2D v (S b) (S v0) := by
                have hne := hv_noncol ib iv0 hv0_ne_b.symm; have h1 := not_lt.mp hnot
                exact lt_of_le_of_ne (by unfold orient2D at h1 ⊢; linarith) (fun h => hne (by unfold orient2D at h ⊢; linarith))
              exact h_caseB_front_contradict iv0 hv0_nf (lt_trans hord1 hord2) hord3 hbb' hbv0 hv0b'
            rcases ha1 iv0 ib hv0_ne_b (hss_u0_v0.symm.trans hb_ss) with hLv | hRv
            · have hordv := farChain_all_nonfacing_lt_pi_subchain cycD v q h_all_nf iv0 ib hv0_ne_b hLv
              have hyb : 0 < orient2D v (S y) (S b) := by
                have hid := orient2D_angle_trans_id v q (S y) (S v0) (S b)
                unfold OnSameSide at hy_same_u0 hss_u0_v0 hb_ss
                have hqy : orient2D v q (S y) < 0 := by nlinarith only [hy_same_u0, hqn]
                have hqv : orient2D v q (S v0) < 0 := by nlinarith only [hss_u0_v0, hqn]
                have hqb : orient2D v q (S b) < 0 := by nlinarith only [hb_ss, hqn]
                nlinarith only [hid, hqy, hqv, hqb, hv0b, hy_cone_pos.2.1]
              exact interior_anchor_buildR hPoly h25 hDB cycD hy_notD hy_tri hord1 hord2 hord3
                (goodAnchorPair_of_cone_ends hy_O hb_O hb_ne_y.symm (hy_same_u0.symm.trans hb_ss) hyb
                  (fun h => False.elim (by unfold OnSameSide at hy_same_u0; nlinarith only [hy_same_u0, hqn, h]))
                  (fun _ => ⟨cycD.toFun id_v, hm_out hb'_ne_d.symm hb_ne_d.symm,
                    by unfold OnSameSide at hss_u0_d; nlinarith only [hss_u0_d, hqn], hbd⟩))
                hyb (fun m hm1 hm2 => ⟨by
                  by_cases hmv : m = iv0
                  · rw [hmv]; exact hy_cone_pos.2.1
                  · have hm_lt : (m - iv0).val ≤ (ib - iv0).val := by
                      have hs_m := fin_sub_split_le hm1
                      have hs_b := fin_sub_split_le (le_of_lt hord3)
                      omega
                    have hm_pos : (iv0 - iv0).val < (m - iv0).val := by
                      rw [sub_self, Fin.val_zero]; exact Nat.pos_of_ne_zero (fun h => hmv (sub_eq_zero.mp (Fin.ext h)))
                    have hv0m := (hordv iv0 m hm_pos hm_lt).1
                    have hqm : orient2D v q (S (cycD.toFun m)) < 0 := by
                      have hs' := hLv (m - iv0).val hm_lt
                      have htm : iv0 + finNat (kD + 3) (m - iv0).val = m := by
                        have : finNat (kD + 3) (m - iv0).val = m - iv0 := by ext; exact Nat.mod_eq_of_lt (m - iv0).isLt
                        rw [this, add_sub_cancel]
                      rw [htm] at hs'; unfold OnSameSide at hss_u0_v0 hs'; nlinarith only [hss_u0_v0, hs', hqn]
                    have hqy : orient2D v q (S y) < 0 := by unfold OnSameSide at hy_same_u0; nlinarith only [hy_same_u0, hqn]
                    have hqv : orient2D v q (S v0) < 0 := by unfold OnSameSide at hss_u0_v0; nlinarith only [hss_u0_v0, hqn]
                    have hid := orient2D_angle_trans_id v q (S y) (S v0) (S (cycD.toFun m))
                    nlinarith only [hid, hqy, hqv, hqm, hv0m, hy_cone_pos.2.1],
                  (hordv m ib (by
                    have hs_m := fin_sub_split_le hm1
                    have hs_b := fin_sub_split_le (le_of_lt hord3)
                    omega) le_rfl).1⟩)
            · exfalso
              have hordv := farChain_all_nonfacing_lt_pi_subchain cycD v q h_all_nf ib iv0 hv0_ne_b.symm
                (fun t ht => (hb_ss.symm.trans hss_u0_v0).trans (hRv t ht))
              have hbv0 := (hordv ib iv0 (by rw [sub_self, Fin.val_zero]; exact Nat.pos_of_ne_zero (fun h => hv0_ne_b (sub_eq_zero.mp (Fin.ext h)))) le_rfl).1
              unfold orient2D at hv0b hbv0; linarith
        · by_cases hub : 0 < orient2D v (S u0) (S b)
          · exact interior_anchor_buildMid hPoly h25 hDB cycD hy_notD
              (goodAnchorPair_of_cone_ends hb_O hb'_O (cycD.inj.ne hb'_ne_b).symm hss_bb' hbb'
                (fun _ => ⟨u0, hm_out hb'_ne_u0.symm hu0_ne_b, hqp, hub⟩)
                (fun h => False.elim (by unfold OnSameSide at hb_ss; nlinarith only [hb_ss, hqp, h])))
              hbb' (fun m hm1 hm2 => ⟨(hord ib m (by simpa using hm1) (le_of_lt hm2)).1, (hord m ib' hm2 le_rfl).1⟩)
          · have hbu0 : 0 < orient2D v (S b) (S u0) := by
              have hne := hv_noncol ib iu0 hu0_ne_b.symm; have h1 := not_lt.mp hub
              exact lt_of_le_of_ne (by unfold orient2D at h1 ⊢; linarith) (fun h => hne (by unfold orient2D at h ⊢; linarith))
            have hb'u0 : 0 < orient2D v (S b') (S u0) := by
              by_contra hnot
              have hu0b' : 0 < orient2D v (S u0) (S b') := by
                have hne := hv_noncol iu0 ib' hb'_ne_u0.symm; have h1 := not_lt.mp hnot
                exact lt_of_le_of_ne (by unfold orient2D at h1 ⊢; linarith) (fun h => hne (by unfold orient2D at h ⊢; linarith))
              exact h_caseB_front_contradict iu0 hu0_nf hord1 (lt_trans hord2 hord3) hbb' hbu0 hu0b'
            rcases ha1 ib' iu0 hb'_ne_u0 hb'_ss.symm with hLu | hRu
            · have hordu := farChain_all_nonfacing_lt_pi_subchain cycD v q h_all_nf ib' iu0 hb'_ne_u0 hLu
              have hb'y : 0 < orient2D v (S b') (S y) := by
                have hid := orient2D_angle_trans_id v q (S b') (S u0) (S y)
                unfold OnSameSide at hb'_ss hy_same_u0
                have hqb' : 0 < orient2D v q (S b') := by nlinarith only [hb'_ss, hqp]
                have hqy : 0 < orient2D v q (S y) := by nlinarith only [hy_same_u0, hqp]
                nlinarith only [hid, hqb', hqy, hqp, hb'u0, hy_cone_pos.1]
              exact interior_anchor_buildL hPoly h25 hDB cycD hy_notD (lt_trans hord2 hord3) hy_tri hord2
                (goodAnchorPair_of_cone_ends hb'_O hy_O hb'_ne_y (hb'_ss.symm.trans hy_same_u0) hb'y
                  (fun _ => ⟨cycD.toFun id_v, hm_out hb'_ne_d.symm hb_ne_d.symm,
                    by unfold OnSameSide at hss_u0_d; nlinarith only [hss_u0_d, hqp], hdb'⟩)
                  (fun h => False.elim (by unfold OnSameSide at hb'_ss; nlinarith only [hb'_ss, hqp, h])))
                hb'y (fun m hm1 hm2 => ⟨(hordu ib' m (by simpa using hm1) hm2).1, by
                  by_cases hmu : m = iu0
                  · rw [hmu]; exact hy_cone_pos.1
                  · have hm_lt : (m - ib').val < (iu0 - ib').val := lt_of_le_of_ne hm2 (fun h => hmu (sub_left_inj.mp (Fin.ext h)))
                    have hmu_o := (hordu m iu0 hm_lt le_rfl).1
                    have hqm : 0 < orient2D v q (S (cycD.toFun m)) := by
                      have hs' := hLu (m - ib').val hm2
                      have htm : ib' + finNat (kD + 3) (m - ib').val = m := by
                        have : finNat (kD + 3) (m - ib').val = m - ib' := by ext; exact Nat.mod_eq_of_lt (m - ib').isLt
                        rw [this, add_sub_cancel]
                      rw [htm] at hs'; unfold OnSameSide at hb'_ss hs'; nlinarith only [hb'_ss, hs', hqp]
                    have hqy : 0 < orient2D v q (S y) := by unfold OnSameSide at hy_same_u0; nlinarith only [hy_same_u0, hqp]
                    have hid := orient2D_angle_trans_id v q (S (cycD.toFun m)) (S u0) (S y)
                    nlinarith only [hid, hqm, hqp, hqy, hmu_o, hy_cone_pos.1]⟩)
            · exfalso
              have hordu := farChain_all_nonfacing_lt_pi_subchain cycD v q h_all_nf iu0 ib' hb'_ne_u0.symm
                (fun t ht => hb'_ss.trans (hRu t ht))
              have hu0b' := (hordu iu0 ib' (by rw [sub_self, Fin.val_zero]; exact Nat.pos_of_ne_zero (fun h => hb'_ne_u0 (sub_eq_zero.mp (Fin.ext h)))) le_rfl).1
              unfold orient2D at hb'u0 hu0b'; linarith
    · have h_no_v0_d : ¬ OnSameSide v q (S (cycD.toFun id_v)) (S b) := fun h => hb_ss (hss_u0_d.trans h)
      rcases ha1 id_v iv0 hv0_ne_d.symm (hss_u0_d.symm.trans hss_u0_v0) with hL | hbad
      · have hord := farChain_all_nonfacing_lt_pi_subchain cycD v q h_all_nf id_v iv0 hv0_ne_d.symm hL
        have hc_db' : (ib' - id_v).val < (iv0 - id_v).val := by
          have h1 := fin_sub_add_compl hb'_ne_d
          have := fin_sub_split_lt (lt_trans hord1 (lt_trans hord2 hord3)) hord4
          have : iv0 - id_v = (iv0 - ib') + (ib' - id_v) := by abel
          have hlt1 : (iv0 - ib').val + (ib' - id_v).val < kD + 3 := by omega
          have hv' := congrArg Fin.val this; rw [Fin.val_add, Nat.mod_eq_of_lt hlt1] at hv'; omega
        have hc_v0d : (iv0 - id_v).val = (iv0 - ib').val + (ib' - id_v).val := by
          have h1 := fin_sub_add_compl hb'_ne_d
          have := fin_sub_split_lt (lt_trans hord1 (lt_trans hord2 hord3)) hord4
          have : iv0 - id_v = (iv0 - ib') + (ib' - id_v) := by abel
          have hlt1 : (iv0 - ib').val + (ib' - id_v).val < kD + 3 := by omega
          have hv' := congrArg Fin.val this; rw [Fin.val_add, Nat.mod_eq_of_lt hlt1] at hv'; exact hv'
        have hc_u0d : (iu0 - id_v).val = (iu0 - ib').val + (ib' - id_v).val := by
          have h1 := fin_sub_add_compl hb'_ne_d
          have := fin_sub_split_lt (lt_trans hord1 (lt_trans hord2 hord3)) hord4
          have : iu0 - id_v = (iu0 - ib') + (ib' - id_v) := by abel
          have hlt1 : (iu0 - ib').val + (ib' - id_v).val < kD + 3 := by omega
          have hv' := congrArg Fin.val this; rw [Fin.val_add, Nat.mod_eq_of_lt hlt1] at hv'; exact hv'
        have hdb' := (hord id_v ib' (by rw [sub_self, Fin.val_zero]; exact Nat.pos_of_ne_zero (fun h => hb'_ne_d (sub_eq_zero.mp (Fin.ext h)))) (le_of_lt hc_db')).1
        have hb'u0 := (hord ib' iu0 (by omega) (by omega)).1
        have hb'v0 := (hord ib' iv0 (by omega) le_rfl).1
        have hb'y : 0 < orient2D v (S b') (S y) := hy_orient_from_uv (S b') hb'u0 hb'v0
        have hss_b'y : OnSameSide v q (S b') (S y) := hb'_ss.symm.trans hy_same_u0
        exact interior_anchor_buildL hPoly h25 hDB cycD hy_notD (lt_trans hord2 hord3) hy_tri hord2
          (goodAnchorPair_of_cone_ends hb'_O hy_O hb'_ne_y hss_b'y hb'y
            (fun hqb' => ⟨cycD.toFun id_v, hm_out hb'_ne_d.symm hb_ne_d.symm,
              by unfold OnSameSide at hss_u0_d hb'_ss; nlinarith only [hss_u0_d, hb'_ss, hqb'], hdb'⟩)
            (fun hqb' => ⟨v0, hm_out hb'_ne_v0.symm hv0_ne_b,
              by unfold OnSameSide at hss_u0_v0 hb'_ss; nlinarith only [hss_u0_v0, hb'_ss, hqb'], hy_cone_pos.2.1⟩))
          hb'y (fun m hm1 hm2 => by
            have hm_d : (m - id_v).val = (m - ib').val + (ib' - id_v).val := by
              have h1 := fin_sub_add_compl hb'_ne_d
              have := fin_sub_split_lt (lt_trans hord1 (lt_trans hord2 hord3)) hord4
              have : m - id_v = (m - ib') + (ib' - id_v) := by abel
              have hlt1 : (m - ib').val + (ib' - id_v).val < kD + 3 := by omega
              have hv' := congrArg Fin.val this; rw [Fin.val_add, Nat.mod_eq_of_lt hlt1] at hv'; exact hv'
            refine ⟨(hord ib' m (by omega) (by omega)).1, ?_⟩
            by_cases hmu : m = iu0
            · rw [hmu]; exact hy_cone_pos.1
            · have hm_lt : (m - ib').val < (iu0 - ib').val := lt_of_le_of_ne hm2 (fun h => hmu (sub_left_inj.mp (Fin.ext h)))
              exact hy_orient_from_uv _ (hord m iu0 (by omega) (by omega)).1 (hord m iv0 (by omega) le_rfl).1)
      · exfalso
        have h_b_val : (ib - iv0).val ≤ (id_v - iv0).val := by
          have := fin_sub_split_lt (lt_trans hord1 hord2) hord3
          have := fin_sub_split_lt (lt_trans hord1 hord2) (lt_trans hord3 hord4)
          omega
        have hss_b := hbad (ib - iv0).val h_b_val
        have htb : iv0 + finNat (kD + 3) (ib - iv0).val = ib := by
          have : finNat (kD + 3) (ib - iv0).val = ib - iv0 := by ext; exact Nat.mod_eq_of_lt (ib - iv0).isLt
          rw [this, add_sub_cancel]
        rw [htb] at hss_b
        exact h_no_v0_d hss_b
  · have hb_ss' : OnSameSide v q (S u0) (S b) := hb'_or_b_ss.resolve_left hb'_ss
    rcases ha1 iu0 id_v hu0_ne_d hss_u0_d with hL | hbad
    · have hord := farChain_all_nonfacing_lt_pi_subchain cycD v q h_all_nf iu0 id_v hu0_ne_d hL
      have hc_v0 : (iv0 - iu0).val < (id_v - iu0).val := by
        have := fin_sub_split_lt hord1 hord2
        have := fin_sub_split_lt hord1 (lt_trans hord2 (lt_trans hord3 hord4))
        omega
      have hc_b : (ib - iu0).val < (id_v - iu0).val := by
        have := fin_sub_split_lt hord1 (lt_trans hord2 hord3)
        have := fin_sub_split_lt hord1 (lt_trans hord2 (lt_trans hord3 hord4))
        omega
      have hc_v0_b : (iv0 - iu0).val < (ib - iu0).val := by
        have := fin_sub_split_lt hord1 hord2
        have := fin_sub_split_lt hord1 (lt_trans hord2 hord3)
        omega
      have hu0_b := (hord iu0 ib (by rw [sub_self, Fin.val_zero]; exact Nat.pos_of_ne_zero (fun h => hu0_ne_b (sub_eq_zero.mp (Fin.ext h)).symm)) (le_of_lt hc_b)).1
      have hv0_b := (hord iv0 ib hc_v0_b (le_of_lt hc_b)).1
      have hb_d := (hord ib id_v (by omega) le_rfl).1
      have hyb : 0 < orient2D v (S y) (S b) := hy_orient_to_uv (S b) hu0_b hv0_b
      have hss_yb : OnSameSide v q (S y) (S b) := hy_same_u0.symm.trans hb_ss'
      exact interior_anchor_buildR hPoly h25 hDB cycD hy_notD hy_tri hord1 hord2 hord3
        (goodAnchorPair_of_cone_ends hy_O hb_O hb_ne_y.symm hss_yb hyb
          (fun hqy => ⟨u0, hm_out hb'_ne_u0.symm hu0_ne_b,
            by unfold OnSameSide at hy_same_u0; nlinarith only [hy_same_u0, hqy], hy_cone_pos.1⟩)
          (fun hqy => ⟨cycD.toFun id_v, hm_out hb'_ne_d.symm hb_ne_d.symm,
            by unfold OnSameSide at hss_u0_d hy_same_u0; nlinarith only [hss_u0_d, hy_same_u0, hqy], hb_d⟩))
        hyb (fun m hm1 hm2 => by
          have hs_m := fin_sub_split_le (le_trans (le_of_lt hord2) hm1)
          have hs_b := fin_sub_split_le (le_of_lt (lt_trans hord2 hord3))
          have hm_u0_pos : (iu0 - iu0).val < (m - iu0).val := by rw [sub_self, Fin.val_zero]; omega
          have hm_b_lt : (m - iu0).val < (ib - iu0).val := by omega
          refine ⟨?_, (hord m ib hm_b_lt (le_of_lt hc_b)).1⟩
          by_cases hmv : m = iv0
          · rw [hmv]; exact hy_cone_pos.2.1
          · have hmv_gt : (iv0 - ib').val < (m - ib').val := lt_of_le_of_ne hm1 (fun h => hmv (sub_left_inj.mp (Fin.ext h)).symm)
            have hs_v0 := fin_sub_split_le (le_of_lt hord2)
            have hvm_lt : (iv0 - iu0).val < (m - iu0).val := by omega
            have hm_le : (m - iu0).val ≤ (id_v - iu0).val := le_of_lt (lt_trans hm_b_lt hc_b)
            exact hy_orient_to_uv _ (hord iu0 m hm_u0_pos hm_le).1 (hord iv0 m hvm_lt hm_le).1)
    · exfalso
      have h_b'_val : (ib' - id_v).val ≤ (iu0 - id_v).val := by
        have h1 := fin_sub_add_compl hb'_ne_d; have h2 := fin_sub_add_compl hu0_ne_d
        have := fin_sub_split_lt hord1 (lt_trans hord2 (lt_trans hord3 hord4)); omega
      have hss_b' := hbad (ib' - id_v).val h_b'_val
      have htb' : id_v + finNat (kD + 3) (ib' - id_v).val = ib' := by
        have : finNat (kD + 3) (ib' - id_v).val = ib' - id_v := by ext; exact Nat.mod_eq_of_lt (ib' - id_v).isLt
        rw [this, add_sub_cancel]
      rw [htb'] at hss_b'
      exact hb'_ss (hss_u0_d.trans (hss_u0_d.symm.trans hss_b'))

/-- Proposition 6.6 (`interior-anchor`, `upper_9.tex` lines 707–731):
    For any `y ∈ M` on exit edge `u0 v0`, and `b', u0, v0, b, d` in cyclic order around `D`
    (`O* = {b', y, b}`, `v = w (S \ O*)`):
    (i) `y ∈ IntTri(v, u0, v0)` and none of `b', u0, v0, b` is a front vertex of `D` from `v`;
    (iii) at least one of `gapL = arc_D(b' -> u0) \ {b'}` (anchors `{b', y}`),
    `gapR = arc_D(v0 -> b) \ {b}` (anchors `{y, b}`), or
    `gapMid = arc_D(b -> b') \ {b, b'}` (anchors `{b, b'}`) is a good gap for `v`. -/
theorem interior_anchor {n kD : ℕ} {P : Set (ℝ × ℝ)}
    {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ}
    (hPoly : ShatteredSimplePolygon P S w) (h25 : Sec2To5Interface P S w)
    {D : Finset (Fin n)} (hDB : D = hullVertices S \ certifiedVertices S w)
    (cycD : CCWCycle S D kD)
    {y : Fin n} (hyM : y ∈ Finset.univ \ D)
    (ib' iu0 iv0 ib id_v : Fin (kD + 3))
    (hiv0 : iv0 = iu0 + 1)
    (hord1 : 0 < (iu0 - ib').val)
    (hord2 : (iu0 - ib').val < (iv0 - ib').val)
    (hord3 : (iv0 - ib').val < (ib - ib').val)
    (hord4 : (ib - ib').val < (id_v - ib').val)
    (h_exit_v : 0 < orient2D (S (cycD.toFun iu0)) (S (cycD.toFun iv0)) (w D) ∧
      InIntTri (w D) (S (cycD.toFun iu0)) (S (cycD.toFun iv0)) (S y) ∧
      (∀ x ∈ WitnessSet {cycD.toFun iu0, cycD.toFun iv0} ∅ w,
        InIntTri x (S (cycD.toFun iu0)) (S (cycD.toFun iv0)) (S y)) ∧
      (∀ l r : Fin n, (certifiedVertices S w).Nonempty →
        IsCCWEdge S D l r → (∀ h ∈ certifiedVertices S w, orient2D (S l) (S r) (S h) < 0) →
        (cycD.toFun iu0, cycD.toFun iv0) ≠ (l, r))) :
    let b' := cycD.toFun ib'
    let u0 := cycD.toFun iu0
    let v0 := cycD.toFun iv0
    let b := cycD.toFun ib
    let O_star : Finset (Fin n) := {b', y, b}
    let v := w (Finset.univ \ O_star)
    let gapL := D.filter (fun p => ∃ m : Fin (kD + 3), cycD.toFun m = p ∧
      0 < (m - ib').val ∧ (m - ib').val ≤ (iu0 - ib').val)
    let gapR := D.filter (fun p => ∃ m : Fin (kD + 3), cycD.toFun m = p ∧
      (iv0 - ib').val ≤ (m - ib').val ∧ (m - ib').val < (ib - ib').val)
    let gapMid := D.filter (fun p => ∃ m : Fin (kD + 3), cycD.toFun m = p ∧
      0 < (m - ib).val ∧ (m - ib).val < (ib' - ib).val)
    (InIntTri v (S u0) (S v0) (S y) ∧
      ¬ IsFrontVertexOf S D b' v ∧ ¬ IsFrontVertexOf S D u0 v ∧
      ¬ IsFrontVertexOf S D v0 v ∧ ¬ IsFrontVertexOf S D b v) ∧
    ∃ (oa ob : Fin n) (Γ : Finset (Fin n)),
      ((oa = b' ∧ ob = y ∧ Γ = gapL) ∨
       (oa = y ∧ ob = b ∧ Γ = gapR) ∨
       (oa = b ∧ ob = b' ∧ Γ = gapMid)) ∧
      GoodAnchorPair P S w O_star oa ob ∧
      (∀ p ∈ Γ,
        IsBackVertexOf S (hullVertices S) p v ∧
        SegmentsCross v (S p) (S oa) (S ob) ∧
        (∃ H_hp : OpenHalfPlane, IsHalfPlaneTest P (WitnessSet {oa, ob} ∅ w) (S p) H_hp)) ∧
      (∀ z : Fin n, z ≠ oa → z ≠ ob → z ∉ O_star →
        S z ∈ convexHull ℝ ((Γ ∪ {oa, ob}).image S : Set (ℝ × ℝ)) →
        SegmentsCross v (S z) (S oa) (S ob) ∧
        (∃ H_hp : OpenHalfPlane, IsHalfPlaneTest P (WitnessSet {oa, ob} ∅ w) (S z) H_hp) ∧
        (z ∈ hullVertices S → IsBackVertexOf S (hullVertices S) z v)) := by
  intro b' u0 v0 b O_star v gapL gapR gapMid
  let B := hullVertices S
  let Tv := Finset.univ \ O_star
  let q := w Finset.univ
  have hy_notD : y ∉ D := (Finset.mem_sdiff.mp hyM).2
  have hb'D : b' ∈ D := ccwCycle_mem cycD ib'
  have hu0D : u0 ∈ D := ccwCycle_mem cycD iu0
  have hv0D : v0 ∈ D := ccwCycle_mem cycD iv0
  have hbD : b ∈ D := ccwCycle_mem cycD ib
  have hdD : cycD.toFun id_v ∈ D := ccwCycle_mem cycD id_v
  have h5_ord : kD + 3 ≥ 5 := by
    have h1 := (id_v - ib').isLt; omega
  have hb'_ne_u0 : ib' ≠ iu0 := fun h => by rw [h, sub_self, Fin.val_zero] at hord1; omega
  have hu0_ne_v0 : iu0 ≠ iv0 := fun h => by rw [h] at hord2; omega
  have hv0_ne_b : iv0 ≠ ib := fun h => by rw [h] at hord3; omega
  have hb_ne_d : ib ≠ id_v := fun h => by rw [h] at hord4; omega
  have hb'_ne_v0 : ib' ≠ iv0 := fun h => by rw [h, sub_self, Fin.val_zero] at hord2; omega
  have hb'_ne_b : ib' ≠ ib := fun h => by rw [h, sub_self, Fin.val_zero] at hord3; omega
  have hb'_ne_d : ib' ≠ id_v := fun h => by rw [h, sub_self, Fin.val_zero] at hord4; omega
  have hu0_ne_b : iu0 ≠ ib := fun h => by rw [h] at hord2; omega
  have hv0_ne_d : iv0 ≠ id_v := fun h => by rw [h] at hord3; omega
  have hu0_ne_d : iu0 ≠ id_v := fun h => by rw [h] at hord2; omega
  have hb'_ne_y : b' ≠ y := fun h => hy_notD (h ▸ hb'D)
  have hu0_ne_y : u0 ≠ y := fun h => hy_notD (h ▸ hu0D)
  have hv0_ne_y : v0 ≠ y := fun h => hy_notD (h ▸ hv0D)
  have hb_ne_y : b ≠ y := fun h => hy_notD (h ▸ hbD)
  have hd_ne_y : cycD.toFun id_v ≠ y := fun h => hy_notD (h ▸ hdD)
  have hv_in_W : v ∈ WitnessSet {u0, v0} ∅ w := by
    refine ⟨Tv, ?_, Finset.disjoint_empty_right _, rfl⟩
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun hxO => ?_⟩
    simp only [O_star, Finset.mem_insert, Finset.mem_singleton] at hxO
    rcases hx with rfl | rfl <;> rcases hxO with h | h | h
    · exact hb'_ne_u0 (cycD.inj h.symm)
    · exact hu0_ne_y h
    · exact hu0_ne_b (cycD.inj h)
    · exact hb'_ne_v0 (cycD.inj h.symm)
    · exact hv0_ne_y h
    · exact hv0_ne_b (cycD.inj h)
  have hy_tri : InIntTri v (S u0) (S v0) (S y) := h_exit_v.2.2.1 v hv_in_W
  have hu0v0_nf : 0 < orient2D (S u0) (S v0) v := by
    rcases hy_tri with ⟨μ₁, μ₂, μ₃, h1, _, _, hs, hy1, hy2⟩
    have hccw : 0 < orient2D (S u0) (S v0) (S y) := by
      have he_D : IsCCWEdge S D u0 v0 := by
        dsimp [u0, v0]; rw [hiv0]; exact ccwCycle_isCCWEdge cycD iu0
      have hD3 : 3 ≤ D.card := by
        rw [← cycD.image_eq, Finset.card_image_of_injective Finset.univ cycD.inj, Finset.card_fin]
        omega
      have he_B := isCCWEdge_B_of_D_ne_lr h25 (hDB ▸ hD3) (hDB ▸ he_D) (fun l r hH hlD hrD hlr hlrD hHn =>
        h_exit_v.2.2.2 l r hH (hDB ▸ hlrD) hHn)
      exact orient2D_pos_of_isCCWEdge_B hPoly he_B hu0_ne_y.symm hv0_ne_y.symm
    have hid : orient2D (S u0) (S v0) (S y) = μ₁ * orient2D (S u0) (S v0) v := by
      unfold orient2D; rw [hy1, hy2]
      linear_combination ((S u0).2 * (S v0).1 - (S u0).1 * (S v0).2) * hs
    nlinarith
  have hu0_nf : ¬ IsFrontVertexOf S D u0 v := by
    intro hf
    rw [isFrontVertexOf_iff_ccwCycle cycD iu0 v] at hf
    change orient2D (S (cycD.toFun (iu0 - 1))) (S u0) v < 0 ∧
      orient2D (S u0) (S (cycD.toFun (iu0 + 1))) v < 0 at hf
    rw [← hiv0] at hf
    linarith [hf.2, hu0v0_nf]
  have hv0_nf : ¬ IsFrontVertexOf S D v0 v := by
    intro hf
    rw [isFrontVertexOf_iff_ccwCycle cycD iv0 v] at hf
    have hm1 : iv0 - 1 = iu0 := by rw [hiv0]; abel
    have h1 := hf.1
    rw [hm1] at h1
    linarith [h1, hu0v0_nf]
  have hD_card : D.card = kD + 3 := by
    rw [← cycD.image_eq, Finset.card_image_of_injective Finset.univ cycD.inj, Finset.card_fin]
  have hb'_nf : ¬ IsFrontVertexOf S D b' v := by
    refine no_odd_front hPoly h25 (hDB ▸ Subset.rfl) (by omega) hb'D
      (fun h => (Finset.mem_sdiff.mp h).2 (Finset.mem_insert_self _ _)) (fun x hxD hadj => ?_)
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun hxO => ?_⟩
    simp only [O_star, Finset.mem_insert, Finset.mem_singleton] at hxO
    rcases hxO with rfl | rfl | rfl
    · rcases hadj with e | e <;> exact e.2.2.1 rfl
    · exact hy_notD hxD
    · rcases hadj with e | e
      · rw [isCCWEdge_iff_ccwCycle cycD] at e
        rcases e with ⟨r, hr1, hr2⟩
        have hrb : r = ib := cycD.inj hr1.symm
        have hrb' : r + 1 = ib' := cycD.inj hr2.symm
        rw [hrb] at hrb'
        have h_eq1 : ib' - ib = 1 := by rw [← hrb']; abel
        have h_sum1 := fin_sub_split_lt (lt_trans hord1 (lt_trans hord2 hord3)) hord4
        have h_comp := fin_sub_add_compl hb'_ne_b
        have h1_val : (1 : Fin (kD + 3)).val = 1 := fin_val_one_of_gt (by omega)
        have : (ib' - ib).val = 1 := by rw [h_eq1, h1_val]
        omega
      · rw [isCCWEdge_iff_ccwCycle cycD] at e
        rcases e with ⟨r, hr1, hr2⟩
        have hrb' : r = ib' := cycD.inj hr1.symm
        have hrb : r + 1 = ib := cycD.inj hr2.symm
        rw [hrb'] at hrb
        have h_eq1 : ib - ib' = 1 := by rw [← hrb]; abel
        have h1_val : (1 : Fin (kD + 3)).val = 1 := fin_val_one_of_gt (by omega)
        have : (ib - ib').val = 1 := by rw [h_eq1, h1_val]
        omega
  have hb_nf : ¬ IsFrontVertexOf S D b v := by
    refine no_odd_front hPoly h25 (hDB ▸ Subset.rfl) (by omega) hbD
      (fun h => (Finset.mem_sdiff.mp h).2 (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))))
      (fun x hxD hadj => ?_)
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun hxO => ?_⟩
    simp only [O_star, Finset.mem_insert, Finset.mem_singleton] at hxO
    rcases hxO with rfl | rfl | rfl
    · rcases hadj with e | e
      · rw [isCCWEdge_iff_ccwCycle cycD] at e
        rcases e with ⟨r, hr1, hr2⟩
        have h1_val : (1 : Fin (kD + 3)).val = 1 := fin_val_one_of_gt (by omega)
        have hr1' := cycD.inj hr1.symm
        have hr2' := cycD.inj hr2.symm
        rw [hr1'] at hr2'
        have h_eq1 : ib - ib' = 1 := by rw [← hr2']; abel
        have : (ib - ib').val = 1 := by rw [h_eq1, h1_val]
        omega
      · rw [isCCWEdge_iff_ccwCycle cycD] at e
        rcases e with ⟨r, hr1, hr2⟩
        have h1_val : (1 : Fin (kD + 3)).val = 1 := fin_val_one_of_gt (by omega)
        have hr1' := cycD.inj hr1.symm
        have hr2' := cycD.inj hr2.symm
        rw [hr1'] at hr2'
        have h_eq1 : ib' - ib = 1 := by rw [← hr2']; abel
        have : (ib' - ib).val = 1 := by rw [h_eq1, h1_val]
        have h_sum1 := fin_sub_split_lt (lt_trans hord1 (lt_trans hord2 hord3)) hord4
        have h_comp := fin_sub_add_compl hb'_ne_b
        omega
    · exact hy_notD hxD
    · rcases hadj with e | e <;> exact e.2.2.1 rfl
  refine ⟨⟨hy_tri, hb'_nf, hu0_nf, hv0_nf, hb_nf⟩, ?_⟩
  have hv_ne_q : v ≠ q := by
    intro h
    have hys : Sees P v (S y) := by rw [h]; exact (hPoly.shatters Finset.univ y).mpr (Finset.mem_univ _)
    exact hy_notD (by
      have hyT : y ∈ Tv := (hPoly.shatters Tv y).mp hys
      exfalso; exact (Finset.mem_sdiff.mp hyT).2 (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)))
  have hv_noncol : ∀ i j : Fin (kD + 3), i ≠ j → orient2D (S (cycD.toFun i)) (S (cycD.toFun j)) v ≠ 0 :=
    fun i j hij => hPoly.no_three_collinear _ _ _
      (Or.inl (Set.mem_range_self _)) (Or.inl (Set.mem_range_self _)) (Or.inr (Set.mem_range_self _))
      (hPoly.s_inj.ne (cycD.inj.ne hij)) (hPoly.s_ne_w _ _) (hPoly.s_ne_w _ _)
  have hvq_D : ∀ i : Fin (kD + 3), orient2D v q (S (cycD.toFun i)) ≠ 0 :=
    fun i => hPoly.no_three_collinear _ _ _
      (Or.inr (Set.mem_range_self _)) (Or.inr (Set.mem_range_self _)) (Or.inl (Set.mem_range_self _))
      (hPoly.w_inj.ne (fun h => hv_ne_q (congrArg w h))) (hPoly.s_ne_w _ _).symm (hPoly.s_ne_w _ _).symm
  have hvq_y : orient2D v q (S y) ≠ 0 :=
    hPoly.no_three_collinear _ _ _
      (Or.inr (Set.mem_range_self _)) (Or.inr (Set.mem_range_self _)) (Or.inl (Set.mem_range_self _))
      (hPoly.w_inj.ne (fun h => hv_ne_q (congrArg w h))) (hPoly.s_ne_w _ _).symm (hPoly.s_ne_w _ _).symm
  have hv_noncol_y : ∀ x : Fin n, x ≠ y → orient2D v (S y) (S x) ≠ 0 := fun x hxy =>
    hPoly.no_three_collinear _ _ _
      (Or.inr (Set.mem_range_self _)) (Or.inl (Set.mem_range_self _)) (Or.inl (Set.mem_range_self _))
      (hPoly.s_ne_w _ _).symm (hPoly.s_inj.ne hxy.symm) (hPoly.s_ne_w _ _).symm
  have h_seen_ss : ∀ a b : Fin n, a ∉ O_star → b ∉ O_star → ¬ Sees P v q →
      OnSameSide v q (S a) (S b) := by
    intro a b haO hbO hnq
    have ha_tv : a ∈ Tv := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, haO⟩
    have hb_tv : b ∈ Tv := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hbO⟩
    have hsa := (hPoly.shatters Tv a).mpr ha_tv
    have hsb := (hPoly.shatters Tv b).mpr hb_tv
    have hqa := (hPoly.shatters Finset.univ a).mpr (Finset.mem_univ _)
    have hqb := (hPoly.shatters Finset.univ b).mpr (Finset.mem_univ _)
    by_contra hnot
    have hna : orient2D v q (S a) ≠ 0 := hPoly.no_three_collinear _ _ _
      (Or.inr (Set.mem_range_self _)) (Or.inr (Set.mem_range_self _)) (Or.inl (Set.mem_range_self _))
      (hPoly.w_inj.ne (fun h => hv_ne_q (congrArg w h))) (hPoly.s_ne_w _ _).symm (hPoly.s_ne_w _ _).symm
    have hnb : orient2D v q (S b) ≠ 0 := hPoly.no_three_collinear _ _ _
      (Or.inr (Set.mem_range_self _)) (Or.inr (Set.mem_range_self _)) (Or.inl (Set.mem_range_self _))
      (hPoly.w_inj.ne (fun h => hv_ne_q (congrArg w h))) (hPoly.s_ne_w _ _).symm (hPoly.s_ne_w _ _).symm
    have hneg : orient2D v q (S a) * orient2D v q (S b) < 0 :=
      lt_of_le_of_ne (not_lt.mp hnot) (mul_ne_zero hna hnb)
    rcases lt_or_gt_of_ne hna with han | hap
    · have hbp : 0 < orient2D v q (S b) := by nlinarith
      have hp1 := isPolygonalPathIn_three hsb (sees_symm hqb)
      have hp2 := isPolygonalPathIn_three hsa (sees_symm hqa)
      have hL : InteriorOnLeft v q [v, S b, q] := ⟨le_rfl, fun k hk hk0 hk1 => by
        dsimp at hk1; have : k = 1 := by omega
        subst this; exact hbp⟩
      have hR : InteriorOnRight v q [v, S a, q] := ⟨le_rfl, fun k hk hk0 hk1 => by
        dsimp at hk1; have : k = 1 := by omega
        subst this; exact han⟩
      exact hnq (hPoly.two_path_enclosure v q [v, S b, q] [v, S a, q] hv_ne_q hp1 hp2 hL hR)
    · have hbn : orient2D v q (S b) < 0 := by nlinarith
      have hp1 := isPolygonalPathIn_three hsa (sees_symm hqa)
      have hp2 := isPolygonalPathIn_three hsb (sees_symm hqb)
      have hL : InteriorOnLeft v q [v, S a, q] := ⟨le_rfl, fun k hk hk0 hk1 => by
        dsimp at hk1; have : k = 1 := by omega
        subst this; exact hap⟩
      have hR : InteriorOnRight v q [v, S b, q] := ⟨le_rfl, fun k hk hk0 hk1 => by
        dsimp at hk1; have : k = 1 := by omega
        subst this; exact hbn⟩
      exact hnq (hPoly.two_path_enclosure v q [v, S a, q] [v, S b, q] hv_ne_q hp1 hp2 hL hR)
  -- Helper: `y ∈ InIntTri v u0 v0` inherits strict orientation/angle order between `u0` and `v0`
  have hy_cone_pos : 0 < orient2D v (S u0) (S y) ∧ 0 < orient2D v (S y) (S v0) ∧ 0 < orient2D v (S u0) (S v0) := by
    rcases hy_tri with ⟨μ₁, μ₂, μ₃, hm1, hm2, hm3, hs, hy1, hy2⟩
    have h1 := orient2D_convex_comb3 v (S u0) v (S u0) (S v0) (S y) μ₁ μ₂ μ₃ hs hy1 hy2
    rw [orient2D_self_right, orient2D_self_outer, mul_zero, mul_zero, add_zero, zero_add] at h1
    have h2 := orient2D_convex_comb3 v (S v0) v (S u0) (S v0) (S y) μ₁ μ₂ μ₃ hs hy1 hy2
    rw [orient2D_self_outer, orient2D_self_right, mul_zero, mul_zero, zero_add, add_zero] at h2
    have h0 : 0 < orient2D v (S u0) (S v0) := by unfold orient2D at hu0v0_nf ⊢; linarith
    refine ⟨by rw [h1]; exact mul_pos hm3 h0, by rw [orient2D_swap23, h2]; unfold orient2D at h0 ⊢; nlinarith, h0⟩
  have hy_orient_from_uv : ∀ x : ℝ × ℝ, 0 < orient2D v x (S u0) → 0 < orient2D v x (S v0) →
      0 < orient2D v x (S y) := by
    intro x h1 h2
    rcases hy_tri with ⟨μ₁, μ₂, μ₃, _, hm2, hm3, hs, hy1, hy2⟩
    have hid := orient2D_convex_comb3 v x v (S u0) (S v0) (S y) _ _ _ hs hy1 hy2
    rw [orient2D_self_outer, mul_zero, zero_add] at hid
    rw [hid]; exact add_pos (mul_pos hm2 h1) (mul_pos hm3 h2)
  have hy_orient_to_uv : ∀ x : ℝ × ℝ, 0 < orient2D v (S u0) x → 0 < orient2D v (S v0) x →
      0 < orient2D v (S y) x := by
    intro x h1 h2
    rcases hy_tri with ⟨μ₁, μ₂, μ₃, _, hm2, hm3, hs, hy1, hy2⟩
    have hid := orient2D_convex_comb3 v x v (S u0) (S v0) (S y) _ _ _ hs hy1 hy2
    rw [orient2D_self_outer, mul_zero, zero_add] at hid
    have hneg : orient2D v x (S y) < 0 := by
      rw [hid]
      have h1' : orient2D v x (S u0) < 0 := by unfold orient2D at h1 ⊢; linarith
      have h2' : orient2D v x (S v0) < 0 := by unfold orient2D at h2 ⊢; linarith
      linarith [mul_neg_of_pos_of_neg hm2 h1', mul_neg_of_pos_of_neg hm3 h2']
    unfold orient2D at hneg ⊢; linarith
  by_cases h_ex : ∃ j0 : Fin (kD + 3), orient2D (S (cycD.toFun j0)) (S (cycD.toFun (j0 + 1))) v < 0
  · obtain ⟨e_start, e_end, L, _, _, _, h_face_lt, _, h_far_iff, _, _, h_ang⟩ :=
      facing_arc_complement_order cycD v hv_noncol h_ex
    have h_not_in_face : ∀ p : Fin (kD + 3), ¬ IsFrontVertexOf S D (cycD.toFun p) v →
        (p - e_end).val ≤ (e_start - e_end).val := by
      intro p hnf
      rw [← h_far_iff p]
      rintro ⟨hp0, hpL⟩
      apply hnf
      rw [isFrontVertexOf_iff_ccwCycle cycD p v]
      have hpm1 : ((p - 1) - e_start).val < L := by
        have h1_val : (1 : Fin (kD + 3)).val = 1 := fin_val_one_of_gt (by omega)
        have heq : (p - 1) - e_start = (p - e_start) - 1 := by abel
        rw [heq, fin_val_sub_eq, if_pos (Fin.le_def.mpr (by rw [h1_val]; omega)), h1_val]; omega
      exact ⟨by have := h_face_lt (p - 1) hpm1; rwa [sub_add_cancel] at this, h_face_lt p hpL⟩
    have hib'_far := h_not_in_face ib' hb'_nf
    have hiu0_far := h_not_in_face iu0 hu0_nf
    have hib_far := h_not_in_face ib hb_nf
    have h_u0_not_es : iu0 ≠ e_start := fun h => by
      have hf := h_face_lt iu0 (by rw [h, sub_self, Fin.val_zero]; omega)
      rw [← hiv0] at hf; linarith [hf, hu0v0_nf]
    by_cases h1 : (e_start - ib').val < (iu0 - ib').val
    · exact interior_anchor_caseA_L hPoly h25 hDB cycD hy_notD hord1 hord2 hord3 hord4 hy_tri
        hv_noncol hvq_D hvq_y hv_noncol_y h_seen_ss hy_cone_pos hy_orient_to_uv e_start e_end
        hiu0_far h1 h_u0_not_es (fun a b ha hb => (h_ang a b ha hb).2)
    · by_cases h2 : (e_start - ib').val < (ib - ib').val
      · have h_ge_v0 : (iv0 - ib').val ≤ (e_start - ib').val := by
          by_contra hlt
          have hiv_val : (iv0 - ib').val = (iu0 - ib').val + 1 := by
            have h1' : iv0 - ib' = (iu0 - ib') + 1 := by rw [hiv0]; abel
            rw [h1', Fin.val_add, fin_val_one_of_gt (by omega)]
            rw [Nat.mod_eq_of_lt (by have := (iv0 - ib').isLt; omega)]
          have : (e_start - ib').val = (iu0 - ib').val := by omega
          exact h_u0_not_es (sub_left_inj.mp (Fin.ext this)).symm
        exact interior_anchor_caseA_R hPoly h25 hDB cycD hy_notD hord1 hord2 hord3 hord4 hy_tri
          hv_noncol hvq_D hvq_y hv_noncol_y h_seen_ss hy_cone_pos hy_orient_from_uv e_start e_end
          hib_far h_ge_v0 h2 (fun a b ha hb => (h_ang a b ha hb).2)
      · exact interior_anchor_caseA_Mid hPoly h25 hDB cycD hy_notD hord1 hord2 hord3 hord4 hy_tri
          hv_noncol hvq_D hvq_y hv_noncol_y h_seen_ss hy_cone_pos hy_orient_from_uv hy_orient_to_uv
          e_start e_end hib'_far (not_lt.mp h2) (fun a b ha hb => (h_ang a b ha hb).2)
  · push Not at h_ex
    have h_all_nf : ∀ m : Fin (kD + 3), 0 < orient2D (S (cycD.toFun m)) (S (cycD.toFun (m + 1))) v :=
      fun m => lt_of_le_of_ne (h_ex m) (hv_noncol m (m + 1) (fin_add_one_ne_self m)).symm
    by_cases hsee : Sees P v q
    · exact interior_anchor_caseB_see hPoly h25 hDB cycD hy_notD hord1 hord2 hord3 hy_tri
        hv_noncol hvq_D hvq_y hv_noncol_y hy_cone_pos hy_orient_from_uv h_all_nf hsee
    · exact interior_anchor_caseB_miss hPoly h25 hDB cycD hy_notD hord1 hord2 hord3 hord4
        hb'_nf hu0_nf hv0_nf hy_tri hv_noncol hvq_D h_seen_ss hy_cone_pos
        hy_orient_from_uv hy_orient_to_uv h_all_nf hsee

/-! ### Pentagon helpers for Lemma 6.7 (`pairs_in_M`) and Lemma 6.10 (`adjacent_exits`) -/

private lemma pentagon_all_nf_not_all_same {n : ℕ} {S : Fin n → ℝ × ℝ} {D : Finset (Fin n)}
    (cycD : CCWCycle S D 2) (v q : ℝ × ℝ)
    (h_all_nf : ∀ m : Fin 5, 0 < orient2D (S (cycD.toFun m)) (S (cycD.toFun (m + 1))) v)
    (hvq : ∀ m : Fin 5, orient2D v q (S (cycD.toFun m)) ≠ 0) :
    ¬ (∀ m : Fin 5, OnSameSide v q (S (cycD.toFun 0)) (S (cycD.toFun m))) := by
  intro hall
  rcases lt_or_gt_of_ne (hvq 0) with h0n | h0p
  · have hneg : ∀ m : Fin 5, orient2D v q (S (cycD.toFun m)) < 0 := fun m => by
      have hm := hall m; unfold OnSameSide at hm; nlinarith only [hm, h0n]
    have hstep : ∀ m : Fin 5, AngleLt v q (S (cycD.toFun (m + 1))) (S (cycD.toFun m)) := fun m => by
      rw [angleLt_iff_neg_of_neg (hneg (m + 1)) (hneg m)]
      have hf := h_all_nf m
      unfold orient2D at hf ⊢; linarith
    have hcyc : AngleLt v q (S (cycD.toFun 0)) (S (cycD.toFun 0)) :=
      (hstep 4).trans ((hstep 3).trans ((hstep 2).trans ((hstep 1).trans (hstep 0))))
    have h0 := hcyc.2
    rw [orient2D_self_right, mul_zero] at h0
    linarith
  · have hpos : ∀ m : Fin 5, 0 < orient2D v q (S (cycD.toFun m)) := fun m => by
      have hm := hall m; unfold OnSameSide at hm; nlinarith only [hm, h0p]
    have hstep : ∀ m : Fin 5, AngleLt v q (S (cycD.toFun m)) (S (cycD.toFun (m + 1))) := fun m => by
      rw [angleLt_iff_pos_of_pos (hpos m) (hpos (m + 1))]
      have hf := h_all_nf m
      unfold orient2D at hf ⊢; linarith
    have hcyc : AngleLt v q (S (cycD.toFun 0)) (S (cycD.toFun 0)) :=
      (hstep 0).trans ((hstep 1).trans ((hstep 2).trans ((hstep 3).trans (hstep 4))))
    have h0 := hcyc.2
    rw [orient2D_self_right, mul_zero] at h0
    linarith

private def noAltBool (a b c d : Bool) : Bool :=
  !(((a != b) && (b != c)) && (c != d))

private def pent_no_alt4 (s0 s1 s2 s3 s4 : Bool) : Bool :=
  noAltBool s0 s1 s2 s3 && noAltBool s0 s1 s2 s4 && noAltBool s0 s1 s3 s4 &&
  noAltBool s0 s2 s3 s4 && noAltBool s1 s2 s3 s4

private def forallBool (f : Bool → Bool) : Bool := f false && f true

private lemma forallBool_true {f : Bool → Bool} (h : forallBool f = true) (b : Bool) : f b = true := by
  cases b <;> simp only [forallBool, Bool.and_eq_true] at h
  · exact h.1
  · exact h.2

private def pent_pairs_check (s0 s1 s2 s3 s4 sy0 sy1 : Bool) : Bool :=
  if !(s0 == s1 && s0 == s2 && s0 == s3 && s0 == s4) &&
      pent_no_alt4 s0 s1 s2 s3 s4 &&
      (!(s0 == s1) || (sy0 == s0)) &&
      (!(s2 == s3) || (sy1 == s2))
  then (s4 == s0 && s0 == sy0) || (sy0 == s1 && s1 == s2 && s2 == sy1) || (sy1 == s3 && s3 == s4)
  else true

private lemma pent_pairs_all :
    forallBool (fun s0 => forallBool (fun s1 => forallBool (fun s2 =>
    forallBool (fun s3 => forallBool (fun s4 => forallBool (fun sy0 =>
    forallBool (fun sy1 => pent_pairs_check s0 s1 s2 s3 s4 sy0 sy1))))))) = true := rfl

private lemma not_all4_bool_true {s0 s1 s2 s3 s4 : Bool}
    (h : ¬ (s0 = s1 ∧ s0 = s2 ∧ s0 = s3 ∧ s0 = s4)) :
    (!(s0 == s1 && s0 == s2 && s0 == s3 && s0 == s4)) = true := by
  cases s0 <;> cases s1 <;> cases s2 <;> cases s3 <;> cases s4 <;>
    first | rfl | exact False.elim (h ⟨rfl, rfl, rfl, rfl⟩)

private lemma or_not_beq_eq_true {a b c : Bool} (h : a = b → c = a) :
    (!(a == b) || (c == a)) = true := by
  cases a <;> cases b <;> cases c <;>
    first | rfl | exact absurd (h rfl) (by decide)

private lemma pentagon_pairs_bool
    (s0 s1 s2 s3 s4 sy0 sy1 : Bool)
    (h_not_all : ¬ (s0 = s1 ∧ s0 = s2 ∧ s0 = s3 ∧ s0 = s4))
    (h_no_alt : pent_no_alt4 s0 s1 s2 s3 s4 = true)
    (h_y0 : s0 = s1 → sy0 = s0)
    (h_y1 : s2 = s3 → sy1 = s2) :
    (s4 = s0 ∧ s0 = sy0) ∨ (sy0 = s1 ∧ s1 = s2 ∧ s2 = sy1) ∨ (sy1 = s3 ∧ s3 = s4) := by
  have hc := forallBool_true (forallBool_true (forallBool_true (forallBool_true (forallBool_true
    (forallBool_true (forallBool_true pent_pairs_all s0) s1) s2) s3) s4) sy0) sy1
  have hprem : (!(s0 == s1 && s0 == s2 && s0 == s3 && s0 == s4) &&
      pent_no_alt4 s0 s1 s2 s3 s4 &&
      (!(s0 == s1) || (sy0 == s0)) &&
      (!(s2 == s3) || (sy1 == s2))) = true := by
    simp only [Bool.and_eq_true]
    exact ⟨⟨⟨not_all4_bool_true h_not_all, h_no_alt⟩, or_not_beq_eq_true h_y0⟩, or_not_beq_eq_true h_y1⟩
  simp only [pent_pairs_check, hprem, ↓reduceIte, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hc
  tauto

private def pent_adj_b4_check (s0 s1 s2 s3 s4 sy0 sy1 : Bool) : Bool :=
  if !(s0 == s1 && s0 == s2 && s0 == s3 && s0 == s4) &&
      pent_no_alt4 s0 s1 s2 s3 s4 &&
      (!(s0 == s1) || (sy0 == s0)) &&
      (!(s1 == s2) || (sy1 == s1))
  then (s4 == s0 && s0 == sy0) || (sy0 == s1 && s1 == sy1) || (sy1 == s2 && s2 == s3 && s3 == s4)
  else true

private lemma pent_adj_b4_all :
    forallBool (fun s0 => forallBool (fun s1 => forallBool (fun s2 =>
    forallBool (fun s3 => forallBool (fun s4 => forallBool (fun sy0 =>
    forallBool (fun sy1 => pent_adj_b4_check s0 s1 s2 s3 s4 sy0 sy1))))))) = true := rfl

private lemma pentagon_adj_b4_bool
    (s0 s1 s2 s3 s4 sy0 sy1 : Bool)
    (h_not_all : ¬ (s0 = s1 ∧ s0 = s2 ∧ s0 = s3 ∧ s0 = s4))
    (h_no_alt : pent_no_alt4 s0 s1 s2 s3 s4 = true)
    (h_y0 : s0 = s1 → sy0 = s0)
    (h_y1 : s1 = s2 → sy1 = s1) :
    (s4 = s0 ∧ s0 = sy0) ∨ (sy0 = s1 ∧ s1 = sy1) ∨ (sy1 = s2 ∧ s2 = s3 ∧ s3 = s4) := by
  have hc := forallBool_true (forallBool_true (forallBool_true (forallBool_true (forallBool_true
    (forallBool_true (forallBool_true pent_adj_b4_all s0) s1) s2) s3) s4) sy0) sy1
  have hprem : (!(s0 == s1 && s0 == s2 && s0 == s3 && s0 == s4) &&
      pent_no_alt4 s0 s1 s2 s3 s4 &&
      (!(s0 == s1) || (sy0 == s0)) &&
      (!(s1 == s2) || (sy1 == s1))) = true := by
    simp only [Bool.and_eq_true]
    exact ⟨⟨⟨not_all4_bool_true h_not_all, h_no_alt⟩, or_not_beq_eq_true h_y0⟩, or_not_beq_eq_true h_y1⟩
  simp only [pent_adj_b4_check, hprem, ↓reduceIte, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hc
  tauto

private def pent_adj_b3_check (s0 s1 s2 s3 s4 sy0 sy1 : Bool) : Bool :=
  if !(s0 == s1 && s0 == s2 && s0 == s3 && s0 == s4) &&
      pent_no_alt4 s0 s1 s2 s3 s4 &&
      (!(s0 == s1) || (sy0 == s0)) &&
      (!(s1 == s2) || (sy1 == s1))
  then (s3 == s4 && s4 == s0 && s0 == sy0) || (sy0 == s1 && s1 == sy1) || (sy1 == s2 && s2 == s3)
  else true

private lemma pent_adj_b3_all :
    forallBool (fun s0 => forallBool (fun s1 => forallBool (fun s2 =>
    forallBool (fun s3 => forallBool (fun s4 => forallBool (fun sy0 =>
    forallBool (fun sy1 => pent_adj_b3_check s0 s1 s2 s3 s4 sy0 sy1))))))) = true := rfl

private lemma pentagon_adj_b3_bool
    (s0 s1 s2 s3 s4 sy0 sy1 : Bool)
    (h_not_all : ¬ (s0 = s1 ∧ s0 = s2 ∧ s0 = s3 ∧ s0 = s4))
    (h_no_alt : pent_no_alt4 s0 s1 s2 s3 s4 = true)
    (h_y0 : s0 = s1 → sy0 = s0)
    (h_y1 : s1 = s2 → sy1 = s1) :
    (s3 = s4 ∧ s4 = s0 ∧ s0 = sy0) ∨ (sy0 = s1 ∧ s1 = sy1) ∨ (sy1 = s2 ∧ s2 = s3) := by
  have hc := forallBool_true (forallBool_true (forallBool_true (forallBool_true (forallBool_true
    (forallBool_true (forallBool_true pent_adj_b3_all s0) s1) s2) s3) s4) sy0) sy1
  have hprem : (!(s0 == s1 && s0 == s2 && s0 == s3 && s0 == s4) &&
      pent_no_alt4 s0 s1 s2 s3 s4 &&
      (!(s0 == s1) || (sy0 == s0)) &&
      (!(s1 == s2) || (sy1 == s1))) = true := by
    simp only [Bool.and_eq_true]
    exact ⟨⟨⟨not_all4_bool_true h_not_all, h_no_alt⟩, or_not_beq_eq_true h_y0⟩, or_not_beq_eq_true h_y1⟩
  simp only [pent_adj_b3_check, hprem, ↓reduceIte, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hc
  tauto

private noncomputable def posBool (x : ℝ) : Bool := if 0 < x then true else false

private lemma posBool_eq_iff (x y : ℝ) : posBool x = posBool y ↔ (0 < x ↔ 0 < y) := by
  by_cases hx : 0 < x <;> by_cases hy : 0 < y <;> simp [posBool, hx, hy]

private lemma ccwCycle_ccw3_of_lt {n k : ℕ} {S : Fin n → ℝ × ℝ} {D : Finset (Fin n)}
    (cycD : CCWCycle S D k) {a b c : Fin (k + 3)} (hab : a < b) (hbc : b < c) :
    0 < orient2D (S (cycD.toFun a)) (S (cycD.toFun b)) (S (cycD.toFun c)) := by
  have h1 : 0 < (b - a).val := by rw [fin_val_sub_eq, if_pos (le_of_lt hab)]; exact Nat.sub_pos_of_lt hab
  have h2 : (b - a).val < (c - a).val := by
    rw [fin_val_sub_eq, if_pos (le_of_lt hab), fin_val_sub_eq, if_pos (le_of_lt (lt_trans hab hbc))]
    omega
  exact ccwCycle_ccw3 cycD h1 h2

private lemma pent_no_alt4_of_orient {n : ℕ} {S : Fin n → ℝ × ℝ} {D : Finset (Fin n)}
    (cycD : CCWCycle S D 2) (v q : ℝ × ℝ)
    (hvq : ∀ m : Fin 5, orient2D v q (S (cycD.toFun m)) ≠ 0) :
    pent_no_alt4
      (posBool (orient2D v q (S (cycD.toFun 0))))
      (posBool (orient2D v q (S (cycD.toFun 1))))
      (posBool (orient2D v q (S (cycD.toFun 2))))
      (posBool (orient2D v q (S (cycD.toFun 3))))
      (posBool (orient2D v q (S (cycD.toFun 4)))) = true := by
  have h4 : ∀ a b c d : Fin 5, a < b → b < c → c < d →
      noAltBool (posBool (orient2D v q (S (cycD.toFun a))))
        (posBool (orient2D v q (S (cycD.toFun b))))
        (posBool (orient2D v q (S (cycD.toFun c))))
        (posBool (orient2D v q (S (cycD.toFun d)))) = true := by
    intro a b c d hab hbc hcd
    have hbcd := ccwCycle_ccw3_of_lt cycD hbc hcd
    have hcab : 0 < orient2D (S (cycD.toFun c)) (S (cycD.toFun d)) (S (cycD.toFun a)) := by
      have h := ccwCycle_ccw3_of_lt cycD (lt_trans hab hbc) hcd; unfold orient2D at h ⊢; linarith
    have hdab : 0 < orient2D (S (cycD.toFun d)) (S (cycD.toFun a)) (S (cycD.toFun b)) := by
      have h := ccwCycle_ccw3_of_lt cycD hab (lt_trans hbc hcd); unfold orient2D at h ⊢; linarith
    have habc := ccwCycle_ccw3_of_lt cycD hab hbc
    have halt := convex_fourgon_no_alternating_line
      (S (cycD.toFun a)) (S (cycD.toFun b)) (S (cycD.toFun c)) (S (cycD.toFun d)) v q
      hbcd hcab hdab habc
    rcases lt_or_gt_of_ne (hvq a) with ha | ha <;>
    rcases lt_or_gt_of_ne (hvq b) with hb | hb <;>
    rcases lt_or_gt_of_ne (hvq c) with hc | hc <;>
    rcases lt_or_gt_of_ne (hvq d) with hd | hd <;>
      simp [noAltBool, posBool, not_lt_of_gt, ha, hb, hc, hd] at halt ⊢
  dsimp [pent_no_alt4]
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨⟨h4 0 1 2 3 ?_ ?_ ?_, h4 0 1 2 4 ?_ ?_ ?_⟩, h4 0 1 3 4 ?_ ?_ ?_⟩, h4 0 2 3 4 ?_ ?_ ?_⟩, h4 1 2 3 4 ?_ ?_ ?_⟩ <;>
    decide

private lemma orient2D_chain3_pos {v q a b c : ℝ × ℝ}
    (hq_eq : posBool (orient2D v q a) = posBool (orient2D v q b) ∧
             posBool (orient2D v q b) = posBool (orient2D v q c))
    (hqa : orient2D v q a ≠ 0) (hqb : orient2D v q b ≠ 0) (hqc : orient2D v q c ≠ 0)
    (hab : 0 < orient2D v a b) (hbc : 0 < orient2D v b c) :
    0 < orient2D v a c := by
  rw [posBool_eq_iff, posBool_eq_iff] at hq_eq
  by_cases ha : 0 < orient2D v q a
  · have hb : 0 < orient2D v q b := hq_eq.1.mp ha
    have hc : 0 < orient2D v q c := hq_eq.2.mp hb
    have h1 := ((angleLt_iff_pos_of_pos ha hb).mpr hab).trans ((angleLt_iff_pos_of_pos hb hc).mpr hbc)
    exact (angleLt_iff_pos_of_pos ha hc).mp h1
  · have ha' : orient2D v q a < 0 := lt_of_le_of_ne (not_lt.mp ha) hqa
    have hb' : orient2D v q b < 0 := lt_of_le_of_ne (not_lt.mp (mt hq_eq.1.mpr ha)) hqb
    have hc' : orient2D v q c < 0 := lt_of_le_of_ne (not_lt.mp (mt hq_eq.2.mpr (mt hq_eq.1.mpr ha))) hqc
    have hab' : orient2D v b a < 0 := by unfold orient2D at hab ⊢; linarith
    have hbc' : orient2D v c b < 0 := by unfold orient2D at hbc ⊢; linarith
    have h1 := ((angleLt_iff_neg_of_neg hc' hb').mpr hbc').trans ((angleLt_iff_neg_of_neg hb' ha').mpr hab')
    have hca : orient2D v c a < 0 := (angleLt_iff_neg_of_neg hc' ha').mp h1
    unfold orient2D at hca ⊢; linarith

private lemma orient2D_chain4_pos {v q a b c d : ℝ × ℝ}
    (hq_eq : posBool (orient2D v q a) = posBool (orient2D v q b) ∧
             posBool (orient2D v q b) = posBool (orient2D v q c) ∧
             posBool (orient2D v q c) = posBool (orient2D v q d))
    (hqa : orient2D v q a ≠ 0) (hqb : orient2D v q b ≠ 0)
    (hqc : orient2D v q c ≠ 0) (hqd : orient2D v q d ≠ 0)
    (hab : 0 < orient2D v a b) (hbc : 0 < orient2D v b c) (hcd : 0 < orient2D v c d) :
    0 < orient2D v a c ∧ 0 < orient2D v b d ∧ 0 < orient2D v a d := by
  have hac := orient2D_chain3_pos ⟨hq_eq.1, hq_eq.2.1⟩ hqa hqb hqc hab hbc
  have hbd := orient2D_chain3_pos ⟨hq_eq.2.1, hq_eq.2.2⟩ hqb hqc hqd hbc hcd
  have had := orient2D_chain3_pos ⟨hq_eq.1, hq_eq.2.1.trans hq_eq.2.2⟩ hqa hqb hqd hab hbd
  exact ⟨hac, hbd, had⟩

private lemma exitTri_convex_comb_orient_pos {v u0 v0 y a b : ℝ × ℝ}
    (hy : InIntTri v u0 v0 y)
    (hv : 0 < orient2D a b v) (hu0 : 0 ≤ orient2D a b u0) (hv0 : 0 ≤ orient2D a b v0) :
    0 < orient2D a b y := by
  rcases hy with ⟨μ₁, μ₂, μ₃, hm1, hm2, hm3, hs, hy1, hy2⟩
  have hid := orient2D_convex_comb3 a b v u0 v0 y μ₁ μ₂ μ₃ hs hy1 hy2
  rw [hid]
  exact add_pos_of_pos_of_nonneg
    (add_pos_of_pos_of_nonneg (mul_pos hm1 hv) (mul_nonneg (le_of_lt hm2) hu0))
    (mul_nonneg (le_of_lt hm3) hv0)

private lemma exitTri_posBool_of_endpoints {v q u0 v0 y : ℝ × ℝ}
    (hy : InIntTri v u0 v0 y)
    (heq : posBool (orient2D v q u0) = posBool (orient2D v q v0)) :
    posBool (orient2D v q y) = posBool (orient2D v q u0) := by
  rcases hy with ⟨_, μ₂, μ₃, _, hm2, hm3, hs, hy1, hy2⟩
  have hid := orient2D_convex_comb3 v q v u0 v0 y _ _ _ hs hy1 hy2
  rw [orient2D_self_outer, mul_zero, zero_add] at hid
  rw [posBool_eq_iff] at heq ⊢
  constructor <;> intro h
  · by_contra hnu0
    have hnv0 : ¬ 0 < orient2D v q v0 := fun hv0 => hnu0 (heq.mpr hv0)
    have h1 := mul_nonpos_of_nonneg_of_nonpos (le_of_lt hm2) (not_lt.mp hnu0)
    have h2 := mul_nonpos_of_nonneg_of_nonpos (le_of_lt hm3) (not_lt.mp hnv0)
    linarith
  · have hv0 : 0 < orient2D v q v0 := heq.mp h
    rw [hid]; exact add_pos (mul_pos hm2 h) (mul_pos hm3 hv0)

private lemma orient2D_vq_between_sameSide {v q a m b : ℝ × ℝ}
    (hss : OnSameSide v q a b) (hqa : orient2D v q a ≠ 0)
    (hab : 0 < orient2D v a b) (ham : 0 < orient2D v a m) (hmb : 0 < orient2D v m b) :
    OnSameSide v q a m := by
  have hid := orient2D_angle_trans_id v q a m b
  unfold OnSameSide at hss ⊢
  rcases lt_or_gt_of_ne hqa with ha | ha
  · have hb : orient2D v q b < 0 := by nlinarith only [hss, ha]
    have hm : orient2D v q m < 0 := by nlinarith only [hid, ha, hb, hab, ham, hmb]
    exact mul_pos_of_neg_of_neg ha hm
  · have hb : 0 < orient2D v q b := by nlinarith only [hss, ha]
    have hm : 0 < orient2D v q m := by nlinarith only [hid, ha, hb, hab, ham, hmb]
    exact mul_pos ha hm

private lemma posBool_eq_of_onSameSide {v q a b : ℝ × ℝ}
    (hss : OnSameSide v q a b) : posBool (orient2D v q a) = posBool (orient2D v q b) := by
  rw [posBool_eq_iff]
  unfold OnSameSide at hss
  constructor <;> intro h <;> nlinarith only [hss, h]

private lemma onSameSide_of_posBool_eq {v q a b : ℝ × ℝ}
    (heq : posBool (orient2D v q a) = posBool (orient2D v q b))
    (hqa : orient2D v q a ≠ 0) (hqb : orient2D v q b ≠ 0) :
    OnSameSide v q a b := by
  rw [posBool_eq_iff] at heq
  unfold OnSameSide
  by_cases ha : 0 < orient2D v q a
  · exact mul_pos ha (heq.mp ha)
  · exact mul_pos_of_neg_of_neg (lt_of_le_of_ne (not_lt.mp ha) hqa)
      (lt_of_le_of_ne (not_lt.mp (mt heq.mpr ha)) hqb)

private lemma exitTri_orient2D_from_left {v u0 v0 y : ℝ × ℝ}
    (hy : InIntTri v u0 v0 y) (hnf : 0 < orient2D u0 v0 v) :
    0 < orient2D v u0 y ∧ 0 < orient2D v y v0 ∧ 0 < orient2D v u0 v0 := by
  have hccw : 0 < orient2D v u0 v0 := by unfold orient2D at hnf ⊢; linarith
  have hin := (inIntTri_iff_orient_pos hccw).mp hy
  refine ⟨hin.1, ?_, hccw⟩
  unfold orient2D at hin ⊢; linarith [hin.2.2]

private lemma exitTri_orient_before {v u0 v0 y a : ℝ × ℝ}
    (hy : InIntTri v u0 v0 y) (ha_u : 0 < orient2D v a u0) (ha_v : 0 < orient2D v a v0) :
    0 < orient2D v a y := by
  rcases hy with ⟨_, μ₂, μ₃, _, hm2, hm3, hs, hy1, hy2⟩
  have hid := orient2D_convex_comb3 v a v u0 v0 y _ _ _ hs hy1 hy2
  rw [orient2D_self_outer, mul_zero, zero_add] at hid
  rw [hid]; exact add_pos (mul_pos hm2 ha_u) (mul_pos hm3 ha_v)

private lemma exitTri_orient_after {v u0 v0 y b : ℝ × ℝ}
    (hy : InIntTri v u0 v0 y) (hu_b : 0 < orient2D v u0 b) (hv_b : 0 < orient2D v v0 b) :
    0 < orient2D v y b := by
  rcases hy with ⟨_, μ₂, μ₃, _, hm2, hm3, hs, hy1, hy2⟩
  have hid := orient2D_convex_comb3 v b v u0 v0 y _ _ _ hs hy1 hy2
  rw [orient2D_self_outer, mul_zero, zero_add] at hid
  unfold orient2D at hid hu_b hv_b ⊢; nlinarith only [hid, hm2, hm3, hu_b, hv_b]

private lemma exitTri_sameSide_of_in_L {v q u0 v0 y : ℝ × ℝ}
    (hy : InIntTri v u0 v0 y) (hss : OnSameSide v q u0 v0) :
    OnSameSide v q u0 y ∧ OnSameSide v q y v0 := by
  have heq := exitTri_posBool_of_endpoints hy (posBool_eq_of_onSameSide hss)
  have hqu : orient2D v q u0 ≠ 0 := fun h => by unfold OnSameSide at hss; rw [h, zero_mul] at hss; linarith
  have hqv : orient2D v q v0 ≠ 0 := fun h => by unfold OnSameSide at hss; rw [h, mul_zero] at hss; linarith
  have hqy : orient2D v q y ≠ 0 := by
    rw [posBool_eq_iff] at heq
    rcases lt_or_gt_of_ne hqu with hn | hp
    · rcases hy with ⟨_, μ₂, μ₃, _, hm2, hm3, hs, hy1, hy2⟩
      have hid := orient2D_convex_comb3 v q v u0 v0 y _ _ _ hs hy1 hy2
      rw [orient2D_self_outer, mul_zero, zero_add] at hid
      have hvn : orient2D v q v0 < 0 := by unfold OnSameSide at hss; nlinarith only [hss, hn]
      rw [hid]; exact ne_of_lt (add_neg (mul_neg_of_pos_of_neg hm2 hn) (mul_neg_of_pos_of_neg hm3 hvn))
    · exact ne_of_gt (heq.mpr hp)
  exact ⟨onSameSide_of_posBool_eq heq.symm hqu hqy,
    onSameSide_of_posBool_eq (heq.trans (posBool_eq_of_onSameSide hss)) hqy hqv⟩


/-- Helper: `O* = {cycD.toFun ib, y0, y1}` non-collinearity, witness separation, and `ib` non-front
    facts on a pentagon `CCWCycle S D 2`. -/
private lemma pentagon_Ostar_core {n : ℕ} {P : Set (ℝ × ℝ)}
    {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ}
    (hPoly : ShatteredSimplePolygon P S w) (h25 : Sec2To5Interface P S w)
    {D : Finset (Fin n)} (hDB : D = hullVertices S \ certifiedVertices S w)
    (cycD : CCWCycle S D 2)
    {y0 y1 : Fin n} (hy0M : y0 ∈ Finset.univ \ D) (hy1M : y1 ∈ Finset.univ \ D) (hy01 : y0 ≠ y1)
    (ib : Fin 5) :
    let O_star : Finset (Fin n) := {cycD.toFun ib, y0, y1}
    let v := w (Finset.univ \ O_star)
    let q := w Finset.univ
    (∀ m : Fin 5, m ≠ ib → cycD.toFun m ∉ O_star) ∧
    (¬ IsFrontVertexOf S D (cycD.toFun ib) v) ∧
    (∀ i j : Fin 5, i ≠ j → orient2D (S (cycD.toFun i)) (S (cycD.toFun j)) v ≠ 0) ∧
    (∀ i : Fin 5, orient2D v q (S (cycD.toFun i)) ≠ 0) ∧
    (orient2D v q (S y0) ≠ 0) ∧
    (orient2D v q (S y1) ≠ 0) ∧
    (∀ a b : Fin n, a ∉ O_star → b ∉ O_star → ¬ Sees P v q → OnSameSide v q (S a) (S b)) := by
  intro O_star v q
  have hy0_notD : y0 ∉ D := (Finset.mem_sdiff.mp hy0M).2
  have hy1_notD : y1 ∉ D := (Finset.mem_sdiff.mp hy1M).2
  have hm_out : ∀ m : Fin 5, m ≠ ib → cycD.toFun m ∉ O_star := by
    intro m hmb hmO
    simp only [O_star, Finset.mem_insert, Finset.mem_singleton] at hmO
    rcases hmO with h | h | h
    · exact hmb (cycD.inj h)
    · exact hy0_notD (h ▸ ccwCycle_mem cycD m)
    · exact hy1_notD (h ▸ ccwCycle_mem cycD m)
  have hb_nf : ¬ IsFrontVertexOf S D (cycD.toFun ib) v := by
    refine no_odd_front hPoly h25 (hDB ▸ Subset.rfl) (by
      rw [← cycD.image_eq, Finset.card_image_of_injective Finset.univ cycD.inj, Finset.card_fin]; omega)
      (ccwCycle_mem cycD ib)
      (fun h => (Finset.mem_sdiff.mp h).2 (Finset.mem_insert_self _ _))
      (fun x hxD hadj => ?_)
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun hxO => ?_⟩
    simp only [O_star, Finset.mem_insert, Finset.mem_singleton] at hxO
    rcases hxO with rfl | rfl | rfl
    · rcases hadj with e | e <;> exact e.2.2.1 rfl
    · exact hy0_notD hxD
    · exact hy1_notD hxD
  have hv_ne_q : v ≠ q := by
    intro h
    have hy0s : Sees P v (S y0) := by rw [h]; exact (hPoly.shatters Finset.univ y0).mpr (Finset.mem_univ _)
    have hy0T := (hPoly.shatters (Finset.univ \ O_star) y0).mp hy0s
    exact (Finset.mem_sdiff.mp hy0T).2 (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
  have hv_noncol : ∀ i j : Fin 5, i ≠ j → orient2D (S (cycD.toFun i)) (S (cycD.toFun j)) v ≠ 0 :=
    fun i j hij => hPoly.no_three_collinear _ _ _
      (Or.inl (Set.mem_range_self _)) (Or.inl (Set.mem_range_self _)) (Or.inr (Set.mem_range_self _))
      (hPoly.s_inj.ne (cycD.inj.ne hij)) (hPoly.s_ne_w _ _) (hPoly.s_ne_w _ _)
  have hvq_D : ∀ i : Fin 5, orient2D v q (S (cycD.toFun i)) ≠ 0 :=
    fun i => hPoly.no_three_collinear _ _ _
      (Or.inr (Set.mem_range_self _)) (Or.inr (Set.mem_range_self _)) (Or.inl (Set.mem_range_self _))
      (hPoly.w_inj.ne (fun h => hv_ne_q (congrArg w h))) (hPoly.s_ne_w _ _).symm (hPoly.s_ne_w _ _).symm
  have hvq_y0 : orient2D v q (S y0) ≠ 0 :=
    hPoly.no_three_collinear _ _ _
      (Or.inr (Set.mem_range_self _)) (Or.inr (Set.mem_range_self _)) (Or.inl (Set.mem_range_self _))
      (hPoly.w_inj.ne (fun h => hv_ne_q (congrArg w h))) (hPoly.s_ne_w _ _).symm (hPoly.s_ne_w _ _).symm
  have hvq_y1 : orient2D v q (S y1) ≠ 0 :=
    hPoly.no_three_collinear _ _ _
      (Or.inr (Set.mem_range_self _)) (Or.inr (Set.mem_range_self _)) (Or.inl (Set.mem_range_self _))
      (hPoly.w_inj.ne (fun h => hv_ne_q (congrArg w h))) (hPoly.s_ne_w _ _).symm (hPoly.s_ne_w _ _).symm
  have h_seen_ss : ∀ a b : Fin n, a ∉ O_star → b ∉ O_star → ¬ Sees P v q → OnSameSide v q (S a) (S b) := by
    intro a b haO hbO hnq
    have hsa := (hPoly.shatters (Finset.univ \ O_star) a).mpr (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, haO⟩)
    have hsb := (hPoly.shatters (Finset.univ \ O_star) b).mpr (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hbO⟩)
    have hqa := (hPoly.shatters Finset.univ a).mpr (Finset.mem_univ _)
    have hqb := (hPoly.shatters Finset.univ b).mpr (Finset.mem_univ _)
    by_contra hnot
    have hna : orient2D v q (S a) ≠ 0 := hPoly.no_three_collinear _ _ _
      (Or.inr (Set.mem_range_self _)) (Or.inr (Set.mem_range_self _)) (Or.inl (Set.mem_range_self _))
      (hPoly.w_inj.ne (fun h => hv_ne_q (congrArg w h))) (hPoly.s_ne_w _ _).symm (hPoly.s_ne_w _ _).symm
    have hnb : orient2D v q (S b) ≠ 0 := hPoly.no_three_collinear _ _ _
      (Or.inr (Set.mem_range_self _)) (Or.inr (Set.mem_range_self _)) (Or.inl (Set.mem_range_self _))
      (hPoly.w_inj.ne (fun h => hv_ne_q (congrArg w h))) (hPoly.s_ne_w _ _).symm (hPoly.s_ne_w _ _).symm
    have hneg : orient2D v q (S a) * orient2D v q (S b) < 0 :=
      lt_of_le_of_ne (not_lt.mp hnot) (mul_ne_zero hna hnb)
    rcases lt_or_gt_of_ne hna with han | hap
    · have hbp : 0 < orient2D v q (S b) := by nlinarith
      exact hnq (hPoly.two_path_enclosure v q [v, S b, q] [v, S a, q] hv_ne_q
        (isPolygonalPathIn_three hsb (sees_symm hqb)) (isPolygonalPathIn_three hsa (sees_symm hqa))
        ⟨le_rfl, fun k hk hk0 hk1 => by have hke : k = 1 := by dsimp at hk1; omega
                                        subst hke; exact hbp⟩
        ⟨le_rfl, fun k hk hk0 hk1 => by have hke : k = 1 := by dsimp at hk1; omega
                                        subst hke; exact han⟩)
    · have hbn : orient2D v q (S b) < 0 := by nlinarith
      exact hnq (hPoly.two_path_enclosure v q [v, S a, q] [v, S b, q] hv_ne_q
        (isPolygonalPathIn_three hsa (sees_symm hqa)) (isPolygonalPathIn_three hsb (sees_symm hqb))
        ⟨le_rfl, fun k hk hk0 hk1 => by have hke : k = 1 := by dsimp at hk1; omega
                                        subst hke; exact hap⟩
        ⟨le_rfl, fun k hk hk0 hk1 => by have hke : k = 1 := by dsimp at hk1; omega
                                        subst hke; exact hbn⟩)
  exact ⟨hm_out, hb_nf, hv_noncol, hvq_D, hvq_y0, hvq_y1, h_seen_ss⟩

/-- Helper: derive `0 < orient2D (S (cycD i)) (S (cycD (i+1))) v` for an exit edge `(i, i+1)`. -/
private lemma pentagon_exit_nonfacing {n : ℕ} {P : Set (ℝ × ℝ)}
    {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ}
    (hPoly : ShatteredSimplePolygon P S w) (h25 : Sec2To5Interface P S w)
    {D : Finset (Fin n)} (hDB : D = hullVertices S \ certifiedVertices S w)
    (cycD : CCWCycle S D 2) {y : Fin n} (hyM : y ∈ Finset.univ \ D)
    {v : ℝ × ℝ} (i : Fin 5)
    (hy_tri : InIntTri v (S (cycD.toFun i)) (S (cycD.toFun (i + 1))) (S y))
    (h_not_lr : ∀ l r : Fin n, (certifiedVertices S w).Nonempty →
      IsCCWEdge S D l r → (∀ h ∈ certifiedVertices S w, orient2D (S l) (S r) (S h) < 0) →
      (cycD.toFun i, cycD.toFun (i + 1)) ≠ (l, r)) :
    0 < orient2D (S (cycD.toFun i)) (S (cycD.toFun (i + 1))) v := by
  have hy_notD : y ∉ D := (Finset.mem_sdiff.mp hyM).2
  have he_D : IsCCWEdge S D (cycD.toFun i) (cycD.toFun (i + 1)) := ccwCycle_isCCWEdge cycD i
  have hD3 : 3 ≤ D.card := by
    rw [← cycD.image_eq, Finset.card_image_of_injective Finset.univ cycD.inj, Finset.card_fin]; omega
  have he_B := isCCWEdge_B_of_D_ne_lr h25 (hDB ▸ hD3) (hDB ▸ he_D)
    (fun l r hH _ _ _ hlrD hHn => h_not_lr l r hH (hDB ▸ hlrD) hHn)
  have hccw : 0 < orient2D (S (cycD.toFun i)) (S (cycD.toFun (i + 1))) (S y) :=
    orient2D_pos_of_isCCWEdge_B hPoly he_B
      (fun h => hy_notD (h ▸ ccwCycle_mem cycD i))
      (fun h => hy_notD (h ▸ ccwCycle_mem cycD (i + 1)))
  rcases hy_tri with ⟨μ₁, _, _, hm1, _, _, hs, hy1, hy2⟩
  have hid : orient2D (S (cycD.toFun i)) (S (cycD.toFun (i + 1))) (S y) =
      μ₁ * orient2D (S (cycD.toFun i)) (S (cycD.toFun (i + 1))) v := by
    unfold orient2D; rw [hy1, hy2]
    linear_combination ((S (cycD.toFun i)).2 * (S (cycD.toFun (i + 1))).1 -
      (S (cycD.toFun i)).1 * (S (cycD.toFun (i + 1))).2) * hs
  nlinarith

private def fin5PairsCheck (i : Fin 5) (L0 : Fin 4) : Bool :=
  let Lv := L0.val + 1
  let e_end := i + finNat 5 Lv
  let bad := decide ((0 - i).val < Lv) || decide ((2 - i).val < Lv) ||
    (decide ((3 - i).val < Lv) && decide ((4 - i).val < Lv))
  if bad then true else
    (i == 1 && e_end == 2 && Lv == 1) || (i == 3 && e_end == 4 && Lv == 1) || (i == 4 && e_end == 0 && Lv == 1)

private lemma fin5PairsCheck_all :
    (List.finRange 5).all (fun i => (List.finRange 4).all (fun L0 => fin5PairsCheck i L0)) = true := rfl

private lemma pent_facing_cases_pairs (e_start e_end : Fin 5) (L : ℕ)
    (hL1 : 1 ≤ L) (hL4 : L ≤ 4) (heq : e_end = e_start + finNat 5 L)
    (h0 : ¬ (0 - e_start).val < L) (h2 : ¬ (2 - e_start).val < L)
    (h34 : ¬ ((3 - e_start).val < L ∧ (4 - e_start).val < L)) :
    (e_start = 1 ∧ e_end = 2 ∧ L = 1) ∨ (e_start = 3 ∧ e_end = 4 ∧ L = 1) ∨
    (e_start = 4 ∧ e_end = 0 ∧ L = 1) := by
  let L0 : Fin 4 := ⟨L - 1, by omega⟩
  have hLv : L0.val + 1 = L := by dsimp [L0]; omega
  have h1 := List.all_eq_true.mp fin5PairsCheck_all e_start (List.mem_finRange _)
  have h2' := List.all_eq_true.mp h1 L0 (List.mem_finRange _)
  dsimp [fin5PairsCheck] at h2'
  rw [hLv, ← heq] at h2'
  have hbad : (decide ((0 - e_start).val < L) || decide ((2 - e_start).val < L) ||
      (decide ((3 - e_start).val < L) && decide ((4 - e_start).val < L))) = false := by
    simp only [Bool.or_eq_false_iff, Bool.and_eq_false_iff, decide_eq_false_iff_not]
    refine ⟨⟨h0, h2⟩, ?_⟩
    by_cases h3 : (3 - e_start).val < L
    · exact Or.inr (fun h4 => h34 ⟨h3, h4⟩)
    · exact Or.inl h3
  rw [hbad] at h2'
  simp only [Bool.false_eq_true, ↓reduceIte, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h2'
  tauto

private def fin5AdjB4Check (i : Fin 5) (L0 : Fin 4) : Bool :=
  let Lv := L0.val + 1
  let e_end := i + finNat 5 Lv
  let bad := decide ((0 - i).val < Lv) || decide ((1 - i).val < Lv) ||
    (decide ((3 - i).val < Lv) && decide ((4 - i).val < Lv))
  if bad then true else
    (i == 4 && e_end == 0 && Lv == 1) ||
    (decide ((4 - e_end).val < (0 - e_end).val) &&
     decide ((0 - e_end).val < (1 - e_end).val) &&
     decide ((1 - e_end).val < (2 - e_end).val) &&
     decide ((2 - e_end).val ≤ (i - e_end).val))

private lemma fin5AdjB4Check_all :
    (List.finRange 5).all (fun i => (List.finRange 4).all (fun L0 => fin5AdjB4Check i L0)) = true := rfl

private lemma pent_facing_cases_adjB4 (e_start e_end : Fin 5) (L : ℕ)
    (hL1 : 1 ≤ L) (hL4 : L ≤ 4) (heq : e_end = e_start + finNat 5 L)
    (h0 : ¬ (0 - e_start).val < L) (h1 : ¬ (1 - e_start).val < L)
    (h34 : ¬ ((3 - e_start).val < L ∧ (4 - e_start).val < L)) :
    (e_start = 4 ∧ e_end = 0 ∧ L = 1) ∨
    ((4 - e_end : Fin 5).val < (0 - e_end : Fin 5).val ∧
     (0 - e_end : Fin 5).val < (1 - e_end : Fin 5).val ∧
     (1 - e_end : Fin 5).val < (2 - e_end : Fin 5).val ∧
     (2 - e_end : Fin 5).val ≤ (e_start - e_end : Fin 5).val) := by
  let L0 : Fin 4 := ⟨L - 1, by omega⟩
  have hLv : L0.val + 1 = L := by dsimp [L0]; omega
  have h1' := List.all_eq_true.mp fin5AdjB4Check_all e_start (List.mem_finRange _)
  have h2' := List.all_eq_true.mp h1' L0 (List.mem_finRange _)
  dsimp [fin5AdjB4Check] at h2'
  rw [hLv, ← heq] at h2'
  have hbad : (decide ((0 - e_start).val < L) || decide ((1 - e_start).val < L) ||
      (decide ((3 - e_start).val < L) && decide ((4 - e_start).val < L))) = false := by
    simp only [Bool.or_eq_false_iff, Bool.and_eq_false_iff, decide_eq_false_iff_not]
    refine ⟨⟨h0, h1⟩, ?_⟩
    by_cases h3 : (3 - e_start).val < L
    · exact Or.inr (fun h4 => h34 ⟨h3, h4⟩)
    · exact Or.inl h3
  rw [hbad] at h2'
  simp only [Bool.false_eq_true, ↓reduceIte, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h2'
  tauto

private def fin5AdjB3Check (i : Fin 5) (L0 : Fin 4) : Bool :=
  let Lv := L0.val + 1
  let e_end := i + finNat 5 Lv
  let bad := decide ((0 - i).val < Lv) || decide ((1 - i).val < Lv) ||
    (decide ((2 - i).val < Lv) && decide ((3 - i).val < Lv))
  if bad then true else
    (i == 2 && e_end == 3 && Lv == 1) ||
    (decide ((0 - e_end).val < (1 - e_end).val) &&
     decide ((1 - e_end).val < (2 - e_end).val) &&
     decide ((2 - e_end).val < (3 - e_end).val) &&
     decide ((3 - e_end).val ≤ (i - e_end).val))

private lemma fin5AdjB3Check_all :
    (List.finRange 5).all (fun i => (List.finRange 4).all (fun L0 => fin5AdjB3Check i L0)) = true := rfl

private lemma pent_facing_cases_adjB3 (e_start e_end : Fin 5) (L : ℕ)
    (hL1 : 1 ≤ L) (hL4 : L ≤ 4) (heq : e_end = e_start + finNat 5 L)
    (h0 : ¬ (0 - e_start).val < L) (h1 : ¬ (1 - e_start).val < L)
    (h23 : ¬ ((2 - e_start).val < L ∧ (3 - e_start).val < L)) :
    (e_start = 2 ∧ e_end = 3 ∧ L = 1) ∨
    ((0 - e_end : Fin 5).val < (1 - e_end : Fin 5).val ∧
     (1 - e_end : Fin 5).val < (2 - e_end : Fin 5).val ∧
     (2 - e_end : Fin 5).val < (3 - e_end : Fin 5).val ∧
     (3 - e_end : Fin 5).val ≤ (e_start - e_end : Fin 5).val) := by
  let L0 : Fin 4 := ⟨L - 1, by omega⟩
  have hLv : L0.val + 1 = L := by dsimp [L0]; omega
  have h1' := List.all_eq_true.mp fin5AdjB3Check_all e_start (List.mem_finRange _)
  have h2' := List.all_eq_true.mp h1' L0 (List.mem_finRange _)
  dsimp [fin5AdjB3Check] at h2'
  rw [hLv, ← heq] at h2'
  have hbad : (decide ((0 - e_start).val < L) || decide ((1 - e_start).val < L) ||
      (decide ((2 - e_start).val < L) && decide ((3 - e_start).val < L))) = false := by
    simp only [Bool.or_eq_false_iff, Bool.and_eq_false_iff, decide_eq_false_iff_not]
    refine ⟨⟨h0, h1⟩, ?_⟩
    by_cases h2 : (2 - e_start).val < L
    · exact Or.inr (fun h3 => h23 ⟨h2, h3⟩)
    · exact Or.inl h2
  rw [hbad] at h2'
  simp only [Bool.false_eq_true, ↓reduceIte, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h2'
  tauto

/-- **Lemma 6.7 (`pairs-in-M`, `upper_9.tex` lines 733–758, pentagon case)**:
    For a pentagon `D = (0, 1, 2, 3, 4)` (`cycD : CCWCycle S D 2`) and two points `y0, y1 ∈ M`
    on disjoint exit edges `01` and `23`, with witness `v = w (S \ {4, y0, y1})`, at least one
    of the three gaps `{0}` (anchors `{4, y0}`), `{1, 2}` (anchors `{y0, y1}`), or `{3}`
    (anchors `{y1, 4}`) is a good gap for `v`. -/
theorem pairs_in_M {n : ℕ} {P : Set (ℝ × ℝ)}
    {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ}
    (hPoly : ShatteredSimplePolygon P S w) (h25 : Sec2To5Interface P S w)
    {D : Finset (Fin n)} (hDB : D = hullVertices S \ certifiedVertices S w)
    (cycD : CCWCycle S D 2)
    {y0 y1 : Fin n} (hy0M : y0 ∈ Finset.univ \ D) (hy1M : y1 ∈ Finset.univ \ D) (hy01 : y0 ≠ y1)
    (hy0_tri : InIntTri (w (Finset.univ \ {cycD.toFun 4, y0, y1})) (S (cycD.toFun 0)) (S (cycD.toFun 1)) (S y0))
    (hy1_tri : InIntTri (w (Finset.univ \ {cycD.toFun 4, y0, y1})) (S (cycD.toFun 2)) (S (cycD.toFun 3)) (S y1))
    (h_not_lr : ∀ l r : Fin n, (certifiedVertices S w).Nonempty →
      IsCCWEdge S D l r → (∀ h ∈ certifiedVertices S w, orient2D (S l) (S r) (S h) < 0) →
      (cycD.toFun 0, cycD.toFun 1) ≠ (l, r) ∧ (cycD.toFun 2, cycD.toFun 3) ≠ (l, r)) :
    let b := cycD.toFun 4
    let O_star : Finset (Fin n) := {b, y0, y1}
    let v := w (Finset.univ \ O_star)
    ∃ (oa ob : Fin n) (Γ : Finset (Fin n)),
      ((oa = b ∧ ob = y0 ∧ Γ = {cycD.toFun 0}) ∨
       (oa = y0 ∧ ob = y1 ∧ Γ = {cycD.toFun 1, cycD.toFun 2}) ∨
       (oa = y1 ∧ ob = b ∧ Γ = {cycD.toFun 3})) ∧
      GoodAnchorPair P S w O_star oa ob ∧
      (∀ p ∈ Γ,
        IsBackVertexOf S (hullVertices S) p v ∧
        SegmentsCross v (S p) (S oa) (S ob) ∧
        (∃ H_hp : OpenHalfPlane, IsHalfPlaneTest P (WitnessSet {oa, ob} ∅ w) (S p) H_hp)) ∧
      (∀ z : Fin n, z ≠ oa → z ≠ ob → z ∉ O_star →
        S z ∈ convexHull ℝ ((Γ ∪ {oa, ob}).image S : Set (ℝ × ℝ)) →
        SegmentsCross v (S z) (S oa) (S ob) ∧
        (∃ H_hp : OpenHalfPlane, IsHalfPlaneTest P (WitnessSet {oa, ob} ∅ w) (S z) H_hp) ∧
        (z ∈ hullVertices S → IsBackVertexOf S (hullVertices S) z v)) := by
  intro b O_star v
  let d0 := cycD.toFun 0
  let d1 := cycD.toFun 1
  let d2 := cycD.toFun 2
  let d3 := cycD.toFun 3
  let q := w Finset.univ
  have hy0_notD : y0 ∉ D := (Finset.mem_sdiff.mp hy0M).2
  have hy1_notD : y1 ∉ D := (Finset.mem_sdiff.mp hy1M).2
  obtain ⟨hm_out, hb_nf, hv_noncol, hvq_D, hvq_y0, hvq_y1, h_seen_ss⟩ :=
    pentagon_Ostar_core hPoly h25 hDB cycD hy0M hy1M hy01 4
  have h0_out : d0 ∉ O_star := hm_out 0 (by decide)
  have h1_out : d1 ∉ O_star := hm_out 1 (by decide)
  have h2_out : d2 ∉ O_star := hm_out 2 (by decide)
  have h3_out : d3 ∉ O_star := hm_out 3 (by decide)
  have hB : D ⊆ hullVertices S := hDB ▸ Finset.sdiff_subset
  have h0B : d0 ∈ hullVertices S := hB (ccwCycle_mem cycD 0)
  have h1B : d1 ∈ hullVertices S := hB (ccwCycle_mem cycD 1)
  have h2B : d2 ∈ hullVertices S := hB (ccwCycle_mem cycD 2)
  have h3B : d3 ∈ hullVertices S := hB (ccwCycle_mem cycD 3)
  have hb_O : b ∈ O_star := Finset.mem_insert_self _ _
  have hy0_O : y0 ∈ O_star := Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  have hy1_O : y1 ∈ O_star := Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  have hb_ne_y0 : b ≠ y0 := fun h => hy0_notD (h ▸ ccwCycle_mem cycD 4)
  have hy1_ne_b : y1 ≠ b := fun h => hy1_notD (h.symm ▸ ccwCycle_mem cycD 4)
  have h01_nf : 0 < orient2D (S d0) (S d1) v :=
    pentagon_exit_nonfacing hPoly h25 hDB cycD hy0M 0 hy0_tri (fun l r hH he hHn => (h_not_lr l r hH he hHn).1)
  have h23_nf : 0 < orient2D (S d2) (S d3) v :=
    pentagon_exit_nonfacing hPoly h25 hDB cycD hy1M 2 hy1_tri (fun l r hH he hHn => (h_not_lr l r hH he hHn).2)
  have ⟨h0_y0, hy0_1, h01⟩ := exitTri_orient2D_from_left hy0_tri h01_nf
  have ⟨h2_y1, hy1_3, h23⟩ := exitTri_orient2D_from_left hy1_tri h23_nf
  have h_01_y1 : 0 < orient2D (S d0) (S d1) (S y1) :=
    exitTri_convex_comb_orient_pos hy1_tri h01_nf
      (le_of_lt (ccwCycle_ccw3_of_lt cycD (by decide : (0 : Fin 5) < 1) (by decide : (1 : Fin 5) < 2)))
      (le_of_lt (ccwCycle_ccw3_of_lt cycD (by decide : (0 : Fin 5) < 1) (by decide : (1 : Fin 5) < 3)))
  have h_23_y0 : 0 < orient2D (S d2) (S d3) (S y0) :=
    exitTri_convex_comb_orient_pos hy0_tri h23_nf
      (le_of_lt (by have h := ccwCycle_ccw3_of_lt cycD (by decide : (0 : Fin 5) < 2) (by decide : (2 : Fin 5) < 3); unfold orient2D at h ⊢; linarith))
      (le_of_lt (by have h := ccwCycle_ccw3_of_lt cycD (by decide : (1 : Fin 5) < 2) (by decide : (2 : Fin 5) < 3); unfold orient2D at h ⊢; linarith))
  have build_gap0 : ∀ (hgap : GoodAnchorPair P S w O_star b y0),
      0 < orient2D v (S b) (S d0) → 0 < orient2D v (S b) (S y0) →
      ∃ (oa ob : Fin n) (Γ : Finset (Fin n)),
        ((oa = b ∧ ob = y0 ∧ Γ = {d0}) ∨
         (oa = y0 ∧ ob = y1 ∧ Γ = {d1, d2}) ∨
         (oa = y1 ∧ ob = b ∧ Γ = {d3})) ∧
        GoodAnchorPair P S w O_star oa ob ∧
        (∀ p ∈ Γ, IsBackVertexOf S (hullVertices S) p v ∧ SegmentsCross v (S p) (S oa) (S ob) ∧
          (∃ H_hp : OpenHalfPlane, IsHalfPlaneTest P (WitnessSet {oa, ob} ∅ w) (S p) H_hp)) ∧
        (∀ z : Fin n, z ≠ oa → z ≠ ob → z ∉ O_star →
          S z ∈ convexHull ℝ ((Γ ∪ {oa, ob}).image S : Set (ℝ × ℝ)) →
          SegmentsCross v (S z) (S oa) (S ob) ∧
          (∃ H_hp : OpenHalfPlane, IsHalfPlaneTest P (WitnessSet {oa, ob} ∅ w) (S z) H_hp) ∧
          (z ∈ hullVertices S → IsBackVertexOf S (hullVertices S) z v)) := by
    intro hgap h40 hby0
    refine ⟨b, y0, {d0}, Or.inl ⟨rfl, rfl, rfl⟩, hgap, good_gap_of_all_cross hPoly h25 hgap (fun p hp => ?_)⟩
    rw [Finset.mem_singleton] at hp; subst hp
    refine ⟨cycD.inj.ne (by decide : (0 : Fin 5) ≠ 4), fun h => hy0_notD (h ▸ ccwCycle_mem cycD 0),
      h0_out, h0B, segmentsCross_inIntTri_left hy0_tri h40 h0_y0 hby0 (by rw [orient2D_self_right])
        (by have h := ccwCycle_ccw3_of_lt cycD (by decide : (0 : Fin 5) < 1) (by decide : (1 : Fin 5) < 4); dsimp [b, d0, d1]; unfold orient2D at h ⊢; linarith)⟩
  have build_gap3 : ∀ (hgap : GoodAnchorPair P S w O_star y1 b),
      0 < orient2D v (S d3) (S b) → 0 < orient2D v (S y1) (S b) →
      ∃ (oa ob : Fin n) (Γ : Finset (Fin n)),
        ((oa = b ∧ ob = y0 ∧ Γ = {d0}) ∨
         (oa = y0 ∧ ob = y1 ∧ Γ = {d1, d2}) ∨
         (oa = y1 ∧ ob = b ∧ Γ = {d3})) ∧
        GoodAnchorPair P S w O_star oa ob ∧
        (∀ p ∈ Γ, IsBackVertexOf S (hullVertices S) p v ∧ SegmentsCross v (S p) (S oa) (S ob) ∧
          (∃ H_hp : OpenHalfPlane, IsHalfPlaneTest P (WitnessSet {oa, ob} ∅ w) (S p) H_hp)) ∧
        (∀ z : Fin n, z ≠ oa → z ≠ ob → z ∉ O_star →
          S z ∈ convexHull ℝ ((Γ ∪ {oa, ob}).image S : Set (ℝ × ℝ)) →
          SegmentsCross v (S z) (S oa) (S ob) ∧
          (∃ H_hp : OpenHalfPlane, IsHalfPlaneTest P (WitnessSet {oa, ob} ∅ w) (S z) H_hp) ∧
          (z ∈ hullVertices S → IsBackVertexOf S (hullVertices S) z v)) := by
    intro hgap h34 hy1b
    refine ⟨y1, b, {d3}, Or.inr (Or.inr ⟨rfl, rfl, rfl⟩), hgap, good_gap_of_all_cross hPoly h25 hgap (fun p hp => ?_)⟩
    rw [Finset.mem_singleton] at hp; subst hp
    refine ⟨fun h => hy1_notD (h.symm ▸ ccwCycle_mem cycD 3), cycD.inj.ne (by decide : (3 : Fin 5) ≠ 4),
      h3_out, h3B, segmentsCross_inIntTri_right hy1_tri hy1_3 h34 hy1b
        (ccwCycle_ccw3_of_lt cycD (by decide : (2 : Fin 5) < 3) (by decide : (3 : Fin 5) < 4))
        (by dsimp [d3]; rw [orient2D_self_left])⟩
  have build_gap12 : ∀ (hgap : GoodAnchorPair P S w O_star y0 y1),
      0 < orient2D v (S y0) (S d2) → 0 < orient2D v (S d1) (S y1) → 0 < orient2D v (S y0) (S y1) →
      ∃ (oa ob : Fin n) (Γ : Finset (Fin n)),
        ((oa = b ∧ ob = y0 ∧ Γ = {d0}) ∨
         (oa = y0 ∧ ob = y1 ∧ Γ = {d1, d2}) ∨
         (oa = y1 ∧ ob = b ∧ Γ = {d3})) ∧
        GoodAnchorPair P S w O_star oa ob ∧
        (∀ p ∈ Γ, IsBackVertexOf S (hullVertices S) p v ∧ SegmentsCross v (S p) (S oa) (S ob) ∧
          (∃ H_hp : OpenHalfPlane, IsHalfPlaneTest P (WitnessSet {oa, ob} ∅ w) (S p) H_hp)) ∧
        (∀ z : Fin n, z ≠ oa → z ≠ ob → z ∉ O_star →
          S z ∈ convexHull ℝ ((Γ ∪ {oa, ob}).image S : Set (ℝ × ℝ)) →
          SegmentsCross v (S z) (S oa) (S ob) ∧
          (∃ H_hp : OpenHalfPlane, IsHalfPlaneTest P (WitnessSet {oa, ob} ∅ w) (S z) H_hp) ∧
          (z ∈ hullVertices S → IsBackVertexOf S (hullVertices S) z v)) := by
    intro hgap hy0_2 hd1_y1 hy0_y1
    refine ⟨y0, y1, {d1, d2}, Or.inr (Or.inl ⟨rfl, rfl, rfl⟩), hgap, good_gap_of_all_cross hPoly h25 hgap (fun p hp => ?_)⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl
    · refine ⟨fun h => hy0_notD (h.symm ▸ ccwCycle_mem cycD 1), fun h => hy1_notD (h.symm ▸ ccwCycle_mem cycD 1),
        h1_out, h1B, segmentsCross_between_exits_shared (u1 := (0, 0)) hy0_tri hy0_1 hd1_y1 hy0_y1 h_01_y1⟩
    · refine ⟨fun h => hy0_notD (h.symm ▸ ccwCycle_mem cycD 2), fun h => hy1_notD (h.symm ▸ ccwCycle_mem cycD 2),
        h2_out, h2B, segmentsCross_between_exits_shared_right hy1_tri hy0_2 h2_y1 hy0_y1 h_23_y0⟩
  by_cases h_all_nf : ∀ m : Fin 5, 0 < orient2D (S (cycD.toFun m)) (S (cycD.toFun (m + 1))) v
  · have h_nf40 : 0 < orient2D v (S b) (S d0) := by
      have h := h_all_nf 4; dsimp [b, d0] at *; unfold orient2D at h ⊢; linarith
    have h_nf12 : 0 < orient2D v (S d1) (S d2) := by
      have h := h_all_nf 1; dsimp [d1, d2] at *; unfold orient2D at h ⊢; linarith
    have h_nf34 : 0 < orient2D v (S d3) (S b) := by
      have h := h_all_nf 3; dsimp [b, d3] at *; unfold orient2D at h ⊢; linarith
    let s0 := posBool (orient2D v q (S d0))
    let s1 := posBool (orient2D v q (S d1))
    let s2 := posBool (orient2D v q (S d2))
    let s3 := posBool (orient2D v q (S d3))
    let s4 := posBool (orient2D v q (S b))
    let sy0 := posBool (orient2D v q (S y0))
    let sy1 := posBool (orient2D v q (S y1))
    have h_not_all : ¬ (s0 = s1 ∧ s0 = s2 ∧ s0 = s3 ∧ s0 = s4) := by
      intro ⟨h1, h2, h3, h4⟩
      exact pentagon_all_nf_not_all_same cycD v q h_all_nf hvq_D (fun m => by
        fin_cases m
        · exact by unfold OnSameSide; exact mul_self_pos.mpr (hvq_D 0)
        · exact onSameSide_of_posBool_eq h1 (hvq_D 0) (hvq_D 1)
        · exact onSameSide_of_posBool_eq h2 (hvq_D 0) (hvq_D 2)
        · exact onSameSide_of_posBool_eq h3 (hvq_D 0) (hvq_D 3)
        · exact onSameSide_of_posBool_eq h4 (hvq_D 0) (hvq_D 4))
    have h_no_alt := pent_no_alt4_of_orient cycD v q hvq_D
    have hy0_eq : s0 = s1 → sy0 = s0 := fun h => exitTri_posBool_of_endpoints hy0_tri h
    have hy1_eq : s2 = s3 → sy1 = s2 := fun h => exitTri_posBool_of_endpoints hy1_tri h
    rcases pentagon_pairs_bool s0 s1 s2 s3 s4 sy0 sy1 h_not_all h_no_alt hy0_eq hy1_eq with
      ⟨h40, h0y⟩ | ⟨hy01_b, h12_b, h2y_b⟩ | ⟨hy13_b, h34_b⟩
    · have hsee : Sees P v q := by
        by_contra hnq
        have h01' := posBool_eq_of_onSameSide (h_seen_ss d0 d1 h0_out h1_out hnq)
        have h02' := posBool_eq_of_onSameSide (h_seen_ss d0 d2 h0_out h2_out hnq)
        have h03' := posBool_eq_of_onSameSide (h_seen_ss d0 d3 h0_out h3_out hnq)
        exact h_not_all ⟨h01', h02', h03', h40.symm⟩
      have hby0 : 0 < orient2D v (S b) (S y0) :=
        orient2D_chain3_pos ⟨h40, h0y⟩ (hvq_D 4) (hvq_D 0) hvq_y0 h_nf40 h0_y0
      exact build_gap0 (goodAnchorPair_of_see hb_O hy0_O hb_ne_y0 hsee
        (onSameSide_of_posBool_eq (h40.trans h0y) (hvq_D 4) hvq_y0) (ne_of_gt hby0)) h_nf40 hby0
    · have hy0_2 := orient2D_chain3_pos ⟨hy01_b, h12_b⟩ hvq_y0 (hvq_D 1) (hvq_D 2) hy0_1 h_nf12
      have hd1_y1 := orient2D_chain3_pos ⟨h12_b, h2y_b⟩ (hvq_D 1) (hvq_D 2) hvq_y1 h_nf12 h2_y1
      have hy0_y1 := orient2D_chain3_pos ⟨hy01_b, h12_b.trans h2y_b⟩ hvq_y0 (hvq_D 1) hvq_y1 hy0_1 hd1_y1
      by_cases hsee : Sees P v q
      · exact build_gap12 (goodAnchorPair_of_see hy0_O hy1_O hy01 hsee
          (onSameSide_of_posBool_eq (hy01_b.trans (h12_b.trans h2y_b)) hvq_y0 hvq_y1)
          (ne_of_gt hy0_y1)) hy0_2 hd1_y1 hy0_y1
      · have h01' := posBool_eq_of_onSameSide (h_seen_ss d0 d1 h0_out h1_out hsee)
        have h23' := posBool_eq_of_onSameSide (h_seen_ss d2 d3 h2_out h3_out hsee)
        have h0_y0_eq : s0 = sy0 := (hy0_eq h01').symm
        have hy1_3_eq : sy1 = s3 := (hy1_eq h23').trans h23'
        have h03_ss : OnSameSide v q (S d0) (S y0) := onSameSide_of_posBool_eq h0_y0_eq (hvq_D 0) hvq_y0
        have hy1_3_ss : OnSameSide v q (S y1) (S d3) := onSameSide_of_posBool_eq hy1_3_eq hvq_y1 (hvq_D 3)
        have hss_y01 := onSameSide_of_posBool_eq (hy01_b.trans (h12_b.trans h2y_b)) hvq_y0 hvq_y1
        exact build_gap12 (goodAnchorPair_of_cone_ends hy0_O hy1_O hy01 hss_y01 hy0_y1
          (fun hqy0 => ⟨d0, h0_out, by unfold OnSameSide at h03_ss; nlinarith only [h03_ss, hqy0], h0_y0⟩)
          (fun hqy0 => ⟨d3, h3_out, by unfold OnSameSide at hss_y01 hy1_3_ss; nlinarith only [hss_y01, hy1_3_ss, hqy0], hy1_3⟩))
          hy0_2 hd1_y1 hy0_y1
    · have hsee : Sees P v q := by
        by_contra hnq
        have h01' := posBool_eq_of_onSameSide (h_seen_ss d0 d1 h0_out h1_out hnq)
        have h02' := posBool_eq_of_onSameSide (h_seen_ss d0 d2 h0_out h2_out hnq)
        have h03' := posBool_eq_of_onSameSide (h_seen_ss d0 d3 h0_out h3_out hnq)
        exact h_not_all ⟨h01', h02', h03', (h03'.trans hy13_b.symm).trans (hy13_b.trans h34_b)⟩
      have hy1b : 0 < orient2D v (S y1) (S b) :=
        orient2D_chain3_pos ⟨hy13_b, h34_b⟩ hvq_y1 (hvq_D 3) (hvq_D 4) hy1_3 h_nf34
      exact build_gap3 (goodAnchorPair_of_see hy1_O hb_O hy1_ne_b hsee
        (onSameSide_of_posBool_eq (hy13_b.trans h34_b) hvq_y1 (hvq_D 4)) (ne_of_gt hy1b)) h_nf34 hy1b
  · push Not at h_all_nf
    obtain ⟨j0, hj0⟩ := h_all_nf
    have hj0_lt : orient2D (S (cycD.toFun j0)) (S (cycD.toFun (j0 + 1))) v < 0 :=
      lt_of_le_of_ne hj0 (hv_noncol j0 (j0 + 1) (fin_add_one_ne_self j0))
    obtain ⟨e_start, e_end, L, hL1, hL_le, he_end_eq, h_face_lt, _, _, _, _, h_ang⟩ :=
      facing_arc_complement_order cycD v hv_noncol ⟨j0, hj0_lt⟩
    have hcase := pent_facing_cases_pairs e_start e_end L hL1 hL_le he_end_eq
      (fun h => by have hf := h_face_lt 0 h; change orient2D (S d0) (S d1) v < 0 at hf; linarith)
      (fun h => by have hf := h_face_lt 2 h; change orient2D (S d2) (S d3) v < 0 at hf; linarith)
      (fun ⟨h3, h4⟩ => by
        rw [isFrontVertexOf_iff_ccwCycle cycD 4 v] at hb_nf
        exact hb_nf ⟨h_face_lt 3 h3, h_face_lt 4 h4⟩)
    rcases hcase with ⟨rfl, rfl, _⟩ | ⟨rfl, rfl, _⟩ | ⟨rfl, rfl, _⟩
    · -- e_start = 1, e_end = 2: chain 2 -> y1 -> 3 -> 4 -> 0 -> y0 -> 1 spans < pi
      have h_ord : ∀ a c : Fin 5, (a - 2).val < (c - 2).val → (c - 2).val ≤ (1 - 2 : Fin 5).val →
          0 < orient2D v (S (cycD.toFun a)) (S (cycD.toFun c)) :=
        fun a c h1 h2 => (h_ang a c h1 h2).2
      have h24 := h_ord 2 4 (by decide) (by decide)
      have h34 := h_ord 3 4 (by decide) (by decide)
      have h40 := h_ord 4 0 (by decide) (by decide)
      have h41 := h_ord 4 1 (by decide) (by decide)
      have h30 := h_ord 3 0 (by decide) (by decide)
      have hy1_4 : 0 < orient2D v (S y1) (S b) := exitTri_orient_after hy1_tri h24 h34
      have h4_y0 : 0 < orient2D v (S b) (S y0) := exitTri_orient_before hy0_tri h40 h41
      have hy1_y0 : 0 < orient2D v (S y1) (S y0) := exitTri_orient_after hy1_tri
        (exitTri_orient_before hy0_tri (h_ord 2 0 (by decide) (by decide)) (h_ord 2 1 (by decide) (by decide)))
        (exitTri_orient_before hy0_tri h30 (h_ord 3 1 (by decide) (by decide)))
      by_cases hsee : Sees P v q
      · rcases three_missed_in_cone_pigeonhole v q (S y1) (S b) (S y0) hvq_y1 (hvq_D 4) hvq_y0
          hy1_4 h4_y0 hy1_y0 with hss_y1b | hss_by0
        · exact build_gap3 (goodAnchorPair_of_see hy1_O hb_O hy1_ne_b hsee hss_y1b (ne_of_gt hy1_4)) h34 hy1_4
        · exact build_gap0 (goodAnchorPair_of_see hb_O hy0_O hb_ne_y0 hsee hss_by0 (ne_of_gt h4_y0)) h40 h4_y0
      · have hss23 := h_seen_ss d2 d3 h2_out h3_out hsee
        have hss30 := h_seen_ss d3 d0 h3_out h0_out hsee
        have hss01 := h_seen_ss d0 d1 h0_out h1_out hsee
        have hss34 : OnSameSide v q (S d3) (S b) := orient2D_vq_between_sameSide hss30 (hvq_D 3) h30 h34 h40
        have hss2_y1 := (exitTri_sameSide_of_in_L hy1_tri hss23).1
        have hss_y13 := (exitTri_sameSide_of_in_L hy1_tri hss23).2
        have hss_y1b : OnSameSide v q (S y1) (S b) := hss_y13.trans hss34
        have hss_b0 : OnSameSide v q (S b) (S d0) := hss34.symm.trans hss30
        exact build_gap3 (goodAnchorPair_of_cone_ends hy1_O hb_O hy1_ne_b hss_y1b hy1_4
          (fun hqy1 => ⟨d2, h2_out, by unfold OnSameSide at hss2_y1; nlinarith only [hss2_y1, hqy1], h2_y1⟩)
          (fun hqy1 => ⟨d0, h0_out, by unfold OnSameSide at hss_y1b hss_b0; nlinarith only [hss_y1b, hss_b0, hqy1], h40⟩))
          h34 hy1_4
    · -- e_start = 3, e_end = 4: chain 4 -> 0 -> y0 -> 1 -> 2 -> y1 -> 3 spans < pi
      have h_ord : ∀ a c : Fin 5, (a - 4).val < (c - 4).val → (c - 4).val ≤ (3 - 4 : Fin 5).val →
          0 < orient2D v (S (cycD.toFun a)) (S (cycD.toFun c)) :=
        fun a c h1 h2 => (h_ang a c h1 h2).2
      have h40 := h_ord 4 0 (by decide) (by decide)
      have h41 := h_ord 4 1 (by decide) (by decide)
      have h12 := h_ord 1 2 (by decide) (by decide)
      have h02 := h_ord 0 2 (by decide) (by decide)
      have h13 := h_ord 1 3 (by decide) (by decide)
      have h4_y0 : 0 < orient2D v (S b) (S y0) := exitTri_orient_before hy0_tri h40 h41
      have hy0_2 : 0 < orient2D v (S y0) (S d2) := exitTri_orient_after hy0_tri h02 h12
      have hd1_y1 : 0 < orient2D v (S d1) (S y1) := exitTri_orient_before hy1_tri h12 h13
      have hy0_y1 : 0 < orient2D v (S y0) (S y1) := exitTri_orient_after hy0_tri
        (exitTri_orient_before hy1_tri h02 (h_ord 0 3 (by decide) (by decide)))
        (exitTri_orient_before hy1_tri h12 h13)
      have h4_y1 : 0 < orient2D v (S b) (S y1) :=
        exitTri_orient_before hy1_tri (h_ord 4 2 (by decide) (by decide)) (h_ord 4 3 (by decide) (by decide))
      by_cases hsee : Sees P v q
      · rcases three_missed_in_cone_pigeonhole v q (S b) (S y0) (S y1) (hvq_D 4) hvq_y0 hvq_y1
          h4_y0 hy0_y1 h4_y1 with hss_4y0 | hss_y01
        · exact build_gap0 (goodAnchorPair_of_see hb_O hy0_O hb_ne_y0 hsee hss_4y0 (ne_of_gt h4_y0)) h40 h4_y0
        · exact build_gap12 (goodAnchorPair_of_see hy0_O hy1_O hy01 hsee hss_y01 (ne_of_gt hy0_y1)) hy0_2 hd1_y1 hy0_y1
      · have hss01 := h_seen_ss d0 d1 h0_out h1_out hsee
        have hss12 := h_seen_ss d1 d2 h1_out h2_out hsee
        have hss23 := h_seen_ss d2 d3 h2_out h3_out hsee
        have hss0_y0 := (exitTri_sameSide_of_in_L hy0_tri hss01).1
        have hss_y01 := (exitTri_sameSide_of_in_L hy0_tri hss01).2
        have hss2_y1 := (exitTri_sameSide_of_in_L hy1_tri hss23).1
        have hss_y13 := (exitTri_sameSide_of_in_L hy1_tri hss23).2
        have hss_y0_y1 : OnSameSide v q (S y0) (S y1) := hss_y01.trans (hss12.trans hss2_y1)
        exact build_gap12 (goodAnchorPair_of_cone_ends hy0_O hy1_O hy01 hss_y0_y1 hy0_y1
          (fun hqy0 => ⟨d0, h0_out, by unfold OnSameSide at hss0_y0; nlinarith only [hss0_y0, hqy0], h0_y0⟩)
          (fun hqy0 => ⟨d3, h3_out, by unfold OnSameSide at hss_y0_y1 hss_y13; nlinarith only [hss_y0_y1, hss_y13, hqy0], hy1_3⟩))
          hy0_2 hd1_y1 hy0_y1
    · -- e_start = 4, e_end = 0: chain 0 -> y0 -> 1 -> 2 -> y1 -> 3 -> 4 spans < pi
      have h_ord : ∀ a c : Fin 5, (a - 0).val < (c - 0).val → (c - 0).val ≤ (4 - 0 : Fin 5).val →
          0 < orient2D v (S (cycD.toFun a)) (S (cycD.toFun c)) :=
        fun a c h1 h2 => (h_ang a c h1 h2).2
      have h12 := h_ord 1 2 (by decide) (by decide)
      have h02 := h_ord 0 2 (by decide) (by decide)
      have h13 := h_ord 1 3 (by decide) (by decide)
      have h24 := h_ord 2 4 (by decide) (by decide)
      have h34 := h_ord 3 4 (by decide) (by decide)
      have hy0_2 : 0 < orient2D v (S y0) (S d2) := exitTri_orient_after hy0_tri h02 h12
      have hd1_y1 : 0 < orient2D v (S d1) (S y1) := exitTri_orient_before hy1_tri h12 h13
      have hy0_y1 : 0 < orient2D v (S y0) (S y1) := exitTri_orient_after hy0_tri
        (exitTri_orient_before hy1_tri h02 (h_ord 0 3 (by decide) (by decide)))
        (exitTri_orient_before hy1_tri h12 h13)
      have hy1_4 : 0 < orient2D v (S y1) (S b) := exitTri_orient_after hy1_tri h24 h34
      have hy0_4 : 0 < orient2D v (S y0) (S b) :=
        exitTri_orient_after hy0_tri (h_ord 0 4 (by decide) (by decide)) (h_ord 1 4 (by decide) (by decide))
      by_cases hsee : Sees P v q
      · rcases three_missed_in_cone_pigeonhole v q (S y0) (S y1) (S b) hvq_y0 hvq_y1 (hvq_D 4)
          hy0_y1 hy1_4 hy0_4 with hss_y01 | hss_y1b
        · exact build_gap12 (goodAnchorPair_of_see hy0_O hy1_O hy01 hsee hss_y01 (ne_of_gt hy0_y1)) hy0_2 hd1_y1 hy0_y1
        · exact build_gap3 (goodAnchorPair_of_see hy1_O hb_O hy1_ne_b hsee hss_y1b (ne_of_gt hy1_4)) h34 hy1_4
      · have hss01 := h_seen_ss d0 d1 h0_out h1_out hsee
        have hss12 := h_seen_ss d1 d2 h1_out h2_out hsee
        have hss23 := h_seen_ss d2 d3 h2_out h3_out hsee
        have hss0_y0 := (exitTri_sameSide_of_in_L hy0_tri hss01).1
        have hss_y01 := (exitTri_sameSide_of_in_L hy0_tri hss01).2
        have hss2_y1 := (exitTri_sameSide_of_in_L hy1_tri hss23).1
        have hss_y13 := (exitTri_sameSide_of_in_L hy1_tri hss23).2
        have hss_y0_y1 : OnSameSide v q (S y0) (S y1) := hss_y01.trans (hss12.trans hss2_y1)
        exact build_gap12 (goodAnchorPair_of_cone_ends hy0_O hy1_O hy01 hss_y0_y1 hy0_y1
          (fun hqy0 => ⟨d0, h0_out, by unfold OnSameSide at hss0_y0; nlinarith only [hss0_y0, hqy0], h0_y0⟩)
          (fun hqy0 => ⟨d3, h3_out, by unfold OnSameSide at hss_y0_y1 hss_y13; nlinarith only [hss_y0_y1, hss_y13, hqy0], hy1_3⟩))
          hy0_2 hd1_y1 hy0_y1



/-- **Lemma 6.10 (`adjacent-exits`, `b = 4`, `upper_9.tex` lines 777–788)**:
    For a pentagon `D = (0, 1, 2, 3, 4)` (`cycD : CCWCycle S D 2`) and points `y0, y1 ∈ M`
    on adjacent exit edges `01` and `12`, with `O* = {y0, y1, 4}` and `v = w (S \ O*)`,
    at least one of the three gaps `{0}` (anchors `{4, y0}`), `{1}` (anchors `{y0, y1}`), or
    `{2, 3}` (anchors `{y1, 4}`) is a good gap for `v`. -/
theorem adjacent_exits_b4 {n : ℕ} {P : Set (ℝ × ℝ)}
    {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ}
    (hPoly : ShatteredSimplePolygon P S w) (h25 : Sec2To5Interface P S w)
    {D : Finset (Fin n)} (hDB : D = hullVertices S \ certifiedVertices S w)
    (cycD : CCWCycle S D 2)
    {y0 y1 : Fin n} (hy0M : y0 ∈ Finset.univ \ D) (hy1M : y1 ∈ Finset.univ \ D) (hy01 : y0 ≠ y1)
    (hy0_tri : InIntTri (w (Finset.univ \ {cycD.toFun 4, y0, y1})) (S (cycD.toFun 0)) (S (cycD.toFun 1)) (S y0))
    (hy1_tri : InIntTri (w (Finset.univ \ {cycD.toFun 4, y0, y1})) (S (cycD.toFun 1)) (S (cycD.toFun 2)) (S y1))
    (h_not_lr : ∀ l r : Fin n, (certifiedVertices S w).Nonempty →
      IsCCWEdge S D l r → (∀ h ∈ certifiedVertices S w, orient2D (S l) (S r) (S h) < 0) →
      (cycD.toFun 0, cycD.toFun 1) ≠ (l, r) ∧ (cycD.toFun 1, cycD.toFun 2) ≠ (l, r)) :
    let b := cycD.toFun 4
    let O_star : Finset (Fin n) := {b, y0, y1}
    let v := w (Finset.univ \ O_star)
    ∃ (oa ob : Fin n) (Γ : Finset (Fin n)),
      ((oa = b ∧ ob = y0 ∧ Γ = {cycD.toFun 0}) ∨
       (oa = y0 ∧ ob = y1 ∧ Γ = {cycD.toFun 1}) ∨
       (oa = y1 ∧ ob = b ∧ Γ = {cycD.toFun 2, cycD.toFun 3})) ∧
      GoodAnchorPair P S w O_star oa ob ∧
      (∀ p ∈ Γ,
        IsBackVertexOf S (hullVertices S) p v ∧
        SegmentsCross v (S p) (S oa) (S ob) ∧
        (∃ H_hp : OpenHalfPlane, IsHalfPlaneTest P (WitnessSet {oa, ob} ∅ w) (S p) H_hp)) ∧
      (∀ z : Fin n, z ≠ oa → z ≠ ob → z ∉ O_star →
        S z ∈ convexHull ℝ ((Γ ∪ {oa, ob}).image S : Set (ℝ × ℝ)) →
        SegmentsCross v (S z) (S oa) (S ob) ∧
        (∃ H_hp : OpenHalfPlane, IsHalfPlaneTest P (WitnessSet {oa, ob} ∅ w) (S z) H_hp) ∧
        (z ∈ hullVertices S → IsBackVertexOf S (hullVertices S) z v)) := by
  intro b O_star v
  let d0 := cycD.toFun 0
  let d1 := cycD.toFun 1
  let d2 := cycD.toFun 2
  let d3 := cycD.toFun 3
  let q := w Finset.univ
  have hy0_notD : y0 ∉ D := (Finset.mem_sdiff.mp hy0M).2
  have hy1_notD : y1 ∉ D := (Finset.mem_sdiff.mp hy1M).2
  obtain ⟨hm_out, hb_nf, hv_noncol, hvq_D, hvq_y0, hvq_y1, h_seen_ss⟩ :=
    pentagon_Ostar_core hPoly h25 hDB cycD hy0M hy1M hy01 4
  have h0_out : d0 ∉ O_star := hm_out 0 (by decide)
  have h1_out : d1 ∉ O_star := hm_out 1 (by decide)
  have h2_out : d2 ∉ O_star := hm_out 2 (by decide)
  have h3_out : d3 ∉ O_star := hm_out 3 (by decide)
  have hB : D ⊆ hullVertices S := hDB ▸ Finset.sdiff_subset
  have h0B : d0 ∈ hullVertices S := hB (ccwCycle_mem cycD 0)
  have h1B : d1 ∈ hullVertices S := hB (ccwCycle_mem cycD 1)
  have h2B : d2 ∈ hullVertices S := hB (ccwCycle_mem cycD 2)
  have h3B : d3 ∈ hullVertices S := hB (ccwCycle_mem cycD 3)
  have hb_O : b ∈ O_star := Finset.mem_insert_self _ _
  have hy0_O : y0 ∈ O_star := Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  have hy1_O : y1 ∈ O_star := Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  have hb_ne_y0 : b ≠ y0 := fun h => hy0_notD (h ▸ ccwCycle_mem cycD 4)
  have hy1_ne_b : y1 ≠ b := fun h => hy1_notD (h.symm ▸ ccwCycle_mem cycD 4)
  have h01_nf : 0 < orient2D (S d0) (S d1) v :=
    pentagon_exit_nonfacing hPoly h25 hDB cycD hy0M 0 hy0_tri (fun l r hH he hHn => (h_not_lr l r hH he hHn).1)
  have h12_nf : 0 < orient2D (S d1) (S d2) v :=
    pentagon_exit_nonfacing hPoly h25 hDB cycD hy1M 1 hy1_tri (fun l r hH he hHn => (h_not_lr l r hH he hHn).2)
  have ⟨h0_y0, hy0_1, h01⟩ := exitTri_orient2D_from_left hy0_tri h01_nf
  have ⟨h1_y1, hy1_2, h12⟩ := exitTri_orient2D_from_left hy1_tri h12_nf
  have h_01_y1 : 0 < orient2D (S d0) (S d1) (S y1) :=
    exitTri_convex_comb_orient_pos hy1_tri h01_nf (by rw [orient2D_self_right])
      (le_of_lt (ccwCycle_ccw3_of_lt cycD (by decide : (0 : Fin 5) < 1) (by decide : (1 : Fin 5) < 2)))
  have build_gap0 : GoodAnchorPair P S w O_star b y0 →
      0 < orient2D v (S b) (S d0) → 0 < orient2D v (S b) (S y0) →
      ∃ (oa ob : Fin n) (Γ : Finset (Fin n)),
        ((oa = b ∧ ob = y0 ∧ Γ = {d0}) ∨
         (oa = y0 ∧ ob = y1 ∧ Γ = {d1}) ∨
         (oa = y1 ∧ ob = b ∧ Γ = {d2, d3})) ∧
        GoodAnchorPair P S w O_star oa ob ∧
        (∀ p ∈ Γ, IsBackVertexOf S (hullVertices S) p v ∧ SegmentsCross v (S p) (S oa) (S ob) ∧
          (∃ H_hp : OpenHalfPlane, IsHalfPlaneTest P (WitnessSet {oa, ob} ∅ w) (S p) H_hp)) ∧
        (∀ z : Fin n, z ≠ oa → z ≠ ob → z ∉ O_star →
          S z ∈ convexHull ℝ ((Γ ∪ {oa, ob}).image S : Set (ℝ × ℝ)) →
          SegmentsCross v (S z) (S oa) (S ob) ∧
          (∃ H_hp : OpenHalfPlane, IsHalfPlaneTest P (WitnessSet {oa, ob} ∅ w) (S z) H_hp) ∧
          (z ∈ hullVertices S → IsBackVertexOf S (hullVertices S) z v)) := by
    intro hgap h40 hby0
    refine ⟨b, y0, {d0}, Or.inl ⟨rfl, rfl, rfl⟩, hgap, good_gap_of_all_cross hPoly h25 hgap (fun p hp => ?_)⟩
    rw [Finset.mem_singleton] at hp; subst hp
    refine ⟨cycD.inj.ne (by decide : (0 : Fin 5) ≠ 4), fun h => hy0_notD (h ▸ ccwCycle_mem cycD 0),
      h0_out, h0B, segmentsCross_inIntTri_left hy0_tri h40 h0_y0 hby0 (by rw [orient2D_self_right])
        (by have h := ccwCycle_ccw3_of_lt cycD (by decide : (0 : Fin 5) < 1) (by decide : (1 : Fin 5) < 4); dsimp [b, d0, d1]; unfold orient2D at h ⊢; linarith)⟩
  have build_gap1 : GoodAnchorPair P S w O_star y0 y1 → 0 < orient2D v (S y0) (S y1) →
      ∃ (oa ob : Fin n) (Γ : Finset (Fin n)),
        ((oa = b ∧ ob = y0 ∧ Γ = {d0}) ∨
         (oa = y0 ∧ ob = y1 ∧ Γ = {d1}) ∨
         (oa = y1 ∧ ob = b ∧ Γ = {d2, d3})) ∧
        GoodAnchorPair P S w O_star oa ob ∧
        (∀ p ∈ Γ, IsBackVertexOf S (hullVertices S) p v ∧ SegmentsCross v (S p) (S oa) (S ob) ∧
          (∃ H_hp : OpenHalfPlane, IsHalfPlaneTest P (WitnessSet {oa, ob} ∅ w) (S p) H_hp)) ∧
        (∀ z : Fin n, z ≠ oa → z ≠ ob → z ∉ O_star →
          S z ∈ convexHull ℝ ((Γ ∪ {oa, ob}).image S : Set (ℝ × ℝ)) →
          SegmentsCross v (S z) (S oa) (S ob) ∧
          (∃ H_hp : OpenHalfPlane, IsHalfPlaneTest P (WitnessSet {oa, ob} ∅ w) (S z) H_hp) ∧
          (z ∈ hullVertices S → IsBackVertexOf S (hullVertices S) z v)) := by
    intro hgap hy0_y1
    refine ⟨y0, y1, {d1}, Or.inr (Or.inl ⟨rfl, rfl, rfl⟩), hgap, good_gap_of_all_cross hPoly h25 hgap (fun p hp => ?_)⟩
    rw [Finset.mem_singleton] at hp; subst hp
    refine ⟨fun h => hy0_notD (h.symm ▸ ccwCycle_mem cycD 1), fun h => hy1_notD (h.symm ▸ ccwCycle_mem cycD 1),
      h1_out, h1B, segmentsCross_between_exits_shared (u1 := (0, 0)) hy0_tri hy0_1 h1_y1 hy0_y1 h_01_y1⟩
  have build_gap23 : GoodAnchorPair P S w O_star y1 b →
      0 < orient2D v (S d2) (S b) → 0 < orient2D v (S y1) (S d3) →
      0 < orient2D v (S d3) (S b) → 0 < orient2D v (S y1) (S b) →
      ∃ (oa ob : Fin n) (Γ : Finset (Fin n)),
        ((oa = b ∧ ob = y0 ∧ Γ = {d0}) ∨
         (oa = y0 ∧ ob = y1 ∧ Γ = {d1}) ∨
         (oa = y1 ∧ ob = b ∧ Γ = {d2, d3})) ∧
        GoodAnchorPair P S w O_star oa ob ∧
        (∀ p ∈ Γ, IsBackVertexOf S (hullVertices S) p v ∧ SegmentsCross v (S p) (S oa) (S ob) ∧
          (∃ H_hp : OpenHalfPlane, IsHalfPlaneTest P (WitnessSet {oa, ob} ∅ w) (S p) H_hp)) ∧
        (∀ z : Fin n, z ≠ oa → z ≠ ob → z ∉ O_star →
          S z ∈ convexHull ℝ ((Γ ∪ {oa, ob}).image S : Set (ℝ × ℝ)) →
          SegmentsCross v (S z) (S oa) (S ob) ∧
          (∃ H_hp : OpenHalfPlane, IsHalfPlaneTest P (WitnessSet {oa, ob} ∅ w) (S z) H_hp) ∧
          (z ∈ hullVertices S → IsBackVertexOf S (hullVertices S) z v)) := by
    intro hgap h24 hy1_3 h34 hy1_b
    refine ⟨y1, b, {d2, d3}, Or.inr (Or.inr ⟨rfl, rfl, rfl⟩), hgap, good_gap_of_all_cross hPoly h25 hgap (fun p hp => ?_)⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl
    · refine ⟨fun h => hy1_notD (h.symm ▸ ccwCycle_mem cycD 2), cycD.inj.ne (by decide : (2 : Fin 5) ≠ 4),
        h2_out, h2B, segmentsCross_inIntTri_right hy1_tri hy1_2 h24 hy1_b
          (ccwCycle_ccw3_of_lt cycD (by decide : (1 : Fin 5) < 2) (by decide : (2 : Fin 5) < 4)) (by dsimp [d2]; rw [orient2D_self_left])⟩
    · refine ⟨fun h => hy1_notD (h.symm ▸ ccwCycle_mem cycD 3), cycD.inj.ne (by decide : (3 : Fin 5) ≠ 4),
        h3_out, h3B, segmentsCross_inIntTri_right hy1_tri hy1_3 h34 hy1_b
          (ccwCycle_ccw3_of_lt cycD (by decide : (1 : Fin 5) < 3) (by decide : (3 : Fin 5) < 4))
          (le_of_lt (ccwCycle_ccw3_of_lt cycD (by decide : (2 : Fin 5) < 3) (by decide : (3 : Fin 5) < 4)))⟩
  by_cases h_all_nf : ∀ m : Fin 5, 0 < orient2D (S (cycD.toFun m)) (S (cycD.toFun (m + 1))) v
  · have h_nf40 : 0 < orient2D v (S b) (S d0) := by
      have h := h_all_nf 4; dsimp [b, d0] at *; unfold orient2D at h ⊢; linarith
    have h_nf23 : 0 < orient2D v (S d2) (S d3) := by
      have h := h_all_nf 2; dsimp [d2, d3] at *; unfold orient2D at h ⊢; linarith
    have h_nf34 : 0 < orient2D v (S d3) (S b) := by
      have h := h_all_nf 3; dsimp [b, d3] at *; unfold orient2D at h ⊢; linarith
    let s0 := posBool (orient2D v q (S d0))
    let s1 := posBool (orient2D v q (S d1))
    let s2 := posBool (orient2D v q (S d2))
    let s3 := posBool (orient2D v q (S d3))
    let s4 := posBool (orient2D v q (S b))
    let sy0 := posBool (orient2D v q (S y0))
    let sy1 := posBool (orient2D v q (S y1))
    have h_not_all : ¬ (s0 = s1 ∧ s0 = s2 ∧ s0 = s3 ∧ s0 = s4) := by
      intro ⟨h1, h2, h3, h4⟩
      exact pentagon_all_nf_not_all_same cycD v q h_all_nf hvq_D (fun m => by
        fin_cases m
        · exact by unfold OnSameSide; exact mul_self_pos.mpr (hvq_D 0)
        · exact onSameSide_of_posBool_eq h1 (hvq_D 0) (hvq_D 1)
        · exact onSameSide_of_posBool_eq h2 (hvq_D 0) (hvq_D 2)
        · exact onSameSide_of_posBool_eq h3 (hvq_D 0) (hvq_D 3)
        · exact onSameSide_of_posBool_eq h4 (hvq_D 0) (hvq_D 4))
    have h_no_alt := pent_no_alt4_of_orient cycD v q hvq_D
    have hy0_eq : s0 = s1 → sy0 = s0 := fun h => exitTri_posBool_of_endpoints hy0_tri h
    have hy1_eq : s1 = s2 → sy1 = s1 := fun h => exitTri_posBool_of_endpoints hy1_tri h
    rcases pentagon_adj_b4_bool s0 s1 s2 s3 s4 sy0 sy1 h_not_all h_no_alt hy0_eq hy1_eq with
      ⟨h40, h0y⟩ | ⟨hy01_b, h1y1⟩ | ⟨hy12_b, h23_b, h34_b⟩
    · have hsee : Sees P v q := by
        by_contra hnq
        have h01' := posBool_eq_of_onSameSide (h_seen_ss d0 d1 h0_out h1_out hnq)
        have h02' := posBool_eq_of_onSameSide (h_seen_ss d0 d2 h0_out h2_out hnq)
        have h03' := posBool_eq_of_onSameSide (h_seen_ss d0 d3 h0_out h3_out hnq)
        exact h_not_all ⟨h01', h02', h03', h40.symm⟩
      have hby0 := orient2D_chain3_pos ⟨h40, h0y⟩ (hvq_D 4) (hvq_D 0) hvq_y0 h_nf40 h0_y0
      exact build_gap0 (goodAnchorPair_of_see hb_O hy0_O hb_ne_y0 hsee
        (onSameSide_of_posBool_eq (h40.trans h0y) (hvq_D 4) hvq_y0) (ne_of_gt hby0)) h_nf40 hby0
    · have hy0_y1 := orient2D_chain3_pos ⟨hy01_b, h1y1⟩ hvq_y0 (hvq_D 1) hvq_y1 hy0_1 h1_y1
      by_cases hsee : Sees P v q
      · exact build_gap1 (goodAnchorPair_of_see hy0_O hy1_O hy01 hsee
          (onSameSide_of_posBool_eq (hy01_b.trans h1y1) hvq_y0 hvq_y1) (ne_of_gt hy0_y1)) hy0_y1
      · have h01' := posBool_eq_of_onSameSide (h_seen_ss d0 d1 h0_out h1_out hsee)
        have h12' := posBool_eq_of_onSameSide (h_seen_ss d1 d2 h1_out h2_out hsee)
        have h0_y0_ss := onSameSide_of_posBool_eq (hy0_eq h01').symm (hvq_D 0) hvq_y0
        have hy1_2_ss := onSameSide_of_posBool_eq ((hy1_eq h12').trans h12') hvq_y1 (hvq_D 2)
        have hss_y01 := onSameSide_of_posBool_eq (hy01_b.trans h1y1) hvq_y0 hvq_y1
        exact build_gap1 (goodAnchorPair_of_cone_ends hy0_O hy1_O hy01 hss_y01 hy0_y1
          (fun hqy0 => ⟨d0, h0_out, by unfold OnSameSide at h0_y0_ss; nlinarith only [h0_y0_ss, hqy0], h0_y0⟩)
          (fun hqy0 => ⟨d2, h2_out, by unfold OnSameSide at hss_y01 hy1_2_ss; nlinarith only [hss_y01, hy1_2_ss, hqy0], hy1_2⟩))
          hy0_y1
    · have hsee : Sees P v q := by
        by_contra hnq
        have h01' := posBool_eq_of_onSameSide (h_seen_ss d0 d1 h0_out h1_out hnq)
        have h02' := posBool_eq_of_onSameSide (h_seen_ss d0 d2 h0_out h2_out hnq)
        have h03' := posBool_eq_of_onSameSide (h_seen_ss d0 d3 h0_out h3_out hnq)
        exact h_not_all ⟨h01', h02', h03', h03'.trans h34_b⟩
      obtain ⟨hy1_3, hd2_4, hy1_4⟩ := orient2D_chain4_pos ⟨hy12_b, h23_b, h34_b⟩
        hvq_y1 (hvq_D 2) (hvq_D 3) (hvq_D 4) hy1_2 h_nf23 h_nf34
      exact build_gap23 (goodAnchorPair_of_see hy1_O hb_O hy1_ne_b hsee
        (onSameSide_of_posBool_eq (hy12_b.trans (h23_b.trans h34_b)) hvq_y1 (hvq_D 4)) (ne_of_gt hy1_4))
        hd2_4 hy1_3 h_nf34 hy1_4
  · push Not at h_all_nf
    obtain ⟨j0, hj0⟩ := h_all_nf
    have hj0_lt : orient2D (S (cycD.toFun j0)) (S (cycD.toFun (j0 + 1))) v < 0 :=
      lt_of_le_of_ne hj0 (hv_noncol j0 (j0 + 1) (fin_add_one_ne_self j0))
    obtain ⟨e_start, e_end, L, hL1, hL_le, he_end_eq, h_face_lt, _, _, _, _, h_ang⟩ :=
      facing_arc_complement_order cycD v hv_noncol ⟨j0, hj0_lt⟩
    have hcase := pent_facing_cases_adjB4 e_start e_end L hL1 hL_le he_end_eq
      (fun h => by have hf := h_face_lt 0 h; change orient2D (S d0) (S d1) v < 0 at hf; linarith)
      (fun h => by have hf := h_face_lt 1 h; change orient2D (S d1) (S d2) v < 0 at hf; linarith)
      (fun ⟨h3, h4⟩ => by
        rw [isFrontVertexOf_iff_ccwCycle cycD 4 v] at hb_nf
        exact hb_nf ⟨h_face_lt 3 h3, h_face_lt 4 h4⟩)
    rcases hcase with ⟨rfl, rfl, _⟩ | ⟨ho1, ho2, ho3, ho4⟩
    · -- e_start = 4, e_end = 0: chain 0 -> y0 -> 1 -> y1 -> 2 -> 3 -> 4
      have h_ord : ∀ a c : Fin 5, (a - 0).val < (c - 0).val → (c - 0).val ≤ (4 - 0 : Fin 5).val →
          0 < orient2D v (S (cycD.toFun a)) (S (cycD.toFun c)) :=
        fun a c h1 h2 => (h_ang a c h1 h2).2
      have h02 := h_ord 0 2 (by decide) (by decide)
      have h03 := h_ord 0 3 (by decide) (by decide)
      have h04 := h_ord 0 4 (by decide) (by decide)
      have h13 := h_ord 1 3 (by decide) (by decide)
      have h14 := h_ord 1 4 (by decide) (by decide)
      have h24 := h_ord 2 4 (by decide) (by decide)
      have h34 := h_ord 3 4 (by decide) (by decide)
      have hy0_y1 := exitTri_orient_after hy0_tri
        (exitTri_orient_before hy1_tri (h_ord 0 1 (by decide) (by decide)) h02) h1_y1
      have hy1_3 := exitTri_orient_after hy1_tri h13 (h_ord 2 3 (by decide) (by decide))
      have hy1_4 := exitTri_orient_after hy1_tri h14 h24
      have hy0_4 := exitTri_orient_after hy0_tri h04 h14
      by_cases hsee : Sees P v q
      · rcases three_missed_in_cone_pigeonhole v q (S y0) (S y1) (S b) hvq_y0 hvq_y1 (hvq_D 4)
          hy0_y1 hy1_4 hy0_4 with hss_y01 | hss_y1b
        · exact build_gap1 (goodAnchorPair_of_see hy0_O hy1_O hy01 hsee hss_y01 (ne_of_gt hy0_y1)) hy0_y1
        · exact build_gap23 (goodAnchorPair_of_see hy1_O hb_O hy1_ne_b hsee hss_y1b (ne_of_gt hy1_4))
            h24 hy1_3 h34 hy1_4
      · have hss01 := h_seen_ss d0 d1 h0_out h1_out hsee
        have hss12 := h_seen_ss d1 d2 h1_out h2_out hsee
        have hss0_y0 := (exitTri_sameSide_of_in_L hy0_tri hss01).1
        have hss_y01 := (exitTri_sameSide_of_in_L hy0_tri hss01).2
        have hss1_y1 := (exitTri_sameSide_of_in_L hy1_tri hss12).1
        have hss_y12 := (exitTri_sameSide_of_in_L hy1_tri hss12).2
        have hss_y0_y1 : OnSameSide v q (S y0) (S y1) := hss_y01.trans hss1_y1
        exact build_gap1 (goodAnchorPair_of_cone_ends hy0_O hy1_O hy01 hss_y0_y1 hy0_y1
          (fun hqy0 => ⟨d0, h0_out, by unfold OnSameSide at hss0_y0; nlinarith only [hss0_y0, hqy0], h0_y0⟩)
          (fun hqy0 => ⟨d2, h2_out, by unfold OnSameSide at hss_y0_y1 hss_y12; nlinarith only [hss_y0_y1, hss_y12, hqy0], hy1_2⟩))
          hy0_y1
    · -- unified {4, 0, 1, 2} chain:
      have h40 := (h_ang 4 0 ho1 (le_trans (le_of_lt ho2) (le_trans (le_of_lt ho3) ho4))).2
      have h41 := (h_ang 4 1 (lt_trans ho1 ho2) (le_trans (le_of_lt ho3) ho4)).2
      have h42 := (h_ang 4 2 (lt_trans ho1 (lt_trans ho2 ho3)) ho4).2
      have h02 := (h_ang 0 2 (lt_trans ho2 ho3) ho4).2
      have h4_y0 := exitTri_orient_before hy0_tri h40 h41
      have h4_y1 := exitTri_orient_before hy1_tri h41 h42
      have hy0_y1 := exitTri_orient_after hy0_tri
        (exitTri_orient_before hy1_tri (h_ang 0 1 ho2 (le_trans (le_of_lt ho3) ho4)).2 h02) h1_y1
      by_cases hsee : Sees P v q
      · rcases three_missed_in_cone_pigeonhole v q (S b) (S y0) (S y1) (hvq_D 4) hvq_y0 hvq_y1
          h4_y0 hy0_y1 h4_y1 with hss_4y0 | hss_y01
        · exact build_gap0 (goodAnchorPair_of_see hb_O hy0_O hb_ne_y0 hsee hss_4y0 (ne_of_gt h4_y0)) h40 h4_y0
        · exact build_gap1 (goodAnchorPair_of_see hy0_O hy1_O hy01 hsee hss_y01 (ne_of_gt hy0_y1)) hy0_y1
      · have hss01 := h_seen_ss d0 d1 h0_out h1_out hsee
        have hss12 := h_seen_ss d1 d2 h1_out h2_out hsee
        have hss0_y0 := (exitTri_sameSide_of_in_L hy0_tri hss01).1
        have hss_y01 := (exitTri_sameSide_of_in_L hy0_tri hss01).2
        have hss1_y1 := (exitTri_sameSide_of_in_L hy1_tri hss12).1
        have hss_y12 := (exitTri_sameSide_of_in_L hy1_tri hss12).2
        have hss_y0_y1 : OnSameSide v q (S y0) (S y1) := hss_y01.trans hss1_y1
        exact build_gap1 (goodAnchorPair_of_cone_ends hy0_O hy1_O hy01 hss_y0_y1 hy0_y1
          (fun hqy0 => ⟨d0, h0_out, by unfold OnSameSide at hss0_y0; nlinarith only [hss0_y0, hqy0], h0_y0⟩)
          (fun hqy0 => ⟨d2, h2_out, by unfold OnSameSide at hss_y0_y1 hss_y12; nlinarith only [hss_y0_y1, hss_y12, hqy0], hy1_2⟩))
          hy0_y1


/-- **Lemma 6.10 (`adjacent-exits`, `b = 3`, `upper_9.tex` lines 777–788)**:
    Symmetric counterpart of `adjacent_exits_b4` for `O* = {y0, y1, 3}` and `v = w (S \ O*)`:
    at least one of the three gaps `{4, 0}` (anchors `{3, y0}`), `{1}` (anchors `{y0, y1}`), or
    `{2}` (anchors `{y1, 3}`) is a good gap for `v`. -/
theorem adjacent_exits_b3 {n : ℕ} {P : Set (ℝ × ℝ)}
    {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ}
    (hPoly : ShatteredSimplePolygon P S w) (h25 : Sec2To5Interface P S w)
    {D : Finset (Fin n)} (hDB : D = hullVertices S \ certifiedVertices S w)
    (cycD : CCWCycle S D 2)
    {y0 y1 : Fin n} (hy0M : y0 ∈ Finset.univ \ D) (hy1M : y1 ∈ Finset.univ \ D) (hy01 : y0 ≠ y1)
    (hy0_tri : InIntTri (w (Finset.univ \ {cycD.toFun 3, y0, y1})) (S (cycD.toFun 0)) (S (cycD.toFun 1)) (S y0))
    (hy1_tri : InIntTri (w (Finset.univ \ {cycD.toFun 3, y0, y1})) (S (cycD.toFun 1)) (S (cycD.toFun 2)) (S y1))
    (h_not_lr : ∀ l r : Fin n, (certifiedVertices S w).Nonempty →
      IsCCWEdge S D l r → (∀ h ∈ certifiedVertices S w, orient2D (S l) (S r) (S h) < 0) →
      (cycD.toFun 0, cycD.toFun 1) ≠ (l, r) ∧ (cycD.toFun 1, cycD.toFun 2) ≠ (l, r)) :
    let b := cycD.toFun 3
    let O_star : Finset (Fin n) := {b, y0, y1}
    let v := w (Finset.univ \ O_star)
    ∃ (oa ob : Fin n) (Γ : Finset (Fin n)),
      ((oa = b ∧ ob = y0 ∧ Γ = {cycD.toFun 4, cycD.toFun 0}) ∨
       (oa = y0 ∧ ob = y1 ∧ Γ = {cycD.toFun 1}) ∨
       (oa = y1 ∧ ob = b ∧ Γ = {cycD.toFun 2})) ∧
      GoodAnchorPair P S w O_star oa ob ∧
      (∀ p ∈ Γ,
        IsBackVertexOf S (hullVertices S) p v ∧
        SegmentsCross v (S p) (S oa) (S ob) ∧
        (∃ H_hp : OpenHalfPlane, IsHalfPlaneTest P (WitnessSet {oa, ob} ∅ w) (S p) H_hp)) ∧
      (∀ z : Fin n, z ≠ oa → z ≠ ob → z ∉ O_star →
        S z ∈ convexHull ℝ ((Γ ∪ {oa, ob}).image S : Set (ℝ × ℝ)) →
        SegmentsCross v (S z) (S oa) (S ob) ∧
        (∃ H_hp : OpenHalfPlane, IsHalfPlaneTest P (WitnessSet {oa, ob} ∅ w) (S z) H_hp) ∧
        (z ∈ hullVertices S → IsBackVertexOf S (hullVertices S) z v)) := by
  intro b O_star v
  let d0 := cycD.toFun 0
  let d1 := cycD.toFun 1
  let d2 := cycD.toFun 2
  let d4 := cycD.toFun 4
  let q := w Finset.univ
  have hy0_notD : y0 ∉ D := (Finset.mem_sdiff.mp hy0M).2
  have hy1_notD : y1 ∉ D := (Finset.mem_sdiff.mp hy1M).2
  obtain ⟨hm_out, hb_nf, hv_noncol, hvq_D, hvq_y0, hvq_y1, h_seen_ss⟩ :=
    pentagon_Ostar_core hPoly h25 hDB cycD hy0M hy1M hy01 3
  have h0_out : d0 ∉ O_star := hm_out 0 (by decide)
  have h1_out : d1 ∉ O_star := hm_out 1 (by decide)
  have h2_out : d2 ∉ O_star := hm_out 2 (by decide)
  have h4_out : d4 ∉ O_star := hm_out 4 (by decide)
  have hB : D ⊆ hullVertices S := hDB ▸ Finset.sdiff_subset
  have h0B : d0 ∈ hullVertices S := hB (ccwCycle_mem cycD 0)
  have h1B : d1 ∈ hullVertices S := hB (ccwCycle_mem cycD 1)
  have h2B : d2 ∈ hullVertices S := hB (ccwCycle_mem cycD 2)
  have h4B : d4 ∈ hullVertices S := hB (ccwCycle_mem cycD 4)
  have hb_O : b ∈ O_star := Finset.mem_insert_self _ _
  have hy0_O : y0 ∈ O_star := Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  have hy1_O : y1 ∈ O_star := Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  have hb_ne_y0 : b ≠ y0 := fun h => hy0_notD (h ▸ ccwCycle_mem cycD 3)
  have hy1_ne_b : y1 ≠ b := fun h => hy1_notD (h.symm ▸ ccwCycle_mem cycD 3)
  have h01_nf : 0 < orient2D (S d0) (S d1) v :=
    pentagon_exit_nonfacing hPoly h25 hDB cycD hy0M 0 hy0_tri (fun l r hH he hHn => (h_not_lr l r hH he hHn).1)
  have h12_nf : 0 < orient2D (S d1) (S d2) v :=
    pentagon_exit_nonfacing hPoly h25 hDB cycD hy1M 1 hy1_tri (fun l r hH he hHn => (h_not_lr l r hH he hHn).2)
  have ⟨h0_y0, hy0_1, h01⟩ := exitTri_orient2D_from_left hy0_tri h01_nf
  have ⟨h1_y1, hy1_2, h12⟩ := exitTri_orient2D_from_left hy1_tri h12_nf
  have h_01_y1 : 0 < orient2D (S d0) (S d1) (S y1) :=
    exitTri_convex_comb_orient_pos hy1_tri h01_nf (by rw [orient2D_self_right])
      (le_of_lt (ccwCycle_ccw3_of_lt cycD (by decide : (0 : Fin 5) < 1) (by decide : (1 : Fin 5) < 2)))
  have build_gap40 : GoodAnchorPair P S w O_star b y0 →
      0 < orient2D v (S b) (S d4) → 0 < orient2D v (S d4) (S y0) →
      0 < orient2D v (S d0) (S y0) → 0 < orient2D v (S b) (S d0) →
      0 < orient2D v (S b) (S y0) →
      ∃ (oa ob : Fin n) (Γ : Finset (Fin n)),
        ((oa = b ∧ ob = y0 ∧ Γ = {d4, d0}) ∨
         (oa = y0 ∧ ob = y1 ∧ Γ = {d1}) ∨
         (oa = y1 ∧ ob = b ∧ Γ = {d2})) ∧
        GoodAnchorPair P S w O_star oa ob ∧
        (∀ p ∈ Γ, IsBackVertexOf S (hullVertices S) p v ∧ SegmentsCross v (S p) (S oa) (S ob) ∧
          (∃ H_hp : OpenHalfPlane, IsHalfPlaneTest P (WitnessSet {oa, ob} ∅ w) (S p) H_hp)) ∧
        (∀ z : Fin n, z ≠ oa → z ≠ ob → z ∉ O_star →
          S z ∈ convexHull ℝ ((Γ ∪ {oa, ob}).image S : Set (ℝ × ℝ)) →
          SegmentsCross v (S z) (S oa) (S ob) ∧
          (∃ H_hp : OpenHalfPlane, IsHalfPlaneTest P (WitnessSet {oa, ob} ∅ w) (S z) H_hp) ∧
          (z ∈ hullVertices S → IsBackVertexOf S (hullVertices S) z v)) := by
    intro hgap h34 h4y0 h0y0 h30 hby0
    refine ⟨b, y0, {d4, d0}, Or.inl ⟨rfl, rfl, rfl⟩, hgap, good_gap_of_all_cross hPoly h25 hgap (fun p hp => ?_)⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl
    · refine ⟨cycD.inj.ne (by decide : (4 : Fin 5) ≠ 3), fun h => hy0_notD (h ▸ ccwCycle_mem cycD 4),
        h4_out, h4B, segmentsCross_inIntTri_left hy0_tri h34 h4y0 hby0
          (le_of_lt (by have h := ccwCycle_ccw3_of_lt cycD (by decide : (0 : Fin 5) < 3) (by decide : (3 : Fin 5) < 4); unfold orient2D at h ⊢; linarith))
          (by have h := ccwCycle_ccw3_of_lt cycD (by decide : (1 : Fin 5) < 3) (by decide : (3 : Fin 5) < 4); unfold orient2D at h ⊢; linarith)⟩
    · refine ⟨cycD.inj.ne (by decide : (0 : Fin 5) ≠ 3), fun h => hy0_notD (h ▸ ccwCycle_mem cycD 0),
        h0_out, h0B, segmentsCross_inIntTri_left hy0_tri h30 h0y0 hby0 (by rw [orient2D_self_right])
          (by have h := ccwCycle_ccw3_of_lt cycD (by decide : (0 : Fin 5) < 1) (by decide : (1 : Fin 5) < 3); dsimp [b, d0, d1]; unfold orient2D at h ⊢; linarith)⟩
  have build_gap1 : GoodAnchorPair P S w O_star y0 y1 → 0 < orient2D v (S y0) (S y1) →
      ∃ (oa ob : Fin n) (Γ : Finset (Fin n)),
        ((oa = b ∧ ob = y0 ∧ Γ = {d4, d0}) ∨
         (oa = y0 ∧ ob = y1 ∧ Γ = {d1}) ∨
         (oa = y1 ∧ ob = b ∧ Γ = {d2})) ∧
        GoodAnchorPair P S w O_star oa ob ∧
        (∀ p ∈ Γ, IsBackVertexOf S (hullVertices S) p v ∧ SegmentsCross v (S p) (S oa) (S ob) ∧
          (∃ H_hp : OpenHalfPlane, IsHalfPlaneTest P (WitnessSet {oa, ob} ∅ w) (S p) H_hp)) ∧
        (∀ z : Fin n, z ≠ oa → z ≠ ob → z ∉ O_star →
          S z ∈ convexHull ℝ ((Γ ∪ {oa, ob}).image S : Set (ℝ × ℝ)) →
          SegmentsCross v (S z) (S oa) (S ob) ∧
          (∃ H_hp : OpenHalfPlane, IsHalfPlaneTest P (WitnessSet {oa, ob} ∅ w) (S z) H_hp) ∧
          (z ∈ hullVertices S → IsBackVertexOf S (hullVertices S) z v)) := by
    intro hgap hy0_y1
    refine ⟨y0, y1, {d1}, Or.inr (Or.inl ⟨rfl, rfl, rfl⟩), hgap, good_gap_of_all_cross hPoly h25 hgap (fun p hp => ?_)⟩
    rw [Finset.mem_singleton] at hp; subst hp
    refine ⟨fun h => hy0_notD (h.symm ▸ ccwCycle_mem cycD 1), fun h => hy1_notD (h.symm ▸ ccwCycle_mem cycD 1),
      h1_out, h1B, segmentsCross_between_exits_shared (u1 := (0, 0)) hy0_tri hy0_1 h1_y1 hy0_y1 h_01_y1⟩
  have build_gap2 : GoodAnchorPair P S w O_star y1 b →
      0 < orient2D v (S d2) (S b) → 0 < orient2D v (S y1) (S b) →
      ∃ (oa ob : Fin n) (Γ : Finset (Fin n)),
        ((oa = b ∧ ob = y0 ∧ Γ = {d4, d0}) ∨
         (oa = y0 ∧ ob = y1 ∧ Γ = {d1}) ∨
         (oa = y1 ∧ ob = b ∧ Γ = {d2})) ∧
        GoodAnchorPair P S w O_star oa ob ∧
        (∀ p ∈ Γ, IsBackVertexOf S (hullVertices S) p v ∧ SegmentsCross v (S p) (S oa) (S ob) ∧
          (∃ H_hp : OpenHalfPlane, IsHalfPlaneTest P (WitnessSet {oa, ob} ∅ w) (S p) H_hp)) ∧
        (∀ z : Fin n, z ≠ oa → z ≠ ob → z ∉ O_star →
          S z ∈ convexHull ℝ ((Γ ∪ {oa, ob}).image S : Set (ℝ × ℝ)) →
          SegmentsCross v (S z) (S oa) (S ob) ∧
          (∃ H_hp : OpenHalfPlane, IsHalfPlaneTest P (WitnessSet {oa, ob} ∅ w) (S z) H_hp) ∧
          (z ∈ hullVertices S → IsBackVertexOf S (hullVertices S) z v)) := by
    intro hgap h23 hy1_b
    refine ⟨y1, b, {d2}, Or.inr (Or.inr ⟨rfl, rfl, rfl⟩), hgap, good_gap_of_all_cross hPoly h25 hgap (fun p hp => ?_)⟩
    rw [Finset.mem_singleton] at hp; subst hp
    refine ⟨fun h => hy1_notD (h.symm ▸ ccwCycle_mem cycD 2), cycD.inj.ne (by decide : (2 : Fin 5) ≠ 3),
      h2_out, h2B, segmentsCross_inIntTri_right hy1_tri hy1_2 h23 hy1_b
        (ccwCycle_ccw3_of_lt cycD (by decide : (1 : Fin 5) < 2) (by decide : (2 : Fin 5) < 3)) (by dsimp [d2]; rw [orient2D_self_left])⟩
  by_cases h_all_nf : ∀ m : Fin 5, 0 < orient2D (S (cycD.toFun m)) (S (cycD.toFun (m + 1))) v
  · have h_nf34 : 0 < orient2D v (S b) (S d4) := by
      have h := h_all_nf 3; dsimp [b, d4] at *; unfold orient2D at h ⊢; linarith
    have h_nf40 : 0 < orient2D v (S d4) (S d0) := by
      have h := h_all_nf 4; dsimp [d4, d0] at *; unfold orient2D at h ⊢; linarith
    have h_nf23 : 0 < orient2D v (S d2) (S b) := by
      have h := h_all_nf 2; dsimp [b, d2] at *; unfold orient2D at h ⊢; linarith
    let s0 := posBool (orient2D v q (S d0))
    let s1 := posBool (orient2D v q (S d1))
    let s2 := posBool (orient2D v q (S d2))
    let s3 := posBool (orient2D v q (S b))
    let s4 := posBool (orient2D v q (S d4))
    let sy0 := posBool (orient2D v q (S y0))
    let sy1 := posBool (orient2D v q (S y1))
    have h_not_all : ¬ (s0 = s1 ∧ s0 = s2 ∧ s0 = s3 ∧ s0 = s4) := by
      intro ⟨h1, h2, h3, h4⟩
      exact pentagon_all_nf_not_all_same cycD v q h_all_nf hvq_D (fun m => by
        fin_cases m
        · exact by unfold OnSameSide; exact mul_self_pos.mpr (hvq_D 0)
        · exact onSameSide_of_posBool_eq h1 (hvq_D 0) (hvq_D 1)
        · exact onSameSide_of_posBool_eq h2 (hvq_D 0) (hvq_D 2)
        · exact onSameSide_of_posBool_eq h3 (hvq_D 0) (hvq_D 3)
        · exact onSameSide_of_posBool_eq h4 (hvq_D 0) (hvq_D 4))
    have h_no_alt := pent_no_alt4_of_orient cycD v q hvq_D
    have hy0_eq : s0 = s1 → sy0 = s0 := fun h => exitTri_posBool_of_endpoints hy0_tri h
    have hy1_eq : s1 = s2 → sy1 = s1 := fun h => exitTri_posBool_of_endpoints hy1_tri h
    rcases pentagon_adj_b3_bool s0 s1 s2 s3 s4 sy0 sy1 h_not_all h_no_alt hy0_eq hy1_eq with
      ⟨h34_b, h40_b, h0y⟩ | ⟨hy01_b, h1y1⟩ | ⟨hy12_b, h23_b⟩
    · have hsee : Sees P v q := by
        by_contra hnq
        have h01' := posBool_eq_of_onSameSide (h_seen_ss d0 d1 h0_out h1_out hnq)
        have h02' := posBool_eq_of_onSameSide (h_seen_ss d0 d2 h0_out h2_out hnq)
        have h04' := posBool_eq_of_onSameSide (h_seen_ss d0 d4 h0_out h4_out hnq)
        exact h_not_all ⟨h01', h02', h04'.trans h34_b.symm, h04'⟩
      obtain ⟨h30, h4y0, hby0⟩ := orient2D_chain4_pos ⟨h34_b, h40_b, h0y⟩
        (hvq_D 3) (hvq_D 4) (hvq_D 0) hvq_y0 h_nf34 h_nf40 h0_y0
      exact build_gap40 (goodAnchorPair_of_see hb_O hy0_O hb_ne_y0 hsee
        (onSameSide_of_posBool_eq (h34_b.trans (h40_b.trans h0y)) (hvq_D 3) hvq_y0) (ne_of_gt hby0))
        h_nf34 h4y0 h0_y0 h30 hby0
    · have hy0_y1 := orient2D_chain3_pos ⟨hy01_b, h1y1⟩ hvq_y0 (hvq_D 1) hvq_y1 hy0_1 h1_y1
      by_cases hsee : Sees P v q
      · exact build_gap1 (goodAnchorPair_of_see hy0_O hy1_O hy01 hsee
          (onSameSide_of_posBool_eq (hy01_b.trans h1y1) hvq_y0 hvq_y1) (ne_of_gt hy0_y1)) hy0_y1
      · have h01' := posBool_eq_of_onSameSide (h_seen_ss d0 d1 h0_out h1_out hsee)
        have h12' := posBool_eq_of_onSameSide (h_seen_ss d1 d2 h1_out h2_out hsee)
        have h0_y0_ss := onSameSide_of_posBool_eq (hy0_eq h01').symm (hvq_D 0) hvq_y0
        have hy1_2_ss := onSameSide_of_posBool_eq ((hy1_eq h12').trans h12') hvq_y1 (hvq_D 2)
        have hss_y01 := onSameSide_of_posBool_eq (hy01_b.trans h1y1) hvq_y0 hvq_y1
        exact build_gap1 (goodAnchorPair_of_cone_ends hy0_O hy1_O hy01 hss_y01 hy0_y1
          (fun hqy0 => ⟨d0, h0_out, by unfold OnSameSide at h0_y0_ss; nlinarith only [h0_y0_ss, hqy0], h0_y0⟩)
          (fun hqy0 => ⟨d2, h2_out, by unfold OnSameSide at hss_y01 hy1_2_ss; nlinarith only [hss_y01, hy1_2_ss, hqy0], hy1_2⟩))
          hy0_y1
    · have hsee : Sees P v q := by
        by_contra hnq
        have h01' := posBool_eq_of_onSameSide (h_seen_ss d0 d1 h0_out h1_out hnq)
        have h02' := posBool_eq_of_onSameSide (h_seen_ss d0 d2 h0_out h2_out hnq)
        have h04' := posBool_eq_of_onSameSide (h_seen_ss d0 d4 h0_out h4_out hnq)
        exact h_not_all ⟨h01', h02', h02'.trans h23_b, h04'⟩
      have hy1_3 := orient2D_chain3_pos ⟨hy12_b, h23_b⟩ hvq_y1 (hvq_D 2) (hvq_D 3) hy1_2 h_nf23
      exact build_gap2 (goodAnchorPair_of_see hy1_O hb_O hy1_ne_b hsee
        (onSameSide_of_posBool_eq (hy12_b.trans h23_b) hvq_y1 (hvq_D 3)) (ne_of_gt hy1_3)) h_nf23 hy1_3
  · push Not at h_all_nf
    obtain ⟨j0, hj0⟩ := h_all_nf
    have hj0_lt : orient2D (S (cycD.toFun j0)) (S (cycD.toFun (j0 + 1))) v < 0 :=
      lt_of_le_of_ne hj0 (hv_noncol j0 (j0 + 1) (fin_add_one_ne_self j0))
    obtain ⟨e_start, e_end, L, hL1, hL_le, he_end_eq, h_face_lt, _, _, _, _, h_ang⟩ :=
      facing_arc_complement_order cycD v hv_noncol ⟨j0, hj0_lt⟩
    have hcase := pent_facing_cases_adjB3 e_start e_end L hL1 hL_le he_end_eq
      (fun h => by have hf := h_face_lt 0 h; change orient2D (S d0) (S d1) v < 0 at hf; linarith)
      (fun h => by have hf := h_face_lt 1 h; change orient2D (S d1) (S d2) v < 0 at hf; linarith)
      (fun ⟨h2, h3⟩ => by
        rw [isFrontVertexOf_iff_ccwCycle cycD 3 v] at hb_nf
        exact hb_nf ⟨h_face_lt 2 h2, h_face_lt 3 h3⟩)
    rcases hcase with ⟨rfl, rfl, _⟩ | ⟨ho1, ho2, ho3, ho4⟩
    · -- e_start = 2, e_end = 3: chain 3 -> 4 -> 0 -> y0 -> 1 -> y1 -> 2
      have h_ord : ∀ a c : Fin 5, (a - 3).val < (c - 3).val → (c - 3).val ≤ (2 - 3 : Fin 5).val →
          0 < orient2D v (S (cycD.toFun a)) (S (cycD.toFun c)) :=
        fun a c h1 h2 => (h_ang a c h1 h2).2
      have h34 := h_ord 3 4 (by decide) (by decide)
      have h30 := h_ord 3 0 (by decide) (by decide)
      have h31 := h_ord 3 1 (by decide) (by decide)
      have h40 := h_ord 4 0 (by decide) (by decide)
      have h41 := h_ord 4 1 (by decide) (by decide)
      have h02 := h_ord 0 2 (by decide) (by decide)
      have h3_y0 := exitTri_orient_before hy0_tri h30 h31
      have h4_y0 := exitTri_orient_before hy0_tri h40 h41
      have h3_y1 := exitTri_orient_before hy1_tri h31 (h_ord 3 2 (by decide) (by decide))
      have hy0_y1 := exitTri_orient_after hy0_tri
        (exitTri_orient_before hy1_tri (h_ord 0 1 (by decide) (by decide)) h02) h1_y1
      by_cases hsee : Sees P v q
      · rcases three_missed_in_cone_pigeonhole v q (S b) (S y0) (S y1) (hvq_D 3) hvq_y0 hvq_y1
          h3_y0 hy0_y1 h3_y1 with hss_3y0 | hss_y01
        · exact build_gap40 (goodAnchorPair_of_see hb_O hy0_O hb_ne_y0 hsee hss_3y0 (ne_of_gt h3_y0))
            h34 h4_y0 h0_y0 h30 h3_y0
        · exact build_gap1 (goodAnchorPair_of_see hy0_O hy1_O hy01 hsee hss_y01 (ne_of_gt hy0_y1)) hy0_y1
      · have hss01 := h_seen_ss d0 d1 h0_out h1_out hsee
        have hss12 := h_seen_ss d1 d2 h1_out h2_out hsee
        have hss0_y0 := (exitTri_sameSide_of_in_L hy0_tri hss01).1
        have hss_y01 := (exitTri_sameSide_of_in_L hy0_tri hss01).2
        have hss1_y1 := (exitTri_sameSide_of_in_L hy1_tri hss12).1
        have hss_y12 := (exitTri_sameSide_of_in_L hy1_tri hss12).2
        have hss_y0_y1 : OnSameSide v q (S y0) (S y1) := hss_y01.trans hss1_y1
        exact build_gap1 (goodAnchorPair_of_cone_ends hy0_O hy1_O hy01 hss_y0_y1 hy0_y1
          (fun hqy0 => ⟨d0, h0_out, by unfold OnSameSide at hss0_y0; nlinarith only [hss0_y0, hqy0], h0_y0⟩)
          (fun hqy0 => ⟨d2, h2_out, by unfold OnSameSide at hss_y0_y1 hss_y12; nlinarith only [hss_y0_y1, hss_y12, hqy0], hy1_2⟩))
          hy0_y1
    · -- unified {0, 1, 2, 3} chain
      have h02 := (h_ang 0 2 (lt_trans ho1 ho2) (le_trans (le_of_lt ho3) ho4)).2
      have h03 := (h_ang 0 3 (lt_trans ho1 (lt_trans ho2 ho3)) ho4).2
      have h13 := (h_ang 1 3 (lt_trans ho2 ho3) ho4).2
      have h23 := (h_ang 2 3 ho3 ho4).2
      have hy0_y1 := exitTri_orient_after hy0_tri
        (exitTri_orient_before hy1_tri (h_ang 0 1 ho1 (le_trans (le_of_lt ho2) (le_trans (le_of_lt ho3) ho4))).2 h02)
        h1_y1
      have hy1_3 := exitTri_orient_after hy1_tri h13 h23
      have hy0_3 := exitTri_orient_after hy0_tri h03 h13
      by_cases hsee : Sees P v q
      · rcases three_missed_in_cone_pigeonhole v q (S y0) (S y1) (S b) hvq_y0 hvq_y1 (hvq_D 3)
          hy0_y1 hy1_3 hy0_3 with hss_y01 | hss_y1b
        · exact build_gap1 (goodAnchorPair_of_see hy0_O hy1_O hy01 hsee hss_y01 (ne_of_gt hy0_y1)) hy0_y1
        · exact build_gap2 (goodAnchorPair_of_see hy1_O hb_O hy1_ne_b hsee hss_y1b (ne_of_gt hy1_3)) h23 hy1_3
      · have hss01 := h_seen_ss d0 d1 h0_out h1_out hsee
        have hss12 := h_seen_ss d1 d2 h1_out h2_out hsee
        have hss0_y0 := (exitTri_sameSide_of_in_L hy0_tri hss01).1
        have hss_y01 := (exitTri_sameSide_of_in_L hy0_tri hss01).2
        have hss1_y1 := (exitTri_sameSide_of_in_L hy1_tri hss12).1
        have hss_y12 := (exitTri_sameSide_of_in_L hy1_tri hss12).2
        have hss_y0_y1 : OnSameSide v q (S y0) (S y1) := hss_y01.trans hss1_y1
        exact build_gap1 (goodAnchorPair_of_cone_ends hy0_O hy1_O hy01 hss_y0_y1 hy0_y1
          (fun hqy0 => ⟨d0, h0_out, by unfold OnSameSide at hss0_y0; nlinarith only [hss0_y0, hqy0], h0_y0⟩)
          (fun hqy0 => ⟨d2, h2_out, by unfold OnSameSide at hss_y0_y1 hss_y12; nlinarith only [hss_y0_y1, hss_y12, hqy0], hy1_2⟩))
          hy0_y1
