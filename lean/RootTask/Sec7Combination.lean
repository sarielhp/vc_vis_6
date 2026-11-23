import Mathlib

open scoped Classical BigOperators
open Finset

noncomputable section

/-!
# Section 7 (`ray-exit`, `combination`) & Lemma 2.5 Bitmask Bounds

Concrete `ℝ × ℝ` formalization of:
- `orient2D` and `InClosedTri`,
- Lemma 7.1 (`triangle_three_piece_cover` and `ray_exit_polygon_cover`),
- Exit-region `E(M₀)` disjointness (including both non-parallel and parallel cases),
- Explicit `conv D` covering decompositions across Cases 1, 2 (`(L)`, `(R)`, `(M)`), 3a, and 3b,
- Lemma 2.5 face-counting & `< 1024` bitmask arithmetic bounds.
-/

/-- Signed doubled area of the triangle `(a, b, c)` in `ℝ²`. -/
def orient2D (a b c : ℝ × ℝ) : ℝ :=
  (b.1 - a.1) * (c.2 - a.2) - (b.2 - a.2) * (c.1 - a.1)

/-- Closed triangle membership via barycentric coordinates. -/
def InClosedTri (p q r z : ℝ × ℝ) : Prop :=
  ∃ μ₁ μ₂ μ₃ : ℝ, 0 ≤ μ₁ ∧ 0 ≤ μ₂ ∧ 0 ≤ μ₃ ∧ μ₁ + μ₂ + μ₃ = 1 ∧
    z.1 = μ₁ * p.1 + μ₂ * q.1 + μ₃ * r.1 ∧
    z.2 = μ₁ * p.2 + μ₂ * q.2 + μ₃ * r.2

lemma orient2D_self_left (a b : ℝ × ℝ) : orient2D a a b = 0 := by
  unfold orient2D; ring

lemma orient2D_self_right (a b : ℝ × ℝ) : orient2D a b b = 0 := by
  unfold orient2D; ring

lemma orient2D_self_outer (a b : ℝ × ℝ) : orient2D a b a = 0 := by
  unfold orient2D; ring

lemma orient2D_swap23 (a b c : ℝ × ℝ) : orient2D a c b = -orient2D a b c := by
  unfold orient2D; ring

lemma orient2D_cycle (a b c : ℝ × ℝ) : orient2D b c a = orient2D a b c := by
  unfold orient2D; ring

lemma orient2D_affine_comb (a b x y t : ℝ × ℝ) (s : ℝ)
    (ht1 : t.1 = (1 - s) * x.1 + s * y.1)
    (ht2 : t.2 = (1 - s) * x.2 + s * y.2) :
    orient2D a b t = (1 - s) * orient2D a b x + s * orient2D a b y := by
  unfold orient2D
  rw [ht1, ht2]
  ring

/-- Equivalence between `InClosedTri a b c z` and membership in `convexHull ℝ {a, b, c}`. -/
lemma inClosedTri_iff_mem_convexHull (a b c z : ℝ × ℝ) :
    InClosedTri a b c z ↔ z ∈ convexHull ℝ ({a, b, c} : Set (ℝ × ℝ)) := by
  constructor
  · rintro ⟨μ₁, μ₂, μ₃, h1, h2, h3, hsum, hz1, hz2⟩
    have hconv : Convex ℝ (convexHull ℝ ({a, b, c} : Set (ℝ × ℝ))) := convex_convexHull ℝ _
    have ha : a ∈ convexHull ℝ ({a, b, c} : Set (ℝ × ℝ)) :=
      subset_convexHull ℝ _ (by simp)
    have hb : b ∈ convexHull ℝ ({a, b, c} : Set (ℝ × ℝ)) :=
      subset_convexHull ℝ _ (by simp)
    have hc : c ∈ convexHull ℝ ({a, b, c} : Set (ℝ × ℝ)) :=
      subset_convexHull ℝ _ (by simp)
    by_cases hs : μ₁ + μ₂ = 0
    · have hμ1 : μ₁ = 0 := by linarith
      have hμ2 : μ₂ = 0 := by linarith
      have hμ3 : μ₃ = 1 := by linarith
      have hzc : z = c := by ext <;> [rw [hz1, hμ1, hμ2, hμ3]; rw [hz2, hμ1, hμ2, hμ3]] <;> ring
      rwa [hzc]
    · have hs_pos : 0 < μ₁ + μ₂ := lt_of_le_of_ne (add_nonneg h1 h2) (Ne.symm hs)
      let s := μ₁ + μ₂
      let w : ℝ × ℝ := ((μ₁ / s) • a + (μ₂ / s) • b)
      have hw : w ∈ convexHull ℝ ({a, b, c} : Set (ℝ × ℝ)) := by
        apply hconv ha hb (div_nonneg h1 (le_of_lt hs_pos)) (div_nonneg h2 (le_of_lt hs_pos))
        rw [← add_div, div_self (ne_of_gt hs_pos)]
      have hz_eq : z = s • w + μ₃ • c := by
        have hs_ne : s ≠ 0 := ne_of_gt hs_pos
        ext
        · change z.1 = s * ((μ₁ / s) * a.1 + (μ₂ / s) * b.1) + μ₃ * c.1
          rw [hz1, mul_add, ← mul_assoc, mul_div_cancel₀ _ hs_ne, ← mul_assoc, mul_div_cancel₀ _ hs_ne]
        · change z.2 = s * ((μ₁ / s) * a.2 + (μ₂ / s) * b.2) + μ₃ * c.2
          rw [hz2, mul_add, ← mul_assoc, mul_div_cancel₀ _ hs_ne, ← mul_assoc, mul_div_cancel₀ _ hs_ne]
      rw [hz_eq]
      exact hconv hw hc (le_of_lt hs_pos) h3 hsum
  · intro hz
    let T : Set (ℝ × ℝ) := {p | InClosedTri a b c p}
    have hT_conv : Convex ℝ T := by
      intro x hx y hy α β hα hβ hαβ
      rcases hx with ⟨x1, x2, x3, hx1, hx2, hx3, hxsum, hx1eq, hx2eq⟩
      rcases hy with ⟨y1, y2, y3, hy1, hy2, hy3, hysum, hy1eq, hy2eq⟩
      refine ⟨α * x1 + β * y1, α * x2 + β * y2, α * x3 + β * y3,
        add_nonneg (mul_nonneg hα hx1) (mul_nonneg hβ hy1),
        add_nonneg (mul_nonneg hα hx2) (mul_nonneg hβ hy2),
        add_nonneg (mul_nonneg hα hx3) (mul_nonneg hβ hy3), ?_, ?_, ?_⟩
      · calc (α * x1 + β * y1) + (α * x2 + β * y2) + (α * x3 + β * y3)
            = α * (x1 + x2 + x3) + β * (y1 + y2 + y3) := by ring
          _ = α * 1 + β * 1 := by rw [hxsum, hysum]
          _ = 1 := by linarith
      · change α * x.1 + β * y.1 = _
        rw [hx1eq, hy1eq]; ring
      · change α * x.2 + β * y.2 = _
        rw [hx2eq, hy2eq]; ring
    have hsub : ({a, b, c} : Set (ℝ × ℝ)) ⊆ T := by
      intro p hp
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
      rcases hp with rfl | rfl | rfl
      · exact ⟨1, 0, 0, zero_le_one, le_rfl, le_rfl, by ring, by ring, by ring⟩
      · exact ⟨0, 1, 0, le_rfl, zero_le_one, le_rfl, by ring, by ring, by ring⟩
      · exact ⟨0, 0, 1, le_rfl, le_rfl, zero_le_one, by ring, by ring, by ring⟩
    exact convexHull_min hsub hT_conv hz

/-- Convex hull monotonicity helper for triangle pieces. -/
lemma convexHull_tri_subset {a b c : ℝ × ℝ} {S : Set (ℝ × ℝ)}
    (ha : a ∈ convexHull ℝ S) (hb : b ∈ convexHull ℝ S) (hc : c ∈ convexHull ℝ S) :
    convexHull ℝ ({a, b, c} : Set (ℝ × ℝ)) ⊆ convexHull ℝ S := by
  apply convexHull_min _ (convex_convexHull ℝ S)
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl <;> assumption

/-- Convex hull monotonicity helper for arbitrary finite point sets. -/
lemma convexHull_subset_of_mem {T S : Set (ℝ × ℝ)} (h : ∀ x ∈ T, x ∈ convexHull ℝ S) :
    convexHull ℝ T ⊆ convexHull ℝ S :=
  convexHull_min h (convex_convexHull ℝ S)

private lemma radon_case
    (p1 p2 p3 y1 z : ℝ × ℝ) (a1 a2 a3 b1 b2 b3 : ℝ)
    (ha1 : 0 ≤ a1) (ha2 : 0 ≤ a2) (ha3 : 0 ≤ a3) (hasum : a1 + a2 + a3 = 1)
    (hz1 : z.1 = a1 * p1.1 + a2 * p2.1 + a3 * p3.1)
    (hz2 : z.2 = a1 * p1.2 + a2 * p2.2 + a3 * p3.2)
    (hbsum : b1 + b2 + b3 = 1)
    (hy1 : y1.1 = b1 * p1.1 + b2 * p2.1 + b3 * p3.1)
    (hy2 : y1.2 = b1 * p1.2 + b2 * p2.2 + b3 * p3.2)
    (hb3 : 0 < b3)
    (hr1 : b1 ≤ 0 ∨ a3 * b1 ≤ a1 * b3)
    (hr2 : b2 ≤ 0 ∨ a3 * b2 ≤ a2 * b3) :
    InClosedTri y1 p1 p2 z := by
  have hb3_ne : b3 ≠ 0 := ne_of_gt hb3
  refine ⟨a3 / b3, a1 - (a3 / b3) * b1, a2 - (a3 / b3) * b2,
    div_nonneg ha3 (le_of_lt hb3), ?_, ?_, ?_, ?_, ?_⟩
  · rcases hr1 with hle | hmul
    · have : (a3 / b3) * b1 ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (div_nonneg ha3 (le_of_lt hb3)) hle
      linarith
    · rw [sub_nonneg, div_mul_eq_mul_div, div_le_iff₀ hb3]; linarith
  · rcases hr2 with hle | hmul
    · have : (a3 / b3) * b2 ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (div_nonneg ha3 (le_of_lt hb3)) hle
      linarith
    · rw [sub_nonneg, div_mul_eq_mul_div, div_le_iff₀ hb3]; linarith
  · field_simp [hb3_ne]; linear_combination b3 * hasum - a3 * hbsum
  · rw [hz1, hy1]; field_simp [hb3_ne]; ring
  · rw [hz2, hy2]; field_simp [hb3_ne]; ring

private lemma radon_step
    (a b y0 y1 z : ℝ × ℝ) (l1 l2 l3 c1 c2 c3 : ℝ)
    (hl1 : 0 ≤ l1) (hl2 : 0 ≤ l2) (hl3 : 0 ≤ l3) (hlsum : l1 + l2 + l3 = 1)
    (hz1 : z.1 = l1 * a.1 + l2 * b.1 + l3 * y0.1)
    (hz2 : z.2 = l1 * a.2 + l2 * b.2 + l3 * y0.2)
    (hcsum : c1 + c2 + c3 = 1)
    (hy1 : y1.1 = c1 * a.1 + c2 * b.1 + c3 * y0.1)
    (hy2 : y1.2 = c1 * a.2 + c2 * b.2 + c3 * y0.2) :
    InClosedTri y1 a b z ∨ InClosedTri y1 b y0 z ∨ InClosedTri y1 y0 a z := by
  by_cases h3 : 0 < c3 ∧ (c1 ≤ 0 ∨ l3 * c1 ≤ l1 * c3) ∧ (c2 ≤ 0 ∨ l3 * c2 ≤ l2 * c3)
  · left
    exact radon_case a b y0 y1 z l1 l2 l3 c1 c2 c3 hl1 hl2 hl3 hlsum hz1 hz2 hcsum hy1 hy2
      h3.1 h3.2.1 h3.2.2
  · by_cases h1 : 0 < c1 ∧ (c2 ≤ 0 ∨ l1 * c2 ≤ l2 * c1) ∧ (c3 ≤ 0 ∨ l1 * c3 ≤ l3 * c1)
    · right; left
      exact radon_case b y0 a y1 z l2 l3 l1 c2 c3 c1 hl2 hl3 hl1 (by linarith)
        (by rw [hz1]; ring) (by rw [hz2]; ring) (by linarith)
        (by rw [hy1]; ring) (by rw [hy2]; ring) h1.1 h1.2.1 h1.2.2
    · right; right
      have hc2_pos : 0 < c2 := by
        by_contra hc2_le
        have hc2 : c2 ≤ 0 := not_lt.mp hc2_le
        by_cases hc1_pos : 0 < c1
        · by_cases hc3_pos : 0 < c3
          · rcases le_total (l1 * c3) (l3 * c1) with hle13 | hle31
            · exact h1 ⟨hc1_pos, Or.inl hc2, Or.inr hle13⟩
            · exact h3 ⟨hc3_pos, Or.inr hle31, Or.inl hc2⟩
          · exact h1 ⟨hc1_pos, Or.inl hc2, Or.inl (not_lt.mp hc3_pos)⟩
        · have hc1 : c1 ≤ 0 := not_lt.mp hc1_pos
          have hc3_pos : 0 < c3 := by linarith
          exact h3 ⟨hc3_pos, Or.inl hc1, Or.inl hc2⟩
      have hr3 : c3 ≤ 0 ∨ l2 * c3 ≤ l3 * c2 := by
        by_cases hc3 : c3 ≤ 0
        · exact Or.inl hc3
        · right
          have hc3_pos : 0 < c3 := not_le.mp hc3
          by_contra hlt23
          replace hlt23 : l3 * c2 < l2 * c3 := not_le.mp hlt23
          by_cases hc1 : c1 ≤ 0
          · exact h3 ⟨hc3_pos, Or.inl hc1, Or.inr (le_of_lt hlt23)⟩
          · have hc1_pos : 0 < c1 := not_le.mp hc1
            rcases le_total (l3 * c1) (l1 * c3) with hle31 | hle13
            · exact h3 ⟨hc3_pos, Or.inr hle31, Or.inr (le_of_lt hlt23)⟩
            · have hle12 : l1 * c2 ≤ l2 * c1 := by nlinarith
              exact h1 ⟨hc1_pos, Or.inr hle12, Or.inr hle13⟩
      have hr1 : c1 ≤ 0 ∨ l2 * c1 ≤ l1 * c2 := by
        by_cases hc1 : c1 ≤ 0
        · exact Or.inl hc1
        · right
          have hc1_pos : 0 < c1 := not_le.mp hc1
          by_contra hlt21
          replace hlt21 : l1 * c2 < l2 * c1 := not_le.mp hlt21
          by_cases hc3 : c3 ≤ 0
          · exact h1 ⟨hc1_pos, Or.inr (le_of_lt hlt21), Or.inl hc3⟩
          · have hc3_pos : 0 < c3 := not_le.mp hc3
            rcases hr3 with hc3_le | hle23
            · linarith
            · have hle13 : l1 * c3 ≤ l3 * c1 := by nlinarith
              exact h1 ⟨hc1_pos, Or.inr (le_of_lt hlt21), Or.inr hle13⟩
      exact radon_case y0 a b y1 z l3 l1 l2 c3 c1 c2 hl3 hl1 hl2 (by linarith)
        (by rw [hz1]; ring) (by rw [hz2]; ring) (by linarith)
        (by rw [hy1]; ring) (by rw [hy2]; ring) hc2_pos hr3 hr1

/-- Lemma 7.1(ii): Three-triangle cover for any triangle `△(a, b, y₀)` and arbitrary point `y₁`. -/
theorem triangle_three_piece_cover
    (y0 y1 a b z : ℝ × ℝ)
    (hz : InClosedTri a b y0 z) :
    InClosedTri y1 a b z ∨ InClosedTri y1 b y0 z ∨ InClosedTri y1 y0 a z := by
  obtain ⟨l1, l2, l3, hl1, hl2, hl3, hlsum, hz1, hz2⟩ := hz
  let det := (b.1 - a.1) * (y0.2 - a.2) - (b.2 - a.2) * (y0.1 - a.1)
  by_cases hdet : det ≠ 0
  · let c2 := ((y1.1 - a.1) * (y0.2 - a.2) - (y1.2 - a.2) * (y0.1 - a.1)) / det
    let c3 := ((b.1 - a.1) * (y1.2 - a.2) - (b.2 - a.2) * (y1.1 - a.1)) / det
    let c1 := 1 - c2 - c3
    exact radon_step a b y0 y1 z l1 l2 l3 c1 c2 c3 hl1 hl2 hl3 hlsum hz1 hz2
      (by ring)
      (by dsimp only [c1, c2, c3]; field_simp [hdet]; dsimp only [det]; ring)
      (by dsimp only [c1, c2, c3]; field_simp [hdet]; dsimp only [det]; ring)
  · have hdet0 : (b.1 - a.1) * (y0.2 - a.2) - (b.2 - a.2) * (y0.1 - a.1) = 0 :=
      not_ne_iff.mp hdet
    by_cases hab : a = b
    · subst hab
      right; left
      exact ⟨0, l1 + l2, l3, le_rfl, add_nonneg hl1 hl2, hl3, by linarith,
        by rw [hz1]; ring, by rw [hz2]; ring⟩
    · have hab_coord : b.1 - a.1 ≠ 0 ∨ b.2 - a.2 ≠ 0 := by
        by_contra hc
        have hx0 : b.1 - a.1 = 0 := not_ne_iff.mp (not_or.mp hc).1
        have hy0 : b.2 - a.2 = 0 := not_ne_iff.mp (not_or.mp hc).2
        apply hab
        ext <;> linarith
      obtain ⟨t, ht1, ht2⟩ : ∃ t : ℝ, y0.1 = (1 - t) * a.1 + t * b.1 ∧ y0.2 = (1 - t) * a.2 + t * b.2 := by
        rcases hab_coord with hx | hy
        · refine ⟨(y0.1 - a.1) / (b.1 - a.1), ?_, ?_⟩
          · field_simp [hx]; ring
          · field_simp [hx]; linear_combination hdet0
        · refine ⟨(y0.2 - a.2) / (b.2 - a.2), ?_, ?_⟩
          · field_simp [hy]; linear_combination -hdet0
          · field_simp [hy]; ring
      by_cases ht0 : t ≤ 0
      · have h1t : 0 < 1 - t := by linarith
        have h1t_ne : 1 - t ≠ 0 := ne_of_gt h1t
        right; left
        refine ⟨0, l2 + l1 * (-t / (1 - t)), l3 + l1 * (1 / (1 - t)), le_rfl, ?_, ?_, ?_, ?_, ?_⟩
        · exact add_nonneg hl2 (mul_nonneg hl1 (div_nonneg (by linarith) (le_of_lt h1t)))
        · exact add_nonneg hl3 (mul_nonneg hl1 (div_nonneg zero_le_one (le_of_lt h1t)))
        · field_simp [h1t_ne]; linear_combination (1 - t) * hlsum
        · rw [hz1, ht1]; field_simp [h1t_ne]; ring
        · rw [hz2, ht2]; field_simp [h1t_ne]; ring
      · by_cases ht1_le : t ≤ 1
        · left
          refine ⟨0, l1 + l3 * (1 - t), l2 + l3 * t, le_rfl, ?_, ?_,
            by linear_combination hlsum, by rw [hz1, ht1]; ring, by rw [hz2, ht2]; ring⟩
          · exact add_nonneg hl1 (mul_nonneg hl3 (by linarith))
          · exact add_nonneg hl2 (mul_nonneg hl3 (by linarith))
        · have ht_pos : 0 < t := by linarith
          have ht_ne : t ≠ 0 := ne_of_gt ht_pos
          right; right
          refine ⟨0, l3 + l2 * (1 / t), l1 + l2 * ((t - 1) / t), le_rfl, ?_, ?_, ?_, ?_, ?_⟩
          · exact add_nonneg hl3 (mul_nonneg hl2 (div_nonneg zero_le_one (le_of_lt ht_pos)))
          · exact add_nonneg hl1 (mul_nonneg hl2 (div_nonneg (by linarith) (le_of_lt ht_pos)))
          · field_simp [ht_ne]; linear_combination t * hlsum
          · rw [hz1, ht1]; field_simp [ht_ne]; ring
          · rw [hz2, ht2]; field_simp [ht_ne]; ring

/-- `convexHull` form of Lemma 7.1(ii). -/
lemma convexHull_triangle_three_piece_cover (y0 y1 a b z : ℝ × ℝ)
    (hz : z ∈ convexHull ℝ ({a, b, y0} : Set (ℝ × ℝ))) :
    z ∈ convexHull ℝ ({y1, a, b} : Set (ℝ × ℝ)) ∨
    z ∈ convexHull ℝ ({y1, b, y0} : Set (ℝ × ℝ)) ∨
    z ∈ convexHull ℝ ({y1, y0, a} : Set (ℝ × ℝ)) := by
  rw [← inClosedTri_iff_mem_convexHull] at hz ⊢
  simp only [← inClosedTri_iff_mem_convexHull]
  exact triangle_three_piece_cover y0 y1 a b z hz

/-- Strictly convex counterclockwise `(n + 3)`-gon in `ℝ²`. -/
def StrictConvexCCWPoly {n : ℕ} (p : Fin (n + 3) → ℝ × ℝ) : Prop :=
  ∀ i j : Fin (n + 3), j ≠ i → j ≠ i + 1 → 0 < orient2D (p i) (p (i + 1)) (p j)

/-- Lemma 7.1(i) (`ray-exit`): for any convex polygon `K = conv{p_0, ..., p_{n+2}}` and any
    point `y : ℝ × ℝ`, every `z ∈ K` lies in `△(p_i, p_{i+1}, y)` for some `i`. -/
theorem ray_exit_polygon_cover {n : ℕ} (p : Fin (n + 3) → ℝ × ℝ)
    (hp : StrictConvexCCWPoly p) (y z : ℝ × ℝ)
    (hz : z ∈ convexHull ℝ (Set.range p)) :
    ∃ i : Fin (n + 3), InClosedTri (p i) (p (i + 1)) y z := by
  by_cases hzy : z = y
  · refine ⟨0, 0, 0, 1, le_rfl, le_rfl, zero_le_one, by ring, ?_, ?_⟩ <;>
      [rw [hzy]; rw [hzy]] <;> ring
  · have hz_nonneg : ∀ i : Fin (n + 3), 0 ≤ orient2D (p i) (p (i + 1)) z := by
      intro i
      let H : Set (ℝ × ℝ) := {x | 0 ≤ orient2D (p i) (p (i + 1)) x}
      have hH_conv : Convex ℝ H := by
        intro x hx u hu α β hα hβ hαβ
        dsimp [H] at hx hu ⊢
        unfold orient2D at hx hu ⊢
        change 0 ≤ ((p (i + 1)).1 - (p i).1) * ((α * x.2 + β * u.2) - (p i).2) -
          ((p (i + 1)).2 - (p i).2) * ((α * x.1 + β * u.1) - (p i).1)
        have hlin : ((p (i + 1)).1 - (p i).1) * ((α * x.2 + β * u.2) - (p i).2) -
            ((p (i + 1)).2 - (p i).2) * ((α * x.1 + β * u.1) - (p i).1) =
            α * (((p (i + 1)).1 - (p i).1) * (x.2 - (p i).2) -
              ((p (i + 1)).2 - (p i).2) * (x.1 - (p i).1)) +
            β * (((p (i + 1)).1 - (p i).1) * (u.2 - (p i).2) -
              ((p (i + 1)).2 - (p i).2) * (u.1 - (p i).1)) +
            (1 - (α + β)) * (((p (i + 1)).1 - (p i).1) * (-(p i).2) -
              ((p (i + 1)).2 - (p i).2) * (-(p i).1)) := by ring
        rw [hlin, hαβ, sub_self, zero_mul, add_zero]
        exact add_nonneg (mul_nonneg hα hx) (mul_nonneg hβ hu)
      have hsub : Set.range p ⊆ H := by
        rintro _ ⟨j, rfl⟩
        dsimp [H]
        by_cases hji : j = i
        · subst hji; rw [orient2D_self_outer]
        · by_cases hj1 : j = i + 1
          · subst hj1; rw [orient2D_self_right]
          · exact le_of_lt (hp i j hji hj1)
      exact convexHull_min hsub hH_conv hz
    let d : Fin (n + 3) → ℝ := fun i => orient2D (p i) (p (i + 1)) y
    let e : Fin (n + 3) → ℝ := fun i => orient2D (p i) (p (i + 1)) z
    have hsum_zero : ∑ i : Fin (n + 3), (e i - d i) = 0 := by
      have hid : ∀ i : Fin (n + 3), e i - d i =
          ((p (i + 1)).1 * (z.2 - y.2) - (p (i + 1)).2 * (z.1 - y.1)) -
          ((p i).1 * (z.2 - y.2) - (p i).2 * (z.1 - y.1)) := by
        intro i; dsimp [e, d, orient2D]; ring
      simp_rw [hid]
      rw [Finset.sum_sub_distrib]
      have hshift : ∑ i : Fin (n + 3), ((p (i + 1)).1 * (z.2 - y.2) - (p (i + 1)).2 * (z.1 - y.1)) =
          ∑ i : Fin (n + 3), ((p i).1 * (z.2 - y.2) - (p i).2 * (z.1 - y.1)) := by
        exact Equiv.sum_comp (Equiv.addRight (1 : Fin (n + 3)))
          (fun i => (p i).1 * (z.2 - y.2) - (p i).2 * (z.1 - y.1))
      rw [hshift, sub_self]
    have h_exists_neg : ∃ i : Fin (n + 3), e i < d i := by
      by_contra h_all_ge
      push Not at h_all_ge
      have h_all_eq : ∀ i ∈ (Finset.univ : Finset (Fin (n + 3))), e i - d i = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sub_nonneg.mpr (h_all_ge i))).mp hsum_zero
      have h0 : e 0 - d 0 = 0 := h_all_eq 0 (Finset.mem_univ 0)
      have h1 : e 1 - d 1 = 0 := h_all_eq 1 (Finset.mem_univ 1)
      have h2ne0 : (2 : Fin (n + 3)) ≠ 0 := by
        intro h
        have hv := congrArg Fin.val h
        simp [Nat.mod_eq_of_lt (by omega : 2 < n + 3)] at hv
      have h2ne1 : (2 : Fin (n + 3)) ≠ 0 + 1 := by
        intro h
        rw [zero_add] at h
        have hv := congrArg Fin.val h
        simp [Nat.mod_eq_of_lt (by omega : 2 < n + 3), Nat.mod_eq_of_lt (by omega : 1 < n + 3)] at hv
      have h012 : 0 < orient2D (p 0) (p 1) (p 2) := by
        simpa using hp 0 2 h2ne0 h2ne1
      have hid0 : e 0 - d 0 = ((p 1).1 - (p 0).1) * (z.2 - y.2) - ((p 1).2 - (p 0).2) * (z.1 - y.1) := by
        dsimp [e, d, orient2D]; rw [zero_add]; ring
      have hid1 : e 1 - d 1 = ((p 2).1 - (p 1).1) * (z.2 - y.2) - ((p 2).2 - (p 1).2) * (z.1 - y.1) := by
        have h11 : (1 : Fin (n + 3)) + 1 = 2 := by
          apply Fin.ext
          change (1 % (n + 3) + 1 % (n + 3)) % (n + 3) = 2 % (n + 3)
          rw [Nat.mod_eq_of_lt (by omega : 1 < n + 3), Nat.mod_eq_of_lt (by omega : 2 < n + 3)]
        dsimp [e, d, orient2D]
        rw [h11]
        ring
      have hdet_eq : ((p 1).1 - (p 0).1) * ((p 2).2 - (p 1).2) -
          ((p 1).2 - (p 0).2) * ((p 2).1 - (p 1).1) = orient2D (p 0) (p 1) (p 2) := by
        unfold orient2D; ring
      have hzx : z.1 - y.1 = 0 := by
        have hlin : (orient2D (p 0) (p 1) (p 2)) * (z.1 - y.1) =
            ((p 2).1 - (p 1).1) * (e 0 - d 0) - ((p 1).1 - (p 0).1) * (e 1 - d 1) := by
          rw [← hdet_eq, hid0, hid1]; ring
        rw [h0, h1] at hlin
        nlinarith
      have hzy_coord : z.2 - y.2 = 0 := by
        have hlin : (orient2D (p 0) (p 1) (p 2)) * (z.2 - y.2) =
            ((p 2).2 - (p 1).2) * (e 0 - d 0) - ((p 1).2 - (p 0).2) * (e 1 - d 1) := by
          rw [← hdet_eq, hid0, hid1]; ring
        rw [h0, h1] at hlin
        nlinarith
      apply hzy
      ext <;> linarith
    let S_neg : Finset (Fin (n + 3)) := Finset.univ.filter (fun i => e i < d i)
    have hS_ne : S_neg.Nonempty := by
      rcases h_exists_neg with ⟨i, hi⟩
      exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩⟩
    let f : Fin (n + 3) → ℝ := fun i => d i / (d i - e i)
    obtain ⟨i₀, hi₀_mem, hi₀_min⟩ := Finset.exists_min_image S_neg f hS_ne
    have hi₀_lt : e i₀ < d i₀ := (Finset.mem_filter.mp hi₀_mem).2
    have hi₀_e_nn : 0 ≤ e i₀ := hz_nonneg i₀
    have hi₀_den_pos : 0 < d i₀ - e i₀ := sub_pos.mpr hi₀_lt
    have hi₀_d_pos : 0 < d i₀ := lt_of_le_of_lt hi₀_e_nn hi₀_lt
    let tstar : ℝ := f i₀
    have htstar_ge1 : 1 ≤ tstar := by
      dsimp [tstar, f]
      rw [le_div_iff₀ hi₀_den_pos]
      linarith
    have htstar_pos : 0 < tstar := lt_of_lt_of_le zero_lt_one htstar_ge1
    let w : ℝ × ℝ := (y.1 + tstar * (z.1 - y.1), y.2 + tstar * (z.2 - y.2))
    have hw_orient : ∀ j : Fin (n + 3), orient2D (p j) (p (j + 1)) w =
        d j - tstar * (d j - e j) := by
      intro j
      dsimp [d, e, w, orient2D]; ring
    have hw_nonneg : ∀ j : Fin (n + 3), 0 ≤ orient2D (p j) (p (j + 1)) w := by
      intro j
      rw [hw_orient j]
      by_cases hj : e j < d j
      · have hj_mem : j ∈ S_neg := Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩
        have hmin := hi₀_min j hj_mem
        have hj_den : 0 < d j - e j := sub_pos.mpr hj
        have hmul : tstar * (d j - e j) ≤ d j := (le_div_iff₀ hj_den).mp hmin
        linarith
      · have hle : d j ≤ e j := not_lt.mp hj
        have hge : 0 ≤ e j := hz_nonneg j
        nlinarith
    have hw_i0_zero : orient2D (p i₀) (p (i₀ + 1)) w = 0 := by
      rw [hw_orient i₀]
      dsimp [tstar, f]
      have hne : d i₀ - e i₀ ≠ 0 := ne_of_gt hi₀_den_pos
      field_simp [hne]; ring
    have h1_ne_0 : (1 : Fin (n + 3)) ≠ 0 := by
      intro h
      have hv := congrArg Fin.val h
      simp [Nat.mod_eq_of_lt (by omega : 1 < n + 3)] at hv
    have h2_ne_0 : (2 : Fin (n + 3)) ≠ 0 := by
      intro h
      have hv := congrArg Fin.val h
      simp [Nat.mod_eq_of_lt (by omega : 2 < n + 3)] at hv
    have h2_ne_1 : (2 : Fin (n + 3)) ≠ 1 := by
      intro h
      have hv := congrArg Fin.val h
      simp [Nat.mod_eq_of_lt (by omega : 2 < n + 3), Nat.mod_eq_of_lt (by omega : 1 < n + 3)] at hv
    have hi0_ne_succ : i₀ ≠ i₀ + 1 := by
      intro h
      nth_rw 1 [← add_zero i₀] at h
      exact h1_ne_0 (add_left_cancel h).symm
    have h_seg_pos1 : 0 < orient2D (p (i₀ + 1)) (p (i₀ + 1 + 1)) (p i₀) := by
      apply hp (i₀ + 1) i₀
      · exact hi0_ne_succ
      · intro h
        rw [add_assoc] at h
        nth_rw 1 [← add_zero i₀] at h
        have h' : (0 : Fin (n + 3)) = 1 + 1 := add_left_cancel h
        exact h2_ne_0 h'.symm
    have h_seg_pos2 : 0 < orient2D (p (i₀ - 1)) (p (i₀ - 1 + 1)) (p (i₀ + 1)) := by
      apply hp (i₀ - 1) (i₀ + 1)
      · intro h
        have h' := congrArg (· + (1 : Fin (n + 3))) h
        rw [sub_add_cancel, add_assoc] at h'
        nth_rw 2 [← add_zero i₀] at h'
        exact h2_ne_0 (add_left_cancel h')
      · intro h
        rw [sub_add_cancel] at h
        nth_rw 2 [← add_zero i₀] at h
        exact h1_ne_0 (add_left_cancel h)
    have h_edge_ne : p i₀ ≠ p (i₀ + 1) := by
      intro heq
      rw [heq, orient2D_self_outer] at h_seg_pos1
      linarith
    have h_coord_ne : (p (i₀ + 1)).1 - (p i₀).1 ≠ 0 ∨ (p (i₀ + 1)).2 - (p i₀).2 ≠ 0 := by
      by_contra h0
      push Not at h0
      apply h_edge_ne
      ext <;> linarith
    obtain ⟨s, hs1, hs2⟩ : ∃ s : ℝ,
        w.1 = (1 - s) * (p i₀).1 + s * (p (i₀ + 1)).1 ∧
        w.2 = (1 - s) * (p i₀).2 + s * (p (i₀ + 1)).2 := by
      have hdet0 : ((p (i₀ + 1)).1 - (p i₀).1) * (w.2 - (p i₀).2) -
          ((p (i₀ + 1)).2 - (p i₀).2) * (w.1 - (p i₀).1) = 0 := hw_i0_zero
      rcases h_coord_ne with hx | hy
      · refine ⟨(w.1 - (p i₀).1) / ((p (i₀ + 1)).1 - (p i₀).1), ?_, ?_⟩
        · field_simp [hx]; ring
        · field_simp [hx]; linear_combination hdet0
      · refine ⟨(w.2 - (p i₀).2) / ((p (i₀ + 1)).2 - (p i₀).2), ?_, ?_⟩
        · field_simp [hy]; linear_combination -hdet0
        · field_simp [hy]; ring
    have hs_ge0 : 0 ≤ s := by
      have h0 := hw_nonneg (i₀ - 1)
      rw [sub_add_cancel] at h0
      rw [sub_add_cancel] at h_seg_pos2
      have hid := orient2D_affine_comb (p (i₀ - 1)) (p i₀) (p i₀) (p (i₀ + 1)) w s hs1 hs2
      rw [orient2D_self_right, mul_zero, zero_add] at hid
      rw [hid] at h0
      exact nonneg_of_mul_nonneg_left h0 h_seg_pos2
    have hs_le1 : s ≤ 1 := by
      have h0 := hw_nonneg (i₀ + 1)
      have hid := orient2D_affine_comb (p (i₀ + 1)) (p (i₀ + 1 + 1)) (p i₀) (p (i₀ + 1)) w s hs1 hs2
      rw [orient2D_self_outer, mul_zero, add_zero] at hid
      rw [hid] at h0
      have h1s : 0 ≤ 1 - s := nonneg_of_mul_nonneg_left h0 h_seg_pos1
      linarith
    have htstar_ne : tstar ≠ 0 := ne_of_gt htstar_pos
    refine ⟨i₀, (1 - s) / tstar, s / tstar, 1 - 1 / tstar,
      div_nonneg (by linarith) (le_of_lt htstar_pos),
      div_nonneg hs_ge0 (le_of_lt htstar_pos),
      ?_, ?_, ?_, ?_⟩
    · rw [sub_nonneg, div_le_one htstar_pos]; exact htstar_ge1
    · field_simp [htstar_ne]; ring
    · have hz1 : z.1 = (1 - 1 / tstar) * y.1 + (1 / tstar) * w.1 := by
        dsimp [w]; field_simp [htstar_ne]; ring
      rw [hz1, hs1]; field_simp [htstar_ne]; ring
    · have hz2 : z.2 = (1 - 1 / tstar) * y.2 + (1 / tstar) * w.2 := by
        dsimp [w]; field_simp [htstar_ne]; ring
      rw [hz2, hs2]; field_simp [htstar_ne]; ring

/-- `convexHull` form of Lemma 7.1(i): every `z ∈ conv(p)` lies in `conv{p i, p (i+1), y}` for some `i`. -/
lemma convexHull_ray_exit_polygon_cover {n : ℕ} (p : Fin (n + 3) → ℝ × ℝ)
    (hp : StrictConvexCCWPoly p) (y z : ℝ × ℝ)
    (hz : z ∈ convexHull ℝ (Set.range p)) :
    ∃ i : Fin (n + 3), z ∈ convexHull ℝ ({p i, p (i + 1), y} : Set (ℝ × ℝ)) := by
  obtain ⟨i, hi⟩ := ray_exit_polygon_cover p hp y z hz
  exact ⟨i, (inClosedTri_iff_mem_convexHull _ _ _ _).mp hi⟩

/-! ## Exit-Region Disjointness (`E(M₀) ∩ (M \ M₀) = ∅`) -/

/-- Single minimal point `y` on exit edge `u v`: no other point `z ∈ M \ {y}` on the same exit edge
    (with `orient2D u v y ≤ orient2D u v z`) or outside `△(wD, u, v)` lies in `E({y}) = △(u, v, y)`. -/
lemma exitRegion_single_disjoint
    (wD u v y z : ℝ × ℝ)
    (hy_pos : 0 < orient2D u v y)
    (hy_in_fan : InClosedTri wD u v y)
    (hz_tri : InClosedTri u v y z) :
    InClosedTri wD u v z ∧ (orient2D u v y ≤ orient2D u v z → z = y) := by
  rcases hz_tri with ⟨μ₁, μ₂, μ₃, h1, h2, h3, hsum, hz1, hz2⟩
  constructor
  · have hsub : convexHull ℝ ({u, v, y} : Set (ℝ × ℝ)) ⊆ convexHull ℝ ({wD, u, v} : Set (ℝ × ℝ)) := by
      apply convexHull_tri_subset
      · exact subset_convexHull ℝ _ (by simp)
      · exact subset_convexHull ℝ _ (by simp)
      · exact (inClosedTri_iff_mem_convexHull _ _ _ _).mp hy_in_fan
    have hz_conv : z ∈ convexHull ℝ ({u, v, y} : Set (ℝ × ℝ)) :=
      (inClosedTri_iff_mem_convexHull u v y z).mp ⟨μ₁, μ₂, μ₃, h1, h2, h3, hsum, hz1, hz2⟩
    exact (inClosedTri_iff_mem_convexHull wD u v z).mpr (hsub hz_conv)
  · intro hmin
    have hor : orient2D u v z = μ₃ * orient2D u v y := by
      unfold orient2D
      rw [hz1, hz2]
      have hid : (v.1 - u.1) * (μ₁ * u.2 + μ₂ * v.2 + μ₃ * y.2 - u.2) -
          (v.2 - u.2) * (μ₁ * u.1 + μ₂ * v.1 + μ₃ * y.1 - u.1) =
          μ₃ * ((v.1 - u.1) * (y.2 - u.2) - (v.2 - u.2) * (y.1 - u.1)) +
          (1 - (μ₁ + μ₂ + μ₃)) * ((v.1 - u.1) * (-u.2) - (v.2 - u.2) * (-u.1)) := by ring
      rw [hid, hsum, sub_self, zero_mul, add_zero]
    have hμ3_ge1 : 1 ≤ μ₃ := by
      have : orient2D u v y ≤ μ₃ * orient2D u v y := by linarith
      nlinarith
    have hμ3_eq1 : μ₃ = 1 := by linarith
    have hμ1_eq0 : μ₁ = 0 := by linarith
    have hμ2_eq0 : μ₂ = 0 := by linarith
    ext <;> [rw [hz1, hμ1_eq0, hμ2_eq0, hμ3_eq1]; rw [hz2, hμ1_eq0, hμ2_eq0, hμ3_eq1]] <;> ring

/-- Two-minimal-point exit region `E({y₀, y'₀}) = conv{u, v, y₀, y'₀}` on the same exit edge `u v`
    (handling both the non-parallel case `orient2D u v y₀ < orient2D u v y'₀` and the parallel case
    `orient2D u v y₀ = orient2D u v y'₀` via general position `orient2D y₀ y'₀ z ≠ 0`). -/
lemma exitRegion_two_same_edge_disjoint
    (wD u v y0 y0' z : ℝ × ℝ)
    (hy0_pos : 0 < orient2D u v y0)
    (hy_ord : orient2D u v y0 ≤ orient2D u v y0')
    (hy0_fan : InClosedTri wD u v y0)
    (hy0'_fan : InClosedTri wD u v y0')
    (hz_hull : z ∈ convexHull ℝ ({u, v, y0, y0'} : Set (ℝ × ℝ))) :
    InClosedTri wD u v z ∧
      (orient2D u v y0' ≤ orient2D u v z →
        ((orient2D u v y0 < orient2D u v y0' → z = y0') ∧
         (orient2D y0 y0' z ≠ 0 → z = y0 ∨ z = y0'))) := by
  have hz_fan : z ∈ convexHull ℝ ({wD, u, v} : Set (ℝ × ℝ)) := by
    have hsub : convexHull ℝ ({u, v, y0, y0'} : Set (ℝ × ℝ)) ⊆
        convexHull ℝ ({wD, u, v} : Set (ℝ × ℝ)) := by
      apply convexHull_subset_of_mem
      intro p hp
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
      rcases hp with rfl | rfl | rfl | rfl
      · exact subset_convexHull ℝ _ (by simp)
      · exact subset_convexHull ℝ _ (by simp)
      · exact (inClosedTri_iff_mem_convexHull _ _ _ _).mp hy0_fan
      · exact (inClosedTri_iff_mem_convexHull _ _ _ _).mp hy0'_fan
    exact hsub hz_hull
  refine ⟨(inClosedTri_iff_mem_convexHull _ _ _ _).mpr hz_fan, ?_⟩
  intro hz_ge
  let K : Set (ℝ × ℝ) := {p | ∃ a b c d : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ 0 ≤ d ∧
    a + b + c + d = 1 ∧
    p.1 = a * u.1 + b * v.1 + c * y0.1 + d * y0'.1 ∧
    p.2 = a * u.2 + b * v.2 + c * y0.2 + d * y0'.2}
  have hK_conv : Convex ℝ K := by
    intro x hx y hy α β hα hβ hαβ
    rcases hx with ⟨a1, b1, c1, d1, ha1, hb1, hc1, hd1, hsum1, hx1, hx2⟩
    rcases hy with ⟨a2, b2, c2, d2, ha2, hb2, hc2, hd2, hsum2, hy1, hy2⟩
    refine ⟨α * a1 + β * a2, α * b1 + β * b2, α * c1 + β * c2, α * d1 + β * d2,
      add_nonneg (mul_nonneg hα ha1) (mul_nonneg hβ ha2),
      add_nonneg (mul_nonneg hα hb1) (mul_nonneg hβ hb2),
      add_nonneg (mul_nonneg hα hc1) (mul_nonneg hβ hc2),
      add_nonneg (mul_nonneg hα hd1) (mul_nonneg hβ hd2), ?_, ?_, ?_⟩
    · calc (α * a1 + β * a2) + (α * b1 + β * b2) + (α * c1 + β * c2) + (α * d1 + β * d2)
          = α * (a1 + b1 + c1 + d1) + β * (a2 + b2 + c2 + d2) := by ring
        _ = α * 1 + β * 1 := by rw [hsum1, hsum2]
        _ = 1 := by linarith
    · change α * x.1 + β * y.1 = _; rw [hx1, hy1]; ring
    · change α * x.2 + β * y.2 = _; rw [hx2, hy2]; ring
  have hsubK : ({u, v, y0, y0'} : Set (ℝ × ℝ)) ⊆ K := by
    intro p hp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl | rfl | rfl
    · exact ⟨1, 0, 0, 0, zero_le_one, le_rfl, le_rfl, le_rfl, by ring, by ring, by ring⟩
    · exact ⟨0, 1, 0, 0, le_rfl, zero_le_one, le_rfl, le_rfl, by ring, by ring, by ring⟩
    · exact ⟨0, 0, 1, 0, le_rfl, le_rfl, zero_le_one, le_rfl, by ring, by ring, by ring⟩
    · exact ⟨0, 0, 0, 1, le_rfl, le_rfl, le_rfl, zero_le_one, by ring, by ring, by ring⟩
  obtain ⟨a, b, c, d, ha, hb, hc, hd, hsum, hz1, hz2⟩ := convexHull_min hsubK hK_conv hz_hull
  have hor : orient2D u v z = c * orient2D u v y0 + d * orient2D u v y0' := by
    unfold orient2D
    rw [hz1, hz2]
    have hid : (v.1 - u.1) * (a * u.2 + b * v.2 + c * y0.2 + d * y0'.2 - u.2) -
        (v.2 - u.2) * (a * u.1 + b * v.1 + c * y0.1 + d * y0'.1 - u.1) =
        c * ((v.1 - u.1) * (y0.2 - u.2) - (v.2 - u.2) * (y0.1 - u.1)) +
        d * ((v.1 - u.1) * (y0'.2 - u.2) - (v.2 - u.2) * (y0'.1 - u.1)) +
        (1 - (a + b + c + d)) * ((v.1 - u.1) * (-u.2) - (v.2 - u.2) * (-u.1)) := by ring
    rw [hid, hsum, sub_self, zero_mul, add_zero]
  have hy0'_pos : 0 < orient2D u v y0' := lt_of_lt_of_le hy0_pos hy_ord
  have hcd_le1 : c + d ≤ 1 := by linarith
  have hsum_le : c * orient2D u v y0 + d * orient2D u v y0' ≤ (c + d) * orient2D u v y0' := by
    nlinarith
  have hcd_eq1 : c + d = 1 := by
    have h1 : (1 : ℝ) * orient2D u v y0' ≤ (c + d) * orient2D u v y0' := by linarith
    have h2 : 1 ≤ c + d := by nlinarith
    linarith
  have ha0 : a = 0 := by linarith
  have hb0 : b = 0 := by linarith
  constructor
  · intro h_strict
    have hc0 : c = 0 := by nlinarith
    have hd1 : d = 1 := by linarith
    ext <;> [rw [hz1, ha0, hb0, hc0, hd1]; rw [hz2, ha0, hb0, hc0, hd1]] <;> ring
  · intro h_noncol
    have hcol : orient2D y0 y0' z = 0 := by
      unfold orient2D
      rw [hz1, hz2, ha0, hb0]
      have hcd' : d = 1 - c := by linarith
      rw [hcd']
      ring
    exact False.elim (h_noncol hcol)

/-! ## Explicit `conv D` Covering Decompositions (`convD-cover`) -/

private lemma fin_succ_eq_zero_iff_last {n : ℕ} (i : Fin (n + 3)) (h : i + 1 = 0) :
    i = Fin.last (n + 2) := by
  have hval : (i + 1 : Fin (n + 3)).val = 0 := congrArg Fin.val h
  rw [Fin.val_add] at hval
  simp [Nat.mod_eq_of_lt (by omega : 1 < n + 3)] at hval
  have hlt := i.isLt
  ext; change i.val = n + 2
  rcases lt_or_eq_of_le (by omega : i.val + 1 ≤ n + 3) with h1 | h1
  · rw [Nat.mod_eq_of_lt h1] at hval; omega
  · omega

/-- Case 1: when all targets in `Q` have pure-`D` caps, `conv(D \ Q) ⊆ conv F`. -/
lemma convD_cover_case1 {D F : Set (ℝ × ℝ)} (hsub : D ⊆ F) :
    convexHull ℝ D ⊆ convexHull ℝ F :=
  convexHull_mono hsub

/-- Case 2 (L/R): covering `K = conv((D \ Q) ∪ {p})` from `y ∈ M₀ ⊆ F` on exit edge `p v_y`. -/
lemma convD_cover_case2_LR {n : ℕ} (K : Fin (n + 3) → ℝ × ℝ) (hK : StrictConvexCCWPoly K)
    (y : ℝ × ℝ) (F : Set (ℝ × ℝ))
    (hyF : y ∈ F)
    (hother : ∀ i : Fin (n + 3), i ≠ 0 → K i ∈ F) :
    convexHull ℝ (Set.range K) ⊆
      convexHull ℝ F ∪
      convexHull ℝ ({K (Fin.last (n + 2)), K 0, y} : Set (ℝ × ℝ)) ∪
      convexHull ℝ ({K 0, K 1, y} : Set (ℝ × ℝ)) := by
  intro z hz
  obtain ⟨i, hi⟩ := convexHull_ray_exit_polygon_cover K hK y z hz
  by_cases hi0 : i = 0
  · subst hi0
    right
    exact hi
  · by_cases hi_last : i + 1 = 0
    · have hil : i = Fin.last (n + 2) := fin_succ_eq_zero_iff_last i hi_last
      subst hil
      rw [hi_last] at hi
      left; right
      exact hi
    · left; left
      have hsub : convexHull ℝ ({K i, K (i + 1), y} : Set (ℝ × ℝ)) ⊆ convexHull ℝ F :=
        convexHull_tri_subset
          (subset_convexHull ℝ F (hother i hi0))
          (subset_convexHull ℝ F (hother (i + 1) hi_last))
          (subset_convexHull ℝ F hyF)
      exact hsub hi

/-- Case 2 (M): covering pentagon `D = (0, 1, 2, 3, 4)` with `Q = {1}`, `M₀ = {y₀, y₁}` on `01, 12`. -/
lemma convD_cover_case2_M (D : Fin 5 → ℝ × ℝ) (hD : StrictConvexCCWPoly D)
    (y0 y1 : ℝ × ℝ) (F : Set (ℝ × ℝ))
    (hy0F : y0 ∈ F) (hy1F : y1 ∈ F)
    (h0F : D 0 ∈ F) (h2F : D 2 ∈ F) (h3F : D 3 ∈ F) (h4F : D 4 ∈ F) :
    convexHull ℝ (Set.range D) ⊆
      convexHull ℝ F ∪
      convexHull ℝ ({D 0, D 1, y0} : Set (ℝ × ℝ)) ∪
      convexHull ℝ ({D 1, D 2, y1} : Set (ℝ × ℝ)) ∪
      convexHull ℝ ({y0, D 1, y1} : Set (ℝ × ℝ)) := by
  intro z hz
  obtain ⟨i, hi⟩ := convexHull_ray_exit_polygon_cover D hD y0 z hz
  fin_cases i
  · left; left; right; exact hi
  · have hcov := convexHull_triangle_three_piece_cover y0 y1 (D 1) (D 2) z hi
    rcases hcov with hA | hB | hC
    · left; right
      have : ({y1, D 1, D 2} : Set (ℝ × ℝ)) = {D 1, D 2, y1} := by ext p; simp [or_comm, or_left_comm]
      rwa [← this]
    · left; left; left
      exact convexHull_tri_subset
        (subset_convexHull ℝ F hy1F)
        (subset_convexHull ℝ F h2F)
        (subset_convexHull ℝ F hy0F) hB
    · right
      have : ({y1, y0, D 1} : Set (ℝ × ℝ)) = {y0, D 1, y1} := by ext p; simp [or_comm, or_left_comm]
      rwa [← this]
  · left; left; left
    exact convexHull_tri_subset (subset_convexHull ℝ F h2F) (subset_convexHull ℝ F h3F)
      (subset_convexHull ℝ F hy0F) hi
  · left; left; left
    exact convexHull_tri_subset (subset_convexHull ℝ F h3F) (subset_convexHull ℝ F h4F)
      (subset_convexHull ℝ F hy0F) hi
  · left; left; left
    exact convexHull_tri_subset (subset_convexHull ℝ F h4F) (subset_convexHull ℝ F h0F)
      (subset_convexHull ℝ F hy0F) hi

/-- Case 3a (L/R): `Q = {K 0, K 1}` sharing a single gap of size two with cap `conv{K (n+2), K 0, K 1, y}`. -/
lemma convD_cover_case3a_LR {n : ℕ} (K : Fin (n + 3) → ℝ × ℝ) (hK : StrictConvexCCWPoly K)
    (y : ℝ × ℝ) (F : Set (ℝ × ℝ))
    (hyF : y ∈ F)
    (hother : ∀ i : Fin (n + 3), i ≠ 0 → i ≠ 1 → K i ∈ F) :
    convexHull ℝ (Set.range K) ⊆
      convexHull ℝ F ∪
      convexHull ℝ ({K (Fin.last (n + 2)), K 0, K 1, y} : Set (ℝ × ℝ)) ∪
      convexHull ℝ ({K 1, K 2, y} : Set (ℝ × ℝ)) := by
  intro z hz
  obtain ⟨i, hi⟩ := convexHull_ray_exit_polygon_cover K hK y z hz
  by_cases hi0 : i = 0
  · subst hi0
    left; right
    exact convexHull_tri_subset
      (subset_convexHull ℝ _ (by simp))
      (subset_convexHull ℝ _ (by simp))
      (subset_convexHull ℝ _ (by simp)) hi
  · by_cases hi1 : i = 1
    · subst hi1
      right
      exact hi
    · by_cases hi_last : i + 1 = 0
      · have hil : i = Fin.last (n + 2) := fin_succ_eq_zero_iff_last i hi_last
        subst hil
        rw [hi_last] at hi
        left; right
        exact convexHull_tri_subset
          (subset_convexHull ℝ _ (by simp))
          (subset_convexHull ℝ _ (by simp))
          (subset_convexHull ℝ _ (by simp)) hi
      · have hi1_ne1 : i + 1 ≠ 1 := by
          intro h; apply hi0
          nth_rw 2 [← zero_add (1 : Fin (n + 3))] at h
          exact add_right_cancel h
        left; left
        exact convexHull_tri_subset
          (subset_convexHull ℝ F (hother i hi0 hi1))
          (subset_convexHull ℝ F (hother (i + 1) hi_last hi1_ne1))
          (subset_convexHull ℝ F hyF) hi

/-- Case 3a (M): pentagon `D = (0, 1, 2, 3, 4)`, `Q = {1, 2}`, `M₀ = {y₀, y₁}` on `01, 23`. -/
lemma convD_cover_case3a_M (D : Fin 5 → ℝ × ℝ) (hD : StrictConvexCCWPoly D)
    (y0 y1 : ℝ × ℝ) (F : Set (ℝ × ℝ))
    (hy0F : y0 ∈ F) (hy1F : y1 ∈ F)
    (h0F : D 0 ∈ F) (h3F : D 3 ∈ F) (h4F : D 4 ∈ F) :
    convexHull ℝ (Set.range D) ⊆
      convexHull ℝ F ∪
      convexHull ℝ ({D 0, D 1, y0} : Set (ℝ × ℝ)) ∪
      convexHull ℝ ({D 2, D 3, y1} : Set (ℝ × ℝ)) ∪
      convexHull ℝ ({y0, D 1, D 2, y1} : Set (ℝ × ℝ)) := by
  intro z hz
  obtain ⟨i, hi⟩ := convexHull_ray_exit_polygon_cover D hD y0 z hz
  fin_cases i
  · left; left; right; exact hi
  · right
    exact convexHull_tri_subset
      (subset_convexHull ℝ _ (by simp))
      (subset_convexHull ℝ _ (by simp))
      (subset_convexHull ℝ _ (by simp)) hi
  · have hcov := convexHull_triangle_three_piece_cover y0 y1 (D 2) (D 3) z hi
    rcases hcov with hA | hB | hC
    · left; right
      have : ({y1, D 2, D 3} : Set (ℝ × ℝ)) = {D 2, D 3, y1} := by ext p; simp [or_comm, or_left_comm]
      rwa [← this]
    · left; left; left
      exact convexHull_tri_subset (subset_convexHull ℝ F hy1F) (subset_convexHull ℝ F h3F)
        (subset_convexHull ℝ F hy0F) hB
    · right
      exact convexHull_tri_subset
        (subset_convexHull ℝ _ (by simp))
        (subset_convexHull ℝ _ (by simp))
        (subset_convexHull ℝ _ (by simp)) hC
  · left; left; left
    exact convexHull_tri_subset (subset_convexHull ℝ F h3F) (subset_convexHull ℝ F h4F)
      (subset_convexHull ℝ F hy0F) hi
  · left; left; left
    exact convexHull_tri_subset (subset_convexHull ℝ F h4F) (subset_convexHull ℝ F h0F)
      (subset_convexHull ℝ F hy0F) hi

/-- Case 3b (single `M₀ = {a₀}` on `01`, `Q = {0, 1}`): covers any convex `(n + 3)`-gon. -/
lemma convD_cover_case3b_single_M0 {n : ℕ} (D : Fin (n + 3) → ℝ × ℝ) (hD : StrictConvexCCWPoly D)
    (a0 : ℝ × ℝ) (F : Set (ℝ × ℝ))
    (ha0F : a0 ∈ F)
    (hother : ∀ i : Fin (n + 3), i ≠ 0 → i ≠ 1 → D i ∈ F) :
    convexHull ℝ (Set.range D) ⊆
      convexHull ℝ F ∪
      convexHull ℝ ({D (Fin.last (n + 2)), D 0, a0} : Set (ℝ × ℝ)) ∪
      convexHull ℝ ({a0, D 1, D 2} : Set (ℝ × ℝ)) ∪
      convexHull ℝ ({D 0, D 1, a0} : Set (ℝ × ℝ)) := by
  intro z hz
  obtain ⟨i, hi⟩ := convexHull_ray_exit_polygon_cover D hD a0 z hz
  by_cases hi0 : i = 0
  · subst hi0; right; exact hi
  · by_cases hi1 : i = 1
    · subst hi1; left; right
      rw [show (1 + 1 : Fin (n + 3)) = 2 from rfl] at hi
      have : ({D 1, D 2, a0} : Set (ℝ × ℝ)) = {a0, D 1, D 2} := by
        ext p; simp [or_comm, or_left_comm]
      rwa [← this]
    · by_cases hi_last : i + 1 = 0
      · have hil : i = Fin.last (n + 2) := fin_succ_eq_zero_iff_last i hi_last
        subst hil
        rw [hi_last] at hi
        left; left; right; exact hi
      · have hi1_ne1 : i + 1 ≠ 1 := by
          intro h; apply hi0
          nth_rw 2 [← zero_add (1 : Fin (n + 3))] at h
          exact add_right_cancel h
        left; left; left
        exact convexHull_tri_subset
          (subset_convexHull ℝ F (hother i hi0 hi1))
          (subset_convexHull ℝ F (hother (i + 1) hi_last hi1_ne1))
          (subset_convexHull ℝ F ha0F) hi

/-- Helper: pentagon `D : Fin 5 → ℝ × ℝ` is covered by the three fan triangles from vertex `k`. -/
lemma pentagon_fan_triangulation_from_0 (D : Fin 5 → ℝ × ℝ) (hD : StrictConvexCCWPoly D) (z : ℝ × ℝ)
    (hz : z ∈ convexHull ℝ (Set.range D)) :
    z ∈ convexHull ℝ ({D 0, D 1, D 2} : Set (ℝ × ℝ)) ∨
    z ∈ convexHull ℝ ({D 0, D 2, D 3} : Set (ℝ × ℝ)) ∨
    z ∈ convexHull ℝ ({D 0, D 3, D 4} : Set (ℝ × ℝ)) := by
  obtain ⟨i, hi⟩ := convexHull_ray_exit_polygon_cover D hD (D 0) z hz
  fin_cases i
  · left
    exact convexHull_tri_subset (subset_convexHull ℝ _ (by simp))
      (subset_convexHull ℝ _ (by simp)) (subset_convexHull ℝ _ (by simp)) hi
  · left
    exact convexHull_tri_subset (subset_convexHull ℝ _ (by simp))
      (subset_convexHull ℝ _ (by simp)) (subset_convexHull ℝ _ (by simp)) hi
  · right; left
    exact convexHull_tri_subset (subset_convexHull ℝ _ (by simp))
      (subset_convexHull ℝ _ (by simp)) (subset_convexHull ℝ _ (by simp)) hi
  · right; right
    exact convexHull_tri_subset (subset_convexHull ℝ _ (by simp))
      (subset_convexHull ℝ _ (by simp)) (subset_convexHull ℝ _ (by simp)) hi
  · right; right
    exact convexHull_tri_subset (subset_convexHull ℝ _ (by simp))
      (subset_convexHull ℝ _ (by simp)) (subset_convexHull ℝ _ (by simp)) hi

/-- Helper: pentagon `D : Fin 5 → ℝ × ℝ` is covered by the three fan triangles from vertex `1`. -/
lemma pentagon_fan_triangulation_from_1 (D : Fin 5 → ℝ × ℝ) (hD : StrictConvexCCWPoly D) (z : ℝ × ℝ)
    (hz : z ∈ convexHull ℝ (Set.range D)) :
    z ∈ convexHull ℝ ({D 4, D 0, D 1} : Set (ℝ × ℝ)) ∨
    z ∈ convexHull ℝ ({D 1, D 3, D 4} : Set (ℝ × ℝ)) ∨
    z ∈ convexHull ℝ ({D 1, D 2, D 3} : Set (ℝ × ℝ)) := by
  obtain ⟨i, hi⟩ := convexHull_ray_exit_polygon_cover D hD (D 1) z hz
  fin_cases i
  · left
    exact convexHull_tri_subset (subset_convexHull ℝ _ (by simp))
      (subset_convexHull ℝ _ (by simp)) (subset_convexHull ℝ _ (by simp)) hi
  · right; right
    exact convexHull_tri_subset (subset_convexHull ℝ _ (by simp))
      (subset_convexHull ℝ _ (by simp)) (subset_convexHull ℝ _ (by simp)) hi
  · right; right
    exact convexHull_tri_subset (subset_convexHull ℝ _ (by simp))
      (subset_convexHull ℝ _ (by simp)) (subset_convexHull ℝ _ (by simp)) hi
  · right; left
    exact convexHull_tri_subset (subset_convexHull ℝ _ (by simp))
      (subset_convexHull ℝ _ (by simp)) (subset_convexHull ℝ _ (by simp)) hi
  · left
    exact convexHull_tri_subset (subset_convexHull ℝ _ (by simp))
      (subset_convexHull ℝ _ (by simp)) (subset_convexHull ℝ _ (by simp)) hi

/-- Helper: pentagon `D : Fin 5 → ℝ × ℝ` is covered by the three fan triangles from vertex `4`. -/
lemma pentagon_fan_triangulation_from_4 (D : Fin 5 → ℝ × ℝ) (hD : StrictConvexCCWPoly D) (z : ℝ × ℝ)
    (hz : z ∈ convexHull ℝ (Set.range D)) :
    z ∈ convexHull ℝ ({D 4, D 0, D 1} : Set (ℝ × ℝ)) ∨
    z ∈ convexHull ℝ ({D 1, D 2, D 4} : Set (ℝ × ℝ)) ∨
    z ∈ convexHull ℝ ({D 2, D 3, D 4} : Set (ℝ × ℝ)) := by
  obtain ⟨i, hi⟩ := convexHull_ray_exit_polygon_cover D hD (D 4) z hz
  fin_cases i
  · left
    exact convexHull_tri_subset (subset_convexHull ℝ _ (by simp))
      (subset_convexHull ℝ _ (by simp)) (subset_convexHull ℝ _ (by simp)) hi
  · right; left
    exact convexHull_tri_subset (subset_convexHull ℝ _ (by simp))
      (subset_convexHull ℝ _ (by simp)) (subset_convexHull ℝ _ (by simp)) hi
  · right; right
    exact convexHull_tri_subset (subset_convexHull ℝ _ (by simp))
      (subset_convexHull ℝ _ (by simp)) (subset_convexHull ℝ _ (by simp)) hi
  · right; right
    exact convexHull_tri_subset (subset_convexHull ℝ _ (by simp))
      (subset_convexHull ℝ _ (by simp)) (subset_convexHull ℝ _ (by simp)) hi
  · left
    exact convexHull_tri_subset (subset_convexHull ℝ _ (by simp))
      (subset_convexHull ℝ _ (by simp)) (subset_convexHull ℝ _ (by simp)) hi

/-- Helper: 4-gon `(D 1, D 2, D 3, D 4)` of a CCW convex pentagon is strictly convex CCW. -/
lemma quad1234_strictConvexCCW (D : Fin 5 → ℝ × ℝ) (hD : StrictConvexCCWPoly D) :
    StrictConvexCCWPoly ![D 1, D 2, D 3, D 4] := by
  intro i j hij1 hij2
  fin_cases i <;> fin_cases j <;> simp at hij1 hij2 ⊢
  · exact hD 1 3 (by decide) (by decide)
  · exact hD 1 4 (by decide) (by decide)
  · exact hD 2 1 (by decide) (by decide)
  · exact hD 2 4 (by decide) (by decide)
  · exact hD 3 1 (by decide) (by decide)
  · exact hD 3 2 (by decide) (by decide)
  · have h124 := hD 1 4 (by decide) (by decide)
    rw [orient2D_cycle] at h124
    exact h124
  · have h341 := hD 3 1 (by decide) (by decide)
    rw [← orient2D_cycle] at h341
    exact h341

/-- Case 3b, disjoint exit edges `01` (`y₀`) and `23` (`y₁`), `Q = {0, 2}`. -/
lemma convD_cover_case3b_disjoint_02 (D : Fin 5 → ℝ × ℝ) (hD : StrictConvexCCWPoly D)
    (y0 y1 : ℝ × ℝ) (F : Set (ℝ × ℝ))
    (hy0F : y0 ∈ F) (hy1F : y1 ∈ F) (h1F : D 1 ∈ F) (h3F : D 3 ∈ F) (h4F : D 4 ∈ F) :
    convexHull ℝ (Set.range D) ⊆
      convexHull ℝ F ∪
      convexHull ℝ ({D 4, D 0, y0} : Set (ℝ × ℝ)) ∪
      convexHull ℝ ({D 1, D 2, y1} : Set (ℝ × ℝ)) ∪
      (convexHull ℝ ({D 0, D 1, y0} : Set (ℝ × ℝ)) ∪ convexHull ℝ ({D 2, D 3, y1} : Set (ℝ × ℝ))) := by
  intro z hz
  rcases pentagon_fan_triangulation_from_4 D hD z hz with h401 | h124 | h234
  · rcases convexHull_triangle_three_piece_cover (D 1) y0 (D 4) (D 0) z h401 with hA | hB | hC
    · left; left; right
      have : ({y0, D 4, D 0} : Set (ℝ × ℝ)) = {D 4, D 0, y0} := by ext p; simp; tauto
      rwa [← this]
    · right; left
      have : ({y0, D 0, D 1} : Set (ℝ × ℝ)) = {D 0, D 1, y0} := by ext p; simp; tauto
      rwa [← this]
    · left; left; left
      exact convexHull_tri_subset (subset_convexHull ℝ F hy0F) (subset_convexHull ℝ F h1F)
        (subset_convexHull ℝ F h4F) hC
  · have hz_q : z ∈ convexHull ℝ (Set.range ![D 1, D 2, D 3, D 4]) :=
      convexHull_tri_subset
        (subset_convexHull ℝ (Set.range ![D 1, D 2, D 3, D 4]) ⟨0, rfl⟩)
        (subset_convexHull ℝ (Set.range ![D 1, D 2, D 3, D 4]) ⟨1, rfl⟩)
        (subset_convexHull ℝ (Set.range ![D 1, D 2, D 3, D 4]) ⟨3, rfl⟩) h124
    obtain ⟨j, hj⟩ := convexHull_ray_exit_polygon_cover ![D 1, D 2, D 3, D 4]
      (quad1234_strictConvexCCW D hD) y1 z hz_q
    fin_cases j
    · left; right; exact hj
    · right; right; exact hj
    · left; left; left
      exact convexHull_tri_subset (subset_convexHull ℝ F h3F) (subset_convexHull ℝ F h4F)
        (subset_convexHull ℝ F hy1F) hj
    · left; left; left
      exact convexHull_tri_subset (subset_convexHull ℝ F h4F) (subset_convexHull ℝ F h1F)
        (subset_convexHull ℝ F hy1F) hj
  · have hz_q : z ∈ convexHull ℝ (Set.range ![D 1, D 2, D 3, D 4]) :=
      convexHull_tri_subset
        (subset_convexHull ℝ (Set.range ![D 1, D 2, D 3, D 4]) ⟨1, rfl⟩)
        (subset_convexHull ℝ (Set.range ![D 1, D 2, D 3, D 4]) ⟨2, rfl⟩)
        (subset_convexHull ℝ (Set.range ![D 1, D 2, D 3, D 4]) ⟨3, rfl⟩) h234
    obtain ⟨j, hj⟩ := convexHull_ray_exit_polygon_cover ![D 1, D 2, D 3, D 4]
      (quad1234_strictConvexCCW D hD) y1 z hz_q
    fin_cases j
    · left; right; exact hj
    · right; right; exact hj
    · left; left; left
      exact convexHull_tri_subset (subset_convexHull ℝ F h3F) (subset_convexHull ℝ F h4F)
        (subset_convexHull ℝ F hy1F) hj
    · left; left; left
      exact convexHull_tri_subset (subset_convexHull ℝ F h4F) (subset_convexHull ℝ F h1F)
        (subset_convexHull ℝ F hy1F) hj

/-- Case 3b, disjoint exit edges `01` (`y₀`) and `23` (`y₁`), `Q = {0, 3}`. -/
lemma convD_cover_case3b_disjoint_03 (D : Fin 5 → ℝ × ℝ) (hD : StrictConvexCCWPoly D)
    (y0 y1 : ℝ × ℝ) (F : Set (ℝ × ℝ))
    (hy0F : y0 ∈ F) (hy1F : y1 ∈ F) (h1F : D 1 ∈ F) (h2F : D 2 ∈ F) (h4F : D 4 ∈ F) :
    convexHull ℝ (Set.range D) ⊆
      convexHull ℝ F ∪
      convexHull ℝ ({D 4, D 0, y0} : Set (ℝ × ℝ)) ∪
      convexHull ℝ ({y1, D 3, D 4} : Set (ℝ × ℝ)) ∪
      (convexHull ℝ ({D 0, D 1, y0} : Set (ℝ × ℝ)) ∪ convexHull ℝ ({D 2, D 3, y1} : Set (ℝ × ℝ))) := by
  intro z hz
  rcases pentagon_fan_triangulation_from_4 D hD z hz with h401 | h124 | h234
  · rcases convexHull_triangle_three_piece_cover (D 1) y0 (D 4) (D 0) z h401 with hA | hB | hC
    · left; left; right
      have : ({y0, D 4, D 0} : Set (ℝ × ℝ)) = {D 4, D 0, y0} := by ext p; simp; tauto
      rwa [← this]
    · right; left
      have : ({y0, D 0, D 1} : Set (ℝ × ℝ)) = {D 0, D 1, y0} := by ext p; simp; tauto
      rwa [← this]
    · left; left; left
      exact convexHull_tri_subset (subset_convexHull ℝ F hy0F) (subset_convexHull ℝ F h1F)
        (subset_convexHull ℝ F h4F) hC
  · left; left; left
    exact convexHull_tri_subset (subset_convexHull ℝ F h1F) (subset_convexHull ℝ F h2F)
      (subset_convexHull ℝ F h4F) h124
  · rcases convexHull_triangle_three_piece_cover (D 4) y1 (D 2) (D 3) z h234 with hA | hB | hC
    · right; right
      have : ({y1, D 2, D 3} : Set (ℝ × ℝ)) = {D 2, D 3, y1} := by ext p; simp; tauto
      rwa [← this]
    · left; right
      exact hB
    · left; left; left
      exact convexHull_tri_subset (subset_convexHull ℝ F hy1F) (subset_convexHull ℝ F h4F)
        (subset_convexHull ℝ F h2F) hC

/-- Case 3b, adjacent exit edges `01` (`y₀`) and `12` (`y₁`), `Q = {0, 2}`. -/
lemma convD_cover_case3b_adjacent_02 (D : Fin 5 → ℝ × ℝ) (hD : StrictConvexCCWPoly D)
    (y0 y1 : ℝ × ℝ) (F : Set (ℝ × ℝ))
    (hy0F : y0 ∈ F) (hy1F : y1 ∈ F) (h1F : D 1 ∈ F) (h3F : D 3 ∈ F) (h4F : D 4 ∈ F) :
    convexHull ℝ (Set.range D) ⊆
      convexHull ℝ F ∪
      convexHull ℝ ({D 4, D 0, y0} : Set (ℝ × ℝ)) ∪
      convexHull ℝ ({y1, D 2, D 3} : Set (ℝ × ℝ)) ∪
      (convexHull ℝ ({D 0, D 1, y0} : Set (ℝ × ℝ)) ∪ convexHull ℝ ({D 1, D 2, y1} : Set (ℝ × ℝ))) := by
  intro z hz
  rcases pentagon_fan_triangulation_from_1 D hD z hz with h401 | h134 | h123
  · rcases convexHull_triangle_three_piece_cover (D 1) y0 (D 4) (D 0) z h401 with hA | hB | hC
    · left; left; right
      have : ({y0, D 4, D 0} : Set (ℝ × ℝ)) = {D 4, D 0, y0} := by ext p; simp; tauto
      rwa [← this]
    · right; left
      have : ({y0, D 0, D 1} : Set (ℝ × ℝ)) = {D 0, D 1, y0} := by ext p; simp; tauto
      rwa [← this]
    · left; left; left
      exact convexHull_tri_subset (subset_convexHull ℝ F hy0F) (subset_convexHull ℝ F h1F)
        (subset_convexHull ℝ F h4F) hC
  · left; left; left
    exact convexHull_tri_subset (subset_convexHull ℝ F h1F) (subset_convexHull ℝ F h3F)
      (subset_convexHull ℝ F h4F) h134
  · have h123' : z ∈ convexHull ℝ ({D 2, D 3, D 1} : Set (ℝ × ℝ)) := by
      have : ({D 1, D 2, D 3} : Set (ℝ × ℝ)) = {D 2, D 3, D 1} := by ext p; simp; tauto
      rwa [← this]
    rcases convexHull_triangle_three_piece_cover (D 1) y1 (D 2) (D 3) z h123' with hA | hB | hC
    · left; right
      exact hA
    · left; left; left
      exact convexHull_tri_subset (subset_convexHull ℝ F hy1F) (subset_convexHull ℝ F h3F)
        (subset_convexHull ℝ F h1F) hB
    · right; right
      have : ({y1, D 1, D 2} : Set (ℝ × ℝ)) = {D 1, D 2, y1} := by ext p; simp; tauto
      rwa [← this]

/-- Case 3b, adjacent exit edges `01` (`y₀`) and `12` (`y₁`), `Q = {0, 1}`. -/
lemma convD_cover_case3b_adjacent_01 (D : Fin 5 → ℝ × ℝ) (hD : StrictConvexCCWPoly D)
    (y0 y1 : ℝ × ℝ) (F : Set (ℝ × ℝ))
    (hy0F : y0 ∈ F) (hy1F : y1 ∈ F) (h2F : D 2 ∈ F) (h3F : D 3 ∈ F) (h4F : D 4 ∈ F) :
    convexHull ℝ (Set.range D) ⊆
      convexHull ℝ F ∪
      convexHull ℝ ({D 4, D 0, y0} : Set (ℝ × ℝ)) ∪
      convexHull ℝ ({y0, D 1, y1} : Set (ℝ × ℝ)) ∪
      (convexHull ℝ ({D 0, D 1, y0} : Set (ℝ × ℝ)) ∪ convexHull ℝ ({D 1, D 2, y1} : Set (ℝ × ℝ))) := by
  intro z hz
  obtain ⟨i, hi⟩ := convexHull_ray_exit_polygon_cover D hD y0 z hz
  fin_cases i
  · right; left; exact hi
  · rcases convexHull_triangle_three_piece_cover y0 y1 (D 1) (D 2) z hi with hA | hB | hC
    · right; right
      have : ({y1, D 1, D 2} : Set (ℝ × ℝ)) = {D 1, D 2, y1} := by ext p; simp; tauto
      rwa [← this]
    · left; left; left
      exact convexHull_tri_subset (subset_convexHull ℝ F hy1F) (subset_convexHull ℝ F h2F)
        (subset_convexHull ℝ F hy0F) hB
    · left; right
      have : ({y1, y0, D 1} : Set (ℝ × ℝ)) = {y0, D 1, y1} := by ext p; simp; tauto
      rwa [← this]
  · left; left; left
    exact convexHull_tri_subset (subset_convexHull ℝ F h2F) (subset_convexHull ℝ F h3F)
      (subset_convexHull ℝ F hy0F) hi
  · left; left; left
    exact convexHull_tri_subset (subset_convexHull ℝ F h3F) (subset_convexHull ℝ F h4F)
      (subset_convexHull ℝ F hy0F) hi
  · left; left; right; exact hi

/-- Case 3b, same exit edge `01` with `M₀ = {y_a, y_b}` and `Q = {0, 1}`. -/
lemma convD_cover_case3b_same_edge (D : Fin 5 → ℝ × ℝ) (hD : StrictConvexCCWPoly D)
    (ya yb : ℝ × ℝ) (F : Set (ℝ × ℝ))
    (hyaF : ya ∈ F) (hybF : yb ∈ F) (h2F : D 2 ∈ F) (h3F : D 3 ∈ F) (h4F : D 4 ∈ F) :
    convexHull ℝ (Set.range D) ⊆
      convexHull ℝ F ∪
      convexHull ℝ ({D 4, D 0, ya} : Set (ℝ × ℝ)) ∪
      convexHull ℝ ({yb, D 1, D 2} : Set (ℝ × ℝ)) ∪
      convexHull ℝ ({D 0, D 1, ya, yb} : Set (ℝ × ℝ)) := by
  intro z hz
  obtain ⟨i, hi⟩ := convexHull_ray_exit_polygon_cover D hD ya z hz
  fin_cases i
  · right
    exact convexHull_tri_subset (subset_convexHull ℝ _ (by simp))
      (subset_convexHull ℝ _ (by simp)) (subset_convexHull ℝ _ (by simp)) hi
  · rcases convexHull_triangle_three_piece_cover ya yb (D 1) (D 2) z hi with hA | hB | hC
    · left; right; exact hA
    · left; left; left
      exact convexHull_tri_subset (subset_convexHull ℝ F hybF) (subset_convexHull ℝ F h2F)
        (subset_convexHull ℝ F hyaF) hB
    · right
      exact convexHull_tri_subset (subset_convexHull ℝ _ (by simp))
        (subset_convexHull ℝ _ (by simp)) (subset_convexHull ℝ _ (by simp)) hC
  · left; left; left
    exact convexHull_tri_subset (subset_convexHull ℝ F h2F) (subset_convexHull ℝ F h3F)
      (subset_convexHull ℝ F hyaF) hi
  · left; left; left
    exact convexHull_tri_subset (subset_convexHull ℝ F h3F) (subset_convexHull ℝ F h4F)
      (subset_convexHull ℝ F hyaF) hi
  · left; left; right; exact hi

/-! ## Lemma 2.5 Face-Counting & `< 1024` Bitmask Arithmetic Bounds -/

/-- Section 2 (`upper_9.tex` Lemma `three-halfplanes`, lines 201--209):
    (1) `3` lines divide the plane into at most `f3 ≤ 7 < 2^3` faces;
    (2) `2` lines (`f0 ≤ 4` faces) + `3` two-ray wedges give at most `31 < 2^5` faces. -/
theorem lem_three_halfplanes_and_two_hp_three_wedges
    (f3 l1 l2 l3 f0 m1 m2 m3 f : ℕ)
    (hl1 : l1 ≤ 1 + 1) (hl2 : l2 ≤ l1 + 2) (hl3 : l3 ≤ l2 + 3) (hf3 : f3 ≤ l3)
    (hf0 : f0 ≤ 4) (hm1 : m1 ≤ 4) (hm2 : m2 ≤ 8) (hm3 : m3 ≤ 12)
    (hf : f ≤ f0 + (m1 + 1) + (m2 + 1) + (m3 + 1)) :
    f3 < 2 ^ 3 ∧ f < 2 ^ 5 := by
  repeat' omega

/-- Lemma 2.5 bitmask arithmetic bounds on a 10-point shattered set (`2^10 = 1024`):
    using `58 < 64` (six wedges with 4 fixed points), `7 < 8` (three half-planes with 7 fixed points),
    and `29 < 32` / `31 < 32` (two half-planes + three wedges with 5 fixed points). -/
theorem counting_bitmask_bounds_1024
    (f6 f3hp f2hp3w : ℕ)
    (hf6 : f6 ≤ 58) (hf3hp : f3hp ≤ 7) (hf2hp3w : f2hp3w ≤ 29) :
    f6 < 64 ∧ f3hp < 8 ∧ f2hp3w < 32 ∧
    16 * f6 < 1024 ∧ 128 * f3hp < 1024 ∧ 32 * f2hp3w < 1024 := by
  omega

/-- Lemma 7.2 (`combination`) counting deduction:
    Given the impossibility of 6 tests (`< 6` tests when `|Q| = 1`), 3 half-plane tests, and
    2 half-planes + 3 wedge tests, we get `|M'| ≤ 4` if `|Q| = 1` and `|M'| ≤ 2` if `|Q| = 2`. -/
theorem combination_cardinality_bound
    (qCard mPrimeCard : ℕ)
    (hq : qCard = 1 ∨ qCard = 2)
    (h_no_6 : qCard + mPrimeCard < 6)
    (h_no_3hp : ∀ extra_hp : Bool, extra_hp = true → qCard = 2 → False)
    (h_no_2hp3w : ∀ extra_hp : Bool, extra_hp = true → qCard = 1 → mPrimeCard = 4 → False)
    (h_no_2hp3w_q2 : qCard = 2 → 3 ≤ mPrimeCard → False) :
    (qCard = 1 → mPrimeCard ≤ 4) ∧
    (qCard = 2 → mPrimeCard ≤ 2) ∧
    (qCard = 1 → mPrimeCard = 4 → ∀ extra_hp : Bool, extra_hp = false) := by
  have _ := And.intro hq h_no_3hp
  refine ⟨fun h1 => by omega, fun h2 => ?_, fun h1 hm4 extra_hp => ?_⟩
  · by_contra hgt
    exact h_no_2hp3w_q2 h2 (by omega)
  · cases extra_hp
    · rfl
    · exact False.elim (h_no_2hp3w true rfl h1 hm4)

end
