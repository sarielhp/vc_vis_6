import Mathlib
import RootTask.PolygonDefs
import RootTask.Sec8And11Master

open scoped Classical BigOperators
open Finset

noncomputable section

/-!
# Section 11: Visibility-to-Wedges Bridge (`upper_9.tex` Sections 11 & Props 8.6–8.7)

Formalizes the complete visibility-to-wedges bridge from `ShatteredSimplePolygon P S w`
(`n = 10`, Section 8.4 adjacent-exit pentagon reduction) to `False` via:
1. **Lemma 11.1 (`two_sided_visibility_separation`)**: Two-sided visibility separation over
   `ShatteredSimplePolygon` (`two_path_enclosure` + `(G1)`).
2. **Lemma 11.2 (`pentagon_cells_*`)**: Witness localization parts (ii) and (iii) (`pentagon-cells`),
   including missing-single-vertex witnesses `x_k(m)` in `(H_{k-1}^+ ∪ H_k^+)` and `m = 11111` XOR
   conditions, plus certified-vertex cone inclusions `U(h; 0, 1) ⊆ H_0^+ ∩ H_{r*}^-` and
   `U(h; 0, 2) ⊆ H_{02}^+ ∩ H_{r*}^-`.
3. **Lemma 11.3 (`adjacent_ear_empty_and_chord_wedges`)**: Unconditional ear emptiness
   `△(0, 1, 2) ∩ M = ∅`, `w_D ∈ H^+(0, 2)`, `M ⊆ int △(w_D, 0, 2)`, and extraction of the five
   open convex wedges `W_0, ..., W_4` deciding visibility of `M` on `W({u_0, v_0})`.
4. **Theorem 11.4 (`localized_pentagon_shattered_contradiction`)**: Complete contradiction from the
   Section 8.4 adjacent-exit pentagon output across both Regime 1 (`01`) and Regime 2 (`01/12`),
   and both Case 1 (`H ≠ ∅`) and Case 2 (`H = ∅`).
-/

namespace Sec11Bridge

/-! ## Part 0: Self-Contained Visibility, Cone, and Wedge-Extraction Primitives -/

lemma orient2D_swap12 (a b c : ℝ × ℝ) : orient2D b a c = -orient2D a b c := by
  unfold orient2D; ring

lemma sees_mem_left {P : Set (ℝ × ℝ)} {x y : ℝ × ℝ} (h : Sees P x y) : x ∈ P :=
  h (left_mem_segment ℝ x y)

lemma sees_mem_right {P : Set (ℝ × ℝ)} {x y : ℝ × ℝ} (h : Sees P x y) : y ∈ P :=
  h (right_mem_segment ℝ x y)

lemma sees_of_mem_segment_left {P : Set (ℝ × ℝ)} {x y z : ℝ × ℝ}
    (h : Sees P x y) (hz : z ∈ segment ℝ x y) : Sees P x z :=
  ((convex_segment x y).segment_subset (left_mem_segment ℝ x y) hz).trans h

lemma two_path_enclosure_either {P : Set (ℝ × ℝ)} {s t : ℝ × ℝ} {π₁ π₂ : List (ℝ × ℝ)}
    (h2path : ∀ (s t : ℝ × ℝ) (π₁ π₂ : List (ℝ × ℝ)),
      s ≠ t → IsPolygonalPathIn P s t π₁ → IsPolygonalPathIn P s t π₂ →
      InteriorOnLeft s t π₁ → InteriorOnRight s t π₂ → Sees P s t)
    (hst : s ≠ t)
    (hp₁ : IsPolygonalPathIn P s t π₁) (hp₂ : IsPolygonalPathIn P s t π₂)
    (hsides : (InteriorOnLeft s t π₁ ∧ InteriorOnRight s t π₂) ∨
              (InteriorOnRight s t π₁ ∧ InteriorOnLeft s t π₂)) :
    Sees P s t := by
  rcases hsides with ⟨hL, hR⟩ | ⟨hR, hL⟩
  · exact h2path s t π₁ π₂ hst hp₁ hp₂ hL hR
  · exact h2path s t π₂ π₁ hst hp₂ hp₁ hL hR

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

lemma witnessSet_mono {n : ℕ} {F F' N N' : Finset (Fin n)} {w : Finset (Fin n) → ℝ × ℝ}
    (hF : F ⊆ F') (hN : N ⊆ N') :
    WitnessSet F' N' w ⊆ WitnessSet F N w := by
  rintro x ⟨T, hFT, hdisj, rfl⟩
  exact ⟨T, hF.trans hFT, hdisj.mono_right hN, rfl⟩

/-- Strict interior of triangle `(p, q, r)` via strictly positive barycentric coordinates. -/
def InOpenTri (p q r z : ℝ × ℝ) : Prop :=
  ∃ μ₁ μ₂ μ₃ : ℝ, 0 < μ₁ ∧ 0 < μ₂ ∧ 0 < μ₃ ∧ μ₁ + μ₂ + μ₃ = 1 ∧
    z.1 = μ₁ * p.1 + μ₂ * q.1 + μ₃ * r.1 ∧
    z.2 = μ₁ * p.2 + μ₂ * q.2 + μ₃ * r.2

lemma InOpenTri.to_inClosedTri {p q r z : ℝ × ℝ} (h : InOpenTri p q r z) : InClosedTri p q r z := by
  rcases h with ⟨μ₁, μ₂, μ₃, h1, h2, h3, hsum, hx, hy⟩
  exact ⟨μ₁, μ₂, μ₃, le_of_lt h1, le_of_lt h2, le_of_lt h3, hsum, hx, hy⟩

lemma InOpenTri.to_convexHull {p q r z : ℝ × ℝ} (h : InOpenTri p q r z) :
    z ∈ convexHull ℝ ({p, q, r} : Set (ℝ × ℝ)) :=
  (inClosedTri_iff_mem_convexHull p q r z).mp h.to_inClosedTri

lemma InOpenTri.perm_23 {p q r z : ℝ × ℝ} (h : InOpenTri p q r z) : InOpenTri p r q z := by
  rcases h with ⟨μ₁, μ₂, μ₃, h1, h2, h3, hsum, hx, hy⟩
  exact ⟨μ₁, μ₃, μ₂, h1, h3, h2, by linarith, by linarith, by linarith⟩

lemma inOpenTri_of_noncollinear_inClosedTri {p q r z : ℝ × ℝ}
    (hclosed : InClosedTri p q r z)
    (h1 : orient2D q r z ≠ 0) (h2 : orient2D r p z ≠ 0) (h3 : orient2D p q z ≠ 0) :
    InOpenTri p q r z := by
  rcases hclosed with ⟨μ₁, μ₂, μ₃, hm1, hm2, hm3, hsum, hz1, hz2⟩
  have hpos1 : 0 < μ₁ := by
    refine lt_of_le_of_ne hm1 (fun heq => h1 ?_)
    subst heq
    have hμ : μ₂ = 1 - μ₃ := by linarith
    unfold orient2D; rw [hz1, hz2, hμ]; ring
  have hpos2 : 0 < μ₂ := by
    refine lt_of_le_of_ne hm2 (fun heq => h2 ?_)
    subst heq
    have hμ : μ₁ = 1 - μ₃ := by linarith
    unfold orient2D; rw [hz1, hz2, hμ]; ring
  have hpos3 : 0 < μ₃ := by
    refine lt_of_le_of_ne hm3 (fun heq => h3 ?_)
    subst heq
    have hμ : μ₁ = 1 - μ₂ := by linarith
    unfold orient2D; rw [hz1, hz2, hμ]; ring
  exact ⟨μ₁, μ₂, μ₃, hpos1, hpos2, hpos3, hsum, hz1, hz2⟩

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
      field_simp [h1_ne]; rw [ha1, show μ₁ = 1 - μ₂ - μ₃ by linarith]; ring
    · change x.2 = a.2 + (μ₂ / μ₁) * (a.2 - b.2) + (μ₃ / μ₁) * (a.2 - c.2)
      field_simp [h1_ne]; rw [ha2, show μ₁ = 1 - μ₂ - μ₃ by linarith]; ring

theorem u_halfplanes {a b c : ℝ × ℝ} (h_ccw : 0 < orient2D a b c) (x : ℝ × ℝ) :
    (x ∈ UCone a b c ↔ orient2D c a x < 0 ∧ orient2D a b x < 0) ∧
    (x ∈ UCone a b c ↔ (oppositeConeWedge a b c h_ccw).MemOpen x) ∧
    (x ∈ UCone a b c → orient2D c b x < 0) := by
  have hcax_eq : ∀ α β : ℝ,
      orient2D c a (a + α • (a - b) + β • (a - c)) = -α * orient2D a b c := by
    intro α β; unfold orient2D
    simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
      Prod.fst_sub, Prod.snd_sub, smul_eq_mul]; ring
  have habx_eq : ∀ α β : ℝ,
      orient2D a b (a + α • (a - b) + β • (a - c)) = -β * orient2D a b c := by
    intro α β; unfold orient2D
    simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
      Prod.fst_sub, Prod.snd_sub, smul_eq_mul]; ring
  have hcbx_eq : ∀ α β : ℝ,
      orient2D c b (a + α • (a - b) + β • (a - c)) = -(1 + α + β) * orient2D a b c := by
    intro α β; unfold orient2D
    simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
      Prod.fst_sub, Prod.snd_sub, smul_eq_mul]; ring
  have h1 : x ∈ UCone a b c ↔ orient2D c a x < 0 ∧ orient2D a b x < 0 := by
    constructor
    · rintro ⟨α, β, hα, hβ, rfl⟩; rw [hcax_eq, habx_eq]; exact ⟨by nlinarith, by nlinarith⟩
    · rintro ⟨hcax, habx⟩
      have hd_ne : orient2D a b c ≠ 0 := ne_of_gt h_ccw
      let α := -orient2D c a x / orient2D a b c
      let β := -orient2D a b x / orient2D a b c
      refine ⟨α, β, div_pos (neg_pos.mpr hcax) h_ccw, div_pos (neg_pos.mpr habx) h_ccw, ?_⟩
      ext
      · change x.1 = a.1 + α * (a.1 - b.1) + β * (a.1 - c.1)
        dsimp [α, β]; unfold orient2D; unfold orient2D at hd_ne; field_simp [hd_ne]; ring
      · change x.2 = a.2 + α * (a.2 - b.2) + β * (a.2 - c.2)
        dsimp [α, β]; unfold orient2D; unfold orient2D at hd_ne; field_simp [hd_ne]; ring
  have hwedge : (oppositeConeWedge a b c h_ccw).MemOpen x ↔
      orient2D c a x < 0 ∧ orient2D a b x < 0 := by
    unfold OpenWedge.MemOpen oppositeConeWedge orient2D; dsimp only
    constructor <;> rintro ⟨u, v⟩ <;> exact ⟨by linarith, by linarith⟩
  have h3 : x ∈ UCone a b c → orient2D c b x < 0 := by
    rintro ⟨α, β, hα, hβ, rfl⟩; rw [hcbx_eq]; nlinarith
  exact ⟨h1, h1.trans hwedge.symm, h3⟩

lemma u_halfplanes_separates {a b c x : ℝ × ℝ} (h_neq : orient2D a b c ≠ 0)
    (hx : x ∈ UCone a b c) : orient2D a x b * orient2D a x c < 0 := by
  rcases lt_trichotomy (orient2D a b c) 0 with hneg | hzero | hpos
  · have hccw : 0 < orient2D a c b := by rw [orient2D_swap23]; linarith
    have hx' : x ∈ UCone a c b := (uCone_symm a b c) ▸ hx
    obtain ⟨hb, hc⟩ := ((u_halfplanes hccw x).1).mp hx'
    have hb' : orient2D a x b < 0 := by have := orient2D_cycle b a x; linarith
    have hc' : 0 < orient2D a x c := by rw [orient2D_swap23]; linarith
    exact mul_neg_of_neg_of_pos hb' hc'
  · exact False.elim (h_neq hzero)
  · obtain ⟨hc, hb⟩ := ((u_halfplanes hpos x).1).mp hx
    have hb' : 0 < orient2D a x b := by rw [orient2D_swap23]; linarith
    have hc' : orient2D a x c < 0 := by have := orient2D_cycle c a x; linarith
    exact mul_neg_of_pos_of_neg hb' hc'

private structure EncDomain (P : Set (ℝ × ℝ)) : Prop where
  tri : ∀ x ∈ P, ∀ y ∈ P, ∀ z ∈ P, Sees P x y → Sees P y z → Sees P x z →
    convexHull ℝ ({x, y, z} : Set (ℝ × ℝ)) ⊆ P
  two_path : ∀ (s t : ℝ × ℝ) (π₁ π₂ : List (ℝ × ℝ)),
    s ≠ t → IsPolygonalPathIn P s t π₁ → IsPolygonalPathIn P s t π₂ →
    InteriorOnLeft s t π₁ → InteriorOnRight s t π₂ → Sees P s t

private lemma sees_of_collinear_inOpenTri {P : Set (ℝ × ℝ)} {w b c a : ℝ × ℝ}
    (hwb : Sees P w b) (hwc : Sees P w c) (ha : InOpenTri w b c a) (hcol : orient2D w b c = 0) :
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
        · rw [hbw, segment_same] at hzb; rw [Set.mem_singleton_iff.mp hzb]
          exact ⟨0, ⟨min_le_left _ _, le_max_of_le_left zero_le_one⟩, by ext <;> simp⟩
        · rw [segment_eq_image] at hzc; rcases hzc with ⟨t, ht, rfl⟩
          exact ⟨t, ⟨le_trans (min_le_left _ _) ht.1, le_trans ht.2 (le_max_left _ _)⟩,
            by ext <;> simp [smul_eq_mul] <;> ring⟩
      · rintro _ ⟨t, ht, rfl⟩
        have ht01 : t ∈ Set.Icc 0 1 := by
          have hm1 : min 0 (min (0 : ℝ) 1) = 0 := by norm_num
          have hm2 : max 1 (max (0 : ℝ) 1) = 1 := by norm_num
          rw [hm1, hm2] at ht; exact ht
        right; rw [segment_eq_image]; exact ⟨t, ht01, by ext <;> simp [smul_eq_mul] <;> ring⟩
    · have hbw_coord : b.1 - w.1 ≠ 0 ∨ b.2 - w.2 ≠ 0 := by
        by_contra hc; push Not at hc; exact hbw (by ext <;> linarith [hc.1, hc.2])
      obtain ⟨k, hk1, hk2⟩ : ∃ k : ℝ, c.1 = w.1 + k * (b.1 - w.1) ∧ c.2 = w.2 + k * (b.2 - w.2) := by
        unfold orient2D at hcol
        rcases hbw_coord with hx | hy
        · refine ⟨(c.1 - w.1) / (b.1 - w.1), by field_simp [hx]; ring,
            by field_simp [hx]; linear_combination hcol⟩
        · refine ⟨(c.2 - w.2) / (b.2 - w.2), by field_simp [hy]; linear_combination -hcol,
            by field_simp [hy]; ring⟩
      refine ⟨b - w, 1, k, by ext <;> simp, by ext <;> simp [hk1, hk2], ?_, ?_⟩
      · rintro z (hzb | hzc)
        · rw [segment_eq_image] at hzb; rcases hzb with ⟨t, ht, rfl⟩
          exact ⟨t, ⟨le_trans (min_le_left _ _) ht.1, le_trans ht.2 (le_max_left _ _)⟩,
            by ext <;> simp [smul_eq_mul] <;> ring⟩
        · rw [segment_eq_image] at hzc; rcases hzc with ⟨t, ht, rfl⟩
          refine ⟨t * k, ⟨?_, ?_⟩, ?_⟩
          · by_cases hk0 : 0 ≤ k
            · exact le_trans (min_le_left _ _) (mul_nonneg ht.1 hk0)
            · have hk_neg : k < 0 := not_le.mp hk0
              exact le_trans (min_le_of_right_le (min_le_right _ _)) (by nlinarith [ht.1, ht.2])
          · by_cases hk0 : 0 ≤ k
            · exact le_trans (mul_le_of_le_one_left hk0 ht.2) (le_max_of_le_right (le_max_right _ _))
            · have hk_neg : k < 0 := not_le.mp hk0
              exact le_trans (mul_nonpos_of_nonneg_of_nonpos ht.1 (le_of_lt hk_neg)) (le_max_of_le_left zero_le_one)
          · ext <;> simp [smul_eq_mul, hk1, hk2] <;> ring
      · rintro _ ⟨t, ht, rfl⟩
        by_cases ht01 : 0 ≤ t ∧ t ≤ 1
        · left; rw [segment_eq_image]; exact ⟨t, ht01, by ext <;> simp [smul_eq_mul] <;> ring⟩
        · right; rw [segment_eq_image]
          have ht' : min 0 k ≤ t ∧ t ≤ max 1 k := by
            simp only [Set.mem_Icc, min_le_iff, le_max_iff] at ht
            rcases ht with ⟨hlo, hhi⟩
            refine ⟨?_, ?_⟩
            · rcases hlo with h0 | h1 | hk <;>
                [exact min_le_of_left_le h0; exact min_le_of_left_le (by linarith); exact min_le_of_right_le hk]
            · rcases hhi with h1 | h1' | hk <;>
                [exact le_max_of_le_left h1; exact le_max_of_le_left h1'; exact le_max_of_le_right hk]
          by_cases ht_neg : t < 0
          · have hk_neg : k < 0 := by rcases min_le_iff.mp ht'.1 with h0 | hk <;> linarith
            refine ⟨t / k, ⟨div_nonneg_of_nonpos (le_of_lt ht_neg) (le_of_lt hk_neg), ?_⟩, ?_⟩
            · rw [div_le_one_of_neg hk_neg]; rcases min_le_iff.mp ht'.1 with h0 | hk <;> linarith
            · have hk_ne : k ≠ 0 := ne_of_lt hk_neg
              ext <;> simp [smul_eq_mul, hk1, hk2] <;> field_simp [hk_ne] <;> ring
          · have ht_gt1 : 1 < t := by
              push Not at ht_neg; by_contra hle; exact ht01 ⟨ht_neg, not_lt.mp hle⟩
            have hk_gt1 : 1 < k := by rcases le_max_iff.mp ht'.2 with h1 | hk <;> linarith
            refine ⟨t / k, ⟨div_nonneg (by linarith) (by linarith), (div_le_one (by linarith)).mpr ?_⟩, ?_⟩
            · rcases le_max_iff.mp ht'.2 with h1 | hk <;> linarith
            · have hk_ne : k ≠ 0 := by linarith
              ext <;> simp [smul_eq_mul, hk1, hk2] <;> field_simp [hk_ne] <;> ring
  rcases exists_dir with ⟨d, tb, tc, _, _, hsub1, hsub2⟩
  let Img := (fun t : ℝ => w + t • d) '' Set.Icc (min 0 (min tb tc)) (max 1 (max tb tc))
  have hImg_conv : Convex ℝ Img := by
    rintro _ ⟨t₁, ht1, rfl⟩ _ ⟨t₂, ht2, rfl⟩ α β hα hβ hαβ
    refine ⟨α * t₁ + β * t₂, (convex_Icc _ _) ht1 ht2 hα hβ hαβ, ?_⟩
    ext <;> simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] <;>
      rw [show α = 1 - β by linarith] <;> ring
  have ha_Img : a ∈ Img := by
    have htri : ({w, b, c} : Set (ℝ × ℝ)) ⊆ Img := by
      intro p hp; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
      rcases hp with hpw | hpb | hpc
      · rw [hpw]; exact hsub1 (Or.inl (left_mem_segment ℝ w b))
      · rw [hpb]; exact hsub1 (Or.inl (right_mem_segment ℝ w b))
      · rw [hpc]; exact hsub1 (Or.inr (right_mem_segment ℝ w c))
    exact convexHull_min htri hImg_conv ha.to_convexHull
  exact (hImg_conv.segment_subset (hsub1 (Or.inl (left_mem_segment ℝ w b))) ha_Img).trans
    (hsub2.trans (Set.union_subset hwb hwc))

private lemma cone_aux {P : Set (ℝ × ℝ)} (hEnc : EncDomain P)
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
  have ha_wh : a.1 = μ₁ * w.1 + (μ₂ + μ₃) * h.1 ∧ a.2 = μ₁ * w.2 + (μ₂ + μ₃) * h.2 := by
    have h23_ne : μ₂ + μ₃ ≠ 0 := ne_of_gt hμ23
    constructor <;> dsimp [h] <;> field_simp [h23_ne] <;> [rw [ha1]; rw [ha2]] <;> ring
  have hden : 0 < orient2D w a x - orient2D w a b := by linarith
  let α₁ : ℝ := orient2D w a x / (orient2D w a x - orient2D w a b)
  let α₂ : ℝ := -orient2D w a b / (orient2D w a x - orient2D w a b)
  have hα1 : 0 < α₁ := div_pos hwax hden
  have hα2 : 0 < α₂ := div_pos (neg_pos.mpr hwab) hden
  have hαsum : α₁ + α₂ = 1 := by dsimp [α₁, α₂]; field_simp [ne_of_gt hden]; ring
  let t : ℝ × ℝ := (α₁ * b.1 + α₂ * x.1, α₁ * b.2 + α₂ * x.2)
  have ht_seg : t ∈ segment ℝ b x := by
    rw [segment_eq_image]
    refine ⟨α₂, ⟨le_of_lt hα2, by linarith⟩, ?_⟩
    ext <;> [change (1 - α₂) * b.1 + α₂ * x.1 = α₁ * b.1 + α₂ * x.1;
             change (1 - α₂) * b.2 + α₂ * x.2 = α₁ * b.2 + α₂ * x.2] <;>
      rw [show 1 - α₂ = α₁ by linarith]
  have ht_seg' : t ∈ segment ℝ x b := by rwa [segment_symm]
  have ht_col : orient2D w a t = 0 := by
    have heq := orient2D_affine_comb w a b x t α₂
      (by dsimp [t]; linear_combination b.1 * hαsum)
      (by dsimp [t]; linear_combination b.2 * hαsum)
    rw [heq]; dsimp [α₂]; field_simp [ne_of_gt hden]; ring
  have hwa_ne : w ≠ a := by intro hwa; subst hwa; exact hnwa (sees_refl (sees_mem_left hwb))
  have hwa_coord : a.1 - w.1 ≠ 0 ∨ a.2 - w.2 ≠ 0 := by
    by_contra hc; push Not at hc; exact hwa_ne (by ext <;> linarith [hc.1, hc.2])
  obtain ⟨τ, hτ1, hτ2⟩ : ∃ τ : ℝ, t.1 - w.1 = τ * (a.1 - w.1) ∧ t.2 - w.2 = τ * (a.2 - w.2) := by
    unfold orient2D at ht_col
    rcases hwa_coord with hx1 | hx2
    · exact ⟨(t.1 - w.1) / (a.1 - w.1), by field_simp [hx1],
        by field_simp [hx1]; linear_combination ht_col⟩
    · exact ⟨(t.2 - w.2) / (a.2 - w.2),
        by field_simp [hx2]; linear_combination -ht_col, by field_simp [hx2]⟩
  have hτ_ne1 : τ ≠ 1 := by
    intro hτeq; subst hτeq
    have hta : t = a := by ext <;> linarith
    apply hxab
    have h1 : t.1 = (1 - α₂) * b.1 + α₂ * x.1 := by dsimp [t]; linear_combination b.1 * hαsum
    have h2 : t.2 = (1 - α₂) * b.2 + α₂ * x.2 := by dsimp [t]; linear_combination b.2 * hαsum
    rw [hta] at h1 h2; unfold orient2D; rw [h1, h2]; ring
  rcases lt_or_gt_of_ne hτ_ne1 with hτ_lt | hτ_gt
  · let s := μ₂ + μ₃
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
      field_simp [hne2, hs_ne, hne3]; ring
    have ha_th : a.1 = γ₁ * t.1 + γ₂ * h.1 ∧ a.2 = γ₁ * t.2 + γ₂ * h.2 := by
      have hs_ne : s ≠ 0 := ne_of_gt hs_pos
      have hh1 : h.1 - w.1 = (1 / s) * (a.1 - w.1) := by
        dsimp [s]; field_simp [hs_ne]; rw [ha_wh.1]; linear_combination -w.1 * hμsum
      have hh2 : h.2 - w.2 = (1 / s) * (a.2 - w.2) := by
        dsimp [s]; field_simp [hs_ne]; rw [ha_wh.2]; linear_combination -w.2 * hμsum
      have hne2 : 1 / s - τ ≠ 0 := ne_of_gt hden_th
      have hne3 : 1 - s * τ ≠ 0 := by
        have h1 : 0 < s * (1 / s - τ) := mul_pos hs_pos hden_th
        have h2 : s * (1 / s - τ) = 1 - s * τ := by field_simp [hs_ne]
        linarith
      constructor
      · dsimp [γ₁, γ₂]
        have ht1' : t.1 = w.1 + τ * (a.1 - w.1) := by linarith
        have hh1' : h.1 = w.1 + (1 / s) * (a.1 - w.1) := by linarith
        rw [ht1', hh1']; field_simp [hne2, hs_ne, hne3]; ring
      · dsimp [γ₁, γ₂]
        have ht2' : t.2 = w.2 + τ * (a.2 - w.2) := by linarith
        have hh2' : h.2 = w.2 + (1 / s) * (a.2 - w.2) := by linarith
        rw [ht2', hh2']; field_simp [hne2, hs_ne, hne3]; ring
    have ha_tri : InOpenTri x b c a := by
      let ν₁ : ℝ := γ₁ * α₂
      let ν₂ : ℝ := γ₁ * α₁ + γ₂ * (μ₂ / s)
      let ν₃ : ℝ := γ₂ * (μ₃ / s)
      refine ⟨ν₁, ν₂, ν₃, mul_pos hγ1 hα2,
        add_pos (mul_pos hγ1 hα1) (mul_pos hγ2 (div_pos hμ2 hs_pos)),
        mul_pos hγ2 (div_pos hμ3 hs_pos), ?_, ?_, ?_⟩
      · have hs_ne : s ≠ 0 := ne_of_gt hs_pos
        dsimp [ν₁, ν₂, ν₃, s]; field_simp [hs_ne]
        have heq : γ₁ * α₂ * (μ₂ + μ₃) + (γ₁ * α₁ * (μ₂ + μ₃) + γ₂ * μ₂) + γ₂ * μ₃ =
            (γ₁ * (α₁ + α₂) + γ₂) * (μ₂ + μ₃) := by ring
        rw [heq, hαsum, mul_one, hγsum, one_mul]
      · have hs_ne : s ≠ 0 := ne_of_gt hs_pos
        rw [ha_th.1]; dsimp [ν₁, ν₂, ν₃, t, h, s]; field_simp [hs_ne]; ring
      · have hs_ne : s ≠ 0 := ne_of_gt hs_pos
        rw [ha_th.2]; dsimp [ν₁, ν₂, ν₃, t, h, s]; field_simp [hs_ne]; ring
    exact (mem_uCone_iff_inOpenTri a b c x).mpr ha_tri
  · have hτ_pos : 0 < τ := by linarith
    have hwt_ne : w ≠ t := by
      intro hwt; apply hwa_ne
      have h1 : w.1 - w.1 = τ * (a.1 - w.1) := hwt ▸ hτ1
      have h2 : w.2 - w.2 = τ * (a.2 - w.2) := hwt ▸ hτ2
      ext <;> nlinarith
    have hwt_orient : ∀ p : ℝ × ℝ, orient2D w t p = τ * orient2D w a p := by
      intro p; unfold orient2D; rw [hτ1, hτ2]; ring
    have hbt : Sees P b t := sees_of_mem_segment_left (sees_symm hxb) ht_seg
    have hxt : Sees P x t := sees_of_mem_segment_left hxb ht_seg'
    have hwt_sees : Sees P w t := by
      refine two_path_enclosure_either hEnc.two_path hwt_ne
        (isPolygonalPathIn_three hwb hbt)
        (isPolygonalPathIn_four hwc (sees_symm hxc) hxt)
        (Or.inr ⟨interiorOnRight_three ?_, interiorOnLeft_four ?_ ?_⟩)
      · rw [hwt_orient]; exact mul_neg_of_pos_of_neg hτ_pos hwab
      · rw [hwt_orient]; exact mul_pos hτ_pos hwac
      · rw [hwt_orient]; exact mul_pos hτ_pos hwax
    exfalso; apply hnwa
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
private lemma reflectY_invol (p : ℝ × ℝ) : reflectY (reflectY p) = p := by ext <;> simp [reflectY]
private lemma orient2D_reflectY (a b c : ℝ × ℝ) :
    orient2D (reflectY a) (reflectY b) (reflectY c) = -orient2D a b c := by
  unfold orient2D reflectY; ring

private lemma sees_reflectY_iff {P : Set (ℝ × ℝ)} {x y : ℝ × ℝ} :
    Sees (reflectY '' P) (reflectY x) (reflectY y) ↔ Sees P x y := by
  have himg : segment ℝ (reflectY x) (reflectY y) = reflectY '' segment ℝ x y := by
    ext p; simp only [segment_eq_image, Set.mem_image]; constructor
    · rintro ⟨t, ht, rfl⟩
      refine ⟨(1 - t) • x + t • y, ⟨t, ht, rfl⟩, ?_⟩
      ext <;> (simp [reflectY, smul_eq_mul]; try ring)
    · rintro ⟨q, ⟨t, ht, rfl⟩, rfl⟩
      refine ⟨t, ht, ?_⟩
      ext <;> (simp [reflectY, smul_eq_mul]; try ring)
  constructor
  · intro h p hp
    have hmem : reflectY p ∈ segment ℝ (reflectY x) (reflectY y) := by
      rw [himg]; exact ⟨p, hp, rfl⟩
    rcases h hmem with ⟨q, hq, hqp⟩
    have : q = p := by simpa [reflectY_invol] using congrArg reflectY hqp
    rwa [← this]
  · intro h p hp; rw [himg] at hp; rcases hp with ⟨q, hq, rfl⟩; exact ⟨q, h hq, rfl⟩

private lemma encDomain_reflectY {P : Set (ℝ × ℝ)} (hEnc : EncDomain P) :
    EncDomain (reflectY '' P) := by
  constructor
  · intro x hx y hy z hz hxy hyz hxz
    rcases hx with ⟨x', _, rfl⟩; rcases hy with ⟨y', _, rfl⟩; rcases hz with ⟨z', _, rfl⟩
    have hxy' := sees_reflectY_iff.mp hxy
    have hyz' := sees_reflectY_iff.mp hyz
    have hxz' := sees_reflectY_iff.mp hxz
    have htri := hEnc.tri x' (sees_mem_left hxy') y' (sees_mem_right hxy')
      z' (sees_mem_right hxz') hxy' hyz' hxz'
    intro p hp; rw [← inClosedTri_iff_mem_convexHull] at hp
    rcases hp with ⟨μ₁, μ₂, μ₃, h1, h2, h3, hsum, hp1, hp2⟩
    refine ⟨(μ₁ * x'.1 + μ₂ * y'.1 + μ₃ * z'.1, μ₁ * x'.2 + μ₂ * y'.2 + μ₃ * z'.2), ?_, ?_⟩
    · apply htri; rw [← inClosedTri_iff_mem_convexHull]
      exact ⟨μ₁, μ₂, μ₃, h1, h2, h3, hsum, rfl, rfl⟩
    · ext <;> simp only [reflectY] at hp1 hp2 ⊢ <;> linarith
  · intro s t π₁ π₂ hst hp₁ hp₂ hL hR
    have hst' : reflectY s ≠ reflectY t := fun h => hst (by
      simpa [reflectY_invol] using congrArg reflectY h)
    have hpath : ∀ {π : List (ℝ × ℝ)}, IsPolygonalPathIn (reflectY '' P) s t π →
        IsPolygonalPathIn P (reflectY s) (reflectY t) (π.map reflectY) := by
      intro π hπ; rcases hπ with ⟨hne, hhead, hlast, hmem, hchain⟩
      refine ⟨by simp [hne], ?_, ?_, ?_, ?_⟩
      · cases π with | nil => contradiction | cons a l => simpa [List.head_cons] using congrArg reflectY hhead
      · rw [List.getLast_map]; exact congrArg reflectY hlast
      · intro x hx; rcases List.mem_map.mp hx with ⟨y, hy, rfl⟩
        rcases hmem y hy with ⟨z, hz, hyz⟩
        have : z = reflectY y := by simpa [reflectY_invol] using congrArg reflectY hyz
        rwa [← this]
      · rw [List.isChain_map]
        exact hchain.imp (fun u v huv => sees_reflectY_iff.mp (by simpa [reflectY_invol] using huv))
    have hL' : InteriorOnRight (reflectY s) (reflectY t) (π₁.map reflectY) := by
      refine ⟨by simpa using hL.1, fun k hk hk0 hk1 => ?_⟩
      simp only [List.length_map] at hk hk1; rw [List.getElem_map, orient2D_reflectY]
      exact neg_lt_zero.mpr (hL.2 k hk hk0 hk1)
    have hR' : InteriorOnLeft (reflectY s) (reflectY t) (π₂.map reflectY) := by
      refine ⟨by simpa using hR.1, fun k hk hk0 hk1 => ?_⟩
      simp only [List.length_map] at hk hk1; rw [List.getElem_map, orient2D_reflectY]
      exact neg_pos.mpr (hR.2 k hk hk0 hk1)
    have hsees := hEnc.two_path (reflectY s) (reflectY t) (π₂.map reflectY) (π₁.map reflectY)
      hst' (hpath hp₂) (hpath hp₁) hR' hL'
    rw [← reflectY_invol s, ← reflectY_invol t]; exact sees_reflectY_iff.mpr hsees

private lemma inOpenTri_reflectY {p q r z : ℝ × ℝ} (h : InOpenTri p q r z) :
    InOpenTri (reflectY p) (reflectY q) (reflectY r) (reflectY z) := by
  rcases h with ⟨μ₁, μ₂, μ₃, h1, h2, h3, hsum, hz1, hz2⟩
  exact ⟨μ₁, μ₂, μ₃, h1, h2, h3, hsum, hz1, by simp [reflectY]; linarith⟩

private lemma uCone_reflectY {a b c x : ℝ × ℝ}
    (h : reflectY x ∈ UCone (reflectY a) (reflectY b) (reflectY c)) :
    x ∈ UCone a b c := by
  rw [mem_uCone_iff_inOpenTri] at h ⊢
  simpa [reflectY_invol] using inOpenTri_reflectY h

private lemma cone_of_shattered {n : ℕ} {P : Set (ℝ × ℝ)} {S : Fin n → ℝ × ℝ}
    {w : Finset (Fin n) → ℝ × ℝ} (hP : ShatteredSimplePolygon P S w)
    {a b c w₀ x : ℝ × ℝ}
    (hwb : Sees P w₀ b) (hwc : Sees P w₀ c) (hnwa : ¬ Sees P w₀ a)
    (ha : InOpenTri w₀ b c a) (hxb : Sees P x b) (hxc : Sees P x c)
    (hxab : orient2D a b x ≠ 0) (hxac : orient2D a c x ≠ 0) (hxwa : orient2D w₀ a x ≠ 0) :
    x ∈ UCone a b c := by
  let hEnc : EncDomain P := ⟨hP.triangle_enclosure, hP.two_path_enclosure⟩
  have hwbc_ne : orient2D w₀ b c ≠ 0 := fun hcol => hnwa (sees_of_collinear_inOpenTri hwb hwc ha hcol)
  have hwa_bc : orient2D w₀ a b * orient2D w₀ a c < 0 := by
    rcases ha with ⟨μ₁, μ₂, μ₃, h1, h2, h3, hsum, ha1, ha2⟩
    have hμ1 : μ₁ = 1 - μ₂ - μ₃ := by linarith
    have hwab_eq : orient2D w₀ a b = μ₃ * orient2D w₀ c b := by
      unfold orient2D; rw [ha1, ha2, hμ1]; ring
    have hwac_eq : orient2D w₀ a c = μ₂ * orient2D w₀ b c := by
      unfold orient2D; rw [ha1, ha2, hμ1]; ring
    rw [hwab_eq, hwac_eq, orient2D_swap23 w₀ c b]
    have hsq : 0 < (orient2D w₀ c b) ^ 2 := by
      refine sq_pos_of_ne_zero (fun h0 => hwbc_ne ?_)
      rw [orient2D_swap23, h0, neg_zero]
    nlinarith [mul_pos h2 h3, hsq]
  have cone_pos : ∀ {P' : Set (ℝ × ℝ)} (_ : EncDomain P') {a' b' c' w' x' : ℝ × ℝ},
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
      exact cone_aux hEnc' hwc' hwb' hnwa' ha'.perm_23 hxc' hxb' hwac_neg hwab_pos hwax' hxac'
  rcases lt_or_gt_of_ne hxwa with hwax_neg | hwax_pos
  · apply uCone_reflectY
    apply cone_pos (encDomain_reflectY hEnc)
      (sees_reflectY_iff.mpr hwb) (sees_reflectY_iff.mpr hwc)
      (fun h => hnwa (sees_reflectY_iff.mp h)) (inOpenTri_reflectY ha)
      (sees_reflectY_iff.mpr hxb) (sees_reflectY_iff.mpr hxc)
      (by rw [orient2D_reflectY]; exact neg_ne_zero.mpr hxab)
      (by rw [orient2D_reflectY]; exact neg_ne_zero.mpr hxac)
      (by rw [orient2D_reflectY, orient2D_reflectY]; linarith)
      (by rw [orient2D_reflectY]; exact neg_pos.mpr hwax_neg)
  · exact cone_pos hEnc hwb hwc hnwa ha hxb hxc hxab hxac hwa_bc hwax_pos

private lemma wedge_extraction {n : ℕ} {P : Set (ℝ × ℝ)} {S : Fin n → ℝ × ℝ}
    {w : Finset (Fin n) → ℝ × ℝ}
    (hP : ShatteredSimplePolygon P S w)
    {ia ib ic : Fin n} (_hab : ia ≠ ib) (_hbc : ib ≠ ic) (_hac : ia ≠ ic)
    {W' : Set (ℝ × ℝ)} (hW'_sub : W' ⊆ WitnessSet {ib, ic} ∅ w)
    (U : OpenWedge) (hUy : U.y = S ia)
    (hU_sep : ∀ z : ℝ × ℝ, U.MemOpen z →
      orient2D (S ia) z (S ib) * orient2D (S ia) z (S ic) < 0)
    (hX_in_U : ∀ x ∈ W', Sees P x (S ia) → U.MemOpen x) :
    ∃ R : OpenWedge, R.y = S ia ∧ (∀ z : ℝ × ℝ, R.MemOpen z → U.MemOpen z) ∧
      IsWedgeTest P W' (S ia) R := by
  let a := S ia
  let b := S ib
  let c := S ic
  let W'_idx : Finset (Finset (Fin n)) := Finset.univ.filter (fun T => w T ∈ W')
  let X : Finset (Finset (Fin n)) := W'_idx.filter (fun T => ia ∈ T)
  have hW'_mem : ∀ x ∈ W', ∃ T ∈ W'_idx, x = w T ∧ ib ∈ T ∧ ic ∈ T := by
    intro x hx
    obtain ⟨T, hsub, _, rfl⟩ := hW'_sub hx
    exact ⟨T, Finset.mem_filter.mpr ⟨Finset.mem_univ T, hx⟩, rfl, hsub (by simp), hsub (by simp)⟩
  by_cases hX : X.Nonempty
  · let L₁ : ℝ × ℝ → ℝ := fun p => U.u₁.1 * (p.1 - a.1) + U.u₁.2 * (p.2 - a.2)
    let L₂ : ℝ × ℝ → ℝ := fun p => U.u₂.1 * (p.1 - a.1) + U.u₂.2 * (p.2 - a.2)
    let detU : ℝ := U.u₁.1 * U.u₂.2 - U.u₁.2 * U.u₂.1
    have hdetU : 0 < detU := U.h_nondeg
    have hL_orient : ∀ p q : ℝ × ℝ, L₁ p * L₂ q - L₂ p * L₁ q = detU * orient2D a p q := by
      intro p q; dsimp [L₁, L₂, detU, orient2D]; ring
    have hX_U : ∀ T ∈ X, U.MemOpen (w T) := by
      intro T hT
      have hTf := Finset.mem_filter.mp hT
      have hTidx := Finset.mem_filter.mp hTf.1
      exact hX_in_U (w T) hTidx.2 ((hP.shatters T ia).mpr hTf.2)
    have hX_L1_pos : ∀ T ∈ X, 0 < L₁ (w T) := by
      intro T hT; have hmem := hX_U T hT; dsimp [OpenWedge.MemOpen] at hmem; rw [hUy] at hmem; exact hmem.1
    have hX_L2_pos : ∀ T ∈ X, 0 < L₂ (w T) := by
      intro T hT; have hmem := hX_U T hT; dsimp [OpenWedge.MemOpen] at hmem; rw [hUy] at hmem; exact hmem.2
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
      dsimp [OpenWedge.MemOpen]; rw [hUy]
      refine ⟨by change 0 < L₁ u₁; rw [hu1_L1]; exact hL1_T1, ?_⟩
      change 0 < L₂ u₁; rw [hu1_L2]
      have h1 : δ₁ < L₂ (w T₁) / detU := lt_of_lt_of_le hδ1_lt (min_le_left _ _)
      have h2 := (lt_div_iff₀ hdetU).mp h1
      linarith
    have hu1_dist : dist u₁ (w T₁) < ε₁ := by
      rw [Prod.dist_eq]; simp only [Real.dist_eq]
      have hlt : δ₁ < ε₁ / (2 * Mv) := lt_of_lt_of_le hδ1_lt (min_le_right _ _)
      have h1 : |u₁.1 - (w T₁).1| < ε₁ := by
        have : u₁.1 - (w T₁).1 = -(δ₁ * v₂.1) := by dsimp [u₁]; ring
        rw [this, abs_neg, abs_mul, abs_of_pos hδ1_pos]
        have hv1 : |v₂.1| ≤ Mv := by have := abs_nonneg v₂.2; dsimp [Mv]; linarith
        calc δ₁ * |v₂.1| ≤ δ₁ * Mv := mul_le_mul_of_nonneg_left hv1 (le_of_lt hδ1_pos)
          _ < (ε₁ / (2 * Mv)) * Mv := mul_lt_mul_of_pos_right hlt hMv
          _ = ε₁ / 2 := by field_simp [ne_of_gt hMv]
          _ < ε₁ := by linarith
      have h2 : |u₁.2 - (w T₁).2| < ε₁ := by
        have : u₁.2 - (w T₁).2 = -(δ₁ * v₂.2) := by dsimp [u₁]; ring
        rw [this, abs_neg, abs_mul, abs_of_pos hδ1_pos]
        have hv2 : |v₂.2| ≤ Mv := by have := abs_nonneg v₂.1; dsimp [Mv]; linarith
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
          have hx : detU * ((w T).1 - a.1) = 0 := by dsimp [detU]; linear_combination U.u₂.2 * h1 - U.u₁.2 * h2
          have hy : detU * ((w T).2 - a.2) = 0 := by dsimp [detU]; linear_combination -U.u₂.1 * h1 + U.u₁.1 * h2
          have hx0 := (mul_eq_zero.mp hx).resolve_left hdet_ne
          have hy0 := (mul_eq_zero.mp hy).resolve_left hdet_ne
          ext <;> linarith
        exact hP.s_ne_w ia T hwa.symm
      · apply hδ1_nb; refine Finset.mem_image.mpr ⟨T, hT, ?_⟩
        have hden_ne : detU * L₁ (w T) ≠ 0 := mul_ne_zero (ne_of_gt hdetU) hL1T
        field_simp [hden_ne]; linarith
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
      dsimp [OpenWedge.MemOpen]; rw [hUy]
      refine ⟨by change 0 < L₁ u₂; rw [hu2_L1]; exact hL1_T2, ?_⟩
      change 0 < L₂ u₂; rw [hu2_L2]; nlinarith
    have hu2_dist : dist u₂ (w T₂) < ε₂ := by
      rw [Prod.dist_eq]; simp only [Real.dist_eq]
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
          have : L₂ (w T) * L₁ (w T₂) = 0 := by rw [hL1T] at hmul; linarith
          exact (mul_eq_zero.mp this).resolve_right (ne_of_gt hL1_T2)
        have hwa : w T = a := by
          have h1 : U.u₁.1 * ((w T).1 - a.1) + U.u₁.2 * ((w T).2 - a.2) = 0 := hL1T
          have h2 : U.u₂.1 * ((w T).1 - a.1) + U.u₂.2 * ((w T).2 - a.2) = 0 := hL2T_0
          have hdet_ne : detU ≠ 0 := ne_of_gt hdetU
          have hx : detU * ((w T).1 - a.1) = 0 := by dsimp [detU]; linear_combination U.u₂.2 * h1 - U.u₁.2 * h2
          have hy : detU * ((w T).2 - a.2) = 0 := by dsimp [detU]; linear_combination -U.u₂.1 * h1 + U.u₁.1 * h2
          have hx0 := (mul_eq_zero.mp hx).resolve_left hdet_ne
          have hy0 := (mul_eq_zero.mp hy).resolve_left hdet_ne
          ext <;> linarith
        exact hP.s_ne_w ia T hwa.symm
      · apply hδ2_nb; refine Finset.mem_image.mpr ⟨T, hT, ?_⟩
        have hden_ne : detU * L₁ (w T) ≠ 0 := mul_ne_zero (ne_of_gt hdetU) hL1T
        field_simp [hden_ne]; linarith
    have hu1_u2_pos : 0 < orient2D a u₁ u₂ := by
      have hT12 : L₂ (w T₁) * L₁ (w T₂) ≤ L₂ (w T₂) * L₁ (w T₁) := by
        have hle : r T₁ ≤ r T₂ := hT1_min T₂ hT2_mem; dsimp [r] at hle
        exact (div_le_div_iff₀ hL1_T1 hL1_T2).mp hle
      have hmul : 0 < detU * orient2D a u₁ u₂ := by
        rw [← hL_orient u₁ u₂, hu1_L1, hu1_L2, hu2_L1, hu2_L2]
        nlinarith [mul_pos hL1_T1 hdetU, mul_pos hL1_T2 hdetU]
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
      intro z; unfold OpenWedge.MemOpen orient2D; dsimp [R]
      constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨by linarith, by linarith⟩
    have hR_ext_iff : ∀ z : ℝ × ℝ, R.MemExt z ↔ orient2D a z u₂ < 0 ∨ orient2D a u₁ z < 0 := by
      intro z; unfold OpenWedge.MemExt orient2D; dsimp [R]
      constructor
      · rintro (h1 | h2)
        · left; linarith
        · right; linarith
      · rintro (h1 | h2)
        · left; linarith
        · right; linarith
    have hR_sub_U : ∀ z : ℝ × ℝ, R.MemOpen z → U.MemOpen z := by
      intro z hz; rw [hR_open_iff] at hz
      have hα : 0 < orient2D a z u₂ / orient2D a u₁ u₂ := div_pos hz.1 hu1_u2_pos
      have hβ : 0 < orient2D a u₁ z / orient2D a u₁ u₂ := div_pos hz.2 hu1_u2_pos
      have hd_ne' : orient2D a u₁ u₂ ≠ 0 := ne_of_gt hu1_u2_pos
      have hz1_num : orient2D a u₁ u₂ * (z.1 - a.1) =
          orient2D a z u₂ * (u₁.1 - a.1) + orient2D a u₁ z * (u₂.1 - a.1) := by
        unfold orient2D; ring
      have hz2_num : orient2D a u₁ u₂ * (z.2 - a.2) =
          orient2D a z u₂ * (u₁.2 - a.2) + orient2D a u₁ z * (u₂.2 - a.2) := by
        unfold orient2D; ring
      have hz1 : z.1 - a.1 = (orient2D a z u₂ / orient2D a u₁ u₂) * (u₁.1 - a.1) +
          (orient2D a u₁ z / orient2D a u₁ u₂) * (u₂.1 - a.1) := by
        rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, ← hz1_num,
          mul_div_cancel_left₀ _ hd_ne']
      have hz2 : z.2 - a.2 = (orient2D a z u₂ / orient2D a u₁ u₂) * (u₁.2 - a.2) +
          (orient2D a u₁ z / orient2D a u₁ u₂) * (u₂.2 - a.2) := by
        rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, ← hz2_num,
          mul_div_cancel_left₀ _ hd_ne']
      have hL1z : L₁ z = (orient2D a z u₂ / orient2D a u₁ u₂) * L₁ u₁ +
          (orient2D a u₁ z / orient2D a u₁ u₂) * L₁ u₂ := by dsimp [L₁]; rw [hz1, hz2]; ring
      have hL2z : L₂ z = (orient2D a z u₂ / orient2D a u₁ u₂) * L₂ u₁ +
          (orient2D a u₁ z / orient2D a u₁ u₂) * L₂ u₂ := by dsimp [L₂]; rw [hz1, hz2]; ring
      have hu1_L := hu1_in_U; have hu2_L := hu2_in_U
      dsimp [OpenWedge.MemOpen] at hu1_L hu2_L; rw [hUy] at hu1_L hu2_L
      dsimp [OpenWedge.MemOpen]; rw [hUy]
      exact ⟨by change 0 < L₁ z; rw [hL1z]; exact add_pos (mul_pos hα hu1_L.1) (mul_pos hβ hu2_L.1),
             by change 0 < L₂ z; rw [hL2z]; exact add_pos (mul_pos hα hu1_L.2) (mul_pos hβ hu2_L.2)⟩
    refine ⟨R, rfl, hR_sub_U, fun x hx => ?_⟩
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
        have hid1 : L₁ (w T₁) * L₂ (w T) - (L₂ (w T₁) - δ₁ * detU) * L₁ (w T) =
            (L₁ (w T₁) * L₂ (w T) - L₂ (w T₁) * L₁ (w T)) + δ₁ * detU * L₁ (w T) := by ring
        rw [hid1]
        exact add_pos_of_nonneg_of_pos (sub_nonneg.mpr (by linarith [hle1]))
          (mul_pos (mul_pos hδ1_pos hdetU) (hX_L1_pos T hTX))
      have hpos2 : 0 < detU * orient2D a (w T) u₂ := by
        rw [← hL_orient (w T) u₂, hu2_L1, hu2_L2]
        have hid2 : L₁ (w T) * (L₂ (w T₂) + δ₂ * detU) - L₂ (w T) * L₁ (w T₂) =
            (L₁ (w T) * L₂ (w T₂) - L₂ (w T) * L₁ (w T₂)) + δ₂ * detU * L₁ (w T) := by ring
        rw [hid2]
        exact add_pos_of_nonneg_of_pos (sub_nonneg.mpr (by linarith [hle2]))
          (mul_pos (mul_pos hδ2_pos hdetU) (hX_L1_pos T hTX))
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
      have hbc_ne : orient2D a (w T) b ≠ 0 := fun h0 => by rw [h0, zero_mul] at hsep; linarith
      rcases lt_or_gt_of_ne hbc_ne with hbc_lt | hbc_gt
      · have hc_pos : 0 < orient2D a (w T) c := by
          by_contra hc_le; push Not at hc_le
          have : 0 ≤ orient2D a (w T) b * orient2D a (w T) c :=
            mul_nonneg_of_nonpos_of_nonpos (le_of_lt hbc_lt) hc_le
          linarith
        exact sees_symm (two_path_enclosure_either hP.two_path_enclosure hax_ne
          (isPolygonalPathIn_four (sees_symm hu2_vis.1) hu2_vis.2.2 (sees_symm hxc))
          (isPolygonalPathIn_four (sees_symm hu1_vis.1) hu1_vis.2.1 (sees_symm hxb))
          (Or.inl ⟨interiorOnLeft_four hxu2 hc_pos, interiorOnRight_four hxu1 hbc_lt⟩))
      · have hc_neg : orient2D a (w T) c < 0 := by
          by_contra hc_ge; push Not at hc_ge
          have : 0 ≤ orient2D a (w T) b * orient2D a (w T) c := mul_nonneg (le_of_lt hbc_gt) hc_ge
          linarith
        exact sees_symm (two_path_enclosure_either hP.two_path_enclosure hax_ne
          (isPolygonalPathIn_four (sees_symm hu2_vis.1) hu2_vis.2.1 (sees_symm hxb))
          (isPolygonalPathIn_four (sees_symm hu1_vis.1) hu1_vis.2.2 (sees_symm hxc))
          (Or.inl ⟨interiorOnLeft_four hxu2 hbc_gt, interiorOnRight_four hxu1 hc_neg⟩))
  · have hX_empty : ∀ T ∈ W'_idx, ia ∉ T := fun T hT hia => hX ⟨T, Finset.mem_filter.mpr ⟨hT, hia⟩⟩
    let L₁ : ℝ × ℝ → ℝ := fun p => U.u₁.1 * (p.1 - a.1) + U.u₁.2 * (p.2 - a.2)
    let L₂ : ℝ × ℝ → ℝ := fun p => U.u₂.1 * (p.1 - a.1) + U.u₂.2 * (p.2 - a.2)
    let detU : ℝ := U.u₁.1 * U.u₂.2 - U.u₁.2 * U.u₂.1
    have hdetU : 0 < detU := U.h_nondeg
    let badSlope : Finset ℝ := W'_idx.image (fun T => L₂ (w T) / L₁ (w T))
    obtain ⟨t, ht_pos, ht_nb⟩ : ∃ t : ℝ, 0 < t ∧ t ∉ badSlope := by
      obtain ⟨t, ht⟩ := (Set.Ioi_infinite (0 : ℝ)).sdiff badSlope.finite_toSet |>.nonempty
      exact ⟨t, ht.1, by simpa using ht.2⟩
    let W'_pos : Finset (Finset (Fin n)) := W'_idx.filter (fun T => 0 < L₁ (w T))
    let ε_min : ℝ := if hpos : W'_pos.Nonempty then
      (W'_pos.inf' hpos (fun T => |L₂ (w T) - t * L₁ (w T)| / L₁ (w T))) / 2
      else t / 2
    let ε : ℝ := min (t / 2) ε_min
    have hline_ne : ∀ T ∈ W'_idx, L₂ (w T) - t * L₁ (w T) ≠ 0 := by
      intro T hT h0
      by_cases hL1 : L₁ (w T) = 0
      · have hL2 : L₂ (w T) = 0 := by rw [hL1] at h0; linarith
        have hx : detU * ((w T).1 - a.1) = 0 := by dsimp [detU, L₁, L₂] at *; linear_combination U.u₂.2 * hL1 - U.u₁.2 * hL2
        have hy : detU * ((w T).2 - a.2) = 0 := by dsimp [detU, L₁, L₂] at *; linear_combination -U.u₂.1 * hL1 + U.u₁.1 * hL2
        have hdet_ne : detU ≠ 0 := ne_of_gt hdetU
        have hx0 := (mul_eq_zero.mp hx).resolve_left hdet_ne
        have hy0 := (mul_eq_zero.mp hy).resolve_left hdet_ne
        exact hP.s_ne_w ia T (by ext <;> linarith)
      · apply ht_nb; refine Finset.mem_image.mpr ⟨T, hT, ?_⟩
        field_simp [hL1]; linarith
    have hε_pos : 0 < ε := by
      apply lt_min (by linarith)
      dsimp [ε_min]; split_ifs with hpos
      · apply div_pos _ (by norm_num)
        rw [Finset.lt_inf'_iff]; intro T hT
        exact div_pos (abs_pos.mpr (hline_ne T (Finset.mem_filter.mp hT).1))
          (Finset.mem_filter.mp hT).2
      · linarith
    -- Build `R` as `(t + ε) L₁ p - L₂ p > 0 ∧ L₂ p - (t - ε) L₁ p > 0`:
    let R : OpenWedge :=
      { y := a
        u₁ := ((t + ε) * U.u₁.1 - U.u₂.1, (t + ε) * U.u₁.2 - U.u₂.2)
        u₂ := (U.u₂.1 - (t - ε) * U.u₁.1, U.u₂.2 - (t - ε) * U.u₁.2)
        h_nondeg := by
          have heq : ((t + ε) * U.u₁.1 - U.u₂.1) * (U.u₂.2 - (t - ε) * U.u₁.2) -
              ((t + ε) * U.u₁.2 - U.u₂.2) * (U.u₂.1 - (t - ε) * U.u₁.1) =
              2 * ε * detU := by dsimp [detU]; ring
          rw [heq]; positivity }
    have hR_sub_U : ∀ z : ℝ × ℝ, R.MemOpen z → U.MemOpen z := by
      intro z hz; dsimp [OpenWedge.MemOpen, R] at hz ⊢; rw [hUy]
      have h2 : 0 < (t + ε) * L₁ z - L₂ z := by dsimp [L₁, L₂]; linarith [hz.1]
      have h1 : 0 < L₂ z - (t - ε) * L₁ z := by dsimp [L₁, L₂]; linarith [hz.2]
      have h2ε : 0 < 2 * ε * L₁ z := by linarith
      have hL1z : 0 < L₁ z := pos_of_mul_pos_right h2ε (by linarith)
      have htε : 0 < t - ε := by linarith [min_le_left (t / 2) ε_min]
      have hL2z : 0 < L₂ z := lt_trans (mul_pos htε hL1z) (by linarith)
      exact ⟨hL1z, hL2z⟩
    refine ⟨R, rfl, hR_sub_U, fun x hx => ?_⟩
    obtain ⟨T, hTidx, rfl, _, _⟩ := hW'_mem x hx
    have hext : R.MemExt (w T) := by
      dsimp [OpenWedge.MemExt, R]
      have he1 : ((t + ε) * U.u₁.1 - U.u₂.1) * ((w T).1 - a.1) +
          ((t + ε) * U.u₁.2 - U.u₂.2) * ((w T).2 - a.2) = (t + ε) * L₁ (w T) - L₂ (w T) := by
        dsimp [L₁, L₂]; ring
      have he2 : (U.u₂.1 - (t - ε) * U.u₁.1) * ((w T).1 - a.1) +
          (U.u₂.2 - (t - ε) * U.u₁.2) * ((w T).2 - a.2) = L₂ (w T) - (t - ε) * L₁ (w T) := by
        dsimp [L₁, L₂]; ring
      rw [he1, he2]
      by_cases hgt : 0 < L₁ (w T)
      · have hTpos : T ∈ W'_pos := Finset.mem_filter.mpr ⟨hTidx, hgt⟩
        have hinf : 2 * ε ≤ |L₂ (w T) - t * L₁ (w T)| / L₁ (w T) := by
          have h1 : ε ≤ ε_min := min_le_right _ _
          have hle := Finset.inf'_le (fun T' => |L₂ (w T') - t * L₁ (w T')| / L₁ (w T')) hTpos
          dsimp [ε_min] at h1; rw [dif_pos ⟨T, hTpos⟩] at h1; linarith
        have hmul : 2 * ε * L₁ (w T) ≤ |L₂ (w T) - t * L₁ (w T)| := (le_div_iff₀ hgt).mp hinf
        have hstrict : ε * L₁ (w T) < |L₂ (w T) - t * L₁ (w T)| := by
          have : 0 < ε * L₁ (w T) := mul_pos hε_pos hgt; linarith
        rcases lt_abs.mp hstrict with hpos | hneg
        · left; linarith
        · right; linarith
      · have hle : L₁ (w T) ≤ 0 := not_lt.mp hgt
        by_contra hnot; push Not at hnot
        have hsum : ((t + ε) * L₁ (w T) - L₂ (w T)) + (L₂ (w T) - (t - ε) * L₁ (w T)) =
            2 * ε * L₁ (w T) := by ring
        have h2ε_ge : 0 ≤ 2 * ε * L₁ (w T) := by linarith [hnot.1, hnot.2]
        have h2ε_le : 2 * ε * L₁ (w T) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by linarith) hle
        have h2ε_eq : 2 * ε * L₁ (w T) = 0 := le_antisymm h2ε_le h2ε_ge
        have hL1_0 : L₁ (w T) = 0 := (mul_eq_zero.mp h2ε_eq).resolve_left (by linarith)
        have hL2_0 : L₂ (w T) = 0 := by
          have ha1 := hnot.1; have ha2 := hnot.2; rw [hL1_0] at ha1 ha2; linarith
        exact hline_ne T hTidx (by rw [hL1_0, hL2_0]; ring)
    refine ⟨Or.inr hext, ⟨fun hsees => ?_, fun hopen => ?_⟩⟩
    · exact False.elim (hX_empty T hTidx ((hP.shatters T ia).mp hsees))
    · have hU := hR_sub_U (w T) hopen
      dsimp [OpenWedge.MemOpen] at hU; rw [hUy] at hU
      rcases hext with h1 | h2
      · have : (t + ε) * L₁ (w T) - L₂ (w T) < 0 := by dsimp [L₁, L₂] at *; linarith
        dsimp [OpenWedge.MemOpen, R] at hopen; dsimp [L₁, L₂] at this; linarith [hopen.1]
      · have : L₂ (w T) - (t - ε) * L₁ (w T) < 0 := by dsimp [L₁, L₂] at *; linarith
        dsimp [OpenWedge.MemOpen, R] at hopen; dsimp [L₁, L₂] at this; linarith [hopen.2]

/-! ## Part 1: Lemma 11.1 (`two_sided_visibility_separation`) -/

/-- **Lemma 11.1 (Two-sided visibility separation, `upper_9.tex` lines 1492–1498)**:
    Let `d ∈ S`, `F' ⊆ S \ {d}`, and `x = w T_x ∈ W(F') \ W(F' ∪ {d})` be a witness that sees
    `F'` and misses `d`. If the line `ℓ(S d, x)` separates two points `u, v ∈ F'`, then
    `W(F' ∪ {d})` lies entirely in one open half-plane of `ℓ(S d, x)`. In particular,
    `x ∉ convexHull ℝ (W(F' ∪ {d}))`. -/
theorem two_sided_visibility_separation {n : ℕ} {P : Set (ℝ × ℝ)}
    {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ}
    (hP : ShatteredSimplePolygon P S w)
    {d : Fin n} {F' : Finset (Fin n)} (_hd_not : d ∉ F')
    {T_x : Finset (Fin n)} (hF'_Tx : F' ⊆ T_x) (hd_Tx : d ∉ T_x)
    {u v : Fin n} (hu : u ∈ F') (hv : v ∈ F')
    (hsep : orient2D (S d) (w T_x) (S u) * orient2D (S d) (w T_x) (S v) < 0) :
    ((∀ y ∈ WitnessSet (insert d F') ∅ w, 0 < orient2D (S d) (w T_x) y) ∨
     (∀ y ∈ WitnessSet (insert d F') ∅ w, orient2D (S d) (w T_x) y < 0)) ∧
    w T_x ∉ convexHull ℝ (WitnessSet (insert d F') ∅ w) := by
  let x := w T_x
  have hdx_ne : S d ≠ x := hP.s_ne_w d T_x
  have hno_col : ∀ y ∈ WitnessSet (insert d F') ∅ w, orient2D (S d) x y ≠ 0 := by
    intro y hy
    rcases hy with ⟨T_y, hsub_y, _, rfl⟩
    have hTx_ne_Ty : T_x ≠ T_y := fun heq => hd_Tx (heq ▸ hsub_y (Finset.mem_insert_self d F'))
    exact hP.no_three_collinear (S d) x (w T_y)
      (Or.inl ⟨d, rfl⟩) (Or.inr ⟨T_x, rfl⟩) (Or.inr ⟨T_y, rfl⟩)
      hdx_ne (hP.w_inj.ne hTx_ne_Ty) (hP.s_ne_w d T_y)
  have hus_pos_or_neg :
      (∃ a ∈ F', 0 < orient2D (S d) x (S a)) ∧ (∃ b ∈ F', orient2D (S d) x (S b) < 0) := by
    rcases lt_trichotomy (orient2D (S d) x (S u)) 0 with hu_neg | hu0 | hu_pos
    · have hv_pos : 0 < orient2D (S d) x (S v) := by nlinarith
      exact ⟨⟨v, hv, hv_pos⟩, ⟨u, hu, hu_neg⟩⟩
    · rw [hu0, zero_mul] at hsep; exact False.elim (lt_irrefl 0 hsep)
    · have hv_neg : orient2D (S d) x (S v) < 0 := by nlinarith
      exact ⟨⟨u, hu, hu_pos⟩, ⟨v, hv, hv_neg⟩⟩
  rcases hus_pos_or_neg with ⟨⟨a, haF, ha_pos⟩, ⟨b, hbF, hb_neg⟩⟩
  have h_one_side :
      (∀ y ∈ WitnessSet (insert d F') ∅ w, 0 < orient2D (S d) x y) ∨
      (∀ y ∈ WitnessSet (insert d F') ∅ w, orient2D (S d) x y < 0) := by
    by_contra hboth
    push Not at hboth
    rcases hboth with ⟨⟨y₁, hy1_mem, hy1_le⟩, ⟨y₂, hy2_mem, hy2_ge⟩⟩
    have hy1_neg : orient2D (S d) x y₁ < 0 := lt_of_le_of_ne hy1_le (hno_col y₁ hy1_mem)
    have hy2_pos : 0 < orient2D (S d) x y₂ := lt_of_le_of_ne hy2_ge (hno_col y₂ hy2_mem).symm
    rcases hy1_mem with ⟨T₁, hsub1, _, rfl⟩
    rcases hy2_mem with ⟨T₂, hsub2, _, rfl⟩
    have hxa : Sees P x (S a) := (hP.shatters T_x a).mpr (hF'_Tx haF)
    have hxb : Sees P x (S b) := (hP.shatters T_x b).mpr (hF'_Tx hbF)
    have hy1_b : Sees P (w T₁) (S b) := (hP.shatters T₁ b).mpr (hsub1 (Finset.mem_insert_of_mem hbF))
    have hy1_d : Sees P (w T₁) (S d) := (hP.shatters T₁ d).mpr (hsub1 (Finset.mem_insert_self d F'))
    have hy2_a : Sees P (w T₂) (S a) := (hP.shatters T₂ a).mpr (hsub2 (Finset.mem_insert_of_mem haF))
    have hy2_d : Sees P (w T₂) (S d) := (hP.shatters T₂ d).mpr (hsub2 (Finset.mem_insert_self d F'))
    have h_orient_flip : ∀ z : ℝ × ℝ, orient2D x (S d) z = -orient2D (S d) x z := by
      intro z; unfold orient2D; ring
    have hπ1 : IsPolygonalPathIn P x (S d) [x, S b, w T₁, S d] :=
      isPolygonalPathIn_four hxb (sees_symm hy1_b) hy1_d
    have hπ2 : IsPolygonalPathIn P x (S d) [x, S a, w T₂, S d] :=
      isPolygonalPathIn_four hxa (sees_symm hy2_a) hy2_d
    have hL1 : InteriorOnLeft x (S d) [x, S b, w T₁, S d] :=
      interiorOnLeft_four (by rw [h_orient_flip]; linarith) (by rw [h_orient_flip]; linarith)
    have hR2 : InteriorOnRight x (S d) [x, S a, w T₂, S d] :=
      interiorOnRight_four (by rw [h_orient_flip]; linarith) (by rw [h_orient_flip]; linarith)
    have hsees_xd : Sees P x (S d) := hP.two_path_enclosure x (S d) _ _ hdx_ne.symm hπ1 hπ2 hL1 hR2
    exact hd_Tx ((hP.shatters T_x d).mp hsees_xd)
  refine ⟨h_one_side, ?_⟩
  intro hmem
  have hzero : orient2D (S d) x x = 0 := orient2D_self_right (S d) x
  rcases h_one_side with hpos | hneg
  · let H : Set (ℝ × ℝ) := {z | 0 < orient2D (S d) x z}
    have hH_conv : Convex ℝ H := by
      intro p hp q hq α β hα hβ hαβ
      dsimp [H] at hp hq ⊢; unfold orient2D at hp hq ⊢
      have hid : ((x.1 - (S d).1) * ((α * p.2 + β * q.2) - (S d).2) -
            (x.2 - (S d).2) * ((α * p.1 + β * q.1) - (S d).1)) =
          α * ((x.1 - (S d).1) * (p.2 - (S d).2) - (x.2 - (S d).2) * (p.1 - (S d).1)) +
          β * ((x.1 - (S d).1) * (q.2 - (S d).2) - (x.2 - (S d).2) * (q.1 - (S d).1)) +
          (1 - (α + β)) * ((x.1 - (S d).1) * (-(S d).2) - (x.2 - (S d).2) * (-(S d).1)) := by ring
      change 0 < (x.1 - (S d).1) * ((α * p.2 + β * q.2) - (S d).2) -
          (x.2 - (S d).2) * ((α * p.1 + β * q.1) - (S d).1)
      rw [hid, hαβ, sub_self, zero_mul, add_zero]
      rcases eq_or_lt_of_le hα with rfl | hαp
      · have hβ1 : β = 1 := by linarith
        subst hβ1; simpa using hq
      · nlinarith
    have hx_mem : x ∈ H := convexHull_min hpos hH_conv hmem
    dsimp [H] at hx_mem
    linarith
  · let H : Set (ℝ × ℝ) := {z | orient2D (S d) x z < 0}
    have hH_conv : Convex ℝ H := by
      intro p hp q hq α β hα hβ hαβ
      dsimp [H] at hp hq ⊢; unfold orient2D at hp hq ⊢
      have hid : ((x.1 - (S d).1) * ((α * p.2 + β * q.2) - (S d).2) -
            (x.2 - (S d).2) * ((α * p.1 + β * q.1) - (S d).1)) =
          α * ((x.1 - (S d).1) * (p.2 - (S d).2) - (x.2 - (S d).2) * (p.1 - (S d).1)) +
          β * ((x.1 - (S d).1) * (q.2 - (S d).2) - (x.2 - (S d).2) * (q.1 - (S d).1)) +
          (1 - (α + β)) * ((x.1 - (S d).1) * (-(S d).2) - (x.2 - (S d).2) * (-(S d).1)) := by ring
      change (x.1 - (S d).1) * ((α * p.2 + β * q.2) - (S d).2) -
          (x.2 - (S d).2) * ((α * p.1 + β * q.1) - (S d).1) < 0
      rw [hid, hαβ, sub_self, zero_mul, add_zero]
      rcases eq_or_lt_of_le hα with rfl | hαp
      · have hβ1 : β = 1 := by linarith
        subst hβ1; simpa using hq
      · nlinarith
    have hx_mem : x ∈ H := convexHull_min hneg hH_conv hmem
    dsimp [H] at hx_mem
    linarith

/-! ## Part 2: Lemma 11.2 (`pentagon-cells` Parts (ii) & (iii)) -/

/-- Extreme hull vertices `B` of `S`. -/
def hullVertices {n : ℕ} (S : Fin n → ℝ × ℝ) : Finset (Fin n) :=
  Finset.univ.filter (fun i => S i ∉ convexHull ℝ (((Finset.univ.erase i).image S) : Set (ℝ × ℝ)))

/-- Directed counterclockwise boundary edge `(a, b)` of `conv C`. -/
def IsCCWEdge {n : ℕ} (S : Fin n → ℝ × ℝ) (C : Finset (Fin n)) (a b : Fin n) : Prop :=
  a ∈ C ∧ b ∈ C ∧ a ≠ b ∧ ∀ r ∈ C, r ≠ a → r ≠ b → 0 < orient2D (S a) (S b) (S r)

/-- Front vertex of `C` from `v`: both incident edges of `conv C` face `v`. -/
def IsFrontVertexOf {n : ℕ} (S : Fin n → ℝ × ℝ) (C : Finset (Fin n)) (f : Fin n) (v : ℝ × ℝ) : Prop :=
  f ∈ C ∧ ∀ a b : Fin n, IsCCWEdge S C a b → (a = f ∨ b = f) → orient2D (S a) (S b) v < 0

/-- Certified hull vertices `H ⊆ B`. -/
def certifiedVertices {n : ℕ} (S : Fin n → ℝ × ℝ) (w : Finset (Fin n) → ℝ × ℝ) : Finset (Fin n) :=
  let B := hullVertices S
  B.filter (fun f => ∃ T : Finset (Fin n), f ∉ T ∧
    (∀ b : Fin n, IsCCWEdge S B b f → b ∈ T) ∧
    (∀ c : Fin n, IsCCWEdge S B f c → c ∈ T) ∧
    IsFrontVertexOf S B f (w T))

/-- Any affine form that is non-negative on `hullVertices S` is non-negative on all of `S`. -/
lemma affine_nonneg_on_univ_of_hullVertices {n : ℕ} (S : Fin n → ℝ × ℝ)
    (h_inj : Function.Injective S) (a b c : ℝ) (hab : a ≠ 0 ∨ b ≠ 0)
    (hB : ∀ j ∈ hullVertices S, 0 ≤ a * (S j).1 + b * (S j).2 + c) :
    ∀ i : Fin n, 0 ≤ a * (S i).1 + b * (S i).2 + c := by
  intro i
  by_contra hlt
  have hne_u : (Finset.univ : Finset (Fin n)).Nonempty := ⟨i, Finset.mem_univ i⟩
  let L : Fin n → ℝ := fun k => a * (S k).1 + b * (S k).2 + c
  let Lp : Fin n → ℝ := fun k => -b * (S k).1 + a * (S k).2
  obtain ⟨k0, _, hk0_min⟩ := Finset.exists_min_image Finset.univ L hne_u
  have hk0_neg : L k0 < 0 := lt_of_le_of_lt (hk0_min i (Finset.mem_univ i)) (not_le.mp hlt)
  let Mmin : Finset (Fin n) := Finset.univ.filter (fun k => L k = L k0)
  have hMmin_ne : Mmin.Nonempty := ⟨k0, Finset.mem_filter.mpr ⟨Finset.mem_univ k0, rfl⟩⟩
  obtain ⟨i0, hi0_mem, hi0_min⟩ := Finset.exists_min_image Mmin Lp hMmin_ne
  have hi0_L : L i0 = L k0 := (Finset.mem_filter.mp hi0_mem).2
  have hi0_notB : i0 ∉ hullVertices S := fun hmem => by
    have hlt_i0 : L i0 < 0 := hi0_L ▸ hk0_neg
    exact not_le.mpr hlt_i0 (hB i0 hmem)
  have hi0_conv : S i0 ∈ convexHull ℝ (((Finset.univ.erase i0).image S) : Set (ℝ × ℝ)) := by
    by_contra hnot
    exact hi0_notB (Finset.mem_filter.mpr ⟨Finset.mem_univ i0, hnot⟩)
  rw [mem_convexHull_iff_exists_fintype] at hi0_conv
  rcases hi0_conv with ⟨ι, _, μ, pts, hμ_nn, hμ_sum, hpts_img, hsum_eq⟩
  have hL_ge : ∀ j : ι, L i0 ≤ a * (pts j).1 + b * (pts j).2 + c := by
    intro j
    rcases Finset.mem_image.mp (hpts_img j) with ⟨kj, _, hkj⟩
    rw [← hkj, hi0_L]
    exact hk0_min kj (Finset.mem_univ kj)
  have hx_sum : (∑ j : ι, μ j * (pts j).1) = (S i0).1 := by
    have := congrArg Prod.fst hsum_eq
    simpa [Prod.fst_sum, smul_eq_mul] using this
  have hy_sum : (∑ j : ι, μ j * (pts j).2) = (S i0).2 := by
    have := congrArg Prod.snd hsum_eq
    simpa [Prod.snd_sum, smul_eq_mul] using this
  have hL_sum : ∑ j : ι, μ j * (a * (pts j).1 + b * (pts j).2 + c) = L i0 := by
    have hs1 : (∑ j : ι, μ j * (a * (pts j).1)) = a * (∑ j : ι, μ j * (pts j).1) := by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun j _ => by ring)
    have hs2 : (∑ j : ι, μ j * (b * (pts j).2)) = b * (∑ j : ι, μ j * (pts j).2) := by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun j _ => by ring)
    have hs3 : (∑ j : ι, μ j * c) = c * (∑ j : ι, μ j) := by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun j _ => by ring)
    dsimp [L]
    calc ∑ j : ι, μ j * (a * (pts j).1 + b * (pts j).2 + c)
        = (∑ j : ι, μ j * (a * (pts j).1)) + (∑ j : ι, μ j * (b * (pts j).2)) + (∑ j : ι, μ j * c) := by
          simp only [mul_add, Finset.sum_add_distrib]
      _ = a * (∑ j : ι, μ j * (pts j).1) + b * (∑ j : ι, μ j * (pts j).2) + c * (∑ j : ι, μ j) := by
          rw [hs1, hs2, hs3]
      _ = a * (S i0).1 + b * (S i0).2 + c := by rw [hx_sum, hy_sum, hμ_sum, mul_one]
  have hL_eq_all : ∀ j : ι, μ j ≠ 0 → a * (pts j).1 + b * (pts j).2 + c = L i0 := by
    have hdiff : ∑ j : ι, μ j * ((a * (pts j).1 + b * (pts j).2 + c) - L i0) = 0 := by
      simp only [mul_sub, Finset.sum_sub_distrib, hL_sum, ← Finset.sum_mul, hμ_sum, one_mul, sub_self]
    have hnn : ∀ j ∈ (Finset.univ : Finset ι),
        0 ≤ μ j * ((a * (pts j).1 + b * (pts j).2 + c) - L i0) :=
      fun j _ => mul_nonneg (hμ_nn j) (sub_nonneg.mpr (hL_ge j))
    have hzero := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hdiff
    intro j hj_nz
    have hj0 := hzero j (Finset.mem_univ j)
    rcases mul_eq_zero.mp hj0 with hμ0 | hdiff0
    · exact False.elim (hj_nz hμ0)
    · linarith
  have hLp_sum : ∑ j : ι, μ j * (-b * (pts j).1 + a * (pts j).2) = Lp i0 := by
    have hs1 : (∑ j : ι, μ j * (-b * (pts j).1)) = -b * (∑ j : ι, μ j * (pts j).1) := by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun j _ => by ring)
    have hs2 : (∑ j : ι, μ j * (a * (pts j).2)) = a * (∑ j : ι, μ j * (pts j).2) := by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun j _ => by ring)
    dsimp [Lp]
    calc ∑ j : ι, μ j * (-b * (pts j).1 + a * (pts j).2)
        = (∑ j : ι, μ j * (-b * (pts j).1)) + (∑ j : ι, μ j * (a * (pts j).2)) := by
          simp only [mul_add, Finset.sum_add_distrib]
      _ = -b * (∑ j : ι, μ j * (pts j).1) + a * (∑ j : ι, μ j * (pts j).2) := by rw [hs1, hs2]
      _ = -b * (S i0).1 + a * (S i0).2 := by rw [hx_sum, hy_sum]
  have hLp_ge : ∀ j : ι, μ j ≠ 0 → Lp i0 ≤ -b * (pts j).1 + a * (pts j).2 := by
    intro j hj_nz
    rcases Finset.mem_image.mp (hpts_img j) with ⟨kj, _, hkj⟩
    rw [← hkj]
    apply hi0_min kj
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ kj, ?_⟩
    rw [← hi0_L]
    dsimp [L]
    rw [hkj]
    exact hL_eq_all j hj_nz
  have hLp_diff : ∑ j : ι, μ j * ((-b * (pts j).1 + a * (pts j).2) - Lp i0) = 0 := by
    simp only [mul_sub, Finset.sum_sub_distrib, hLp_sum, ← Finset.sum_mul, hμ_sum, one_mul, sub_self]
  have hLp_nn : ∀ j ∈ (Finset.univ : Finset ι),
      0 ≤ μ j * ((-b * (pts j).1 + a * (pts j).2) - Lp i0) := by
    intro j _
    by_cases hμ0 : μ j = 0
    · simp [hμ0]
    · exact mul_nonneg (hμ_nn j) (sub_nonneg.mpr (hLp_ge j hμ0))
  have hLp_zero := (Finset.sum_eq_zero_iff_of_nonneg hLp_nn).mp hLp_diff
  obtain ⟨j0, _, hj0_nz⟩ := Finset.exists_ne_zero_of_sum_ne_zero (hμ_sum ▸ one_ne_zero)
  have hj0_Lp : -b * (pts j0).1 + a * (pts j0).2 = Lp i0 := by
    have hj0 := hLp_zero j0 (Finset.mem_univ j0)
    rcases mul_eq_zero.mp hj0 with hμ0 | hdiff0
    · exact False.elim (hj0_nz hμ0)
    · linarith
  have hj0_L : a * (pts j0).1 + b * (pts j0).2 + c = L i0 := hL_eq_all j0 hj0_nz
  rcases Finset.mem_image.mp (hpts_img j0) with ⟨kj0, hkj0_erase, hkj0_eq⟩
  have hkj0_ne : kj0 ≠ i0 := (Finset.mem_erase.mp hkj0_erase).1
  have hdx : a * ((pts j0).1 - (S i0).1) + b * ((pts j0).2 - (S i0).2) = 0 := by
    dsimp [L] at hj0_L; linarith
  have hdy : -b * ((pts j0).1 - (S i0).1) + a * ((pts j0).2 - (S i0).2) = 0 := by
    dsimp [Lp] at hj0_Lp; linarith
  have hs : a ^ 2 + b ^ 2 ≠ 0 := by
    rcases hab with ha | hb
    · exact ne_of_gt (add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero ha) (sq_nonneg b))
    · exact ne_of_gt (add_pos_of_nonneg_of_pos (sq_nonneg a) (sq_pos_of_ne_zero hb))
  have h1 : (a ^ 2 + b ^ 2) * ((pts j0).1 - (S i0).1) = 0 := by linear_combination a * hdx - b * hdy
  have h2 : (a ^ 2 + b ^ 2) * ((pts j0).2 - (S i0).2) = 0 := by linear_combination b * hdx + a * hdy
  have hx_eq : (pts j0).1 = (S i0).1 := by
    have := (mul_eq_zero.mp h1).resolve_left hs; linarith
  have hy_eq : (pts j0).2 = (S i0).2 := by
    have := (mul_eq_zero.mp h2).resolve_left hs; linarith
  have hpts_eq : S kj0 = S i0 := by rw [hkj0_eq]; ext <;> [exact hx_eq; exact hy_eq]
  exact hkj0_ne (h_inj hpts_eq)

lemma orient2D_pos_of_hullVertices {n : ℕ} {P : Set (ℝ × ℝ)} {S : Fin n → ℝ × ℝ}
    {w : Finset (Fin n) → ℝ × ℝ} (hP : ShatteredSimplePolygon P S w)
    {p q : Fin n} (hpq : p ≠ q)
    (hB : ∀ j ∈ hullVertices S, 0 ≤ orient2D (S p) (S q) (S j)) :
    ∀ i : Fin n, i ≠ p → i ≠ q → 0 < orient2D (S p) (S q) (S i) := by
  have hab : -((S q).2 - (S p).2) ≠ 0 ∨ ((S q).1 - (S p).1) ≠ 0 := by
    by_contra h0; push Not at h0
    apply hpq; apply hP.s_inj
    ext <;> linarith [h0.1, h0.2]
  have hid : ∀ z : ℝ × ℝ, orient2D (S p) (S q) z =
      -((S q).2 - (S p).2) * z.1 + ((S q).1 - (S p).1) * z.2 +
      (((S q).2 - (S p).2) * (S p).1 - ((S q).1 - (S p).1) * (S p).2) := by
    intro z; unfold orient2D; ring
  have hall := affine_nonneg_on_univ_of_hullVertices S hP.s_inj
    (-((S q).2 - (S p).2)) ((S q).1 - (S p).1)
    (((S q).2 - (S p).2) * (S p).1 - ((S q).1 - (S p).1) * (S p).2) hab
    (fun j hj => by rw [← hid (S j)]; exact hB j hj)
  intro i hip hiq
  have hnn : 0 ≤ orient2D (S p) (S q) (S i) := by rw [hid (S i)]; exact hall i
  have hne : orient2D (S p) (S q) (S i) ≠ 0 :=
    hP.no_three_collinear (S p) (S q) (S i)
      (Or.inl ⟨p, rfl⟩) (Or.inl ⟨q, rfl⟩) (Or.inl ⟨i, rfl⟩)
      (hP.s_inj.ne hpq) (hP.s_inj.ne hiq.symm) (hP.s_inj.ne hip.symm)
  exact lt_of_le_of_ne hnn hne.symm

/-- **Lemma 11.2(ii), non-front half-plane part (`pentagon-cells` part (ii))**:
    If `d k ∈ hullVertices S \ certifiedVertices S w` and `T_x` sees `D \ {d k}` and misses `d k`,
    then `w T_x ∈ H_{k-1}^+ ∪ H_k^+`. -/
theorem pentagon_cells_nonfront {n : ℕ} {P : Set (ℝ × ℝ)}
    {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ}
    (hP : ShatteredSimplePolygon P S w)
    {d : Fin 5 → Fin n} (hd_inj : Function.Injective d)
    (hv : StrictConvexCCWPentagon (S ∘ d))
    (hD_B : Finset.univ.image d ⊆ hullVertices S)
    (k : Fin 5) (hk_notH : d k ∉ certifiedVertices S w)
    {T_x : Finset (Fin n)} (hTx_sub : (Finset.univ.image d).erase (d k) ⊆ T_x)
    (hk_not_Tx : d k ∉ T_x) :
    (pentagonEdgeHalfPlane (S ∘ d) hv (k - 1)).MemPos (w T_x) ∨
    (pentagonEdgeHalfPlane (S ∘ d) hv k).MemPos (w T_x) := by
  have hk_B : d k ∈ hullVertices S := hD_B (Finset.mem_image_of_mem d (Finset.mem_univ k))
  have hk1_B : d (k + 1) ∈ hullVertices S := hD_B (Finset.mem_image_of_mem d (Finset.mem_univ (k + 1)))
  have hkm1_B : d (k - 1) ∈ hullVertices S := hD_B (Finset.mem_image_of_mem d (Finset.mem_univ (k - 1)))
  by_contra hnot
  push Not at hnot
  rcases hnot with ⟨hn_prev, hn_curr⟩
  have h_km1_add1 : (k - 1 : Fin 5) + 1 = k := sub_add_cancel k 1
  have hkm1_ne_k_fin : k - 1 ≠ k := (by decide : ∀ x : Fin 5, x - 1 ≠ x) k
  have hk_ne_k1_fin : k ≠ k + 1 := (by decide : ∀ x : Fin 5, x ≠ x + 1) k
  have hkm1_ne_k1_fin : k - 1 ≠ k + 1 := (by decide : ∀ x : Fin 5, x - 1 ≠ x + 1) k
  have hk1_ne_k_fin : k + 1 ≠ k := (by decide : ∀ x : Fin 5, x + 1 ≠ x) k
  have hk1_ne_km1_fin : k + 1 ≠ k - 1 := (by decide : ∀ x : Fin 5, x + 1 ≠ x - 1) k
  have h_prev_ne : orient2D (S (d (k - 1))) (S (d k)) (w T_x) ≠ 0 := by
    refine hP.no_three_collinear _ _ _ (Or.inl ⟨d (k - 1), rfl⟩) (Or.inl ⟨d k, rfl⟩)
      (Or.inr ⟨T_x, rfl⟩) (hP.s_inj.ne (hd_inj.ne hkm1_ne_k_fin))
      (hP.s_ne_w (d k) T_x) (hP.s_ne_w (d (k - 1)) T_x)
  have h_curr_ne : orient2D (S (d k)) (S (d (k + 1))) (w T_x) ≠ 0 := by
    refine hP.no_three_collinear _ _ _ (Or.inl ⟨d k, rfl⟩) (Or.inl ⟨d (k + 1), rfl⟩)
      (Or.inr ⟨T_x, rfl⟩) (hP.s_inj.ne (hd_inj.ne hk_ne_k1_fin))
      (hP.s_ne_w (d (k + 1)) T_x) (hP.s_ne_w (d k) T_x)
  have h_prev_lt : orient2D (S (d (k - 1))) (S (d k)) (w T_x) < 0 := by
    dsimp [pentagonEdgeHalfPlane] at hn_prev
    rw [edgeHalfPlane_memPos_iff] at hn_prev
    change ¬ 0 < orient2D (S (d (k - 1))) (S (d ((k - 1) + 1))) (w T_x) at hn_prev
    rw [h_km1_add1] at hn_prev
    exact lt_of_le_of_ne (not_lt.mp hn_prev) h_prev_ne
  have h_curr_lt : orient2D (S (d k)) (S (d (k + 1))) (w T_x) < 0 := by
    dsimp [pentagonEdgeHalfPlane] at hn_curr
    rw [edgeHalfPlane_memPos_iff] at hn_curr
    exact lt_of_le_of_ne (not_lt.mp hn_curr) h_curr_ne
  have hccw_o : 0 < orient2D (S (d k)) (S (d (k + 1))) (S (d (k - 1))) :=
    hv.toPoly k (k - 1) hkm1_ne_k_fin hkm1_ne_k1_fin
  have hx_U : w T_x ∈ UCone (S (d k)) (S (d (k + 1))) (S (d (k - 1))) :=
    ((u_halfplanes hccw_o (w T_x)).1).mpr ⟨h_prev_lt, h_curr_lt⟩
  have hx_tri : InOpenTri (w T_x) (S (d (k + 1))) (S (d (k - 1))) (S (d k)) :=
    (mem_uCone_iff_inOpenTri _ _ _ _).mp hx_U
  let Tz : Finset (Fin n) := Finset.univ.erase (d k)
  have hk1_ne_k : d (k + 1) ≠ d k := hd_inj.ne hk1_ne_k_fin
  have hkm1_ne_k : d (k - 1) ≠ d k := hd_inj.ne hkm1_ne_k_fin
  have hk1_ne_km1 : d (k + 1) ≠ d (k - 1) := hd_inj.ne hk1_ne_km1_fin
  have hTz_U : w Tz ∈ UCone (S (d k)) (S (d (k + 1))) (S (d (k - 1))) := by
    by_cases hTT : T_x = Tz
    · rwa [← hTT]
    · refine cone_of_shattered hP ?_ ?_ ?_ hx_tri ?_ ?_ ?_ ?_ ?_
      · exact (hP.shatters T_x (d (k + 1))).mpr
          (hTx_sub (Finset.mem_erase.mpr ⟨hk1_ne_k, Finset.mem_image_of_mem d (Finset.mem_univ _)⟩))
      · exact (hP.shatters T_x (d (k - 1))).mpr
          (hTx_sub (Finset.mem_erase.mpr ⟨hkm1_ne_k, Finset.mem_image_of_mem d (Finset.mem_univ _)⟩))
      · exact fun hs => hk_not_Tx ((hP.shatters T_x (d k)).mp hs)
      · exact (hP.shatters Tz (d (k + 1))).mpr (Finset.mem_erase.mpr ⟨hk1_ne_k, Finset.mem_univ _⟩)
      · exact (hP.shatters Tz (d (k - 1))).mpr (Finset.mem_erase.mpr ⟨hkm1_ne_k, Finset.mem_univ _⟩)
      · exact hP.no_three_collinear _ _ _ (Or.inl ⟨d k, rfl⟩) (Or.inl ⟨d (k + 1), rfl⟩)
          (Or.inr ⟨Tz, rfl⟩) (hP.s_inj.ne hk1_ne_k.symm) (hP.s_ne_w (d (k + 1)) Tz) (hP.s_ne_w (d k) Tz)
      · exact hP.no_three_collinear _ _ _ (Or.inl ⟨d k, rfl⟩) (Or.inl ⟨d (k - 1), rfl⟩)
          (Or.inr ⟨Tz, rfl⟩) (hP.s_inj.ne hkm1_ne_k.symm) (hP.s_ne_w (d (k - 1)) Tz) (hP.s_ne_w (d k) Tz)
      · exact hP.no_three_collinear _ _ _ (Or.inr ⟨T_x, rfl⟩) (Or.inl ⟨d k, rfl⟩)
          (Or.inr ⟨Tz, rfl⟩) (hP.s_ne_w (d k) T_x).symm (hP.s_ne_w (d k) Tz) (hP.w_inj.ne hTT)
  obtain ⟨μ₁, μ₂, μ₃, hμ1, hμ2, hμ3, hμsum, hk_eq1, hk_eq2⟩ :=
    (mem_uCone_iff_inOpenTri _ _ _ _).mp hTz_U
  have hcert : d k ∈ certifiedVertices S w := by
    refine Finset.mem_filter.mpr ⟨hk_B, Tz, Finset.notMem_erase _ _, ?_, ?_, hk_B, ?_⟩
    · intro b hb; exact Finset.mem_erase.mpr ⟨hb.2.2.1, Finset.mem_univ _⟩
    · intro c hc; exact Finset.mem_erase.mpr ⟨hc.2.2.1.symm, Finset.mem_univ _⟩
    · intro a b hab heq
      have hcomb : orient2D (S a) (S b) (S (d k)) =
          μ₁ * orient2D (S a) (S b) (w Tz) +
          μ₂ * orient2D (S a) (S b) (S (d (k + 1))) +
          μ₃ * orient2D (S a) (S b) (S (d (k - 1))) := by
        unfold orient2D; rw [hk_eq1, hk_eq2]
        linear_combination ((S a).2 * (S b).1 - (S a).1 * (S b).2) * hμsum
      rcases heq with rfl | rfl
      · have h1_nn : 0 ≤ orient2D (S (d k)) (S b) (S (d (k + 1))) := by
          by_cases h : d (k + 1) = b
          · rw [h, orient2D_self_right]
          · exact le_of_lt (hab.2.2.2 _ hk1_B hk1_ne_k h)
        have h2_nn : 0 ≤ orient2D (S (d k)) (S b) (S (d (k - 1))) := by
          by_cases h : d (k - 1) = b
          · rw [h, orient2D_self_right]
          · exact le_of_lt (hab.2.2.2 _ hkm1_B hkm1_ne_k h)
        have h_strict : 0 < orient2D (S (d k)) (S b) (S (d (k + 1))) ∨
            0 < orient2D (S (d k)) (S b) (S (d (k - 1))) := by
          by_cases h : d (k + 1) = b
          · right; exact hab.2.2.2 _ hkm1_B hkm1_ne_k (fun he => hk1_ne_km1 (h.trans he.symm))
          · left; exact hab.2.2.2 _ hk1_B hk1_ne_k h
        have h0 : orient2D (S (d k)) (S b) (S (d k)) = 0 := orient2D_self_outer _ _
        rw [h0] at hcomb
        rcases h_strict with hs | hs <;> nlinarith
      · have h1_nn : 0 ≤ orient2D (S a) (S (d k)) (S (d (k + 1))) := by
          by_cases h : d (k + 1) = a
          · rw [h, orient2D_self_outer]
          · exact le_of_lt (hab.2.2.2 _ hk1_B h hk1_ne_k)
        have h2_nn : 0 ≤ orient2D (S a) (S (d k)) (S (d (k - 1))) := by
          by_cases h : d (k - 1) = a
          · rw [h, orient2D_self_outer]
          · exact le_of_lt (hab.2.2.2 _ hkm1_B h hkm1_ne_k)
        have h_strict : 0 < orient2D (S a) (S (d k)) (S (d (k + 1))) ∨
            0 < orient2D (S a) (S (d k)) (S (d (k - 1))) := by
          by_cases h : d (k + 1) = a
          · right; exact hab.2.2.2 _ hkm1_B (fun he => hk1_ne_km1 (h.trans he.symm)) hkm1_ne_k
          · left; exact hab.2.2.2 _ hk1_B h hk1_ne_k
        have h0 : orient2D (S a) (S (d k)) (S (d k)) = 0 := orient2D_self_right _ _
        rw [h0] at hcomb
        rcases h_strict with hs | hs <;> nlinarith
  exact hk_notH hcert

/-- **Lemma 11.2(ii), `conv(W(D))` XOR conditions (`pentagon-cells` part (ii))**:
    1. For any `k : Fin 5` with `d k ∉ certifiedVertices S w`, if `w T_x ∈ conv(W(D))`
       with `D \ {d k} ⊆ T_x` and `d k ∉ T_x`, then `w T_x ∈ H_{k-1}^+ ↔ w T_x ∉ H_k^+`.
    2. For `k = 1`, if `w T_x ∈ H_{02}^+ ∩ conv(W(D))` with `D \ {d 1} ⊆ T_x` and `d 1 ∉ T_x`,
       then `w T_x ∈ H_0^+ ↔ w T_x ∉ H_1^+`. -/
theorem pentagon_cells_xor_of_convexHull {n : ℕ} {P : Set (ℝ × ℝ)}
    {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ}
    (hP : ShatteredSimplePolygon P S w)
    {d : Fin 5 → Fin n} (hd_inj : Function.Injective d)
    (hv : StrictConvexCCWPentagon (S ∘ d))
    (hD_B : Finset.univ.image d ⊆ hullVertices S)
    (k : Fin 5) (hk_notH : d k ∉ certifiedVertices S w)
    {T_x : Finset (Fin n)} (hTx_sub : (Finset.univ.image d).erase (d k) ⊆ T_x)
    (hk_not_Tx : d k ∉ T_x)
    (hx_conv : w T_x ∈ convexHull ℝ (WitnessSet (Finset.univ.image d) ∅ w)) :
    (pentagonEdgeHalfPlane (S ∘ d) hv (k - 1)).MemPos (w T_x) ↔
    ¬ (pentagonEdgeHalfPlane (S ∘ d) hv k).MemPos (w T_x) := by
  let D := Finset.univ.image d
  have hkD : d k ∈ D := Finset.mem_image_of_mem d (Finset.mem_univ k)
  have hins : insert (d k) (D.erase (d k)) = D := Finset.insert_erase hkD
  constructor
  · intro hp_prev hp_curr
    dsimp [pentagonEdgeHalfPlane] at hp_prev hp_curr
    rw [edgeHalfPlane_memPos_iff] at hp_prev hp_curr
    have h_km1_add1 : (k - 1 : Fin 5) + 1 = k := sub_add_cancel k 1
    have hp_prev' : 0 < orient2D (S (d (k - 1))) (S (d k)) (w T_x) := by
      change 0 < orient2D (S (d (k - 1))) (S (d ((k - 1) + 1))) (w T_x) at hp_prev
      rwa [h_km1_add1] at hp_prev
    have hsep1 : 0 < orient2D (S (d k)) (w T_x) (S (d (k - 1))) := by
      rw [orient2D_cycle]; exact hp_prev'
    have hsep2 : orient2D (S (d k)) (w T_x) (S (d (k + 1))) < 0 := by
      rw [orient2D_swap23]; linarith
    have hsep : orient2D (S (d k)) (w T_x) (S (d (k - 1))) *
        orient2D (S (d k)) (w T_x) (S (d (k + 1))) < 0 :=
      mul_neg_of_pos_of_neg hsep1 hsep2
    have hkm1_ne_k : k - 1 ≠ k := (by decide : ∀ x : Fin 5, x - 1 ≠ x) k
    have hk1_ne_k : k + 1 ≠ k := (by decide : ∀ x : Fin 5, x + 1 ≠ x) k
    have hnot := (two_sided_visibility_separation hP (Finset.notMem_erase (d k) D)
      hTx_sub hk_not_Tx
      (Finset.mem_erase.mpr ⟨hd_inj.ne hkm1_ne_k,
        Finset.mem_image_of_mem d (Finset.mem_univ _)⟩)
      (Finset.mem_erase.mpr ⟨hd_inj.ne hk1_ne_k,
        Finset.mem_image_of_mem d (Finset.mem_univ _)⟩) hsep).2
    rw [hins] at hnot
    exact hnot hx_conv
  · intro hnot_curr
    exact (pentagon_cells_nonfront hP hd_inj hv hD_B k hk_notH hTx_sub hk_not_Tx).resolve_right hnot_curr

theorem pentagon_cells_xor1_H02 {n : ℕ} {P : Set (ℝ × ℝ)}
    {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ}
    (hP : ShatteredSimplePolygon P S w)
    {d : Fin 5 → Fin n} (hd_inj : Function.Injective d)
    (hv : StrictConvexCCWPentagon (S ∘ d))
    {T_x : Finset (Fin n)} (hTx_sub : (Finset.univ.image d).erase (d 1) ⊆ T_x)
    (h1_not_Tx : d 1 ∉ T_x)
    (hx_02 : (pentagonDiag02HalfPlane (S ∘ d) hv).MemPos (w T_x))
    (hx_conv : w T_x ∈ convexHull ℝ (WitnessSet (Finset.univ.image d) ∅ w)) :
    (pentagonEdgeHalfPlane (S ∘ d) hv 0).MemPos (w T_x) ↔
    ¬ (pentagonEdgeHalfPlane (S ∘ d) hv 1).MemPos (w T_x) := by
  let D := Finset.univ.image d
  have h1D : d 1 ∈ D := Finset.mem_image_of_mem d (Finset.mem_univ 1)
  have hins : insert (d 1) (D.erase (d 1)) = D := Finset.insert_erase h1D
  constructor
  · intro h0 h1
    dsimp [pentagonEdgeHalfPlane] at h0 h1
    rw [edgeHalfPlane_memPos_iff] at h0 h1
    have h0' : 0 < orient2D (S (d 0)) (S (d 1)) (w T_x) := by
      simpa using h0
    have h1' : 0 < orient2D (S (d 1)) (S (d 2)) (w T_x) := by
      simpa using h1
    have hsep1 : 0 < orient2D (S (d 1)) (w T_x) (S (d 0)) := by
      rw [orient2D_cycle]; exact h0'
    have hsep2 : orient2D (S (d 1)) (w T_x) (S (d 2)) < 0 := by
      rw [orient2D_swap23]; linarith
    have hnot := (two_sided_visibility_separation hP (Finset.notMem_erase (d 1) D)
      hTx_sub h1_not_Tx
      (Finset.mem_erase.mpr ⟨hd_inj.ne (by decide), Finset.mem_image_of_mem d (Finset.mem_univ 0)⟩)
      (Finset.mem_erase.mpr ⟨hd_inj.ne (by decide), Finset.mem_image_of_mem d (Finset.mem_univ 2)⟩)
      (mul_neg_of_pos_of_neg hsep1 hsep2)).2
    rw [hins] at hnot
    exact hnot hx_conv
  · intro hn1
    by_contra hn0
    exact (pentagon_halfplane_inclusions_planar (S ∘ d) hv (w T_x)).1 hx_02 hn0 hn1

/-- **Lemma 11.2(iii) core (`leaf93_pentagon_cells_certified_cone`)**:
    `U(h; p0, v0) ⊆ H^+(p0, v0) ∩ H^-(pr, pr_next)`. -/
theorem pentagon_cells_certified_cone
    (p0 v0 pr pr_next h x : ℝ × ℝ) (α0 α1 αx : ℝ)
    (hh_out : orient2D pr pr_next h < 0)
    (hp0_in : 0 ≤ orient2D pr pr_next p0)
    (hv0_in : 0 ≤ orient2D pr pr_next v0)
    (hh_pos : 0 < orient2D p0 v0 h)
    (hα0 : 0 < α0) (hα1 : 0 < α1) (hαx : 0 < αx)
    (hsum : α0 + α1 + αx = 1)
    (hx1 : h.1 = α0 * p0.1 + α1 * v0.1 + αx * x.1)
    (hx2 : h.2 = α0 * p0.2 + α1 * v0.2 + αx * x.2) :
    0 < orient2D p0 v0 x ∧ orient2D pr pr_next x < 0 := by
  have id_0v : orient2D p0 v0 h = αx * orient2D p0 v0 x := by
    delta orient2D; rw [hx1, hx2]
    linear_combination (p0.2 * v0.1 - p0.1 * v0.2) * hsum
  have id_rr : orient2D pr pr_next h =
      α0 * orient2D pr pr_next p0 + α1 * orient2D pr pr_next v0 + αx * orient2D pr pr_next x := by
    delta orient2D; rw [hx1, hx2]
    linear_combination (pr.2 * pr_next.1 - pr.1 * pr_next.2) * hsum
  exact ⟨by nlinarith, by nlinarith⟩

/-- **Lemma 11.2(iii), Regime 1 (`r_* ∈ {1, 2, 3, 4}`)**:
    `U(h; 0, 1) ⊆ H_0^+ ∩ H_{r_*}^-`. -/
theorem pentagon_cells_certified_cone_H0 {v : Fin 5 → ℝ × ℝ} (hv : StrictConvexCCWPentagon v)
    (rstar : Fin 5) (hr0 : rstar ≠ 0) {h : ℝ × ℝ}
    (hh_out : orient2D (v rstar) (v (rstar + 1)) h < 0)
    (hh_01 : 0 < orient2D (v 0) (v 1) h) :
    ∀ x ∈ UCone h (v 0) (v 1),
      (pentagonEdgeHalfPlane v hv 0).MemPos x ∧
      (pentagonEdgeHalfPlane v hv rstar).MemNeg x := by
  intro x hx
  rw [mem_uCone_iff_inOpenTri] at hx
  rcases hx with ⟨μx, μ0, μ1, hμx, hμ0, hμ1, hsum, hx1, hx2⟩
  have hp0_in : 0 ≤ orient2D (v rstar) (v (rstar + 1)) (v 0) := by
    by_cases h0r : (0 : Fin 5) = rstar
    · exact False.elim (hr0 h0r.symm)
    · by_cases h0r1 : (0 : Fin 5) = rstar + 1
      · rw [h0r1, orient2D_self_right]
      · exact le_of_lt (hv.toPoly rstar 0 h0r h0r1)
  have hv0_in : 0 ≤ orient2D (v rstar) (v (rstar + 1)) (v 1) := by
    by_cases h1r : (1 : Fin 5) = rstar
    · rw [← h1r, orient2D_self_outer]
    · by_cases h1r1 : (1 : Fin 5) = rstar + 1
      · rw [← h1r1, orient2D_self_right]
      · exact le_of_lt (hv.toPoly rstar 1 h1r h1r1)
  obtain ⟨hpos, hneg⟩ := pentagon_cells_certified_cone (v 0) (v 1) (v rstar) (v (rstar + 1)) h x
    μ0 μ1 μx hh_out hp0_in hv0_in hh_01 hμ0 hμ1 hμx (by linarith) (by linarith) (by linarith)
  dsimp [pentagonEdgeHalfPlane]
  rw [edgeHalfPlane_memPos_iff, edgeHalfPlane_memNeg_iff]
  exact ⟨by simpa using hpos, hneg⟩

/-- **Lemma 11.2(iii), Regime 2 (`r_* ∈ {2, 3, 4}`)**:
    `U(h; 0, 2) ⊆ H^+(0, 2) ∩ H_{r_*}^-`. -/
theorem pentagon_cells_certified_cone_H02 {v : Fin 5 → ℝ × ℝ} (hv : StrictConvexCCWPentagon v)
    (rstar : Fin 5) (hr0 : rstar ≠ 0) (hr1 : rstar ≠ 1) {h : ℝ × ℝ}
    (hh_out : orient2D (v rstar) (v (rstar + 1)) h < 0)
    (hh_02 : 0 < orient2D (v 0) (v 2) h) :
    ∀ x ∈ UCone h (v 0) (v 2),
      (pentagonDiag02HalfPlane v hv).MemPos x ∧
      (pentagonEdgeHalfPlane v hv rstar).MemNeg x := by
  intro x hx
  rw [mem_uCone_iff_inOpenTri] at hx
  rcases hx with ⟨μx, μ0, μ2, hμx, hμ0, hμ2, hsum, hx1, hx2⟩
  have hp0_in : 0 ≤ orient2D (v rstar) (v (rstar + 1)) (v 0) := by
    by_cases h0r : (0 : Fin 5) = rstar
    · exact False.elim (hr0 h0r.symm)
    · by_cases h0r1 : (0 : Fin 5) = rstar + 1
      · rw [h0r1, orient2D_self_right]
      · exact le_of_lt (hv.toPoly rstar 0 h0r h0r1)
  have hv0_in : 0 ≤ orient2D (v rstar) (v (rstar + 1)) (v 2) := by
    by_cases h2r : (2 : Fin 5) = rstar
    · rw [← h2r, orient2D_self_outer]
    · by_cases h2r1 : (2 : Fin 5) = rstar + 1
      · exact False.elim (hr1 ((by decide : ∀ x : Fin 5, (2 : Fin 5) = x + 1 → x = 1) rstar h2r1))
      · exact le_of_lt (hv.toPoly rstar 2 h2r h2r1)
  obtain ⟨hpos, hneg⟩ := pentagon_cells_certified_cone (v 0) (v 2) (v rstar) (v (rstar + 1)) h x
    μ0 μ2 μx hh_out hp0_in hv0_in hh_02 hμ0 hμ2 hμx (by linarith) (by linarith) (by linarith)
  dsimp [pentagonDiag02HalfPlane, pentagonEdgeHalfPlane]
  rw [edgeHalfPlane_memPos_iff, edgeHalfPlane_memNeg_iff]
  exact ⟨hpos, hneg⟩

/-! ## Part 3: Lemma 11.3 (`adjacent_ear_empty_and_chord_wedges`) -/

/-- Lemma 11.3(i) core (`leaf30_ear_mutual_exclusion`): mutual interior exclusion in `△(0, 1, 2)`. -/
theorem ear_triangle_mutual_exclusion
    (p0 p2 y0 y1 : ℝ × ℝ) (α0 α2 α1 : ℝ)
    (hα0 : 0 < α0) (hα2 : 0 < α2) (hα1 : 0 < α1) (hsum : α0 + α2 + α1 = 1)
    (hy0_1 : y0.1 = α0 * p0.1 + α2 * p2.1 + α1 * y1.1)
    (hy0_2 : y0.2 = α0 * p0.2 + α2 * p2.2 + α1 * y1.2)
    (h_neg : orient2D p0 p2 y0 < 0) :
    orient2D p0 p2 y1 < orient2D p0 p2 y0 ∧ orient2D p0 p2 y1 < 0 := by
  have hid : orient2D p0 p2 y0 = α1 * orient2D p0 p2 y1 := by
    unfold orient2D; rw [hy0_1, hy0_2]
    linear_combination (p0.2 * p2.1 - p0.1 * p2.2) * hsum
  have h1 : orient2D p0 p2 y1 < 0 := by nlinarith
  have h2 : orient2D p0 p2 y1 < orient2D p0 p2 y0 := by nlinarith
  exact ⟨h2, h1⟩

/-- Lemma 11.3(ii) core (`leaf94_adjacent_ear_empty_chord_triangle`):
    `△(w_D, 0, 1) ∩ H^+(0, 2) ⊆ △(w_D, 0, 2)` and `△(w_D, 1, 2) ∩ H^+(0, 2) ⊆ △(w_D, 0, 2)`. -/
theorem adjacent_ear_empty_chord_triangle
    (p0 p1 p2 wD y : ℝ × ℝ)
    (_h012 : 0 < orient2D p0 p1 p2)
    (hw01 : 0 < orient2D p0 p1 wD)
    (hw12 : 0 < orient2D p1 p2 wD)
    (hw02 : 0 < orient2D p0 p2 wD)
    (hy02 : 0 < orient2D p0 p2 y)
    (hy_fan : InOpenTri wD p0 p1 y ∨ InOpenTri wD p1 p2 y) :
    InOpenTri wD p0 p2 y := by
  have orient_of_inOpenTri : ∀ a b c z, 0 < orient2D a b c → InOpenTri a b c z →
      0 < orient2D a b z ∧ 0 < orient2D b c z ∧ 0 < orient2D c a z := by
    rintro a b c z hccw ⟨μ₁, μ₂, μ₃, h1, h2, h3, hs, hz1, hz2⟩
    have e1 : orient2D a b z = μ₃ * orient2D a b c := by
      unfold orient2D; rw [hz1, hz2]; linear_combination (a.2 * b.1 - a.1 * b.2) * hs
    have e2 : orient2D b c z = μ₁ * orient2D a b c := by
      unfold orient2D; rw [hz1, hz2]; linear_combination (b.2 * c.1 - b.1 * c.2) * hs
    have e3 : orient2D c a z = μ₂ * orient2D a b c := by
      unfold orient2D; rw [hz1, hz2]; linear_combination (c.2 * a.1 - c.1 * a.2) * hs
    exact ⟨mul_pos h3 hccw |>.trans_eq e1.symm, mul_pos h1 hccw |>.trans_eq e2.symm,
      mul_pos h2 hccw |>.trans_eq e3.symm⟩
  have of_orient : ∀ a b c z, 0 < orient2D a b c →
      0 < orient2D a b z → 0 < orient2D b c z → 0 < orient2D c a z → InOpenTri a b c z := by
    intro a b c z hccw hab hbc hca
    have hdet : orient2D a b c ≠ 0 := ne_of_gt hccw
    refine ⟨orient2D b c z / orient2D a b c, orient2D c a z / orient2D a b c,
      orient2D a b z / orient2D a b c, div_pos hbc hccw, div_pos hca hccw, div_pos hab hccw, ?_, ?_, ?_⟩
    · have hs : orient2D b c z + orient2D c a z + orient2D a b z = orient2D a b c := by
        unfold orient2D; ring
      rw [← add_div, ← add_div, hs, div_self hdet]
    · have hx : orient2D a b c * z.1 =
          orient2D b c z * a.1 + orient2D c a z * b.1 + orient2D a b z * c.1 := by
        unfold orient2D; ring
      rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, ← add_div,
        ← hx, mul_div_cancel_left₀ _ hdet]
    · have hy' : orient2D a b c * z.2 =
          orient2D b c z * a.2 + orient2D c a z * b.2 + orient2D a b z * c.2 := by
        unfold orient2D; ring
      rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, ← add_div,
        ← hy', mul_div_cancel_left₀ _ hdet]
  have hwp02 : 0 < orient2D wD p0 p2 := by rw [orient2D_cycle, orient2D_cycle]; exact hw02
  refine of_orient wD p0 p2 y hwp02 ?_ hy02 ?_
  · rcases hy_fan with hy01 | hy12
    · have hwp01 : 0 < orient2D wD p0 p1 := by rw [orient2D_cycle, orient2D_cycle]; exact hw01
      exact (orient_of_inOpenTri wD p0 p1 y hwp01 hy01).1
    · have hwp12 : 0 < orient2D wD p1 p2 := by rw [orient2D_cycle, orient2D_cycle]; exact hw12
      have ⟨hw1y, _, hy2w⟩ := orient_of_inOpenTri wD p1 p2 y hwp12 hy12
      have gp2 : orient2D p1 p2 wD * orient2D wD p0 y =
          orient2D p0 p1 wD * orient2D p2 wD y + orient2D p0 p2 wD * orient2D wD p1 y := by
        unfold orient2D; ring
      have hp2wy : 0 < orient2D p2 wD y := hy2w
      nlinarith
  · rcases hy_fan with hy01 | hy12
    · have hwp01 : 0 < orient2D wD p0 p1 := by rw [orient2D_cycle, orient2D_cycle]; exact hw01
      have ⟨hw0y, _, hp1wy⟩ := orient_of_inOpenTri wD p0 p1 y hwp01 hy01
      have gp1 : orient2D p0 p1 wD * orient2D p2 wD y =
          orient2D p0 p2 wD * orient2D p1 wD y + orient2D p1 p2 wD * orient2D wD p0 y := by
        unfold orient2D; ring
      have hp2wy : 0 < orient2D p2 wD y := by nlinarith
      exact hp2wy
    · have hwp12 : 0 < orient2D wD p1 p2 := by rw [orient2D_cycle, orient2D_cycle]; exact hw12
      exact (orient_of_inOpenTri wD p1 p2 y hwp12 hy12).2.2

private lemma inClosedTri_swap12 {a b c z : ℝ × ℝ} (h : InClosedTri a b c z) :
    InClosedTri b a c z := by
  rcases h with ⟨μ₁, μ₂, μ₃, h1, h2, h3, hs, hx, hy⟩
  exact ⟨μ₂, μ₁, μ₃, h2, h1, h3, by linarith, by linarith, by linarith⟩

private lemma inClosedTri_swap23 {a b c z : ℝ × ℝ} (h : InClosedTri a b c z) :
    InClosedTri a c b z := by
  rcases h with ⟨μ₁, μ₂, μ₃, h1, h2, h3, hs, hx, hy⟩
  exact ⟨μ₁, μ₃, μ₂, h1, h3, h2, by linarith, by linarith, by linarith⟩

private lemma inClosedTri_cycle {a b c z : ℝ × ℝ} (h : InClosedTri a b c z) :
    InClosedTri b c a z := by
  rcases h with ⟨μ₁, μ₂, μ₃, h1, h2, h3, hs, hx, hy⟩
  exact ⟨μ₂, μ₃, μ₁, h2, h3, h1, by linarith, by linarith, by linarith⟩

/-- **Lemma 11.3 (`adjacent_ear_empty_and_chord_wedges`, `upper_9.tex` lines 1529–1547)**:
    In Regime 2 (both `01` and `12` exit edges nonempty, with `O*(y0)` and `O*(y1)` localization),
    unconditionally:
    1. `△(0, 1, 2) ∩ M = ∅` and `∀ y ∈ M, 0 < orient2D (S (d 0)) (S (d 2)) (S y)`,
    2. `0 < orient2D (S (d 0)) (S (d 2)) (w D)`,
    3. `∀ y ∈ M, InOpenTri (w D) (S (d 0)) (S (d 2)) (S y)`,
    4. Every witness in `W({d 0, d 2})` lies in `⋂_{y ∈ M} U(y; 0, 2) ⊆ H^+(0, 2)`,
    5. Each `y ∈ M` admits an open convex wedge test `W_y ⊆ U(y; 0, 2)` with apex `S y` on `W({d 0, d 2})`. -/
theorem adjacent_ear_empty_and_chord_wedges {n : ℕ} {P : Set (ℝ × ℝ)}
    {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ}
    (hP : ShatteredSimplePolygon P S w)
    {d : Fin 5 → Fin n} (hd_inj : Function.Injective d)
    (hv : StrictConvexCCWPentagon (S ∘ d))
    (D M : Finset (Fin n)) (hD_eq : D = Finset.univ.image d) (hM_disj : Disjoint D M)
    (y0 y1 : Fin n) (hy0M : y0 ∈ M) (hy1M : y1 ∈ M) (hy01 : y0 ≠ y1)
    (hM_01 : ∀ y ∈ M, 0 < orient2D (S (d 0)) (S (d 1)) (S y))
    (hM_12 : ∀ y ∈ M, 0 < orient2D (S (d 1)) (S (d 2)) (S y))
    (hwD_01 : 0 < orient2D (S (d 0)) (S (d 1)) (w D))
    (hwD_12 : 0 < orient2D (S (d 1)) (S (d 2)) (w D))
    (hM_exit : ∀ y ∈ M, InOpenTri (w D) (S (d 0)) (S (d 1)) (S y) ∨
                        InOpenTri (w D) (S (d 1)) (S (d 2)) (S y))
    (hy0_loc : ∀ z ∈ M.erase y0,
      ¬ InClosedTri (S (d 0)) (S (d 1)) (S y0) (S z) ∧
      ¬ InClosedTri (S y0) (S (d 1)) (S (d 2)) (S z))
    (hy1_loc : ∀ z ∈ M.erase y1,
      ¬ InClosedTri (S (d 2)) (S (d 1)) (S y1) (S z) ∧
      ¬ InClosedTri (S y1) (S (d 1)) (S (d 0)) (S z)) :
    (∀ y ∈ M, ¬ InClosedTri (S (d 0)) (S (d 1)) (S (d 2)) (S y) ∧
              0 < orient2D (S (d 0)) (S (d 2)) (S y)) ∧
    0 < orient2D (S (d 0)) (S (d 2)) (w D) ∧
    (∀ y ∈ M, InOpenTri (w D) (S (d 0)) (S (d 2)) (S y)) ∧
    (∀ x ∈ WitnessSet {d 0, d 2} ∅ w,
      (pentagonDiag02HalfPlane (S ∘ d) hv).MemPos x ∧
      ∀ y ∈ M, x ∈ UCone (S y) (S (d 0)) (S (d 2))) ∧
    (∀ y ∈ M, ∃ W_y : OpenWedge, W_y.y = S y ∧
      (∀ z : ℝ × ℝ, W_y.MemOpen z →
        z ∈ UCone (S y) (S (d 0)) (S (d 2)) ∧
        (pentagonDiag02HalfPlane (S ∘ d) hv).MemPos z) ∧
      IsWedgeTest P (WitnessSet {d 0, d 2} ∅ w) (S y) W_y) := by
  have h012 : 0 < orient2D (S (d 0)) (S (d 1)) (S (d 2)) := hv 0 1 2 (by decide) (by decide)
  have hd0D : d 0 ∈ D := hD_eq ▸ Finset.mem_image_of_mem d (Finset.mem_univ 0)
  have hd1D : d 1 ∈ D := hD_eq ▸ Finset.mem_image_of_mem d (Finset.mem_univ 1)
  have hd2D : d 2 ∈ D := hD_eq ▸ Finset.mem_image_of_mem d (Finset.mem_univ 2)
  have h_not_D : ∀ y ∈ M, y ≠ d 0 ∧ y ≠ d 1 ∧ y ≠ d 2 := fun y hy =>
    ⟨fun h => Finset.disjoint_left.mp hM_disj (h ▸ hd0D) hy,
     fun h => Finset.disjoint_left.mp hM_disj (h ▸ hd1D) hy,
     fun h => Finset.disjoint_left.mp hM_disj (h ▸ hd2D) hy⟩
  have h02_ne : ∀ y ∈ M, orient2D (S (d 0)) (S (d 2)) (S y) ≠ 0 := by
    intro y hy
    have hnd := h_not_D y hy
    exact hP.no_three_collinear _ _ _ (Or.inl ⟨d 0, rfl⟩) (Or.inl ⟨d 2, rfl⟩) (Or.inl ⟨y, rfl⟩)
      (hP.s_inj.ne (hd_inj.ne (by decide))) (hP.s_inj.ne hnd.2.2.symm) (hP.s_inj.ne hnd.1.symm)
  have htri_iff : ∀ y ∈ M, InClosedTri (S (d 0)) (S (d 1)) (S (d 2)) (S y) ↔
      orient2D (S (d 0)) (S (d 2)) (S y) < 0 := by
    intro y hy
    constructor
    · rintro ⟨μ₁, μ₂, μ₃, h1, h2, h3, hs, hy1x, hy2x⟩
      have hid : orient2D (S (d 0)) (S (d 2)) (S y) = -μ₂ * orient2D (S (d 0)) (S (d 1)) (S (d 2)) := by
        unfold orient2D; rw [hy1x, hy2x]
        linear_combination ((S (d 0)).2 * (S (d 2)).1 - (S (d 0)).1 * (S (d 2)).2) * hs
      have hle : orient2D (S (d 0)) (S (d 2)) (S y) ≤ 0 := by nlinarith
      exact lt_of_le_of_ne hle (h02_ne y hy)
    · intro hneg
      have h20 : 0 < orient2D (S (d 2)) (S (d 0)) (S y) := by
        unfold orient2D at hneg ⊢; linarith
      have hsum : orient2D (S (d 1)) (S (d 2)) (S y) + orient2D (S (d 2)) (S (d 0)) (S y) +
          orient2D (S (d 0)) (S (d 1)) (S y) = orient2D (S (d 0)) (S (d 1)) (S (d 2)) := by
        unfold orient2D; ring
      have hy' : orient2D (S (d 0)) (S (d 1)) (S (d 2)) * (S y).2 =
          orient2D (S (d 1)) (S (d 2)) (S y) * (S (d 0)).2 +
          orient2D (S (d 2)) (S (d 0)) (S y) * (S (d 1)).2 +
          orient2D (S (d 0)) (S (d 1)) (S y) * (S (d 2)).2 := by unfold orient2D; ring
      have hdet : orient2D (S (d 0)) (S (d 1)) (S (d 2)) ≠ 0 := ne_of_gt h012
      refine ⟨orient2D (S (d 1)) (S (d 2)) (S y) / orient2D (S (d 0)) (S (d 1)) (S (d 2)),
        orient2D (S (d 2)) (S (d 0)) (S y) / orient2D (S (d 0)) (S (d 1)) (S (d 2)),
        orient2D (S (d 0)) (S (d 1)) (S y) / orient2D (S (d 0)) (S (d 1)) (S (d 2)),
        div_nonneg (le_of_lt (hM_12 y hy)) (le_of_lt h012),
        div_nonneg (le_of_lt h20) (le_of_lt h012),
        div_nonneg (le_of_lt (hM_01 y hy)) (le_of_lt h012), ?_, ?_, ?_⟩
      · rw [← add_div, ← add_div, hsum, div_self hdet]
      · rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, ← add_div]
        have hx' : orient2D (S (d 0)) (S (d 1)) (S (d 2)) * (S y).1 =
            orient2D (S (d 1)) (S (d 2)) (S y) * (S (d 0)).1 +
            orient2D (S (d 2)) (S (d 0)) (S y) * (S (d 1)).1 +
            orient2D (S (d 0)) (S (d 1)) (S y) * (S (d 2)).1 := by unfold orient2D; ring
        rw [← hx', mul_div_cancel_left₀ _ hdet]
      · rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, ← add_div,
          ← hy', mul_div_cancel_left₀ _ hdet]
  have hy0_pos : 0 < orient2D (S (d 0)) (S (d 2)) (S y0) := by
    by_contra hle
    have hy0_neg : orient2D (S (d 0)) (S (d 2)) (S y0) < 0 :=
      lt_of_le_of_ne (not_lt.mp hle) (h02_ne y0 hy0M)
    have hy0_tri : InClosedTri (S (d 0)) (S (d 2)) (S (d 1)) (S y0) :=
      inClosedTri_swap23 ((htri_iff y0 hy0M).mpr hy0_neg)
    have hy0_cov := triangle_three_piece_cover (S (d 1)) (S y1) (S (d 0)) (S (d 2)) (S y0) hy0_tri
    have hloc1 := hy1_loc y0 (Finset.mem_erase.mpr ⟨hy01, hy0M⟩)
    have hy0_021 : InClosedTri (S y1) (S (d 0)) (S (d 2)) (S y0) := by
      rcases hy0_cov with h | h | h
      · exact h
      · exact False.elim (hloc1.1 (inClosedTri_cycle h))
      · exact False.elim (hloc1.2 h)
    have hy0_open : InOpenTri (S (d 0)) (S (d 2)) (S y1) (S y0) := by
      refine inOpenTri_of_noncollinear_inClosedTri (inClosedTri_cycle hy0_021) ?_ ?_ ?_
      · have hnd := h_not_D y0 hy0M
        exact hP.no_three_collinear _ _ _ (Or.inl ⟨d 2, rfl⟩) (Or.inl ⟨y1, rfl⟩) (Or.inl ⟨y0, rfl⟩)
          (hP.s_inj.ne (h_not_D y1 hy1M).2.2.symm) (hP.s_inj.ne hy01.symm) (hP.s_inj.ne hnd.2.2.symm)
      · have hnd := h_not_D y0 hy0M
        exact hP.no_three_collinear _ _ _ (Or.inl ⟨y1, rfl⟩) (Or.inl ⟨d 0, rfl⟩) (Or.inl ⟨y0, rfl⟩)
          (hP.s_inj.ne (h_not_D y1 hy1M).1) (hP.s_inj.ne hnd.1.symm) (hP.s_inj.ne hy01.symm)
      · exact h02_ne y0 hy0M
    rcases hy0_open with ⟨α0, α2, α1, hα0, hα2, hα1, hsum, hx1, hx2⟩
    have hmut1 := ear_triangle_mutual_exclusion (S (d 0)) (S (d 2)) (S y0) (S y1)
      α0 α2 α1 hα0 hα2 hα1 hsum hx1 hx2 hy0_neg
    have hy1_tri : InClosedTri (S (d 0)) (S (d 2)) (S (d 1)) (S y1) :=
      inClosedTri_swap23 ((htri_iff y1 hy1M).mpr hmut1.2)
    have hy1_cov := triangle_three_piece_cover (S (d 1)) (S y0) (S (d 0)) (S (d 2)) (S y1) hy1_tri
    have hloc0 := hy0_loc y1 (Finset.mem_erase.mpr ⟨hy01.symm, hy1M⟩)
    have hy1_020 : InClosedTri (S y0) (S (d 0)) (S (d 2)) (S y1) := by
      rcases hy1_cov with h | h | h
      · exact h
      · exact False.elim (hloc0.2 (inClosedTri_swap23 h))
      · exact False.elim (hloc0.1 (inClosedTri_swap12 (inClosedTri_cycle h)))
    have hy1_open : InOpenTri (S (d 0)) (S (d 2)) (S y0) (S y1) := by
      refine inOpenTri_of_noncollinear_inClosedTri (inClosedTri_cycle hy1_020) ?_ ?_ ?_
      · have hnd := h_not_D y1 hy1M
        exact hP.no_three_collinear _ _ _ (Or.inl ⟨d 2, rfl⟩) (Or.inl ⟨y0, rfl⟩) (Or.inl ⟨y1, rfl⟩)
          (hP.s_inj.ne (h_not_D y0 hy0M).2.2.symm) (hP.s_inj.ne hy01) (hP.s_inj.ne hnd.2.2.symm)
      · have hnd := h_not_D y1 hy1M
        exact hP.no_three_collinear _ _ _ (Or.inl ⟨y0, rfl⟩) (Or.inl ⟨d 0, rfl⟩) (Or.inl ⟨y1, rfl⟩)
          (hP.s_inj.ne (h_not_D y0 hy0M).1) (hP.s_inj.ne hnd.1.symm) (hP.s_inj.ne hy01)
      · exact h02_ne y1 hy1M
    rcases hy1_open with ⟨β0, β2, β1, hβ0, hβ2, hβ1, hsum', hx1', hx2'⟩
    have hmut2 := ear_triangle_mutual_exclusion (S (d 0)) (S (d 2)) (S y1) (S y0)
      β0 β2 β1 hβ0 hβ2 hβ1 hsum' hx1' hx2' hmut1.2
    linarith [hmut1.1, hmut2.1]
  have hM_02_pos : ∀ y ∈ M, ¬ InClosedTri (S (d 0)) (S (d 1)) (S (d 2)) (S y) ∧
      0 < orient2D (S (d 0)) (S (d 2)) (S y) := by
    intro y hy
    have hy_pos : 0 < orient2D (S (d 0)) (S (d 2)) (S y) := by
      by_cases hy0 : y = y0
      · rwa [hy0]
      · by_contra hle
        have hy_neg : orient2D (S (d 0)) (S (d 2)) (S y) < 0 :=
          lt_of_le_of_ne (not_lt.mp hle) (h02_ne y hy)
        have hy_tri : InClosedTri (S (d 0)) (S (d 2)) (S (d 1)) (S y) :=
          inClosedTri_swap23 ((htri_iff y hy).mpr hy_neg)
        have hy_cov := triangle_three_piece_cover (S (d 1)) (S y0) (S (d 0)) (S (d 2)) (S y) hy_tri
        have hloc0 := hy0_loc y (Finset.mem_erase.mpr ⟨hy0, hy⟩)
        have hy_020 : InClosedTri (S y0) (S (d 0)) (S (d 2)) (S y) := by
          rcases hy_cov with h | h | h
          · exact h
          · exact False.elim (hloc0.2 (inClosedTri_swap23 h))
          · exact False.elim (hloc0.1 (inClosedTri_swap12 (inClosedTri_cycle h)))
        rcases hy_020 with ⟨μ₁, μ₂, μ₃, hm1, hm2, hm3, hs, hx1, hx2⟩
        have hid : orient2D (S (d 0)) (S (d 2)) (S y) =
            μ₁ * orient2D (S (d 0)) (S (d 2)) (S y0) := by
          unfold orient2D; rw [hx1, hx2]
          linear_combination ((S (d 0)).2 * (S (d 2)).1 - (S (d 0)).1 * (S (d 2)).2) * hs
        have : 0 ≤ orient2D (S (d 0)) (S (d 2)) (S y) := by rw [hid]; exact mul_nonneg hm1 (le_of_lt hy0_pos)
        linarith
    exact ⟨fun htri => absurd ((htri_iff y hy).mp htri) (not_lt.mpr (le_of_lt hy_pos)), hy_pos⟩
  have hwD_02 : 0 < orient2D (S (d 0)) (S (d 2)) (w D) := by
    by_contra hle
    have hwD_20 : 0 ≤ orient2D (S (d 2)) (S (d 0)) (w D) := by
      rw [orient2D_swap12]; linarith [not_lt.mp hle]
    have hwD_mem : w D ∈ convexHull ℝ ({S (d 0), S (d 1), S (d 2)} : Set (ℝ × ℝ)) := by
      rw [← inClosedTri_iff_mem_convexHull]
      have hsum : orient2D (S (d 1)) (S (d 2)) (w D) + orient2D (S (d 2)) (S (d 0)) (w D) +
          orient2D (S (d 0)) (S (d 1)) (w D) = orient2D (S (d 0)) (S (d 1)) (S (d 2)) := by
        unfold orient2D; ring
      have hdet : orient2D (S (d 0)) (S (d 1)) (S (d 2)) ≠ 0 := ne_of_gt h012
      refine ⟨orient2D (S (d 1)) (S (d 2)) (w D) / orient2D (S (d 0)) (S (d 1)) (S (d 2)),
        orient2D (S (d 2)) (S (d 0)) (w D) / orient2D (S (d 0)) (S (d 1)) (S (d 2)),
        orient2D (S (d 0)) (S (d 1)) (w D) / orient2D (S (d 0)) (S (d 1)) (S (d 2)),
        div_nonneg (le_of_lt hwD_12) (le_of_lt h012),
        div_nonneg hwD_20 (le_of_lt h012),
        div_nonneg (le_of_lt hwD_01) (le_of_lt h012), ?_, ?_, ?_⟩
      · rw [← add_div, ← add_div, hsum, div_self hdet]
      · have hx' : orient2D (S (d 0)) (S (d 1)) (S (d 2)) * (w D).1 =
            orient2D (S (d 1)) (S (d 2)) (w D) * (S (d 0)).1 +
            orient2D (S (d 2)) (S (d 0)) (w D) * (S (d 1)).1 +
            orient2D (S (d 0)) (S (d 1)) (w D) * (S (d 2)).1 := by unfold orient2D; ring
        rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, ← add_div,
          ← hx', mul_div_cancel_left₀ _ hdet]
      · have hy' : orient2D (S (d 0)) (S (d 1)) (S (d 2)) * (w D).2 =
            orient2D (S (d 1)) (S (d 2)) (w D) * (S (d 0)).2 +
            orient2D (S (d 2)) (S (d 0)) (w D) * (S (d 1)).2 +
            orient2D (S (d 0)) (S (d 1)) (w D) * (S (d 2)).2 := by unfold orient2D; ring
        rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, ← add_div,
          ← hy', mul_div_cancel_left₀ _ hdet]
    have hy0_conv : S y0 ∈ convexHull ℝ ({S (d 0), S (d 1), S (d 2)} : Set (ℝ × ℝ)) := by
      rcases hM_exit y0 hy0M with h | h
      · refine convexHull_min ?_ (convex_convexHull ℝ _) h.to_convexHull
        intro z hz; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
        rcases hz with rfl | rfl | rfl
        · exact hwD_mem
        · exact subset_convexHull ℝ _ (by simp)
        · exact subset_convexHull ℝ _ (by simp)
      · refine convexHull_min ?_ (convex_convexHull ℝ _) h.to_convexHull
        intro z hz; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
        rcases hz with rfl | rfl | rfl
        · exact hwD_mem
        · exact subset_convexHull ℝ _ (by simp)
        · exact subset_convexHull ℝ _ (by simp)
    rw [← inClosedTri_iff_mem_convexHull] at hy0_conv
    exact (hM_02_pos y0 hy0M).1 hy0_conv
  have hM_chord : ∀ y ∈ M, InOpenTri (w D) (S (d 0)) (S (d 2)) (S y) := by
    intro y hy
    exact adjacent_ear_empty_chord_triangle (S (d 0)) (S (d 1)) (S (d 2)) (w D) (S y)
      h012 hwD_01 hwD_12 hwD_02 (hM_02_pos y hy).2 (hM_exit y hy)
  have hW_sub : ∀ x ∈ WitnessSet {d 0, d 2} ∅ w,
      (pentagonDiag02HalfPlane (S ∘ d) hv).MemPos x ∧
      ∀ y ∈ M, x ∈ UCone (S y) (S (d 0)) (S (d 2)) := by
    intro x hx
    rcases hx with ⟨T, hT02, _, rfl⟩
    have hxU : ∀ y ∈ M, w T ∈ UCone (S y) (S (d 0)) (S (d 2)) := by
      intro y hy
      by_cases hTD : T = D
      · rw [hTD, mem_uCone_iff_inOpenTri]; exact hM_chord y hy
      · have hnd := h_not_D y hy
        refine cone_of_shattered hP ?_ ?_ ?_ (hM_chord y hy) ?_ ?_ ?_ ?_ ?_
        · exact (hP.shatters D (d 0)).mpr hd0D
        · exact (hP.shatters D (d 2)).mpr hd2D
        · exact fun hs => Finset.disjoint_left.mp hM_disj ((hP.shatters D y).mp hs) hy
        · exact (hP.shatters T (d 0)).mpr (hT02 (by simp))
        · exact (hP.shatters T (d 2)).mpr (hT02 (by simp))
        · exact hP.no_three_collinear _ _ _ (Or.inl ⟨y, rfl⟩) (Or.inl ⟨d 0, rfl⟩) (Or.inr ⟨T, rfl⟩)
            (hP.s_inj.ne hnd.1) (hP.s_ne_w (d 0) T) (hP.s_ne_w y T)
        · exact hP.no_three_collinear _ _ _ (Or.inl ⟨y, rfl⟩) (Or.inl ⟨d 2, rfl⟩) (Or.inr ⟨T, rfl⟩)
            (hP.s_inj.ne hnd.2.2) (hP.s_ne_w (d 2) T) (hP.s_ne_w y T)
        · exact hP.no_three_collinear _ _ _ (Or.inr ⟨D, rfl⟩) (Or.inl ⟨y, rfl⟩) (Or.inr ⟨T, rfl⟩)
            (hP.s_ne_w y D).symm (hP.s_ne_w y T) (hP.w_inj.ne (Ne.symm hTD))
    refine ⟨?_, hxU⟩
    have hy0U := hxU y0 hy0M
    have hccw : 0 < orient2D (S y0) (S (d 0)) (S (d 2)) := by
      rw [orient2D_cycle, orient2D_cycle]; exact (hM_02_pos y0 hy0M).2
    have hneg := (u_halfplanes hccw (w T)).2.2 hy0U
    dsimp [pentagonDiag02HalfPlane]
    rw [edgeHalfPlane_memPos_iff]
    rw [orient2D_swap12]; linarith
  have hM_wedges : ∀ y ∈ M, ∃ W_y : OpenWedge, W_y.y = S y ∧
      (∀ z : ℝ × ℝ, W_y.MemOpen z →
        z ∈ UCone (S y) (S (d 0)) (S (d 2)) ∧
        (pentagonDiag02HalfPlane (S ∘ d) hv).MemPos z) ∧
      IsWedgeTest P (WitnessSet {d 0, d 2} ∅ w) (S y) W_y := by
    intro y hy
    have hnd := h_not_D y hy
    have hccw : 0 < orient2D (S y) (S (d 0)) (S (d 2)) := by
      rw [orient2D_cycle, orient2D_cycle]; exact (hM_02_pos y hy).2
    let U := oppositeConeWedge (S y) (S (d 0)) (S (d 2)) hccw
    obtain ⟨R, hRy, hR_sub_U, hRtest⟩ := wedge_extraction hP hnd.1 (hd_inj.ne (by decide)) hnd.2.2
      (Set.Subset.rfl : WitnessSet {d 0, d 2} ∅ w ⊆ WitnessSet {d 0, d 2} ∅ w) U rfl
      (fun z hz => u_halfplanes_separates (ne_of_gt hccw) (((u_halfplanes hccw z).2.1).mpr hz))
      (fun x hx _ => ((u_halfplanes hccw x).2.1).mp ((hW_sub x hx).2 y hy))
    refine ⟨R, hRy, fun z hz => ?_, hRtest⟩
    have hzU : z ∈ UCone (S y) (S (d 0)) (S (d 2)) := ((u_halfplanes hccw z).2.1).mpr (hR_sub_U z hz)
    have hneg := (u_halfplanes hccw z).2.2 hzU
    dsimp [pentagonDiag02HalfPlane]
    rw [edgeHalfPlane_memPos_iff]
    exact ⟨hzU, by rw [orient2D_swap12]; linarith⟩
  exact ⟨hM_02_pos, hwD_02, hM_chord, hW_sub, hM_wedges⟩

/-- Regime 1 (`e(M) = {01}`) chord-wedge extraction counterpart of Lemma 11.3. -/
theorem exit01_chord_wedges {n : ℕ} {P : Set (ℝ × ℝ)}
    {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ}
    (hP : ShatteredSimplePolygon P S w)
    {d : Fin 5 → Fin n} (hd_inj : Function.Injective d)
    (hv : StrictConvexCCWPentagon (S ∘ d))
    (D M : Finset (Fin n)) (hD_eq : D = Finset.univ.image d) (hM_disj : Disjoint D M)
    (hM_ne : M.Nonempty)
    (hM_01 : ∀ y ∈ M, 0 < orient2D (S (d 0)) (S (d 1)) (S y))
    (hM_exit : ∀ y ∈ M, InOpenTri (w D) (S (d 0)) (S (d 1)) (S y)) :
    (∀ x ∈ WitnessSet {d 0, d 1} ∅ w,
      (pentagonEdgeHalfPlane (S ∘ d) hv 0).MemPos x ∧
      ∀ y ∈ M, x ∈ UCone (S y) (S (d 0)) (S (d 1))) ∧
    (∀ y ∈ M, ∃ W_y : OpenWedge, W_y.y = S y ∧
      (∀ z : ℝ × ℝ, W_y.MemOpen z →
        z ∈ UCone (S y) (S (d 0)) (S (d 1)) ∧
        (pentagonEdgeHalfPlane (S ∘ d) hv 0).MemPos z) ∧
      IsWedgeTest P (WitnessSet {d 0, d 1} ∅ w) (S y) W_y) := by
  have hd0D : d 0 ∈ D := hD_eq ▸ Finset.mem_image_of_mem d (Finset.mem_univ 0)
  have hd1D : d 1 ∈ D := hD_eq ▸ Finset.mem_image_of_mem d (Finset.mem_univ 1)
  have h_not_D : ∀ y ∈ M, y ≠ d 0 ∧ y ≠ d 1 := fun y hy =>
    ⟨fun h => Finset.disjoint_left.mp hM_disj (h ▸ hd0D) hy,
     fun h => Finset.disjoint_left.mp hM_disj (h ▸ hd1D) hy⟩
  have hW_sub : ∀ x ∈ WitnessSet {d 0, d 1} ∅ w,
      (pentagonEdgeHalfPlane (S ∘ d) hv 0).MemPos x ∧
      ∀ y ∈ M, x ∈ UCone (S y) (S (d 0)) (S (d 1)) := by
    intro x hx
    rcases hx with ⟨T, hT01, _, rfl⟩
    have hxU : ∀ y ∈ M, w T ∈ UCone (S y) (S (d 0)) (S (d 1)) := by
      intro y hy
      by_cases hTD : T = D
      · rw [hTD, mem_uCone_iff_inOpenTri]; exact hM_exit y hy
      · have hnd := h_not_D y hy
        refine cone_of_shattered hP ?_ ?_ ?_ (hM_exit y hy) ?_ ?_ ?_ ?_ ?_
        · exact (hP.shatters D (d 0)).mpr hd0D
        · exact (hP.shatters D (d 1)).mpr hd1D
        · exact fun hs => Finset.disjoint_left.mp hM_disj ((hP.shatters D y).mp hs) hy
        · exact (hP.shatters T (d 0)).mpr (hT01 (by simp))
        · exact (hP.shatters T (d 1)).mpr (hT01 (by simp))
        · exact hP.no_three_collinear _ _ _ (Or.inl ⟨y, rfl⟩) (Or.inl ⟨d 0, rfl⟩) (Or.inr ⟨T, rfl⟩)
            (hP.s_inj.ne hnd.1) (hP.s_ne_w (d 0) T) (hP.s_ne_w y T)
        · exact hP.no_three_collinear _ _ _ (Or.inl ⟨y, rfl⟩) (Or.inl ⟨d 1, rfl⟩) (Or.inr ⟨T, rfl⟩)
            (hP.s_inj.ne hnd.2) (hP.s_ne_w (d 1) T) (hP.s_ne_w y T)
        · exact hP.no_three_collinear _ _ _ (Or.inr ⟨D, rfl⟩) (Or.inl ⟨y, rfl⟩) (Or.inr ⟨T, rfl⟩)
            (hP.s_ne_w y D).symm (hP.s_ne_w y T) (hP.w_inj.ne (Ne.symm hTD))
    refine ⟨?_, hxU⟩
    obtain ⟨y0, hy0M⟩ := hM_ne
    have hy0U := hxU y0 hy0M
    have hccw : 0 < orient2D (S y0) (S (d 0)) (S (d 1)) := by
      rw [orient2D_cycle, orient2D_cycle]; exact hM_01 y0 hy0M
    have hneg := (u_halfplanes hccw (w T)).2.2 hy0U
    dsimp [pentagonEdgeHalfPlane]
    rw [edgeHalfPlane_memPos_iff]
    change 0 < orient2D (S (d 0)) (S (d 1)) (w T)
    rw [orient2D_swap12]; linarith
  have hM_wedges : ∀ y ∈ M, ∃ W_y : OpenWedge, W_y.y = S y ∧
      (∀ z : ℝ × ℝ, W_y.MemOpen z →
        z ∈ UCone (S y) (S (d 0)) (S (d 1)) ∧
        (pentagonEdgeHalfPlane (S ∘ d) hv 0).MemPos z) ∧
      IsWedgeTest P (WitnessSet {d 0, d 1} ∅ w) (S y) W_y := by
    intro y hy
    have hnd := h_not_D y hy
    have hccw : 0 < orient2D (S y) (S (d 0)) (S (d 1)) := by
      rw [orient2D_cycle, orient2D_cycle]; exact hM_01 y hy
    let U := oppositeConeWedge (S y) (S (d 0)) (S (d 1)) hccw
    obtain ⟨R, hRy, hR_sub_U, hRtest⟩ := wedge_extraction hP hnd.1 (hd_inj.ne (by decide)) hnd.2
      (Set.Subset.rfl : WitnessSet {d 0, d 1} ∅ w ⊆ WitnessSet {d 0, d 1} ∅ w) U rfl
      (fun z hz => u_halfplanes_separates (ne_of_gt hccw) (((u_halfplanes hccw z).2.1).mpr hz))
      (fun x hx _ => ((u_halfplanes hccw x).2.1).mp ((hW_sub x hx).2 y hy))
    refine ⟨R, hRy, fun z hz => ?_, hRtest⟩
    have hzU : z ∈ UCone (S y) (S (d 0)) (S (d 1)) := ((u_halfplanes hccw z).2.1).mpr (hR_sub_U z hz)
    have hneg := (u_halfplanes hccw z).2.2 hzU
    dsimp [pentagonEdgeHalfPlane]
    rw [edgeHalfPlane_memPos_iff]
    exact ⟨hzU, by change 0 < orient2D (S (d 0)) (S (d 1)) z; rw [orient2D_swap12]; linarith⟩
  exact ⟨hW_sub, hM_wedges⟩

/-! ## Part 4: Theorem 11.4 (`localized_pentagon_shattered_contradiction`) -/

private lemma exists_memNeg_in_R11111
    (W : Fin 5 → OpenWedge) (H : OpenHalfPlane)
    (z : ℝ × ℝ) (hz_open : ∀ i : Fin 5, (W i).MemOpen z) (hz_not : ¬ H.MemPos z) :
    ∃ z' : ℝ × ℝ, H.MemNeg z' ∧ ∀ i : Fin 5, (W i).MemOpen z' := by
  have hz_le : H.n.1 * z.1 + H.n.2 * z.2 + H.c ≤ 0 := not_lt.mp hz_not
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
  obtain ⟨ε, hε, hball⟩ := hopen z hz_open
  let denom : ℝ := |H.n.1| + |H.n.2| + 1
  have hdenom_pos : 0 < denom := by
    have h1 : 0 ≤ |H.n.1| := abs_nonneg _
    have h2 : 0 ≤ |H.n.2| := abs_nonneg _
    dsimp [denom]; linarith
  let δ : ℝ := ε / (2 * denom)
  have hδ_pos : 0 < δ := div_pos hε (by linarith)
  let z' : ℝ × ℝ := (z.1 - δ * H.n.1, z.2 - δ * H.n.2)
  have hz'_mem : z' ∈ Metric.ball z ε := by
    rw [Metric.mem_ball, Prod.dist_eq]; simp only [Real.dist_eq, z']
    have h1 : |(z.1 - δ * H.n.1) - z.1| < ε := by
      have heq : (z.1 - δ * H.n.1) - z.1 = -(δ * H.n.1) := by ring
      rw [heq, abs_neg, abs_mul, abs_of_pos hδ_pos]
      have hle : |H.n.1| ≤ denom := by have := abs_nonneg H.n.2; dsimp [denom]; linarith
      calc δ * |H.n.1| ≤ δ * denom := mul_le_mul_of_nonneg_left hle (le_of_lt hδ_pos)
        _ = ε / 2 := by dsimp [δ]; field_simp [ne_of_gt hdenom_pos]
        _ < ε := by linarith
    have h2 : |(z.2 - δ * H.n.2) - z.2| < ε := by
      have heq : (z.2 - δ * H.n.2) - z.2 = -(δ * H.n.2) := by ring
      rw [heq, abs_neg, abs_mul, abs_of_pos hδ_pos]
      have hle : |H.n.2| ≤ denom := by have := abs_nonneg H.n.1; dsimp [denom]; linarith
      calc δ * |H.n.2| ≤ δ * denom := mul_le_mul_of_nonneg_left hle (le_of_lt hδ_pos)
        _ = ε / 2 := by dsimp [δ]; field_simp [ne_of_gt hdenom_pos]
        _ < ε := by linarith
    exact max_lt h1 h2
  refine ⟨z', ?_, hball hz'_mem⟩
  dsimp [OpenHalfPlane.MemNeg, z']
  have hs : 0 < H.n.1 ^ 2 + H.n.2 ^ 2 := by
    rcases H.hn with h1 | h2
    · exact add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero h1) (sq_nonneg _)
    · exact add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_ne_zero h2)
  have heq : H.n.1 * (z.1 - δ * H.n.1) + H.n.2 * (z.2 - δ * H.n.2) + H.c =
      (H.n.1 * z.1 + H.n.2 * z.2 + H.c) - δ * (H.n.1 ^ 2 + H.n.2 ^ 2) := by ring
  rw [heq]; nlinarith

/-- Regime 2 planar instantiation of Section 11 (`no_ten_point_shattered_master_masked`
    with `isRegime2 = true`, dropping the unused `h_nonfront2` hypothesis of
    `pentagon_wedges_no_ten_shattered_planar` since `xk 2` is not in `K_0 = {1, 3, 4}`). -/
private theorem pentagon_wedges_no_ten_shattered_planar_regime2
    (h_thm1 : ∀ f : Fin 5 → VFunc, ¬ (∀ m : Fin 5 → Bool, ∃ q : ℝ × ℝ, RealizesVMask f m q))
    (h_caseA_orig :
      (∀ f : Fin 5 → VFunc, ¬ (∀ m : Fin 5 → Bool, ∃ p : ℝ × ℝ, RealizesVMask f m p)) →
      ∀ W : Fin 5 → OpenWedge,
        (∀ i : Fin 5, (W i).y.1 < 0 ∧ (W i).y.2 < 0) →
        (∀ i : Fin 5, (W i).MemOpen (0, 0)) →
        ¬ (∀ m : Fin 5 → Bool, ∃ p : ℝ × ℝ, (p.1 < 0 ∨ p.2 < 0) ∧ RealizesWedgeMask W m p))
    (v : Fin 5 → ℝ × ℝ) (hv : StrictConvexCCWPentagon v)
    (W : Fin 5 → OpenWedge)
    (xk : Fin 5 → (Fin 5 → Bool) → ℝ × ℝ)
    (hxk_mask : ∀ k m, RealizesWedgeMask W m (xk k m))
    (h_nonfront3 : ∀ m, (pentagonEdgeHalfPlane v hv 2).MemPos (xk 3 m) ∨
                        (pentagonEdgeHalfPlane v hv 3).MemPos (xk 3 m))
    (h_nonfront4 : ∀ m, (pentagonEdgeHalfPlane v hv 3).MemPos (xk 4 m) ∨
                        (pentagonEdgeHalfPlane v hv 4).MemPos (xk 4 m))
    (h_xor3 : (pentagonEdgeHalfPlane v hv 2).MemPos (xk 3 (fun _ => true)) ↔
              ¬ (pentagonEdgeHalfPlane v hv 3).MemPos (xk 3 (fun _ => true)))
    (h_xor4 : (pentagonEdgeHalfPlane v hv 3).MemPos (xk 4 (fun _ => true)) ↔
              ¬ (pentagonEdgeHalfPlane v hv 4).MemPos (xk 4 (fun _ => true)))
    (h_regime2 :
      (∀ k m, (pentagonDiag02HalfPlane v hv).MemPos (xk k m)) ∧
      (∀ z, (∀ i : Fin 5, (W i).MemOpen z) → (pentagonDiag02HalfPlane v hv).MemPos z) ∧
      ((pentagonEdgeHalfPlane v hv 0).MemPos (xk 1 (fun _ => true)) ↔
        ¬ (pentagonEdgeHalfPlane v hv 1).MemPos (xk 1 (fun _ => true))))
    (h_case :
      (∃ rstar : Fin 5, rstar ≠ 0 ∧ rstar ≠ 1 ∧
        (∀ k m, ¬ (pentagonEdgeHalfPlane v hv rstar).MemPos (xk k m)) ∧
        (∀ z, (∀ i : Fin 5, (W i).MemOpen z) → ¬ (pentagonEdgeHalfPlane v hv rstar).MemPos z)) ∨
      (∀ i r : Fin 5, (pentagonEdgeHalfPlane v hv r).MemPos (W i).y)) :
    False := by
  let H := pentagonEdgeHalfPlane v hv
  let H02 := pentagonDiag02HalfPlane v hv
  let R11111 : ℝ × ℝ → Prop := fun z => ∀ i : Fin 5, (W i).MemOpen z
  have hxk_R11111 : ∀ k, R11111 (xk k (fun _ => true)) := fun k i => by
    simpa using hxk_mask k (fun _ => true) i
  have h_inc := fun z => pentagon_halfplane_inclusions_planar v hv z
  have thm_v_sep : ∀ (r : Fin 5) (fam : (Fin 5 → Bool) → ℝ × ℝ),
      (∀ m, RealizesWedgeMask W m (fam m)) →
      (∀ m, (H r).MemPos (fam m)) → ∀ z, R11111 z → (H r).MemPos z := by
    intro r fam hfam_mask hfam z hz
    exact thm1_part2_general_halfplane h_thm1 W (H r)
      (fun m => ⟨fam m, hfam m, hfam_mask m⟩) z hz
  rcases h_regime2 with ⟨h02_xk, h02_R, h_xor1⟩
  rcases h_case with ⟨rstar, hr0, hr1, hr_xk, hr_R⟩ | h_apices
  · fin_cases rstar
    · exact hr0 rfl
    · exact hr1 rfl
    · have hx3_in_H3 : ∀ m, (H 3).MemPos (xk 3 m) := fun m =>
        (h_nonfront3 m).resolve_left (hr_xk 3 m)
      have hR_H3 := thm_v_sep 3 (xk 3) (hxk_mask 3) hx3_in_H3
      have h4_3 := hR_H3 (xk 4 (fun _ => true)) (hxk_R11111 4)
      have hn4 := h_xor4.mp h4_3
      exact (h_inc (xk 4 (fun _ => true))).2.2.2.2.2.2
        (h02_R _ (hxk_R11111 4)) (hr_R _ (hxk_R11111 4)) hn4 |>.2 h4_3
    · have hx3_in_H2 : ∀ m, (H 2).MemPos (xk 3 m) := fun m =>
        (h_nonfront3 m).resolve_right (hr_xk 3 m)
      have hx4_in_H4 : ∀ m, (H 4).MemPos (xk 4 m) := fun m =>
        (h_nonfront4 m).resolve_left (hr_xk 4 m)
      have hR_H2 := thm_v_sep 2 (xk 3) (hxk_mask 3) hx3_in_H2
      have hR_H4 := thm_v_sep 4 (xk 4) (hxk_mask 4) hx4_in_H4
      have hn3_1 := hr_R (xk 1 (fun _ => true)) (hxk_R11111 1)
      have h1_in_H1 : (H 1).MemPos (xk 1 (fun _ => true)) := by
        by_contra hn1
        exact ((h_inc _).2.2.2.2.1 (h02_R _ (hxk_R11111 1)) hn1 hn3_1).1
          (hR_H2 _ (hxk_R11111 1))
      have h1_in_H0 : (H 0).MemPos (xk 1 (fun _ => true)) := by
        by_contra hn0
        exact ((h_inc _).2.2.2.2.2.1 (h02_R _ (hxk_R11111 1)) hn0 hn3_1).2
          (hR_H4 _ (hxk_R11111 1))
      exact (h_xor1.mp h1_in_H0) h1_in_H1
    · have hx4_in_H3 : ∀ m, (H 3).MemPos (xk 4 m) := fun m =>
        (h_nonfront4 m).resolve_right (hr_xk 4 m)
      have hR_H3 := thm_v_sep 3 (xk 4) (hxk_mask 4) hx4_in_H3
      have h3_3 := hR_H3 (xk 3 (fun _ => true)) (hxk_R11111 3)
      have hn2 : ¬ (H 2).MemPos (xk 3 (fun _ => true)) := fun h2 => (h_xor3.mp h2) h3_3
      exact ((h_inc _).2.2.2.2.2.2 (h02_R _ (hxk_R11111 3)) hn2 (hr_R _ (hxk_R11111 3))).2 h3_3
  · have thm_L_obs : ∀ (a b : Fin 5) (fam : (Fin 5 → Bool) → ℝ × ℝ),
        (∀ m, RealizesWedgeMask W m (fam m)) →
        (∀ m, (H a).MemPos (fam m) ∨ (H b).MemPos (fam m)) →
        ∀ za zb, R11111 za → R11111 zb → ¬ (H a).MemPos za → ¬ (H b).MemPos zb → False := by
      intro a b fam hfam_mask hfam za zb hza hzb hna hnb
      obtain ⟨za', hza'_neg, hza'_open⟩ := exists_memNeg_in_R11111 W (H a) za hza hna
      obtain ⟨zb', hzb'_neg, hzb'_open⟩ := exists_memNeg_in_R11111 W (H b) zb hzb hnb
      exact five_wedges_two_halfplanes_general h_thm1 h_caseA_orig (H a) (H b) W
        (fun i => ⟨h_apices i a, h_apices i b⟩)
        ⟨za', hza'_neg, hza'_open⟩ ⟨zb', hzb'_neg, hzb'_open⟩
        (fun m => ⟨fam m, hfam m, hfam_mask m⟩)
    have hx3_24 : ∀ m, (H 2).MemPos (xk 3 m) ∨ (H 4).MemPos (xk 3 m) := by
      intro m
      by_cases h2 : (H 2).MemPos (xk 3 m)
      · exact Or.inl h2
      · right; by_contra h4
        exact h2 ((h_nonfront3 m).resolve_right
          ((h_inc _).2.2.2.2.2.2 (h02_xk 3 m) h2 h4).2)
    by_cases h3_2 : (H 2).MemPos (xk 3 (fun _ => true))
    · have hn3 := h_xor3.mp h3_2
      have hx3_13 : ∀ m, (H 1).MemPos (xk 3 m) ∨ (H 3).MemPos (xk 3 m) := by
        intro m
        by_cases h1 : (H 1).MemPos (xk 3 m)
        · exact Or.inl h1
        · right; by_contra h3
          have := (h_inc (xk 3 m)).2.2.2.2.1 (h02_xk 3 m) h1 h3
          rcases h_nonfront3 m with h2 | h3'
          · exact this.1 h2
          · exact h3 h3'
      have hx4_03 : ∀ m, (H 0).MemPos (xk 4 m) ∨ (H 3).MemPos (xk 4 m) := by
        intro m
        by_cases h0 : (H 0).MemPos (xk 4 m)
        · exact Or.inl h0
        · right; by_contra h3
          have := (h_inc (xk 4 m)).2.2.2.2.2.1 (h02_xk 4 m) h0 h3
          rcases h_nonfront4 m with h3' | h4
          · exact h3 h3'
          · exact this.2 h4
      by_cases h1_0 : (H 0).MemPos (xk 1 (fun _ => true))
      · exact thm_L_obs 1 3 (xk 3) (hxk_mask 3) hx3_13
          (xk 1 (fun _ => true)) (xk 3 (fun _ => true))
          (hxk_R11111 1) (hxk_R11111 3) (h_xor1.mp h1_0) hn3
      · exact thm_L_obs 0 3 (xk 4) (hxk_mask 4) hx4_03
          (xk 1 (fun _ => true)) (xk 3 (fun _ => true))
          (hxk_R11111 1) (hxk_R11111 3) h1_0 hn3
    · have hn4_3 : ¬ (H 3).MemPos (xk 4 (fun _ => true)) → False := fun hn3_4 =>
        thm_L_obs 2 3 (xk 3) (hxk_mask 3) h_nonfront3
          (xk 3 (fun _ => true)) (xk 4 (fun _ => true))
          (hxk_R11111 3) (hxk_R11111 4) h3_2 hn3_4
      have h4_3 : (H 3).MemPos (xk 4 (fun _ => true)) := by by_contra h; exact hn4_3 h
      exact thm_L_obs 2 4 (xk 3) (hxk_mask 3) hx3_24
        (xk 3 (fun _ => true)) (xk 4 (fun _ => true))
        (hxk_R11111 3) (hxk_R11111 4) h3_2 (h_xor4.mp h4_3)

private lemma strictConvexCCWPentagon_shift1 {v : Fin 5 → ℝ × ℝ} (hv : StrictConvexCCWPentagon v) :
    StrictConvexCCWPentagon (fun i => v (i + 1)) := by
  intro i j k hij hjk
  by_cases hk4 : k = 4
  · subst hk4
    have h0i : (0 : Fin 5) < i + 1 := by omega
    have hij' : i + 1 < j + 1 := by omega
    change 0 < orient2D (v (i + 1)) (v (j + 1)) (v 0)
    rw [orient2D_cycle]
    exact hv 0 (i + 1) (j + 1) h0i hij'
  · have hij' : i + 1 < j + 1 := by omega
    have hjk' : j + 1 < k + 1 := by omega
    exact hv (i + 1) (j + 1) (k + 1) hij' hjk'

private lemma finset_M_enum {M : Finset (Fin 10)} (hM_card : M.card = 5) :
    ∃ m_enum : Fin 5 → Fin 10, Function.Injective m_enum ∧ Finset.univ.image m_enum = M := by
  let e := M.equivFin
  refine ⟨fun i => (e.symm (i.cast hM_card.symm)).1, ?_, ?_⟩
  · intro i j hij
    have h1 : e.symm (i.cast hM_card.symm) = e.symm (j.cast hM_card.symm) := Subtype.ext hij
    have h2 : i.cast hM_card.symm = j.cast hM_card.symm := e.symm.injective h1
    exact Fin.ext (by simpa using congrArg Fin.val h2)
  · ext x; simp only [Finset.mem_image, Finset.mem_univ, true_and]; constructor
    · rintro ⟨i, rfl⟩; exact (e.symm _).2
    · intro hx; refine ⟨(e ⟨x, hx⟩).cast hM_card, ?_⟩
      simp

private lemma hullVertices_nonneg_edge {n : ℕ} {P : Set (ℝ × ℝ)} {S : Fin n → ℝ × ℝ}
    {w : Finset (Fin n) → ℝ × ℝ} (hP : ShatteredSimplePolygon P S w)
    {d : Fin 5 → Fin n} (hd_inj : Function.Injective d)
    (hv : StrictConvexCCWPentagon (S ∘ d))
    {D H : Finset (Fin n)} (hDB : D = hullVertices S \ H) (hD_eq : D = Finset.univ.image d)
    (i : Fin 5)
    (hH_edge : ∀ h ∈ H, 0 < orient2D (S (d i)) (S (d (i + 1))) (S h)) :
    ∀ x ∈ Finset.univ \ D, 0 < orient2D (S (d i)) (S (d (i + 1))) (S x) := by
  have hB_nn : ∀ b ∈ hullVertices S, 0 ≤ orient2D (S (d i)) (S (d (i + 1))) (S b) := by
    intro b hb
    by_cases hbH : b ∈ H
    · exact le_of_lt (hH_edge b hbH)
    · have hbD : b ∈ D := hDB ▸ Finset.mem_sdiff.mpr ⟨hb, hbH⟩
      rw [hD_eq] at hbD
      rcases Finset.mem_image.mp hbD with ⟨j, _, rfl⟩
      by_cases hji : j = i
      · subst hji; rw [orient2D_self_outer]
      · by_cases hji1 : j = i + 1
        · subst hji1; rw [orient2D_self_right]
        · exact le_of_lt (hv.toPoly i j hji hji1)
  have hpos := orient2D_pos_of_hullVertices hP (hd_inj.ne ((by decide : ∀ x : Fin 5, x ≠ x + 1) i)) hB_nn
  intro x hx
  have hxD : x ∉ D := (Finset.mem_sdiff.mp hx).2
  have hxi : x ≠ d i := fun h => hxD (h ▸ hD_eq ▸ Finset.mem_image_of_mem d (Finset.mem_univ i))
  have hxi1 : x ≠ d (i + 1) := fun h =>
    hxD (h ▸ hD_eq ▸ Finset.mem_image_of_mem d (Finset.mem_univ (i + 1)))
  exact hpos x hxi hxi1

private lemma localized_pentagon_regime1_contradiction
    (h_thm1 : ∀ f : Fin 5 → VFunc, ¬ (∀ m : Fin 5 → Bool, ∃ q : ℝ × ℝ, RealizesVMask f m q))
    (h_caseA_orig :
      (∀ f : Fin 5 → VFunc, ¬ (∀ m : Fin 5 → Bool, ∃ p : ℝ × ℝ, RealizesVMask f m p)) →
      ∀ W : Fin 5 → OpenWedge,
        (∀ i : Fin 5, (W i).y.1 < 0 ∧ (W i).y.2 < 0) →
        (∀ i : Fin 5, (W i).MemOpen (0, 0)) →
        ¬ (∀ m : Fin 5 → Bool, ∃ p : ℝ × ℝ, (p.1 < 0 ∨ p.2 < 0) ∧ RealizesWedgeMask W m p))
    {P : Set (ℝ × ℝ)} {S : Fin 10 → ℝ × ℝ} {w : Finset (Fin 10) → ℝ × ℝ}
    (hP : ShatteredSimplePolygon P S w)
    (d : Fin 5 → Fin 10) (hd_inj : Function.Injective d) (hv : StrictConvexCCWPentagon (S ∘ d))
    (hDB : Finset.univ.image d = hullVertices S \ certifiedVertices S w)
    (h_exit01 : ∀ y ∈ Finset.univ \ Finset.univ.image d,
      0 < orient2D (S (d 0)) (S (d 1)) (w (Finset.univ.image d)) ∧
      InOpenTri (w (Finset.univ.image d)) (S (d 0)) (S (d 1)) (S y))
    (h_H_arc : (certifiedVertices S w).Nonempty →
      ∃ rstar : Fin 5, rstar ≠ 0 ∧
        (∀ h ∈ certifiedVertices S w, orient2D (S (d rstar)) (S (d (rstar + 1))) (S h) < 0) ∧
        (∀ i : Fin 5, i ≠ rstar → ∀ h ∈ certifiedVertices S w,
          0 < orient2D (S (d i)) (S (d (i + 1))) (S h))) :
    False := by
  let D : Finset (Fin 10) := Finset.univ.image d
  let M : Finset (Fin 10) := Finset.univ \ D
  let B := hullVertices S
  let H := certifiedVertices S w
  have hD_B : D ⊆ B := by dsimp [D, B]; rw [hDB]; exact Finset.sdiff_subset
  have hD_card : D.card = 5 := by
    rw [Finset.card_image_of_injective Finset.univ hd_inj, Finset.card_fin]
  have hM_card : M.card = 5 := by
    dsimp [M]; rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_fin, hD_card]
  have hM_ne : M.Nonempty := Finset.card_pos.mp (by omega)
  have hM_disj : Disjoint D M := Finset.disjoint_left.mpr fun _ hx hm => (Finset.mem_sdiff.mp hm).2 hx
  have hM_01 : ∀ y ∈ M, 0 < orient2D (S (d 0)) (S (d 1)) (S y) := by
    by_cases hHne : H.Nonempty
    · obtain ⟨rstar, hr0, _, hH_pos⟩ := h_H_arc hHne
      exact hullVertices_nonneg_edge hP hd_inj hv hDB rfl 0 (hH_pos 0 hr0.symm)
    · have hH_empty : H = ∅ := Finset.not_nonempty_iff_eq_empty.mp hHne
      exact hullVertices_nonneg_edge hP hd_inj hv hDB rfl 0 (fun h hh => by change h ∈ H at hh; rw [hH_empty] at hh; simp at hh)
  obtain ⟨hW_sub, hM_wedges⟩ := exit01_chord_wedges hP hd_inj hv D M rfl hM_disj hM_ne hM_01
    (fun y hy => (h_exit01 y hy).2)
  obtain ⟨m_enum, hm_inj, hm_img⟩ := finset_M_enum hM_card
  have hm_mem : ∀ i : Fin 5, m_enum i ∈ M := fun i => hm_img ▸ Finset.mem_image_of_mem m_enum (Finset.mem_univ i)
  have h_wedges_ex : ∀ i : Fin 5, ∃ W_i : OpenWedge, W_i.y = S (m_enum i) ∧
      (∀ z : ℝ × ℝ, W_i.MemOpen z →
        z ∈ UCone (S (m_enum i)) (S (d 0)) (S (d 1)) ∧
        (pentagonEdgeHalfPlane (S ∘ d) hv 0).MemPos z) ∧
      IsWedgeTest P (WitnessSet {d 0, d 1} ∅ w) (S (m_enum i)) W_i :=
    fun i => hM_wedges (m_enum i) (hm_mem i)
  choose W hWy hW_U hW_test using h_wedges_ex
  let M_mask : (Fin 5 → Bool) → Finset (Fin 10) := fun mask =>
    (Finset.univ.filter (fun i : Fin 5 => mask i = true)).image m_enum
  have h_d_not_M : ∀ (k : Fin 5) (mask : Fin 5 → Bool), d k ∉ M_mask mask := by
    intro k mask hmem
    rcases Finset.mem_image.mp hmem with ⟨i, _, hi⟩
    exact Finset.disjoint_left.mp hM_disj (Finset.mem_image_of_mem d (Finset.mem_univ k)) (hi ▸ hm_mem i)
  let xk_T : Fin 5 → (Fin 5 → Bool) → Finset (Fin 10) := fun k mask =>
    if k = 2 ∨ k = 3 ∨ k = 4 then (D.erase (d k)) ∪ M_mask mask
    else (D.erase (d 3)) ∪ M_mask mask
  let xk : Fin 5 → (Fin 5 → Bool) → ℝ × ℝ := fun k mask => w (xk_T k mask)
  have hxk_in_W01 : ∀ k mask, xk k mask ∈ WitnessSet {d 0, d 1} ∅ w := by
    intro k mask
    refine ⟨xk_T k mask, ?_, Finset.disjoint_empty_right _, rfl⟩
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    dsimp [xk_T]
    split_ifs with hk
    · refine Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨?_, ?_⟩)
      · rcases hx with rfl | rfl <;> rcases hk with rfl | rfl | rfl <;> exact hd_inj.ne (by decide)
      · rcases hx with rfl | rfl <;> exact Finset.mem_image_of_mem d (Finset.mem_univ _)
    · refine Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨?_, ?_⟩)
      · rcases hx with rfl | rfl <;> exact hd_inj.ne (by decide)
      · rcases hx with rfl | rfl <;> exact Finset.mem_image_of_mem d (Finset.mem_univ _)
  have h_realizes : ∀ T : Finset (Fin 10), ∀ mask : Fin 5 → Bool,
      w T ∈ WitnessSet {d 0, d 1} ∅ w →
      (∀ i : Fin 5, m_enum i ∈ T ↔ mask i = true) →
      RealizesWedgeMask W mask (w T) := by
    intro T mask hwT him i
    have htest := hW_test i (w T) hwT
    have hsees := (hP.shatters T (m_enum i)).trans (him i)
    cases hmi : mask i
    · simp only [Bool.false_eq_true, ↓reduceIte]
      rcases htest.1 with ho | he
      · exfalso; have := hsees.mp (htest.2.mpr ho); simp [hmi] at this
      · exact he
    · simp only [↓reduceIte]
      exact htest.2.mp (hsees.mpr hmi)
  have hxk_mask : ∀ k mask, RealizesWedgeMask W mask (xk k mask) := by
    intro k mask
    refine h_realizes (xk_T k mask) mask (hxk_in_W01 k mask) (fun i => ?_)
    dsimp [xk_T, M_mask]
    split_ifs
    · simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_image, Finset.mem_filter,
        Finset.mem_univ, true_and]
      constructor
      · rintro (⟨_, hiD⟩ | ⟨j, hj, hji⟩)
        · exact False.elim (Finset.disjoint_left.mp hM_disj hiD (hm_mem i))
        · rwa [← hm_inj hji]
      · intro hmi; right; exact ⟨i, hmi, rfl⟩
    · simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_image, Finset.mem_filter,
        Finset.mem_univ, true_and]
      constructor
      · rintro (⟨_, hiD⟩ | ⟨j, hj, hji⟩)
        · exact False.elim (Finset.disjoint_left.mp hM_disj hiD (hm_mem i))
        · rwa [← hm_inj hji]
      · intro hmi; right; exact ⟨i, hmi, rfl⟩
  let pm : (Fin 5 → Bool) → ℝ × ℝ := fun mask => w (D ∪ M_mask mask)
  have hpm_mask : ∀ mask, RealizesWedgeMask W mask (pm mask) := by
    intro mask
    refine h_realizes (D ∪ M_mask mask) mask ⟨D ∪ M_mask mask, ?_, Finset.disjoint_empty_right _, rfl⟩
      (fun i => ?_)
    · intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> exact Finset.mem_union_left _ (Finset.mem_image_of_mem d (Finset.mem_univ _))
    · dsimp [M_mask]
      simp only [Finset.mem_union, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro (hiD | ⟨j, hj, hji⟩)
        · exact False.elim (Finset.disjoint_left.mp hM_disj hiD (hm_mem i))
        · rwa [← hm_inj hji]
      · intro hmi; right; exact ⟨i, hmi, rfl⟩
  have hR_in_conv : ∀ z : ℝ × ℝ, (∀ i : Fin 5, (W i).MemOpen z) →
      z ∈ convexHull ℝ (WitnessSet D ∅ w) := by
    intro z hz
    have hcz := thm1_part2_convexHull_containment h_thm1 W pm hpm_mask z hz
    refine convexHull_mono ?_ hcz
    rintro _ ⟨mask, rfl⟩
    exact ⟨D ∪ M_mask mask, Finset.subset_union_left, Finset.disjoint_empty_right _, rfl⟩
  have hk_nonfront : ∀ (k : Fin 5) (hk : k = 2 ∨ k = 3 ∨ k = 4) (mask : Fin 5 → Bool),
      (pentagonEdgeHalfPlane (S ∘ d) hv (k - 1)).MemPos (xk k mask) ∨
      (pentagonEdgeHalfPlane (S ∘ d) hv k).MemPos (xk k mask) := by
    intro k hk mask
    have hk_notH : d k ∉ H := fun h =>
      Finset.disjoint_left.mp (by rw [hDB]; exact Finset.sdiff_disjoint)
        (Finset.mem_image_of_mem d (Finset.mem_univ k)) h
    have hTx_sub : D.erase (d k) ⊆ xk_T k mask := by
      dsimp [xk_T]; rw [if_pos hk]; exact Finset.subset_union_left
    have hk_not_Tx : d k ∉ xk_T k mask := by
      dsimp [xk_T]; rw [if_pos hk]; simp [h_d_not_M k mask]
    exact pentagon_cells_nonfront hP hd_inj hv hD_B k hk_notH hTx_sub hk_not_Tx
  have hk_xor : ∀ (k : Fin 5) (hk : k = 2 ∨ k = 3 ∨ k = 4),
      (pentagonEdgeHalfPlane (S ∘ d) hv (k - 1)).MemPos (xk k (fun _ => true)) ↔
      ¬ (pentagonEdgeHalfPlane (S ∘ d) hv k).MemPos (xk k (fun _ => true)) := by
    intro k hk
    have hk_notH : d k ∉ H := fun h =>
      Finset.disjoint_left.mp (by rw [hDB]; exact Finset.sdiff_disjoint)
        (Finset.mem_image_of_mem d (Finset.mem_univ k)) h
    have hTx_sub : D.erase (d k) ⊆ xk_T k (fun _ => true) := by
      dsimp [xk_T]; rw [if_pos hk]; exact Finset.subset_union_left
    have hk_not_Tx : d k ∉ xk_T k (fun _ => true) := by
      dsimp [xk_T]; rw [if_pos hk]; simp [h_d_not_M k _]
    have hx_conv : xk k (fun _ => true) ∈ convexHull ℝ (WitnessSet D ∅ w) :=
      hR_in_conv _ (fun i => by simpa using hxk_mask k (fun _ => true) i)
    exact pentagon_cells_xor_of_convexHull hP hd_inj hv hD_B k hk_notH hTx_sub hk_not_Tx hx_conv
  refine pentagon_wedges_no_ten_shattered_planar h_thm1 h_caseA_orig false (S ∘ d) hv W xk
    hxk_mask
    (hk_nonfront 3 (Or.inr (Or.inl rfl)))
    (hk_nonfront 4 (Or.inr (Or.inr rfl)))
    (hk_nonfront 2 (Or.inl rfl))
    (hk_xor 3 (Or.inr (Or.inl rfl)))
    (hk_xor 4 (Or.inr (Or.inr rfl)))
    ?_ ?_
  · rw [if_pos rfl]
    refine ⟨fun k mask => (hW_sub _ (hxk_in_W01 k mask)).1,
      fun z hz => (hW_U 0 z (hz 0)).2, hk_xor 2 (Or.inl rfl)⟩
  · by_cases hHne : H.Nonempty
    · obtain ⟨rstar, hr0, hr_out, _⟩ := h_H_arc hHne
      obtain ⟨h_in_H, hhH⟩ := hHne
      have hhM : h_in_H ∈ M := by
        refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun hhD => ?_⟩
        dsimp [D] at hhD
        rw [hDB] at hhD
        exact (Finset.mem_sdiff.mp hhD).2 hhH
      have hh_01 : 0 < orient2D (S (d 0)) (S (d 1)) (S h_in_H) := hM_01 h_in_H hhM
      left
      refine ⟨rstar, hr0, fun h => False.elim (by cases h), ?_, ?_⟩
      · intro k mask
        have hkU := (hW_sub _ (hxk_in_W01 k mask)).2 h_in_H hhM
        have hneg := (pentagon_cells_certified_cone_H0 hv rstar hr0 (hr_out h_in_H hhH) hh_01 _ hkU).2
        dsimp [pentagonEdgeHalfPlane] at hneg ⊢
        rw [edgeHalfPlane_memPos_iff]; rw [edgeHalfPlane_memNeg_iff] at hneg; linarith
      · intro z hz
        have hh_img : h_in_H ∈ Finset.univ.image m_enum := by rwa [hm_img]
        obtain ⟨i_h, _, hi_eq⟩ := Finset.mem_image.mp hh_img
        have hzU : z ∈ UCone (S h_in_H) (S (d 0)) (S (d 1)) := by
          rw [← hi_eq]; exact (hW_U i_h z (hz i_h)).1
        have hneg := (pentagon_cells_certified_cone_H0 hv rstar hr0 (hr_out h_in_H hhH) hh_01 _ hzU).2
        dsimp [pentagonEdgeHalfPlane] at hneg ⊢
        rw [edgeHalfPlane_memPos_iff]; rw [edgeHalfPlane_memNeg_iff] at hneg; linarith
    · have hH_empty : H = ∅ := Finset.not_nonempty_iff_eq_empty.mp hHne
      right
      intro i r
      rw [hWy i]
      have hall_r : ∀ y ∈ M, 0 < orient2D (S (d r)) (S (d (r + 1))) (S y) :=
        hullVertices_nonneg_edge hP hd_inj hv hDB rfl r
          (fun h hh => by change h ∈ H at hh; rw [hH_empty] at hh; simp at hh)
      dsimp [pentagonEdgeHalfPlane]
      rw [edgeHalfPlane_memPos_iff]
      exact hall_r (m_enum i) (hm_mem i)

/-- **Theorem 11.4 (`localized_pentagon_shattered_contradiction`, `upper_9.tex` Theorem 11.4)**:
    Given `h_thm1`, `h_caseA_orig`, `ShatteredSimplePolygon P S w` (`n = 10`), and the Section 8.4
    adjacent-exit pentagon output (`D = {d_0..d_4}` strictly convex CCW pentagon, `M = S \ D` of
    size 5, `{e(y) : y ∈ M} ⊆ {01, 12}` with `O*(y_0)`/`O*(y_1)` localization in Regime 2 and
    `H` arc structure), derives `False` across both Regime 1 and Regime 2 and both Case 1 (`H ≠ ∅`)
    and Case 2 (`H = ∅`). -/
theorem localized_pentagon_shattered_contradiction
    (h_thm1 : ∀ f : Fin 5 → VFunc, ¬ (∀ m : Fin 5 → Bool, ∃ q : ℝ × ℝ, RealizesVMask f m q))
    (h_caseA_orig :
      (∀ f : Fin 5 → VFunc, ¬ (∀ m : Fin 5 → Bool, ∃ p : ℝ × ℝ, RealizesVMask f m p)) →
      ∀ W : Fin 5 → OpenWedge,
        (∀ i : Fin 5, (W i).y.1 < 0 ∧ (W i).y.2 < 0) →
        (∀ i : Fin 5, (W i).MemOpen (0, 0)) →
        ¬ (∀ m : Fin 5 → Bool, ∃ p : ℝ × ℝ, (p.1 < 0 ∨ p.2 < 0) ∧ RealizesWedgeMask W m p))
    {P : Set (ℝ × ℝ)} {S : Fin 10 → ℝ × ℝ} {w : Finset (Fin 10) → ℝ × ℝ}
    (hP : ShatteredSimplePolygon P S w)
    (d : Fin 5 → Fin 10) (hd_inj : Function.Injective d) (hv : StrictConvexCCWPentagon (S ∘ d))
    (hDB : Finset.univ.image d = hullVertices S \ certifiedVertices S w)
    (h_exit : ∀ y ∈ Finset.univ \ Finset.univ.image d,
      (0 < orient2D (S (d 0)) (S (d 1)) (w (Finset.univ.image d)) ∧
        InOpenTri (w (Finset.univ.image d)) (S (d 0)) (S (d 1)) (S y)) ∨
      (0 < orient2D (S (d 1)) (S (d 2)) (w (Finset.univ.image d)) ∧
        InOpenTri (w (Finset.univ.image d)) (S (d 1)) (S (d 2)) (S y)))
    (h_H_arc : (certifiedVertices S w).Nonempty →
      ∃ rstar : Fin 5,
        (∀ h ∈ certifiedVertices S w, orient2D (S (d rstar)) (S (d (rstar + 1))) (S h) < 0) ∧
        (∀ i : Fin 5, i ≠ rstar → ∀ h ∈ certifiedVertices S w,
          0 < orient2D (S (d i)) (S (d (i + 1))) (S h)) ∧
        (∀ y ∈ Finset.univ \ Finset.univ.image d,
          ¬ InOpenTri (w (Finset.univ.image d)) (S (d rstar)) (S (d (rstar + 1))) (S y)))
    (h_reg2_loc :
      (∃ y ∈ Finset.univ \ Finset.univ.image d,
        InOpenTri (w (Finset.univ.image d)) (S (d 0)) (S (d 1)) (S y)) →
      (∃ y ∈ Finset.univ \ Finset.univ.image d,
        InOpenTri (w (Finset.univ.image d)) (S (d 1)) (S (d 2)) (S y)) →
      ∃ y0 ∈ Finset.univ \ Finset.univ.image d,
        ∃ y1 ∈ Finset.univ \ Finset.univ.image d,
          y0 ≠ y1 ∧
          InOpenTri (w (Finset.univ.image d)) (S (d 0)) (S (d 1)) (S y0) ∧
          InOpenTri (w (Finset.univ.image d)) (S (d 1)) (S (d 2)) (S y1) ∧
          (∀ z ∈ (Finset.univ \ Finset.univ.image d).erase y0,
            ¬ InClosedTri (S (d 0)) (S (d 1)) (S y0) (S z) ∧
            ¬ InClosedTri (S y0) (S (d 1)) (S (d 2)) (S z)) ∧
          (∀ z ∈ (Finset.univ \ Finset.univ.image d).erase y1,
            ¬ InClosedTri (S (d 2)) (S (d 1)) (S y1) (S z) ∧
            ¬ InClosedTri (S y1) (S (d 1)) (S (d 0)) (S z))) :
    False := by
  let D : Finset (Fin 10) := Finset.univ.image d
  let M : Finset (Fin 10) := Finset.univ \ D
  let B := hullVertices S
  let H := certifiedVertices S w
  by_cases h_has01 : ∃ y ∈ M, InOpenTri (w D) (S (d 0)) (S (d 1)) (S y)
  · by_cases h_has12 : ∃ y ∈ M, InOpenTri (w D) (S (d 1)) (S (d 2)) (S y)
    · -- Regime 2: both e⁻¹(01) and e⁻¹(12) are nonempty
      obtain ⟨y0, hy0M, y1, hy1M, hy01, hy0_ex, hy1_ex, hy0_loc, hy1_loc⟩ :=
        h_reg2_loc h_has01 h_has12
      have hD_B : D ⊆ B := by dsimp [D, B]; rw [hDB]; exact Finset.sdiff_subset
      have hD_card : D.card = 5 := by
        dsimp [D]; rw [Finset.card_image_of_injective Finset.univ hd_inj, Finset.card_fin]
      have hM_card : M.card = 5 := by
        dsimp [M]; rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_fin, hD_card]
      have hM_disj : Disjoint D M := Finset.disjoint_left.mpr fun _ hx hm => (Finset.mem_sdiff.mp hm).2 hx
      have h_H_arc2 : H.Nonempty → ∃ rstar : Fin 5, rstar ≠ 0 ∧ rstar ≠ 1 ∧
          (∀ h ∈ H, orient2D (S (d rstar)) (S (d (rstar + 1))) (S h) < 0) ∧
          (∀ i : Fin 5, i ≠ rstar → ∀ h ∈ H, 0 < orient2D (S (d i)) (S (d (i + 1))) (S h)) := by
        intro hHne
        obtain ⟨rstar, hr_out, hH_pos, h_not_lr⟩ := h_H_arc hHne
        refine ⟨rstar, fun h0 => h_not_lr y0 hy0M (by rw [h0]; exact hy0_ex), ?_, hr_out, hH_pos⟩
        intro h1
        have h12 : rstar + 1 = 2 := by rw [h1]; decide
        refine h_not_lr y1 hy1M ?_
        rw [h12, h1]; exact hy1_ex
      have hM_01 : ∀ y ∈ M, 0 < orient2D (S (d 0)) (S (d 1)) (S y) := by
        by_cases hHne : H.Nonempty
        · obtain ⟨rstar, hr0, _, _, hH_pos⟩ := h_H_arc2 hHne
          exact hullVertices_nonneg_edge hP hd_inj hv hDB rfl 0 (hH_pos 0 hr0.symm)
        · have hH_empty : H = ∅ := Finset.not_nonempty_iff_eq_empty.mp hHne
          exact hullVertices_nonneg_edge hP hd_inj hv hDB rfl 0
            (fun h hh => by change h ∈ H at hh; rw [hH_empty] at hh; simp at hh)
      have hM_12 : ∀ y ∈ M, 0 < orient2D (S (d 1)) (S (d 2)) (S y) := by
        by_cases hHne : H.Nonempty
        · obtain ⟨rstar, _, hr1, _, hH_pos⟩ := h_H_arc2 hHne
          exact hullVertices_nonneg_edge hP hd_inj hv hDB rfl 1 (hH_pos 1 hr1.symm)
        · have hH_empty : H = ∅ := Finset.not_nonempty_iff_eq_empty.mp hHne
          exact hullVertices_nonneg_edge hP hd_inj hv hDB rfl 1
            (fun h hh => by change h ∈ H at hh; rw [hH_empty] at hh; simp at hh)
      have hwD_01 : 0 < orient2D (S (d 0)) (S (d 1)) (w D) := by
        rcases hy0_ex with ⟨μ₁, μ₂, μ₃, hμ1, _, _, hs, hx1, hx2⟩
        have hid : orient2D (S (d 0)) (S (d 1)) (S y0) =
            μ₁ * orient2D (S (d 0)) (S (d 1)) (w D) := by
          unfold orient2D; rw [hx1, hx2]
          linear_combination ((S (d 0)).2 * (S (d 1)).1 - (S (d 0)).1 * (S (d 1)).2) * hs
        have hpos := hM_01 y0 hy0M
        nlinarith
      have hwD_12 : 0 < orient2D (S (d 1)) (S (d 2)) (w D) := by
        rcases hy1_ex with ⟨μ₁, μ₂, μ₃, hμ1, _, _, hs, hx1, hx2⟩
        have hid : orient2D (S (d 1)) (S (d 2)) (S y1) =
            μ₁ * orient2D (S (d 1)) (S (d 2)) (w D) := by
          unfold orient2D; rw [hx1, hx2]
          linear_combination ((S (d 1)).2 * (S (d 2)).1 - (S (d 1)).1 * (S (d 2)).2) * hs
        have hpos := hM_12 y1 hy1M
        nlinarith
      have hM_exit : ∀ y ∈ M, InOpenTri (w D) (S (d 0)) (S (d 1)) (S y) ∨
          InOpenTri (w D) (S (d 1)) (S (d 2)) (S y) := by
        intro y hy
        rcases h_exit y hy with h | h
        · exact Or.inl h.2
        · exact Or.inr h.2
      obtain ⟨hM_02_pos, _, _, hW_sub, hM_wedges⟩ :=
        adjacent_ear_empty_and_chord_wedges hP hd_inj hv D M rfl hM_disj
          y0 y1 hy0M hy1M hy01 hM_01 hM_12 hwD_01 hwD_12 hM_exit hy0_loc hy1_loc
      obtain ⟨m_enum, hm_inj, hm_img⟩ := finset_M_enum hM_card
      have hm_mem : ∀ i : Fin 5, m_enum i ∈ M := fun i =>
        hm_img ▸ Finset.mem_image_of_mem m_enum (Finset.mem_univ i)
      have h_wedges_ex : ∀ i : Fin 5, ∃ W_i : OpenWedge, W_i.y = S (m_enum i) ∧
          (∀ z : ℝ × ℝ, W_i.MemOpen z →
            z ∈ UCone (S (m_enum i)) (S (d 0)) (S (d 2)) ∧
            (pentagonDiag02HalfPlane (S ∘ d) hv).MemPos z) ∧
          IsWedgeTest P (WitnessSet {d 0, d 2} ∅ w) (S (m_enum i)) W_i :=
        fun i => hM_wedges (m_enum i) (hm_mem i)
      choose W hWy hW_U hW_test using h_wedges_ex
      let M_mask : (Fin 5 → Bool) → Finset (Fin 10) := fun mask =>
        (Finset.univ.filter (fun i : Fin 5 => mask i = true)).image m_enum
      have h_d_not_M : ∀ (k : Fin 5) (mask : Fin 5 → Bool), d k ∉ M_mask mask := by
        intro k mask hmem
        rcases Finset.mem_image.mp hmem with ⟨i, _, hi⟩
        exact Finset.disjoint_left.mp hM_disj
          (Finset.mem_image_of_mem d (Finset.mem_univ k)) (hi ▸ hm_mem i)
      let xk_T : Fin 5 → (Fin 5 → Bool) → Finset (Fin 10) := fun k mask =>
        if k = 1 ∨ k = 3 ∨ k = 4 then (D.erase (d k)) ∪ M_mask mask
        else (D.erase (d 3)) ∪ M_mask mask
      let xk : Fin 5 → (Fin 5 → Bool) → ℝ × ℝ := fun k mask => w (xk_T k mask)
      have hxk_in_W02 : ∀ k mask, xk k mask ∈ WitnessSet {d 0, d 2} ∅ w := by
        intro k mask
        refine ⟨xk_T k mask, ?_, Finset.disjoint_empty_right _, rfl⟩
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        dsimp [xk_T]
        split_ifs with hk
        · refine Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨?_, ?_⟩)
          · rcases hx with rfl | rfl <;> rcases hk with rfl | rfl | rfl <;> exact hd_inj.ne (by decide)
          · rcases hx with rfl | rfl <;> exact Finset.mem_image_of_mem d (Finset.mem_univ _)
        · refine Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨?_, ?_⟩)
          · rcases hx with rfl | rfl <;> exact hd_inj.ne (by decide)
          · rcases hx with rfl | rfl <;> exact Finset.mem_image_of_mem d (Finset.mem_univ _)
      have h_realizes : ∀ T : Finset (Fin 10), ∀ mask : Fin 5 → Bool,
          w T ∈ WitnessSet {d 0, d 2} ∅ w →
          (∀ i : Fin 5, m_enum i ∈ T ↔ mask i = true) →
          RealizesWedgeMask W mask (w T) := by
        intro T mask hwT him i
        have htest := hW_test i (w T) hwT
        have hsees := (hP.shatters T (m_enum i)).trans (him i)
        cases hmi : mask i
        · simp only [Bool.false_eq_true, ↓reduceIte]
          rcases htest.1 with ho | he
          · exfalso; have := hsees.mp (htest.2.mpr ho); simp [hmi] at this
          · exact he
        · simp only [↓reduceIte]
          exact htest.2.mp (hsees.mpr hmi)
      have hxk_mask : ∀ k mask, RealizesWedgeMask W mask (xk k mask) := by
        intro k mask
        refine h_realizes (xk_T k mask) mask (hxk_in_W02 k mask) (fun i => ?_)
        dsimp [xk_T, M_mask]
        split_ifs
        · simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_image, Finset.mem_filter,
            Finset.mem_univ, true_and]
          constructor
          · rintro (⟨_, hiD⟩ | ⟨j, hj, hji⟩)
            · exact False.elim (Finset.disjoint_left.mp hM_disj hiD (hm_mem i))
            · rwa [← hm_inj hji]
          · intro hmi; right; exact ⟨i, hmi, rfl⟩
        · simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_image, Finset.mem_filter,
            Finset.mem_univ, true_and]
          constructor
          · rintro (⟨_, hiD⟩ | ⟨j, hj, hji⟩)
            · exact False.elim (Finset.disjoint_left.mp hM_disj hiD (hm_mem i))
            · rwa [← hm_inj hji]
          · intro hmi; right; exact ⟨i, hmi, rfl⟩
      let pm : (Fin 5 → Bool) → ℝ × ℝ := fun mask => w (D ∪ M_mask mask)
      have hpm_mask : ∀ mask, RealizesWedgeMask W mask (pm mask) := by
        intro mask
        refine h_realizes (D ∪ M_mask mask) mask ⟨D ∪ M_mask mask, ?_, Finset.disjoint_empty_right _, rfl⟩
          (fun i => ?_)
        · intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl <;> exact Finset.mem_union_left _ (Finset.mem_image_of_mem d (Finset.mem_univ _))
        · dsimp [M_mask]
          simp only [Finset.mem_union, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
          constructor
          · rintro (hiD | ⟨j, hj, hji⟩)
            · exact False.elim (Finset.disjoint_left.mp hM_disj hiD (hm_mem i))
            · rwa [← hm_inj hji]
          · intro hmi; right; exact ⟨i, hmi, rfl⟩
      have hR_in_conv : ∀ z : ℝ × ℝ, (∀ i : Fin 5, (W i).MemOpen z) →
          z ∈ convexHull ℝ (WitnessSet D ∅ w) := by
        intro z hz
        have hcz := thm1_part2_convexHull_containment h_thm1 W pm hpm_mask z hz
        refine convexHull_mono ?_ hcz
        rintro _ ⟨mask, rfl⟩
        exact ⟨D ∪ M_mask mask, Finset.subset_union_left, Finset.disjoint_empty_right _, rfl⟩
      have hk_nonfront : ∀ (k : Fin 5) (hk : k = 1 ∨ k = 3 ∨ k = 4) (mask : Fin 5 → Bool),
          (pentagonEdgeHalfPlane (S ∘ d) hv (k - 1)).MemPos (xk k mask) ∨
          (pentagonEdgeHalfPlane (S ∘ d) hv k).MemPos (xk k mask) := by
        intro k hk mask
        have hk_notH : d k ∉ H := fun h =>
          Finset.disjoint_left.mp (by rw [hDB]; exact Finset.sdiff_disjoint)
            (Finset.mem_image_of_mem d (Finset.mem_univ k)) h
        have hTx_sub : D.erase (d k) ⊆ xk_T k mask := by
          dsimp [xk_T]; rw [if_pos hk]; exact Finset.subset_union_left
        have hk_not_Tx : d k ∉ xk_T k mask := by
          dsimp [xk_T]; rw [if_pos hk]; simp [h_d_not_M k mask]
        exact pentagon_cells_nonfront hP hd_inj hv hD_B k hk_notH hTx_sub hk_not_Tx
      have hk_xor : ∀ (k : Fin 5) (hk : k = 1 ∨ k = 3 ∨ k = 4),
          (pentagonEdgeHalfPlane (S ∘ d) hv (k - 1)).MemPos (xk k (fun _ => true)) ↔
          ¬ (pentagonEdgeHalfPlane (S ∘ d) hv k).MemPos (xk k (fun _ => true)) := by
        intro k hk
        have hk_notH : d k ∉ H := fun h =>
          Finset.disjoint_left.mp (by rw [hDB]; exact Finset.sdiff_disjoint)
            (Finset.mem_image_of_mem d (Finset.mem_univ k)) h
        have hTx_sub : D.erase (d k) ⊆ xk_T k (fun _ => true) := by
          dsimp [xk_T]; rw [if_pos hk]; exact Finset.subset_union_left
        have hk_not_Tx : d k ∉ xk_T k (fun _ => true) := by
          dsimp [xk_T]; rw [if_pos hk]; simp [h_d_not_M k _]
        have hx_conv : xk k (fun _ => true) ∈ convexHull ℝ (WitnessSet D ∅ w) :=
          hR_in_conv _ (fun i => by simpa using hxk_mask k (fun _ => true) i)
        exact pentagon_cells_xor_of_convexHull hP hd_inj hv hD_B k hk_notH hTx_sub hk_not_Tx hx_conv
      have h_xor1 : (pentagonEdgeHalfPlane (S ∘ d) hv 0).MemPos (xk 1 (fun _ => true)) ↔
          ¬ (pentagonEdgeHalfPlane (S ∘ d) hv 1).MemPos (xk 1 (fun _ => true)) := by
        have hTx_sub : D.erase (d 1) ⊆ xk_T 1 (fun _ => true) := by
          dsimp [xk_T]; exact Finset.subset_union_left
        have h1_not_Tx : d 1 ∉ xk_T 1 (fun _ => true) := by
          dsimp [xk_T]; simp [h_d_not_M 1 _]
        have hx_conv : xk 1 (fun _ => true) ∈ convexHull ℝ (WitnessSet D ∅ w) :=
          hR_in_conv _ (fun i => by simpa using hxk_mask 1 (fun _ => true) i)
        exact pentagon_cells_xor1_H02 hP hd_inj hv hTx_sub h1_not_Tx
          (hW_sub _ (hxk_in_W02 1 _)).1 hx_conv
      refine pentagon_wedges_no_ten_shattered_planar_regime2 h_thm1 h_caseA_orig (S ∘ d) hv W xk
        hxk_mask
        (hk_nonfront 3 (Or.inr (Or.inl rfl)))
        (hk_nonfront 4 (Or.inr (Or.inr rfl)))
        (hk_xor 3 (Or.inr (Or.inl rfl)))
        (hk_xor 4 (Or.inr (Or.inr rfl)))
        ⟨fun k mask => (hW_sub _ (hxk_in_W02 k mask)).1,
         fun z hz => (hW_U 0 z (hz 0)).2, h_xor1⟩
        ?_
      by_cases hHne : H.Nonempty
      · obtain ⟨rstar, hr0, hr1, hr_out, _⟩ := h_H_arc2 hHne
        obtain ⟨h_in_H, hhH⟩ := hHne
        have hhM : h_in_H ∈ M := by
          refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun hhD => ?_⟩
          dsimp [D] at hhD
          rw [hDB] at hhD
          exact (Finset.mem_sdiff.mp hhD).2 hhH
        have hh_02 : 0 < orient2D (S (d 0)) (S (d 2)) (S h_in_H) := (hM_02_pos h_in_H hhM).2
        left
        refine ⟨rstar, hr0, hr1, ?_, ?_⟩
        · intro k mask
          have hkU := (hW_sub _ (hxk_in_W02 k mask)).2 h_in_H hhM
          have hneg := (pentagon_cells_certified_cone_H02 hv rstar hr0 hr1 (hr_out h_in_H hhH) hh_02 _ hkU).2
          dsimp [pentagonEdgeHalfPlane] at hneg ⊢
          rw [edgeHalfPlane_memPos_iff]; rw [edgeHalfPlane_memNeg_iff] at hneg; linarith
        · intro z hz
          have hh_img : h_in_H ∈ Finset.univ.image m_enum := by rwa [hm_img]
          obtain ⟨i_h, _, hi_eq⟩ := Finset.mem_image.mp hh_img
          have hzU : z ∈ UCone (S h_in_H) (S (d 0)) (S (d 2)) := by
            rw [← hi_eq]; exact (hW_U i_h z (hz i_h)).1
          have hneg := (pentagon_cells_certified_cone_H02 hv rstar hr0 hr1 (hr_out h_in_H hhH) hh_02 _ hzU).2
          dsimp [pentagonEdgeHalfPlane] at hneg ⊢
          rw [edgeHalfPlane_memPos_iff]; rw [edgeHalfPlane_memNeg_iff] at hneg; linarith
      · have hH_empty : H = ∅ := Finset.not_nonempty_iff_eq_empty.mp hHne
        right
        intro i r
        rw [hWy i]
        have hall_r : ∀ y ∈ M, 0 < orient2D (S (d r)) (S (d (r + 1))) (S y) :=
          hullVertices_nonneg_edge hP hd_inj hv hDB rfl r
            (fun h hh => by change h ∈ H at hh; rw [hH_empty] at hh; simp at hh)
        dsimp [pentagonEdgeHalfPlane]
        rw [edgeHalfPlane_memPos_iff]
        exact hall_r (m_enum i) (hm_mem i)
    · -- Regime 1: e⁻¹(12) = ∅, so e(M) = {01}
      have h_exit01 : ∀ y ∈ M, 0 < orient2D (S (d 0)) (S (d 1)) (w D) ∧
          InOpenTri (w D) (S (d 0)) (S (d 1)) (S y) := by
        intro y hy
        rcases h_exit y hy with h | h
        · exact h
        · exact False.elim (h_has12 ⟨y, hy, h.2⟩)
      refine localized_pentagon_regime1_contradiction h_thm1 h_caseA_orig hP d hd_inj hv hDB h_exit01 ?_
      intro hHne
      obtain ⟨rstar, hr_out, hH_pos, h_not_lr⟩ := h_H_arc hHne
      obtain ⟨y0, hy0M, hy0_ex⟩ := h_has01
      have hr0 : rstar ≠ 0 := fun h0 => h_not_lr y0 hy0M (by rw [h0]; exact hy0_ex)
      exact ⟨rstar, hr0, hr_out, hH_pos⟩
  · -- e⁻¹(01) = ∅, so e(M) = {12}; cyclically shift d' i = d (i + 1) to get Regime 1!
    let d' : Fin 5 → Fin 10 := fun i => d (i + 1)
    have hd'_inj : Function.Injective d' := hd_inj.comp (add_left_injective (1 : Fin 5))
    have hv' : StrictConvexCCWPentagon (S ∘ d') := strictConvexCCWPentagon_shift1 hv
    have hD'_eq : Finset.univ.image d' = D := by
      ext x; simp only [Finset.mem_image, Finset.mem_univ, true_and, D, d']
      constructor
      · rintro ⟨i, hi⟩; exact ⟨i + 1, hi⟩
      · rintro ⟨i, hi⟩; exact ⟨i - 1, by simpa using hi⟩
    have hDB' : Finset.univ.image d' = hullVertices S \ certifiedVertices S w := hD'_eq ▸ hDB
    have h_exit01' : ∀ y ∈ Finset.univ \ Finset.univ.image d',
        0 < orient2D (S (d' 0)) (S (d' 1)) (w (Finset.univ.image d')) ∧
        InOpenTri (w (Finset.univ.image d')) (S (d' 0)) (S (d' 1)) (S y) := by
      intro y hy
      rw [hD'_eq] at hy ⊢
      rcases h_exit y hy with h | h
      · exact False.elim (h_has01 ⟨y, hy, h.2⟩)
      · simpa [d'] using h
    refine localized_pentagon_regime1_contradiction h_thm1 h_caseA_orig hP d' hd'_inj hv' hDB' h_exit01' ?_
    intro hHne
    obtain ⟨rstar, hr_out, hH_pos, h_not_lr⟩ := h_H_arc hHne
    have hM_card : M.card = 5 := by
      have hD_card : D.card = 5 := by
        rw [Finset.card_image_of_injective Finset.univ hd_inj, Finset.card_fin]
      dsimp [M]; rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_fin, hD_card]
    obtain ⟨y0, hy0M⟩ := Finset.card_pos.mp (by omega : 0 < M.card)
    have hy0_12 : InOpenTri (w D) (S (d 1)) (S (d 2)) (S y0) := by
      rcases h_exit y0 hy0M with h | h
      · exact False.elim (h_has01 ⟨y0, hy0M, h.2⟩)
      · exact h.2
    have hr1 : rstar ≠ 1 := by
      intro h1
      have h12 : rstar + 1 = 2 := by rw [h1]; decide
      exact h_not_lr y0 hy0M (by rw [h12, h1]; exact hy0_12)
    refine ⟨rstar - 1, ?_, ?_, ?_⟩
    · intro h0; exact hr1 (sub_eq_zero.mp h0)
    · intro h hh
      simpa [d', sub_add_cancel] using hr_out h hh
    · intro i hi h hh
      have hi1 : i + 1 ≠ rstar := fun heq => hi (eq_sub_of_add_eq heq)
      simpa [d', add_assoc] using hH_pos (i + 1) hi1 h hh

end Sec11Bridge
