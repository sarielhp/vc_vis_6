import Mathlib
import RootTask.PolygonDefs
import RootTask.PolygonEnclosureCore
import RootTask.SixWedges
import RootTask.Sec5HalfPlane
import RootTask.Sec6Targets
import RootTask.Sec7Combination
import RootTask.ArrangementBounds
import RootTask.Sec8And11PolygonBridge
import RootTask.NewEnclosureLemmas
import RootTask.ChirotopeSoundness
import RootTask.CertifiedAndHalfPlaneSoundness

open scoped Classical BigOperators
open Finset
open ChirotopeSoundness CertifiedAndHalfPlaneSoundness

noncomputable section

namespace SourceGapAndCaseSplits

/-!
# Clause `(C7)` Source-Gap Chirotope Soundness, Complete Theorem 8.1, and Structural Case Splits

1. **General-`n` `Sec2To5Interface` Bridge (`mk_sec2To5Interface_general`)**:
   Instantiates `Sec2To5Interface P S w` for every `ShatteredSimplePolygon P S w` with `3 ≤ n`.
2. **Two-Anchor Hexagon Lemmas (`Lemma 5.11` & `Lemma 5.12` of `upper_8.tex`)**:
   Proves disjoint exit-edge selection (`hexagon_disjoint_exits_23_b4`, `hexagon_disjoint_exits_23_b5`,
   `hexagon_disjoint_exits_34_b2`) and adjacent exit-edge selection (`hexagon_adjacent_exits_b5`,
   `hexagon_adjacent_exits_b3`, `hexagon_adjacent_exits_b4`).
3. **Clause `(C7)` (`SourceGapSoundness`) & Complete Theorem 8.1 (`complete_theorem_8_1_chirotope_soundness`)**:
   Bridges `GoodAnchorPair` + `SegmentsCross` to `HalfPlaneChirotopeConfig` + `half_plane_chirotope_clauses_C9`
   with a uniform sign `σ` across all gap and cap points, uniting `(C1)`–`(C11)`.
4. **Exhaustive Structural Case-Split Theorems (`|B| ≤ 6`, `|M| ≤ 5`, `|B| ≥ 3`)**:
   Proves the exact `(|D|, |M|, |H|)` case splits for `|S| = 7` (`A = ∅`, convex = 6),
   `|S| = 9` (`VC-dim ≤ 8`), `|S| = 8` (`VC-dim ≤ 7`), and `|S| = 7` (`VC-dim ≤ 6`).
-/

/-! ## 1. Predicate Equivalences & General-`n` `Sec2To5Interface` Bridge -/

lemma hullVertices_eq {n : ℕ} (S : Fin n → ℝ × ℝ) :
    PolygonCore.hullVertices S = hullVertices S := by
  ext i; simp [PolygonCore.hullVertices, hullVertices]

lemma interiorPoints_eq {n : ℕ} (S : Fin n → ℝ × ℝ) :
    PolygonCore.interiorPoints S = interiorPoints S := by
  rw [PolygonCore.interiorPoints, interiorPoints, hullVertices_eq]

lemma isCCWEdge_iff_isCCWHullEdge {n : ℕ} {P : Set (ℝ × ℝ)}
    {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ}
    (hPoly : ShatteredSimplePolygon P S w) (C : Finset (Fin n)) (a b : Fin n) :
    IsCCWEdge S C a b ↔ PolygonCore.IsCCWHullEdge (C.image S) (S a) (S b) := by
  constructor
  · rintro ⟨ha, hb, hab, hall⟩
    refine ⟨Finset.mem_image_of_mem S ha, Finset.mem_image_of_mem S hb, hPoly.s_inj.ne hab, ?_⟩
    intro z hz hza hzb
    rcases Finset.mem_image.mp hz with ⟨r, hr, rfl⟩
    exact hall r hr (fun h => hza (congrArg S h)) (fun h => hzb (congrArg S h))
  · rintro ⟨ha, hb, hab, hall⟩
    rcases Finset.mem_image.mp ha with ⟨a', ha', ha_eq⟩
    rcases Finset.mem_image.mp hb with ⟨b', hb', hb_eq⟩
    have haa' : a' = a := hPoly.s_inj ha_eq
    have hbb' : b' = b := hPoly.s_inj hb_eq
    subst haa' hbb'
    refine ⟨ha', hb', fun h => hab (congrArg S h), ?_⟩
    intro r hr hra hrb
    exact hall (S r) (Finset.mem_image_of_mem S hr) (hPoly.s_inj.ne hra) (hPoly.s_inj.ne hrb)

private lemma isFrontVertexOf_of_isFrontVertex {n : ℕ} {P : Set (ℝ × ℝ)}
    {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ}
    (hPoly : ShatteredSimplePolygon P S w) {C : Finset (Fin n)} {f : Fin n} (hf : f ∈ C)
    {v : ℝ × ℝ} (hfront : PolygonCore.IsFrontVertex (C.image S) v (S f)) :
    IsFrontVertexOf S C f v := by
  rcases hfront with ⟨b_pt, c_pt, hbf_pt, hfc_pt, hbv, hcv⟩
  refine ⟨hf, fun a b hab heq => ?_⟩
  have hab_pt := (isCCWEdge_iff_isCCWHullEdge hPoly C a b).mp hab
  rcases heq with rfl | rfl
  · rw [PolygonCore.isCCWHullEdge_succ_unique hab_pt hfc_pt]; exact hcv
  · rw [PolygonCore.isCCWHullEdge_pred_unique hab_pt hbf_pt]; exact hbv

private lemma isFrontVertex_of_isFrontVertexOf {n : ℕ} {P : Set (ℝ × ℝ)}
    {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ}
    (hPoly : ShatteredSimplePolygon P S w) {C : Finset (Fin n)} (hCB : C ⊆ hullVertices S)
    (hC3 : 3 ≤ C.card) {f : Fin n} {v : ℝ × ℝ}
    (hfront : IsFrontVertexOf S C f v) :
    PolygonCore.IsFrontVertex (C.image S) v (S f) := by
  obtain ⟨cyc⟩ := exists_ccwCycle S C (fun a _ b _ h => hPoly.s_inj h)
    (fun a _ b _ c _ hab hbc hac => orient_S_S_S_ne hPoly hab hbc hac)
    (hullVertices_convexPos S hCB) (show C.card = (C.card - 3) + 3 by omega)
  obtain ⟨i, rfl⟩ := ccwCycle_exists_index cyc hfront.1
  have e1 := ccwCycle_isCCWEdge cyc (i - 1)
  rw [sub_add_cancel] at e1
  have e2 := ccwCycle_isCCWEdge cyc i
  have ho := (isFrontVertexOf_iff_ccwCycle cyc i v).mp hfront
  exact ⟨S (cyc.toFun (i - 1)), S (cyc.toFun (i + 1)),
    (isCCWEdge_iff_isCCWHullEdge hPoly C _ _).mp e1,
    (isCCWEdge_iff_isCCWHullEdge hPoly C _ _).mp e2, ho.1, ho.2⟩

lemma isBackVertexOf_iff_isBackVertex {n : ℕ} {P : Set (ℝ × ℝ)}
    {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ}
    (hPoly : ShatteredSimplePolygon P S w) {C : Finset (Fin n)} (hCB : C ⊆ hullVertices S)
    (hC3 : 3 ≤ C.card) {p : Fin n} {v : ℝ × ℝ} :
    IsBackVertexOf S C p v ↔ PolygonCore.IsBackVertex (C.image S) v (S p) := by
  obtain ⟨cyc⟩ := exists_ccwCycle S C (fun a _ b _ h => hPoly.s_inj h)
    (fun a _ b _ c _ hab hbc hac => orient_S_S_S_ne hPoly hab hbc hac)
    (hullVertices_convexPos S hCB) (show C.card = (C.card - 3) + 3 by omega)
  constructor
  · intro hback
    obtain ⟨i, rfl⟩ := ccwCycle_exists_index cyc hback.1
    have e1 := ccwCycle_isCCWEdge cyc (i - 1)
    rw [sub_add_cancel] at e1
    have e2 := ccwCycle_isCCWEdge cyc i
    have ho := (isBackVertexOf_iff_ccwCycle cyc i v).mp hback
    exact ⟨S (cyc.toFun (i - 1)), S (cyc.toFun (i + 1)),
      (isCCWEdge_iff_isCCWHullEdge hPoly C _ _).mp e1,
      (isCCWEdge_iff_isCCWHullEdge hPoly C _ _).mp e2, ho.1, ho.2⟩
  · rintro ⟨b_pt, c_pt, hbp_pt, hpc_pt, hbv, hcv⟩
    obtain ⟨p', hp'C, hp'eq⟩ := Finset.mem_image.mp hbp_pt.2.1
    have hpp' : p' = p := hPoly.s_inj hp'eq
    subst hpp'
    refine ⟨hp'C, fun a b hab heq => ?_⟩
    have hab_pt := (isCCWEdge_iff_isCCWHullEdge hPoly C a b).mp hab
    rcases heq with rfl | rfl
    · rw [PolygonCore.isCCWHullEdge_succ_unique hab_pt hpc_pt]; exact hcv
    · rw [PolygonCore.isCCWHullEdge_pred_unique hab_pt hbp_pt]; exact hbv

lemma certifiedVertices_eq_certifiedSet {n : ℕ} (hn : 3 ≤ n) {P : Set (ℝ × ℝ)}
    {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ}
    (hPoly : ShatteredSimplePolygon P S w) :
    certifiedVertices S w = PolygonCore.certifiedSet P S w := by
  let B := hullVertices S
  have hB3 : 3 ≤ B.card := PolygonCore.hullVertices_card_ge_three hn hPoly
  ext f
  simp only [certifiedVertices, PolygonCore.certifiedSet, PolygonCore.IsCertified,
    Finset.mem_filter, hullVertices_eq]
  constructor
  · rintro ⟨hfB, T, hfT, hbT, hcT, hfront⟩
    refine ⟨hfB, hfB, T, fun hsees => hfT ((hPoly.shatters T f).mp hsees), ?_,
      isFrontVertex_of_isFrontVertexOf hPoly Finset.Subset.rfl hB3 hfront⟩
    intro b _ h_or
    refine (hPoly.shatters T b).mpr ?_
    rcases h_or with hbf | hfb
    · exact hbT b ((isCCWEdge_iff_isCCWHullEdge hPoly B b f).mpr hbf)
    · exact hcT b ((isCCWEdge_iff_isCCWHullEdge hPoly B f b).mpr hfb)
  · rintro ⟨hfB, _, T, hvnf, hvs, hfront⟩
    refine ⟨hfB, T, fun hfT => hvnf ((hPoly.shatters T f).mpr hfT), ?_, ?_,
      isFrontVertexOf_of_isFrontVertex hPoly hfB hfront⟩
    · intro b hbf
      exact (hPoly.shatters T b).mp (hvs b hbf.1 (Or.inl ((isCCWEdge_iff_isCCWHullEdge hPoly B b f).mp hbf)))
    · intro c hfc
      exact (hPoly.shatters T c).mp (hvs c hfc.2.1 (Or.inr ((isCCWEdge_iff_isCCWHullEdge hPoly B f c).mp hfc)))

private lemma openWedge_inter_at_apex (R₀ U : OpenWedge)
    (hy : R₀.y = U.y) (p₀ : ℝ × ℝ) (hpR : R₀.MemOpen p₀) (hpU : U.MemOpen p₀) :
    ∃ R : OpenWedge, R.y = U.y ∧
      (∀ z : ℝ × ℝ, R.MemOpen z ↔ R₀.MemOpen z ∧ U.MemOpen z) ∧
      (∀ z : ℝ × ℝ, R.MemExt z ↔ R₀.MemExt z ∨ U.MemExt z) := by
  let y := U.y
  let e₁ : ℝ × ℝ := (p₀.1 - y.1, p₀.2 - y.2)
  let e₂ : ℝ × ℝ := (-e₁.2, e₁.1)
  have he1_sq : 0 < e₁.1 ^ 2 + e₁.2 ^ 2 := by
    by_contra hle
    have hle' : e₁.1 ^ 2 + e₁.2 ^ 2 ≤ 0 := not_lt.mp hle
    have hs1 : e₁.1 = 0 := sq_eq_zero_iff.mp (by nlinarith [sq_nonneg e₁.1, sq_nonneg e₁.2])
    have hs2 : e₁.2 = 0 := sq_eq_zero_iff.mp (by nlinarith [sq_nonneg e₁.1, sq_nonneg e₁.2])
    have h1 : 0 < U.u₁.1 * e₁.1 + U.u₁.2 * e₁.2 := hpU.1
    rw [hs1, hs2, mul_zero, mul_zero, add_zero] at h1
    exact lt_irrefl 0 h1
  let dotE1 : ℝ × ℝ → ℝ := fun u => u.1 * e₁.1 + u.2 * e₁.2
  let dotE2 : ℝ × ℝ → ℝ := fun u => u.1 * e₂.1 + u.2 * e₂.2
  have hU1 : 0 < dotE1 U.u₁ := hpU.1
  have hU2 : 0 < dotE1 U.u₂ := hpU.2
  have hR1 : 0 < dotE1 R₀.u₁ := by simpa [dotE1, e₁, y, hy] using hpR.1
  have hR2 : 0 < dotE1 R₀.u₂ := by simpa [dotE1, e₁, y, hy] using hpR.2
  let k : ℝ × ℝ → ℝ := fun u => dotE2 u / dotE1 u
  have hdet_iff : ∀ u v : ℝ × ℝ, 0 < dotE1 u → 0 < dotE1 v →
      (0 < u.1 * v.2 - u.2 * v.1 ↔ k u < k v) := by
    intro u v hu hv
    have hid : (e₁.1 ^ 2 + e₁.2 ^ 2) * (u.1 * v.2 - u.2 * v.1) =
        dotE1 u * dotE2 v - dotE2 u * dotE1 v := by dsimp [dotE1, dotE2, e₁, e₂]; ring
    dsimp [k]; rw [div_lt_div_iff₀ hu hv]
    exact ⟨fun hdet => by have := mul_pos he1_sq hdet; linarith,
      fun hlt => pos_of_mul_pos_right (by linarith) (le_of_lt he1_sq)⟩
  have hkU : k U.u₁ < k U.u₂ := (hdet_iff U.u₁ U.u₂ hU1 hU2).mp U.h_nondeg
  have hkR : k R₀.u₁ < k R₀.u₂ := (hdet_iff R₀.u₁ R₀.u₂ hR1 hR2).mp R₀.h_nondeg
  let u₁s : ℝ × ℝ := if k U.u₁ ≤ k R₀.u₁ then U.u₁ else R₀.u₁
  let u₂s : ℝ × ℝ := if k U.u₂ ≤ k R₀.u₂ then R₀.u₂ else U.u₂
  have hu1s_dot : 0 < dotE1 u₁s := by dsimp [u₁s]; split_ifs <;> assumption
  have hu2s_dot : 0 < dotE1 u₂s := by dsimp [u₂s]; split_ifs <;> assumption
  have hku1s : k u₁s ≤ k U.u₁ ∧ k u₁s ≤ k R₀.u₁ := by
    dsimp [u₁s]; split_ifs with h; exact ⟨le_rfl, h⟩; exact ⟨le_of_lt (not_le.mp h), le_rfl⟩
  have hku2s : k U.u₂ ≤ k u₂s ∧ k R₀.u₂ ≤ k u₂s := by
    dsimp [u₂s]; split_ifs with h; exact ⟨h, le_rfl⟩; exact ⟨le_rfl, le_of_lt (not_le.mp h)⟩
  have hk12 : k u₁s < k u₂s := lt_of_le_of_lt hku1s.1 (lt_of_lt_of_le hkU hku2s.1)
  let R : OpenWedge := ⟨y, u₁s, u₂s, (hdet_iff u₁s u₂s hu1s_dot hu2s_dot).mpr hk12⟩
  have hcomb : ∀ u : ℝ × ℝ, 0 < dotE1 u → k u₁s ≤ k u → k u ≤ k u₂s →
      ∃ α β : ℝ, 0 ≤ α ∧ 0 ≤ β ∧ (0 < α ∨ 0 < β) ∧
        ∀ z : ℝ × ℝ, u.1 * (z.1 - y.1) + u.2 * (z.2 - y.2) =
          α * (u₁s.1 * (z.1 - y.1) + u₁s.2 * (z.2 - y.2)) +
          β * (u₂s.1 * (z.1 - y.1) + u₂s.2 * (z.2 - y.2)) := by
    intro u hu hlo hhi
    let den := k u₂s - k u₁s
    have hden : 0 < den := sub_pos.mpr hk12
    let t := (k u - k u₁s) / den
    have ht0 : 0 ≤ t := div_nonneg (sub_nonneg.mpr hlo) (le_of_lt hden)
    have hk12_ne : k u₂s - k u₁s ≠ 0 := sub_ne_zero.mpr (ne_of_gt hk12)
    have ht1 : 0 ≤ 1 - t := by
      have : 1 - t = (k u₂s - k u) / den := by
        dsimp [t, den]; field_simp [hk12_ne]; ring
      rw [this]; exact div_nonneg (sub_nonneg.mpr hhi) (le_of_lt hden)
    let α := dotE1 u * (1 - t) / dotE1 u₁s
    let β := dotE1 u * t / dotE1 u₂s
    refine ⟨α, β, div_nonneg (mul_nonneg (le_of_lt hu) ht1) (le_of_lt hu1s_dot),
      div_nonneg (mul_nonneg (le_of_lt hu) ht0) (le_of_lt hu2s_dot), ?_, fun z => ?_⟩
    · by_cases ht_zero : t = 0
      · left; dsimp [α]; rw [ht_zero, sub_zero, mul_one]; exact div_pos hu hu1s_dot
      · right; dsimp [β]; exact div_pos (mul_pos hu (lt_of_le_of_ne ht0 (Ne.symm ht_zero))) hu2s_dot
    · have hbasis : ∀ v : ℝ × ℝ, (e₁.1 ^ 2 + e₁.2 ^ 2) * v.1 = dotE1 v * e₁.1 + dotE2 v * e₂.1 ∧
          (e₁.1 ^ 2 + e₁.2 ^ 2) * v.2 = dotE1 v * e₁.2 + dotE2 v * e₂.2 :=
        fun v => ⟨by dsimp [dotE1, dotE2, e₁, e₂]; ring, by dsimp [dotE1, dotE2, e₁, e₂]; ring⟩
      have hsum_e1 : α * dotE1 u₁s + β * dotE1 u₂s = dotE1 u := by
        dsimp [α, β]; field_simp [ne_of_gt hu1s_dot, ne_of_gt hu2s_dot]; ring
      have hsum_e2 : α * dotE2 u₁s + β * dotE2 u₂s = dotE2 u := by
        have hku1 : dotE2 u₁s = k u₁s * dotE1 u₁s := by
          dsimp [k]; rw [div_mul_cancel₀ _ (ne_of_gt hu1s_dot)]
        have hku2 : dotE2 u₂s = k u₂s * dotE1 u₂s := by
          dsimp [k]; rw [div_mul_cancel₀ _ (ne_of_gt hu2s_dot)]
        have hku : dotE2 u = k u * dotE1 u := by
          dsimp [k]; rw [div_mul_cancel₀ _ (ne_of_gt hu)]
        rw [hku1, hku2, hku]; dsimp [α, β, t, den]
        field_simp [ne_of_gt hu1s_dot, ne_of_gt hu2s_dot, hk12_ne]; ring
      have h1 : (e₁.1 ^ 2 + e₁.2 ^ 2) * (u.1 - (α * u₁s.1 + β * u₂s.1)) = 0 :=
        by linear_combination (hbasis u).1 - α * (hbasis u₁s).1 - β * (hbasis u₂s).1 - e₁.1 * hsum_e1 - e₂.1 * hsum_e2
      have h2 : (e₁.1 ^ 2 + e₁.2 ^ 2) * (u.2 - (α * u₁s.2 + β * u₂s.2)) = 0 :=
        by linear_combination (hbasis u).2 - α * (hbasis u₁s).2 - β * (hbasis u₂s).2 - e₁.2 * hsum_e1 - e₂.2 * hsum_e2
      have hu1_eq : u.1 = α * u₁s.1 + β * u₂s.1 := by
        linarith [(mul_eq_zero.mp h1).resolve_left (ne_of_gt he1_sq)]
      have hu2_eq : u.2 = α * u₁s.2 + β * u₂s.2 := by
        linarith [(mul_eq_zero.mp h2).resolve_left (ne_of_gt he1_sq)]
      rw [hu1_eq, hu2_eq]; ring
  have hcU1 := hcomb U.u₁ hU1 hku1s.1 (le_trans (le_of_lt hkU) hku2s.1)
  have hcU2 := hcomb U.u₂ hU2 (le_trans hku1s.1 (le_of_lt hkU)) hku2s.1
  have hcR1 := hcomb R₀.u₁ hR1 hku1s.2 (le_trans (le_of_lt hkR) hku2s.2)
  have hcR2 := hcomb R₀.u₂ hR2 (le_trans hku1s.2 (le_of_lt hkR)) hku2s.2
  have himp_pos : ∀ {u z : ℝ × ℝ},
      (∃ α β : ℝ, 0 ≤ α ∧ 0 ≤ β ∧ (0 < α ∨ 0 < β) ∧
        ∀ w' : ℝ × ℝ, u.1 * (w'.1 - y.1) + u.2 * (w'.2 - y.2) =
          α * (u₁s.1 * (w'.1 - y.1) + u₁s.2 * (w'.2 - y.2)) +
          β * (u₂s.1 * (w'.1 - y.1) + u₂s.2 * (w'.2 - y.2))) →
      R.MemOpen z → 0 < u.1 * (z.1 - y.1) + u.2 * (z.2 - y.2) := by
    rintro u z ⟨α, β, hα, hβ, hpos, heq⟩ ⟨hz1, hz2⟩
    change 0 < u₁s.1 * (z.1 - y.1) + u₁s.2 * (z.2 - y.2) at hz1
    change 0 < u₂s.1 * (z.1 - y.1) + u₂s.2 * (z.2 - y.2) at hz2
    rw [heq z]
    rcases hpos with hαp | hβp
    · linarith [mul_pos hαp hz1, mul_nonneg hβ (le_of_lt hz2)]
    · linarith [mul_nonneg hα (le_of_lt hz1), mul_pos hβp hz2]
  have himp_neg : ∀ {u z : ℝ × ℝ},
      (∃ α β : ℝ, 0 ≤ α ∧ 0 ≤ β ∧ (0 < α ∨ 0 < β) ∧
        ∀ w' : ℝ × ℝ, u.1 * (w'.1 - y.1) + u.2 * (w'.2 - y.2) =
          α * (u₁s.1 * (w'.1 - y.1) + u₁s.2 * (w'.2 - y.2)) +
          β * (u₂s.1 * (w'.1 - y.1) + u₂s.2 * (w'.2 - y.2))) →
      u.1 * (z.1 - y.1) + u.2 * (z.2 - y.2) < 0 → R.MemExt z := by
    rintro u z ⟨α, β, hα, hβ, _, heq⟩ hneg
    rw [heq z] at hneg
    by_contra hno; dsimp [OpenWedge.MemExt, R] at hno; push Not at hno
    linarith [mul_nonneg hα hno.1, mul_nonneg hβ hno.2]
  refine ⟨R, rfl, fun z => ⟨fun hz => ?_, fun ⟨hzR, hzU⟩ => ?_⟩, fun z => ⟨fun hz => ?_, fun hz => ?_⟩⟩
  · refine ⟨⟨?_, ?_⟩, ⟨himp_pos hcU1 hz, himp_pos hcU2 hz⟩⟩
    · rw [hy]; exact himp_pos hcR1 hz
    · rw [hy]; exact himp_pos hcR2 hz
  · constructor
    · dsimp [R, u₁s]; split_ifs; exact hzU.1
      dsimp [y]; rw [← hy]; exact hzR.1
    · dsimp [R, u₂s]; split_ifs
      · dsimp [y]; rw [← hy]; exact hzR.2
      · exact hzU.2
  · rcases hz with hz1 | hz2
    · dsimp [R, u₁s] at hz1; split_ifs at hz1
      · exact Or.inr (Or.inl hz1)
      · exact Or.inl (Or.inl (by rw [hy]; exact hz1))
    · dsimp [R, u₂s] at hz2; split_ifs at hz2
      · exact Or.inl (Or.inr (by rw [hy]; exact hz2))
      · exact Or.inr (Or.inr hz2)
  · rcases hz with (hzR1 | hzR2) | (hzU1 | hzU2)
    · exact himp_neg hcR1 (by dsimp [y]; rw [← hy]; exact hzR1)
    · exact himp_neg hcR2 (by dsimp [y]; rw [← hy]; exact hzR2)
    · exact himp_neg hcU1 hzU1
    · exact himp_neg hcU2 hzU2

private lemma pos_sub_of_eps_abs {A B ε : ℝ} (hε : 0 ≤ ε) (h : ε * |B| < A) :
    0 < A - ε * B ∧ 0 < A + ε * B :=
  ⟨by linarith [mul_le_mul_of_nonneg_left (le_abs_self B) hε],
   by linarith [mul_le_mul_of_nonneg_left (neg_abs_le B) hε]⟩

private lemma subwedge_from_ray (U : OpenWedge) (F : Finset (ℝ × ℝ)) (r₀ : ℝ × ℝ)
    (hr₀_1 : 0 < U.u₁.1 * r₀.1 + U.u₁.2 * r₀.2)
    (hr₀_2 : 0 < U.u₂.1 * r₀.1 + U.u₂.2 * r₀.2)
    (hx_det_ne : ∀ x ∈ F, (x.1 - U.y.1) * r₀.2 - (x.2 - U.y.2) * r₀.1 ≠ 0) :
    ∃ R : OpenWedge, R.y = U.y ∧ (∀ z : ℝ × ℝ, R.MemOpen z → U.MemOpen z) ∧
      (∀ x ∈ F, R.MemExt x) := by
  let y := U.y
  let nr0sq : ℝ := r₀.1 ^ 2 + r₀.2 ^ 2
  have hnr0 : 0 < nr0sq := by
    by_contra hle
    have hle' : nr0sq ≤ 0 := not_lt.mp hle
    have hs1 : r₀.1 ^ 2 = 0 := by dsimp [nr0sq] at hle'; nlinarith [sq_nonneg r₀.1, sq_nonneg r₀.2]
    have hs2 : r₀.2 ^ 2 = 0 := by dsimp [nr0sq] at hle'; nlinarith [sq_nonneg r₀.1, sq_nonneg r₀.2]
    have h0 : r₀.1 = 0 ∧ r₀.2 = 0 := ⟨sq_eq_zero_iff.mp hs1, sq_eq_zero_iff.mp hs2⟩
    rw [h0.1, h0.2, mul_zero, mul_zero, add_zero] at hr₀_1
    exact lt_irrefl 0 hr₀_1
  let εU1 : ℝ := (U.u₁.1 * r₀.1 + U.u₁.2 * r₀.2) / (|U.u₁.1 * (-r₀.2) + U.u₁.2 * r₀.1| + 1)
  let εU2 : ℝ := (U.u₂.1 * r₀.1 + U.u₂.2 * r₀.2) / (|U.u₂.1 * (-r₀.2) + U.u₂.2 * r₀.1| + 1)
  let εF : ℝ := if hne : F.Nonempty then
    F.inf' hne (fun x => |(x.1 - y.1) * r₀.2 - (x.2 - y.2) * r₀.1| /
      (|(x.1 - y.1) * r₀.1 + (x.2 - y.2) * r₀.2| + 1)) else 1
  have hεU1 : 0 < εU1 := div_pos hr₀_1 (by positivity)
  have hεU2 : 0 < εU2 := div_pos hr₀_2 (by positivity)
  have hεF : 0 < εF := by
    dsimp [εF]
    split_ifs with hne
    · rw [Finset.lt_inf'_iff]
      intro x hx
      exact div_pos (abs_pos.mpr (hx_det_ne x hx)) (by positivity)
    · exact zero_lt_one
  obtain ⟨ε, hε_pos, hε1, hε2, hε_lt_F⟩ :
      ∃ ε : ℝ, 0 < ε ∧ ε < εU1 ∧ ε < εU2 ∧ ε < εF := by
    refine ⟨min 1 (min εU1 (min εU2 εF)) / 2, by positivity, ?_, ?_, ?_⟩
    · have := min_le_left εU1 (min εU2 εF)
      have := min_le_right 1 (min εU1 (min εU2 εF))
      linarith
    · have := min_le_left εU2 εF
      have := min_le_right εU1 (min εU2 εF)
      have := min_le_right 1 (min εU1 (min εU2 εF))
      linarith
    · have := min_le_right εU2 εF
      have := min_le_right εU1 (min εU2 εF)
      have := min_le_right 1 (min εU1 (min εU2 εF))
      linarith
  have hmul_U1 : ε * |U.u₁.1 * (-r₀.2) + U.u₁.2 * r₀.1| < U.u₁.1 * r₀.1 + U.u₁.2 * r₀.2 := by
    have hlt : ε * (|U.u₁.1 * (-r₀.2) + U.u₁.2 * r₀.1| + 1) < U.u₁.1 * r₀.1 + U.u₁.2 * r₀.2 :=
      (lt_div_iff₀ (by positivity : 0 < |U.u₁.1 * (-r₀.2) + U.u₁.2 * r₀.1| + 1)).mp hε1
    linarith
  have hmul_U2 : ε * |U.u₂.1 * (-r₀.2) + U.u₂.2 * r₀.1| < U.u₂.1 * r₀.1 + U.u₂.2 * r₀.2 := by
    have hlt : ε * (|U.u₂.1 * (-r₀.2) + U.u₂.2 * r₀.1| + 1) < U.u₂.1 * r₀.1 + U.u₂.2 * r₀.2 :=
      (lt_div_iff₀ (by positivity : 0 < |U.u₂.1 * (-r₀.2) + U.u₂.2 * r₀.1| + 1)).mp hε2
    linarith
  let n₁ : ℝ × ℝ := (r₀.2 + ε * r₀.1, -r₀.1 + ε * r₀.2)
  let n₂ : ℝ × ℝ := (-r₀.2 + ε * r₀.1, r₀.1 + ε * r₀.2)
  have hdet_n : 0 < n₁.1 * n₂.2 - n₁.2 * n₂.1 := by
    have hid : n₁.1 * n₂.2 - n₁.2 * n₂.1 = 2 * ε * nr0sq := by dsimp [n₁, n₂, nr0sq]; ring
    rw [hid]; positivity
  let R : OpenWedge :=
    { y := y
      u₁ := n₁
      u₂ := n₂
      h_nondeg := hdet_n }
  refine ⟨R, rfl, fun z hz => ?_, fun x hx => ?_⟩
  · let d₁ : ℝ × ℝ := (r₀.1 - ε * r₀.2, r₀.2 + ε * r₀.1)
    let d₂ : ℝ × ℝ := (r₀.1 + ε * r₀.2, r₀.2 - ε * r₀.1)
    have hz1 := hz.1
    have hz2 := hz.2
    change 0 < n₁.1 * (z.1 - y.1) + n₁.2 * (z.2 - y.2) at hz1
    change 0 < n₂.1 * (z.1 - y.1) + n₂.2 * (z.2 - y.2) at hz2
    let α := (n₂.1 * (z.1 - y.1) + n₂.2 * (z.2 - y.2)) / (2 * ε * nr0sq)
    let β := (n₁.1 * (z.1 - y.1) + n₁.2 * (z.2 - y.2)) / (2 * ε * nr0sq)
    have hα : 0 < α := div_pos hz2 (by positivity)
    have hβ : 0 < β := div_pos hz1 (by positivity)
    have hden_ne : 2 * ε * nr0sq ≠ 0 := ne_of_gt (by positivity)
    have hzx : z.1 - y.1 = α * d₁.1 + β * d₂.1 := by
      dsimp [α, β, d₁, d₂, n₁, n₂]; field_simp [hden_ne]; dsimp [nr0sq]; ring
    have hzy : z.2 - y.2 = α * d₁.2 + β * d₂.2 := by
      dsimp [α, β, d₁, d₂, n₁, n₂]; field_simp [hden_ne]; dsimp [nr0sq]; ring
    have hd1_U1 : 0 < U.u₁.1 * d₁.1 + U.u₁.2 * d₁.2 := by
      have hid : U.u₁.1 * d₁.1 + U.u₁.2 * d₁.2 =
          (U.u₁.1 * r₀.1 + U.u₁.2 * r₀.2) + ε * (U.u₁.1 * (-r₀.2) + U.u₁.2 * r₀.1) := by
        dsimp [d₁]; ring
      rw [hid]; exact (pos_sub_of_eps_abs (le_of_lt hε_pos) hmul_U1).2
    have hd2_U1 : 0 < U.u₁.1 * d₂.1 + U.u₁.2 * d₂.2 := by
      have hid : U.u₁.1 * d₂.1 + U.u₁.2 * d₂.2 =
          (U.u₁.1 * r₀.1 + U.u₁.2 * r₀.2) - ε * (U.u₁.1 * (-r₀.2) + U.u₁.2 * r₀.1) := by
        dsimp [d₂]; ring
      rw [hid]; exact (pos_sub_of_eps_abs (le_of_lt hε_pos) hmul_U1).1
    have hd1_U2 : 0 < U.u₂.1 * d₁.1 + U.u₂.2 * d₁.2 := by
      have hid : U.u₂.1 * d₁.1 + U.u₂.2 * d₁.2 =
          (U.u₂.1 * r₀.1 + U.u₂.2 * r₀.2) + ε * (U.u₂.1 * (-r₀.2) + U.u₂.2 * r₀.1) := by
        dsimp [d₁]; ring
      rw [hid]; exact (pos_sub_of_eps_abs (le_of_lt hε_pos) hmul_U2).2
    have hd2_U2 : 0 < U.u₂.1 * d₂.1 + U.u₂.2 * d₂.2 := by
      have hid : U.u₂.1 * d₂.1 + U.u₂.2 * d₂.2 =
          (U.u₂.1 * r₀.1 + U.u₂.2 * r₀.2) - ε * (U.u₂.1 * (-r₀.2) + U.u₂.2 * r₀.1) := by
        dsimp [d₂]; ring
      rw [hid]; exact (pos_sub_of_eps_abs (le_of_lt hε_pos) hmul_U2).1
    refine ⟨?_, ?_⟩
    · change 0 < U.u₁.1 * (z.1 - y.1) + U.u₁.2 * (z.2 - y.2)
      rw [hzx, hzy]
      have : U.u₁.1 * (α * d₁.1 + β * d₂.1) + U.u₁.2 * (α * d₁.2 + β * d₂.2) =
          α * (U.u₁.1 * d₁.1 + U.u₁.2 * d₁.2) + β * (U.u₁.1 * d₂.1 + U.u₁.2 * d₂.2) := by ring
      rw [this]; exact add_pos (mul_pos hα hd1_U1) (mul_pos hβ hd2_U1)
    · change 0 < U.u₂.1 * (z.1 - y.1) + U.u₂.2 * (z.2 - y.2)
      rw [hzx, hzy]
      have : U.u₂.1 * (α * d₁.1 + β * d₂.1) + U.u₂.2 * (α * d₁.2 + β * d₂.2) =
          α * (U.u₂.1 * d₁.1 + U.u₂.2 * d₁.2) + β * (U.u₂.1 * d₂.1 + U.u₂.2 * d₂.2) := by ring
      rw [this]; exact add_pos (mul_pos hα hd1_U2) (mul_pos hβ hd2_U2)
  · have hεx : ε < |(x.1 - y.1) * r₀.2 - (x.2 - y.2) * r₀.1| /
        (|(x.1 - y.1) * r₀.1 + (x.2 - y.2) * r₀.2| + 1) := by
      have hne : F.Nonempty := ⟨x, hx⟩
      have hinf : εF ≤ |(x.1 - y.1) * r₀.2 - (x.2 - y.2) * r₀.1| /
          (|(x.1 - y.1) * r₀.1 + (x.2 - y.2) * r₀.2| + 1) := by
        dsimp [εF]; rw [dif_pos hne]
        exact Finset.inf'_le _ hx
      exact lt_of_lt_of_le hε_lt_F hinf
    have hmul : ε * |(x.1 - y.1) * r₀.1 + (x.2 - y.2) * r₀.2| <
        |(x.1 - y.1) * r₀.2 - (x.2 - y.2) * r₀.1| := by
      have hlt : ε * (|(x.1 - y.1) * r₀.1 + (x.2 - y.2) * r₀.2| + 1) <
          |(x.1 - y.1) * r₀.2 - (x.2 - y.2) * r₀.1| :=
        (lt_div_iff₀ (by positivity : 0 < |(x.1 - y.1) * r₀.1 + (x.2 - y.2) * r₀.2| + 1)).mp hεx
      linarith
    have h1_eq : n₁.1 * (x.1 - y.1) + n₁.2 * (x.2 - y.2) =
        ((x.1 - y.1) * r₀.2 - (x.2 - y.2) * r₀.1) +
        ε * ((x.1 - y.1) * r₀.1 + (x.2 - y.2) * r₀.2) := by
      dsimp [n₁]; ring
    have h2_eq : n₂.1 * (x.1 - y.1) + n₂.2 * (x.2 - y.2) =
        ((x.1 - y.1) * r₀.2 - (x.2 - y.2) * r₀.1) * (-1) +
        ε * ((x.1 - y.1) * r₀.1 + (x.2 - y.2) * r₀.2) := by
      dsimp [n₂]; ring
    dsimp [OpenWedge.MemExt, R]
    rcases lt_or_gt_of_ne (hx_det_ne x hx) with hlt | hgt
    · left; rw [h1_eq]; rw [abs_of_neg hlt] at hmul
      linarith only [(pos_sub_of_eps_abs (le_of_lt hε_pos) hmul).1]
    · right; rw [h2_eq]; rw [abs_of_pos hgt] at hmul
      linarith only [(pos_sub_of_eps_abs (le_of_lt hε_pos) hmul).1]

private lemma subwedge_avoiding_finset (U : OpenWedge) (F : Finset (ℝ × ℝ)) (hF : U.y ∉ F) :
    ∃ R : OpenWedge, R.y = U.y ∧ (∀ z : ℝ × ℝ, R.MemOpen z → U.MemOpen z) ∧
      (∀ x ∈ F, R.MemExt x) := by
  let y := U.y
  let p₀ : ℝ × ℝ := (y.1 + (SixWedges.dir1 U).1 + (SixWedges.dir2 U).1,
                     y.2 + (SixWedges.dir1 U).2 + (SixWedges.dir2 U).2)
  let d₀ : ℝ × ℝ := (p₀.1 - y.1, p₀.2 - y.2)
  let v₀ : ℝ × ℝ := (-d₀.2, d₀.1)
  have hd_in_U1 : 0 < U.u₁.1 * d₀.1 + U.u₁.2 * d₀.2 := by
    have : U.u₁.1 * d₀.1 + U.u₁.2 * d₀.2 = U.u₁.1 * U.u₂.2 - U.u₁.2 * U.u₂.1 := by
      dsimp [d₀, p₀, SixWedges.dir1, SixWedges.dir2]; ring
    rw [this]; exact U.h_nondeg
  have hd_in_U2 : 0 < U.u₂.1 * d₀.1 + U.u₂.2 * d₀.2 := by
    have : U.u₂.1 * d₀.1 + U.u₂.2 * d₀.2 = U.u₁.1 * U.u₂.2 - U.u₁.2 * U.u₂.1 := by
      dsimp [d₀, p₀, SixWedges.dir1, SixWedges.dir2]; ring
    rw [this]; exact U.h_nondeg
  let u1d : ℝ := U.u₁.1 * d₀.1 + U.u₁.2 * d₀.2
  let u1v : ℝ := U.u₁.1 * v₀.1 + U.u₁.2 * v₀.2
  let u2d : ℝ := U.u₂.1 * d₀.1 + U.u₂.2 * d₀.2
  let u2v : ℝ := U.u₂.1 * v₀.1 + U.u₂.2 * v₀.2
  let tBound : ℝ := min (u1d / (|u1v| + 1)) (u2d / (|u2v| + 1)) / 2
  have htBound_pos : 0 < tBound := by
    dsimp [tBound]
    positivity
  let badT : Finset ℝ := F.image (fun x =>
    -((x.1 - y.1) * d₀.2 - (x.2 - y.2) * d₀.1) / ((x.1 - y.1) * v₀.2 - (x.2 - y.2) * v₀.1))
  obtain ⟨t, ht_mem⟩ := (Set.Ioo_infinite htBound_pos).sdiff badT.finite_toSet |>.nonempty
  have ht_pos : 0 < t := ht_mem.1.1
  have ht_lt : t < tBound := ht_mem.1.2
  have ht_nb : t ∉ badT := by simpa using ht_mem.2
  let r₀ : ℝ × ℝ := (d₀.1 + t * v₀.1, d₀.2 + t * v₀.2)
  have hr₀_1 : 0 < U.u₁.1 * r₀.1 + U.u₁.2 * r₀.2 := by
    have hlt : |t * u1v| < u1d := by
      rw [abs_mul, abs_of_pos ht_pos]
      have h1 : t < u1d / (|u1v| + 1) := by
        have := min_le_left (u1d / (|u1v| + 1)) (u2d / (|u2v| + 1))
        dsimp [tBound] at ht_lt; linarith
      have h2 := (lt_div_iff₀ (by positivity : 0 < |u1v| + 1)).mp h1
      nlinarith [abs_nonneg u1v]
    have heq : U.u₁.1 * r₀.1 + U.u₁.2 * r₀.2 = u1d + t * u1v := by dsimp [r₀, u1d, u1v]; ring
    rw [heq]; linarith [neg_abs_le (t * u1v)]
  have hr₀_2 : 0 < U.u₂.1 * r₀.1 + U.u₂.2 * r₀.2 := by
    have hlt : |t * u2v| < u2d := by
      rw [abs_mul, abs_of_pos ht_pos]
      have h1 : t < u2d / (|u2v| + 1) := by
        have := min_le_right (u1d / (|u1v| + 1)) (u2d / (|u2v| + 1))
        dsimp [tBound] at ht_lt; linarith
      have h2 := (lt_div_iff₀ (by positivity : 0 < |u2v| + 1)).mp h1
      nlinarith [abs_nonneg u2v]
    have heq : U.u₂.1 * r₀.1 + U.u₂.2 * r₀.2 = u2d + t * u2v := by dsimp [r₀, u2d, u2v]; ring
    rw [heq]; linarith [neg_abs_le (t * u2v)]
  have hx_det_ne : ∀ x ∈ F, (x.1 - y.1) * r₀.2 - (x.2 - y.2) * r₀.1 ≠ 0 := by
    intro x hx h0
    have hden_eq : (x.1 - y.1) * v₀.2 - (x.2 - y.2) * v₀.1 =
        (x.1 - y.1) * d₀.1 + (x.2 - y.2) * d₀.2 := by dsimp [v₀]; ring
    by_cases hden0 : (x.1 - y.1) * v₀.2 - (x.2 - y.2) * v₀.1 = 0
    · have hnum0 : (x.1 - y.1) * d₀.2 - (x.2 - y.2) * d₀.1 = 0 := by
        have hid : (x.1 - y.1) * r₀.2 - (x.2 - y.2) * r₀.1 =
            ((x.1 - y.1) * d₀.2 - (x.2 - y.2) * d₀.1) +
            t * ((x.1 - y.1) * v₀.2 - (x.2 - y.2) * v₀.1) := by dsimp [r₀]; ring
        rw [hid, hden0, mul_zero, add_zero] at h0; exact h0
      have hd0_sq : 0 < d₀.1 ^ 2 + d₀.2 ^ 2 := by
        have hnz : d₀.1 ≠ 0 ∨ d₀.2 ≠ 0 := by
          by_contra hno; push Not at hno
          rw [hno.1, hno.2, mul_zero, mul_zero, add_zero] at hd_in_U1; exact lt_irrefl 0 hd_in_U1
        rcases hnz with h1 | h2
        · exact add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero h1) (sq_nonneg _)
        · exact add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_ne_zero h2)
      have hx1 : (d₀.1 ^ 2 + d₀.2 ^ 2) * (x.1 - y.1) = 0 := by
        rw [hden_eq] at hden0; linear_combination d₀.1 * hden0 + d₀.2 * hnum0
      have hx2 : (d₀.1 ^ 2 + d₀.2 ^ 2) * (x.2 - y.2) = 0 := by
        rw [hden_eq] at hden0; linear_combination d₀.2 * hden0 - d₀.1 * hnum0
      have hxy : x = y := by
        ext <;> linarith [(mul_eq_zero.mp hx1).resolve_left (ne_of_gt hd0_sq),
                          (mul_eq_zero.mp hx2).resolve_left (ne_of_gt hd0_sq)]
      exact hF (by dsimp [y] at hxy; rw [← hxy]; exact hx)
    · apply ht_nb
      refine Finset.mem_image.mpr ⟨x, hx, ?_⟩
      have hid : (x.1 - y.1) * r₀.2 - (x.2 - y.2) * r₀.1 =
          ((x.1 - y.1) * d₀.2 - (x.2 - y.2) * d₀.1) +
          t * ((x.1 - y.1) * v₀.2 - (x.2 - y.2) * v₀.1) := by dsimp [r₀]; ring
      rw [hid] at h0
      field_simp [hden0]
      linarith
  exact subwedge_from_ray U F r₀ hr₀_1 hr₀_2 hx_det_ne

/-- General-`n` instantiation of `Sec2To5Interface P S w` for every `3 ≤ n`. -/
theorem mk_sec2To5Interface_general {n : ℕ} (hn : 3 ≤ n) {P : Set (ℝ × ℝ)}
    {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ}
    (hPoly : ShatteredSimplePolygon P S w) : Sec2To5Interface P S w := by
  have hcert_eq : certifiedVertices S w = PolygonCore.certifiedSet P S w :=
    certifiedVertices_eq_certifiedSet hn hPoly
  have hB_eq : PolygonCore.hullVertices S = hullVertices S := hullVertices_eq S
  refine
    { three_halfplanes := ArrangementBounds.three_halfplanes_not_all_8
      two_hp_three_wedges := ArrangementBounds.two_hp_three_wedges_not_all_32
      cone_lemma := fun a b c w0 x _ _ _ _ _ hwb hwc hnwa ha hxb hxc hxab hxac hxwa =>
        (PolygonCore.mem_uCone_iff_inOpenTri a b c x).mp
          (PolygonCore.cone_of_shattered hPoly hwb hwc hnwa ha hxb hxc hxab hxac hxwa)
      wedge_extraction := ?_
      fan_corollary := ?_
      hidden_targets := ?_
      hidden_front := ?_
      front_restoration := ?_
      certified_structure := ?_
      side_preservation := ?_
      exit_edge_lemma := ?_
      endpoint_back_criterion := ?_
      half_plane_lemma := ?_ }
  · intro a b c W' U hab hac hbc hW' hUy hU_sep hX_in_U
    by_cases hX : ∃ x ∈ W', Sees P x (S a)
    · obtain ⟨p₀, hp₀W', hp₀_sees⟩ := hX
      obtain ⟨R₀, hR₀y, hR₀_test⟩ :=
        PolygonCore.wedge_extraction hPoly hab hbc hac hW' U hUy hU_sep hX_in_U
      obtain ⟨R, hRy, hR_open, hR_ext⟩ :=
        openWedge_inter_at_apex R₀ U (hR₀y.trans hUy.symm) p₀
          (((hR₀_test p₀ hp₀W').2).mp hp₀_sees) (hX_in_U p₀ hp₀W' hp₀_sees)
      refine ⟨R, hRy.trans hUy, fun z hz => ((hR_open z).mp hz).2, fun x hx => ⟨?_, ?_⟩⟩
      · rcases (hR₀_test x hx).1 with h1 | h2
        · by_cases hsees : Sees P x (S a)
          · exact Or.inl ((hR_open x).mpr ⟨h1, hX_in_U x hx hsees⟩)
          · exact Or.inr ((hR_ext x).mpr (Or.inl (((hR₀_test x hx).1).resolve_left
              (((hR₀_test x hx).2).not.mp hsees))))
        · exact Or.inr ((hR_ext x).mpr (Or.inl h2))
      · exact ⟨fun hsees => (hR_open x).mpr ⟨((hR₀_test x hx).2).mp hsees, hX_in_U x hx hsees⟩,
               fun hmem => ((hR₀_test x hx).2).mpr ((hR_open x).mp hmem).1⟩
    · push Not at hX
      let W'_idx : Finset (Finset (Fin n)) := Finset.univ.filter (fun T => w T ∈ W')
      let F : Finset (ℝ × ℝ) := W'_idx.image w
      have hF : U.y ∉ F := by
        intro hmem; rcases Finset.mem_image.mp hmem with ⟨T, _, heq⟩
        exact hPoly.s_ne_w a T (hUy.symm.trans heq.symm)
      obtain ⟨R, hRy, hRU, hRF⟩ := subwedge_avoiding_finset U F hF
      refine ⟨R, hRy.trans hUy, hRU, fun x hx => ?_⟩
      obtain ⟨T, _, _, rfl⟩ := hW' hx
      have hext := hRF (w T) (Finset.mem_image_of_mem w (Finset.mem_filter.mpr ⟨Finset.mem_univ T, hx⟩))
      refine ⟨Or.inr hext, fun hsees => absurd hsees (hX (w T) hx), fun hopen => ?_⟩
      rcases hext with h1 | h2 <;> [linarith [hopen.1]; linarith [hopen.2]]
  · intro Tw F a hFT ha_not ha_conv
    rw [Set.union_singleton] at ha_conv
    obtain ⟨R, _, hR_test⟩ := PolygonCore.fan hPoly hFT ha_not ha_conv
    exact ⟨R, hR_test⟩
  · intro T hTB htarg
    rw [← hB_eq] at hTB
    apply PolygonCore.hidden_targets hPoly T hTB
    intro t ht
    obtain ⟨b, c, Tv, hb, hc, _, hbTv, hcTv, htTv, htri⟩ := htarg t ht
    rw [← hB_eq] at hb hc
    exact ⟨b, hb, c, hc, Tv, (hPoly.shatters Tv b).mpr hbTv, (hPoly.shatters Tv c).mpr hcTv,
      fun h => htTv ((hPoly.shatters Tv t).mp h), htri⟩
  · intro C Tv f b c hCB hC3 hf hbf hfc hbTv hcTv hfTv hfront
    have hCB' : C ⊆ PolygonCore.hullVertices S := hB_eq.symm ▸ hCB
    obtain ⟨htri, hall⟩ := PolygonCore.hidden_front_vertex hPoly C hCB' hC3 Tv hf hbf.1 hfc.2.1
      ((isCCWEdge_iff_isCCWHullEdge hPoly C b f).mp hbf)
      ((isCCWEdge_iff_isCCWHullEdge hPoly C f c).mp hfc)
      (isFrontVertex_of_isFrontVertexOf hPoly hCB hC3 hfront)
      ((hPoly.shatters Tv b).mpr hbTv) ((hPoly.shatters Tv c).mpr hcTv)
      (fun h => hfTv ((hPoly.shatters Tv f).mp h))
    refine ⟨htri, fun Tx hbTx hcTx => ?_⟩
    obtain ⟨hx_tri, hx_front⟩ := hall Tx ((hPoly.shatters Tx b).mpr hbTx) ((hPoly.shatters Tx c).mpr hcTx)
    exact ⟨hx_tri, isFrontVertexOf_of_isFrontVertex hPoly hf hx_front⟩
  · intro C D' f v hCD' hD'_conv hC3 _ hfront
    have hD'3 : 3 ≤ D'.card := le_trans hC3 (Finset.card_le_card hCD')
    have hD'_img_conv : PolygonCore.IsConvexPos (D'.image S) := by
      refine ⟨fun p hp hmem => ?_, fun x hx y hy z hz hxy hyz hxz => ?_⟩
      · rcases Finset.mem_image.mp hp with ⟨i, hi, rfl⟩
        refine hD'_conv i hi (convexHull_mono ?_ hmem)
        intro q hq
        rcases Finset.mem_image.mp (Finset.mem_erase.mp hq).2 with ⟨j, hj, rfl⟩
        exact Finset.mem_image.mpr ⟨j, Finset.mem_erase.mpr
          ⟨fun h => (Finset.mem_erase.mp hq).1 (congrArg S h), hj⟩, rfl⟩
      · rcases Finset.mem_image.mp hx with ⟨ix, _, rfl⟩
        rcases Finset.mem_image.mp hy with ⟨iy, _, rfl⟩
        rcases Finset.mem_image.mp hz with ⟨iz, _, rfl⟩
        exact hPoly.no_three_collinear _ _ _ (Or.inl ⟨ix, rfl⟩) (Or.inl ⟨iy, rfl⟩) (Or.inl ⟨iz, rfl⟩)
          hxy hyz hxz
    obtain ⟨cycC⟩ := exists_ccwCycle S C (fun a _ b _ h => hPoly.s_inj h)
      (fun a _ b _ c _ hab hbc hac => orient_S_S_S_ne hPoly hab hbc hac)
      (fun i hi hmem => hD'_conv i (hCD' hi) (convexHull_mono (by
        intro q hq; rcases Finset.mem_image.mp hq with ⟨j, hj, rfl⟩
        exact Finset.mem_image_of_mem S (Finset.mem_erase.mpr
          ⟨(Finset.mem_erase.mp hj).1, hCD' (Finset.mem_erase.mp hj).2⟩)) hmem))
      (show C.card = (C.card - 3) + 3 by omega)
    obtain ⟨cycD'⟩ := exists_ccwCycle S D' (fun a _ b _ h => hPoly.s_inj h)
      (fun a _ b _ c _ hab hbc hac => orient_S_S_S_ne hPoly hab hbc hac)
      hD'_conv (show D'.card = (D'.card - 3) + 3 by omega)
    obtain ⟨iC, rfl⟩ := ccwCycle_exists_index cycC hfront.1
    have eC1 := ccwCycle_isCCWEdge cycC (iC - 1); rw [sub_add_cancel] at eC1
    have eC2 := ccwCycle_isCCWEdge cycC iC
    have hoC := (isFrontVertexOf_iff_ccwCycle cycC iC v).mp hfront
    have hfD' : cycC.toFun iC ∈ D' := hCD' hfront.1
    obtain ⟨iD, hiD⟩ := ccwCycle_exists_index cycD' hfD'
    have eD1 := ccwCycle_isCCWEdge cycD' (iD - 1); rw [sub_add_cancel, hiD] at eD1
    have eD2 := ccwCycle_isCCWEdge cycD' iD; rw [hiD] at eD2
    exact isFrontVertexOf_of_isFrontVertex hPoly hfD'
      (PolygonCore.front_restoration (Finset.image_subset_image hCD') hD'_img_conv
        (Finset.mem_image_of_mem S hfront.1)
        ⟨S (cycC.toFun (iC - 1)), S (cycC.toFun (iC + 1)),
          (isCCWEdge_iff_isCCWHullEdge hPoly C _ _).mp eC1,
          (isCCWEdge_iff_isCCWHullEdge hPoly C _ _).mp eC2, hoC.1, hoC.2⟩
        ((isCCWEdge_iff_isCCWHullEdge hPoly D' _ _).mp eD1)
        ((isCCWEdge_iff_isCCWHullEdge hPoly D' _ _).mp eD2))
  · dsimp only []; rw [hcert_eq]
    let B := hullVertices S
    let H := PolygonCore.certifiedSet P S w
    let D := B \ H
    refine ⟨?_, ?_⟩
    · by_cases hHne : H.Nonempty
      · have hB3 : 3 ≤ B.card := PolygonCore.hullVertices_card_ge_three hn hPoly
        obtain ⟨cb⟩ := PolygonCore.exists_cyclicSubsetBoundary hPoly (Finset.Subset.refl B) hB3
        have ⟨h₀, hh₀⟩ := hHne
        obtain ⟨vc⟩ := PolygonCore.exists_q_visibleContour hPoly hn cb (Finset.mem_filter.mp hh₀).2
        obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, h5⟩ :=
          PolygonCore.certified_structure hPoly hn cb vc hHne
        rwa [interiorPoints_eq S] at h5
      · have hHempty : PolygonCore.certifiedSet P S w = ∅ := Finset.not_nonempty_iff_eq_empty.mp hHne
        rw [hHempty, Finset.card_empty, add_zero]
        have h0 := PolygonCore.hidden_targets hPoly ∅ (Finset.empty_subset B) (fun _ h => by simp at h)
        rw [interiorPoints_eq S] at h0; simpa using h0
    · intro hHne
      have hB3 : 3 ≤ B.card := PolygonCore.hullVertices_card_ge_three hn hPoly
      obtain ⟨cb⟩ := PolygonCore.exists_cyclicSubsetBoundary hPoly (Finset.Subset.refl B) hB3
      have ⟨h₀, hh₀⟩ := hHne
      obtain ⟨vc⟩ := PolygonCore.exists_q_visibleContour hPoly hn cb (Finset.mem_filter.mp hh₀).2
      obtain ⟨k_f, k_g, l, r, hkf0, hkfg, hkg_lt, hl_eq, hr_eq, hlD, hrD, hlr, hblock, hpart_ii, _⟩ :=
        PolygonCore.certified_structure hPoly hn cb vc hHne
      haveI : NeZero (cb.m + 3) := ⟨by omega⟩
      have hcb_mem : ∀ j : Fin (cb.m + 3), cb.p_idx j ∈ B := fun j => by
        have h := Finset.mem_image_of_mem cb.p_idx (Finset.mem_univ j); rwa [cb.hp_idx_img] at h
      have hcb_ex : ∀ x ∈ B, ∃ k : ℕ, k < cb.m + 3 ∧ cb.p_idx (PolygonCore.finShift vc.i_max k) = x := by
        intro x hx; rw [← cb.hp_idx_img] at hx
        rcases Finset.mem_image.mp hx with ⟨j, _, rfl⟩
        refine ⟨(j - vc.i_max).val, (j - vc.i_max).isLt, ?_⟩
        rw [PolygonCore.finShift_eq_add vc.i_max (j - vc.i_max).isLt]; simp [add_sub_cancel]
      have hd_pos : ∀ d ∈ D, d ≠ l → d ≠ r → 0 < orient2D (S l) (S r) (S d) := by
        intro d hd hdl hdr
        obtain ⟨kd, hkd_lt, hkd_eq⟩ := hcb_ex d (Finset.mem_sdiff.mp hd).1
        have hkd_notH : ¬ (k_f ≤ kd ∧ kd ≤ k_g) := by
          rw [hblock kd hkd_lt, hkd_eq]; exact (Finset.mem_sdiff.mp hd).2
        have hkd_ne_l : kd ≠ k_f - 1 := fun h => hdl (by rw [← hkd_eq, hl_eq, h])
        have hkd_ne_r : kd ≠ k_g + 1 := fun h => hdr (by rw [← hkd_eq, hr_eq, h])
        have hd_vc := vc.hd_lt
        have h_cyc : PolygonCore.CyclicOrder (PolygonCore.finShift vc.i_max (k_f - 1))
            (PolygonCore.finShift vc.i_max (k_g + 1)) (PolygonCore.finShift vc.i_max kd) := by
          rcases (by omega : kd < k_f - 1 ∨ k_g + 1 < kd) with hlt | hgt
          · exact PolygonCore.cyclicOrder_cycle (PolygonCore.cyclicOrder_finShift vc.i_max hlt (by omega) (by omega))
          · exact PolygonCore.cyclicOrder_finShift vc.i_max (by omega) hgt hkd_lt
        rw [← hkd_eq, hl_eq, hr_eq]; exact cb.hcyc _ _ _ h_cyc
      refine ⟨l, r, hlD, hrD, hlr, fun _ => ⟨hlD, hrD, hlr, hd_pos⟩, ?_, hd_pos, ?_, ?_, ?_, ?_⟩
      · intro h hh
        obtain ⟨kh, hkh_lt, hkh_eq⟩ := hcb_ex h (Finset.filter_subset _ _ hh)
        have hkh_range : k_f ≤ kh ∧ kh ≤ k_g := (hblock kh hkh_lt).mpr (by rw [hkh_eq]; exact hh)
        have hd_vc := vc.hd_lt
        have hpos := cb.hcyc _ _ _ (PolygonCore.cyclicOrder_finShift vc.i_max (by omega : k_f - 1 < kh) (by omega : kh < k_g + 1) (by omega))
        rw [hkh_eq, ← hl_eq, ← hr_eq] at hpos; rw [orient2D_swap23]; linarith
      · exact fun h T hh hlT hrT => hpart_ii h hh T ((hPoly.shatters T l).mpr hlT) ((hPoly.shatters T r).mpr hrT)
      · intro d hd hdl hdr x _
        have hD3 : 3 ≤ D.card := by
          have hsub : {l, r, d} ⊆ D := by
            intro z hz; simp only [Finset.mem_insert, Finset.mem_singleton] at hz
            rcases hz with rfl | rfl | rfl <;> assumption
          have h3 : ({l, r, d} : Finset (Fin n)).card = 3 := by
            rw [Finset.card_insert_of_notMem, Finset.card_pair hdr.symm]; simp [hlr, hdl.symm]
          exact h3 ▸ Finset.card_le_card hsub
        obtain ⟨cycB⟩ := exists_ccwCycle S B (fun a _ b _ h => hPoly.s_inj h)
          (fun a _ b _ c _ hab hbc hac => orient_S_S_S_ne hPoly hab hbc hac)
          (hullVertices_convexPos S Finset.Subset.rfl) (show B.card = (B.card - 3) + 3 by omega)
        obtain ⟨cycD⟩ := exists_ccwCycle S D (fun a _ b _ h => hPoly.s_inj h)
          (fun a _ b _ c _ hab hbc hac => orient_S_S_S_ne hPoly hab hbc hac)
          (hullVertices_convexPos S Finset.sdiff_subset)
          (show D.card = (D.card - 3) + 3 by omega)
        obtain ⟨kd, hkd_lt, hkd_eq⟩ := hcb_ex d (Finset.mem_sdiff.mp hd).1
        have hkd_notH : ¬ (k_f ≤ kd ∧ kd ≤ k_g) := by
          rw [hblock kd hkd_lt, hkd_eq]; exact (Finset.mem_sdiff.mp hd).2
        have hkd_ne_l : kd ≠ k_f - 1 := fun h => hdl (by rw [← hkd_eq, hl_eq, h])
        have hkd_ne_r : kd ≠ k_g + 1 := fun h => hdr (by rw [← hkd_eq, hr_eq, h])
        let kp := if kd = 0 then cb.m + 2 else kd - 1
        have hkp_lt : kp < cb.m + 3 := by dsimp [kp]; split_ifs <;> omega
        have hp_D : cb.p_idx (PolygonCore.finShift vc.i_max kp) ∈ D := Finset.mem_sdiff.mpr
          ⟨hcb_mem _, by rw [← hblock kp hkp_lt]; dsimp [kp]; split_ifs; have := vc.hd_lt; omega; omega⟩
        have hp0B : IsCCWEdge S B (cb.p_idx (PolygonCore.finShift vc.i_max kp)) d := by
          refine ⟨hcb_mem _, (Finset.mem_sdiff.mp hd).1, fun heq => ?_, fun z hz hzp hzd => ?_⟩
          · have hsub := congrArg (· - vc.i_max) (cb.hp_idx_inj (heq.trans hkd_eq.symm))
            rw [PolygonCore.finShift_eq_add vc.i_max hkp_lt, PolygonCore.finShift_eq_add vc.i_max hkd_lt,
              add_sub_cancel_left, add_sub_cancel_left] at hsub
            have hv := congrArg Fin.val hsub; dsimp [kp] at hv; split_ifs at hv <;> omega
          · obtain ⟨kz, hkz_lt, hkz_eq⟩ := hcb_ex z hz
            have hkz_p : kz ≠ kp := fun h => hzp (by rw [← hkz_eq, h])
            have hkz_d : kz ≠ kd := fun h => hzd (by rw [← hkz_eq, ← hkd_eq, h])
            have hcyc : PolygonCore.CyclicOrder (PolygonCore.finShift vc.i_max kp)
                (PolygonCore.finShift vc.i_max kd) (PolygonCore.finShift vc.i_max kz) := by
              dsimp [kp] at hkz_p ⊢; split_ifs at hkz_p ⊢ with h0
              · subst h0; exact PolygonCore.cyclicOrder_cycle (PolygonCore.cyclicOrder_cycle
                  (PolygonCore.cyclicOrder_finShift vc.i_max (by omega : 0 < kz) (by omega : kz < cb.m + 2) (by omega)))
              · rcases (by omega : kz < kd - 1 ∨ kd < kz) with hlt | hgt
                · exact PolygonCore.cyclicOrder_cycle (PolygonCore.cyclicOrder_finShift vc.i_max hlt (by omega) hkd_lt)
                · exact PolygonCore.cyclicOrder_finShift vc.i_max (by omega) hgt hkz_lt
            rw [← hkz_eq, ← hkd_eq]; exact cb.hcyc _ _ _ hcyc
        let ks := if kd + 1 = cb.m + 3 then 0 else kd + 1
        have hks_lt : ks < cb.m + 3 := by dsimp [ks]; split_ifs <;> omega
        have hs_D : cb.p_idx (PolygonCore.finShift vc.i_max ks) ∈ D := Finset.mem_sdiff.mpr
          ⟨hcb_mem _, by rw [← hblock ks hks_lt]; dsimp [ks]; split_ifs; omega; have := vc.hd_lt; omega⟩
        have hs0B : IsCCWEdge S B d (cb.p_idx (PolygonCore.finShift vc.i_max ks)) := by
          refine ⟨(Finset.mem_sdiff.mp hd).1, hcb_mem _, fun heq => ?_, fun z hz hzd hzs => ?_⟩
          · have hsub := congrArg (· - vc.i_max) (cb.hp_idx_inj (hkd_eq.trans heq))
            rw [PolygonCore.finShift_eq_add vc.i_max hkd_lt, PolygonCore.finShift_eq_add vc.i_max hks_lt,
              add_sub_cancel_left, add_sub_cancel_left] at hsub
            have hv := congrArg Fin.val hsub; dsimp [ks] at hv; split_ifs at hv <;> omega
          · obtain ⟨kz, hkz_lt, hkz_eq⟩ := hcb_ex z hz
            have hkz_d : kz ≠ kd := fun h => hzd (by rw [← hkz_eq, ← hkd_eq, h])
            have hkz_s : kz ≠ ks := fun h => hzs (by rw [← hkz_eq, h])
            have hcyc : PolygonCore.CyclicOrder (PolygonCore.finShift vc.i_max kd)
                (PolygonCore.finShift vc.i_max ks) (PolygonCore.finShift vc.i_max kz) := by
              dsimp [ks] at hkz_s ⊢; split_ifs at hkz_s ⊢ with hmax
              · rw [show kd = cb.m + 2 by omega] at hkz_d ⊢
                exact PolygonCore.cyclicOrder_cycle (PolygonCore.cyclicOrder_cycle
                  (PolygonCore.cyclicOrder_finShift vc.i_max (by omega : 0 < kz) (by omega : kz < cb.m + 2) (by omega)))
              · rcases (by omega : kz < kd ∨ kd + 1 < kz) with hlt | hgt
                · exact PolygonCore.cyclicOrder_cycle (PolygonCore.cyclicOrder_finShift vc.i_max hlt (by omega) (by omega : kd + 1 < cb.m + 3))
                · exact PolygonCore.cyclicOrder_finShift vc.i_max (by omega) hgt hkz_lt
            rw [← hkz_eq, ← hkd_eq]; exact cb.hcyc _ _ _ hcyc
        have hp0D_edge : IsCCWEdge S D _ d := ⟨hp_D, hd, hp0B.2.2.1, fun z hz => hp0B.2.2.2 z (Finset.sdiff_subset hz)⟩
        have hs0D_edge : IsCCWEdge S D d _ := ⟨hd, hs_D, hs0B.2.2.1, fun z hz => hs0B.2.2.2 z (Finset.sdiff_subset hz)⟩
        exact ⟨⟨fun hB => by rw [isCCWEdge_unique_pred cycB hB hp0B]; exact hp0D_edge,
                fun hD => by rw [isCCWEdge_unique_pred cycD hD hp0D_edge]; exact hp0B⟩,
               ⟨fun hB => by rw [isCCWEdge_unique_succ cycB hB hs0B]; exact hs0D_edge,
                fun hD => by rw [isCCWEdge_unique_succ cycD hD hs0D_edge]; exact hs0B⟩⟩
      · intro hH1 h hh
        obtain ⟨kh, hkh_lt, hkh_eq⟩ := hcb_ex h (Finset.filter_subset _ _ hh)
        have hkh_range : k_f ≤ kh ∧ kh ≤ k_g := (hblock kh hkh_lt).mpr (by rw [hkh_eq]; exact hh)
        have hkf_inH : cb.p_idx (PolygonCore.finShift vc.i_max k_f) ∈ H := by
          rw [← hblock k_f (by have := vc.hd_lt; omega)]; exact ⟨le_rfl, hkfg⟩
        have hkg_inH : cb.p_idx (PolygonCore.finShift vc.i_max k_g) ∈ H := by
          rw [← hblock k_g (by have := vc.hd_lt; omega)]; exact ⟨hkfg, le_rfl⟩
        have hfg_eq : k_f = k_g := by
          by_contra hne
          have hneq_pts : cb.p_idx (PolygonCore.finShift vc.i_max k_f) ≠
              cb.p_idx (PolygonCore.finShift vc.i_max k_g) := by
            intro heq
            have hsub := congrArg (· - vc.i_max) (cb.hp_idx_inj heq)
            have := vc.hd_lt
            rw [PolygonCore.finShift_eq_add vc.i_max (by omega : k_f < cb.m + 3),
              PolygonCore.finShift_eq_add vc.i_max (by omega : k_g < cb.m + 3),
              add_sub_cancel_left, add_sub_cancel_left] at hsub
            exact hne (by simpa using congrArg Fin.val hsub)
          have h2 : 2 ≤ H.card := Finset.one_lt_card.mpr ⟨_, hkf_inH, _, hkg_inH, hneq_pts⟩
          dsimp [H] at h2; omega
        have hkh_kf : kh = k_f := by omega
        have hkh_kg : kh = k_g := by omega
        have hd_vc := vc.hd_lt
        refine ⟨⟨Finset.sdiff_subset hlD, Finset.filter_subset _ _ hh,
            fun h' => (Finset.mem_sdiff.mp hlD).2 (h' ▸ hh), fun z hz hzl hzh => ?_⟩,
          ⟨Finset.filter_subset _ _ hh, Finset.sdiff_subset hrD,
            fun h' => (Finset.mem_sdiff.mp hrD).2 (h'.symm ▸ hh), fun z hz hzh hzr => ?_⟩⟩
        · obtain ⟨kz, hkz_lt, hkz_eq⟩ := hcb_ex z hz
          have hkz_l : kz ≠ k_f - 1 := fun e => hzl (by rw [← hkz_eq, hl_eq, e])
          have hkz_h : kz ≠ k_f := fun e => hzh (by rw [← hkz_eq, ← hkh_eq, hkh_kf, e])
          have hcyc : PolygonCore.CyclicOrder (PolygonCore.finShift vc.i_max (k_f - 1))
              (PolygonCore.finShift vc.i_max k_f) (PolygonCore.finShift vc.i_max kz) := by
            rcases (by omega : kz < k_f - 1 ∨ k_f < kz) with hlt | hgt
            · exact PolygonCore.cyclicOrder_cycle (PolygonCore.cyclicOrder_finShift vc.i_max hlt (by omega) (by omega))
            · exact PolygonCore.cyclicOrder_finShift vc.i_max (by omega) hgt hkz_lt
          rw [← hkz_eq, ← hkh_eq, hkh_kf, hl_eq]; exact cb.hcyc _ _ _ hcyc
        · obtain ⟨kz, hkz_lt, hkz_eq⟩ := hcb_ex z hz
          have hkz_h : kz ≠ k_g := fun e => hzh (by rw [← hkz_eq, ← hkh_eq, hkh_kg, e])
          have hkz_r : kz ≠ k_g + 1 := fun e => hzr (by rw [← hkz_eq, hr_eq, e])
          have hcyc : PolygonCore.CyclicOrder (PolygonCore.finShift vc.i_max k_g)
              (PolygonCore.finShift vc.i_max (k_g + 1)) (PolygonCore.finShift vc.i_max kz) := by
            rcases (by omega : kz < k_g ∨ k_g + 1 < kz) with hlt | hgt
            · exact PolygonCore.cyclicOrder_cycle (PolygonCore.cyclicOrder_finShift vc.i_max hlt (by omega) (by omega))
            · exact PolygonCore.cyclicOrder_finShift vc.i_max (by omega) hgt hkz_lt
          rw [← hkz_eq, ← hkh_eq, hkh_kg, hr_eq]; exact cb.hcyc _ _ _ hcyc
      · intro hH2
        have hkf_lt_kg : k_f < k_g := by
          by_contra hge
          have hsub : H ⊆ {cb.p_idx (PolygonCore.finShift vc.i_max k_f)} := by
            intro h hh
            obtain ⟨kh, hkh_lt, hkh_eq⟩ := hcb_ex h (Finset.filter_subset _ _ hh)
            have hkr := (hblock kh hkh_lt).mpr (by rw [hkh_eq]; exact hh)
            simp [← hkh_eq, show kh = k_f by omega]
          have hle : H.card ≤ 1 := (Finset.card_le_card hsub).trans (Finset.card_singleton _).le
          dsimp [H] at hle; omega
        have hd_vc := vc.hd_lt
        let h1 := cb.p_idx (PolygonCore.finShift vc.i_max k_f)
        let h2 := cb.p_idx (PolygonCore.finShift vc.i_max (k_f + 1))
        have hh1 : h1 ∈ H := by rw [← hblock k_f (by omega)]; exact ⟨le_rfl, le_of_lt hkf_lt_kg⟩
        have hh2 : h2 ∈ H := by rw [← hblock (k_f + 1) (by omega)]; exact ⟨by omega, by omega⟩
        have h12 : h1 ≠ h2 := by
          intro heq
          have hsub := congrArg (· - vc.i_max) (cb.hp_idx_inj heq)
          rw [PolygonCore.finShift_eq_add vc.i_max (by omega : k_f < cb.m + 3),
            PolygonCore.finShift_eq_add vc.i_max (by omega : k_f + 1 < cb.m + 3),
            add_sub_cancel_left, add_sub_cancel_left] at hsub
          have hv := congrArg Fin.val hsub; dsimp at hv; omega
        refine ⟨h1, h2, hh1, hh2, h12,
          ⟨Finset.sdiff_subset hlD, Finset.filter_subset _ _ hh1,
            fun heq => (Finset.mem_sdiff.mp hlD).2 (heq ▸ hh1), fun z hz hzl hzh => ?_⟩,
          ⟨Finset.filter_subset _ _ hh1, Finset.filter_subset _ _ hh2, h12, fun z hz hzh1 hzh2 => ?_⟩⟩
        · obtain ⟨kz, hkz_lt, hkz_eq⟩ := hcb_ex z hz
          have hkz_l : kz ≠ k_f - 1 := fun e => hzl (by rw [← hkz_eq, hl_eq, e])
          have hkz_h1 : kz ≠ k_f := fun e => hzh (by rw [← hkz_eq, e])
          have hcyc : PolygonCore.CyclicOrder (PolygonCore.finShift vc.i_max (k_f - 1))
              (PolygonCore.finShift vc.i_max k_f) (PolygonCore.finShift vc.i_max kz) := by
            rcases (by omega : kz < k_f - 1 ∨ k_f < kz) with hlt | hgt
            · exact PolygonCore.cyclicOrder_cycle (PolygonCore.cyclicOrder_finShift vc.i_max hlt (by omega) (by omega))
            · exact PolygonCore.cyclicOrder_finShift vc.i_max (by omega) hgt hkz_lt
          rw [← hkz_eq, hl_eq]; exact cb.hcyc _ _ _ hcyc
        · obtain ⟨kz, hkz_lt, hkz_eq⟩ := hcb_ex z hz
          have hkz_h1 : kz ≠ k_f := fun e => hzh1 (by rw [← hkz_eq, e])
          have hkz_h2 : kz ≠ k_f + 1 := fun e => hzh2 (by rw [← hkz_eq, e])
          have hcyc : PolygonCore.CyclicOrder (PolygonCore.finShift vc.i_max k_f)
              (PolygonCore.finShift vc.i_max (k_f + 1)) (PolygonCore.finShift vc.i_max kz) := by
            rcases (by omega : kz < k_f ∨ k_f + 1 < kz) with hlt | hgt
            · exact PolygonCore.cyclicOrder_cycle (PolygonCore.cyclicOrder_finShift vc.i_max hlt (by omega) (by omega))
            · exact PolygonCore.cyclicOrder_finShift vc.i_max (by omega) hgt hkz_lt
          rw [← hkz_eq]; exact cb.hcyc _ _ _ hcyc
  · dsimp only []; rw [hcert_eq]
    intro hHne hD5 Q M₀ hQD hQ2 hM0M hQ_back
    let B := hullVertices S
    let H := PolygonCore.certifiedSet P S w
    let D := B \ H
    have hB3 : 3 ≤ B.card := PolygonCore.hullVertices_card_ge_three hn hPoly
    obtain ⟨cb⟩ := PolygonCore.exists_cyclicSubsetBoundary hPoly (Finset.Subset.refl B) hB3
    have ⟨h₀, hh₀⟩ := hHne
    obtain ⟨vc⟩ := PolygonCore.exists_q_visibleContour hPoly hn cb (Finset.mem_filter.mp hh₀).2
    obtain ⟨k_f, k_g, l, r, hkf0, hkfg, hkg_lt, hl_eq, hr_eq, _, _, _, hblock, _, _⟩ :=
      PolygonCore.certified_structure hPoly hn cb vc hHne
    have hM0' : M₀ ⊆ PolygonCore.interiorPoints S ∪ H := by
      intro x hx
      have hxM := (Finset.mem_sdiff.mp (hM0M hx)).2
      by_cases hxB : x ∈ B
      · exact Finset.mem_union.mpr (Or.inr (by by_contra hxH; exact hxM (Finset.mem_sdiff.mpr ⟨hxB, hxH⟩)))
      · exact Finset.mem_union.mpr (Or.inl (Finset.mem_sdiff.mpr ⟨Finset.mem_univ x, hxB⟩))
    have hQ_back' : ∀ p ∈ Q, ∃ O : Finset (Fin n), p ∉ O ∧
        (∀ a ∈ O ∩ D, ∀ b ∈ O ∩ D, ¬ PolygonCore.IsCCWHullEdge (B.image S) (S a) (S b)) ∧
        PolygonCore.IsBackVertex (B.image S) (w (Finset.univ \ O)) (S p) := by
      intro p hpQ
      obtain ⟨O, hpO, hOnoadj, hp_back⟩ := hQ_back p hpQ
      refine ⟨O, hpO, fun a ha b hb h_edge => hOnoadj a ha b hb
        ((isCCWEdge_iff_isCCWHullEdge hPoly B a b).mpr h_edge), ?_⟩
      exact (isBackVertexOf_iff_isBackVertex hPoly Finset.Subset.rfl hB3).mp hp_back
    have hsp := (PolygonCore.side_preservation hPoly hn cb vc hHne hD5 hkf0 hkfg hkg_lt
      hl_eq hr_eq hblock).2 Q hQD hQ2 hQ_back' M₀ hM0'
    intro h hh
    obtain ⟨a, haF, b, hbF, hall⟩ := hsp h hh
    have hab : a ≠ b := by
      intro heq; subst heq
      have htri := hall {a} ((hPoly.shatters {a} a).mpr (by simp)) ((hPoly.shatters {a} a).mpr (by simp))
      have hha : h ≠ a := by
        intro h'; subst h'
        have hhM0 : h ∉ M₀ := (Finset.mem_sdiff.mp hh).2
        rcases Finset.mem_union.mp haF with haD | haM0
        · exact (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp haD).1).2 (Finset.mem_sdiff.mp hh).1
        · exact hhM0 haM0
      rcases htri with ⟨μ₁, μ₂, μ₃, _, _, _, hsum, hx1, hx2⟩
      exact orient_w_S_S_ne hPoly {a} hha.symm
        (by unfold orient2D; rw [hx1, hx2, show μ₁ = 1 - μ₂ - μ₃ by linarith]; ring)
    refine ⟨a, b, haF, hbF, hab, fun x hx => ?_⟩
    obtain ⟨Tx, hsub, _, rfl⟩ := hx
    exact hall Tx ((hPoly.shatters Tx a).mpr (hsub (by simp))) ((hPoly.shatters Tx b).mpr (hsub (by simp)))
  · dsimp only []; rw [hcert_eq]
    intro hD3 y hyM
    let B := hullVertices S
    let H := PolygonCore.certifiedSet P S w
    let D := B \ H
    have hyM' : y ∈ PolygonCore.interiorPoints S ∪ H := by
      have hy := (Finset.mem_sdiff.mp hyM).2
      by_cases hyB : y ∈ B
      · exact Finset.mem_union.mpr (Or.inr (by by_contra hyH; exact hy (Finset.mem_sdiff.mpr ⟨hyB, hyH⟩)))
      · exact Finset.mem_union.mpr (Or.inl (Finset.mem_sdiff.mpr ⟨Finset.mem_univ y, hyB⟩))
    obtain ⟨dc⟩ := PolygonCore.exists_cyclicSubsetBoundary hPoly Finset.sdiff_subset hD3
    obtain ⟨⟨i, ⟨hpos_i, htri_i⟩, huniq_i⟩, himp_i⟩ := PolygonCore.exit_edge hPoly hn hD3 dc y hyM'
    obtain ⟨hall_i, hB_edge⟩ := himp_i i hpos_i htri_i
    have hD3' : 3 ≤ D.card := hD3
    obtain ⟨cycD⟩ := exists_ccwCycle S D (fun a _ b _ h => hPoly.s_inj h)
      (fun a _ b _ c _ hab hbc hac => orient_S_S_S_ne hPoly hab hbc hac)
      (hullVertices_convexPos S Finset.sdiff_subset)
      (show D.card = (D.card - 3) + 3 by omega)
    have hdc_mem : ∀ j : Fin (dc.m + 3), dc.p_idx j ∈ D := fun j => by
      have h := Finset.mem_image_of_mem dc.p_idx (Finset.mem_univ j); rwa [dc.hp_idx_img] at h
    have hdc_edge : ∀ j : Fin (dc.m + 3), IsCCWEdge S D (dc.p_idx j) (dc.p_idx (j + 1)) := by
      intro j
      haveI : NeZero (dc.m + 3) := ⟨by omega⟩
      have hj1_ne : j ≠ j + 1 := fin_add_one_ne_self j
      refine ⟨hdc_mem j, hdc_mem (j + 1), fun h => hj1_ne (dc.hp_idx_inj h), fun r hr hr1 hr2 => ?_⟩
      change r ∈ PolygonCore.hullVertices S \ PolygonCore.certifiedSet P S w at hr
      rw [← dc.hp_idx_img] at hr
      rcases Finset.mem_image.mp hr with ⟨k, _, rfl⟩
      have hcyc := PolygonCore.cyclicOrder_succ (by omega : 3 ≤ dc.m + 3)
        (fun h => hr1 (congrArg dc.p_idx h)) (fun h => hr2 (congrArg dc.p_idx h))
      rw [show (⟨1 % (dc.m + 3), Nat.mod_lt 1 (by omega)⟩ : Fin (dc.m + 3)) = 1 from
        Fin.ext (Nat.mod_eq_of_lt (by omega))] at hcyc
      exact dc.hcyc j (j + 1) k hcyc
    refine ⟨dc.p_idx i, dc.p_idx (i + 1), hdc_edge i, hpos_i, htri_i, ?_, ?_, ?_⟩
    · intro l r hHne _ hHneg heq
      obtain ⟨h, hh⟩ := hHne
      have hB_lr := (isCCWEdge_iff_isCCWHullEdge hPoly B (dc.p_idx i) (dc.p_idx (i + 1))).mpr (hB_edge ⟨h, hh⟩)
      have heq1 : dc.p_idx i = l := (Prod.ext_iff.mp heq).1
      have heq2 : dc.p_idx (i + 1) = r := (Prod.ext_iff.mp heq).2
      have hhl : h ≠ l := fun e => (Finset.mem_sdiff.mp (heq1 ▸ hdc_mem i)).2 (e ▸ hh)
      have hhr : h ≠ r := fun e => (Finset.mem_sdiff.mp (heq2 ▸ hdc_mem (i + 1))).2 (e ▸ hh)
      have hpos := hB_lr.2.2.2 h (Finset.filter_subset _ _ hh) (heq1 ▸ hhl) (heq2 ▸ hhr)
      have hneg := hHneg h hh; rw [heq1, heq2] at hpos; linarith
    · intro x hx; obtain ⟨Tx, hsub, _, rfl⟩ := hx
      exact hall_i Tx ((hPoly.shatters Tx _).mpr (hsub (by simp))) ((hPoly.shatters Tx _).mpr (hsub (by simp)))
    · intro u' v' huv' hpos' hy_conv
      have hu'D : u' ∈ PolygonCore.hullVertices S \ PolygonCore.certifiedSet P S w := huv'.1
      rw [← dc.hp_idx_img] at hu'D
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hu'D
      have hv'eq : v' = dc.p_idx (j + 1) := isCCWEdge_unique_succ cycD huv' (hdc_edge j)
      subst hv'eq
      have hy_notD : y ∉ D := (Finset.mem_sdiff.mp hyM).2
      have hyn1 : y ≠ dc.p_idx j := fun h => hy_notD (h ▸ hdc_mem j)
      have hyn2 : y ≠ dc.p_idx (j + 1) := fun h => hy_notD (h ▸ hdc_mem (j + 1))
      have hopen : PolygonCore.InOpenTri (w D) (S (dc.p_idx j)) (S (dc.p_idx (j + 1))) (S y) :=
        PolygonCore.inOpenTri_of_noncollinear_inClosedTri ((inClosedTri_iff_mem_convexHull _ _ _ _).mpr hy_conv)
          (orient_S_S_S_ne hPoly (hdc_edge j).2.2.1 hyn2.symm hyn1.symm)
          (orient_S_w_S_ne hPoly hyn2.symm D)
          (orient_w_S_S_ne hPoly D hyn1.symm)
      have hj_eq : j = i := huniq_i j ⟨hpos', hopen⟩
      subst hj_eq; exact ⟨rfl, rfl⟩
  · dsimp only []; rw [hcert_eq]
    intro hHne hD5 l r p y_other hlD hrD hlr hed hHneg hp_end ⟨O, hpO, hOnoadj, hp_back⟩
    let B := hullVertices S
    let H := PolygonCore.certifiedSet P S w
    let D := B \ H
    have hB3 : 3 ≤ B.card := PolygonCore.hullVertices_card_ge_three hn hPoly
    have hD3 : 3 ≤ D.card := by dsimp [D, B, H] at hD5 ⊢; omega
    obtain ⟨cb⟩ := PolygonCore.exists_cyclicSubsetBoundary hPoly (Finset.Subset.refl B) hB3
    have ⟨h₀, hh₀⟩ := hHne
    obtain ⟨vc⟩ := PolygonCore.exists_q_visibleContour hPoly hn cb (Finset.mem_filter.mp hh₀).2
    obtain ⟨k_f, k_g, l₀, r₀, hkf0, hkfg, hkg_lt, hl0_eq, hr0_eq, hl0D, hr0D, hl0r0, hblock, _, _⟩ :=
      PolygonCore.certified_structure hPoly hn cb vc hHne
    have hcb_ex : ∀ x ∈ B, ∃ k : ℕ, k < cb.m + 3 ∧ cb.p_idx (PolygonCore.finShift vc.i_max k) = x := by
      intro x hx; rw [← cb.hp_idx_img] at hx
      rcases Finset.mem_image.mp hx with ⟨j, _, rfl⟩
      refine ⟨(j - vc.i_max).val, (j - vc.i_max).isLt, ?_⟩
      rw [PolygonCore.finShift_eq_add vc.i_max (j - vc.i_max).isLt]; simp [add_sub_cancel]
    have hl_eq_l0 : l = l₀ ∧ r = r₀ := by
      obtain ⟨kl, hkl_lt, hkl_eq⟩ := hcb_ex l (Finset.sdiff_subset hlD)
      obtain ⟨kr, hkr_lt, hkr_eq⟩ := hcb_ex r (Finset.sdiff_subset hrD)
      have hkl_notH : ¬ (k_f ≤ kl ∧ kl ≤ k_g) := by rw [hblock kl hkl_lt, hkl_eq]; exact (Finset.mem_sdiff.mp hlD).2
      have hkr_notH : ¬ (k_f ≤ kr ∧ kr ≤ k_g) := by rw [hblock kr hkr_lt, hkr_eq]; exact (Finset.mem_sdiff.mp hrD).2
      have hd_vc := vc.hd_lt
      have h_lr_neg : orient2D (S l) (S r) (S h₀) < 0 := hHneg h₀ hh₀
      obtain ⟨kh0, hkh0_lt, hkh0_eq⟩ := hcb_ex h₀ (Finset.filter_subset _ _ hh₀)
      have hkh0_range : k_f ≤ kh0 ∧ kh0 ≤ k_g := (hblock kh0 hkh0_lt).mpr (by rw [hkh0_eq]; exact hh₀)
      have hkl_ne_r : kl ≠ kr := fun e => hlr (by rw [← hkl_eq, ← hkr_eq, e])
      have h_not_cyc_lr_h : ¬ PolygonCore.CyclicOrder (PolygonCore.finShift vc.i_max kl)
          (PolygonCore.finShift vc.i_max kr) (PolygonCore.finShift vc.i_max kh0) := by
        intro hcyc; have hpos := cb.hcyc _ _ _ hcyc; rw [hkl_eq, hkr_eq, hkh0_eq] at hpos; linarith
      have hidx_ne : ∀ {k₁ k₂ : ℕ} (hk1 : k₁ < cb.m + 3) (hk2 : k₂ < cb.m + 3), k₁ ≠ k₂ →
          cb.p_idx (PolygonCore.finShift vc.i_max k₁) ≠ cb.p_idx (PolygonCore.finShift vc.i_max k₂) := by
        intro k₁ k₂ hk1 hk2 hne heq
        have hsub := congrArg (· - vc.i_max) (cb.hp_idx_inj heq)
        rw [PolygonCore.finShift_eq_add vc.i_max hk1, PolygonCore.finShift_eq_add vc.i_max hk2,
          add_sub_cancel_left, add_sub_cancel_left] at hsub
        exact hne (by simpa using congrArg Fin.val hsub)
      have hkl_lt_kf : kl < k_f := by
        by_contra hge; have hkl_gt : k_g < kl := by omega
        rcases (by omega : kr < k_f ∨ k_g < kr) with hkr_lt' | hkr_gt'
        · exact h_not_cyc_lr_h (PolygonCore.cyclicOrder_cycle (PolygonCore.cyclicOrder_cycle
            (PolygonCore.cyclicOrder_finShift vc.i_max (by omega : kr < kh0) (by omega) hkl_lt)))
        · have hkr_lt_kl : kr < kl := by
            by_contra hle; exact h_not_cyc_lr_h (PolygonCore.cyclicOrder_cycle
              (PolygonCore.cyclicOrder_finShift vc.i_max (by omega) (by omega : kl < kr) hkr_lt))
          have hpos_l0 := hed.2.2.2 l₀ hl0D
            (by rw [hl0_eq, ← hkl_eq]; exact hidx_ne (by omega) hkl_lt (by omega))
            (by rw [hl0_eq, ← hkr_eq]; exact hidx_ne (by omega) hkr_lt (by omega))
          have hneg_l0 := cb.hcyc _ _ _ (PolygonCore.cyclicOrder_cycle
            (PolygonCore.cyclicOrder_finShift vc.i_max (by omega : k_f - 1 < kr) hkr_lt_kl hkl_lt))
          rw [← hl0_eq, hkr_eq, hkl_eq] at hneg_l0
          have : orient2D (S r) (S l) (S l₀) = -orient2D (S l) (S r) (S l₀) := by unfold orient2D; ring
          linarith
      have hkr_gt_kg : k_g < kr := by
        by_contra hle; have hkr_lt' : kr < k_f := by omega
        have hkr_lt_kl : kr < kl := by
          by_contra hle'; exact h_not_cyc_lr_h
            (PolygonCore.cyclicOrder_finShift vc.i_max (by omega : kl < kr) (by omega) hkh0_lt)
        have hpos_r0 := hed.2.2.2 r₀ hr0D
          (by rw [hr0_eq, ← hkl_eq]; exact hidx_ne (by omega) hkl_lt (by omega))
          (by rw [hr0_eq, ← hkr_eq]; exact hidx_ne (by omega) hkr_lt (by omega))
        have hneg_r0 := cb.hcyc _ _ _
          (PolygonCore.cyclicOrder_finShift vc.i_max hkr_lt_kl (by omega : kl < k_g + 1) (by omega))
        rw [← hr0_eq, hkr_eq, hkl_eq] at hneg_r0
        have : orient2D (S r) (S l) (S r₀) = -orient2D (S l) (S r) (S r₀) := by unfold orient2D; ring
        linarith
      have hkl_eq_kf : kl = k_f - 1 := by
        by_contra hne; have hlt : kl < k_f - 1 := by omega
        have hpos_l0 := hed.2.2.2 l₀ hl0D
          (by rw [hl0_eq, ← hkl_eq]; exact hidx_ne (by omega) hkl_lt (by omega))
          (by rw [hl0_eq, ← hkr_eq]; exact hidx_ne (by omega) hkr_lt (by omega))
        have hneg_l0 := cb.hcyc _ _ _ (PolygonCore.cyclicOrder_cycle (PolygonCore.cyclicOrder_cycle
          (PolygonCore.cyclicOrder_finShift vc.i_max hlt (by omega : k_f - 1 < kr) hkr_lt)))
        rw [← hl0_eq, hkr_eq, hkl_eq] at hneg_l0
        have : orient2D (S r) (S l) (S l₀) = -orient2D (S l) (S r) (S l₀) := by unfold orient2D; ring
        linarith
      have hkr_eq_kg : kr = k_g + 1 := by
        by_contra hne; have hgt : k_g + 1 < kr := by omega
        have hpos_r0 := hed.2.2.2 r₀ hr0D
          (by rw [hr0_eq, ← hkl_eq]; exact hidx_ne (by omega) hkl_lt (by omega))
          (by rw [hr0_eq, ← hkr_eq]; exact hidx_ne (by omega) hkr_lt (by omega))
        have hneg_r0 := cb.hcyc _ _ _ (PolygonCore.cyclicOrder_cycle (PolygonCore.cyclicOrder_cycle
          (PolygonCore.cyclicOrder_finShift vc.i_max (by omega : kl < k_g + 1) hgt hkr_lt)))
        rw [← hr0_eq, hkr_eq, hkl_eq] at hneg_r0
        have : orient2D (S r) (S l) (S r₀) = -orient2D (S l) (S r) (S r₀) := by unfold orient2D; ring
        linarith
      exact ⟨by rw [← hkl_eq, hkl_eq_kf, ← hl0_eq], by rw [← hkr_eq, hkr_eq_kg, ← hr0_eq]⟩
    rcases hl_eq_l0 with ⟨rfl, rfl⟩
    obtain ⟨dc⟩ := PolygonCore.exists_cyclicSubsetBoundary hPoly Finset.sdiff_subset hD3
    obtain ⟨h_part1, h_part2⟩ := PolygonCore.endpoint_back_vertex_criterion hPoly hn cb vc hHne hD5 dc
      hkf0 hkfg hkg_lt hl0_eq hr0_eq hblock hp_end O hpO
      (fun a ha b hb he => hOnoadj a ha b hb ((isCCWEdge_iff_isCCWHullEdge hPoly B a b).mpr he))
      ((isBackVertexOf_iff_isBackVertex hPoly Finset.Subset.rfl hB3).mp hp_back)
    have hdc_mem : ∀ j : Fin (dc.m + 3), dc.p_idx j ∈ D := fun j => by
      have h := Finset.mem_image_of_mem dc.p_idx (Finset.mem_univ j); rwa [dc.hp_idx_img] at h
    have hdc_edge : ∀ j : Fin (dc.m + 3), IsCCWEdge S D (dc.p_idx j) (dc.p_idx (j + 1)) := by
      intro j
      haveI : NeZero (dc.m + 3) := ⟨by omega⟩
      refine ⟨hdc_mem j, hdc_mem (j + 1), fun h => fin_add_one_ne_self j (dc.hp_idx_inj h), fun z hz hz1 hz2 => ?_⟩
      change z ∈ PolygonCore.hullVertices S \ PolygonCore.certifiedSet P S w at hz
      rw [← dc.hp_idx_img] at hz
      rcases Finset.mem_image.mp hz with ⟨k, _, rfl⟩
      have hcyc := PolygonCore.cyclicOrder_succ (by omega : 3 ≤ dc.m + 3)
        (fun h => hz1 (congrArg dc.p_idx h)) (fun h => hz2 (congrArg dc.p_idx h))
      rw [show (⟨1 % (dc.m + 3), Nat.mod_lt 1 (by omega)⟩ : Fin (dc.m + 3)) = 1 from
        Fin.ext (Nat.mod_eq_of_lt (by omega))] at hcyc
      exact dc.hcyc j (j + 1) k hcyc
    have hD3' : 3 ≤ D.card := hD3
    obtain ⟨cycD⟩ := exists_ccwCycle S D (fun a _ b _ h => hPoly.s_inj h)
      (fun a _ b _ c _ hab hbc hac => orient_S_S_S_ne hPoly hab hbc hac)
      (hullVertices_convexPos S Finset.sdiff_subset)
      (show D.card = (D.card - 3) + 3 by omega)
    refine ⟨?_, fun ⟨O', hyO', hO'noadj, hy_back⟩ => h_part2 O' hyO'
      (fun a ha b hb he => hO'noadj a ha b hb ((isCCWEdge_iff_isCCWHullEdge hPoly B a b).mpr he))
      ((isBackVertexOf_iff_isBackVertex hPoly Finset.Subset.rfl hB3).mp hy_back)⟩
    intro h hh u v huv htri
    by_cases huv_lr : (u = l ∧ v = r)
    · rcases hp_end with ⟨_, hyr⟩ | ⟨_, hyl⟩
      · exact Or.inr (huv_lr.2.trans hyr.symm)
      · exact Or.inl (huv_lr.1.trans hyl.symm)
    · have huD : u ∈ PolygonCore.hullVertices S \ PolygonCore.certifiedSet P S w := huv.1
      rw [← dc.hp_idx_img] at huD
      rcases Finset.mem_image.mp huD with ⟨i, _, rfl⟩
      have hv_eq : v = dc.p_idx (i + 1) := isCCWEdge_unique_succ cycD huv (hdc_edge i)
      subst hv_eq
      have h_not_both_lr : ¬ ((dc.p_idx i = l ∨ dc.p_idx i = r) ∧
          (dc.p_idx (i + 1) = l ∨ dc.p_idx (i + 1) = r)) := by
        rintro ⟨hi | hi, hi1 | hi1⟩
        · exact huv.2.2.1 (hi.trans hi1.symm)
        · exact huv_lr ⟨hi, hi1⟩
        · have hlt : ({l, r} : Finset (Fin n)).card < D.card := by
            have := Finset.card_le_two (a := l) (b := r); omega
          obtain ⟨d, hdD, hd2⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hd2
          have ho1 := huv.2.2.2 d hdD (hi ▸ hd2.2) (hi1 ▸ hd2.1)
          obtain ⟨kd, hkd_lt, hkd_eq⟩ := hcb_ex d (Finset.sdiff_subset hdD)
          have hkd_notH : ¬ (k_f ≤ kd ∧ kd ≤ k_g) := by
            rw [hblock kd hkd_lt, hkd_eq]; exact (Finset.mem_sdiff.mp hdD).2
          have hkd_ne_l : kd ≠ k_f - 1 := fun e => hd2.1 (by rw [← hkd_eq, hl0_eq, e])
          have hkd_ne_r : kd ≠ k_g + 1 := fun e => hd2.2 (by rw [← hkd_eq, hr0_eq, e])
          have hd_vc := vc.hd_lt
          have hcyc : PolygonCore.CyclicOrder (PolygonCore.finShift vc.i_max (k_f - 1))
              (PolygonCore.finShift vc.i_max (k_g + 1)) (PolygonCore.finShift vc.i_max kd) := by
            rcases (by omega : kd < k_f - 1 ∨ k_g + 1 < kd) with hlt' | hgt'
            · exact PolygonCore.cyclicOrder_cycle (PolygonCore.cyclicOrder_finShift vc.i_max hlt' (by omega) (by omega))
            · exact PolygonCore.cyclicOrder_finShift vc.i_max (by omega) hgt' hkd_lt
          have ho2 := cb.hcyc _ _ _ hcyc
          rw [← hl0_eq, ← hr0_eq, hkd_eq] at ho2
          rw [hi, hi1] at ho1
          have : orient2D (S r) (S l) (S d) = -orient2D (S l) (S r) (S d) := by unfold orient2D; ring
          linarith
        · exact huv.2.2.1 (hi.trans hi1.symm)
      have hh_pos_uv : 0 < orient2D (S (dc.p_idx i)) (S (dc.p_idx (i + 1))) (S h) := by
        have hcb_mem : ∀ j : Fin (cb.m + 3), cb.p_idx j ∈ B := fun j => by
          have h' := Finset.mem_image_of_mem cb.p_idx (Finset.mem_univ j); rwa [cb.hp_idx_img] at h'
        have h_edge_B : ∀ d ∈ D, d ≠ l → d ≠ r → ∀ x ∈ D,
            (IsCCWEdge S D x d → IsCCWEdge S B x d) ∧ (IsCCWEdge S D d x → IsCCWEdge S B d x) := by
          intro d hd hdl hdr x _
          obtain ⟨kd, hkd_lt, hkd_eq⟩ := hcb_ex d (Finset.mem_sdiff.mp hd).1
          have hkd_notH : ¬ (k_f ≤ kd ∧ kd ≤ k_g) := by
            rw [hblock kd hkd_lt, hkd_eq]; exact (Finset.mem_sdiff.mp hd).2
          have hkd_ne_l : kd ≠ k_f - 1 := fun e => hdl (by rw [← hkd_eq, hl0_eq, e])
          have hkd_ne_r : kd ≠ k_g + 1 := fun e => hdr (by rw [← hkd_eq, hr0_eq, e])
          let kp := if kd = 0 then cb.m + 2 else kd - 1
          have hkp_lt : kp < cb.m + 3 := by dsimp [kp]; split_ifs <;> omega
          have hp_D : cb.p_idx (PolygonCore.finShift vc.i_max kp) ∈ D := Finset.mem_sdiff.mpr
            ⟨hcb_mem _, by rw [← hblock kp hkp_lt]; dsimp [kp]; split_ifs; have := vc.hd_lt; omega; omega⟩
          have hp_B : IsCCWEdge S B (cb.p_idx (PolygonCore.finShift vc.i_max kp)) d := by
            refine ⟨hcb_mem _, (Finset.mem_sdiff.mp hd).1, fun heq => ?_, fun z hz hzp hzd => ?_⟩
            · have hsub := congrArg (· - vc.i_max) (cb.hp_idx_inj (heq.trans hkd_eq.symm))
              rw [PolygonCore.finShift_eq_add vc.i_max hkp_lt, PolygonCore.finShift_eq_add vc.i_max hkd_lt,
                add_sub_cancel_left, add_sub_cancel_left] at hsub
              have hv := congrArg Fin.val hsub; dsimp [kp] at hv; split_ifs at hv <;> omega
            · obtain ⟨kz, hkz_lt, hkz_eq⟩ := hcb_ex z hz
              have hkz_p : kz ≠ kp := fun e => hzp (by rw [← hkz_eq, e])
              have hkz_d : kz ≠ kd := fun e => hzd (by rw [← hkz_eq, ← hkd_eq, e])
              have hcyc : PolygonCore.CyclicOrder (PolygonCore.finShift vc.i_max kp)
                  (PolygonCore.finShift vc.i_max kd) (PolygonCore.finShift vc.i_max kz) := by
                dsimp [kp] at hkz_p ⊢; split_ifs at hkz_p ⊢ with h0
                · subst h0; exact PolygonCore.cyclicOrder_cycle (PolygonCore.cyclicOrder_cycle
                    (PolygonCore.cyclicOrder_finShift vc.i_max (by omega : 0 < kz) (by omega : kz < cb.m + 2) (by omega)))
                · rcases (by omega : kz < kd - 1 ∨ kd < kz) with hlt' | hgt'
                  · exact PolygonCore.cyclicOrder_cycle (PolygonCore.cyclicOrder_finShift vc.i_max hlt' (by omega) hkd_lt)
                  · exact PolygonCore.cyclicOrder_finShift vc.i_max (by omega) hgt' hkz_lt
              rw [← hkz_eq, ← hkd_eq]; exact cb.hcyc _ _ _ hcyc
          let ks := if kd + 1 = cb.m + 3 then 0 else kd + 1
          have hks_lt : ks < cb.m + 3 := by dsimp [ks]; split_ifs <;> omega
          have hs_D : cb.p_idx (PolygonCore.finShift vc.i_max ks) ∈ D := Finset.mem_sdiff.mpr
            ⟨hcb_mem _, by rw [← hblock ks hks_lt]; dsimp [ks]; split_ifs; omega; have := vc.hd_lt; omega⟩
          have hs_B : IsCCWEdge S B d (cb.p_idx (PolygonCore.finShift vc.i_max ks)) := by
            refine ⟨(Finset.mem_sdiff.mp hd).1, hcb_mem _, fun heq => ?_, fun z hz hzd hzs => ?_⟩
            · have hsub := congrArg (· - vc.i_max) (cb.hp_idx_inj (hkd_eq.trans heq))
              rw [PolygonCore.finShift_eq_add vc.i_max hkd_lt, PolygonCore.finShift_eq_add vc.i_max hks_lt,
                add_sub_cancel_left, add_sub_cancel_left] at hsub
              have hv := congrArg Fin.val hsub; dsimp [ks] at hv; split_ifs at hv <;> omega
            · obtain ⟨kz, hkz_lt, hkz_eq⟩ := hcb_ex z hz
              have hkz_d : kz ≠ kd := fun e => hzd (by rw [← hkz_eq, ← hkd_eq, e])
              have hkz_s : kz ≠ ks := fun e => hzs (by rw [← hkz_eq, e])
              have hcyc : PolygonCore.CyclicOrder (PolygonCore.finShift vc.i_max kd)
                  (PolygonCore.finShift vc.i_max ks) (PolygonCore.finShift vc.i_max kz) := by
                dsimp [ks] at hkz_s ⊢; split_ifs at hkz_s ⊢ with hm
                · rw [show kd = cb.m + 2 by omega] at hkz_d ⊢
                  exact PolygonCore.cyclicOrder_cycle (PolygonCore.cyclicOrder_cycle
                    (PolygonCore.cyclicOrder_finShift vc.i_max (by omega : 0 < kz) (by omega : kz < cb.m + 2) (by omega)))
                · rcases (by omega : kz < kd ∨ kd + 1 < kz) with hlt' | hgt'
                  · exact PolygonCore.cyclicOrder_cycle (PolygonCore.cyclicOrder_finShift vc.i_max hlt' (by omega) (by omega : kd + 1 < cb.m + 3))
                  · exact PolygonCore.cyclicOrder_finShift vc.i_max (by omega) hgt' hkz_lt
              rw [← hkz_eq, ← hkd_eq]; exact cb.hcyc _ _ _ hcyc
          exact ⟨fun hD => by rw [isCCWEdge_unique_pred cycD hD ⟨hp_D, hd, hp_B.2.2.1, fun z hz => hp_B.2.2.2 z (Finset.sdiff_subset hz)⟩]; exact hp_B,
                 fun hD => by rw [isCCWEdge_unique_succ cycD hD ⟨hd, hs_D, hs_B.2.2.1, fun z hz => hs_B.2.2.2 z (Finset.sdiff_subset hz)⟩]; exact hs_B⟩
        have huv_B : IsCCWEdge S B (dc.p_idx i) (dc.p_idx (i + 1)) := by
          by_cases hu_lr : dc.p_idx i = l ∨ dc.p_idx i = r
          · have hv_not : dc.p_idx (i + 1) ≠ l ∧ dc.p_idx (i + 1) ≠ r := by
              by_contra hno; rw [not_and_or, not_not, not_not] at hno; exact h_not_both_lr ⟨hu_lr, hno⟩
            exact (h_edge_B (dc.p_idx (i + 1)) huv.2.1 hv_not.1 hv_not.2 (dc.p_idx i) huv.1).1 huv
          · push Not at hu_lr
            exact (h_edge_B (dc.p_idx i) huv.1 hu_lr.1 hu_lr.2 (dc.p_idx (i + 1)) huv.2.1).2 huv
        exact huv_B.2.2.2 h (Finset.filter_subset _ _ hh)
          (fun e => (Finset.mem_sdiff.mp huv.1).2 (e ▸ hh))
          (fun e => (Finset.mem_sdiff.mp huv.2.1).2 (e ▸ hh))
      have hpos : 0 < orient2D (S (dc.p_idx i)) (S (dc.p_idx (i + 1))) (w D) := by
        rcases htri with ⟨μ₁, μ₂, μ₃, hμ1, _, _, hsum, hx1, hx2⟩
        have hid := orient2D_convex_comb3 (S (dc.p_idx i)) (S (dc.p_idx (i + 1)))
          (w D) (S (dc.p_idx i)) (S (dc.p_idx (i + 1))) (S h) μ₁ μ₂ μ₃ hsum hx1 hx2
        simp only [orient2D_self_outer, orient2D_self_right, mul_zero, add_zero] at hid
        rw [hid] at hh_pos_uv; exact pos_of_mul_pos_right hh_pos_uv (le_of_lt hμ1)
      rcases h_part1 h hh i hpos htri with h' | h'
      · exact Or.inl h'.symm
      · exact Or.inr h'.symm
  · intro Tv Tq a p c hpTv haTv hcTv haTq hpTq hcTq ⟨hsap, hoap⟩ ⟨hspc, hopc⟩ hcross hiv
    have ha_ne0 : orient2D (w Tv) (w Tq) (S a) ≠ 0 :=
      fun h0 => by rw [OnSameSide, h0, zero_mul] at hsap; exact lt_irrefl 0 hsap
    have hor_ap : 0 < orient2D (w Tv) (S a) (S p) * orient2D (w Tv) (w Tq) (S p) := by
      have hmul : (orient2D (w Tv) (w Tq) (S a)) ^ 2 *
          (orient2D (w Tv) (S a) (S p) * orient2D (w Tv) (w Tq) (S p)) =
          (orient2D (w Tv) (S a) (S p) * orient2D (w Tv) (w Tq) (S a)) *
          (orient2D (w Tv) (w Tq) (S a) * orient2D (w Tv) (w Tq) (S p)) := by ring
      nlinarith [sq_pos_of_ne_zero ha_ne0, mul_pos (by linarith : 0 < orient2D (w Tv) (S a) (S p) * orient2D (w Tv) (w Tq) (S a)) hsap]
    have hor_pc : 0 < orient2D (w Tv) (S p) (S c) * orient2D (w Tv) (w Tq) (S p) := by
      unfold OnSameSide at *; linarith
    have hiv' : Sees P (w Tv) (w Tq) ∨
        ∃ ie : Fin n, Sees P (w Tv) (S ie) ∧ Sees P (w Tq) (S ie) ∧
          Sec5HP.SameSideOfLine (w Tv) (w Tq) (S ie) (S a) ∧
          0 < orient2D (w Tv) (S ie) (S a) * orient2D (w Tv) (w Tq) (S p) := by
      rcases hiv with hvq | ⟨e, heTv, heTq, he_same, he_ang2⟩
      · exact Or.inl hvq
      · right
        have he_ne0 : orient2D (w Tv) (w Tq) (S e) ≠ 0 :=
          fun h0 => by rw [OnSameSide, h0, zero_mul] at he_same; exact lt_irrefl 0 he_same
        have hsame_ep : 0 < orient2D (w Tv) (w Tq) (S e) * orient2D (w Tv) (w Tq) (S p) := by
          have hmul : (orient2D (w Tv) (w Tq) (S a)) ^ 2 *
              (orient2D (w Tv) (w Tq) (S e) * orient2D (w Tv) (w Tq) (S p)) =
              (orient2D (w Tv) (w Tq) (S e) * orient2D (w Tv) (w Tq) (S a)) *
              (orient2D (w Tv) (w Tq) (S a) * orient2D (w Tv) (w Tq) (S p)) := by ring
          unfold OnSameSide at he_same hsap
          nlinarith [sq_pos_of_ne_zero ha_ne0, mul_pos he_same hsap]
        have hmul : (orient2D (w Tv) (w Tq) (S e)) ^ 2 *
            (orient2D (w Tv) (S e) (S a) * orient2D (w Tv) (w Tq) (S p)) =
            (orient2D (w Tv) (S e) (S a) * orient2D (w Tv) (w Tq) (S e)) *
            (orient2D (w Tv) (w Tq) (S e) * orient2D (w Tv) (w Tq) (S p)) := by ring
        refine ⟨e, (hPoly.shatters Tv e).mpr heTv, (hPoly.shatters Tq e).mpr heTq, he_same, ?_⟩
        nlinarith [sq_pos_of_ne_zero he_ne0, mul_pos (by linarith : 0 < orient2D (w Tv) (S e) (S a) * orient2D (w Tv) (w Tq) (S e)) hsame_ep]
    obtain ⟨H_hp, hH_test, _⟩ := Sec5HP.half_plane_lemma_orient hPoly Tv Tq a p c
      ((hPoly.shatters Tv p).mpr hpTv)
      (fun h => haTv ((hPoly.shatters Tv a).mp h))
      (fun h => hcTv ((hPoly.shatters Tv c).mp h))
      ((hPoly.shatters Tq a).mpr haTq)
      ((hPoly.shatters Tq p).mpr hpTq)
      ((hPoly.shatters Tq c).mpr hcTq)
      hsap (by unfold OnSameSide at hspc; change 0 < orient2D (w Tv) (w Tq) (S c) * orient2D (w Tv) (w Tq) (S p); linarith)
      hor_ap hor_pc hcross hiv'
    exact ⟨H_hp, hH_test⟩


/-! ## 2. Two-Anchor Hexagon Lemmas (`Lemma 5.11` & `Lemma 5.12` of `upper_8.tex`) -/

section HexagonTwoAnchorHelpers

private def noAltBool4 (a b c d : Bool) : Bool :=
  !(((a != b) && (b != c)) && (c != d))

private def hexNoAlt4 (s0 s1 s2 s3 s4 s5 : Bool) : Bool :=
  noAltBool4 s0 s1 s2 s3 && noAltBool4 s0 s1 s2 s4 && noAltBool4 s0 s1 s2 s5 &&
  noAltBool4 s0 s1 s3 s4 && noAltBool4 s0 s1 s3 s5 && noAltBool4 s0 s1 s4 s5 &&
  noAltBool4 s0 s2 s3 s4 && noAltBool4 s0 s2 s3 s5 && noAltBool4 s0 s2 s4 s5 &&
  noAltBool4 s0 s3 s4 s5 && noAltBool4 s1 s2 s3 s4 && noAltBool4 s1 s2 s3 s5 &&
  noAltBool4 s1 s2 s4 s5 && noAltBool4 s1 s3 s4 s5 && noAltBool4 s2 s3 s4 s5

private def forallB (f : Bool → Bool) : Bool := f false && f true

private lemma forallB_true {f : Bool → Bool} (h : forallB f = true) (b : Bool) : f b = true := by
  cases b <;> simp only [forallB, Bool.and_eq_true] at h
  · exact h.1
  · exact h.2

private lemma not_all5_eq_bool {s0 s1 s2 s3 s4 s5 : Bool}
    (h : ¬ (s0 = s1 ∧ s0 = s2 ∧ s0 = s3 ∧ s0 = s4 ∧ s0 = s5)) :
    (!(s0 == s1 && s0 == s2 && s0 == s3 && s0 == s4 && s0 == s5)) = true := by
  cases s0 <;> cases s1 <;> cases s2 <;> cases s3 <;> cases s4 <;> cases s5 <;>
    first | rfl | exact False.elim (h ⟨rfl, rfl, rfl, rfl, rfl⟩)

private lemma imp_beq_bool {a b c : Bool} (h : a = b → c = a) :
    (!(a == b) || (c == a)) = true := by
  cases a <;> cases b <;> cases c <;>
    first | rfl | exact absurd (h rfl) (by decide)

private lemma ccw6_lt {n : ℕ} {S : Fin n → ℝ × ℝ} {D : Finset (Fin n)}
    (cycD : CCWCycle S D 3) {a b c : Fin 6} (hab : a < b) (hbc : b < c) :
    0 < orient2D (S (cycD.toFun a)) (S (cycD.toFun b)) (S (cycD.toFun c)) :=
  cycD.ccw_tri a b c hab hbc

private lemma hexNoAlt4_of_orientSign {n : ℕ} {S : Fin n → ℝ × ℝ} {D : Finset (Fin n)}
    (cycD : CCWCycle S D 3) (v q : ℝ × ℝ)
    (hvq : ∀ m : Fin 6, orient2D v q (S (cycD.toFun m)) ≠ 0) :
    hexNoAlt4
      (orientSign v q (S (cycD.toFun 0)))
      (orientSign v q (S (cycD.toFun 1)))
      (orientSign v q (S (cycD.toFun 2)))
      (orientSign v q (S (cycD.toFun 3)))
      (orientSign v q (S (cycD.toFun 4)))
      (orientSign v q (S (cycD.toFun 5))) = true := by
  have h4 : ∀ a b c d : Fin 6, a < b → b < c → c < d →
      noAltBool4 (orientSign v q (S (cycD.toFun a)))
        (orientSign v q (S (cycD.toFun b)))
        (orientSign v q (S (cycD.toFun c)))
        (orientSign v q (S (cycD.toFun d))) = true := by
    intro a b c d hab hbc hcd
    have hbcd := ccw6_lt cycD hbc hcd
    have hcab : 0 < orient2D (S (cycD.toFun c)) (S (cycD.toFun d)) (S (cycD.toFun a)) := by
      have h := ccw6_lt cycD (lt_trans hab hbc) hcd; unfold orient2D at h ⊢; linarith
    have hdab : 0 < orient2D (S (cycD.toFun d)) (S (cycD.toFun a)) (S (cycD.toFun b)) := by
      have h := ccw6_lt cycD hab (lt_trans hbc hcd); unfold orient2D at h ⊢; linarith
    have habc := ccw6_lt cycD hab hbc
    have halt := convex_fourgon_no_alternating_line
      (S (cycD.toFun a)) (S (cycD.toFun b)) (S (cycD.toFun c)) (S (cycD.toFun d)) v q
      hbcd hcab hdab habc
    rcases lt_or_gt_of_ne (hvq a) with ha | ha <;>
    rcases lt_or_gt_of_ne (hvq b) with hb | hb <;>
    rcases lt_or_gt_of_ne (hvq c) with hc | hc <;>
    rcases lt_or_gt_of_ne (hvq d) with hd | hd <;>
      simp [noAltBool4, orientSign, not_lt_of_gt, ha, hb, hc, hd] at halt ⊢
  dsimp [hexNoAlt4]
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨
    h4 0 1 2 3 ?_ ?_ ?_, h4 0 1 2 4 ?_ ?_ ?_⟩, h4 0 1 2 5 ?_ ?_ ?_⟩,
    h4 0 1 3 4 ?_ ?_ ?_⟩, h4 0 1 3 5 ?_ ?_ ?_⟩, h4 0 1 4 5 ?_ ?_ ?_⟩,
    h4 0 2 3 4 ?_ ?_ ?_⟩, h4 0 2 3 5 ?_ ?_ ?_⟩, h4 0 2 4 5 ?_ ?_ ?_⟩,
    h4 0 3 4 5 ?_ ?_ ?_⟩, h4 1 2 3 4 ?_ ?_ ?_⟩, h4 1 2 3 5 ?_ ?_ ?_⟩,
    h4 1 2 4 5 ?_ ?_ ?_⟩, h4 1 3 4 5 ?_ ?_ ?_⟩, h4 2 3 4 5 ?_ ?_ ?_⟩ <;> decide

private lemma hex_all_nf_not_all_same {n : ℕ} {S : Fin n → ℝ × ℝ} {D : Finset (Fin n)}
    (cycD : CCWCycle S D 3) (v q : ℝ × ℝ)
    (h_all_nf : ∀ m : Fin 6, 0 < orient2D (S (cycD.toFun m)) (S (cycD.toFun (m + 1))) v)
    (hvq : ∀ m : Fin 6, orient2D v q (S (cycD.toFun m)) ≠ 0) :
    ¬ (orientSign v q (S (cycD.toFun 0)) = orientSign v q (S (cycD.toFun 1)) ∧
       orientSign v q (S (cycD.toFun 0)) = orientSign v q (S (cycD.toFun 2)) ∧
       orientSign v q (S (cycD.toFun 0)) = orientSign v q (S (cycD.toFun 3)) ∧
       orientSign v q (S (cycD.toFun 0)) = orientSign v q (S (cycD.toFun 4)) ∧
       orientSign v q (S (cycD.toFun 0)) = orientSign v q (S (cycD.toFun 5))) := by
  rintro ⟨h1, h2, h3, h4, h5⟩
  cases hs0 : orientSign v q (S (cycD.toFun 0))
  · have hneg : ∀ m : Fin 6, orient2D v q (S (cycD.toFun m)) < 0 := fun m => by
      fin_cases m
      · exact (orientSign_eq_false_iff_of_ne_zero (hvq 0)).mp hs0
      · exact (orientSign_eq_false_iff_of_ne_zero (hvq 1)).mp (h1.symm.trans hs0)
      · exact (orientSign_eq_false_iff_of_ne_zero (hvq 2)).mp (h2.symm.trans hs0)
      · exact (orientSign_eq_false_iff_of_ne_zero (hvq 3)).mp (h3.symm.trans hs0)
      · exact (orientSign_eq_false_iff_of_ne_zero (hvq 4)).mp (h4.symm.trans hs0)
      · exact (orientSign_eq_false_iff_of_ne_zero (hvq 5)).mp (h5.symm.trans hs0)
    have hstep : ∀ m : Fin 6, AngleLt v q (S (cycD.toFun (m + 1))) (S (cycD.toFun m)) := fun m => by
      rw [angleLt_iff_neg_of_neg (hneg (m + 1)) (hneg m)]
      have hf := h_all_nf m; unfold orient2D at hf ⊢; linarith
    exact AngleLt.irrefl v q (S (cycD.toFun 0))
      ((hstep 5).trans ((hstep 4).trans ((hstep 3).trans ((hstep 2).trans ((hstep 1).trans (hstep 0))))))
  · have hpos : ∀ m : Fin 6, 0 < orient2D v q (S (cycD.toFun m)) := fun m => by
      fin_cases m
      · exact (orientSign_eq_true_iff _ _ _).mp hs0
      · exact (orientSign_eq_true_iff _ _ _).mp (h1.symm.trans hs0)
      · exact (orientSign_eq_true_iff _ _ _).mp (h2.symm.trans hs0)
      · exact (orientSign_eq_true_iff _ _ _).mp (h3.symm.trans hs0)
      · exact (orientSign_eq_true_iff _ _ _).mp (h4.symm.trans hs0)
      · exact (orientSign_eq_true_iff _ _ _).mp (h5.symm.trans hs0)
    have hstep : ∀ m : Fin 6, AngleLt v q (S (cycD.toFun m)) (S (cycD.toFun (m + 1))) := fun m => by
      rw [angleLt_iff_pos_of_pos (hpos m) (hpos (m + 1))]
      have hf := h_all_nf m; unfold orient2D at hf ⊢; linarith
    exact AngleLt.irrefl v q (S (cycD.toFun 0))
      ((hstep 0).trans ((hstep 1).trans ((hstep 2).trans ((hstep 3).trans ((hstep 4).trans (hstep 5))))))

private lemma exitTri_orientSign_of_endpoints {v q u0 v0 y : ℝ × ℝ}
    (hy : InIntTri v u0 v0 y) (hqu : orient2D v q u0 ≠ 0) (hqv : orient2D v q v0 ≠ 0)
    (heq : orientSign v q u0 = orientSign v q v0) :
    orientSign v q y = orientSign v q u0 := by
  rcases hy with ⟨_, μ₂, μ₃, _, hm2, hm3, hs, hy1, hy2⟩
  have hid := orient2D_convex_comb3 v q v u0 v0 y _ _ _ hs hy1 hy2
  rw [orient2D_self_outer, mul_zero, zero_add] at hid
  cases hsu : orientSign v q u0
  · have hu : orient2D v q u0 < 0 := (orientSign_eq_false_iff_of_ne_zero hqu).mp hsu
    have hv' : orient2D v q v0 < 0 := (orientSign_eq_false_iff_of_ne_zero hqv).mp (heq.symm.trans hsu)
    exact (orientSign_eq_false_iff _ _ _).mpr (le_of_lt (by rw [hid]; nlinarith))
  · have hu : 0 < orient2D v q u0 := (orientSign_eq_true_iff _ _ _).mp hsu
    have hv' : 0 < orient2D v q v0 := (orientSign_eq_true_iff _ _ _).mp (heq.symm.trans hsu)
    exact (orientSign_eq_true_iff _ _ _).mpr (by rw [hid]; nlinarith)

private lemma onSameSide_of_orientSign_eq {v q a b : ℝ × ℝ}
    (heq : orientSign v q a = orientSign v q b)
    (hqa : orient2D v q a ≠ 0) (hqb : orient2D v q b ≠ 0) :
    OnSameSide v q a b :=
  mul_pos_of_orientSign_eq hqa hqb rfl heq.symm

private lemma orientSign_eq_of_onSameSide {v q a b : ℝ × ℝ}
    (hss : OnSameSide v q a b) : orientSign v q a = orientSign v q b := by
  unfold OnSameSide at hss
  have hqa : orient2D v q a ≠ 0 := fun h => by rw [h, zero_mul] at hss; linarith
  have hqb : orient2D v q b ≠ 0 := fun h => by rw [h, mul_zero] at hss; linarith
  exact beq_iff_eq.mp ((sameSideBool_iff_sameSide hqa hqb).mpr hss)

private lemma exitTri_sameSide_in_L {v q u0 v0 y : ℝ × ℝ}
    (hy : InIntTri v u0 v0 y) (hss : OnSameSide v q u0 v0) :
    OnSameSide v q u0 y ∧ OnSameSide v q y v0 := by
  have hqu : orient2D v q u0 ≠ 0 := fun h => by unfold OnSameSide at hss; rw [h, zero_mul] at hss; linarith
  have hqv : orient2D v q v0 ≠ 0 := fun h => by unfold OnSameSide at hss; rw [h, mul_zero] at hss; linarith
  have heq := exitTri_orientSign_of_endpoints hy hqu hqv (orientSign_eq_of_onSameSide hss)
  have hqy : orient2D v q y ≠ 0 := by
    rcases hy with ⟨_, μ₂, μ₃, _, hm2, hm3, hs, hy1, hy2⟩
    have hid := orient2D_convex_comb3 v q v u0 v0 y _ _ _ hs hy1 hy2
    rw [orient2D_self_outer, mul_zero, zero_add] at hid
    rcases lt_or_gt_of_ne hqu with hn | hp
    · have hvn : orient2D v q v0 < 0 := by unfold OnSameSide at hss; nlinarith
      rw [hid]; linarith [mul_neg_of_pos_of_neg hm2 hn, mul_neg_of_pos_of_neg hm3 hvn]
    · have hvp : 0 < orient2D v q v0 := by unfold OnSameSide at hss; nlinarith
      rw [hid]; linarith [mul_pos hm2 hp, mul_pos hm3 hvp]
  exact ⟨onSameSide_of_orientSign_eq heq.symm hqu hqy,
    onSameSide_of_orientSign_eq (heq.trans (orientSign_eq_of_onSameSide hss)) hqy hqv⟩

private lemma vq_between_sameSide {v q a m b : ℝ × ℝ}
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

private lemma chain3_orient_pos {v q a b c : ℝ × ℝ}
    (hq_eq : orientSign v q a = orientSign v q b ∧ orientSign v q b = orientSign v q c)
    (hqa : orient2D v q a ≠ 0) (hqb : orient2D v q b ≠ 0) (hqc : orient2D v q c ≠ 0)
    (hab : 0 < orient2D v a b) (hbc : 0 < orient2D v b c) :
    0 < orient2D v a c := by
  cases hsa : orientSign v q a
  · have ha := (orientSign_eq_false_iff_of_ne_zero hqa).mp hsa
    have hb := (orientSign_eq_false_iff_of_ne_zero hqb).mp (hq_eq.1.symm.trans hsa)
    have hc := (orientSign_eq_false_iff_of_ne_zero hqc).mp (hq_eq.2.symm.trans (hq_eq.1.symm.trans hsa))
    have h1 := ((angleLt_iff_neg_of_neg hc hb).mpr (by unfold orient2D at hbc ⊢; linarith)).trans
      ((angleLt_iff_neg_of_neg hb ha).mpr (by unfold orient2D at hab ⊢; linarith))
    have hca := (angleLt_iff_neg_of_neg hc ha).mp h1
    unfold orient2D at hca ⊢; linarith
  · have ha := (orientSign_eq_true_iff _ _ _).mp hsa
    have hb := (orientSign_eq_true_iff _ _ _).mp (hq_eq.1.symm.trans hsa)
    have hc := (orientSign_eq_true_iff _ _ _).mp (hq_eq.2.symm.trans (hq_eq.1.symm.trans hsa))
    exact (angleLt_iff_pos_of_pos ha hc).mp
      (((angleLt_iff_pos_of_pos ha hb).mpr hab).trans ((angleLt_iff_pos_of_pos hb hc).mpr hbc))

private lemma chain4_orient_pos {v q a b c d : ℝ × ℝ}
    (hq_eq : orientSign v q a = orientSign v q b ∧
             orientSign v q b = orientSign v q c ∧
             orientSign v q c = orientSign v q d)
    (hqa : orient2D v q a ≠ 0) (hqb : orient2D v q b ≠ 0)
    (hqc : orient2D v q c ≠ 0) (hqd : orient2D v q d ≠ 0)
    (hab : 0 < orient2D v a b) (hbc : 0 < orient2D v b c) (hcd : 0 < orient2D v c d) :
    0 < orient2D v a c ∧ 0 < orient2D v b d ∧ 0 < orient2D v a d := by
  have hac := chain3_orient_pos ⟨hq_eq.1, hq_eq.2.1⟩ hqa hqb hqc hab hbc
  have hbd := chain3_orient_pos ⟨hq_eq.2.1, hq_eq.2.2⟩ hqb hqc hqd hbc hcd
  exact ⟨hac, hbd, chain3_orient_pos ⟨hq_eq.1, hq_eq.2.1.trans hq_eq.2.2⟩ hqa hqb hqd hab hbd⟩

private lemma chain5_orient_pos {v q a b c d e : ℝ × ℝ}
    (hq_eq : orientSign v q a = orientSign v q b ∧
             orientSign v q b = orientSign v q c ∧
             orientSign v q c = orientSign v q d ∧
             orientSign v q d = orientSign v q e)
    (hqa : orient2D v q a ≠ 0) (hqb : orient2D v q b ≠ 0) (hqc : orient2D v q c ≠ 0)
    (hqd : orient2D v q d ≠ 0) (hqe : orient2D v q e ≠ 0)
    (hab : 0 < orient2D v a b) (hbc : 0 < orient2D v b c)
    (hcd : 0 < orient2D v c d) (hde : 0 < orient2D v d e) :
    0 < orient2D v a c ∧ 0 < orient2D v a d ∧ 0 < orient2D v b e ∧
    0 < orient2D v c e ∧ 0 < orient2D v a e := by
  obtain ⟨hac, hbd, had⟩ := chain4_orient_pos ⟨hq_eq.1, hq_eq.2.1, hq_eq.2.2.1⟩ hqa hqb hqc hqd hab hbc hcd
  obtain ⟨_, hce, hbe⟩ := chain4_orient_pos ⟨hq_eq.2.1, hq_eq.2.2.1, hq_eq.2.2.2⟩ hqb hqc hqd hqe hbc hcd hde
  exact ⟨hac, had, hbe, hce,
    chain3_orient_pos ⟨hq_eq.1, hq_eq.2.1.trans (hq_eq.2.2.1.trans hq_eq.2.2.2)⟩ hqa hqb hqe hab hbe⟩

private lemma exitTri_orient2D_left {v u0 v0 y : ℝ × ℝ}
    (hy : InIntTri v u0 v0 y) (hnf : 0 < orient2D u0 v0 v) :
    0 < orient2D v u0 y ∧ 0 < orient2D v y v0 ∧ 0 < orient2D v u0 v0 := by
  have hccw : 0 < orient2D v u0 v0 := by unfold orient2D at hnf ⊢; linarith
  have hin := (inIntTri_iff_orient_pos hccw).mp hy
  exact ⟨hin.1, by unfold orient2D at hin ⊢; linarith [hin.2.2], hccw⟩

private lemma exitTri_comb_pos {v u0 v0 y a b : ℝ × ℝ}
    (hy : InIntTri v u0 v0 y)
    (hv : 0 < orient2D a b v) (hu0 : 0 ≤ orient2D a b u0) (hv0 : 0 ≤ orient2D a b v0) :
    0 < orient2D a b y := by
  rcases hy with ⟨μ₁, μ₂, μ₃, hm1, hm2, hm3, hs, hy1, hy2⟩
  rw [orient2D_convex_comb3 a b v u0 v0 y μ₁ μ₂ μ₃ hs hy1 hy2]
  exact add_pos_of_pos_of_nonneg
    (add_pos_of_pos_of_nonneg (mul_pos hm1 hv) (mul_nonneg (le_of_lt hm2) hu0))
    (mul_nonneg (le_of_lt hm3) hv0)

private lemma exitTri_before {v u0 v0 y a : ℝ × ℝ}
    (hy : InIntTri v u0 v0 y) (ha_u : 0 < orient2D v a u0) (ha_v : 0 < orient2D v a v0) :
    0 < orient2D v a y := by
  rcases hy with ⟨_, μ₂, μ₃, _, hm2, hm3, hs, hy1, hy2⟩
  have hid := orient2D_convex_comb3 v a v u0 v0 y _ _ _ hs hy1 hy2
  rw [orient2D_self_outer, mul_zero, zero_add] at hid
  rw [hid]; exact add_pos (mul_pos hm2 ha_u) (mul_pos hm3 ha_v)

private lemma exitTri_after {v u0 v0 y b : ℝ × ℝ}
    (hy : InIntTri v u0 v0 y) (hu_b : 0 < orient2D v u0 b) (hv_b : 0 < orient2D v v0 b) :
    0 < orient2D v y b := by
  rcases hy with ⟨_, μ₂, μ₃, _, hm2, hm3, hs, hy1, hy2⟩
  have hid := orient2D_convex_comb3 v b v u0 v0 y _ _ _ hs hy1 hy2
  rw [orient2D_self_outer, mul_zero, zero_add] at hid
  unfold orient2D at hid hu_b hv_b ⊢; nlinarith only [hid, hm2, hm3, hu_b, hv_b]

/-- Polynomial crossing propagation for an intermediate convex vertex `m` between `a` and `b`
    when `v a` and `v b` already cross `oa ob`. -/
private lemma segmentsCross_middle_of_endpoints_cross {v a m b oa ob : ℝ × ℝ}
    (hcra : SegmentsCross v a oa ob) (hcrb : SegmentsCross v b oa ob)
    (hvoab : 0 < orient2D v oa ob)
    (hvam : 0 < orient2D v a m) (hvmb : 0 < orient2D v m b) (hvab : 0 < orient2D v a b)
    (hamb : 0 < orient2D a m b)
    (hoam : 0 < orient2D v oa m) (hmob : 0 < orient2D v m ob) :
    SegmentsCross v m oa ob := by
  have hid : orient2D v a b * orient2D oa ob m =
      -(orient2D a m b * orient2D oa ob v) +
      orient2D v m b * orient2D oa ob a +
      orient2D v a m * orient2D oa ob b := by unfold orient2D; ring
  have hoabv : 0 < orient2D oa ob v := by unfold orient2D at hvoab ⊢; linarith
  have hoaba : orient2D oa ob a < 0 := by have := hcra.2; nlinarith only [this, hoabv]
  have hoabb : orient2D oa ob b < 0 := by have := hcrb.2; nlinarith only [this, hoabv]
  have hoabm : orient2D oa ob m < 0 := by nlinarith
  have hvmoa : orient2D v m oa < 0 := by unfold orient2D at hoam ⊢; linarith
  exact ⟨mul_neg_of_neg_of_pos hvmoa hmob, mul_neg_of_pos_of_neg hoabv hoabm⟩

private lemma good_gap_of_all_cross_hex {n : ℕ} {P : Set (ℝ × ℝ)}
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

private lemma goodAnchor_of_see {n : ℕ} {P : Set (ℝ × ℝ)}
    {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ}
    {O_miss : Finset (Fin n)} {oa ob : Fin n}
    (hao : oa ∈ O_miss) (hbo : ob ∈ O_miss) (hne : oa ≠ ob)
    (hsee : Sees P (w (Finset.univ \ O_miss)) (w Finset.univ))
    (hss : OnSameSide (w (Finset.univ \ O_miss)) (w Finset.univ) (S oa) (S ob))
    (hnc : orient2D (w (Finset.univ \ O_miss)) (S oa) (S ob) ≠ 0) :
    GoodAnchorPair P S w O_miss oa ob := by
  let v := w (Finset.univ \ O_miss); let q := w Finset.univ
  have hqa : orient2D v q (S oa) ≠ 0 := fun h => by unfold OnSameSide at hss; rw [h, zero_mul] at hss; linarith
  refine ⟨hao, hbo, hne, ?_⟩
  rcases lt_or_gt_of_ne hnc with hneg | hpos <;> rcases lt_or_gt_of_ne hqa with hqn | hqp
  · exact Or.inl ⟨⟨hss, mul_pos_of_neg_of_neg hqn hneg⟩, Or.inl hsee⟩
  · exact Or.inr ⟨⟨hss.symm, mul_pos (by unfold OnSameSide at hss; nlinarith)
      (by unfold orient2D at hneg ⊢; linarith)⟩, Or.inl hsee⟩
  · exact Or.inr ⟨⟨hss.symm, mul_pos_of_neg_of_neg (by unfold OnSameSide at hss; nlinarith)
      (by unfold orient2D at hpos ⊢; linarith)⟩, Or.inl hsee⟩
  · exact Or.inl ⟨⟨hss, mul_pos hqp hpos⟩, Or.inl hsee⟩

private lemma goodAnchor_of_cone_ends {n : ℕ} {P : Set (ℝ × ℝ)}
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
  let v := w (Finset.univ \ O_miss); let q := w Finset.univ
  have hqa : orient2D v q (S oa) ≠ 0 := fun h => by unfold OnSameSide at hss; rw [h, zero_mul] at hss; linarith
  refine ⟨hao, hbo, hne, ?_⟩
  rcases lt_or_gt_of_ne hqa with hqn | hqp
  · have hqb : orient2D v q (S ob) < 0 := by unfold OnSameSide at hss; nlinarith
    obtain ⟨e2, he2O, he2q, he2o⟩ := he2 hqn
    exact Or.inr ⟨⟨hss.symm, mul_pos_of_neg_of_neg hqb (by unfold orient2D at ho ⊢; linarith)⟩,
      Or.inr ⟨e2, he2O, ⟨by unfold OnSameSide; exact mul_pos_of_neg_of_neg he2q hqb,
        mul_pos_of_neg_of_neg he2q (by unfold orient2D at he2o ⊢; linarith)⟩⟩⟩
  · obtain ⟨e1, he1O, he1q, he1o⟩ := he1 hqp
    exact Or.inl ⟨⟨hss, mul_pos hqp ho⟩,
      Or.inr ⟨e1, he1O, ⟨by unfold OnSameSide; exact mul_pos he1q hqp, mul_pos he1q he1o⟩⟩⟩

private lemma three_missed_pigeonhole (v q m1 m2 m3 : ℝ × ℝ)
    (hq1 : orient2D v q m1 ≠ 0) (hq2 : orient2D v q m2 ≠ 0) (hq3 : orient2D v q m3 ≠ 0)
    (h12 : 0 < orient2D v m1 m2) (h23 : 0 < orient2D v m2 m3) (h13 : 0 < orient2D v m1 m3) :
    OnSameSide v q m1 m2 ∨ OnSameSide v q m2 m3 := by
  by_contra hnot; push Not at hnot
  have h12_neg := lt_of_le_of_ne (not_lt.mp hnot.1) (mul_ne_zero hq1 hq2)
  have h23_neg := lt_of_le_of_ne (not_lt.mp hnot.2) (mul_ne_zero hq2 hq3)
  have hid := orient2D_angle_trans_id v q m1 m2 m3
  rcases lt_or_gt_of_ne hq2 with h2n | h2p
  · have h1p : 0 < orient2D v q m1 := by nlinarith
    have h3p : 0 < orient2D v q m3 := by nlinarith
    nlinarith
  · have h1n : orient2D v q m1 < 0 := by nlinarith
    have h3n : orient2D v q m3 < 0 := by nlinarith
    nlinarith

private lemma hexagon_Ostar_core {n : ℕ} {P : Set (ℝ × ℝ)}
    {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ}
    (hPoly : ShatteredSimplePolygon P S w) (h25 : Sec2To5Interface P S w)
    {D : Finset (Fin n)} (hDB : D = hullVertices S \ certifiedVertices S w)
    (cycD : CCWCycle S D 3)
    {y0 y1 : Fin n} (hy0M : y0 ∈ Finset.univ \ D) (hy1M : y1 ∈ Finset.univ \ D) (_hy01 : y0 ≠ y1)
    (ib : Fin 6) :
    let O_star : Finset (Fin n) := {cycD.toFun ib, y0, y1}
    let v := w (Finset.univ \ O_star)
    let q := w Finset.univ
    (∀ m : Fin 6, m ≠ ib → cycD.toFun m ∉ O_star) ∧
    (¬ IsFrontVertexOf S D (cycD.toFun ib) v) ∧
    (∀ i j : Fin 6, i ≠ j → orient2D (S (cycD.toFun i)) (S (cycD.toFun j)) v ≠ 0) ∧
    (∀ i : Fin 6, orient2D v q (S (cycD.toFun i)) ≠ 0) ∧
    (orient2D v q (S y0) ≠ 0) ∧
    (orient2D v q (S y1) ≠ 0) ∧
    (∀ a b : Fin n, a ∉ O_star → b ∉ O_star → ¬ Sees P v q → OnSameSide v q (S a) (S b)) := by
  intro O_star v q
  have hy0_notD : y0 ∉ D := (Finset.mem_sdiff.mp hy0M).2
  have hy1_notD : y1 ∉ D := (Finset.mem_sdiff.mp hy1M).2
  have hm_out : ∀ m : Fin 6, m ≠ ib → cycD.toFun m ∉ O_star := by
    intro m hmb hmO; simp only [O_star, Finset.mem_insert, Finset.mem_singleton] at hmO
    rcases hmO with h | h | h
    · exact hmb (cycD.inj h)
    · exact hy0_notD (h ▸ ccwCycle_mem cycD m)
    · exact hy1_notD (h ▸ ccwCycle_mem cycD m)
  have hb_nf : ¬ IsFrontVertexOf S D (cycD.toFun ib) v := by
    refine no_odd_front hPoly h25 (hDB ▸ Subset.rfl) (by
      rw [← cycD.image_eq, Finset.card_image_of_injective Finset.univ cycD.inj, Finset.card_fin]; omega)
      (ccwCycle_mem cycD ib)
      (fun h => (Finset.mem_sdiff.mp h).2 (Finset.mem_insert_self _ _))
      (fun x hxD hadj => Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun hxO => ?_⟩)
    simp only [O_star, Finset.mem_insert, Finset.mem_singleton] at hxO
    rcases hxO with rfl | rfl | rfl
    · rcases hadj with e | e <;> exact e.2.2.1 rfl
    · exact hy0_notD hxD
    · exact hy1_notD hxD
  have hTv_ne_Tq : Finset.univ \ O_star ≠ Finset.univ := fun heq => by
    have hmem : y0 ∈ Finset.univ \ O_star := heq.symm ▸ Finset.mem_univ y0
    exact (Finset.mem_sdiff.mp hmem).2 (by simp [O_star])
  exact ⟨hm_out, hb_nf,
    fun i j hij => orient_S_S_w_ne hPoly (cycD.inj.ne hij) _,
    fun i => orient_w_w_S_ne hPoly hTv_ne_Tq (cycD.toFun i),
    orient_w_w_S_ne hPoly hTv_ne_Tq y0,
    orient_w_w_S_ne hPoly hTv_ne_Tq y1,
    fun a b haO hbO hnq => seen_same_side_of_misses_q hPoly hnq a b
      (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, haO⟩)
      (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hbO⟩)⟩

private lemma hexagon_exit_nonfacing {n : ℕ} {P : Set (ℝ × ℝ)}
    {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ}
    (hPoly : ShatteredSimplePolygon P S w) (h25 : Sec2To5Interface P S w)
    {D : Finset (Fin n)} (hDB : D = hullVertices S \ certifiedVertices S w)
    (cycD : CCWCycle S D 3) {y : Fin n} (hyM : y ∈ Finset.univ \ D)
    {v : ℝ × ℝ} (i : Fin 6)
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
  have hccw := orient2D_pos_of_isCCWEdge_B (z := y) hPoly he_B
    (fun h => hy_notD (by rw [h]; exact ccwCycle_mem cycD i))
    (fun h => hy_notD (by rw [h]; exact ccwCycle_mem cycD (i + 1)))
  rcases hy_tri with ⟨μ₁, _, _, hm1, _, _, hs, hy1, hy2⟩
  have hid : orient2D (S (cycD.toFun i)) (S (cycD.toFun (i + 1))) (S y) =
      μ₁ * orient2D (S (cycD.toFun i)) (S (cycD.toFun (i + 1))) v := by
    unfold orient2D; rw [hy1, hy2]
    linear_combination ((S (cycD.toFun i)).2 * (S (cycD.toFun (i + 1))).1 -
      (S (cycD.toFun i)).1 * (S (cycD.toFun (i + 1))).2) * hs
  nlinarith

/-- When all 6 edges of `cycD` are non-facing from `v` and `¬ Sees P v q`, the 5 seen vertices
    `ib + 1, ib + 2, ib + 3, ib + 4, ib + 5` form a strict `< π` chain around `v` inside `L`. -/
private lemma hexagon_seen5_chain_orient {n : ℕ} {S : Fin n → ℝ × ℝ} {D : Finset (Fin n)}
    (cycD : CCWCycle S D 3) (v q : ℝ × ℝ) (ib : Fin 6)
    (h_all_nf : ∀ m : Fin 6, 0 < orient2D (S (cycD.toFun m)) (S (cycD.toFun (m + 1))) v)
    (hvq : ∀ m : Fin 6, orient2D v q (S (cycD.toFun m)) ≠ 0)
    (hss_5 : ∀ m : Fin 6, m ≠ ib → OnSameSide v q (S (cycD.toFun (ib + 1))) (S (cycD.toFun m))) :
    ∀ α β : Fin 5, α < β →
      0 < orient2D v (S (cycD.toFun (ib + 1 + finNat 6 α.val)))
                     (S (cycD.toFun (ib + 1 + finNat 6 β.val))) := by
  let p : Fin 5 → ℝ × ℝ := fun k => S (cycD.toFun (ib + 1 + finNat 6 k.val))
  have hne_ib : ∀ k : Fin 5, ib + 1 + finNat 6 k.val ≠ ib := by
    intro k; fin_cases ib <;> fin_cases k <;> decide
  have hsucc : ∀ k : Fin 5, k.val < 4 →
      ib + 1 + finNat 6 (k.val + 1) = (ib + 1 + finNat 6 k.val) + 1 := by
    intro k hk; fin_cases ib <;> fin_cases k <;> simp at hk <;> decide
  have hp0 : p 0 = S (cycD.toFun (ib + 1)) := by dsimp [p, finNat]; simp
  have hsgn_eq : ∀ k : Fin 5, orientSign v q (p 0) = orientSign v q (p k) := fun k => by
    rw [hp0]; exact orientSign_eq_of_onSameSide (hss_5 _ (hne_ib k))
  have hstep_orient : ∀ (k : Fin 5) (hk : k.val < 4), 0 < orient2D v (p k) (p ⟨k.val + 1, by omega⟩) := by
    intro k hk
    dsimp [p]; rw [hsucc k hk]
    have hf := h_all_nf (ib + 1 + finNat 6 k.val)
    unfold orient2D at hf ⊢; linarith
  obtain ⟨h02, h03, h14, h24, h04⟩ := chain5_orient_pos
    ⟨hsgn_eq 1, (hsgn_eq 1).symm.trans (hsgn_eq 2),
     (hsgn_eq 2).symm.trans (hsgn_eq 3), (hsgn_eq 3).symm.trans (hsgn_eq 4)⟩
    (hvq _) (hvq _) (hvq _) (hvq _) (hvq _)
    (hstep_orient 0 (by decide)) (hstep_orient 1 (by decide))
    (hstep_orient 2 (by decide)) (hstep_orient 3 (by decide))
  have h13 := chain3_orient_pos ⟨(hsgn_eq 1).symm.trans (hsgn_eq 2), (hsgn_eq 2).symm.trans (hsgn_eq 3)⟩
    (hvq _) (hvq _) (hvq _) (hstep_orient 1 (by decide)) (hstep_orient 2 (by decide))
  intro α β hαβ
  fin_cases α <;> fin_cases β <;> simp at hαβ
  · exact hstep_orient 0 (by decide)
  · exact h02
  · exact h03
  · exact h04
  · exact hstep_orient 1 (by decide)
  · exact h13
  · exact h14
  · exact hstep_orient 2 (by decide)
  · exact h24
  · exact hstep_orient 3 (by decide)

-- Exhaustive 8-variable Bool tables for all 6 hexagon lemmas (`2^8 = 256` states, proved by `rfl`)
private def hex23B4Bool (s0 s1 s2 s3 s4 s5 sy0 sy1 : Bool) : Bool :=
  if !(s0 == s1 && s0 == s2 && s0 == s3 && s0 == s4 && s0 == s5) &&
      hexNoAlt4 s0 s1 s2 s3 s4 s5 && (!(s0 == s1) || (sy0 == s0)) && (!(s2 == s3) || (sy1 == s2))
  then (s4 == s5 && s5 == s0 && s0 == sy0) || (sy0 == s1 && s1 == s2 && s2 == sy1) || (sy1 == s3 && s3 == s4)
  else true

private lemma hex23B4Bool_all :
    forallB (fun s0 => forallB (fun s1 => forallB (fun s2 => forallB (fun s3 =>
    forallB (fun s4 => forallB (fun s5 => forallB (fun sy0 => forallB (fun sy1 =>
      hex23B4Bool s0 s1 s2 s3 s4 s5 sy0 sy1)))))))) = true := rfl

private lemma hex23B4_cases (s0 s1 s2 s3 s4 s5 sy0 sy1 : Bool)
    (hna : ¬ (s0 = s1 ∧ s0 = s2 ∧ s0 = s3 ∧ s0 = s4 ∧ s0 = s5))
    (halt : hexNoAlt4 s0 s1 s2 s3 s4 s5 = true)
    (hy0 : s0 = s1 → sy0 = s0) (hy1 : s2 = s3 → sy1 = s2) :
    (s4 = s5 ∧ s5 = s0 ∧ s0 = sy0) ∨ (sy0 = s1 ∧ s1 = s2 ∧ s2 = sy1) ∨ (sy1 = s3 ∧ s3 = s4) := by
  have hc := forallB_true (forallB_true (forallB_true (forallB_true (forallB_true
    (forallB_true (forallB_true (forallB_true hex23B4Bool_all s0) s1) s2) s3) s4) s5) sy0) sy1
  have hp : (!(s0 == s1 && s0 == s2 && s0 == s3 && s0 == s4 && s0 == s5) &&
      hexNoAlt4 s0 s1 s2 s3 s4 s5 && (!(s0 == s1) || (sy0 == s0)) && (!(s2 == s3) || (sy1 == s2))) = true := by
    simp only [Bool.and_eq_true]
    exact ⟨⟨⟨not_all5_eq_bool hna, halt⟩, imp_beq_bool hy0⟩, imp_beq_bool hy1⟩
  simp only [hex23B4Bool, hp, ↓reduceIte, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hc; tauto

private def hex23B5Bool (s0 s1 s2 s3 s4 s5 sy0 sy1 : Bool) : Bool :=
  if !(s0 == s1 && s0 == s2 && s0 == s3 && s0 == s4 && s0 == s5) &&
      hexNoAlt4 s0 s1 s2 s3 s4 s5 && (!(s0 == s1) || (sy0 == s0)) && (!(s2 == s3) || (sy1 == s2))
  then (s5 == s0 && s0 == sy0) || (sy0 == s1 && s1 == s2 && s2 == sy1) || (sy1 == s3 && s3 == s4 && s4 == s5)
  else true

private lemma hex23B5Bool_all :
    forallB (fun s0 => forallB (fun s1 => forallB (fun s2 => forallB (fun s3 =>
    forallB (fun s4 => forallB (fun s5 => forallB (fun sy0 => forallB (fun sy1 =>
      hex23B5Bool s0 s1 s2 s3 s4 s5 sy0 sy1)))))))) = true := rfl

private lemma hex23B5_cases (s0 s1 s2 s3 s4 s5 sy0 sy1 : Bool)
    (hna : ¬ (s0 = s1 ∧ s0 = s2 ∧ s0 = s3 ∧ s0 = s4 ∧ s0 = s5))
    (halt : hexNoAlt4 s0 s1 s2 s3 s4 s5 = true)
    (hy0 : s0 = s1 → sy0 = s0) (hy1 : s2 = s3 → sy1 = s2) :
    (s5 = s0 ∧ s0 = sy0) ∨ (sy0 = s1 ∧ s1 = s2 ∧ s2 = sy1) ∨ (sy1 = s3 ∧ s3 = s4 ∧ s4 = s5) := by
  have hc := forallB_true (forallB_true (forallB_true (forallB_true (forallB_true
    (forallB_true (forallB_true (forallB_true hex23B5Bool_all s0) s1) s2) s3) s4) s5) sy0) sy1
  have hp : (!(s0 == s1 && s0 == s2 && s0 == s3 && s0 == s4 && s0 == s5) &&
      hexNoAlt4 s0 s1 s2 s3 s4 s5 && (!(s0 == s1) || (sy0 == s0)) && (!(s2 == s3) || (sy1 == s2))) = true := by
    simp only [Bool.and_eq_true]
    exact ⟨⟨⟨not_all5_eq_bool hna, halt⟩, imp_beq_bool hy0⟩, imp_beq_bool hy1⟩
  simp only [hex23B5Bool, hp, ↓reduceIte, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hc; tauto

private def hex34B2Bool (s0 s1 s2 s3 s4 s5 sy0 sy1 : Bool) : Bool :=
  if !(s0 == s1 && s0 == s2 && s0 == s3 && s0 == s4 && s0 == s5) &&
      hexNoAlt4 s0 s1 s2 s3 s4 s5 && (!(s0 == s1) || (sy0 == s0)) && (!(s3 == s4) || (sy1 == s3))
  then (s2 == s3 && s3 == sy1) || (sy1 == s4 && s4 == s5 && s5 == s0 && s0 == sy0) || (sy0 == s1 && s1 == s2)
  else true

private lemma hex34B2Bool_all :
    forallB (fun s0 => forallB (fun s1 => forallB (fun s2 => forallB (fun s3 =>
    forallB (fun s4 => forallB (fun s5 => forallB (fun sy0 => forallB (fun sy1 =>
      hex34B2Bool s0 s1 s2 s3 s4 s5 sy0 sy1)))))))) = true := rfl

private lemma hex34B2_cases (s0 s1 s2 s3 s4 s5 sy0 sy1 : Bool)
    (hna : ¬ (s0 = s1 ∧ s0 = s2 ∧ s0 = s3 ∧ s0 = s4 ∧ s0 = s5))
    (halt : hexNoAlt4 s0 s1 s2 s3 s4 s5 = true)
    (hy0 : s0 = s1 → sy0 = s0) (hy1 : s3 = s4 → sy1 = s3) :
    (s2 = s3 ∧ s3 = sy1) ∨ (sy1 = s4 ∧ s4 = s5 ∧ s5 = s0 ∧ s0 = sy0) ∨ (sy0 = s1 ∧ s1 = s2) := by
  have hc := forallB_true (forallB_true (forallB_true (forallB_true (forallB_true
    (forallB_true (forallB_true (forallB_true hex34B2Bool_all s0) s1) s2) s3) s4) s5) sy0) sy1
  have hp : (!(s0 == s1 && s0 == s2 && s0 == s3 && s0 == s4 && s0 == s5) &&
      hexNoAlt4 s0 s1 s2 s3 s4 s5 && (!(s0 == s1) || (sy0 == s0)) && (!(s3 == s4) || (sy1 == s3))) = true := by
    simp only [Bool.and_eq_true]
    exact ⟨⟨⟨not_all5_eq_bool hna, halt⟩, imp_beq_bool hy0⟩, imp_beq_bool hy1⟩
  simp only [hex34B2Bool, hp, ↓reduceIte, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hc; tauto

private def hexAdjB5Bool (s0 s1 s2 s3 s4 s5 sy0 sy1 : Bool) : Bool :=
  if !(s0 == s1 && s0 == s2 && s0 == s3 && s0 == s4 && s0 == s5) &&
      hexNoAlt4 s0 s1 s2 s3 s4 s5 && (!(s0 == s1) || (sy0 == s0)) && (!(s1 == s2) || (sy1 == s1))
  then (s5 == s0 && s0 == sy0) || (sy0 == s1 && s1 == sy1) || (sy1 == s2 && s2 == s3 && s3 == s4 && s4 == s5)
  else true

private lemma hexAdjB5Bool_all :
    forallB (fun s0 => forallB (fun s1 => forallB (fun s2 => forallB (fun s3 =>
    forallB (fun s4 => forallB (fun s5 => forallB (fun sy0 => forallB (fun sy1 =>
      hexAdjB5Bool s0 s1 s2 s3 s4 s5 sy0 sy1)))))))) = true := rfl

private lemma hexAdjB5_cases (s0 s1 s2 s3 s4 s5 sy0 sy1 : Bool)
    (hna : ¬ (s0 = s1 ∧ s0 = s2 ∧ s0 = s3 ∧ s0 = s4 ∧ s0 = s5))
    (halt : hexNoAlt4 s0 s1 s2 s3 s4 s5 = true)
    (hy0 : s0 = s1 → sy0 = s0) (hy1 : s1 = s2 → sy1 = s1) :
    (s5 = s0 ∧ s0 = sy0) ∨ (sy0 = s1 ∧ s1 = sy1) ∨ (sy1 = s2 ∧ s2 = s3 ∧ s3 = s4 ∧ s4 = s5) := by
  have hc := forallB_true (forallB_true (forallB_true (forallB_true (forallB_true
    (forallB_true (forallB_true (forallB_true hexAdjB5Bool_all s0) s1) s2) s3) s4) s5) sy0) sy1
  have hp : (!(s0 == s1 && s0 == s2 && s0 == s3 && s0 == s4 && s0 == s5) &&
      hexNoAlt4 s0 s1 s2 s3 s4 s5 && (!(s0 == s1) || (sy0 == s0)) && (!(s1 == s2) || (sy1 == s1))) = true := by
    simp only [Bool.and_eq_true]
    exact ⟨⟨⟨not_all5_eq_bool hna, halt⟩, imp_beq_bool hy0⟩, imp_beq_bool hy1⟩
  simp only [hexAdjB5Bool, hp, ↓reduceIte, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hc; tauto

private def hexAdjB3Bool (s0 s1 s2 s3 s4 s5 sy0 sy1 : Bool) : Bool :=
  if !(s0 == s1 && s0 == s2 && s0 == s3 && s0 == s4 && s0 == s5) &&
      hexNoAlt4 s0 s1 s2 s3 s4 s5 && (!(s0 == s1) || (sy0 == s0)) && (!(s1 == s2) || (sy1 == s1))
  then (s3 == s4 && s4 == s5 && s5 == s0 && s0 == sy0) || (sy0 == s1 && s1 == sy1) || (sy1 == s2 && s2 == s3)
  else true

private lemma hexAdjB3Bool_all :
    forallB (fun s0 => forallB (fun s1 => forallB (fun s2 => forallB (fun s3 =>
    forallB (fun s4 => forallB (fun s5 => forallB (fun sy0 => forallB (fun sy1 =>
      hexAdjB3Bool s0 s1 s2 s3 s4 s5 sy0 sy1)))))))) = true := rfl

private lemma hexAdjB3_cases (s0 s1 s2 s3 s4 s5 sy0 sy1 : Bool)
    (hna : ¬ (s0 = s1 ∧ s0 = s2 ∧ s0 = s3 ∧ s0 = s4 ∧ s0 = s5))
    (halt : hexNoAlt4 s0 s1 s2 s3 s4 s5 = true)
    (hy0 : s0 = s1 → sy0 = s0) (hy1 : s1 = s2 → sy1 = s1) :
    (s3 = s4 ∧ s4 = s5 ∧ s5 = s0 ∧ s0 = sy0) ∨ (sy0 = s1 ∧ s1 = sy1) ∨ (sy1 = s2 ∧ s2 = s3) := by
  have hc := forallB_true (forallB_true (forallB_true (forallB_true (forallB_true
    (forallB_true (forallB_true (forallB_true hexAdjB3Bool_all s0) s1) s2) s3) s4) s5) sy0) sy1
  have hp : (!(s0 == s1 && s0 == s2 && s0 == s3 && s0 == s4 && s0 == s5) &&
      hexNoAlt4 s0 s1 s2 s3 s4 s5 && (!(s0 == s1) || (sy0 == s0)) && (!(s1 == s2) || (sy1 == s1))) = true := by
    simp only [Bool.and_eq_true]
    exact ⟨⟨⟨not_all5_eq_bool hna, halt⟩, imp_beq_bool hy0⟩, imp_beq_bool hy1⟩
  simp only [hexAdjB3Bool, hp, ↓reduceIte, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hc; tauto

private def hexAdjB4Bool (s0 s1 s2 s3 s4 s5 sy0 sy1 : Bool) : Bool :=
  if !(s0 == s1 && s0 == s2 && s0 == s3 && s0 == s4 && s0 == s5) &&
      hexNoAlt4 s0 s1 s2 s3 s4 s5 && (!(s0 == s1) || (sy0 == s0)) && (!(s1 == s2) || (sy1 == s1))
  then (s4 == s5 && s5 == s0 && s0 == sy0) || (sy0 == s1 && s1 == sy1) || (sy1 == s2 && s2 == s3 && s3 == s4)
  else true

private lemma hexAdjB4Bool_all :
    forallB (fun s0 => forallB (fun s1 => forallB (fun s2 => forallB (fun s3 =>
    forallB (fun s4 => forallB (fun s5 => forallB (fun sy0 => forallB (fun sy1 =>
      hexAdjB4Bool s0 s1 s2 s3 s4 s5 sy0 sy1)))))))) = true := rfl

private lemma hexAdjB4_cases (s0 s1 s2 s3 s4 s5 sy0 sy1 : Bool)
    (hna : ¬ (s0 = s1 ∧ s0 = s2 ∧ s0 = s3 ∧ s0 = s4 ∧ s0 = s5))
    (halt : hexNoAlt4 s0 s1 s2 s3 s4 s5 = true)
    (hy0 : s0 = s1 → sy0 = s0) (hy1 : s1 = s2 → sy1 = s1) :
    (s4 = s5 ∧ s5 = s0 ∧ s0 = sy0) ∨ (sy0 = s1 ∧ s1 = sy1) ∨ (sy1 = s2 ∧ s2 = s3 ∧ s3 = s4) := by
  have hc := forallB_true (forallB_true (forallB_true (forallB_true (forallB_true
    (forallB_true (forallB_true (forallB_true hexAdjB4Bool_all s0) s1) s2) s3) s4) s5) sy0) sy1
  have hp : (!(s0 == s1 && s0 == s2 && s0 == s3 && s0 == s4 && s0 == s5) &&
      hexNoAlt4 s0 s1 s2 s3 s4 s5 && (!(s0 == s1) || (sy0 == s0)) && (!(s1 == s2) || (sy1 == s1))) = true := by
    simp only [Bool.and_eq_true]
    exact ⟨⟨⟨not_all5_eq_bool hna, halt⟩, imp_beq_bool hy0⟩, imp_beq_bool hy1⟩
  simp only [hexAdjB4Bool, hp, ↓reduceIte, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hc; tauto

-- Facing-arc subchain classifiers on `Fin 6` (`30` states each, proved by `rfl`)
private def subchain5 (ee es a0 a1 a2 a3 a4 : Fin 6) : Bool :=
  decide ((a0 - ee).val < (a1 - ee).val) &&
  decide ((a1 - ee).val < (a2 - ee).val) &&
  decide ((a2 - ee).val < (a3 - ee).val) &&
  decide ((a3 - ee).val < (a4 - ee).val) &&
  decide ((a4 - ee).val ≤ (es - ee).val)

private def subchain4 (ee es a0 a1 a2 a3 : Fin 6) : Bool :=
  decide ((a0 - ee).val < (a1 - ee).val) &&
  decide ((a1 - ee).val < (a2 - ee).val) &&
  decide ((a2 - ee).val < (a3 - ee).val) &&
  decide ((a3 - ee).val ≤ (es - ee).val)

private lemma subchain5_orient {n : ℕ} {S : Fin n → ℝ × ℝ} {D : Finset (Fin n)}
    {cycD : CCWCycle S D 3} {v : ℝ × ℝ} {ee es a0 a1 a2 a3 a4 : Fin 6}
    (h_ang : ∀ a b : Fin 6, (a - ee).val < (b - ee).val → (b - ee).val ≤ (es - ee).val →
      0 < orient2D v (S (cycD.toFun a)) (S (cycD.toFun b)))
    (hsc : subchain5 ee es a0 a1 a2 a3 a4 = true) :
    let pts : Fin 5 → Fin 6 := ![a0, a1, a2, a3, a4]
    ∀ i j : Fin 5, i < j → 0 < orient2D v (S (cycD.toFun (pts i))) (S (cycD.toFun (pts j))) := by
  dsimp only [subchain5] at hsc
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hsc
  rcases hsc with ⟨⟨⟨⟨h01, h12⟩, h23⟩, h34⟩, h4e⟩
  intro pts i j hij
  fin_cases i <;> fin_cases j <;> simp at hij <;> dsimp [pts]
  · exact h_ang _ _ h01 (by omega)
  · exact h_ang _ _ (by omega) (by omega)
  · exact h_ang _ _ (by omega) (by omega)
  · exact h_ang _ _ (by omega) h4e
  · exact h_ang _ _ h12 (by omega)
  · exact h_ang _ _ (by omega) (by omega)
  · exact h_ang _ _ (by omega) h4e
  · exact h_ang _ _ h23 (by omega)
  · exact h_ang _ _ (by omega) h4e
  · exact h_ang _ _ h34 h4e

private lemma subchain4_orient {n : ℕ} {S : Fin n → ℝ × ℝ} {D : Finset (Fin n)}
    {cycD : CCWCycle S D 3} {v : ℝ × ℝ} {ee es a0 a1 a2 a3 : Fin 6}
    (h_ang : ∀ a b : Fin 6, (a - ee).val < (b - ee).val → (b - ee).val ≤ (es - ee).val →
      0 < orient2D v (S (cycD.toFun a)) (S (cycD.toFun b)))
    (hsc : subchain4 ee es a0 a1 a2 a3 = true) :
    let pts : Fin 4 → Fin 6 := ![a0, a1, a2, a3]
    ∀ i j : Fin 4, i < j → 0 < orient2D v (S (cycD.toFun (pts i))) (S (cycD.toFun (pts j))) := by
  dsimp only [subchain4] at hsc
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hsc
  rcases hsc with ⟨⟨⟨h01, h12⟩, h23⟩, h3e⟩
  intro pts i j hij
  fin_cases i <;> fin_cases j <;> simp at hij <;> dsimp [pts]
  · exact h_ang _ _ h01 (by omega)
  · exact h_ang _ _ (by omega) (by omega)
  · exact h_ang _ _ (by omega) h3e
  · exact h_ang _ _ h12 (by omega)
  · exact h_ang _ _ (by omega) h3e
  · exact h_ang _ _ h23 h3e

private def hexFacingCheck (nf1 nf2 bm b : Fin 6)
    (out : Fin 6 → Fin 6 → Bool) (i : Fin 6) (L0 : Fin 5) : Bool :=
  let Lv := L0.val + 1
  let ee := i + finNat 6 Lv
  let bad := decide ((nf1 - i).val < Lv) || decide ((nf2 - i).val < Lv) ||
    (decide ((bm - i).val < Lv) && decide ((b - i).val < Lv))
  if bad then true else out ee i

private lemma hexFacing_elim {nf1 nf2 bm b : Fin 6} {out : Fin 6 → Fin 6 → Bool}
    (hall : (List.finRange 6).all (fun i => (List.finRange 5).all (fun L0 =>
      hexFacingCheck nf1 nf2 bm b out i L0)) = true)
    (es ee : Fin 6) (L : ℕ) (hL1 : 1 ≤ L) (hL5 : L ≤ 5) (heq : ee = es + finNat 6 L)
    (hnf1 : ¬ (nf1 - es).val < L) (hnf2 : ¬ (nf2 - es).val < L)
    (hbbm : ¬ ((bm - es).val < L ∧ (b - es).val < L)) :
    out ee es = true := by
  let L0 : Fin 5 := ⟨L - 1, by omega⟩
  have hLv : L0.val + 1 = L := by dsimp [L0]; omega
  have h1 := List.all_eq_true.mp hall es (List.mem_finRange _)
  have h2 := List.all_eq_true.mp h1 L0 (List.mem_finRange _)
  dsimp [hexFacingCheck] at h2
  rw [hLv, ← heq] at h2
  have hbad : (decide ((nf1 - es).val < L) || decide ((nf2 - es).val < L) ||
      (decide ((bm - es).val < L) && decide ((b - es).val < L))) = false := by
    simp only [Bool.or_eq_false_iff, Bool.and_eq_false_iff, decide_eq_false_iff_not]
    refine ⟨⟨hnf1, hnf2⟩, ?_⟩
    by_cases hbm : (bm - es).val < L
    · exact Or.inr (fun hb => hbbm ⟨hbm, hb⟩)
    · exact Or.inl hbm
  rw [hbad] at h2
  simpa using h2

private lemma hexFace_23_b4_all :
    (List.finRange 6).all (fun i => (List.finRange 5).all (fun L0 =>
      hexFacingCheck 0 2 3 4 (fun ee es =>
        (es == 1 && ee == 2) || (es == 3 && ee == 4) || subchain5 ee es 0 1 2 3 4) i L0)) = true := rfl

private lemma hexFace_23_b5_all :
    (List.finRange 6).all (fun i => (List.finRange 5).all (fun L0 =>
      hexFacingCheck 0 2 4 5 (fun ee es =>
        (es == 1 && ee == 2) || (es == 5 && ee == 0) || subchain5 ee es 5 0 1 2 3) i L0)) = true := rfl

private lemma hexFace_34_b2_all :
    (List.finRange 6).all (fun i => (List.finRange 5).all (fun L0 =>
      hexFacingCheck 0 3 1 2 (fun ee es =>
        (es == 1 && ee == 2) || (es == 2 && ee == 3) || subchain5 ee es 0 1 2 3 4) i L0)) = true := rfl

private lemma hexFace_adj_b5_all :
    (List.finRange 6).all (fun i => (List.finRange 5).all (fun L0 =>
      hexFacingCheck 0 1 4 5 (fun ee es =>
        (es == 5 && ee == 0) || subchain4 ee es 5 0 1 2) i L0)) = true := rfl

private lemma hexFace_adj_b3_all :
    (List.finRange 6).all (fun i => (List.finRange 5).all (fun L0 =>
      hexFacingCheck 0 1 2 3 (fun ee es =>
        (es == 2 && ee == 3) || subchain4 ee es 0 1 2 3) i L0)) = true := rfl

private lemma hexFace_adj_b4_all :
    (List.finRange 6).all (fun i => (List.finRange 5).all (fun L0 =>
      hexFacingCheck 0 1 3 4 (fun ee es =>
        subchain5 ee es 4 5 0 1 2 || subchain5 ee es 0 1 2 3 4) i L0)) = true := rfl

private abbrev HexDisjGoal {n : ℕ} (P : Set (ℝ × ℝ))
    (S : Fin n → ℝ × ℝ) (w : Finset (Fin n) → ℝ × ℝ)
    (O_star : Finset (Fin n))
    (a1 b1 : Fin n) (G1 : Finset (Fin n))
    (a2 b2 : Fin n) (G2 : Finset (Fin n))
    (a3 b3 : Fin n) (G3 : Finset (Fin n)) : Prop :=
  let v := w (Finset.univ \ O_star)
  ∃ (oa ob : Fin n) (Γ : Finset (Fin n)),
    ((oa = a1 ∧ ob = b1 ∧ Γ = G1) ∨
     (oa = a2 ∧ ob = b2 ∧ Γ = G2) ∨
     (oa = a3 ∧ ob = b3 ∧ Γ = G3)) ∧
    GoodAnchorPair P S w O_star oa ob ∧
    (∀ p ∈ Γ, IsBackVertexOf S (hullVertices S) p v ∧ SegmentsCross v (S p) (S oa) (S ob) ∧
      (∃ H_hp : OpenHalfPlane, IsHalfPlaneTest P (WitnessSet {oa, ob} ∅ w) (S p) H_hp)) ∧
    (∀ z : Fin n, z ≠ oa → z ≠ ob → z ∉ O_star →
      S z ∈ convexHull ℝ ((Γ ∪ {oa, ob}).image S : Set (ℝ × ℝ)) →
      SegmentsCross v (S z) (S oa) (S ob) ∧
      (∃ H_hp : OpenHalfPlane, IsHalfPlaneTest P (WitnessSet {oa, ob} ∅ w) (S z) H_hp) ∧
      (z ∈ hullVertices S → IsBackVertexOf S (hullVertices S) z v))

/-- **Lemma 5.11(i), `b = 4` (`hexagon-disjoint-exits`, `upper_8.tex`)**:
    For a hexagon `D = (0, 1, 2, 3, 4, 5)` and `y0, y1 ∈ M` on disjoint exit edges `01` and `23`,
    with `O* = {4, y0, y1}` and `v = w (S \ O*)`, at least one of `{5, 0}` (`{4, y0}`),
    `{1, 2}` (`{y0, y1}`), or `{3}` (`{y1, 4}`) is a good gap for `v`. -/
theorem hexagon_disjoint_exits_23_b4 {n : ℕ} {P : Set (ℝ × ℝ)}
    {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ}
    (hPoly : ShatteredSimplePolygon P S w) (h25 : Sec2To5Interface P S w)
    {D : Finset (Fin n)} (hDB : D = hullVertices S \ certifiedVertices S w)
    (cycD : CCWCycle S D 3)
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
      ((oa = b ∧ ob = y0 ∧ Γ = {cycD.toFun 5, cycD.toFun 0}) ∨
       (oa = y0 ∧ ob = y1 ∧ Γ = {cycD.toFun 1, cycD.toFun 2}) ∨
       (oa = y1 ∧ ob = b ∧ Γ = {cycD.toFun 3})) ∧
      GoodAnchorPair P S w O_star oa ob ∧
      (∀ p ∈ Γ, IsBackVertexOf S (hullVertices S) p v ∧ SegmentsCross v (S p) (S oa) (S ob) ∧
        (∃ H_hp : OpenHalfPlane, IsHalfPlaneTest P (WitnessSet {oa, ob} ∅ w) (S p) H_hp)) ∧
      (∀ z : Fin n, z ≠ oa → z ≠ ob → z ∉ O_star →
        S z ∈ convexHull ℝ ((Γ ∪ {oa, ob}).image S : Set (ℝ × ℝ)) →
        SegmentsCross v (S z) (S oa) (S ob) ∧
        (∃ H_hp : OpenHalfPlane, IsHalfPlaneTest P (WitnessSet {oa, ob} ∅ w) (S z) H_hp) ∧
        (z ∈ hullVertices S → IsBackVertexOf S (hullVertices S) z v)) := by
  intro b O_star v
  let d0 := cycD.toFun 0; let d1 := cycD.toFun 1; let d2 := cycD.toFun 2
  let d3 := cycD.toFun 3; let d5 := cycD.toFun 5; let q := w Finset.univ
  have hy0_notD : y0 ∉ D := (Finset.mem_sdiff.mp hy0M).2
  have hy1_notD : y1 ∉ D := (Finset.mem_sdiff.mp hy1M).2
  obtain ⟨hm_out, hb_nf, hv_noncol, hvq_D, hvq_y0, hvq_y1, h_seen_ss⟩ :=
    hexagon_Ostar_core hPoly h25 hDB cycD hy0M hy1M hy01 4
  have h0_out := hm_out 0 (by decide); have h1_out := hm_out 1 (by decide)
  have h2_out := hm_out 2 (by decide); have h3_out := hm_out 3 (by decide)
  have h5_out := hm_out 5 (by decide)
  have hB : D ⊆ hullVertices S := hDB ▸ Finset.sdiff_subset
  have hb_O : b ∈ O_star := by simp [O_star]
  have hy0_O : y0 ∈ O_star := by simp [O_star]
  have hy1_O : y1 ∈ O_star := by simp [O_star]
  have hb_ne_y0 : b ≠ y0 := fun h => hy0_notD (h ▸ ccwCycle_mem cycD 4)
  have hy1_ne_b : y1 ≠ b := fun h => hy1_notD (h.symm ▸ ccwCycle_mem cycD 4)
  have h01_nf := hexagon_exit_nonfacing hPoly h25 hDB cycD hy0M 0 hy0_tri (fun l r hH he hHn => (h_not_lr l r hH he hHn).1)
  have h23_nf := hexagon_exit_nonfacing hPoly h25 hDB cycD hy1M 2 hy1_tri (fun l r hH he hHn => (h_not_lr l r hH he hHn).2)
  have ⟨h0_y0, hy0_1, _⟩ := exitTri_orient2D_left hy0_tri h01_nf
  have ⟨h2_y1, hy1_3, _⟩ := exitTri_orient2D_left hy1_tri h23_nf
  have h_01_y1 : 0 < orient2D (S d0) (S d1) (S y1) :=
    exitTri_comb_pos hy1_tri h01_nf (le_of_lt (ccw6_lt cycD (by decide) (by decide)))
      (le_of_lt (ccw6_lt cycD (by decide) (by decide)))
  have h_23_y0 : 0 < orient2D (S d2) (S d3) (S y0) :=
    exitTri_comb_pos hy0_tri h23_nf
      (le_of_lt (by have h := ccw6_lt cycD (by decide : (0 : Fin 6) < 2) (by decide : (2 : Fin 6) < 3); unfold orient2D at h ⊢; linarith))
      (le_of_lt (by have h := ccw6_lt cycD (by decide : (1 : Fin 6) < 2) (by decide : (2 : Fin 6) < 3); unfold orient2D at h ⊢; linarith))
  let Goal := HexDisjGoal P S w O_star b y0 {d5, d0} y0 y1 {d1, d2} y1 b {d3}
  have build50 : GoodAnchorPair P S w O_star b y0 →
      0 < orient2D v (S b) (S d5) → 0 < orient2D v (S d5) (S y0) →
      0 < orient2D v (S b) (S d0) → 0 < orient2D v (S b) (S y0) → Goal := by
    intro hgap h45 h5y0 h40 hby0
    refine ⟨b, y0, {d5, d0}, Or.inl ⟨rfl, rfl, rfl⟩, hgap, good_gap_of_all_cross_hex hPoly h25 hgap (fun p hp => ?_)⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp; rcases hp with rfl | rfl
    · refine ⟨cycD.inj.ne (by decide), fun h => hy0_notD (by rw [← h]; exact ccwCycle_mem cycD 5), h5_out, hB (ccwCycle_mem cycD 5),
        segmentsCross_inIntTri_left hy0_tri h45 h5y0 hby0
          (le_of_lt (by have h := ccw6_lt cycD (by decide : (0 : Fin 6) < 4) (by decide : (4 : Fin 6) < 5); unfold orient2D at h ⊢; linarith))
          (by have h := ccw6_lt cycD (by decide : (1 : Fin 6) < 4) (by decide : (4 : Fin 6) < 5); unfold orient2D at h ⊢; linarith)⟩
    · refine ⟨cycD.inj.ne (by decide), fun h => hy0_notD (by rw [← h]; exact ccwCycle_mem cycD 0), h0_out, hB (ccwCycle_mem cycD 0),
        segmentsCross_inIntTri_left hy0_tri h40 h0_y0 hby0 (by rw [orient2D_self_right])
          (by have h := ccw6_lt cycD (by decide : (0 : Fin 6) < 1) (by decide : (1 : Fin 6) < 4); dsimp [b, d0, d1]; unfold orient2D at h ⊢; linarith)⟩
  have build12 : GoodAnchorPair P S w O_star y0 y1 →
      0 < orient2D v (S y0) (S d2) → 0 < orient2D v (S d1) (S y1) → 0 < orient2D v (S y0) (S y1) → Goal := by
    intro hgap hy0_2 hd1_y1 hy0_y1
    refine ⟨y0, y1, {d1, d2}, Or.inr (Or.inl ⟨rfl, rfl, rfl⟩), hgap, good_gap_of_all_cross_hex hPoly h25 hgap (fun p hp => ?_)⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp; rcases hp with rfl | rfl
    · exact ⟨fun h => hy0_notD (by rw [← h]; exact ccwCycle_mem cycD 1), fun h => hy1_notD (by rw [← h]; exact ccwCycle_mem cycD 1),
        h1_out, hB (ccwCycle_mem cycD 1), segmentsCross_between_exits_shared (u1 := (0, 0)) hy0_tri hy0_1 hd1_y1 hy0_y1 h_01_y1⟩
    · exact ⟨fun h => hy0_notD (by rw [← h]; exact ccwCycle_mem cycD 2), fun h => hy1_notD (by rw [← h]; exact ccwCycle_mem cycD 2),
        h2_out, hB (ccwCycle_mem cycD 2), segmentsCross_between_exits_shared_right hy1_tri hy0_2 h2_y1 hy0_y1 h_23_y0⟩
  have build3 : GoodAnchorPair P S w O_star y1 b → 0 < orient2D v (S d3) (S b) → 0 < orient2D v (S y1) (S b) → Goal := by
    intro hgap h34 hy1b
    refine ⟨y1, b, {d3}, Or.inr (Or.inr ⟨rfl, rfl, rfl⟩), hgap, good_gap_of_all_cross_hex hPoly h25 hgap (fun p hp => ?_)⟩
    rw [Finset.mem_singleton] at hp; subst hp
    exact ⟨fun h => hy1_notD (by rw [← h]; exact ccwCycle_mem cycD 3), cycD.inj.ne (by decide), h3_out, hB (ccwCycle_mem cycD 3),
      segmentsCross_inIntTri_right hy1_tri hy1_3 h34 hy1b (ccw6_lt cycD (by decide) (by decide)) (by dsimp [d3]; rw [orient2D_self_left])⟩
  by_cases h_all_nf : ∀ m : Fin 6, 0 < orient2D (S (cycD.toFun m)) (S (cycD.toFun (m + 1))) v
  · by_cases hsee : Sees P v q
    · have h45 : 0 < orient2D v (S b) (S d5) := by have h := h_all_nf 4; dsimp [b, d5] at *; unfold orient2D at h ⊢; linarith
      have h50 : 0 < orient2D v (S d5) (S d0) := by have h := h_all_nf 5; dsimp [d5, d0] at *; unfold orient2D at h ⊢; linarith
      have h12 : 0 < orient2D v (S d1) (S d2) := by have h := h_all_nf 1; dsimp [d1, d2] at *; unfold orient2D at h ⊢; linarith
      have h34 : 0 < orient2D v (S d3) (S b) := by have h := h_all_nf 3; dsimp [d3, b] at *; unfold orient2D at h ⊢; linarith
      rcases hex23B4_cases _ _ _ _ _ _ _ _
        (hex_all_nf_not_all_same cycD v q h_all_nf hvq_D) (hexNoAlt4_of_orientSign cycD v q hvq_D)
        (exitTri_orientSign_of_endpoints hy0_tri (hvq_D 0) (hvq_D 1))
        (exitTri_orientSign_of_endpoints hy1_tri (hvq_D 2) (hvq_D 3)) with
        ⟨h45_s, h50_s, h0y_s⟩ | ⟨hy01_s, h12_s, h2y_s⟩ | ⟨hy13_s, h34_s⟩
      · obtain ⟨h40, h5y0, hby0⟩ := chain4_orient_pos ⟨h45_s, h50_s, h0y_s⟩ (hvq_D 4) (hvq_D 5) (hvq_D 0) hvq_y0 h45 h50 h0_y0
        exact build50 (goodAnchor_of_see hb_O hy0_O hb_ne_y0 hsee
          (onSameSide_of_orientSign_eq (h45_s.trans (h50_s.trans h0y_s)) (hvq_D 4) hvq_y0) (ne_of_gt hby0)) h45 h5y0 h40 hby0
      · obtain ⟨hy0_2, hd1_y1, hy0_y1⟩ := chain4_orient_pos ⟨hy01_s, h12_s, h2y_s⟩ hvq_y0 (hvq_D 1) (hvq_D 2) hvq_y1 hy0_1 h12 h2_y1
        exact build12 (goodAnchor_of_see hy0_O hy1_O hy01 hsee
          (onSameSide_of_orientSign_eq (hy01_s.trans (h12_s.trans h2y_s)) hvq_y0 hvq_y1) (ne_of_gt hy0_y1)) hy0_2 hd1_y1 hy0_y1
      · have hy1b := chain3_orient_pos ⟨hy13_s, h34_s⟩ hvq_y1 (hvq_D 3) (hvq_D 4) hy1_3 h34
        exact build3 (goodAnchor_of_see hy1_O hb_O hy1_ne_b hsee
          (onSameSide_of_orientSign_eq (hy13_s.trans h34_s) hvq_y1 (hvq_D 4)) (ne_of_gt hy1b)) h34 hy1b
    · have hch := hexagon_seen5_chain_orient cycD v q 4 h_all_nf hvq_D
        (fun m hm => h_seen_ss (cycD.toFun 5) (cycD.toFun m) h5_out (hm_out m hm) hsee)
      have h12 : 0 < orient2D v (S d1) (S d2) := hch 2 3 (by decide)
      have h13 : 0 < orient2D v (S d1) (S d3) := hch 2 4 (by decide)
      have h02 : 0 < orient2D v (S d0) (S d2) := hch 1 3 (by decide)
      have h03 : 0 < orient2D v (S d0) (S d3) := hch 1 4 (by decide)
      have hd1_y1 := exitTri_before hy1_tri h12 h13
      have hy0_2 := exitTri_after hy0_tri h02 h12
      have hy0_y1 := exitTri_after hy0_tri (exitTri_before hy1_tri h02 h03) hd1_y1
      have hss01 := h_seen_ss d0 d1 h0_out h1_out hsee
      have hss23 := h_seen_ss d2 d3 h2_out h3_out hsee
      have hss0_y0 := (exitTri_sameSide_in_L hy0_tri hss01).1
      have hss_y13 := (exitTri_sameSide_in_L hy1_tri hss23).2
      have hss_y0_y1 : OnSameSide v q (S y0) (S y1) :=
        hss0_y0.symm.trans ((h_seen_ss d0 d2 h0_out h2_out hsee).trans (exitTri_sameSide_in_L hy1_tri hss23).1)
      exact build12 (goodAnchor_of_cone_ends hy0_O hy1_O hy01 hss_y0_y1 hy0_y1
        (fun hqy0 => ⟨d0, h0_out, by unfold OnSameSide at hss0_y0; nlinarith, h0_y0⟩)
        (fun hqy0 => ⟨d3, h3_out, by unfold OnSameSide at hss_y0_y1 hss_y13; nlinarith, hy1_3⟩)) hy0_2 hd1_y1 hy0_y1
  · push Not at h_all_nf; obtain ⟨j0, hj0⟩ := h_all_nf
    obtain ⟨es, ee, L, hL1, hL5, heq, h_face_lt, _, _, _, _, h_ang⟩ :=
      facing_arc_complement_order cycD v hv_noncol ⟨j0, lt_of_le_of_ne hj0 (hv_noncol j0 (j0 + 1) (fin_add_one_ne_self j0))⟩
    have hc := hexFacing_elim hexFace_23_b4_all es ee L hL1 hL5 heq
      (fun h => by linarith [h_face_lt 0 h, h01_nf])
      (fun h => by linarith [h_face_lt 2 h, h23_nf])
      (fun ⟨h3, h4⟩ => hb_nf ((isFrontVertexOf_iff_ccwCycle cycD 4 v).mpr ⟨h_face_lt 3 h3, h_face_lt 4 h4⟩))
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hc
    rcases hc with (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) | hsc
    · -- [2, 3, 4, 5, 0, 1]
      have ho : ∀ a c : Fin 6, (a - 2).val < (c - 2).val → (c - 2).val ≤ (1 - 2 : Fin 6).val →
          0 < orient2D v (S (cycD.toFun a)) (S (cycD.toFun c)) := fun a c h1 h2 => (h_ang a c h1 h2).2
      have h34 := ho 3 4 (by decide) (by decide)
      have h45 := ho 4 5 (by decide) (by decide)
      have h40 := ho 4 0 (by decide) (by decide)
      have hy1_4 := exitTri_after hy1_tri (ho 2 4 (by decide) (by decide)) h34
      have h4_y0 := exitTri_before hy0_tri h40 (ho 4 1 (by decide) (by decide))
      have h5_y0 := exitTri_before hy0_tri (ho 5 0 (by decide) (by decide)) (ho 5 1 (by decide) (by decide))
      have hy1_y0 := exitTri_after hy1_tri
        (exitTri_before hy0_tri (ho 2 0 (by decide) (by decide)) (ho 2 1 (by decide) (by decide)))
        (exitTri_before hy0_tri (ho 3 0 (by decide) (by decide)) (ho 3 1 (by decide) (by decide)))
      by_cases hsee : Sees P v q
      · rcases three_missed_pigeonhole v q (S y1) (S b) (S y0) hvq_y1 (hvq_D 4) hvq_y0 hy1_4 h4_y0 hy1_y0 with hss1 | hss2
        · exact build3 (goodAnchor_of_see hy1_O hb_O hy1_ne_b hsee hss1 (ne_of_gt hy1_4)) h34 hy1_4
        · exact build50 (goodAnchor_of_see hb_O hy0_O hb_ne_y0 hsee hss2 (ne_of_gt h4_y0)) h45 h5_y0 h40 h4_y0
      · have hss21 := h_seen_ss d2 d1 h2_out h1_out hsee
        have hss2_4 := vq_between_sameSide hss21 (hvq_D 2)
          (ho 2 1 (by decide) (by decide)) (ho 2 4 (by decide) (by decide)) (ho 4 1 (by decide) (by decide))
        have hss2_y1 := (exitTri_sameSide_in_L hy1_tri (h_seen_ss d2 d3 h2_out h3_out hsee)).1
        have hss_y1_4 := hss2_y1.symm.trans hss2_4
        have hss4_1 := hss2_4.symm.trans hss21
        exact build3 (goodAnchor_of_cone_ends hy1_O hb_O hy1_ne_b hss_y1_4 hy1_4
          (fun hqy1 => ⟨d2, h2_out, by unfold OnSameSide at hss2_y1; nlinarith, h2_y1⟩)
          (fun hqy1 => ⟨d1, h1_out, by unfold OnSameSide at hss_y1_4 hss4_1; nlinarith, ho 4 1 (by decide) (by decide)⟩)) h34 hy1_4
    · -- [4, 5, 0, 1, 2, 3]
      have ho : ∀ a c : Fin 6, (a - 4).val < (c - 4).val → (c - 4).val ≤ (3 - 4 : Fin 6).val →
          0 < orient2D v (S (cycD.toFun a)) (S (cycD.toFun c)) := fun a c h1 h2 => (h_ang a c h1 h2).2
      have h45 := ho 4 5 (by decide) (by decide)
      have h40 := ho 4 0 (by decide) (by decide)
      have h12 := ho 1 2 (by decide) (by decide)
      have h4_y0 := exitTri_before hy0_tri h40 (ho 4 1 (by decide) (by decide))
      have h5_y0 := exitTri_before hy0_tri (ho 5 0 (by decide) (by decide)) (ho 5 1 (by decide) (by decide))
      have hd1_y1 := exitTri_before hy1_tri h12 (ho 1 3 (by decide) (by decide))
      have hy0_2 := exitTri_after hy0_tri (ho 0 2 (by decide) (by decide)) h12
      have hy0_y1 := exitTri_after hy0_tri (exitTri_before hy1_tri (ho 0 2 (by decide) (by decide)) (ho 0 3 (by decide) (by decide))) hd1_y1
      have h4_y1 := exitTri_before hy1_tri (ho 4 2 (by decide) (by decide)) (ho 4 3 (by decide) (by decide))
      by_cases hsee : Sees P v q
      · rcases three_missed_pigeonhole v q (S b) (S y0) (S y1) (hvq_D 4) hvq_y0 hvq_y1 h4_y0 hy0_y1 h4_y1 with hss1 | hss2
        · exact build50 (goodAnchor_of_see hb_O hy0_O hb_ne_y0 hsee hss1 (ne_of_gt h4_y0)) h45 h5_y0 h40 h4_y0
        · exact build12 (goodAnchor_of_see hy0_O hy1_O hy01 hsee hss2 (ne_of_gt hy0_y1)) hy0_2 hd1_y1 hy0_y1
      · have hss0_y0 := (exitTri_sameSide_in_L hy0_tri (h_seen_ss d0 d1 h0_out h1_out hsee)).1
        have hss23 := h_seen_ss d2 d3 h2_out h3_out hsee
        have hss_y0_y1 := hss0_y0.symm.trans ((h_seen_ss d0 d2 h0_out h2_out hsee).trans (exitTri_sameSide_in_L hy1_tri hss23).1)
        have hss_y13 := (exitTri_sameSide_in_L hy1_tri hss23).2
        exact build12 (goodAnchor_of_cone_ends hy0_O hy1_O hy01 hss_y0_y1 hy0_y1
          (fun hqy0 => ⟨d0, h0_out, by unfold OnSameSide at hss0_y0; nlinarith, h0_y0⟩)
          (fun hqy0 => ⟨d3, h3_out, by unfold OnSameSide at hss_y0_y1 hss_y13; nlinarith, hy1_3⟩)) hy0_2 hd1_y1 hy0_y1
    · -- subchain [0, 1, 2, 3, 4]
      have ho := subchain5_orient (fun a c h1 h2 => (h_ang a c h1 h2).2) hsc
      have h12 : 0 < orient2D v (S d1) (S d2) := ho 1 2 (by decide)
      have h34 : 0 < orient2D v (S d3) (S b) := ho 3 4 (by decide)
      have hd1_y1 := exitTri_before hy1_tri h12 (ho 1 3 (by decide))
      have hy0_2 := exitTri_after hy0_tri (ho 0 2 (by decide)) h12
      have hy0_y1 := exitTri_after hy0_tri (exitTri_before hy1_tri (ho 0 2 (by decide)) (ho 0 3 (by decide))) hd1_y1
      have hy1_4 := exitTri_after hy1_tri (ho 2 4 (by decide)) h34
      have hy0_4 := exitTri_after hy0_tri (ho 0 4 (by decide)) (ho 1 4 (by decide))
      by_cases hsee : Sees P v q
      · rcases three_missed_pigeonhole v q (S y0) (S y1) (S b) hvq_y0 hvq_y1 (hvq_D 4) hy0_y1 hy1_4 hy0_4 with hss1 | hss2
        · exact build12 (goodAnchor_of_see hy0_O hy1_O hy01 hsee hss1 (ne_of_gt hy0_y1)) hy0_2 hd1_y1 hy0_y1
        · exact build3 (goodAnchor_of_see hy1_O hb_O hy1_ne_b hsee hss2 (ne_of_gt hy1_4)) h34 hy1_4
      · have hss0_y0 := (exitTri_sameSide_in_L hy0_tri (h_seen_ss d0 d1 h0_out h1_out hsee)).1
        have hss23 := h_seen_ss d2 d3 h2_out h3_out hsee
        have hss_y0_y1 := hss0_y0.symm.trans ((h_seen_ss d0 d2 h0_out h2_out hsee).trans (exitTri_sameSide_in_L hy1_tri hss23).1)
        have hss_y13 := (exitTri_sameSide_in_L hy1_tri hss23).2
        exact build12 (goodAnchor_of_cone_ends hy0_O hy1_O hy01 hss_y0_y1 hy0_y1
          (fun hqy0 => ⟨d0, h0_out, by unfold OnSameSide at hss0_y0; nlinarith, h0_y0⟩)
          (fun hqy0 => ⟨d3, h3_out, by unfold OnSameSide at hss_y0_y1 hss_y13; nlinarith, hy1_3⟩)) hy0_2 hd1_y1 hy0_y1

/-- **Lemma 5.11(i), `b = 5` (`hexagon-disjoint-exits`, `upper_8.tex`)**:
    For `D = (0, 1, 2, 3, 4, 5)` and `y0, y1 ∈ M` on `01` and `23`, with `O* = {5, y0, y1}`,
    at least one of `{0}` (`{5, y0}`), `{1, 2}` (`{y0, y1}`), or `{3, 4}` (`{y1, 5}`) is good. -/
theorem hexagon_disjoint_exits_23_b5 {n : ℕ} {P : Set (ℝ × ℝ)}
    {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ}
    (hPoly : ShatteredSimplePolygon P S w) (h25 : Sec2To5Interface P S w)
    {D : Finset (Fin n)} (hDB : D = hullVertices S \ certifiedVertices S w)
    (cycD : CCWCycle S D 3)
    {y0 y1 : Fin n} (hy0M : y0 ∈ Finset.univ \ D) (hy1M : y1 ∈ Finset.univ \ D) (hy01 : y0 ≠ y1)
    (hy0_tri : InIntTri (w (Finset.univ \ {cycD.toFun 5, y0, y1})) (S (cycD.toFun 0)) (S (cycD.toFun 1)) (S y0))
    (hy1_tri : InIntTri (w (Finset.univ \ {cycD.toFun 5, y0, y1})) (S (cycD.toFun 2)) (S (cycD.toFun 3)) (S y1))
    (h_not_lr : ∀ l r : Fin n, (certifiedVertices S w).Nonempty →
      IsCCWEdge S D l r → (∀ h ∈ certifiedVertices S w, orient2D (S l) (S r) (S h) < 0) →
      (cycD.toFun 0, cycD.toFun 1) ≠ (l, r) ∧ (cycD.toFun 2, cycD.toFun 3) ≠ (l, r)) :
    let b := cycD.toFun 5
    let O_star : Finset (Fin n) := {b, y0, y1}
    let v := w (Finset.univ \ O_star)
    ∃ (oa ob : Fin n) (Γ : Finset (Fin n)),
      ((oa = b ∧ ob = y0 ∧ Γ = {cycD.toFun 0}) ∨
       (oa = y0 ∧ ob = y1 ∧ Γ = {cycD.toFun 1, cycD.toFun 2}) ∨
       (oa = y1 ∧ ob = b ∧ Γ = {cycD.toFun 3, cycD.toFun 4})) ∧
      GoodAnchorPair P S w O_star oa ob ∧
      (∀ p ∈ Γ, IsBackVertexOf S (hullVertices S) p v ∧ SegmentsCross v (S p) (S oa) (S ob) ∧
        (∃ H_hp : OpenHalfPlane, IsHalfPlaneTest P (WitnessSet {oa, ob} ∅ w) (S p) H_hp)) ∧
      (∀ z : Fin n, z ≠ oa → z ≠ ob → z ∉ O_star →
        S z ∈ convexHull ℝ ((Γ ∪ {oa, ob}).image S : Set (ℝ × ℝ)) →
        SegmentsCross v (S z) (S oa) (S ob) ∧
        (∃ H_hp : OpenHalfPlane, IsHalfPlaneTest P (WitnessSet {oa, ob} ∅ w) (S z) H_hp) ∧
        (z ∈ hullVertices S → IsBackVertexOf S (hullVertices S) z v)) := by
  intro b O_star v
  let d0 := cycD.toFun 0; let d1 := cycD.toFun 1; let d2 := cycD.toFun 2
  let d3 := cycD.toFun 3; let d4 := cycD.toFun 4; let q := w Finset.univ
  have hy0_notD : y0 ∉ D := (Finset.mem_sdiff.mp hy0M).2
  have hy1_notD : y1 ∉ D := (Finset.mem_sdiff.mp hy1M).2
  obtain ⟨hm_out, hb_nf, hv_noncol, hvq_D, hvq_y0, hvq_y1, h_seen_ss⟩ :=
    hexagon_Ostar_core hPoly h25 hDB cycD hy0M hy1M hy01 5
  have h0_out := hm_out 0 (by decide); have h1_out := hm_out 1 (by decide)
  have h2_out := hm_out 2 (by decide); have h3_out := hm_out 3 (by decide)
  have h4_out := hm_out 4 (by decide)
  have hB : D ⊆ hullVertices S := hDB ▸ Finset.sdiff_subset
  have hb_O : b ∈ O_star := by simp [O_star]
  have hy0_O : y0 ∈ O_star := by simp [O_star]
  have hy1_O : y1 ∈ O_star := by simp [O_star]
  have hb_ne_y0 : b ≠ y0 := fun h => hy0_notD (h ▸ ccwCycle_mem cycD 5)
  have hy1_ne_b : y1 ≠ b := fun h => hy1_notD (h.symm ▸ ccwCycle_mem cycD 5)
  have h01_nf := hexagon_exit_nonfacing hPoly h25 hDB cycD hy0M 0 hy0_tri (fun l r hH he hHn => (h_not_lr l r hH he hHn).1)
  have h23_nf := hexagon_exit_nonfacing hPoly h25 hDB cycD hy1M 2 hy1_tri (fun l r hH he hHn => (h_not_lr l r hH he hHn).2)
  have ⟨h0_y0, hy0_1, _⟩ := exitTri_orient2D_left hy0_tri h01_nf
  have ⟨h2_y1, hy1_3, _⟩ := exitTri_orient2D_left hy1_tri h23_nf
  have h_01_y1 : 0 < orient2D (S d0) (S d1) (S y1) :=
    exitTri_comb_pos hy1_tri h01_nf (le_of_lt (ccw6_lt cycD (by decide) (by decide)))
      (le_of_lt (ccw6_lt cycD (by decide) (by decide)))
  have h_23_y0 : 0 < orient2D (S d2) (S d3) (S y0) :=
    exitTri_comb_pos hy0_tri h23_nf
      (le_of_lt (by have h := ccw6_lt cycD (by decide : (0 : Fin 6) < 2) (by decide : (2 : Fin 6) < 3); unfold orient2D at h ⊢; linarith))
      (le_of_lt (by have h := ccw6_lt cycD (by decide : (1 : Fin 6) < 2) (by decide : (2 : Fin 6) < 3); unfold orient2D at h ⊢; linarith))
  let Goal := HexDisjGoal P S w O_star b y0 {d0} y0 y1 {d1, d2} y1 b {d3, d4}
  have build0 : GoodAnchorPair P S w O_star b y0 → 0 < orient2D v (S b) (S d0) → 0 < orient2D v (S b) (S y0) → Goal := by
    intro hgap h50 hby0
    refine ⟨b, y0, {d0}, Or.inl ⟨rfl, rfl, rfl⟩, hgap, good_gap_of_all_cross_hex hPoly h25 hgap (fun p hp => ?_)⟩
    rw [Finset.mem_singleton] at hp; subst hp
    exact ⟨cycD.inj.ne (by decide), fun h => hy0_notD (by rw [← h]; exact ccwCycle_mem cycD 0), h0_out, hB (ccwCycle_mem cycD 0),
      segmentsCross_inIntTri_left hy0_tri h50 h0_y0 hby0 (by rw [orient2D_self_right])
        (by have h := ccw6_lt cycD (by decide : (0 : Fin 6) < 1) (by decide : (1 : Fin 6) < 5); dsimp [b, d0, d1]; unfold orient2D at h ⊢; linarith)⟩
  have build12 : GoodAnchorPair P S w O_star y0 y1 →
      0 < orient2D v (S y0) (S d2) → 0 < orient2D v (S d1) (S y1) → 0 < orient2D v (S y0) (S y1) → Goal := by
    intro hgap hy0_2 hd1_y1 hy0_y1
    refine ⟨y0, y1, {d1, d2}, Or.inr (Or.inl ⟨rfl, rfl, rfl⟩), hgap, good_gap_of_all_cross_hex hPoly h25 hgap (fun p hp => ?_)⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp; rcases hp with rfl | rfl
    · exact ⟨fun h => hy0_notD (by rw [← h]; exact ccwCycle_mem cycD 1), fun h => hy1_notD (by rw [← h]; exact ccwCycle_mem cycD 1),
        h1_out, hB (ccwCycle_mem cycD 1), segmentsCross_between_exits_shared (u1 := (0, 0)) hy0_tri hy0_1 hd1_y1 hy0_y1 h_01_y1⟩
    · exact ⟨fun h => hy0_notD (by rw [← h]; exact ccwCycle_mem cycD 2), fun h => hy1_notD (by rw [← h]; exact ccwCycle_mem cycD 2),
        h2_out, hB (ccwCycle_mem cycD 2), segmentsCross_between_exits_shared_right hy1_tri hy0_2 h2_y1 hy0_y1 h_23_y0⟩
  have build34 : GoodAnchorPair P S w O_star y1 b →
      0 < orient2D v (S y1) (S d4) → 0 < orient2D v (S d4) (S b) →
      0 < orient2D v (S d3) (S b) → 0 < orient2D v (S y1) (S b) → Goal := by
    intro hgap hy1_4 h45 h35 hy1b
    refine ⟨y1, b, {d3, d4}, Or.inr (Or.inr ⟨rfl, rfl, rfl⟩), hgap, good_gap_of_all_cross_hex hPoly h25 hgap (fun p hp => ?_)⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp; rcases hp with rfl | rfl
    · exact ⟨fun h => hy1_notD (by rw [← h]; exact ccwCycle_mem cycD 3), cycD.inj.ne (by decide), h3_out, hB (ccwCycle_mem cycD 3),
        segmentsCross_inIntTri_right hy1_tri hy1_3 h35 hy1b (ccw6_lt cycD (by decide) (by decide)) (by dsimp [d3]; rw [orient2D_self_left])⟩
    · exact ⟨fun h => hy1_notD (by rw [← h]; exact ccwCycle_mem cycD 4), cycD.inj.ne (by decide), h4_out, hB (ccwCycle_mem cycD 4),
        segmentsCross_inIntTri_right hy1_tri hy1_4 h45 hy1b (ccw6_lt cycD (by decide) (by decide)) (le_of_lt (ccw6_lt cycD (by decide) (by decide)))⟩
  by_cases h_all_nf : ∀ m : Fin 6, 0 < orient2D (S (cycD.toFun m)) (S (cycD.toFun (m + 1))) v
  · by_cases hsee : Sees P v q
    · have h50 : 0 < orient2D v (S b) (S d0) := by have h := h_all_nf 5; dsimp [b, d0] at *; unfold orient2D at h ⊢; linarith
      have h12 : 0 < orient2D v (S d1) (S d2) := by have h := h_all_nf 1; dsimp [d1, d2] at *; unfold orient2D at h ⊢; linarith
      have h34 : 0 < orient2D v (S d3) (S d4) := by have h := h_all_nf 3; dsimp [d3, d4] at *; unfold orient2D at h ⊢; linarith
      have h45 : 0 < orient2D v (S d4) (S b) := by have h := h_all_nf 4; dsimp [d4, b] at *; unfold orient2D at h ⊢; linarith
      rcases hex23B5_cases _ _ _ _ _ _ _ _
        (hex_all_nf_not_all_same cycD v q h_all_nf hvq_D) (hexNoAlt4_of_orientSign cycD v q hvq_D)
        (exitTri_orientSign_of_endpoints hy0_tri (hvq_D 0) (hvq_D 1))
        (exitTri_orientSign_of_endpoints hy1_tri (hvq_D 2) (hvq_D 3)) with
        ⟨h50_s, h0y_s⟩ | ⟨hy01_s, h12_s, h2y_s⟩ | ⟨hy13_s, h34_s, h45_s⟩
      · have hby0 := chain3_orient_pos ⟨h50_s, h0y_s⟩ (hvq_D 5) (hvq_D 0) hvq_y0 h50 h0_y0
        exact build0 (goodAnchor_of_see hb_O hy0_O hb_ne_y0 hsee
          (onSameSide_of_orientSign_eq (h50_s.trans h0y_s) (hvq_D 5) hvq_y0) (ne_of_gt hby0)) h50 hby0
      · obtain ⟨hy0_2, hd1_y1, hy0_y1⟩ := chain4_orient_pos ⟨hy01_s, h12_s, h2y_s⟩ hvq_y0 (hvq_D 1) (hvq_D 2) hvq_y1 hy0_1 h12 h2_y1
        exact build12 (goodAnchor_of_see hy0_O hy1_O hy01 hsee
          (onSameSide_of_orientSign_eq (hy01_s.trans (h12_s.trans h2y_s)) hvq_y0 hvq_y1) (ne_of_gt hy0_y1)) hy0_2 hd1_y1 hy0_y1
      · obtain ⟨hy1_4, h35, hy1b⟩ := chain4_orient_pos ⟨hy13_s, h34_s, h45_s⟩ hvq_y1 (hvq_D 3) (hvq_D 4) (hvq_D 5) hy1_3 h34 h45
        exact build34 (goodAnchor_of_see hy1_O hb_O hy1_ne_b hsee
          (onSameSide_of_orientSign_eq (hy13_s.trans (h34_s.trans h45_s)) hvq_y1 (hvq_D 5)) (ne_of_gt hy1b)) hy1_4 h45 h35 hy1b
    · have hch := hexagon_seen5_chain_orient cycD v q 5 h_all_nf hvq_D
        (fun m hm => h_seen_ss (cycD.toFun 0) (cycD.toFun m) h0_out (hm_out m hm) hsee)
      have h12 : 0 < orient2D v (S d1) (S d2) := hch 1 2 (by decide)
      have h13 : 0 < orient2D v (S d1) (S d3) := hch 1 3 (by decide)
      have h02 : 0 < orient2D v (S d0) (S d2) := hch 0 2 (by decide)
      have h03 : 0 < orient2D v (S d0) (S d3) := hch 0 3 (by decide)
      have hd1_y1 := exitTri_before hy1_tri h12 h13
      have hy0_2 := exitTri_after hy0_tri h02 h12
      have hy0_y1 := exitTri_after hy0_tri (exitTri_before hy1_tri h02 h03) hd1_y1
      have hss0_y0 := (exitTri_sameSide_in_L hy0_tri (h_seen_ss d0 d1 h0_out h1_out hsee)).1
      have hss23 := h_seen_ss d2 d3 h2_out h3_out hsee
      have hss_y0_y1 := hss0_y0.symm.trans ((h_seen_ss d0 d2 h0_out h2_out hsee).trans (exitTri_sameSide_in_L hy1_tri hss23).1)
      have hss_y13 := (exitTri_sameSide_in_L hy1_tri hss23).2
      exact build12 (goodAnchor_of_cone_ends hy0_O hy1_O hy01 hss_y0_y1 hy0_y1
        (fun hqy0 => ⟨d0, h0_out, by unfold OnSameSide at hss0_y0; nlinarith, h0_y0⟩)
        (fun hqy0 => ⟨d3, h3_out, by unfold OnSameSide at hss_y0_y1 hss_y13; nlinarith, hy1_3⟩)) hy0_2 hd1_y1 hy0_y1
  · push Not at h_all_nf; obtain ⟨j0, hj0⟩ := h_all_nf
    obtain ⟨es, ee, L, hL1, hL5, heq, h_face_lt, _, _, _, _, h_ang⟩ :=
      facing_arc_complement_order cycD v hv_noncol ⟨j0, lt_of_le_of_ne hj0 (hv_noncol j0 (j0 + 1) (fin_add_one_ne_self j0))⟩
    have hc := hexFacing_elim hexFace_23_b5_all es ee L hL1 hL5 heq
      (fun h => by linarith [h_face_lt 0 h, h01_nf])
      (fun h => by linarith [h_face_lt 2 h, h23_nf])
      (fun ⟨h4, h5⟩ => hb_nf ((isFrontVertexOf_iff_ccwCycle cycD 5 v).mpr ⟨h_face_lt 4 h4, h_face_lt 5 h5⟩))
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hc
    rcases hc with (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) | hsc
    · -- [2, 3, 4, 5, 0, 1]
      have ho : ∀ a c : Fin 6, (a - 2).val < (c - 2).val → (c - 2).val ≤ (1 - 2 : Fin 6).val →
          0 < orient2D v (S (cycD.toFun a)) (S (cycD.toFun c)) := fun a c h1 h2 => (h_ang a c h1 h2).2
      have h35 := ho 3 5 (by decide) (by decide)
      have h45 := ho 4 5 (by decide) (by decide)
      have h50 := ho 5 0 (by decide) (by decide)
      have hy1_4 := exitTri_after hy1_tri (ho 2 4 (by decide) (by decide)) (ho 3 4 (by decide) (by decide))
      have hy1_5 := exitTri_after hy1_tri (ho 2 5 (by decide) (by decide)) h35
      have h5_y0 := exitTri_before hy0_tri h50 (ho 5 1 (by decide) (by decide))
      have hy1_y0 := exitTri_after hy1_tri
        (exitTri_before hy0_tri (ho 2 0 (by decide) (by decide)) (ho 2 1 (by decide) (by decide)))
        (exitTri_before hy0_tri (ho 3 0 (by decide) (by decide)) (ho 3 1 (by decide) (by decide)))
      by_cases hsee : Sees P v q
      · rcases three_missed_pigeonhole v q (S y1) (S b) (S y0) hvq_y1 (hvq_D 5) hvq_y0 hy1_5 h5_y0 hy1_y0 with hss1 | hss2
        · exact build34 (goodAnchor_of_see hy1_O hb_O hy1_ne_b hsee hss1 (ne_of_gt hy1_5)) hy1_4 h45 h35 hy1_5
        · exact build0 (goodAnchor_of_see hb_O hy0_O hb_ne_y0 hsee hss2 (ne_of_gt h5_y0)) h50 h5_y0
      · have hss21 := h_seen_ss d2 d1 h2_out h1_out hsee
        have hss2_5 := vq_between_sameSide hss21 (hvq_D 2)
          (ho 2 1 (by decide) (by decide)) (ho 2 5 (by decide) (by decide)) (ho 5 1 (by decide) (by decide))
        have hss2_y1 := (exitTri_sameSide_in_L hy1_tri (h_seen_ss d2 d3 h2_out h3_out hsee)).1
        have hss_y1_5 := hss2_y1.symm.trans hss2_5
        have hss5_1 := hss2_5.symm.trans hss21
        exact build34 (goodAnchor_of_cone_ends hy1_O hb_O hy1_ne_b hss_y1_5 hy1_5
          (fun hqy1 => ⟨d2, h2_out, by unfold OnSameSide at hss2_y1; nlinarith, h2_y1⟩)
          (fun hqy1 => ⟨d1, h1_out, by unfold OnSameSide at hss_y1_5 hss5_1; nlinarith, ho 5 1 (by decide) (by decide)⟩)) hy1_4 h45 h35 hy1_5
    · -- [0, 1, 2, 3, 4, 5]
      have ho : ∀ a c : Fin 6, (a - 0).val < (c - 0).val → (c - 0).val ≤ (5 - 0 : Fin 6).val →
          0 < orient2D v (S (cycD.toFun a)) (S (cycD.toFun c)) := fun a c h1 h2 => (h_ang a c h1 h2).2
      have h12 := ho 1 2 (by decide) (by decide)
      have h35 := ho 3 5 (by decide) (by decide)
      have h45 := ho 4 5 (by decide) (by decide)
      have hd1_y1 := exitTri_before hy1_tri h12 (ho 1 3 (by decide) (by decide))
      have hy0_2 := exitTri_after hy0_tri (ho 0 2 (by decide) (by decide)) h12
      have hy0_y1 := exitTri_after hy0_tri (exitTri_before hy1_tri (ho 0 2 (by decide) (by decide)) (ho 0 3 (by decide) (by decide))) hd1_y1
      have hy1_4 := exitTri_after hy1_tri (ho 2 4 (by decide) (by decide)) (ho 3 4 (by decide) (by decide))
      have hy1_5 := exitTri_after hy1_tri (ho 2 5 (by decide) (by decide)) h35
      have hy0_5 := exitTri_after hy0_tri (ho 0 5 (by decide) (by decide)) (ho 1 5 (by decide) (by decide))
      by_cases hsee : Sees P v q
      · rcases three_missed_pigeonhole v q (S y0) (S y1) (S b) hvq_y0 hvq_y1 (hvq_D 5) hy0_y1 hy1_5 hy0_5 with hss1 | hss2
        · exact build12 (goodAnchor_of_see hy0_O hy1_O hy01 hsee hss1 (ne_of_gt hy0_y1)) hy0_2 hd1_y1 hy0_y1
        · exact build34 (goodAnchor_of_see hy1_O hb_O hy1_ne_b hsee hss2 (ne_of_gt hy1_5)) hy1_4 h45 h35 hy1_5
      · have hss0_y0 := (exitTri_sameSide_in_L hy0_tri (h_seen_ss d0 d1 h0_out h1_out hsee)).1
        have hss23 := h_seen_ss d2 d3 h2_out h3_out hsee
        have hss_y0_y1 := hss0_y0.symm.trans ((h_seen_ss d0 d2 h0_out h2_out hsee).trans (exitTri_sameSide_in_L hy1_tri hss23).1)
        have hss_y13 := (exitTri_sameSide_in_L hy1_tri hss23).2
        exact build12 (goodAnchor_of_cone_ends hy0_O hy1_O hy01 hss_y0_y1 hy0_y1
          (fun hqy0 => ⟨d0, h0_out, by unfold OnSameSide at hss0_y0; nlinarith, h0_y0⟩)
          (fun hqy0 => ⟨d3, h3_out, by unfold OnSameSide at hss_y0_y1 hss_y13; nlinarith, hy1_3⟩)) hy0_2 hd1_y1 hy0_y1
    · -- subchain [5, 0, 1, 2, 3]
      have ho := subchain5_orient (fun a c h1 h2 => (h_ang a c h1 h2).2) hsc
      have h50 : 0 < orient2D v (S b) (S d0) := ho 0 1 (by decide)
      have h12 : 0 < orient2D v (S d1) (S d2) := ho 2 3 (by decide)
      have h5_y0 := exitTri_before hy0_tri h50 (ho 0 2 (by decide))
      have hd1_y1 := exitTri_before hy1_tri h12 (ho 2 4 (by decide))
      have hy0_2 := exitTri_after hy0_tri (ho 1 3 (by decide)) h12
      have hy0_y1 := exitTri_after hy0_tri (exitTri_before hy1_tri (ho 1 3 (by decide)) (ho 1 4 (by decide))) hd1_y1
      have h5_y1 := exitTri_before hy1_tri (ho 0 3 (by decide)) (ho 0 4 (by decide))
      by_cases hsee : Sees P v q
      · rcases three_missed_pigeonhole v q (S b) (S y0) (S y1) (hvq_D 5) hvq_y0 hvq_y1 h5_y0 hy0_y1 h5_y1 with hss1 | hss2
        · exact build0 (goodAnchor_of_see hb_O hy0_O hb_ne_y0 hsee hss1 (ne_of_gt h5_y0)) h50 h5_y0
        · exact build12 (goodAnchor_of_see hy0_O hy1_O hy01 hsee hss2 (ne_of_gt hy0_y1)) hy0_2 hd1_y1 hy0_y1
      · have hss0_y0 := (exitTri_sameSide_in_L hy0_tri (h_seen_ss d0 d1 h0_out h1_out hsee)).1
        have hss23 := h_seen_ss d2 d3 h2_out h3_out hsee
        have hss_y0_y1 := hss0_y0.symm.trans ((h_seen_ss d0 d2 h0_out h2_out hsee).trans (exitTri_sameSide_in_L hy1_tri hss23).1)
        have hss_y13 := (exitTri_sameSide_in_L hy1_tri hss23).2
        exact build12 (goodAnchor_of_cone_ends hy0_O hy1_O hy01 hss_y0_y1 hy0_y1
          (fun hqy0 => ⟨d0, h0_out, by unfold OnSameSide at hss0_y0; nlinarith, h0_y0⟩)
          (fun hqy0 => ⟨d3, h3_out, by unfold OnSameSide at hss_y0_y1 hss_y13; nlinarith, hy1_3⟩)) hy0_2 hd1_y1 hy0_y1

/-- **Lemma 5.11(ii), `b = 2` (`hexagon-disjoint-exits`, `upper_8.tex`)**:
    For `D = (0, 1, 2, 3, 4, 5)` and `y0, y1 ∈ M` on opposite exit edges `01` and `34`,
    with `O* = {2, y0, y1}`, at least one of `{3}` (`{2, y1}`), `{4, 5, 0}` (`{y1, y0}`),
    or `{1}` (`{y0, 2}`) is a good gap for `v`. -/
theorem hexagon_disjoint_exits_34_b2 {n : ℕ} {P : Set (ℝ × ℝ)}
    {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ}
    (hPoly : ShatteredSimplePolygon P S w) (h25 : Sec2To5Interface P S w)
    {D : Finset (Fin n)} (hDB : D = hullVertices S \ certifiedVertices S w)
    (cycD : CCWCycle S D 3)
    {y0 y1 : Fin n} (hy0M : y0 ∈ Finset.univ \ D) (hy1M : y1 ∈ Finset.univ \ D) (hy01 : y0 ≠ y1)
    (hy0_tri : InIntTri (w (Finset.univ \ {cycD.toFun 2, y0, y1})) (S (cycD.toFun 0)) (S (cycD.toFun 1)) (S y0))
    (hy1_tri : InIntTri (w (Finset.univ \ {cycD.toFun 2, y0, y1})) (S (cycD.toFun 3)) (S (cycD.toFun 4)) (S y1))
    (h_not_lr : ∀ l r : Fin n, (certifiedVertices S w).Nonempty →
      IsCCWEdge S D l r → (∀ h ∈ certifiedVertices S w, orient2D (S l) (S r) (S h) < 0) →
      (cycD.toFun 0, cycD.toFun 1) ≠ (l, r) ∧ (cycD.toFun 3, cycD.toFun 4) ≠ (l, r)) :
    let b := cycD.toFun 2
    let O_star : Finset (Fin n) := {b, y0, y1}
    let v := w (Finset.univ \ O_star)
    ∃ (oa ob : Fin n) (Γ : Finset (Fin n)),
      ((oa = b ∧ ob = y1 ∧ Γ = {cycD.toFun 3}) ∨
       (oa = y1 ∧ ob = y0 ∧ Γ = {cycD.toFun 4, cycD.toFun 5, cycD.toFun 0}) ∨
       (oa = y0 ∧ ob = b ∧ Γ = {cycD.toFun 1})) ∧
      GoodAnchorPair P S w O_star oa ob ∧
      (∀ p ∈ Γ, IsBackVertexOf S (hullVertices S) p v ∧ SegmentsCross v (S p) (S oa) (S ob) ∧
        (∃ H_hp : OpenHalfPlane, IsHalfPlaneTest P (WitnessSet {oa, ob} ∅ w) (S p) H_hp)) ∧
      (∀ z : Fin n, z ≠ oa → z ≠ ob → z ∉ O_star →
        S z ∈ convexHull ℝ ((Γ ∪ {oa, ob}).image S : Set (ℝ × ℝ)) →
        SegmentsCross v (S z) (S oa) (S ob) ∧
        (∃ H_hp : OpenHalfPlane, IsHalfPlaneTest P (WitnessSet {oa, ob} ∅ w) (S z) H_hp) ∧
        (z ∈ hullVertices S → IsBackVertexOf S (hullVertices S) z v)) := by
  intro b O_star v
  let d0 := cycD.toFun 0; let d1 := cycD.toFun 1; let d3 := cycD.toFun 3
  let d4 := cycD.toFun 4; let d5 := cycD.toFun 5; let q := w Finset.univ
  have hy0_notD : y0 ∉ D := (Finset.mem_sdiff.mp hy0M).2
  have hy1_notD : y1 ∉ D := (Finset.mem_sdiff.mp hy1M).2
  obtain ⟨hm_out, hb_nf, hv_noncol, hvq_D, hvq_y0, hvq_y1, h_seen_ss⟩ :=
    hexagon_Ostar_core hPoly h25 hDB cycD hy0M hy1M hy01 2
  have h0_out := hm_out 0 (by decide); have h1_out := hm_out 1 (by decide)
  have h3_out := hm_out 3 (by decide); have h4_out := hm_out 4 (by decide)
  have h5_out := hm_out 5 (by decide)
  have hB : D ⊆ hullVertices S := hDB ▸ Finset.sdiff_subset
  have hb_O : b ∈ O_star := by simp [O_star]
  have hy0_O : y0 ∈ O_star := by simp [O_star]
  have hy1_O : y1 ∈ O_star := by simp [O_star]
  have hb_ne_y1 : b ≠ y1 := fun h => hy1_notD (h ▸ ccwCycle_mem cycD 2)
  have hy0_ne_b : y0 ≠ b := fun h => hy0_notD (h.symm ▸ ccwCycle_mem cycD 2)
  have h01_nf := hexagon_exit_nonfacing hPoly h25 hDB cycD hy0M 0 hy0_tri (fun l r hH he hHn => (h_not_lr l r hH he hHn).1)
  have h34_nf := hexagon_exit_nonfacing hPoly h25 hDB cycD hy1M 3 hy1_tri (fun l r hH he hHn => (h_not_lr l r hH he hHn).2)
  have ⟨h0_y0, hy0_1, _⟩ := exitTri_orient2D_left hy0_tri h01_nf
  have ⟨h3_y1, hy1_4, _⟩ := exitTri_orient2D_left hy1_tri h34_nf
  have h_34_y0 : 0 < orient2D (S d3) (S d4) (S y0) :=
    exitTri_comb_pos hy0_tri h34_nf
      (le_of_lt (by have h := ccw6_lt cycD (by decide : (0 : Fin 6) < 3) (by decide : (3 : Fin 6) < 4); unfold orient2D at h ⊢; linarith))
      (le_of_lt (by have h := ccw6_lt cycD (by decide : (1 : Fin 6) < 3) (by decide : (3 : Fin 6) < 4); unfold orient2D at h ⊢; linarith))
  have h_01_y1 : 0 < orient2D (S d0) (S d1) (S y1) :=
    exitTri_comb_pos hy1_tri h01_nf (le_of_lt (ccw6_lt cycD (by decide) (by decide)))
      (le_of_lt (ccw6_lt cycD (by decide) (by decide)))
  let Goal := HexDisjGoal P S w O_star b y1 {d3} y1 y0 {d4, d5, d0} y0 b {d1}
  have build3 : GoodAnchorPair P S w O_star b y1 → 0 < orient2D v (S b) (S d3) → 0 < orient2D v (S b) (S y1) → Goal := by
    intro hgap h23 hby1
    refine ⟨b, y1, {d3}, Or.inl ⟨rfl, rfl, rfl⟩, hgap, good_gap_of_all_cross_hex hPoly h25 hgap (fun p hp => ?_)⟩
    rw [Finset.mem_singleton] at hp; subst hp
    exact ⟨cycD.inj.ne (by decide), fun h => hy1_notD (by rw [← h]; exact ccwCycle_mem cycD 3), h3_out, hB (ccwCycle_mem cycD 3),
      segmentsCross_inIntTri_left hy1_tri h23 h3_y1 hby1 (by rw [orient2D_self_right])
        (ccw6_lt cycD (by decide) (by decide))⟩
  have build1 : GoodAnchorPair P S w O_star y0 b → 0 < orient2D v (S d1) (S b) → 0 < orient2D v (S y0) (S b) → Goal := by
    intro hgap h12 hy0b
    refine ⟨y0, b, {d1}, Or.inr (Or.inr ⟨rfl, rfl, rfl⟩), hgap, good_gap_of_all_cross_hex hPoly h25 hgap (fun p hp => ?_)⟩
    rw [Finset.mem_singleton] at hp; subst hp
    exact ⟨fun h => hy0_notD (by rw [← h]; exact ccwCycle_mem cycD 1), cycD.inj.ne (by decide), h1_out, hB (ccwCycle_mem cycD 1),
      segmentsCross_inIntTri_right hy0_tri hy0_1 h12 hy0b (ccw6_lt cycD (by decide) (by decide)) (by dsimp [d1]; rw [orient2D_self_left])⟩
  have build450 : GoodAnchorPair P S w O_star y1 y0 →
      0 < orient2D v (S d4) (S d5) → 0 < orient2D v (S d5) (S d0) → 0 < orient2D v (S d4) (S d0) →
      0 < orient2D v (S d4) (S y0) → 0 < orient2D v (S y1) (S d0) →
      0 < orient2D v (S y1) (S d5) → 0 < orient2D v (S d5) (S y0) →
      0 < orient2D v (S y1) (S y0) → Goal := by
    intro hgap h45 h50 h40 h4y0 hy1_0 hy1_5 h5y0 hy1_y0
    have hcr4 := segmentsCross_between_exits_shared (u1 := (0, 0)) hy1_tri hy1_4 h4y0 hy1_y0 h_34_y0
    have hcr0 := segmentsCross_between_exits_shared_right hy0_tri hy1_0 h0_y0 hy1_y0 h_01_y1
    have hccw450 : 0 < orient2D (S d4) (S d5) (S d0) := by
      have h := ccw6_lt cycD (by decide : (0 : Fin 6) < 4) (by decide : (4 : Fin 6) < 5); unfold orient2D at h ⊢; linarith
    have hcr5 := segmentsCross_middle_of_endpoints_cross hcr4 hcr0 hy1_y0 h45 h50 h40 hccw450 hy1_5 h5y0
    refine ⟨y1, y0, {d4, d5, d0}, Or.inr (Or.inl ⟨rfl, rfl, rfl⟩), hgap, good_gap_of_all_cross_hex hPoly h25 hgap (fun p hp => ?_)⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp; rcases hp with rfl | rfl | rfl
    · exact ⟨fun h => hy1_notD (by rw [← h]; exact ccwCycle_mem cycD 4), fun h => hy0_notD (by rw [← h]; exact ccwCycle_mem cycD 4),
        h4_out, hB (ccwCycle_mem cycD 4), hcr4⟩
    · exact ⟨fun h => hy1_notD (by rw [← h]; exact ccwCycle_mem cycD 5), fun h => hy0_notD (by rw [← h]; exact ccwCycle_mem cycD 5),
        h5_out, hB (ccwCycle_mem cycD 5), hcr5⟩
    · exact ⟨fun h => hy1_notD (by rw [← h]; exact ccwCycle_mem cycD 0), fun h => hy0_notD (by rw [← h]; exact ccwCycle_mem cycD 0),
        h0_out, hB (ccwCycle_mem cycD 0), hcr0⟩
  by_cases h_all_nf : ∀ m : Fin 6, 0 < orient2D (S (cycD.toFun m)) (S (cycD.toFun (m + 1))) v
  · by_cases hsee : Sees P v q
    · have h23 : 0 < orient2D v (S b) (S d3) := by have h := h_all_nf 2; dsimp [b, d3] at *; unfold orient2D at h ⊢; linarith
      have h45 : 0 < orient2D v (S d4) (S d5) := by have h := h_all_nf 4; dsimp [d4, d5] at *; unfold orient2D at h ⊢; linarith
      have h50 : 0 < orient2D v (S d5) (S d0) := by have h := h_all_nf 5; dsimp [d5, d0] at *; unfold orient2D at h ⊢; linarith
      have h12 : 0 < orient2D v (S d1) (S b) := by have h := h_all_nf 1; dsimp [d1, b] at *; unfold orient2D at h ⊢; linarith
      rcases hex34B2_cases _ _ _ _ _ _ _ _
        (hex_all_nf_not_all_same cycD v q h_all_nf hvq_D) (hexNoAlt4_of_orientSign cycD v q hvq_D)
        (exitTri_orientSign_of_endpoints hy0_tri (hvq_D 0) (hvq_D 1))
        (exitTri_orientSign_of_endpoints hy1_tri (hvq_D 3) (hvq_D 4)) with
        ⟨h23_s, h3y1_s⟩ | ⟨hy14_s, h45_s, h50_s, h0y0_s⟩ | ⟨hy01_s, h12_s⟩
      · have hby1 := chain3_orient_pos ⟨h23_s, h3y1_s⟩ (hvq_D 2) (hvq_D 3) hvq_y1 h23 h3_y1
        exact build3 (goodAnchor_of_see hb_O hy1_O hb_ne_y1 hsee
          (onSameSide_of_orientSign_eq (h23_s.trans h3y1_s) (hvq_D 2) hvq_y1) (ne_of_gt hby1)) h23 hby1
      · obtain ⟨hy1_5, hy1_0, h4y0, h5y0, hy1_y0⟩ := chain5_orient_pos ⟨hy14_s, h45_s, h50_s, h0y0_s⟩
          hvq_y1 (hvq_D 4) (hvq_D 5) (hvq_D 0) hvq_y0 hy1_4 h45 h50 h0_y0
        have h40 := chain3_orient_pos ⟨h45_s, h50_s⟩ (hvq_D 4) (hvq_D 5) (hvq_D 0) h45 h50
        exact build450 (goodAnchor_of_see hy1_O hy0_O hy01.symm hsee
          (onSameSide_of_orientSign_eq (hy14_s.trans (h45_s.trans (h50_s.trans h0y0_s))) hvq_y1 hvq_y0) (ne_of_gt hy1_y0))
          h45 h50 h40 h4y0 hy1_0 hy1_5 h5y0 hy1_y0
      · have hy0b := chain3_orient_pos ⟨hy01_s, h12_s⟩ hvq_y0 (hvq_D 1) (hvq_D 2) hy0_1 h12
        exact build1 (goodAnchor_of_see hy0_O hb_O hy0_ne_b hsee
          (onSameSide_of_orientSign_eq (hy01_s.trans h12_s) hvq_y0 (hvq_D 2)) (ne_of_gt hy0b)) h12 hy0b
    · have hch := hexagon_seen5_chain_orient cycD v q 2 h_all_nf hvq_D
        (fun m hm => h_seen_ss (cycD.toFun 3) (cycD.toFun m) h3_out (hm_out m hm) hsee)
      -- c = [3, 4, 5, 0, 1]
      have h45 : 0 < orient2D v (S d4) (S d5) := hch 1 2 (by decide)
      have h50 : 0 < orient2D v (S d5) (S d0) := hch 2 3 (by decide)
      have h40 : 0 < orient2D v (S d4) (S d0) := hch 1 3 (by decide)
      have h4y0 := exitTri_before hy0_tri h40 (hch 1 4 (by decide))
      have h5y0 := exitTri_before hy0_tri h50 (hch 2 4 (by decide))
      have hy1_5 := exitTri_after hy1_tri (hch 0 2 (by decide)) h45
      have hy1_0 := exitTri_after hy1_tri (hch 0 3 (by decide)) h40
      have hy1_y0 := exitTri_after hy1_tri (exitTri_before hy0_tri (hch 0 3 (by decide)) (hch 0 4 (by decide))) h4y0
      have hss3_y1 := (exitTri_sameSide_in_L hy1_tri (h_seen_ss d3 d4 h3_out h4_out hsee)).1
      have hss01 := h_seen_ss d0 d1 h0_out h1_out hsee
      have hss_y1_y0 := hss3_y1.symm.trans ((h_seen_ss d3 d0 h3_out h0_out hsee).trans (exitTri_sameSide_in_L hy0_tri hss01).1)
      have hss_y01 := (exitTri_sameSide_in_L hy0_tri hss01).2
      exact build450 (goodAnchor_of_cone_ends hy1_O hy0_O hy01.symm hss_y1_y0 hy1_y0
        (fun hqy1 => ⟨d3, h3_out, by unfold OnSameSide at hss3_y1; nlinarith, h3_y1⟩)
        (fun hqy1 => ⟨d1, h1_out, by unfold OnSameSide at hss_y1_y0 hss_y01; nlinarith, hy0_1⟩))
        h45 h50 h40 h4y0 hy1_0 hy1_5 h5y0 hy1_y0
  · push Not at h_all_nf; obtain ⟨j0, hj0⟩ := h_all_nf
    obtain ⟨es, ee, L, hL1, hL5, heq, h_face_lt, _, _, _, _, h_ang⟩ :=
      facing_arc_complement_order cycD v hv_noncol ⟨j0, lt_of_le_of_ne hj0 (hv_noncol j0 (j0 + 1) (fin_add_one_ne_self j0))⟩
    have hc := hexFacing_elim hexFace_34_b2_all es ee L hL1 hL5 heq
      (fun h => by linarith [h_face_lt 0 h, h01_nf])
      (fun h => by linarith [h_face_lt 3 h, h34_nf])
      (fun ⟨h1, h2⟩ => hb_nf ((isFrontVertexOf_iff_ccwCycle cycD 2 v).mpr ⟨h_face_lt 1 h1, h_face_lt 2 h2⟩))
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hc
    rcases hc with (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) | hsc
    · -- [2, 3, 4, 5, 0, 1]
      have ho : ∀ a c : Fin 6, (a - 2).val < (c - 2).val → (c - 2).val ≤ (1 - 2 : Fin 6).val →
          0 < orient2D v (S (cycD.toFun a)) (S (cycD.toFun c)) := fun a c h1 h2 => (h_ang a c h1 h2).2
      have h23 := ho 2 3 (by decide) (by decide)
      have h45 := ho 4 5 (by decide) (by decide)
      have h50 := ho 5 0 (by decide) (by decide)
      have h40 := ho 4 0 (by decide) (by decide)
      have h2_y1 := exitTri_before hy1_tri h23 (ho 2 4 (by decide) (by decide))
      have h4y0 := exitTri_before hy0_tri h40 (ho 4 1 (by decide) (by decide))
      have h5y0 := exitTri_before hy0_tri h50 (ho 5 1 (by decide) (by decide))
      have hy1_5 := exitTri_after hy1_tri (ho 3 5 (by decide) (by decide)) h45
      have hy1_0 := exitTri_after hy1_tri (ho 3 0 (by decide) (by decide)) h40
      have hy1_y0 := exitTri_after hy1_tri (exitTri_before hy0_tri (ho 3 0 (by decide) (by decide)) (ho 3 1 (by decide) (by decide))) h4y0
      have h2_y0 := exitTri_before hy0_tri (ho 2 0 (by decide) (by decide)) (ho 2 1 (by decide) (by decide))
      by_cases hsee : Sees P v q
      · rcases three_missed_pigeonhole v q (S b) (S y1) (S y0) (hvq_D 2) hvq_y1 hvq_y0 h2_y1 hy1_y0 h2_y0 with hss1 | hss2
        · exact build3 (goodAnchor_of_see hb_O hy1_O hb_ne_y1 hsee hss1 (ne_of_gt h2_y1)) h23 h2_y1
        · exact build450 (goodAnchor_of_see hy1_O hy0_O hy01.symm hsee hss2 (ne_of_gt hy1_y0))
            h45 h50 h40 h4y0 hy1_0 hy1_5 h5y0 hy1_y0
      · have hss3_y1 := (exitTri_sameSide_in_L hy1_tri (h_seen_ss d3 d4 h3_out h4_out hsee)).1
        have hss01 := h_seen_ss d0 d1 h0_out h1_out hsee
        have hss_y1_y0 := hss3_y1.symm.trans ((h_seen_ss d3 d0 h3_out h0_out hsee).trans (exitTri_sameSide_in_L hy0_tri hss01).1)
        have hss_y01 := (exitTri_sameSide_in_L hy0_tri hss01).2
        exact build450 (goodAnchor_of_cone_ends hy1_O hy0_O hy01.symm hss_y1_y0 hy1_y0
          (fun hqy1 => ⟨d3, h3_out, by unfold OnSameSide at hss3_y1; nlinarith, h3_y1⟩)
          (fun hqy1 => ⟨d1, h1_out, by unfold OnSameSide at hss_y1_y0 hss_y01; nlinarith, hy0_1⟩))
          h45 h50 h40 h4y0 hy1_0 hy1_5 h5y0 hy1_y0
    · -- [3, 4, 5, 0, 1, 2]
      have ho : ∀ a c : Fin 6, (a - 3).val < (c - 3).val → (c - 3).val ≤ (2 - 3 : Fin 6).val →
          0 < orient2D v (S (cycD.toFun a)) (S (cycD.toFun c)) := fun a c h1 h2 => (h_ang a c h1 h2).2
      have h45 := ho 4 5 (by decide) (by decide)
      have h50 := ho 5 0 (by decide) (by decide)
      have h40 := ho 4 0 (by decide) (by decide)
      have h12 := ho 1 2 (by decide) (by decide)
      have h4y0 := exitTri_before hy0_tri h40 (ho 4 1 (by decide) (by decide))
      have h5y0 := exitTri_before hy0_tri h50 (ho 5 1 (by decide) (by decide))
      have hy1_5 := exitTri_after hy1_tri (ho 3 5 (by decide) (by decide)) h45
      have hy1_0 := exitTri_after hy1_tri (ho 3 0 (by decide) (by decide)) h40
      have hy1_y0 := exitTri_after hy1_tri (exitTri_before hy0_tri (ho 3 0 (by decide) (by decide)) (ho 3 1 (by decide) (by decide))) h4y0
      have hy0_2 := exitTri_after hy0_tri (ho 0 2 (by decide) (by decide)) h12
      have hy1_2 := exitTri_after hy1_tri (ho 3 2 (by decide) (by decide)) (ho 4 2 (by decide) (by decide))
      by_cases hsee : Sees P v q
      · rcases three_missed_pigeonhole v q (S y1) (S y0) (S b) hvq_y1 hvq_y0 (hvq_D 2) hy1_y0 hy0_2 hy1_2 with hss1 | hss2
        · exact build450 (goodAnchor_of_see hy1_O hy0_O hy01.symm hsee hss1 (ne_of_gt hy1_y0))
            h45 h50 h40 h4y0 hy1_0 hy1_5 h5y0 hy1_y0
        · exact build1 (goodAnchor_of_see hy0_O hb_O hy0_ne_b hsee hss2 (ne_of_gt hy0_2)) h12 hy0_2
      · have hss3_y1 := (exitTri_sameSide_in_L hy1_tri (h_seen_ss d3 d4 h3_out h4_out hsee)).1
        have hss01 := h_seen_ss d0 d1 h0_out h1_out hsee
        have hss_y1_y0 := hss3_y1.symm.trans ((h_seen_ss d3 d0 h3_out h0_out hsee).trans (exitTri_sameSide_in_L hy0_tri hss01).1)
        have hss_y01 := (exitTri_sameSide_in_L hy0_tri hss01).2
        exact build450 (goodAnchor_of_cone_ends hy1_O hy0_O hy01.symm hss_y1_y0 hy1_y0
          (fun hqy1 => ⟨d3, h3_out, by unfold OnSameSide at hss3_y1; nlinarith, h3_y1⟩)
          (fun hqy1 => ⟨d1, h1_out, by unfold OnSameSide at hss_y1_y0 hss_y01; nlinarith, hy0_1⟩))
          h45 h50 h40 h4y0 hy1_0 hy1_5 h5y0 hy1_y0
    · -- subchain [0, 1, 2, 3, 4]
      have ho := subchain5_orient (fun a c h1 h2 => (h_ang a c h1 h2).2) hsc
      have h12 : 0 < orient2D v (S d1) (S b) := ho 1 2 (by decide)
      have h23 : 0 < orient2D v (S b) (S d3) := ho 2 3 (by decide)
      have hy0_2 := exitTri_after hy0_tri (ho 0 2 (by decide)) h12
      have h2_y1 := exitTri_before hy1_tri h23 (ho 2 4 (by decide))
      have hy0_y1 := exitTri_after hy0_tri
        (exitTri_before hy1_tri (ho 0 3 (by decide)) (ho 0 4 (by decide)))
        (exitTri_before hy1_tri (ho 1 3 (by decide)) (ho 1 4 (by decide)))
      by_cases hsee : Sees P v q
      · rcases three_missed_pigeonhole v q (S y0) (S b) (S y1) hvq_y0 (hvq_D 2) hvq_y1 hy0_2 h2_y1 hy0_y1 with hss1 | hss2
        · exact build1 (goodAnchor_of_see hy0_O hb_O hy0_ne_b hsee hss1 (ne_of_gt hy0_2)) h12 hy0_2
        · exact build3 (goodAnchor_of_see hb_O hy1_O hb_ne_y1 hsee hss2 (ne_of_gt h2_y1)) h23 h2_y1
      · have hss04 := h_seen_ss d0 d4 h0_out h4_out hsee
        have hss0_2 := vq_between_sameSide hss04 (hvq_D 0) (ho 0 4 (by decide)) (ho 0 2 (by decide)) (ho 2 4 (by decide))
        have hss0_y0 := (exitTri_sameSide_in_L hy0_tri (h_seen_ss d0 d1 h0_out h1_out hsee)).1
        have hss_y0_2 := hss0_y0.symm.trans hss0_2
        have hss2_4 := hss0_2.symm.trans hss04
        exact build1 (goodAnchor_of_cone_ends hy0_O hb_O hy0_ne_b hss_y0_2 hy0_2
          (fun hqy0 => ⟨d0, h0_out, by unfold OnSameSide at hss0_y0; nlinarith, h0_y0⟩)
          (fun hqy0 => ⟨d4, h4_out, by unfold OnSameSide at hss_y0_2 hss2_4; nlinarith, ho 2 4 (by decide)⟩)) h12 hy0_2

/-- **Lemma 5.12(i), `b = 5` (`hexagon-adjacent-exits`, `upper_8.tex`)**:
    For `D = (0, 1, 2, 3, 4, 5)` and `y0, y1 ∈ M` on adjacent exit edges `01` and `12`,
    with `O* = {5, y0, y1}`, at least one of `{0}` (`{5, y0}`), `{1}` (`{y0, y1}`),
    or `{2, 3, 4}` (`{y1, 5}`) is a good gap for `v`. -/
theorem hexagon_adjacent_exits_b5 {n : ℕ} {P : Set (ℝ × ℝ)}
    {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ}
    (hPoly : ShatteredSimplePolygon P S w) (h25 : Sec2To5Interface P S w)
    {D : Finset (Fin n)} (hDB : D = hullVertices S \ certifiedVertices S w)
    (cycD : CCWCycle S D 3)
    {y0 y1 : Fin n} (hy0M : y0 ∈ Finset.univ \ D) (hy1M : y1 ∈ Finset.univ \ D) (hy01 : y0 ≠ y1)
    (hy0_tri : InIntTri (w (Finset.univ \ {cycD.toFun 5, y0, y1})) (S (cycD.toFun 0)) (S (cycD.toFun 1)) (S y0))
    (hy1_tri : InIntTri (w (Finset.univ \ {cycD.toFun 5, y0, y1})) (S (cycD.toFun 1)) (S (cycD.toFun 2)) (S y1))
    (h_not_lr : ∀ l r : Fin n, (certifiedVertices S w).Nonempty →
      IsCCWEdge S D l r → (∀ h ∈ certifiedVertices S w, orient2D (S l) (S r) (S h) < 0) →
      (cycD.toFun 0, cycD.toFun 1) ≠ (l, r) ∧ (cycD.toFun 1, cycD.toFun 2) ≠ (l, r)) :
    let b := cycD.toFun 5
    let O_star : Finset (Fin n) := {b, y0, y1}
    let v := w (Finset.univ \ O_star)
    ∃ (oa ob : Fin n) (Γ : Finset (Fin n)),
      ((oa = b ∧ ob = y0 ∧ Γ = {cycD.toFun 0}) ∨
       (oa = y0 ∧ ob = y1 ∧ Γ = {cycD.toFun 1}) ∨
       (oa = y1 ∧ ob = b ∧ Γ = {cycD.toFun 2, cycD.toFun 3, cycD.toFun 4})) ∧
      GoodAnchorPair P S w O_star oa ob ∧
      (∀ p ∈ Γ, IsBackVertexOf S (hullVertices S) p v ∧ SegmentsCross v (S p) (S oa) (S ob) ∧
        (∃ H_hp : OpenHalfPlane, IsHalfPlaneTest P (WitnessSet {oa, ob} ∅ w) (S p) H_hp)) ∧
      (∀ z : Fin n, z ≠ oa → z ≠ ob → z ∉ O_star →
        S z ∈ convexHull ℝ ((Γ ∪ {oa, ob}).image S : Set (ℝ × ℝ)) →
        SegmentsCross v (S z) (S oa) (S ob) ∧
        (∃ H_hp : OpenHalfPlane, IsHalfPlaneTest P (WitnessSet {oa, ob} ∅ w) (S z) H_hp) ∧
        (z ∈ hullVertices S → IsBackVertexOf S (hullVertices S) z v)) := by
  intro b O_star v
  let d0 := cycD.toFun 0; let d1 := cycD.toFun 1; let d2 := cycD.toFun 2
  let d3 := cycD.toFun 3; let d4 := cycD.toFun 4; let q := w Finset.univ
  have hy0_notD : y0 ∉ D := (Finset.mem_sdiff.mp hy0M).2
  have hy1_notD : y1 ∉ D := (Finset.mem_sdiff.mp hy1M).2
  obtain ⟨hm_out, hb_nf, hv_noncol, hvq_D, hvq_y0, hvq_y1, h_seen_ss⟩ :=
    hexagon_Ostar_core hPoly h25 hDB cycD hy0M hy1M hy01 5
  have h0_out := hm_out 0 (by decide); have h1_out := hm_out 1 (by decide)
  have h2_out := hm_out 2 (by decide); have h3_out := hm_out 3 (by decide)
  have h4_out := hm_out 4 (by decide)
  have hB : D ⊆ hullVertices S := hDB ▸ Finset.sdiff_subset
  have hb_O : b ∈ O_star := by simp [O_star]
  have hy0_O : y0 ∈ O_star := by simp [O_star]
  have hy1_O : y1 ∈ O_star := by simp [O_star]
  have hb_ne_y0 : b ≠ y0 := fun h => hy0_notD (h ▸ ccwCycle_mem cycD 5)
  have hy1_ne_b : y1 ≠ b := fun h => hy1_notD (h.symm ▸ ccwCycle_mem cycD 5)
  have h01_nf := hexagon_exit_nonfacing hPoly h25 hDB cycD hy0M 0 hy0_tri (fun l r hH he hHn => (h_not_lr l r hH he hHn).1)
  have h12_nf := hexagon_exit_nonfacing hPoly h25 hDB cycD hy1M 1 hy1_tri (fun l r hH he hHn => (h_not_lr l r hH he hHn).2)
  have ⟨h0_y0, hy0_1, _⟩ := exitTri_orient2D_left hy0_tri h01_nf
  have ⟨h1_y1, hy1_2, _⟩ := exitTri_orient2D_left hy1_tri h12_nf
  have h_01_y1 : 0 < orient2D (S d0) (S d1) (S y1) :=
    exitTri_comb_pos hy1_tri h01_nf (by rw [orient2D_self_right]) (le_of_lt (ccw6_lt cycD (by decide) (by decide)))
  let Goal := HexDisjGoal P S w O_star b y0 {d0} y0 y1 {d1} y1 b {d2, d3, d4}
  have build0 : GoodAnchorPair P S w O_star b y0 → 0 < orient2D v (S b) (S d0) → 0 < orient2D v (S b) (S y0) → Goal := by
    intro hgap h50 hby0
    refine ⟨b, y0, {d0}, Or.inl ⟨rfl, rfl, rfl⟩, hgap, good_gap_of_all_cross_hex hPoly h25 hgap (fun p hp => ?_)⟩
    rw [Finset.mem_singleton] at hp; subst hp
    exact ⟨cycD.inj.ne (by decide), fun h => hy0_notD (by rw [← h]; exact ccwCycle_mem cycD 0), h0_out, hB (ccwCycle_mem cycD 0),
      segmentsCross_inIntTri_left hy0_tri h50 h0_y0 hby0 (by rw [orient2D_self_right])
        (by have h := ccw6_lt cycD (by decide : (0 : Fin 6) < 1) (by decide : (1 : Fin 6) < 5); dsimp [b, d0, d1]; unfold orient2D at h ⊢; linarith)⟩
  have build1 : GoodAnchorPair P S w O_star y0 y1 → 0 < orient2D v (S y0) (S y1) → Goal := by
    intro hgap hy0_y1
    refine ⟨y0, y1, {d1}, Or.inr (Or.inl ⟨rfl, rfl, rfl⟩), hgap, good_gap_of_all_cross_hex hPoly h25 hgap (fun p hp => ?_)⟩
    rw [Finset.mem_singleton] at hp; subst hp
    exact ⟨fun h => hy0_notD (by rw [← h]; exact ccwCycle_mem cycD 1), fun h => hy1_notD (by rw [← h]; exact ccwCycle_mem cycD 1),
      h1_out, hB (ccwCycle_mem cycD 1), segmentsCross_between_exits_shared (u1 := (0, 0)) hy0_tri hy0_1 h1_y1 hy0_y1 h_01_y1⟩
  have build234 : GoodAnchorPair P S w O_star y1 b →
      0 < orient2D v (S y1) (S d3) → 0 < orient2D v (S y1) (S d4) →
      0 < orient2D v (S d2) (S b) → 0 < orient2D v (S d3) (S b) →
      0 < orient2D v (S d4) (S b) → 0 < orient2D v (S y1) (S b) → Goal := by
    intro hgap hy1_3 hy1_4 hd25 h35 h45 hy1b
    refine ⟨y1, b, {d2, d3, d4}, Or.inr (Or.inr ⟨rfl, rfl, rfl⟩), hgap, good_gap_of_all_cross_hex hPoly h25 hgap (fun p hp => ?_)⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp; rcases hp with rfl | rfl | rfl
    · exact ⟨fun h => hy1_notD (by rw [← h]; exact ccwCycle_mem cycD 2), cycD.inj.ne (by decide), h2_out, hB (ccwCycle_mem cycD 2),
        segmentsCross_inIntTri_right hy1_tri hy1_2 hd25 hy1b (ccw6_lt cycD (by decide) (by decide)) (by dsimp [d2]; rw [orient2D_self_left])⟩
    · exact ⟨fun h => hy1_notD (by rw [← h]; exact ccwCycle_mem cycD 3), cycD.inj.ne (by decide), h3_out, hB (ccwCycle_mem cycD 3),
        segmentsCross_inIntTri_right hy1_tri hy1_3 h35 hy1b (ccw6_lt cycD (by decide) (by decide)) (le_of_lt (ccw6_lt cycD (by decide) (by decide)))⟩
    · exact ⟨fun h => hy1_notD (by rw [← h]; exact ccwCycle_mem cycD 4), cycD.inj.ne (by decide), h4_out, hB (ccwCycle_mem cycD 4),
        segmentsCross_inIntTri_right hy1_tri hy1_4 h45 hy1b (ccw6_lt cycD (by decide) (by decide)) (le_of_lt (ccw6_lt cycD (by decide) (by decide)))⟩
  by_cases h_all_nf : ∀ m : Fin 6, 0 < orient2D (S (cycD.toFun m)) (S (cycD.toFun (m + 1))) v
  · by_cases hsee : Sees P v q
    · have h50 : 0 < orient2D v (S b) (S d0) := by have h := h_all_nf 5; dsimp [b, d0] at *; unfold orient2D at h ⊢; linarith
      have h23 : 0 < orient2D v (S d2) (S d3) := by have h := h_all_nf 2; dsimp [d2, d3] at *; unfold orient2D at h ⊢; linarith
      have h34 : 0 < orient2D v (S d3) (S d4) := by have h := h_all_nf 3; dsimp [d3, d4] at *; unfold orient2D at h ⊢; linarith
      have h45 : 0 < orient2D v (S d4) (S b) := by have h := h_all_nf 4; dsimp [d4, b] at *; unfold orient2D at h ⊢; linarith
      rcases hexAdjB5_cases _ _ _ _ _ _ _ _
        (hex_all_nf_not_all_same cycD v q h_all_nf hvq_D) (hexNoAlt4_of_orientSign cycD v q hvq_D)
        (exitTri_orientSign_of_endpoints hy0_tri (hvq_D 0) (hvq_D 1))
        (exitTri_orientSign_of_endpoints hy1_tri (hvq_D 1) (hvq_D 2)) with
        ⟨h50_s, h0y_s⟩ | ⟨hy01_s, h1y1_s⟩ | ⟨hy12_s, h23_s, h34_s, h45_s⟩
      · have hby0 := chain3_orient_pos ⟨h50_s, h0y_s⟩ (hvq_D 5) (hvq_D 0) hvq_y0 h50 h0_y0
        exact build0 (goodAnchor_of_see hb_O hy0_O hb_ne_y0 hsee
          (onSameSide_of_orientSign_eq (h50_s.trans h0y_s) (hvq_D 5) hvq_y0) (ne_of_gt hby0)) h50 hby0
      · have hy0_y1 := chain3_orient_pos ⟨hy01_s, h1y1_s⟩ hvq_y0 (hvq_D 1) hvq_y1 hy0_1 h1_y1
        exact build1 (goodAnchor_of_see hy0_O hy1_O hy01 hsee
          (onSameSide_of_orientSign_eq (hy01_s.trans h1y1_s) hvq_y0 hvq_y1) (ne_of_gt hy0_y1)) hy0_y1
      · obtain ⟨hy1_3, hy1_4, h25, h35, hy1b⟩ := chain5_orient_pos ⟨hy12_s, h23_s, h34_s, h45_s⟩
          hvq_y1 (hvq_D 2) (hvq_D 3) (hvq_D 4) (hvq_D 5) hy1_2 h23 h34 h45
        exact build234 (goodAnchor_of_see hy1_O hb_O hy1_ne_b hsee
          (onSameSide_of_orientSign_eq (hy12_s.trans (h23_s.trans (h34_s.trans h45_s))) hvq_y1 (hvq_D 5)) (ne_of_gt hy1b))
          hy1_3 hy1_4 h25 h35 h45 hy1b
    · have hch := hexagon_seen5_chain_orient cycD v q 5 h_all_nf hvq_D
        (fun m hm => h_seen_ss (cycD.toFun 0) (cycD.toFun m) h0_out (hm_out m hm) hsee)
      have hy0_y1 := exitTri_after hy0_tri (exitTri_before hy1_tri (hch 0 1 (by decide)) (hch 0 2 (by decide))) h1_y1
      have hss01 := h_seen_ss d0 d1 h0_out h1_out hsee
      have hss12 := h_seen_ss d1 d2 h1_out h2_out hsee
      have hss0_y0 := (exitTri_sameSide_in_L hy0_tri hss01).1
      have hss_y0_y1 := (exitTri_sameSide_in_L hy0_tri hss01).2.trans (exitTri_sameSide_in_L hy1_tri hss12).1
      have hss_y12 := (exitTri_sameSide_in_L hy1_tri hss12).2
      exact build1 (goodAnchor_of_cone_ends hy0_O hy1_O hy01 hss_y0_y1 hy0_y1
        (fun hqy0 => ⟨d0, h0_out, by unfold OnSameSide at hss0_y0; nlinarith, h0_y0⟩)
        (fun hqy0 => ⟨d2, h2_out, by unfold OnSameSide at hss_y0_y1 hss_y12; nlinarith, hy1_2⟩)) hy0_y1
  · push Not at h_all_nf; obtain ⟨j0, hj0⟩ := h_all_nf
    obtain ⟨es, ee, L, hL1, hL5, heq, h_face_lt, _, _, _, _, h_ang⟩ :=
      facing_arc_complement_order cycD v hv_noncol ⟨j0, lt_of_le_of_ne hj0 (hv_noncol j0 (j0 + 1) (fin_add_one_ne_self j0))⟩
    have hc := hexFacing_elim hexFace_adj_b5_all es ee L hL1 hL5 heq
      (fun h => by linarith [h_face_lt 0 h, h01_nf])
      (fun h => by linarith [h_face_lt 1 h, h12_nf])
      (fun ⟨h4, h5⟩ => hb_nf ((isFrontVertexOf_iff_ccwCycle cycD 5 v).mpr ⟨h_face_lt 4 h4, h_face_lt 5 h5⟩))
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hc
    rcases hc with ⟨rfl, rfl⟩ | hsc
    · -- [0, 1, 2, 3, 4, 5]
      have ho : ∀ a c : Fin 6, (a - 0).val < (c - 0).val → (c - 0).val ≤ (5 - 0 : Fin 6).val →
          0 < orient2D v (S (cycD.toFun a)) (S (cycD.toFun c)) := fun a c h1 h2 => (h_ang a c h1 h2).2
      have h25 := ho 2 5 (by decide) (by decide)
      have h35 := ho 3 5 (by decide) (by decide)
      have h45 := ho 4 5 (by decide) (by decide)
      have hy0_y1 := exitTri_after hy0_tri (exitTri_before hy1_tri (ho 0 1 (by decide) (by decide)) (ho 0 2 (by decide) (by decide))) h1_y1
      have hy1_3 := exitTri_after hy1_tri (ho 1 3 (by decide) (by decide)) (ho 2 3 (by decide) (by decide))
      have hy1_4 := exitTri_after hy1_tri (ho 1 4 (by decide) (by decide)) (ho 2 4 (by decide) (by decide))
      have hy1_5 := exitTri_after hy1_tri (ho 1 5 (by decide) (by decide)) h25
      have hy0_5 := exitTri_after hy0_tri (ho 0 5 (by decide) (by decide)) (ho 1 5 (by decide) (by decide))
      by_cases hsee : Sees P v q
      · rcases three_missed_pigeonhole v q (S y0) (S y1) (S b) hvq_y0 hvq_y1 (hvq_D 5) hy0_y1 hy1_5 hy0_5 with hss1 | hss2
        · exact build1 (goodAnchor_of_see hy0_O hy1_O hy01 hsee hss1 (ne_of_gt hy0_y1)) hy0_y1
        · exact build234 (goodAnchor_of_see hy1_O hb_O hy1_ne_b hsee hss2 (ne_of_gt hy1_5)) hy1_3 hy1_4 h25 h35 h45 hy1_5
      · have hss01 := h_seen_ss d0 d1 h0_out h1_out hsee
        have hss12 := h_seen_ss d1 d2 h1_out h2_out hsee
        have hss0_y0 := (exitTri_sameSide_in_L hy0_tri hss01).1
        have hss_y0_y1 := (exitTri_sameSide_in_L hy0_tri hss01).2.trans (exitTri_sameSide_in_L hy1_tri hss12).1
        have hss_y12 := (exitTri_sameSide_in_L hy1_tri hss12).2
        exact build1 (goodAnchor_of_cone_ends hy0_O hy1_O hy01 hss_y0_y1 hy0_y1
          (fun hqy0 => ⟨d0, h0_out, by unfold OnSameSide at hss0_y0; nlinarith, h0_y0⟩)
          (fun hqy0 => ⟨d2, h2_out, by unfold OnSameSide at hss_y0_y1 hss_y12; nlinarith, hy1_2⟩)) hy0_y1
    · -- subchain [5, 0, 1, 2]
      have ho := subchain4_orient (fun a c h1 h2 => (h_ang a c h1 h2).2) hsc
      have h50 : 0 < orient2D v (S b) (S d0) := ho 0 1 (by decide)
      have h5_y0 := exitTri_before hy0_tri h50 (ho 0 2 (by decide))
      have hy0_y1 := exitTri_after hy0_tri (exitTri_before hy1_tri (ho 1 2 (by decide)) (ho 1 3 (by decide))) h1_y1
      have h5_y1 := exitTri_before hy1_tri (ho 0 2 (by decide)) (ho 0 3 (by decide))
      by_cases hsee : Sees P v q
      · rcases three_missed_pigeonhole v q (S b) (S y0) (S y1) (hvq_D 5) hvq_y0 hvq_y1 h5_y0 hy0_y1 h5_y1 with hss1 | hss2
        · exact build0 (goodAnchor_of_see hb_O hy0_O hb_ne_y0 hsee hss1 (ne_of_gt h5_y0)) h50 h5_y0
        · exact build1 (goodAnchor_of_see hy0_O hy1_O hy01 hsee hss2 (ne_of_gt hy0_y1)) hy0_y1
      · have hss01 := h_seen_ss d0 d1 h0_out h1_out hsee
        have hss12 := h_seen_ss d1 d2 h1_out h2_out hsee
        have hss0_y0 := (exitTri_sameSide_in_L hy0_tri hss01).1
        have hss_y0_y1 := (exitTri_sameSide_in_L hy0_tri hss01).2.trans (exitTri_sameSide_in_L hy1_tri hss12).1
        have hss_y12 := (exitTri_sameSide_in_L hy1_tri hss12).2
        exact build1 (goodAnchor_of_cone_ends hy0_O hy1_O hy01 hss_y0_y1 hy0_y1
          (fun hqy0 => ⟨d0, h0_out, by unfold OnSameSide at hss0_y0; nlinarith, h0_y0⟩)
          (fun hqy0 => ⟨d2, h2_out, by unfold OnSameSide at hss_y0_y1 hss_y12; nlinarith, hy1_2⟩)) hy0_y1

/-- **Lemma 5.12(i), `b = 3` (`hexagon-adjacent-exits`, `upper_8.tex`)**:
    For `D = (0, 1, 2, 3, 4, 5)` and `y0, y1 ∈ M` on `01` and `12`, with `O* = {3, y0, y1}`,
    at least one of `{4, 5, 0}` (`{3, y0}`), `{1}` (`{y0, y1}`), or `{2}` (`{y1, 3}`) is good. -/
theorem hexagon_adjacent_exits_b3 {n : ℕ} {P : Set (ℝ × ℝ)}
    {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ}
    (hPoly : ShatteredSimplePolygon P S w) (h25 : Sec2To5Interface P S w)
    {D : Finset (Fin n)} (hDB : D = hullVertices S \ certifiedVertices S w)
    (cycD : CCWCycle S D 3)
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
      ((oa = b ∧ ob = y0 ∧ Γ = {cycD.toFun 4, cycD.toFun 5, cycD.toFun 0}) ∨
       (oa = y0 ∧ ob = y1 ∧ Γ = {cycD.toFun 1}) ∨
       (oa = y1 ∧ ob = b ∧ Γ = {cycD.toFun 2})) ∧
      GoodAnchorPair P S w O_star oa ob ∧
      (∀ p ∈ Γ, IsBackVertexOf S (hullVertices S) p v ∧ SegmentsCross v (S p) (S oa) (S ob) ∧
        (∃ H_hp : OpenHalfPlane, IsHalfPlaneTest P (WitnessSet {oa, ob} ∅ w) (S p) H_hp)) ∧
      (∀ z : Fin n, z ≠ oa → z ≠ ob → z ∉ O_star →
        S z ∈ convexHull ℝ ((Γ ∪ {oa, ob}).image S : Set (ℝ × ℝ)) →
        SegmentsCross v (S z) (S oa) (S ob) ∧
        (∃ H_hp : OpenHalfPlane, IsHalfPlaneTest P (WitnessSet {oa, ob} ∅ w) (S z) H_hp) ∧
        (z ∈ hullVertices S → IsBackVertexOf S (hullVertices S) z v)) := by
  intro b O_star v
  let d0 := cycD.toFun 0; let d1 := cycD.toFun 1; let d2 := cycD.toFun 2
  let d4 := cycD.toFun 4; let d5 := cycD.toFun 5; let q := w Finset.univ
  have hy0_notD : y0 ∉ D := (Finset.mem_sdiff.mp hy0M).2
  have hy1_notD : y1 ∉ D := (Finset.mem_sdiff.mp hy1M).2
  obtain ⟨hm_out, hb_nf, hv_noncol, hvq_D, hvq_y0, hvq_y1, h_seen_ss⟩ :=
    hexagon_Ostar_core hPoly h25 hDB cycD hy0M hy1M hy01 3
  have h0_out := hm_out 0 (by decide); have h1_out := hm_out 1 (by decide)
  have h2_out := hm_out 2 (by decide); have h4_out := hm_out 4 (by decide)
  have h5_out := hm_out 5 (by decide)
  have hB : D ⊆ hullVertices S := hDB ▸ Finset.sdiff_subset
  have hb_O : b ∈ O_star := by simp [O_star]
  have hy0_O : y0 ∈ O_star := by simp [O_star]
  have hy1_O : y1 ∈ O_star := by simp [O_star]
  have hb_ne_y0 : b ≠ y0 := fun h => hy0_notD (h ▸ ccwCycle_mem cycD 3)
  have hy1_ne_b : y1 ≠ b := fun h => hy1_notD (h.symm ▸ ccwCycle_mem cycD 3)
  have h01_nf := hexagon_exit_nonfacing hPoly h25 hDB cycD hy0M 0 hy0_tri (fun l r hH he hHn => (h_not_lr l r hH he hHn).1)
  have h12_nf := hexagon_exit_nonfacing hPoly h25 hDB cycD hy1M 1 hy1_tri (fun l r hH he hHn => (h_not_lr l r hH he hHn).2)
  have ⟨h0_y0, hy0_1, _⟩ := exitTri_orient2D_left hy0_tri h01_nf
  have ⟨h1_y1, hy1_2, _⟩ := exitTri_orient2D_left hy1_tri h12_nf
  have h_01_y1 : 0 < orient2D (S d0) (S d1) (S y1) :=
    exitTri_comb_pos hy1_tri h01_nf (by rw [orient2D_self_right]) (le_of_lt (ccw6_lt cycD (by decide) (by decide)))
  let Goal := HexDisjGoal P S w O_star b y0 {d4, d5, d0} y0 y1 {d1} y1 b {d2}
  have build450 : GoodAnchorPair P S w O_star b y0 →
      0 < orient2D v (S b) (S d4) → 0 < orient2D v (S b) (S d5) → 0 < orient2D v (S b) (S d0) →
      0 < orient2D v (S d4) (S y0) → 0 < orient2D v (S d5) (S y0) → 0 < orient2D v (S b) (S y0) → Goal := by
    intro hgap h34 h35 h30 h4y0 h5y0 hby0
    refine ⟨b, y0, {d4, d5, d0}, Or.inl ⟨rfl, rfl, rfl⟩, hgap, good_gap_of_all_cross_hex hPoly h25 hgap (fun p hp => ?_)⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp; rcases hp with rfl | rfl | rfl
    · exact ⟨cycD.inj.ne (by decide), fun h => hy0_notD (by rw [← h]; exact ccwCycle_mem cycD 4), h4_out, hB (ccwCycle_mem cycD 4),
        segmentsCross_inIntTri_left hy0_tri h34 h4y0 hby0
          (le_of_lt (by have h := ccw6_lt cycD (by decide : (0 : Fin 6) < 3) (by decide : (3 : Fin 6) < 4); unfold orient2D at h ⊢; linarith))
          (by have h := ccw6_lt cycD (by decide : (1 : Fin 6) < 3) (by decide : (3 : Fin 6) < 4); unfold orient2D at h ⊢; linarith)⟩
    · exact ⟨cycD.inj.ne (by decide), fun h => hy0_notD (by rw [← h]; exact ccwCycle_mem cycD 5), h5_out, hB (ccwCycle_mem cycD 5),
        segmentsCross_inIntTri_left hy0_tri h35 h5y0 hby0
          (le_of_lt (by have h := ccw6_lt cycD (by decide : (0 : Fin 6) < 3) (by decide : (3 : Fin 6) < 5); unfold orient2D at h ⊢; linarith))
          (by have h := ccw6_lt cycD (by decide : (1 : Fin 6) < 3) (by decide : (3 : Fin 6) < 5); unfold orient2D at h ⊢; linarith)⟩
    · exact ⟨cycD.inj.ne (by decide), fun h => hy0_notD (by rw [← h]; exact ccwCycle_mem cycD 0), h0_out, hB (ccwCycle_mem cycD 0),
        segmentsCross_inIntTri_left hy0_tri h30 h0_y0 hby0 (by rw [orient2D_self_right])
          (by have h := ccw6_lt cycD (by decide : (0 : Fin 6) < 1) (by decide : (1 : Fin 6) < 3); dsimp [b, d0, d1]; unfold orient2D at h ⊢; linarith)⟩
  have build1 : GoodAnchorPair P S w O_star y0 y1 → 0 < orient2D v (S y0) (S y1) → Goal := by
    intro hgap hy0_y1
    refine ⟨y0, y1, {d1}, Or.inr (Or.inl ⟨rfl, rfl, rfl⟩), hgap, good_gap_of_all_cross_hex hPoly h25 hgap (fun p hp => ?_)⟩
    rw [Finset.mem_singleton] at hp; subst hp
    exact ⟨fun h => hy0_notD (by rw [← h]; exact ccwCycle_mem cycD 1), fun h => hy1_notD (by rw [← h]; exact ccwCycle_mem cycD 1),
      h1_out, hB (ccwCycle_mem cycD 1), segmentsCross_between_exits_shared (u1 := (0, 0)) hy0_tri hy0_1 h1_y1 hy0_y1 h_01_y1⟩
  have build2 : GoodAnchorPair P S w O_star y1 b → 0 < orient2D v (S d2) (S b) → 0 < orient2D v (S y1) (S b) → Goal := by
    intro hgap h23 hy1b
    refine ⟨y1, b, {d2}, Or.inr (Or.inr ⟨rfl, rfl, rfl⟩), hgap, good_gap_of_all_cross_hex hPoly h25 hgap (fun p hp => ?_)⟩
    rw [Finset.mem_singleton] at hp; subst hp
    exact ⟨fun h => hy1_notD (by rw [← h]; exact ccwCycle_mem cycD 2), cycD.inj.ne (by decide), h2_out, hB (ccwCycle_mem cycD 2),
      segmentsCross_inIntTri_right hy1_tri hy1_2 h23 hy1b (ccw6_lt cycD (by decide) (by decide)) (by dsimp [d2]; rw [orient2D_self_left])⟩
  by_cases h_all_nf : ∀ m : Fin 6, 0 < orient2D (S (cycD.toFun m)) (S (cycD.toFun (m + 1))) v
  · by_cases hsee : Sees P v q
    · have h34 : 0 < orient2D v (S b) (S d4) := by have h := h_all_nf 3; dsimp [b, d4] at *; unfold orient2D at h ⊢; linarith
      have h45 : 0 < orient2D v (S d4) (S d5) := by have h := h_all_nf 4; dsimp [d4, d5] at *; unfold orient2D at h ⊢; linarith
      have h50 : 0 < orient2D v (S d5) (S d0) := by have h := h_all_nf 5; dsimp [d5, d0] at *; unfold orient2D at h ⊢; linarith
      have h23 : 0 < orient2D v (S d2) (S b) := by have h := h_all_nf 2; dsimp [d2, b] at *; unfold orient2D at h ⊢; linarith
      rcases hexAdjB3_cases _ _ _ _ _ _ _ _
        (hex_all_nf_not_all_same cycD v q h_all_nf hvq_D) (hexNoAlt4_of_orientSign cycD v q hvq_D)
        (exitTri_orientSign_of_endpoints hy0_tri (hvq_D 0) (hvq_D 1))
        (exitTri_orientSign_of_endpoints hy1_tri (hvq_D 1) (hvq_D 2)) with
        ⟨h34_s, h45_s, h50_s, h0y_s⟩ | ⟨hy01_s, h1y1_s⟩ | ⟨hy12_s, h23_s⟩
      · obtain ⟨h35, h30, h4y0, h5y0, hby0⟩ := chain5_orient_pos ⟨h34_s, h45_s, h50_s, h0y_s⟩
          (hvq_D 3) (hvq_D 4) (hvq_D 5) (hvq_D 0) hvq_y0 h34 h45 h50 h0_y0
        exact build450 (goodAnchor_of_see hb_O hy0_O hb_ne_y0 hsee
          (onSameSide_of_orientSign_eq (h34_s.trans (h45_s.trans (h50_s.trans h0y_s))) (hvq_D 3) hvq_y0) (ne_of_gt hby0))
          h34 h35 h30 h4y0 h5y0 hby0
      · have hy0_y1 := chain3_orient_pos ⟨hy01_s, h1y1_s⟩ hvq_y0 (hvq_D 1) hvq_y1 hy0_1 h1_y1
        exact build1 (goodAnchor_of_see hy0_O hy1_O hy01 hsee
          (onSameSide_of_orientSign_eq (hy01_s.trans h1y1_s) hvq_y0 hvq_y1) (ne_of_gt hy0_y1)) hy0_y1
      · have hy1b := chain3_orient_pos ⟨hy12_s, h23_s⟩ hvq_y1 (hvq_D 2) (hvq_D 3) hy1_2 h23
        exact build2 (goodAnchor_of_see hy1_O hb_O hy1_ne_b hsee
          (onSameSide_of_orientSign_eq (hy12_s.trans h23_s) hvq_y1 (hvq_D 3)) (ne_of_gt hy1b)) h23 hy1b
    · have hch := hexagon_seen5_chain_orient cycD v q 3 h_all_nf hvq_D
        (fun m hm => h_seen_ss (cycD.toFun 4) (cycD.toFun m) h4_out (hm_out m hm) hsee)
      have hy0_y1 := exitTri_after hy0_tri (exitTri_before hy1_tri (hch 2 3 (by decide)) (hch 2 4 (by decide))) h1_y1
      have hss01 := h_seen_ss d0 d1 h0_out h1_out hsee
      have hss12 := h_seen_ss d1 d2 h1_out h2_out hsee
      have hss0_y0 := (exitTri_sameSide_in_L hy0_tri hss01).1
      have hss_y0_y1 := (exitTri_sameSide_in_L hy0_tri hss01).2.trans (exitTri_sameSide_in_L hy1_tri hss12).1
      have hss_y12 := (exitTri_sameSide_in_L hy1_tri hss12).2
      exact build1 (goodAnchor_of_cone_ends hy0_O hy1_O hy01 hss_y0_y1 hy0_y1
        (fun hqy0 => ⟨d0, h0_out, by unfold OnSameSide at hss0_y0; nlinarith, h0_y0⟩)
        (fun hqy0 => ⟨d2, h2_out, by unfold OnSameSide at hss_y0_y1 hss_y12; nlinarith, hy1_2⟩)) hy0_y1
  · push Not at h_all_nf; obtain ⟨j0, hj0⟩ := h_all_nf
    obtain ⟨es, ee, L, hL1, hL5, heq, h_face_lt, _, _, _, _, h_ang⟩ :=
      facing_arc_complement_order cycD v hv_noncol ⟨j0, lt_of_le_of_ne hj0 (hv_noncol j0 (j0 + 1) (fin_add_one_ne_self j0))⟩
    have hc := hexFacing_elim hexFace_adj_b3_all es ee L hL1 hL5 heq
      (fun h => by linarith [h_face_lt 0 h, h01_nf])
      (fun h => by linarith [h_face_lt 1 h, h12_nf])
      (fun ⟨h2, h3⟩ => hb_nf ((isFrontVertexOf_iff_ccwCycle cycD 3 v).mpr ⟨h_face_lt 2 h2, h_face_lt 3 h3⟩))
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hc
    rcases hc with ⟨rfl, rfl⟩ | hsc
    · -- [3, 4, 5, 0, 1, 2]
      have ho : ∀ a c : Fin 6, (a - 3).val < (c - 3).val → (c - 3).val ≤ (2 - 3 : Fin 6).val →
          0 < orient2D v (S (cycD.toFun a)) (S (cycD.toFun c)) := fun a c h1 h2 => (h_ang a c h1 h2).2
      have h34 := ho 3 4 (by decide) (by decide)
      have h35 := ho 3 5 (by decide) (by decide)
      have h30 := ho 3 0 (by decide) (by decide)
      have h3_y0 := exitTri_before hy0_tri h30 (ho 3 1 (by decide) (by decide))
      have h4y0 := exitTri_before hy0_tri (ho 4 0 (by decide) (by decide)) (ho 4 1 (by decide) (by decide))
      have h5y0 := exitTri_before hy0_tri (ho 5 0 (by decide) (by decide)) (ho 5 1 (by decide) (by decide))
      have hy0_y1 := exitTri_after hy0_tri (exitTri_before hy1_tri (ho 0 1 (by decide) (by decide)) (ho 0 2 (by decide) (by decide))) h1_y1
      have h3_y1 := exitTri_before hy1_tri (ho 3 1 (by decide) (by decide)) (ho 3 2 (by decide) (by decide))
      by_cases hsee : Sees P v q
      · rcases three_missed_pigeonhole v q (S b) (S y0) (S y1) (hvq_D 3) hvq_y0 hvq_y1 h3_y0 hy0_y1 h3_y1 with hss1 | hss2
        · exact build450 (goodAnchor_of_see hb_O hy0_O hb_ne_y0 hsee hss1 (ne_of_gt h3_y0)) h34 h35 h30 h4y0 h5y0 h3_y0
        · exact build1 (goodAnchor_of_see hy0_O hy1_O hy01 hsee hss2 (ne_of_gt hy0_y1)) hy0_y1
      · have hss01 := h_seen_ss d0 d1 h0_out h1_out hsee
        have hss12 := h_seen_ss d1 d2 h1_out h2_out hsee
        have hss0_y0 := (exitTri_sameSide_in_L hy0_tri hss01).1
        have hss_y0_y1 := (exitTri_sameSide_in_L hy0_tri hss01).2.trans (exitTri_sameSide_in_L hy1_tri hss12).1
        have hss_y12 := (exitTri_sameSide_in_L hy1_tri hss12).2
        exact build1 (goodAnchor_of_cone_ends hy0_O hy1_O hy01 hss_y0_y1 hy0_y1
          (fun hqy0 => ⟨d0, h0_out, by unfold OnSameSide at hss0_y0; nlinarith, h0_y0⟩)
          (fun hqy0 => ⟨d2, h2_out, by unfold OnSameSide at hss_y0_y1 hss_y12; nlinarith, hy1_2⟩)) hy0_y1
    · -- subchain [0, 1, 2, 3]
      have ho := subchain4_orient (fun a c h1 h2 => (h_ang a c h1 h2).2) hsc
      have h23 : 0 < orient2D v (S d2) (S b) := ho 2 3 (by decide)
      have hy0_y1 := exitTri_after hy0_tri (exitTri_before hy1_tri (ho 0 1 (by decide)) (ho 0 2 (by decide))) h1_y1
      have hy1_3 := exitTri_after hy1_tri (ho 1 3 (by decide)) h23
      have hy0_3 := exitTri_after hy0_tri (ho 0 3 (by decide)) (ho 1 3 (by decide))
      by_cases hsee : Sees P v q
      · rcases three_missed_pigeonhole v q (S y0) (S y1) (S b) hvq_y0 hvq_y1 (hvq_D 3) hy0_y1 hy1_3 hy0_3 with hss1 | hss2
        · exact build1 (goodAnchor_of_see hy0_O hy1_O hy01 hsee hss1 (ne_of_gt hy0_y1)) hy0_y1
        · exact build2 (goodAnchor_of_see hy1_O hb_O hy1_ne_b hsee hss2 (ne_of_gt hy1_3)) h23 hy1_3
      · have hss01 := h_seen_ss d0 d1 h0_out h1_out hsee
        have hss12 := h_seen_ss d1 d2 h1_out h2_out hsee
        have hss0_y0 := (exitTri_sameSide_in_L hy0_tri hss01).1
        have hss_y0_y1 := (exitTri_sameSide_in_L hy0_tri hss01).2.trans (exitTri_sameSide_in_L hy1_tri hss12).1
        have hss_y12 := (exitTri_sameSide_in_L hy1_tri hss12).2
        exact build1 (goodAnchor_of_cone_ends hy0_O hy1_O hy01 hss_y0_y1 hy0_y1
          (fun hqy0 => ⟨d0, h0_out, by unfold OnSameSide at hss0_y0; nlinarith, h0_y0⟩)
          (fun hqy0 => ⟨d2, h2_out, by unfold OnSameSide at hss_y0_y1 hss_y12; nlinarith, hy1_2⟩)) hy0_y1

/-- **Lemma 5.12(ii), `b = 4` (`hexagon-adjacent-exits`, `upper_8.tex`)**:
    For `D = (0, 1, 2, 3, 4, 5)` and `y0, y1 ∈ M` on `01` and `12`, with `O* = {4, y0, y1}`,
    at least one of `{5, 0}` (`{4, y0}`), `{1}` (`{y0, y1}`), or `{2, 3}` (`{y1, 4}`) is good. -/
theorem hexagon_adjacent_exits_b4 {n : ℕ} {P : Set (ℝ × ℝ)}
    {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ}
    (hPoly : ShatteredSimplePolygon P S w) (h25 : Sec2To5Interface P S w)
    {D : Finset (Fin n)} (hDB : D = hullVertices S \ certifiedVertices S w)
    (cycD : CCWCycle S D 3)
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
      ((oa = b ∧ ob = y0 ∧ Γ = {cycD.toFun 5, cycD.toFun 0}) ∨
       (oa = y0 ∧ ob = y1 ∧ Γ = {cycD.toFun 1}) ∨
       (oa = y1 ∧ ob = b ∧ Γ = {cycD.toFun 2, cycD.toFun 3})) ∧
      GoodAnchorPair P S w O_star oa ob ∧
      (∀ p ∈ Γ, IsBackVertexOf S (hullVertices S) p v ∧ SegmentsCross v (S p) (S oa) (S ob) ∧
        (∃ H_hp : OpenHalfPlane, IsHalfPlaneTest P (WitnessSet {oa, ob} ∅ w) (S p) H_hp)) ∧
      (∀ z : Fin n, z ≠ oa → z ≠ ob → z ∉ O_star →
        S z ∈ convexHull ℝ ((Γ ∪ {oa, ob}).image S : Set (ℝ × ℝ)) →
        SegmentsCross v (S z) (S oa) (S ob) ∧
        (∃ H_hp : OpenHalfPlane, IsHalfPlaneTest P (WitnessSet {oa, ob} ∅ w) (S z) H_hp) ∧
        (z ∈ hullVertices S → IsBackVertexOf S (hullVertices S) z v)) := by
  intro b O_star v
  let d0 := cycD.toFun 0; let d1 := cycD.toFun 1; let d2 := cycD.toFun 2
  let d3 := cycD.toFun 3; let d5 := cycD.toFun 5; let q := w Finset.univ
  have hy0_notD : y0 ∉ D := (Finset.mem_sdiff.mp hy0M).2
  have hy1_notD : y1 ∉ D := (Finset.mem_sdiff.mp hy1M).2
  obtain ⟨hm_out, hb_nf, hv_noncol, hvq_D, hvq_y0, hvq_y1, h_seen_ss⟩ :=
    hexagon_Ostar_core hPoly h25 hDB cycD hy0M hy1M hy01 4
  have h0_out := hm_out 0 (by decide); have h1_out := hm_out 1 (by decide)
  have h2_out := hm_out 2 (by decide); have h3_out := hm_out 3 (by decide)
  have h5_out := hm_out 5 (by decide)
  have hB : D ⊆ hullVertices S := hDB ▸ Finset.sdiff_subset
  have hb_O : b ∈ O_star := by simp [O_star]
  have hy0_O : y0 ∈ O_star := by simp [O_star]
  have hy1_O : y1 ∈ O_star := by simp [O_star]
  have hb_ne_y0 : b ≠ y0 := fun h => hy0_notD (h ▸ ccwCycle_mem cycD 4)
  have hy1_ne_b : y1 ≠ b := fun h => hy1_notD (h.symm ▸ ccwCycle_mem cycD 4)
  have h01_nf := hexagon_exit_nonfacing hPoly h25 hDB cycD hy0M 0 hy0_tri (fun l r hH he hHn => (h_not_lr l r hH he hHn).1)
  have h12_nf := hexagon_exit_nonfacing hPoly h25 hDB cycD hy1M 1 hy1_tri (fun l r hH he hHn => (h_not_lr l r hH he hHn).2)
  have ⟨h0_y0, hy0_1, _⟩ := exitTri_orient2D_left hy0_tri h01_nf
  have ⟨h1_y1, hy1_2, _⟩ := exitTri_orient2D_left hy1_tri h12_nf
  have h_01_y1 : 0 < orient2D (S d0) (S d1) (S y1) :=
    exitTri_comb_pos hy1_tri h01_nf (by rw [orient2D_self_right]) (le_of_lt (ccw6_lt cycD (by decide) (by decide)))
  let Goal := HexDisjGoal P S w O_star b y0 {d5, d0} y0 y1 {d1} y1 b {d2, d3}
  have build50 : GoodAnchorPair P S w O_star b y0 →
      0 < orient2D v (S b) (S d5) → 0 < orient2D v (S d5) (S y0) →
      0 < orient2D v (S b) (S d0) → 0 < orient2D v (S b) (S y0) → Goal := by
    intro hgap h45 h5y0 h40 hby0
    refine ⟨b, y0, {d5, d0}, Or.inl ⟨rfl, rfl, rfl⟩, hgap, good_gap_of_all_cross_hex hPoly h25 hgap (fun p hp => ?_)⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp; rcases hp with rfl | rfl
    · exact ⟨cycD.inj.ne (by decide), fun h => hy0_notD (by rw [← h]; exact ccwCycle_mem cycD 5), h5_out, hB (ccwCycle_mem cycD 5),
        segmentsCross_inIntTri_left hy0_tri h45 h5y0 hby0
          (le_of_lt (by have h := ccw6_lt cycD (by decide : (0 : Fin 6) < 4) (by decide : (4 : Fin 6) < 5); unfold orient2D at h ⊢; linarith))
          (by have h := ccw6_lt cycD (by decide : (1 : Fin 6) < 4) (by decide : (4 : Fin 6) < 5); unfold orient2D at h ⊢; linarith)⟩
    · exact ⟨cycD.inj.ne (by decide), fun h => hy0_notD (by rw [← h]; exact ccwCycle_mem cycD 0), h0_out, hB (ccwCycle_mem cycD 0),
        segmentsCross_inIntTri_left hy0_tri h40 h0_y0 hby0 (by rw [orient2D_self_right])
          (by have h := ccw6_lt cycD (by decide : (0 : Fin 6) < 1) (by decide : (1 : Fin 6) < 4); dsimp [b, d0, d1]; unfold orient2D at h ⊢; linarith)⟩
  have build1 : GoodAnchorPair P S w O_star y0 y1 → 0 < orient2D v (S y0) (S y1) → Goal := by
    intro hgap hy0_y1
    refine ⟨y0, y1, {d1}, Or.inr (Or.inl ⟨rfl, rfl, rfl⟩), hgap, good_gap_of_all_cross_hex hPoly h25 hgap (fun p hp => ?_)⟩
    rw [Finset.mem_singleton] at hp; subst hp
    exact ⟨fun h => hy0_notD (by rw [← h]; exact ccwCycle_mem cycD 1), fun h => hy1_notD (by rw [← h]; exact ccwCycle_mem cycD 1),
      h1_out, hB (ccwCycle_mem cycD 1), segmentsCross_between_exits_shared (u1 := (0, 0)) hy0_tri hy0_1 h1_y1 hy0_y1 h_01_y1⟩
  have build23 : GoodAnchorPair P S w O_star y1 b →
      0 < orient2D v (S y1) (S d3) → 0 < orient2D v (S d3) (S b) →
      0 < orient2D v (S d2) (S b) → 0 < orient2D v (S y1) (S b) → Goal := by
    intro hgap hy1_3 h34 h24 hy1b
    refine ⟨y1, b, {d2, d3}, Or.inr (Or.inr ⟨rfl, rfl, rfl⟩), hgap, good_gap_of_all_cross_hex hPoly h25 hgap (fun p hp => ?_)⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp; rcases hp with rfl | rfl
    · exact ⟨fun h => hy1_notD (by rw [← h]; exact ccwCycle_mem cycD 2), cycD.inj.ne (by decide), h2_out, hB (ccwCycle_mem cycD 2),
        segmentsCross_inIntTri_right hy1_tri hy1_2 h24 hy1b (ccw6_lt cycD (by decide) (by decide)) (by dsimp [d2]; rw [orient2D_self_left])⟩
    · exact ⟨fun h => hy1_notD (by rw [← h]; exact ccwCycle_mem cycD 3), cycD.inj.ne (by decide), h3_out, hB (ccwCycle_mem cycD 3),
        segmentsCross_inIntTri_right hy1_tri hy1_3 h34 hy1b (ccw6_lt cycD (by decide) (by decide)) (le_of_lt (ccw6_lt cycD (by decide) (by decide)))⟩
  by_cases h_all_nf : ∀ m : Fin 6, 0 < orient2D (S (cycD.toFun m)) (S (cycD.toFun (m + 1))) v
  · by_cases hsee : Sees P v q
    · have h45 : 0 < orient2D v (S b) (S d5) := by have h := h_all_nf 4; dsimp [b, d5] at *; unfold orient2D at h ⊢; linarith
      have h50 : 0 < orient2D v (S d5) (S d0) := by have h := h_all_nf 5; dsimp [d5, d0] at *; unfold orient2D at h ⊢; linarith
      have h23 : 0 < orient2D v (S d2) (S d3) := by have h := h_all_nf 2; dsimp [d2, d3] at *; unfold orient2D at h ⊢; linarith
      have h34 : 0 < orient2D v (S d3) (S b) := by have h := h_all_nf 3; dsimp [d3, b] at *; unfold orient2D at h ⊢; linarith
      rcases hexAdjB4_cases _ _ _ _ _ _ _ _
        (hex_all_nf_not_all_same cycD v q h_all_nf hvq_D) (hexNoAlt4_of_orientSign cycD v q hvq_D)
        (exitTri_orientSign_of_endpoints hy0_tri (hvq_D 0) (hvq_D 1))
        (exitTri_orientSign_of_endpoints hy1_tri (hvq_D 1) (hvq_D 2)) with
        ⟨h45_s, h50_s, h0y_s⟩ | ⟨hy01_s, h1y1_s⟩ | ⟨hy12_s, h23_s, h34_s⟩
      · obtain ⟨h40, h5y0, hby0⟩ := chain4_orient_pos ⟨h45_s, h50_s, h0y_s⟩ (hvq_D 4) (hvq_D 5) (hvq_D 0) hvq_y0 h45 h50 h0_y0
        exact build50 (goodAnchor_of_see hb_O hy0_O hb_ne_y0 hsee
          (onSameSide_of_orientSign_eq (h45_s.trans (h50_s.trans h0y_s)) (hvq_D 4) hvq_y0) (ne_of_gt hby0)) h45 h5y0 h40 hby0
      · have hy0_y1 := chain3_orient_pos ⟨hy01_s, h1y1_s⟩ hvq_y0 (hvq_D 1) hvq_y1 hy0_1 h1_y1
        exact build1 (goodAnchor_of_see hy0_O hy1_O hy01 hsee
          (onSameSide_of_orientSign_eq (hy01_s.trans h1y1_s) hvq_y0 hvq_y1) (ne_of_gt hy0_y1)) hy0_y1
      · obtain ⟨hy1_3, h24, hy1b⟩ := chain4_orient_pos ⟨hy12_s, h23_s, h34_s⟩ hvq_y1 (hvq_D 2) (hvq_D 3) (hvq_D 4) hy1_2 h23 h34
        exact build23 (goodAnchor_of_see hy1_O hb_O hy1_ne_b hsee
          (onSameSide_of_orientSign_eq (hy12_s.trans (h23_s.trans h34_s)) hvq_y1 (hvq_D 4)) (ne_of_gt hy1b)) hy1_3 h34 h24 hy1b
    · have hch := hexagon_seen5_chain_orient cycD v q 4 h_all_nf hvq_D
        (fun m hm => h_seen_ss (cycD.toFun 5) (cycD.toFun m) h5_out (hm_out m hm) hsee)
      have hy0_y1 := exitTri_after hy0_tri (exitTri_before hy1_tri (hch 1 2 (by decide)) (hch 1 3 (by decide))) h1_y1
      have hss01 := h_seen_ss d0 d1 h0_out h1_out hsee
      have hss12 := h_seen_ss d1 d2 h1_out h2_out hsee
      have hss0_y0 := (exitTri_sameSide_in_L hy0_tri hss01).1
      have hss_y0_y1 := (exitTri_sameSide_in_L hy0_tri hss01).2.trans (exitTri_sameSide_in_L hy1_tri hss12).1
      have hss_y12 := (exitTri_sameSide_in_L hy1_tri hss12).2
      exact build1 (goodAnchor_of_cone_ends hy0_O hy1_O hy01 hss_y0_y1 hy0_y1
        (fun hqy0 => ⟨d0, h0_out, by unfold OnSameSide at hss0_y0; nlinarith, h0_y0⟩)
        (fun hqy0 => ⟨d2, h2_out, by unfold OnSameSide at hss_y0_y1 hss_y12; nlinarith, hy1_2⟩)) hy0_y1
  · push Not at h_all_nf; obtain ⟨j0, hj0⟩ := h_all_nf
    obtain ⟨es, ee, L, hL1, hL5, heq, h_face_lt, _, _, _, _, h_ang⟩ :=
      facing_arc_complement_order cycD v hv_noncol ⟨j0, lt_of_le_of_ne hj0 (hv_noncol j0 (j0 + 1) (fin_add_one_ne_self j0))⟩
    have hc := hexFacing_elim hexFace_adj_b4_all es ee L hL1 hL5 heq
      (fun h => by linarith [h_face_lt 0 h, h01_nf])
      (fun h => by linarith [h_face_lt 1 h, h12_nf])
      (fun ⟨h3, h4⟩ => hb_nf ((isFrontVertexOf_iff_ccwCycle cycD 4 v).mpr ⟨h_face_lt 3 h3, h_face_lt 4 h4⟩))
    simp only [Bool.or_eq_true] at hc
    rcases hc with hsc1 | hsc2
    · -- subchain [4, 5, 0, 1, 2]
      have ho := subchain5_orient (fun a c h1 h2 => (h_ang a c h1 h2).2) hsc1
      have h45 : 0 < orient2D v (S b) (S d5) := ho 0 1 (by decide)
      have h40 : 0 < orient2D v (S b) (S d0) := ho 0 2 (by decide)
      have h4_y0 := exitTri_before hy0_tri h40 (ho 0 3 (by decide))
      have h5y0 := exitTri_before hy0_tri (ho 1 2 (by decide)) (ho 1 3 (by decide))
      have hy0_y1 := exitTri_after hy0_tri (exitTri_before hy1_tri (ho 2 3 (by decide)) (ho 2 4 (by decide))) h1_y1
      have h4_y1 := exitTri_before hy1_tri (ho 0 3 (by decide)) (ho 0 4 (by decide))
      by_cases hsee : Sees P v q
      · rcases three_missed_pigeonhole v q (S b) (S y0) (S y1) (hvq_D 4) hvq_y0 hvq_y1 h4_y0 hy0_y1 h4_y1 with hss1 | hss2
        · exact build50 (goodAnchor_of_see hb_O hy0_O hb_ne_y0 hsee hss1 (ne_of_gt h4_y0)) h45 h5y0 h40 h4_y0
        · exact build1 (goodAnchor_of_see hy0_O hy1_O hy01 hsee hss2 (ne_of_gt hy0_y1)) hy0_y1
      · have hss01 := h_seen_ss d0 d1 h0_out h1_out hsee
        have hss12 := h_seen_ss d1 d2 h1_out h2_out hsee
        have hss0_y0 := (exitTri_sameSide_in_L hy0_tri hss01).1
        have hss_y0_y1 := (exitTri_sameSide_in_L hy0_tri hss01).2.trans (exitTri_sameSide_in_L hy1_tri hss12).1
        have hss_y12 := (exitTri_sameSide_in_L hy1_tri hss12).2
        exact build1 (goodAnchor_of_cone_ends hy0_O hy1_O hy01 hss_y0_y1 hy0_y1
          (fun hqy0 => ⟨d0, h0_out, by unfold OnSameSide at hss0_y0; nlinarith, h0_y0⟩)
          (fun hqy0 => ⟨d2, h2_out, by unfold OnSameSide at hss_y0_y1 hss_y12; nlinarith, hy1_2⟩)) hy0_y1
    · -- subchain [0, 1, 2, 3, 4]
      have ho := subchain5_orient (fun a c h1 h2 => (h_ang a c h1 h2).2) hsc2
      have h24 : 0 < orient2D v (S d2) (S b) := ho 2 4 (by decide)
      have h34 : 0 < orient2D v (S d3) (S b) := ho 3 4 (by decide)
      have hy0_y1 := exitTri_after hy0_tri (exitTri_before hy1_tri (ho 0 1 (by decide)) (ho 0 2 (by decide))) h1_y1
      have hy1_3 := exitTri_after hy1_tri (ho 1 3 (by decide)) (ho 2 3 (by decide))
      have hy1_4 := exitTri_after hy1_tri (ho 1 4 (by decide)) h24
      have hy0_4 := exitTri_after hy0_tri (ho 0 4 (by decide)) (ho 1 4 (by decide))
      by_cases hsee : Sees P v q
      · rcases three_missed_pigeonhole v q (S y0) (S y1) (S b) hvq_y0 hvq_y1 (hvq_D 4) hy0_y1 hy1_4 hy0_4 with hss1 | hss2
        · exact build1 (goodAnchor_of_see hy0_O hy1_O hy01 hsee hss1 (ne_of_gt hy0_y1)) hy0_y1
        · exact build23 (goodAnchor_of_see hy1_O hb_O hy1_ne_b hsee hss2 (ne_of_gt hy1_4)) hy1_3 h34 h24 hy1_4
      · have hss01 := h_seen_ss d0 d1 h0_out h1_out hsee
        have hss12 := h_seen_ss d1 d2 h1_out h2_out hsee
        have hss0_y0 := (exitTri_sameSide_in_L hy0_tri hss01).1
        have hss_y0_y1 := (exitTri_sameSide_in_L hy0_tri hss01).2.trans (exitTri_sameSide_in_L hy1_tri hss12).1
        have hss_y12 := (exitTri_sameSide_in_L hy1_tri hss12).2
        exact build1 (goodAnchor_of_cone_ends hy0_O hy1_O hy01 hss_y0_y1 hy0_y1
          (fun hqy0 => ⟨d0, h0_out, by unfold OnSameSide at hss0_y0; nlinarith, h0_y0⟩)
          (fun hqy0 => ⟨d2, h2_out, by unfold OnSameSide at hss_y0_y1 hss_y12; nlinarith, hy1_2⟩)) hy0_y1

end HexagonTwoAnchorHelpers


/-! ## 3. Clause `(C7)` (`SourceGapSoundness`): Pure `orientSign` Bridge to `(C9)` -/

/-- Pure chirotope good-gap certificate matching `add_gap_disjunction` (`gen_chiro_v2.cpp` lines 250–290)
    and Theorem 8.1 `(C7)` of `upper_8.tex`:
    There exist an ordered anchor pair `(ia, ic)` (`{ia, ic} = {oa, ob} ⊆ O_miss`) and a single uniform
    orientation sign `σ : Bool` such that for `Tv := Finset.univ \ O_miss`, `v := w Tv`, and `q := w Finset.univ`:
    1. `orientSign v q (S ia) = σ`, `orientSign v q (S ic) = σ`, `orientSign v (S ia) (S ic) = σ`;
    2. Either `Sees P v q` or some `ie ∈ Tv` satisfies `orientSign v q (S ie) = σ` and `orientSign v (S ie) (S ia) = σ`;
    3. Every gap vertex `ip ∈ Γ` is seen by `v`, is a back vertex of `B = hullVertices S` from `v` in `orientSign` form,
       satisfies `orientSign v q (S ip) = σ`, `orientSign v (S ia) (S ip) = σ`, `orientSign v (S ip) (S ic) = σ`,
       `segsCrossBool v (S ip) (S ia) (S ic) = true` (`oppSideBool (S ia) (S ic) v (S ip) = true`),
       satisfies `HalfPlaneChirotopeConfig P S w Tv Finset.univ ia ip ic`, and obeys all four pure `orientSign` /
       `sameSideBool` witness-ordering clauses of `half_plane_chirotope_clauses_C9` with that same uniform `σ`! -/
def IsGoodChirotopeGap {n : ℕ} (P : Set (ℝ × ℝ))
    (S : Fin n → ℝ × ℝ) (w : Finset (Fin n) → ℝ × ℝ)
    (O_miss : Finset (Fin n)) (oa ob : Fin n) (Γ : Finset (Fin n)) : Prop :=
  let Tv := Finset.univ \ O_miss
  let v := w Tv
  let q := w Finset.univ
  ∃ (ia ic : Fin n) (σ : Bool),
    ((ia = oa ∧ ic = ob) ∨ (ia = ob ∧ ic = oa)) ∧
    ia ∈ O_miss ∧ ic ∈ O_miss ∧ ia ≠ ic ∧
    orientSign v q (S ia) = σ ∧
    orientSign v q (S ic) = σ ∧
    orientSign v (S ia) (S ic) = σ ∧
    (Sees P v q ∨ ∃ ie ∈ Tv, orientSign v q (S ie) = σ ∧ orientSign v (S ie) (S ia) = σ) ∧
    ∀ ip ∈ Γ,
      ip ∈ Tv ∧ ip ∈ hullVertices S ∧
      IsBackVertexOf S (hullVertices S) ip v ∧
      (∀ pm : Fin n, IsCCWEdge S (hullVertices S) pm ip → orientSign (S pm) (S ip) v = true) ∧
      (∀ pp : Fin n, IsCCWEdge S (hullVertices S) ip pp → orientSign (S ip) (S pp) v = true) ∧
      orientSign v q (S ip) = σ ∧
      orientSign v (S ia) (S ip) = σ ∧
      orientSign v (S ip) (S ic) = σ ∧
      segsCrossBool v (S ip) (S ia) (S ic) = true ∧
      oppSideBool (S ia) (S ic) v (S ip) = true ∧
      HalfPlaneChirotopeConfig P S w Tv Finset.univ ia ip ic ∧
      (∀ {Tx : Finset (Fin n)}, {ia, ic} ⊆ Tx →
        orientSign v (S ia) (w Tx) = !σ ∧ sameSideBool v (S ia) (w Tx) q = true) ∧
      (∀ {Tx : Finset (Fin n)}, {ia, ic} ⊆ Tx →
        orientSign v (S ip) (w Tx) = !σ ∧ sameSideBool v (S ip) (w Tx) q = true) ∧
      (∀ {Tx : Finset (Fin n)}, {ia, ic} ⊆ Tx → ip ∈ Tx →
        orientSign (S ip) (w Tx) (S ia) = σ ∧
        (Tx ≠ Finset.univ → sameSideBool (S ip) (S ia) (w Tx) q = true)) ∧
      (∀ {Tx Ty : Finset (Fin n)}, {ia, ic} ⊆ Tx → ip ∈ Tx → {ia, ic} ⊆ Ty → ip ∉ Ty →
        orientSign (S ip) (w Tx) (w Ty) = σ)

private lemma orientSign_eq_of_mul_pos_left {x y : ℝ} (hx : x ≠ 0) (hmul : 0 < x * y) :
    decide (0 < y) = decide (0 < x) := by
  by_cases hxp : 0 < x
  · have hyp : 0 < y := by nlinarith
    simp [hxp, hyp]
  · have hxn : x < 0 := lt_of_le_of_ne (not_lt.mp hxp) hx
    have hyn : y < 0 := by nlinarith
    simp [hxp, not_lt_of_gt hyn]

/-- Universal point-level bridge: for any `iz ∉ O_miss` whose segment `v(S iz)` crosses `(S ia)(S ic)`
    under an ordered good-anchor pair `(ia, ic)` with `σ := orientSign v q (S ia)`, `iz` satisfies
    `orientSign v q (S iz) = σ` and `HalfPlaneChirotopeConfig P S w Tv Finset.univ ia iz ic`
    (hence all four pure `orientSign` clauses of `(C9)` with uniform sign `σ`). -/
theorem halfPlaneChirotopeConfig_of_ordered_anchor_cross {n : ℕ} {P : Set (ℝ × ℝ)}
    {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ}
    (hP : ShatteredSimplePolygon P S w)
    {O_miss : Finset (Fin n)} {ia ic iz : Fin n}
    (hiaO : ia ∈ O_miss) (hicO : ic ∈ O_miss) (hiac : ia ≠ ic)
    (hang : AngleLt (w (Finset.univ \ O_miss)) (w Finset.univ) (S ia) (S ic))
    (hcond4 : Sees P (w (Finset.univ \ O_miss)) (w Finset.univ) ∨
      ∃ ie : Fin n, ie ∉ O_miss ∧
        AngleLt (w (Finset.univ \ O_miss)) (w Finset.univ) (S ie) (S ia))
    (hiz_notO : iz ∉ O_miss)
    (hcross : SegmentsCross (w (Finset.univ \ O_miss)) (S iz) (S ia) (S ic)) :
    let Tv := Finset.univ \ O_miss
    let v := w Tv
    let q := w Finset.univ
    let σ := orientSign v q (S ia)
    orientSign v q (S ic) = σ ∧
    orientSign v (S ia) (S ic) = σ ∧
    orientSign v q (S iz) = σ ∧
    orientSign v (S ia) (S iz) = σ ∧
    orientSign v (S iz) (S ic) = σ ∧
    segsCrossBool v (S iz) (S ia) (S ic) = true ∧
    oppSideBool (S ia) (S ic) v (S iz) = true ∧
    HalfPlaneChirotopeConfig P S w Tv Finset.univ ia iz ic := by
  intro Tv v q σ
  have hTv_ne_Tq : Tv ≠ Finset.univ := fun heq => by
    have hmem : ia ∈ Tv := heq.symm ▸ Finset.mem_univ ia
    exact (Finset.mem_sdiff.mp hmem).2 hiaO
  have hiz_Tv : iz ∈ Tv := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hiz_notO⟩
  have hia_not_Tv : ia ∉ Tv := fun h => (Finset.mem_sdiff.mp h).2 hiaO
  have hic_not_Tv : ic ∉ Tv := fun h => (Finset.mem_sdiff.mp h).2 hicO
  have hiaz : ia ≠ iz := fun h => hiz_notO (h ▸ hiaO)
  have hicz : ic ≠ iz := fun h => hiz_notO (h ▸ hicO)
  have hvqa_ne : orient2D v q (S ia) ≠ 0 := orient_w_w_S_ne hP hTv_ne_Tq ia
  have hvqz_ne : orient2D v q (S iz) ≠ 0 := orient_w_w_S_ne hP hTv_ne_Tq iz
  have ⟨hang_az, hang_zc⟩ := universal_crossing_angles hang hcross
  have hvqc : orientSign v q (S ic) = σ := orientSign_eq_of_mul_pos_left hvqa_ne hang.1
  have hvac : orientSign v (S ia) (S ic) = σ := orientSign_eq_of_mul_pos_left hvqa_ne hang.2
  have hvqz : orientSign v q (S iz) = σ := orientSign_eq_of_mul_pos_left hvqa_ne hang_az.1
  have hvaz : orientSign v (S ia) (S iz) = σ := orientSign_eq_of_mul_pos_left hvqa_ne hang_az.2
  have hvzc : orientSign v (S iz) (S ic) = σ :=
    (orientSign_eq_of_mul_pos_left hvqz_ne hang_zc.2).trans hvqz
  have hopp1 : oppSideBool v (S iz) (S ia) (S ic) = true :=
    (oppSideBool_iff_mul_neg (orient_w_S_S_ne hP Tv hiaz.symm) (orient_w_S_S_ne hP Tv hicz.symm)).mpr hcross.1
  have hopp2 : oppSideBool (S ia) (S ic) v (S iz) = true :=
    (oppSideBool_iff_mul_neg (orient_S_S_w_ne hP hiac Tv) (orient_S_S_S_ne hP hiac hicz hiaz)).mpr hcross.2
  have hcross_b : segsCrossBool v (S iz) (S ia) (S ic) = true := by
    unfold segsCrossBool; rw [hopp1, hopp2]; rfl
  have hiv_b : Sees P v q ∨
      (∃ s₁ s₂ : Fin n, s₁ ∈ Tv ∧ s₁ ∈ Finset.univ ∧ s₂ ∈ Tv ∧ s₂ ∈ Finset.univ ∧
        oppSideBool v q (S s₁) (S s₂) = true) ∨
      (∃ ie : Fin n, ie ∈ Tv ∧ ie ∈ Finset.univ ∧
        orientSign v q (S ie) = orientSign v q (S iz) ∧
        orientSign v (S ie) (S ia) = orientSign v q (S iz)) := by
    rcases hcond4 with hvq | ⟨ie, hie_notO, hie_ang⟩
    · exact Or.inl hvq
    · right; right
      have hvqe_ne : orient2D v q (S ie) ≠ 0 := orient_w_w_S_ne hP hTv_ne_Tq ie
      have hvqe_eq : orientSign v q (S ie) = σ :=
        (orientSign_eq_of_mul_pos_left hvqe_ne hie_ang.1).symm
      have hvea_eq : orientSign v (S ie) (S ia) = σ :=
        (orientSign_eq_of_mul_pos_left hvqe_ne hie_ang.2).trans hvqe_eq
      exact ⟨ie, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hie_notO⟩, Finset.mem_univ _,
        hvqe_eq.trans hvqz.symm, hvea_eq.trans hvqz.symm⟩
  have hcfg : HalfPlaneChirotopeConfig P S w Tv Finset.univ ia iz ic :=
    { hp_v := hiz_Tv
      ha_not_v := hia_not_Tv
      hc_not_v := hic_not_Tv
      ha_q := Finset.mem_univ _
      hp_q := Finset.mem_univ _
      hc_q := Finset.mem_univ _
      h_vqa := hvqz.symm
      h_vqc := hvqc.trans hvqz.symm
      h_vap := hvaz.trans hvqz.symm
      h_vpc := hvzc.trans hvqz.symm
      h_cross_ac := hopp2
      h_cond_iv := hiv_b }
  exact ⟨hvqc, hvac, hvqz, hvaz, hvzc, hcross_b, hopp2, hcfg⟩

/-- **Master `(C7)` Bridge (`isGoodChirotopeGap_of_goodAnchorPair`)**:
    Converts any `GoodAnchorPair P S w O_miss oa ob` + `IsBackVertexOf` + `SegmentsCross` on `Γ`
    directly into `IsGoodChirotopeGap P S w O_miss oa ob Γ` in pure `orientSign` form! -/
theorem isGoodChirotopeGap_of_goodAnchorPair {n : ℕ} {P : Set (ℝ × ℝ)}
    {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ}
    (hP : ShatteredSimplePolygon P S w)
    {O_miss : Finset (Fin n)} {oa ob : Fin n} {Γ : Finset (Fin n)}
    (hgap : GoodAnchorPair P S w O_miss oa ob)
    (hΓ : ∀ ip ∈ Γ, ip ∉ O_miss ∧
      IsBackVertexOf S (hullVertices S) ip (w (Finset.univ \ O_miss)) ∧
      SegmentsCross (w (Finset.univ \ O_miss)) (S ip) (S oa) (S ob)) :
    IsGoodChirotopeGap P S w O_miss oa ob Γ := by
  let Tv := Finset.univ \ O_miss
  let v := w Tv
  let q := w Finset.univ
  have hTv_ne_Tq : Tv ≠ Finset.univ := fun heq => by
    have hmem : oa ∈ Tv := heq.symm ▸ Finset.mem_univ oa
    exact (Finset.mem_sdiff.mp hmem).2 hgap.1
  have build_ord : ∀ (ia ic : Fin n),
      ((ia = oa ∧ ic = ob) ∨ (ia = ob ∧ ic = oa)) →
      ia ∈ O_miss → ic ∈ O_miss → ia ≠ ic →
      AngleLt v q (S ia) (S ic) →
      (Sees P v q ∨ ∃ ie : Fin n, ie ∉ O_miss ∧ AngleLt v q (S ie) (S ia)) →
      (∀ ip ∈ Γ, ip ∉ O_miss ∧ IsBackVertexOf S (hullVertices S) ip v ∧
        SegmentsCross v (S ip) (S ia) (S ic)) →
      IsGoodChirotopeGap P S w O_miss oa ob Γ := by
    intro ia ic h_ord hiaO hicO hiac hang hcond4 hΓ_ord
    let σ := orientSign v q (S ia)
    have hvqa_ne : orient2D v q (S ia) ≠ 0 := orient_w_w_S_ne hP hTv_ne_Tq ia
    have hvqc : orientSign v q (S ic) = σ := orientSign_eq_of_mul_pos_left hvqa_ne hang.1
    have hvac : orientSign v (S ia) (S ic) = σ := orientSign_eq_of_mul_pos_left hvqa_ne hang.2
    have hiv_top : Sees P v q ∨ ∃ ie ∈ Tv, orientSign v q (S ie) = σ ∧ orientSign v (S ie) (S ia) = σ := by
      rcases hcond4 with hvq | ⟨ie, hie_notO, hie_ang⟩
      · exact Or.inl hvq
      · right
        have hvqe_ne : orient2D v q (S ie) ≠ 0 := orient_w_w_S_ne hP hTv_ne_Tq ie
        have hvqe_eq : orientSign v q (S ie) = σ := (orientSign_eq_of_mul_pos_left hvqe_ne hie_ang.1).symm
        exact ⟨ie, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hie_notO⟩, hvqe_eq,
          (orientSign_eq_of_mul_pos_left hvqe_ne hie_ang.2).trans hvqe_eq⟩
    refine ⟨ia, ic, σ, h_ord, hiaO, hicO, hiac, rfl, hvqc, hvac, hiv_top, fun ip hip => ?_⟩
    obtain ⟨hip_notO, hback, hcr⟩ := hΓ_ord ip hip
    obtain ⟨_, _, hvqp, hvap, hvpc, hcr_b, hopp_b, hcfg⟩ :=
      halfPlaneChirotopeConfig_of_ordered_anchor_cross hP hiaO hicO hiac hang hcond4 hip_notO hcr
    obtain ⟨hca, hcb, hcc, hcs⟩ := half_plane_chirotope_clauses_C9 hP hcfg
    rw [hvqp] at hca hcb hcc hcs
    exact ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hip_notO⟩, hback.1, hback,
      fun pm he => (orientSign_eq_true_iff _ _ _).mpr (hback.2 pm ip he (Or.inr rfl)),
      fun pp he => (orientSign_eq_true_iff _ _ _).mpr (hback.2 ip pp he (Or.inl rfl)),
      hvqp, hvap, hvpc, hcr_b, hopp_b, hcfg, hca, hcb, hcc, hcs⟩
  rcases hgap with ⟨hoaO, hobO, hoab, ⟨hang, hcond4⟩ | ⟨hang, hcond4⟩⟩
  · exact build_ord oa ob (Or.inl ⟨rfl, rfl⟩) hoaO hobO hoab hang hcond4 hΓ
  · exact build_ord ob oa (Or.inr ⟨rfl, rfl⟩) hobO hoaO hoab.symm hang hcond4
      (fun ip hip => ⟨(hΓ ip hip).1, (hΓ ip hip).2.1, (hΓ ip hip).2.2.symm34⟩)

private lemma n_ge_three_of_ccwCycle {n kD : ℕ} {S : Fin n → ℝ × ℝ} {D : Finset (Fin n)}
    (cycD : CCWCycle S D kD) : 3 ≤ n := by
  have hcard : D.card = kD + 3 := by
    rw [← cycD.image_eq, Finset.card_image_of_injective Finset.univ cycD.inj, Finset.card_fin]
  have hle : D.card ≤ n := (Finset.card_le_univ D).trans_eq (Fintype.card_fin n)
  omega

/-- **Clause `(C7)` Part 1 (`c7_nonadj_triple_gap`, `upper_8.tex` Proposition 5.6)**:
    Every pairwise non-adjacent triple `O = {o1, o2, o3} ⊆ D` (`D ⊆ B \ H`, `6 ≤ |D|`) realizes
    `IsGoodChirotopeGap` on at least one of its three cyclic `D`-gaps `gap1`, `gap2`, `gap3`. -/
theorem c7_nonadj_triple_gap {n kD : ℕ} {P : Set (ℝ × ℝ)}
    {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ}
    (hP : ShatteredSimplePolygon P S w)
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
    IsGoodChirotopeGap P S w O_miss o1 o2 gap1 ∨
    IsGoodChirotopeGap P S w O_miss o2 o3 gap2 ∨
    IsGoodChirotopeGap P S w O_miss o3 o1 gap3 := by
  intro o1 o2 o3 O_miss gap1 gap2 gap3
  have h25 := mk_sec2To5Interface_general (n_ge_three_of_ccwCycle cycD) hP
  obtain ⟨oa, ob, Γ, hbranch, hgap, hΓ⟩ := gap_lemma hP h25 hD_sub cycD i1 i2 i3 h12 h23 h31 hsum
  have hnotO : ∀ {ia ib ic : Fin (kD + 3)},
      1 < (ia - ic).val →
      (ib - ia).val + (ic - ib).val + (ia - ic).val = kD + 3 →
      ∀ p ∈ D.filter (fun p => ∃ m : Fin (kD + 3), cycD.toFun m = p ∧
        0 < (m - ia).val ∧ (m - ia).val < (ib - ia).val),
      p ∉ ({cycD.toFun ia, cycD.toFun ib, cycD.toFun ic} : Finset (Fin n)) := by
    intro ia ib ic hia hs p hp hpO
    rcases (Finset.mem_filter.mp hp).2 with ⟨m, rfl, hm1, hm2⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hpO
    rcases hpO with h | h | h
    · have := cycD.inj h; subst this; simp at hm1
    · have := cycD.inj h; subst this; omega
    · have hm_eq := cycD.inj h
      rw [hm_eq] at hm2
      have hid : ic - ia = (ic - ib) + (ib - ia) := by abel
      rw [hid, Fin.val_add, Nat.mod_eq_of_lt (by omega)] at hm2
      omega
  rcases hbranch with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · exact Or.inl (isGoodChirotopeGap_of_goodAnchorPair hP hgap
      (fun ip hip => ⟨hnotO h31 hsum ip hip, (hΓ ip hip).1, (hΓ ip hip).2.1⟩))
  · refine Or.inr (Or.inl (isGoodChirotopeGap_of_goodAnchorPair hP hgap (fun ip hip => ⟨?_, (hΓ ip hip).1, (hΓ ip hip).2.1⟩)))
    have hset : ({o2, o3, o1} : Finset (Fin n)) = O_miss := by ext x; simp [O_miss]; tauto
    rw [← hset]; exact hnotO h12 (by omega) ip hip
  · refine Or.inr (Or.inr (isGoodChirotopeGap_of_goodAnchorPair hP hgap (fun ip hip => ⟨?_, (hΓ ip hip).1, (hΓ ip hip).2.1⟩)))
    have hset : ({o3, o1, o2} : Finset (Fin n)) = O_miss := by ext x; simp [O_miss]; tauto
    rw [← hset]; exact hnotO h23 (by omega) ip hip

/-- **Clause `(C7)` Part 2 (`c7_alternating_source`, `upper_8.tex` Proposition 5.5)**:
    Every alternating 6-vertex (`m = 3`) or 8-vertex (`m = 5`) source `C ⊆ D` has at least `1`
    (for `m = 3`) or `2` (for `m = 5`) even indices `ig` realizing `IsGoodChirotopeGap`. -/
theorem c7_alternating_source {n m : ℕ} {P : Set (ℝ × ℝ)}
    {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ}
    (hP : ShatteredSimplePolygon P S w)
    {C : Finset (Fin n)} (hm : m = 3 ∨ m = 5)
    (hCD : C ⊆ hullVertices S \ certifiedVertices S w)
    (cyc : CCWCycle S C m) :
    let O_miss := C.filter (fun x => ∃ i : Fin (m + 3), i.val % 2 = 1 ∧ cyc.toFun i = x)
    ∃ Tgt : Finset (Fin (m + 3)), Tgt.card = (if m = 3 then 1 else 2) ∧
      ∀ ig ∈ Tgt, ig.val % 2 = 0 ∧
        IsBackVertexOf S C (cyc.toFun ig) (w (Finset.univ \ O_miss)) ∧
        IsGoodChirotopeGap P S w O_miss (cyc.toFun (ig - 1)) (cyc.toFun (ig + 1)) {cyc.toFun ig} := by
  intro O_miss
  have h25 := mk_sec2To5Interface_general (n_ge_three_of_ccwCycle cyc) hP
  obtain ⟨Tgt, hcard, hTgt⟩ := good_targets hP h25 hm hCD cyc
  refine ⟨Tgt, hcard, fun ig hig => ?_⟩
  obtain ⟨hev, hbackC, hbackB, hgap, hcross, _, _⟩ := hTgt ig hig
  have hnotO : cyc.toFun ig ∉ O_miss := by
    intro hmem; rcases (Finset.mem_filter.mp hmem).2 with ⟨j, hj, heq⟩
    rw [← cyc.inj heq] at hev; omega
  refine ⟨hev, hbackC, isGoodChirotopeGap_of_goodAnchorPair hP hgap (fun ip hip => ?_)⟩
  rw [Finset.mem_singleton] at hip; subst hip
  exact ⟨hnotO, hbackB, hcross⟩

/-- Explicit 6-way disjunction on an alternating hexagon `C ⊆ D` (`m = 3`, `upper_8.tex` Proposition 5.5):
    at least one of the three even vertices `0, 2, 4` realizes `IsGoodChirotopeGap`! -/
theorem c7_alternating_hexagon {n : ℕ} {P : Set (ℝ × ℝ)}
    {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ}
    (hP : ShatteredSimplePolygon P S w)
    {C : Finset (Fin n)} (hCD : C ⊆ hullVertices S \ certifiedVertices S w)
    (cyc : CCWCycle S C 3) :
    let O_miss : Finset (Fin n) := {cyc.toFun 1, cyc.toFun 3, cyc.toFun 5}
    IsGoodChirotopeGap P S w O_miss (cyc.toFun 5) (cyc.toFun 1) {cyc.toFun 0} ∨
    IsGoodChirotopeGap P S w O_miss (cyc.toFun 1) (cyc.toFun 3) {cyc.toFun 2} ∨
    IsGoodChirotopeGap P S w O_miss (cyc.toFun 3) (cyc.toFun 5) {cyc.toFun 4} := by
  intro O_miss
  obtain ⟨Tgt, hcard, hTgt⟩ := c7_alternating_source hP (Or.inl rfl) hCD cyc
  have hO_eq : C.filter (fun x => ∃ i : Fin 6, i.val % 2 = 1 ∧ cyc.toFun i = x) = O_miss := by
    ext x; simp only [Finset.mem_filter, O_miss, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨_, i, hi, rfl⟩; fin_cases i <;> simp at hi <;> tauto
    · rintro (rfl | rfl | rfl)
      · exact ⟨ccwCycle_mem cyc 1, 1, by decide, rfl⟩
      · exact ⟨ccwCycle_mem cyc 3, 3, by decide, rfl⟩
      · exact ⟨ccwCycle_mem cyc 5, 5, by decide, rfl⟩
  obtain ⟨ig, hig⟩ := Finset.card_pos.mp (by rw [hcard]; decide : 0 < Tgt.card)
  obtain ⟨hev, _, hgood⟩ := hTgt ig hig
  rw [hO_eq] at hgood
  fin_cases ig <;> simp at hev
  · exact Or.inl hgood
  · exact Or.inr (Or.inl hgood)
  · exact Or.inr (Or.inr hgood)

/-- **Clause `(C7)` Part 3 (`c7_interior_anchor`, `upper_8.tex` Proposition 5.8)**:
    Every interior-anchor source `O* = {b', y, b}` (`y ∈ M` on exit edge `u0 v0` of `D`, `5 ≤ |D|`)
    satisfies `inOpenTriBool (S y) v (S u0) (S v0) = true` and realizes `IsGoodChirotopeGap` on at least
    one of `gapL` (`{b', y}`), `gapR` (`{y, b}`), or `gapMid` (`{b, b'}`). -/
theorem c7_interior_anchor {n kD : ℕ} {P : Set (ℝ × ℝ)}
    {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ}
    (hP : ShatteredSimplePolygon P S w)
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
    inOpenTriBool (S y) v (S u0) (S v0) = true ∧
    (IsGoodChirotopeGap P S w O_star b' y gapL ∨
     IsGoodChirotopeGap P S w O_star y b gapR ∨
     IsGoodChirotopeGap P S w O_star b b' gapMid) := by
  intro b' u0 v0 b O_star v gapL gapR gapMid
  have h25 := mk_sec2To5Interface_general (n_ge_three_of_ccwCycle cycD) hP
  obtain ⟨⟨hy_tri, _⟩, oa, ob, Γ, hbranch, hgap, hΓ, _⟩ :=
    interior_anchor hP h25 hDB cycD hyM ib' iu0 iv0 ib id_v hiv0 hord1 hord2 hord3 hord4 h_exit_v
  have hy_notD : y ∉ D := (Finset.mem_sdiff.mp hyM).2
  have hu0_ne_v0 : u0 ≠ v0 := cycD.inj.ne (fun h => by rw [h] at hord2; omega)
  have hy_ne_u0 : y ≠ u0 := fun h => hy_notD (h ▸ ccwCycle_mem cycD iu0)
  have hy_ne_v0 : y ≠ v0 := fun h => hy_notD (h ▸ ccwCycle_mem cycD iv0)
  have hy_tri_b : inOpenTriBool (S y) v (S u0) (S v0) = true :=
    (inOpenTriBool_S_w_S_S hP hy_ne_u0 hy_ne_v0 hu0_ne_v0 (Finset.univ \ O_star)).mpr hy_tri
  refine ⟨hy_tri_b, ?_⟩
  rcases hbranch with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · refine Or.inl (isGoodChirotopeGap_of_goodAnchorPair hP hgap (fun ip hip => ⟨?_, (hΓ ip hip).1, (hΓ ip hip).2.1⟩))
    intro hpO; rcases (Finset.mem_filter.mp hip).2 with ⟨m, rfl, hm1, hm2⟩
    simp only [O_star, Finset.mem_insert, Finset.mem_singleton] at hpO
    rcases hpO with h | h | h
    · have hm_eq := cycD.inj h; rw [hm_eq, sub_self, Fin.val_zero] at hm1; omega
    · exact hy_notD (by rw [← h]; exact ccwCycle_mem cycD m)
    · have hm_eq := cycD.inj h; rw [hm_eq] at hm2; omega
  · refine Or.inr (Or.inl (isGoodChirotopeGap_of_goodAnchorPair hP hgap (fun ip hip => ⟨?_, (hΓ ip hip).1, (hΓ ip hip).2.1⟩)))
    intro hpO; rcases (Finset.mem_filter.mp hip).2 with ⟨m, rfl, hm1, hm2⟩
    simp only [O_star, Finset.mem_insert, Finset.mem_singleton] at hpO
    rcases hpO with h | h | h
    · have hm_eq := cycD.inj h; rw [hm_eq, sub_self, Fin.val_zero] at hm1; omega
    · exact hy_notD (by rw [← h]; exact ccwCycle_mem cycD m)
    · have hm_eq := cycD.inj h; rw [hm_eq] at hm2; omega
  · refine Or.inr (Or.inr (isGoodChirotopeGap_of_goodAnchorPair hP hgap (fun ip hip => ⟨?_, (hΓ ip hip).1, (hΓ ip hip).2.1⟩)))
    intro hpO; rcases (Finset.mem_filter.mp hip).2 with ⟨m, rfl, hm1, hm2⟩
    simp only [O_star, Finset.mem_insert, Finset.mem_singleton] at hpO
    rcases hpO with h | h | h
    · have hm_eq := cycD.inj h; rw [hm_eq] at hm2; omega
    · exact hy_notD (by rw [← h]; exact ccwCycle_mem cycD m)
    · have hm_eq := cycD.inj h; rw [hm_eq, sub_self, Fin.val_zero] at hm1; omega

private lemma inIntTri_exit_of_bool {n k : ℕ} {P : Set (ℝ × ℝ)}
    {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ}
    (hP : ShatteredSimplePolygon P S w)
    {D : Finset (Fin n)} (cycD : CCWCycle S D k)
    {y : Fin n} (hy_notD : y ∉ D) {i j : Fin (k + 3)} (hij : i ≠ j)
    {Tw : Finset (Fin n)}
    (hb : inOpenTriBool (S y) (w Tw) (S (cycD.toFun i)) (S (cycD.toFun j)) = true) :
    InIntTri (w Tw) (S (cycD.toFun i)) (S (cycD.toFun j)) (S y) :=
  (inOpenTriBool_S_w_S_S hP
    (fun h => hy_notD (by rw [h]; exact ccwCycle_mem cycD i))
    (fun h => hy_notD (by rw [h]; exact ccwCycle_mem cycD j))
    (cycD.inj.ne hij) Tw).mp hb

private lemma not_mem_Ostar_of_ne {n k : ℕ} {S : Fin n → ℝ × ℝ} {D : Finset (Fin n)}
    (cycD : CCWCycle S D k) {y0 y1 : Fin n} (hy0 : y0 ∉ D) (hy1 : y1 ∉ D)
    {ib m : Fin (k + 3)} (hne : m ≠ ib) :
    cycD.toFun m ∉ ({cycD.toFun ib, y0, y1} : Finset (Fin n)) := by
  intro h; simp only [Finset.mem_insert, Finset.mem_singleton] at h
  rcases h with h | h | h
  · exact hne (cycD.inj h)
  · exact hy0 (by rw [← h]; exact ccwCycle_mem cycD m)
  · exact hy1 (by rw [← h]; exact ccwCycle_mem cycD m)

/-- **Clause `(C7)` Part 4a (`c7_pentagon_disjoint_exits`, `upper_8.tex` Lemma 5.9)**:
    Pentagon `D = (0, 1, 2, 3, 4)` with disjoint exit edges `01` (`y0`) and `23` (`y1`), `O* = {4, y0, y1}`. -/
theorem c7_pentagon_disjoint_exits {n : ℕ} {P : Set (ℝ × ℝ)}
    {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ}
    (hP : ShatteredSimplePolygon P S w)
    {D : Finset (Fin n)} (hDB : D = hullVertices S \ certifiedVertices S w)
    (cycD : CCWCycle S D 2)
    {y0 y1 : Fin n} (hy0M : y0 ∈ Finset.univ \ D) (hy1M : y1 ∈ Finset.univ \ D) (hy01 : y0 ≠ y1)
    (hy0_tri : inOpenTriBool (S y0) (w (Finset.univ \ {cycD.toFun 4, y0, y1})) (S (cycD.toFun 0)) (S (cycD.toFun 1)) = true)
    (hy1_tri : inOpenTriBool (S y1) (w (Finset.univ \ {cycD.toFun 4, y0, y1})) (S (cycD.toFun 2)) (S (cycD.toFun 3)) = true)
    (h_not_lr : ∀ l r : Fin n, (certifiedVertices S w).Nonempty →
      IsCCWEdge S D l r → (∀ h ∈ certifiedVertices S w, orient2D (S l) (S r) (S h) < 0) →
      (cycD.toFun 0, cycD.toFun 1) ≠ (l, r) ∧ (cycD.toFun 2, cycD.toFun 3) ≠ (l, r)) :
    let b := cycD.toFun 4
    let O_star : Finset (Fin n) := {b, y0, y1}
    IsGoodChirotopeGap P S w O_star b y0 {cycD.toFun 0} ∨
    IsGoodChirotopeGap P S w O_star y0 y1 {cycD.toFun 1, cycD.toFun 2} ∨
    IsGoodChirotopeGap P S w O_star y1 b {cycD.toFun 3} := by
  intro b O_star
  have hy0_notD : y0 ∉ D := (Finset.mem_sdiff.mp hy0M).2
  have hy1_notD : y1 ∉ D := (Finset.mem_sdiff.mp hy1M).2
  have h25 := mk_sec2To5Interface_general (n_ge_three_of_ccwCycle cycD) hP
  obtain ⟨oa, ob, Γ, hbr, hgap, hΓ, _⟩ := pairs_in_M hP h25 hDB cycD hy0M hy1M hy01
    (inIntTri_exit_of_bool hP cycD hy0_notD (by decide) hy0_tri)
    (inIntTri_exit_of_bool hP cycD hy1_notD (by decide) hy1_tri)
    h_not_lr
  rcases hbr with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · refine Or.inl (isGoodChirotopeGap_of_goodAnchorPair hP hgap (fun ip hip => ⟨?_, (hΓ ip hip).1, (hΓ ip hip).2.1⟩))
    rw [Finset.mem_singleton] at hip; subst hip; exact not_mem_Ostar_of_ne cycD hy0_notD hy1_notD (by decide)
  · refine Or.inr (Or.inl (isGoodChirotopeGap_of_goodAnchorPair hP hgap (fun ip hip => ⟨?_, (hΓ ip hip).1, (hΓ ip hip).2.1⟩)))
    simp only [Finset.mem_insert, Finset.mem_singleton] at hip; rcases hip with rfl | rfl <;>
      exact not_mem_Ostar_of_ne cycD hy0_notD hy1_notD (by decide)
  · refine Or.inr (Or.inr (isGoodChirotopeGap_of_goodAnchorPair hP hgap (fun ip hip => ⟨?_, (hΓ ip hip).1, (hΓ ip hip).2.1⟩)))
    rw [Finset.mem_singleton] at hip; subst hip; exact not_mem_Ostar_of_ne cycD hy0_notD hy1_notD (by decide)

/-- **Clause `(C7)` Part 4b (`c7_pentagon_adjacent_exits_b4`, `upper_8.tex` Lemma 5.10, `b = 4`)**. -/
theorem c7_pentagon_adjacent_exits_b4 {n : ℕ} {P : Set (ℝ × ℝ)}
    {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ}
    (hP : ShatteredSimplePolygon P S w)
    {D : Finset (Fin n)} (hDB : D = hullVertices S \ certifiedVertices S w)
    (cycD : CCWCycle S D 2)
    {y0 y1 : Fin n} (hy0M : y0 ∈ Finset.univ \ D) (hy1M : y1 ∈ Finset.univ \ D) (hy01 : y0 ≠ y1)
    (hy0_tri : inOpenTriBool (S y0) (w (Finset.univ \ {cycD.toFun 4, y0, y1})) (S (cycD.toFun 0)) (S (cycD.toFun 1)) = true)
    (hy1_tri : inOpenTriBool (S y1) (w (Finset.univ \ {cycD.toFun 4, y0, y1})) (S (cycD.toFun 1)) (S (cycD.toFun 2)) = true)
    (h_not_lr : ∀ l r : Fin n, (certifiedVertices S w).Nonempty →
      IsCCWEdge S D l r → (∀ h ∈ certifiedVertices S w, orient2D (S l) (S r) (S h) < 0) →
      (cycD.toFun 0, cycD.toFun 1) ≠ (l, r) ∧ (cycD.toFun 1, cycD.toFun 2) ≠ (l, r)) :
    let b := cycD.toFun 4
    let O_star : Finset (Fin n) := {b, y0, y1}
    IsGoodChirotopeGap P S w O_star b y0 {cycD.toFun 0} ∨
    IsGoodChirotopeGap P S w O_star y0 y1 {cycD.toFun 1} ∨
    IsGoodChirotopeGap P S w O_star y1 b {cycD.toFun 2, cycD.toFun 3} := by
  intro b O_star
  have hy0_notD : y0 ∉ D := (Finset.mem_sdiff.mp hy0M).2
  have hy1_notD : y1 ∉ D := (Finset.mem_sdiff.mp hy1M).2
  have h25 := mk_sec2To5Interface_general (n_ge_three_of_ccwCycle cycD) hP
  obtain ⟨oa, ob, Γ, hbr, hgap, hΓ, _⟩ := adjacent_exits_b4 hP h25 hDB cycD hy0M hy1M hy01
    (inIntTri_exit_of_bool hP cycD hy0_notD (by decide) hy0_tri)
    (inIntTri_exit_of_bool hP cycD hy1_notD (by decide) hy1_tri)
    h_not_lr
  rcases hbr with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · refine Or.inl (isGoodChirotopeGap_of_goodAnchorPair hP hgap (fun ip hip => ⟨?_, (hΓ ip hip).1, (hΓ ip hip).2.1⟩))
    rw [Finset.mem_singleton] at hip; subst hip; exact not_mem_Ostar_of_ne cycD hy0_notD hy1_notD (by decide)
  · refine Or.inr (Or.inl (isGoodChirotopeGap_of_goodAnchorPair hP hgap (fun ip hip => ⟨?_, (hΓ ip hip).1, (hΓ ip hip).2.1⟩)) )
    rw [Finset.mem_singleton] at hip; subst hip; exact not_mem_Ostar_of_ne cycD hy0_notD hy1_notD (by decide)
  · refine Or.inr (Or.inr (isGoodChirotopeGap_of_goodAnchorPair hP hgap (fun ip hip => ⟨?_, (hΓ ip hip).1, (hΓ ip hip).2.1⟩)))
    simp only [Finset.mem_insert, Finset.mem_singleton] at hip; rcases hip with rfl | rfl <;>
      exact not_mem_Ostar_of_ne cycD hy0_notD hy1_notD (by decide)

/-- **Clause `(C7)` Part 4c (`c7_pentagon_adjacent_exits_b3`, `upper_8.tex` Lemma 5.10, `b = 3`)**. -/
theorem c7_pentagon_adjacent_exits_b3 {n : ℕ} {P : Set (ℝ × ℝ)}
    {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ}
    (hP : ShatteredSimplePolygon P S w)
    {D : Finset (Fin n)} (hDB : D = hullVertices S \ certifiedVertices S w)
    (cycD : CCWCycle S D 2)
    {y0 y1 : Fin n} (hy0M : y0 ∈ Finset.univ \ D) (hy1M : y1 ∈ Finset.univ \ D) (hy01 : y0 ≠ y1)
    (hy0_tri : inOpenTriBool (S y0) (w (Finset.univ \ {cycD.toFun 3, y0, y1})) (S (cycD.toFun 0)) (S (cycD.toFun 1)) = true)
    (hy1_tri : inOpenTriBool (S y1) (w (Finset.univ \ {cycD.toFun 3, y0, y1})) (S (cycD.toFun 1)) (S (cycD.toFun 2)) = true)
    (h_not_lr : ∀ l r : Fin n, (certifiedVertices S w).Nonempty →
      IsCCWEdge S D l r → (∀ h ∈ certifiedVertices S w, orient2D (S l) (S r) (S h) < 0) →
      (cycD.toFun 0, cycD.toFun 1) ≠ (l, r) ∧ (cycD.toFun 1, cycD.toFun 2) ≠ (l, r)) :
    let b := cycD.toFun 3
    let O_star : Finset (Fin n) := {b, y0, y1}
    IsGoodChirotopeGap P S w O_star b y0 {cycD.toFun 4, cycD.toFun 0} ∨
    IsGoodChirotopeGap P S w O_star y0 y1 {cycD.toFun 1} ∨
    IsGoodChirotopeGap P S w O_star y1 b {cycD.toFun 2} := by
  intro b O_star
  have hy0_notD : y0 ∉ D := (Finset.mem_sdiff.mp hy0M).2
  have hy1_notD : y1 ∉ D := (Finset.mem_sdiff.mp hy1M).2
  have h25 := mk_sec2To5Interface_general (n_ge_three_of_ccwCycle cycD) hP
  obtain ⟨oa, ob, Γ, hbr, hgap, hΓ, _⟩ := adjacent_exits_b3 hP h25 hDB cycD hy0M hy1M hy01
    (inIntTri_exit_of_bool hP cycD hy0_notD (by decide) hy0_tri)
    (inIntTri_exit_of_bool hP cycD hy1_notD (by decide) hy1_tri)
    h_not_lr
  rcases hbr with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · refine Or.inl (isGoodChirotopeGap_of_goodAnchorPair hP hgap (fun ip hip => ⟨?_, (hΓ ip hip).1, (hΓ ip hip).2.1⟩))
    simp only [Finset.mem_insert, Finset.mem_singleton] at hip; rcases hip with rfl | rfl <;>
      exact not_mem_Ostar_of_ne cycD hy0_notD hy1_notD (by decide)
  · refine Or.inr (Or.inl (isGoodChirotopeGap_of_goodAnchorPair hP hgap (fun ip hip => ⟨?_, (hΓ ip hip).1, (hΓ ip hip).2.1⟩)))
    rw [Finset.mem_singleton] at hip; subst hip; exact not_mem_Ostar_of_ne cycD hy0_notD hy1_notD (by decide)
  · refine Or.inr (Or.inr (isGoodChirotopeGap_of_goodAnchorPair hP hgap (fun ip hip => ⟨?_, (hΓ ip hip).1, (hΓ ip hip).2.1⟩)))
    rw [Finset.mem_singleton] at hip; subst hip; exact not_mem_Ostar_of_ne cycD hy0_notD hy1_notD (by decide)

/-- **Clause `(C7)` Part 5a (`c7_hexagon_disjoint_exits_23_b4`, `upper_8.tex` Lemma 5.11(i), `b = 4`)**. -/
theorem c7_hexagon_disjoint_exits_23_b4 {n : ℕ} {P : Set (ℝ × ℝ)}
    {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ}
    (hP : ShatteredSimplePolygon P S w)
    {D : Finset (Fin n)} (hDB : D = hullVertices S \ certifiedVertices S w)
    (cycD : CCWCycle S D 3)
    {y0 y1 : Fin n} (hy0M : y0 ∈ Finset.univ \ D) (hy1M : y1 ∈ Finset.univ \ D) (hy01 : y0 ≠ y1)
    (hy0_tri : inOpenTriBool (S y0) (w (Finset.univ \ {cycD.toFun 4, y0, y1})) (S (cycD.toFun 0)) (S (cycD.toFun 1)) = true)
    (hy1_tri : inOpenTriBool (S y1) (w (Finset.univ \ {cycD.toFun 4, y0, y1})) (S (cycD.toFun 2)) (S (cycD.toFun 3)) = true)
    (h_not_lr : ∀ l r : Fin n, (certifiedVertices S w).Nonempty →
      IsCCWEdge S D l r → (∀ h ∈ certifiedVertices S w, orient2D (S l) (S r) (S h) < 0) →
      (cycD.toFun 0, cycD.toFun 1) ≠ (l, r) ∧ (cycD.toFun 2, cycD.toFun 3) ≠ (l, r)) :
    let b := cycD.toFun 4
    let O_star : Finset (Fin n) := {b, y0, y1}
    IsGoodChirotopeGap P S w O_star b y0 {cycD.toFun 5, cycD.toFun 0} ∨
    IsGoodChirotopeGap P S w O_star y0 y1 {cycD.toFun 1, cycD.toFun 2} ∨
    IsGoodChirotopeGap P S w O_star y1 b {cycD.toFun 3} := by
  intro b O_star
  have hy0_notD : y0 ∉ D := (Finset.mem_sdiff.mp hy0M).2
  have hy1_notD : y1 ∉ D := (Finset.mem_sdiff.mp hy1M).2
  have h25 := mk_sec2To5Interface_general (n_ge_three_of_ccwCycle cycD) hP
  obtain ⟨oa, ob, Γ, hbr, hgap, hΓ, _⟩ := hexagon_disjoint_exits_23_b4 hP h25 hDB cycD hy0M hy1M hy01
    (inIntTri_exit_of_bool hP cycD hy0_notD (by decide) hy0_tri)
    (inIntTri_exit_of_bool hP cycD hy1_notD (by decide) hy1_tri)
    h_not_lr
  rcases hbr with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · refine Or.inl (isGoodChirotopeGap_of_goodAnchorPair hP hgap (fun ip hip => ⟨?_, (hΓ ip hip).1, (hΓ ip hip).2.1⟩))
    simp only [Finset.mem_insert, Finset.mem_singleton] at hip; rcases hip with rfl | rfl <;>
      exact not_mem_Ostar_of_ne cycD hy0_notD hy1_notD (by decide)
  · refine Or.inr (Or.inl (isGoodChirotopeGap_of_goodAnchorPair hP hgap (fun ip hip => ⟨?_, (hΓ ip hip).1, (hΓ ip hip).2.1⟩)))
    simp only [Finset.mem_insert, Finset.mem_singleton] at hip; rcases hip with rfl | rfl <;>
      exact not_mem_Ostar_of_ne cycD hy0_notD hy1_notD (by decide)
  · refine Or.inr (Or.inr (isGoodChirotopeGap_of_goodAnchorPair hP hgap (fun ip hip => ⟨?_, (hΓ ip hip).1, (hΓ ip hip).2.1⟩)))
    rw [Finset.mem_singleton] at hip; subst hip; exact not_mem_Ostar_of_ne cycD hy0_notD hy1_notD (by decide)

/-- **Clause `(C7)` Part 5b (`c7_hexagon_disjoint_exits_23_b5`, `upper_8.tex` Lemma 5.11(i), `b = 5`)**. -/
theorem c7_hexagon_disjoint_exits_23_b5 {n : ℕ} {P : Set (ℝ × ℝ)}
    {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ}
    (hP : ShatteredSimplePolygon P S w)
    {D : Finset (Fin n)} (hDB : D = hullVertices S \ certifiedVertices S w)
    (cycD : CCWCycle S D 3)
    {y0 y1 : Fin n} (hy0M : y0 ∈ Finset.univ \ D) (hy1M : y1 ∈ Finset.univ \ D) (hy01 : y0 ≠ y1)
    (hy0_tri : inOpenTriBool (S y0) (w (Finset.univ \ {cycD.toFun 5, y0, y1})) (S (cycD.toFun 0)) (S (cycD.toFun 1)) = true)
    (hy1_tri : inOpenTriBool (S y1) (w (Finset.univ \ {cycD.toFun 5, y0, y1})) (S (cycD.toFun 2)) (S (cycD.toFun 3)) = true)
    (h_not_lr : ∀ l r : Fin n, (certifiedVertices S w).Nonempty →
      IsCCWEdge S D l r → (∀ h ∈ certifiedVertices S w, orient2D (S l) (S r) (S h) < 0) →
      (cycD.toFun 0, cycD.toFun 1) ≠ (l, r) ∧ (cycD.toFun 2, cycD.toFun 3) ≠ (l, r)) :
    let b := cycD.toFun 5
    let O_star : Finset (Fin n) := {b, y0, y1}
    IsGoodChirotopeGap P S w O_star b y0 {cycD.toFun 0} ∨
    IsGoodChirotopeGap P S w O_star y0 y1 {cycD.toFun 1, cycD.toFun 2} ∨
    IsGoodChirotopeGap P S w O_star y1 b {cycD.toFun 3, cycD.toFun 4} := by
  intro b O_star
  have hy0_notD : y0 ∉ D := (Finset.mem_sdiff.mp hy0M).2
  have hy1_notD : y1 ∉ D := (Finset.mem_sdiff.mp hy1M).2
  have h25 := mk_sec2To5Interface_general (n_ge_three_of_ccwCycle cycD) hP
  obtain ⟨oa, ob, Γ, hbr, hgap, hΓ, _⟩ := hexagon_disjoint_exits_23_b5 hP h25 hDB cycD hy0M hy1M hy01
    (inIntTri_exit_of_bool hP cycD hy0_notD (by decide) hy0_tri)
    (inIntTri_exit_of_bool hP cycD hy1_notD (by decide) hy1_tri)
    h_not_lr
  rcases hbr with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · refine Or.inl (isGoodChirotopeGap_of_goodAnchorPair hP hgap (fun ip hip => ⟨?_, (hΓ ip hip).1, (hΓ ip hip).2.1⟩))
    rw [Finset.mem_singleton] at hip; subst hip; exact not_mem_Ostar_of_ne cycD hy0_notD hy1_notD (by decide)
  · refine Or.inr (Or.inl (isGoodChirotopeGap_of_goodAnchorPair hP hgap (fun ip hip => ⟨?_, (hΓ ip hip).1, (hΓ ip hip).2.1⟩)))
    simp only [Finset.mem_insert, Finset.mem_singleton] at hip; rcases hip with rfl | rfl <;>
      exact not_mem_Ostar_of_ne cycD hy0_notD hy1_notD (by decide)
  · refine Or.inr (Or.inr (isGoodChirotopeGap_of_goodAnchorPair hP hgap (fun ip hip => ⟨?_, (hΓ ip hip).1, (hΓ ip hip).2.1⟩)))
    simp only [Finset.mem_insert, Finset.mem_singleton] at hip; rcases hip with rfl | rfl <;>
      exact not_mem_Ostar_of_ne cycD hy0_notD hy1_notD (by decide)

/-- **Clause `(C7)` Part 5c (`c7_hexagon_disjoint_exits_34_b2`, `upper_8.tex` Lemma 5.11(ii), `b = 2`)**. -/
theorem c7_hexagon_disjoint_exits_34_b2 {n : ℕ} {P : Set (ℝ × ℝ)}
    {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ}
    (hP : ShatteredSimplePolygon P S w)
    {D : Finset (Fin n)} (hDB : D = hullVertices S \ certifiedVertices S w)
    (cycD : CCWCycle S D 3)
    {y0 y1 : Fin n} (hy0M : y0 ∈ Finset.univ \ D) (hy1M : y1 ∈ Finset.univ \ D) (hy01 : y0 ≠ y1)
    (hy0_tri : inOpenTriBool (S y0) (w (Finset.univ \ {cycD.toFun 2, y0, y1})) (S (cycD.toFun 0)) (S (cycD.toFun 1)) = true)
    (hy1_tri : inOpenTriBool (S y1) (w (Finset.univ \ {cycD.toFun 2, y0, y1})) (S (cycD.toFun 3)) (S (cycD.toFun 4)) = true)
    (h_not_lr : ∀ l r : Fin n, (certifiedVertices S w).Nonempty →
      IsCCWEdge S D l r → (∀ h ∈ certifiedVertices S w, orient2D (S l) (S r) (S h) < 0) →
      (cycD.toFun 0, cycD.toFun 1) ≠ (l, r) ∧ (cycD.toFun 3, cycD.toFun 4) ≠ (l, r)) :
    let b := cycD.toFun 2
    let O_star : Finset (Fin n) := {b, y0, y1}
    IsGoodChirotopeGap P S w O_star b y1 {cycD.toFun 3} ∨
    IsGoodChirotopeGap P S w O_star y1 y0 {cycD.toFun 4, cycD.toFun 5, cycD.toFun 0} ∨
    IsGoodChirotopeGap P S w O_star y0 b {cycD.toFun 1} := by
  intro b O_star
  have hy0_notD : y0 ∉ D := (Finset.mem_sdiff.mp hy0M).2
  have hy1_notD : y1 ∉ D := (Finset.mem_sdiff.mp hy1M).2
  have h25 := mk_sec2To5Interface_general (n_ge_three_of_ccwCycle cycD) hP
  obtain ⟨oa, ob, Γ, hbr, hgap, hΓ, _⟩ := hexagon_disjoint_exits_34_b2 hP h25 hDB cycD hy0M hy1M hy01
    (inIntTri_exit_of_bool hP cycD hy0_notD (by decide) hy0_tri)
    (inIntTri_exit_of_bool hP cycD hy1_notD (by decide) hy1_tri)
    h_not_lr
  rcases hbr with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · refine Or.inl (isGoodChirotopeGap_of_goodAnchorPair hP hgap (fun ip hip => ⟨?_, (hΓ ip hip).1, (hΓ ip hip).2.1⟩))
    rw [Finset.mem_singleton] at hip; subst hip; exact not_mem_Ostar_of_ne cycD hy0_notD hy1_notD (by decide)
  · refine Or.inr (Or.inl (isGoodChirotopeGap_of_goodAnchorPair hP hgap (fun ip hip => ⟨?_, (hΓ ip hip).1, (hΓ ip hip).2.1⟩)))
    simp only [Finset.mem_insert, Finset.mem_singleton] at hip; rcases hip with rfl | rfl | rfl <;>
      exact not_mem_Ostar_of_ne cycD hy0_notD hy1_notD (by decide)
  · refine Or.inr (Or.inr (isGoodChirotopeGap_of_goodAnchorPair hP hgap (fun ip hip => ⟨?_, (hΓ ip hip).1, (hΓ ip hip).2.1⟩)))
    rw [Finset.mem_singleton] at hip; subst hip; exact not_mem_Ostar_of_ne cycD hy0_notD hy1_notD (by decide)

/-- **Clause `(C7)` Part 5d (`c7_hexagon_adjacent_exits_b5`, `upper_8.tex` Lemma 5.12(i), `b = 5`)**. -/
theorem c7_hexagon_adjacent_exits_b5 {n : ℕ} {P : Set (ℝ × ℝ)}
    {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ}
    (hP : ShatteredSimplePolygon P S w)
    {D : Finset (Fin n)} (hDB : D = hullVertices S \ certifiedVertices S w)
    (cycD : CCWCycle S D 3)
    {y0 y1 : Fin n} (hy0M : y0 ∈ Finset.univ \ D) (hy1M : y1 ∈ Finset.univ \ D) (hy01 : y0 ≠ y1)
    (hy0_tri : inOpenTriBool (S y0) (w (Finset.univ \ {cycD.toFun 5, y0, y1})) (S (cycD.toFun 0)) (S (cycD.toFun 1)) = true)
    (hy1_tri : inOpenTriBool (S y1) (w (Finset.univ \ {cycD.toFun 5, y0, y1})) (S (cycD.toFun 1)) (S (cycD.toFun 2)) = true)
    (h_not_lr : ∀ l r : Fin n, (certifiedVertices S w).Nonempty →
      IsCCWEdge S D l r → (∀ h ∈ certifiedVertices S w, orient2D (S l) (S r) (S h) < 0) →
      (cycD.toFun 0, cycD.toFun 1) ≠ (l, r) ∧ (cycD.toFun 1, cycD.toFun 2) ≠ (l, r)) :
    let b := cycD.toFun 5
    let O_star : Finset (Fin n) := {b, y0, y1}
    IsGoodChirotopeGap P S w O_star b y0 {cycD.toFun 0} ∨
    IsGoodChirotopeGap P S w O_star y0 y1 {cycD.toFun 1} ∨
    IsGoodChirotopeGap P S w O_star y1 b {cycD.toFun 2, cycD.toFun 3, cycD.toFun 4} := by
  intro b O_star
  have hy0_notD : y0 ∉ D := (Finset.mem_sdiff.mp hy0M).2
  have hy1_notD : y1 ∉ D := (Finset.mem_sdiff.mp hy1M).2
  have h25 := mk_sec2To5Interface_general (n_ge_three_of_ccwCycle cycD) hP
  obtain ⟨oa, ob, Γ, hbr, hgap, hΓ, _⟩ := hexagon_adjacent_exits_b5 hP h25 hDB cycD hy0M hy1M hy01
    (inIntTri_exit_of_bool hP cycD hy0_notD (by decide) hy0_tri)
    (inIntTri_exit_of_bool hP cycD hy1_notD (by decide) hy1_tri)
    h_not_lr
  rcases hbr with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · refine Or.inl (isGoodChirotopeGap_of_goodAnchorPair hP hgap (fun ip hip => ⟨?_, (hΓ ip hip).1, (hΓ ip hip).2.1⟩))
    rw [Finset.mem_singleton] at hip; subst hip; exact not_mem_Ostar_of_ne cycD hy0_notD hy1_notD (by decide)
  · refine Or.inr (Or.inl (isGoodChirotopeGap_of_goodAnchorPair hP hgap (fun ip hip => ⟨?_, (hΓ ip hip).1, (hΓ ip hip).2.1⟩)))
    rw [Finset.mem_singleton] at hip; subst hip; exact not_mem_Ostar_of_ne cycD hy0_notD hy1_notD (by decide)
  · refine Or.inr (Or.inr (isGoodChirotopeGap_of_goodAnchorPair hP hgap (fun ip hip => ⟨?_, (hΓ ip hip).1, (hΓ ip hip).2.1⟩)))
    simp only [Finset.mem_insert, Finset.mem_singleton] at hip; rcases hip with rfl | rfl | rfl <;>
      exact not_mem_Ostar_of_ne cycD hy0_notD hy1_notD (by decide)

/-- **Clause `(C7)` Part 5e (`c7_hexagon_adjacent_exits_b3`, `upper_8.tex` Lemma 5.12(i), `b = 3`)**. -/
theorem c7_hexagon_adjacent_exits_b3 {n : ℕ} {P : Set (ℝ × ℝ)}
    {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ}
    (hP : ShatteredSimplePolygon P S w)
    {D : Finset (Fin n)} (hDB : D = hullVertices S \ certifiedVertices S w)
    (cycD : CCWCycle S D 3)
    {y0 y1 : Fin n} (hy0M : y0 ∈ Finset.univ \ D) (hy1M : y1 ∈ Finset.univ \ D) (hy01 : y0 ≠ y1)
    (hy0_tri : inOpenTriBool (S y0) (w (Finset.univ \ {cycD.toFun 3, y0, y1})) (S (cycD.toFun 0)) (S (cycD.toFun 1)) = true)
    (hy1_tri : inOpenTriBool (S y1) (w (Finset.univ \ {cycD.toFun 3, y0, y1})) (S (cycD.toFun 1)) (S (cycD.toFun 2)) = true)
    (h_not_lr : ∀ l r : Fin n, (certifiedVertices S w).Nonempty →
      IsCCWEdge S D l r → (∀ h ∈ certifiedVertices S w, orient2D (S l) (S r) (S h) < 0) →
      (cycD.toFun 0, cycD.toFun 1) ≠ (l, r) ∧ (cycD.toFun 1, cycD.toFun 2) ≠ (l, r)) :
    let b := cycD.toFun 3
    let O_star : Finset (Fin n) := {b, y0, y1}
    IsGoodChirotopeGap P S w O_star b y0 {cycD.toFun 4, cycD.toFun 5, cycD.toFun 0} ∨
    IsGoodChirotopeGap P S w O_star y0 y1 {cycD.toFun 1} ∨
    IsGoodChirotopeGap P S w O_star y1 b {cycD.toFun 2} := by
  intro b O_star
  have hy0_notD : y0 ∉ D := (Finset.mem_sdiff.mp hy0M).2
  have hy1_notD : y1 ∉ D := (Finset.mem_sdiff.mp hy1M).2
  have h25 := mk_sec2To5Interface_general (n_ge_three_of_ccwCycle cycD) hP
  obtain ⟨oa, ob, Γ, hbr, hgap, hΓ, _⟩ := hexagon_adjacent_exits_b3 hP h25 hDB cycD hy0M hy1M hy01
    (inIntTri_exit_of_bool hP cycD hy0_notD (by decide) hy0_tri)
    (inIntTri_exit_of_bool hP cycD hy1_notD (by decide) hy1_tri)
    h_not_lr
  rcases hbr with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · refine Or.inl (isGoodChirotopeGap_of_goodAnchorPair hP hgap (fun ip hip => ⟨?_, (hΓ ip hip).1, (hΓ ip hip).2.1⟩))
    simp only [Finset.mem_insert, Finset.mem_singleton] at hip; rcases hip with rfl | rfl | rfl <;>
      exact not_mem_Ostar_of_ne cycD hy0_notD hy1_notD (by decide)
  · refine Or.inr (Or.inl (isGoodChirotopeGap_of_goodAnchorPair hP hgap (fun ip hip => ⟨?_, (hΓ ip hip).1, (hΓ ip hip).2.1⟩)))
    rw [Finset.mem_singleton] at hip; subst hip; exact not_mem_Ostar_of_ne cycD hy0_notD hy1_notD (by decide)
  · refine Or.inr (Or.inr (isGoodChirotopeGap_of_goodAnchorPair hP hgap (fun ip hip => ⟨?_, (hΓ ip hip).1, (hΓ ip hip).2.1⟩)))
    rw [Finset.mem_singleton] at hip; subst hip; exact not_mem_Ostar_of_ne cycD hy0_notD hy1_notD (by decide)

/-- **Clause `(C7)` Part 5f (`c7_hexagon_adjacent_exits_b4`, `upper_8.tex` Lemma 5.12(ii), `b = 4`)**. -/
theorem c7_hexagon_adjacent_exits_b4 {n : ℕ} {P : Set (ℝ × ℝ)}
    {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ}
    (hP : ShatteredSimplePolygon P S w)
    {D : Finset (Fin n)} (hDB : D = hullVertices S \ certifiedVertices S w)
    (cycD : CCWCycle S D 3)
    {y0 y1 : Fin n} (hy0M : y0 ∈ Finset.univ \ D) (hy1M : y1 ∈ Finset.univ \ D) (hy01 : y0 ≠ y1)
    (hy0_tri : inOpenTriBool (S y0) (w (Finset.univ \ {cycD.toFun 4, y0, y1})) (S (cycD.toFun 0)) (S (cycD.toFun 1)) = true)
    (hy1_tri : inOpenTriBool (S y1) (w (Finset.univ \ {cycD.toFun 4, y0, y1})) (S (cycD.toFun 1)) (S (cycD.toFun 2)) = true)
    (h_not_lr : ∀ l r : Fin n, (certifiedVertices S w).Nonempty →
      IsCCWEdge S D l r → (∀ h ∈ certifiedVertices S w, orient2D (S l) (S r) (S h) < 0) →
      (cycD.toFun 0, cycD.toFun 1) ≠ (l, r) ∧ (cycD.toFun 1, cycD.toFun 2) ≠ (l, r)) :
    let b := cycD.toFun 4
    let O_star : Finset (Fin n) := {b, y0, y1}
    IsGoodChirotopeGap P S w O_star b y0 {cycD.toFun 5, cycD.toFun 0} ∨
    IsGoodChirotopeGap P S w O_star y0 y1 {cycD.toFun 1} ∨
    IsGoodChirotopeGap P S w O_star y1 b {cycD.toFun 2, cycD.toFun 3} := by
  intro b O_star
  have hy0_notD : y0 ∉ D := (Finset.mem_sdiff.mp hy0M).2
  have hy1_notD : y1 ∉ D := (Finset.mem_sdiff.mp hy1M).2
  have h25 := mk_sec2To5Interface_general (n_ge_three_of_ccwCycle cycD) hP
  obtain ⟨oa, ob, Γ, hbr, hgap, hΓ, _⟩ := hexagon_adjacent_exits_b4 hP h25 hDB cycD hy0M hy1M hy01
    (inIntTri_exit_of_bool hP cycD hy0_notD (by decide) hy0_tri)
    (inIntTri_exit_of_bool hP cycD hy1_notD (by decide) hy1_tri)
    h_not_lr
  rcases hbr with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · refine Or.inl (isGoodChirotopeGap_of_goodAnchorPair hP hgap (fun ip hip => ⟨?_, (hΓ ip hip).1, (hΓ ip hip).2.1⟩))
    simp only [Finset.mem_insert, Finset.mem_singleton] at hip; rcases hip with rfl | rfl <;>
      exact not_mem_Ostar_of_ne cycD hy0_notD hy1_notD (by decide)
  · refine Or.inr (Or.inl (isGoodChirotopeGap_of_goodAnchorPair hP hgap (fun ip hip => ⟨?_, (hΓ ip hip).1, (hΓ ip hip).2.1⟩)))
    rw [Finset.mem_singleton] at hip; subst hip; exact not_mem_Ostar_of_ne cycD hy0_notD hy1_notD (by decide)
  · refine Or.inr (Or.inr (isGoodChirotopeGap_of_goodAnchorPair hP hgap (fun ip hip => ⟨?_, (hΓ ip hip).1, (hΓ ip hip).2.1⟩)))
    simp only [Finset.mem_insert, Finset.mem_singleton] at hip; rcases hip with rfl | rfl <;>
      exact not_mem_Ostar_of_ne cycD hy0_notD hy1_notD (by decide)


/-! ## 4. Complete Theorem 8.1 Bundle (`(C1)`–`(C11)`, `complete_theorem_8_1_chirotope_soundness`) -/

/-- Bundled Clause `(C7)` Source-Gap Soundness across all five source families of `upper_8.tex` Section 8. -/
structure SourceGapSoundnessBundle {n : ℕ} (P : Set (ℝ × ℝ))
    (S : Fin n → ℝ × ℝ) (w : Finset (Fin n) → ℝ × ℝ) : Prop where
  /-- Prop 5.6: Non-adjacent triple gap disjunction on `D`. -/
  nonadj_triple : ∀ {kD : ℕ} {D : Finset (Fin n)},
    D ⊆ hullVertices S \ certifiedVertices S w →
    ∀ (cycD : CCWCycle S D kD) (i1 i2 i3 : Fin (kD + 3)),
      1 < (i2 - i1).val → 1 < (i3 - i2).val → 1 < (i1 - i3).val →
      (i2 - i1).val + (i3 - i2).val + (i1 - i3).val = kD + 3 →
      let o1 := cycD.toFun i1; let o2 := cycD.toFun i2; let o3 := cycD.toFun i3
      let O_miss : Finset (Fin n) := {o1, o2, o3}
      IsGoodChirotopeGap P S w O_miss o1 o2
        (D.filter (fun p => ∃ m, cycD.toFun m = p ∧ 0 < (m - i1).val ∧ (m - i1).val < (i2 - i1).val)) ∨
      IsGoodChirotopeGap P S w O_miss o2 o3
        (D.filter (fun p => ∃ m, cycD.toFun m = p ∧ 0 < (m - i2).val ∧ (m - i2).val < (i3 - i2).val)) ∨
      IsGoodChirotopeGap P S w O_miss o3 o1
        (D.filter (fun p => ∃ m, cycD.toFun m = p ∧ 0 < (m - i3).val ∧ (m - i3).val < (i1 - i3).val))
  /-- Prop 5.5: Alternating hexagon good-target disjunction. -/
  alternating_hexagon : ∀ {C : Finset (Fin n)},
    C ⊆ hullVertices S \ certifiedVertices S w →
    ∀ (cyc : CCWCycle S C 3),
      let O_miss : Finset (Fin n) := {cyc.toFun 1, cyc.toFun 3, cyc.toFun 5}
      IsGoodChirotopeGap P S w O_miss (cyc.toFun 5) (cyc.toFun 1) {cyc.toFun 0} ∨
      IsGoodChirotopeGap P S w O_miss (cyc.toFun 1) (cyc.toFun 3) {cyc.toFun 2} ∨
      IsGoodChirotopeGap P S w O_miss (cyc.toFun 3) (cyc.toFun 5) {cyc.toFun 4}
  /-- Prop 5.8: Interior-anchor source `O* = {b', y, b}` good-gap disjunction. -/
  interior_anchor_gap : ∀ {kD : ℕ} {D : Finset (Fin n)},
    D = hullVertices S \ certifiedVertices S w →
    ∀ (cycD : CCWCycle S D kD) {y : Fin n}, y ∈ Finset.univ \ D →
    ∀ (ib' iu0 iv0 ib id_v : Fin (kD + 3)),
      iv0 = iu0 + 1 →
      0 < (iu0 - ib').val → (iu0 - ib').val < (iv0 - ib').val →
      (iv0 - ib').val < (ib - ib').val → (ib - ib').val < (id_v - ib').val →
      (0 < orient2D (S (cycD.toFun iu0)) (S (cycD.toFun iv0)) (w D) ∧
        InIntTri (w D) (S (cycD.toFun iu0)) (S (cycD.toFun iv0)) (S y) ∧
        (∀ x ∈ WitnessSet {cycD.toFun iu0, cycD.toFun iv0} ∅ w,
          InIntTri x (S (cycD.toFun iu0)) (S (cycD.toFun iv0)) (S y)) ∧
        (∀ l r : Fin n, (certifiedVertices S w).Nonempty →
          IsCCWEdge S D l r → (∀ h ∈ certifiedVertices S w, orient2D (S l) (S r) (S h) < 0) →
          (cycD.toFun iu0, cycD.toFun iv0) ≠ (l, r))) →
      let b' := cycD.toFun ib'; let u0 := cycD.toFun iu0; let v0 := cycD.toFun iv0; let b := cycD.toFun ib
      let O_star : Finset (Fin n) := {b', y, b}
      inOpenTriBool (S y) (w (Finset.univ \ O_star)) (S u0) (S v0) = true ∧
      (IsGoodChirotopeGap P S w O_star b' y
        (D.filter (fun p => ∃ m, cycD.toFun m = p ∧ 0 < (m - ib').val ∧ (m - ib').val ≤ (iu0 - ib').val)) ∨
       IsGoodChirotopeGap P S w O_star y b
        (D.filter (fun p => ∃ m, cycD.toFun m = p ∧ (iv0 - ib').val ≤ (m - ib').val ∧ (m - ib').val < (ib - ib').val)) ∨
       IsGoodChirotopeGap P S w O_star b b'
        (D.filter (fun p => ∃ m, cycD.toFun m = p ∧ 0 < (m - ib).val ∧ (m - ib).val < (ib' - ib).val)))
  /-- Lemma 5.9: Pentagon disjoint exit edges (`01` and `23`, `b = 4`). -/
  pentagon_disjoint : ∀ {D : Finset (Fin n)},
    D = hullVertices S \ certifiedVertices S w →
    ∀ (cycD : CCWCycle S D 2) {y0 y1 : Fin n},
      y0 ∈ Finset.univ \ D → y1 ∈ Finset.univ \ D → y0 ≠ y1 →
      inOpenTriBool (S y0) (w (Finset.univ \ {cycD.toFun 4, y0, y1})) (S (cycD.toFun 0)) (S (cycD.toFun 1)) = true →
      inOpenTriBool (S y1) (w (Finset.univ \ {cycD.toFun 4, y0, y1})) (S (cycD.toFun 2)) (S (cycD.toFun 3)) = true →
      (∀ l r : Fin n, (certifiedVertices S w).Nonempty → IsCCWEdge S D l r →
        (∀ h ∈ certifiedVertices S w, orient2D (S l) (S r) (S h) < 0) →
        (cycD.toFun 0, cycD.toFun 1) ≠ (l, r) ∧ (cycD.toFun 2, cycD.toFun 3) ≠ (l, r)) →
      let b := cycD.toFun 4; let O_star : Finset (Fin n) := {b, y0, y1}
      IsGoodChirotopeGap P S w O_star b y0 {cycD.toFun 0} ∨
      IsGoodChirotopeGap P S w O_star y0 y1 {cycD.toFun 1, cycD.toFun 2} ∨
      IsGoodChirotopeGap P S w O_star y1 b {cycD.toFun 3}
  /-- Lemma 5.10: Pentagon adjacent exit edges (`01` and `12`, `b = 4` and `b = 3`). -/
  pentagon_adjacent_b4 : ∀ {D : Finset (Fin n)},
    D = hullVertices S \ certifiedVertices S w →
    ∀ (cycD : CCWCycle S D 2) {y0 y1 : Fin n},
      y0 ∈ Finset.univ \ D → y1 ∈ Finset.univ \ D → y0 ≠ y1 →
      inOpenTriBool (S y0) (w (Finset.univ \ {cycD.toFun 4, y0, y1})) (S (cycD.toFun 0)) (S (cycD.toFun 1)) = true →
      inOpenTriBool (S y1) (w (Finset.univ \ {cycD.toFun 4, y0, y1})) (S (cycD.toFun 1)) (S (cycD.toFun 2)) = true →
      (∀ l r : Fin n, (certifiedVertices S w).Nonempty → IsCCWEdge S D l r →
        (∀ h ∈ certifiedVertices S w, orient2D (S l) (S r) (S h) < 0) →
        (cycD.toFun 0, cycD.toFun 1) ≠ (l, r) ∧ (cycD.toFun 1, cycD.toFun 2) ≠ (l, r)) →
      let b := cycD.toFun 4; let O_star : Finset (Fin n) := {b, y0, y1}
      IsGoodChirotopeGap P S w O_star b y0 {cycD.toFun 0} ∨
      IsGoodChirotopeGap P S w O_star y0 y1 {cycD.toFun 1} ∨
      IsGoodChirotopeGap P S w O_star y1 b {cycD.toFun 2, cycD.toFun 3}
  pentagon_adjacent_b3 : ∀ {D : Finset (Fin n)},
    D = hullVertices S \ certifiedVertices S w →
    ∀ (cycD : CCWCycle S D 2) {y0 y1 : Fin n},
      y0 ∈ Finset.univ \ D → y1 ∈ Finset.univ \ D → y0 ≠ y1 →
      inOpenTriBool (S y0) (w (Finset.univ \ {cycD.toFun 3, y0, y1})) (S (cycD.toFun 0)) (S (cycD.toFun 1)) = true →
      inOpenTriBool (S y1) (w (Finset.univ \ {cycD.toFun 3, y0, y1})) (S (cycD.toFun 1)) (S (cycD.toFun 2)) = true →
      (∀ l r : Fin n, (certifiedVertices S w).Nonempty → IsCCWEdge S D l r →
        (∀ h ∈ certifiedVertices S w, orient2D (S l) (S r) (S h) < 0) →
        (cycD.toFun 0, cycD.toFun 1) ≠ (l, r) ∧ (cycD.toFun 1, cycD.toFun 2) ≠ (l, r)) →
      let b := cycD.toFun 3; let O_star : Finset (Fin n) := {b, y0, y1}
      IsGoodChirotopeGap P S w O_star b y0 {cycD.toFun 4, cycD.toFun 0} ∨
      IsGoodChirotopeGap P S w O_star y0 y1 {cycD.toFun 1} ∨
      IsGoodChirotopeGap P S w O_star y1 b {cycD.toFun 2}
  /-- Lemma 5.11(i)–(ii): Hexagon disjoint exit edges (`23` with `b ∈ {4, 5}`, and `34` with `b = 2`). -/
  hexagon_disjoint_23_b4 : ∀ {D : Finset (Fin n)},
    D = hullVertices S \ certifiedVertices S w →
    ∀ (cycD : CCWCycle S D 3) {y0 y1 : Fin n},
      y0 ∈ Finset.univ \ D → y1 ∈ Finset.univ \ D → y0 ≠ y1 →
      inOpenTriBool (S y0) (w (Finset.univ \ {cycD.toFun 4, y0, y1})) (S (cycD.toFun 0)) (S (cycD.toFun 1)) = true →
      inOpenTriBool (S y1) (w (Finset.univ \ {cycD.toFun 4, y0, y1})) (S (cycD.toFun 2)) (S (cycD.toFun 3)) = true →
      (∀ l r : Fin n, (certifiedVertices S w).Nonempty → IsCCWEdge S D l r →
        (∀ h ∈ certifiedVertices S w, orient2D (S l) (S r) (S h) < 0) →
        (cycD.toFun 0, cycD.toFun 1) ≠ (l, r) ∧ (cycD.toFun 2, cycD.toFun 3) ≠ (l, r)) →
      let b := cycD.toFun 4; let O_star : Finset (Fin n) := {b, y0, y1}
      IsGoodChirotopeGap P S w O_star b y0 {cycD.toFun 5, cycD.toFun 0} ∨
      IsGoodChirotopeGap P S w O_star y0 y1 {cycD.toFun 1, cycD.toFun 2} ∨
      IsGoodChirotopeGap P S w O_star y1 b {cycD.toFun 3}
  hexagon_disjoint_23_b5 : ∀ {D : Finset (Fin n)},
    D = hullVertices S \ certifiedVertices S w →
    ∀ (cycD : CCWCycle S D 3) {y0 y1 : Fin n},
      y0 ∈ Finset.univ \ D → y1 ∈ Finset.univ \ D → y0 ≠ y1 →
      inOpenTriBool (S y0) (w (Finset.univ \ {cycD.toFun 5, y0, y1})) (S (cycD.toFun 0)) (S (cycD.toFun 1)) = true →
      inOpenTriBool (S y1) (w (Finset.univ \ {cycD.toFun 5, y0, y1})) (S (cycD.toFun 2)) (S (cycD.toFun 3)) = true →
      (∀ l r : Fin n, (certifiedVertices S w).Nonempty → IsCCWEdge S D l r →
        (∀ h ∈ certifiedVertices S w, orient2D (S l) (S r) (S h) < 0) →
        (cycD.toFun 0, cycD.toFun 1) ≠ (l, r) ∧ (cycD.toFun 2, cycD.toFun 3) ≠ (l, r)) →
      let b := cycD.toFun 5; let O_star : Finset (Fin n) := {b, y0, y1}
      IsGoodChirotopeGap P S w O_star b y0 {cycD.toFun 0} ∨
      IsGoodChirotopeGap P S w O_star y0 y1 {cycD.toFun 1, cycD.toFun 2} ∨
      IsGoodChirotopeGap P S w O_star y1 b {cycD.toFun 3, cycD.toFun 4}
  hexagon_disjoint_34_b2 : ∀ {D : Finset (Fin n)},
    D = hullVertices S \ certifiedVertices S w →
    ∀ (cycD : CCWCycle S D 3) {y0 y1 : Fin n},
      y0 ∈ Finset.univ \ D → y1 ∈ Finset.univ \ D → y0 ≠ y1 →
      inOpenTriBool (S y0) (w (Finset.univ \ {cycD.toFun 2, y0, y1})) (S (cycD.toFun 0)) (S (cycD.toFun 1)) = true →
      inOpenTriBool (S y1) (w (Finset.univ \ {cycD.toFun 2, y0, y1})) (S (cycD.toFun 3)) (S (cycD.toFun 4)) = true →
      (∀ l r : Fin n, (certifiedVertices S w).Nonempty → IsCCWEdge S D l r →
        (∀ h ∈ certifiedVertices S w, orient2D (S l) (S r) (S h) < 0) →
        (cycD.toFun 0, cycD.toFun 1) ≠ (l, r) ∧ (cycD.toFun 3, cycD.toFun 4) ≠ (l, r)) →
      let b := cycD.toFun 2; let O_star : Finset (Fin n) := {b, y0, y1}
      IsGoodChirotopeGap P S w O_star b y1 {cycD.toFun 3} ∨
      IsGoodChirotopeGap P S w O_star y1 y0 {cycD.toFun 4, cycD.toFun 5, cycD.toFun 0} ∨
      IsGoodChirotopeGap P S w O_star y0 b {cycD.toFun 1}
  /-- Lemma 5.12(i)–(ii): Hexagon adjacent exit edges (`01` and `12` with `b ∈ {5, 3, 4}`). -/
  hexagon_adjacent_b5 : ∀ {D : Finset (Fin n)},
    D = hullVertices S \ certifiedVertices S w →
    ∀ (cycD : CCWCycle S D 3) {y0 y1 : Fin n},
      y0 ∈ Finset.univ \ D → y1 ∈ Finset.univ \ D → y0 ≠ y1 →
      inOpenTriBool (S y0) (w (Finset.univ \ {cycD.toFun 5, y0, y1})) (S (cycD.toFun 0)) (S (cycD.toFun 1)) = true →
      inOpenTriBool (S y1) (w (Finset.univ \ {cycD.toFun 5, y0, y1})) (S (cycD.toFun 1)) (S (cycD.toFun 2)) = true →
      (∀ l r : Fin n, (certifiedVertices S w).Nonempty → IsCCWEdge S D l r →
        (∀ h ∈ certifiedVertices S w, orient2D (S l) (S r) (S h) < 0) →
        (cycD.toFun 0, cycD.toFun 1) ≠ (l, r) ∧ (cycD.toFun 1, cycD.toFun 2) ≠ (l, r)) →
      let b := cycD.toFun 5; let O_star : Finset (Fin n) := {b, y0, y1}
      IsGoodChirotopeGap P S w O_star b y0 {cycD.toFun 0} ∨
      IsGoodChirotopeGap P S w O_star y0 y1 {cycD.toFun 1} ∨
      IsGoodChirotopeGap P S w O_star y1 b {cycD.toFun 2, cycD.toFun 3, cycD.toFun 4}
  hexagon_adjacent_b3 : ∀ {D : Finset (Fin n)},
    D = hullVertices S \ certifiedVertices S w →
    ∀ (cycD : CCWCycle S D 3) {y0 y1 : Fin n},
      y0 ∈ Finset.univ \ D → y1 ∈ Finset.univ \ D → y0 ≠ y1 →
      inOpenTriBool (S y0) (w (Finset.univ \ {cycD.toFun 3, y0, y1})) (S (cycD.toFun 0)) (S (cycD.toFun 1)) = true →
      inOpenTriBool (S y1) (w (Finset.univ \ {cycD.toFun 3, y0, y1})) (S (cycD.toFun 1)) (S (cycD.toFun 2)) = true →
      (∀ l r : Fin n, (certifiedVertices S w).Nonempty → IsCCWEdge S D l r →
        (∀ h ∈ certifiedVertices S w, orient2D (S l) (S r) (S h) < 0) →
        (cycD.toFun 0, cycD.toFun 1) ≠ (l, r) ∧ (cycD.toFun 1, cycD.toFun 2) ≠ (l, r)) →
      let b := cycD.toFun 3; let O_star : Finset (Fin n) := {b, y0, y1}
      IsGoodChirotopeGap P S w O_star b y0 {cycD.toFun 4, cycD.toFun 5, cycD.toFun 0} ∨
      IsGoodChirotopeGap P S w O_star y0 y1 {cycD.toFun 1} ∨
      IsGoodChirotopeGap P S w O_star y1 b {cycD.toFun 2}
  hexagon_adjacent_b4 : ∀ {D : Finset (Fin n)},
    D = hullVertices S \ certifiedVertices S w →
    ∀ (cycD : CCWCycle S D 3) {y0 y1 : Fin n},
      y0 ∈ Finset.univ \ D → y1 ∈ Finset.univ \ D → y0 ≠ y1 →
      inOpenTriBool (S y0) (w (Finset.univ \ {cycD.toFun 4, y0, y1})) (S (cycD.toFun 0)) (S (cycD.toFun 1)) = true →
      inOpenTriBool (S y1) (w (Finset.univ \ {cycD.toFun 4, y0, y1})) (S (cycD.toFun 1)) (S (cycD.toFun 2)) = true →
      (∀ l r : Fin n, (certifiedVertices S w).Nonempty → IsCCWEdge S D l r →
        (∀ h ∈ certifiedVertices S w, orient2D (S l) (S r) (S h) < 0) →
        (cycD.toFun 0, cycD.toFun 1) ≠ (l, r) ∧ (cycD.toFun 1, cycD.toFun 2) ≠ (l, r)) →
      let b := cycD.toFun 4; let O_star : Finset (Fin n) := {b, y0, y1}
      IsGoodChirotopeGap P S w O_star b y0 {cycD.toFun 5, cycD.toFun 0} ∨
      IsGoodChirotopeGap P S w O_star y0 y1 {cycD.toFun 1} ∨
      IsGoodChirotopeGap P S w O_star y1 b {cycD.toFun 2, cycD.toFun 3}

theorem sourceGapSoundness_C7 {n : ℕ} {P : Set (ℝ × ℝ)}
    {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ}
    (hP : ShatteredSimplePolygon P S w) :
    SourceGapSoundnessBundle P S w where
  nonadj_triple := by
    intro kD D hD cycD i1 i2 i3 h12 h23 h31 hs
    exact c7_nonadj_triple_gap hP hD cycD i1 i2 i3 h12 h23 h31 hs
  alternating_hexagon := by
    intro C hC cyc
    exact c7_alternating_hexagon hP hC cyc
  interior_anchor_gap := by
    intro kD D hDB cycD y hyM ib' iu0 iv0 ib id_v hiv0 h1 h2 h3 h4 hex
    exact c7_interior_anchor hP hDB cycD hyM ib' iu0 iv0 ib id_v hiv0 h1 h2 h3 h4 hex
  pentagon_disjoint := by
    intro D hDB cycD y0 y1 hy0 hy1 hne ht0 ht1 hlr
    exact c7_pentagon_disjoint_exits hP hDB cycD hy0 hy1 hne ht0 ht1 hlr
  pentagon_adjacent_b4 := by
    intro D hDB cycD y0 y1 hy0 hy1 hne ht0 ht1 hlr
    exact c7_pentagon_adjacent_exits_b4 hP hDB cycD hy0 hy1 hne ht0 ht1 hlr
  pentagon_adjacent_b3 := by
    intro D hDB cycD y0 y1 hy0 hy1 hne ht0 ht1 hlr
    exact c7_pentagon_adjacent_exits_b3 hP hDB cycD hy0 hy1 hne ht0 ht1 hlr
  hexagon_disjoint_23_b4 := by
    intro D hDB cycD y0 y1 hy0 hy1 hne ht0 ht1 hlr
    exact c7_hexagon_disjoint_exits_23_b4 hP hDB cycD hy0 hy1 hne ht0 ht1 hlr
  hexagon_disjoint_23_b5 := by
    intro D hDB cycD y0 y1 hy0 hy1 hne ht0 ht1 hlr
    exact c7_hexagon_disjoint_exits_23_b5 hP hDB cycD hy0 hy1 hne ht0 ht1 hlr
  hexagon_disjoint_34_b2 := by
    intro D hDB cycD y0 y1 hy0 hy1 hne ht0 ht1 hlr
    exact c7_hexagon_disjoint_exits_34_b2 hP hDB cycD hy0 hy1 hne ht0 ht1 hlr
  hexagon_adjacent_b5 := by
    intro D hDB cycD y0 y1 hy0 hy1 hne ht0 ht1 hlr
    exact c7_hexagon_adjacent_exits_b5 hP hDB cycD hy0 hy1 hne ht0 ht1 hlr
  hexagon_adjacent_b3 := by
    intro D hDB cycD y0 y1 hy0 hy1 hne ht0 ht1 hlr
    exact c7_hexagon_adjacent_exits_b3 hP hDB cycD hy0 hy1 hne ht0 ht1 hlr
  hexagon_adjacent_b4 := by
    intro D hDB cycD y0 y1 hy0 hy1 hne ht0 ht1 hlr
    exact c7_hexagon_adjacent_exits_b4 hP hDB cycD hy0 hy1 hne ht0 ht1 hlr

/-- Complete Theorem 8.1 Soundness Bundle uniting all eleven clause families `(C1)`–`(C11)`
    of `upper_8.tex` Theorem 8.1 (`thmlab{chirotope-sound}`). -/
structure CompleteTheorem81Bundle {n k : ℕ} (P : Set (ℝ × ℝ))
    (S : Fin n → ℝ × ℝ) (w : Finset (Fin n) → ℝ × ℝ)
    (W₀ : Fin k ↪ Finset (Fin n)) : Prop where
  /-- Clauses `(C1)`, `(C2)`, `(C6)`, `(C8)`, `(C9)`, `(C10)`, `(C11)` and `(G1)`. -/
  extended : ExtendedSoundChirotopeBundle P S w W₀
  /-- Clause `(C3)`: Carathéodory 4-subset interior triangle extraction on any non-convex subset `F`. -/
  c3_caratheodory : ∀ (F : Finset (Fin n)),
    (¬ ∀ i ∈ F, S i ∉ convexHull ℝ (((F.erase i).image S : Finset (ℝ × ℝ)) : Set (ℝ × ℝ))) →
    ∃ x ∈ F, ∃ a ∈ F, ∃ b ∈ F, ∃ c ∈ F,
      x ≠ a ∧ x ≠ b ∧ x ≠ c ∧ a ≠ b ∧ b ≠ c ∧ a ≠ c ∧
      inOpenTriBool (S x) (S a) (S b) (S c) = true
  /-- Clause `(C4)`: Non-certified hull-vertex obstruction `k ∉ int tri(w Tw, S s₁, S s₂)`. -/
  c4_obstruction : 3 ≤ n → ∀ {k' s₁ s₂ : Fin n} {Tw : Finset (Fin n)},
    k' ∈ PolygonCore.hullVertices S \ PolygonCore.certifiedSet P S w →
    k' ∉ Tw → s₁ ∈ Tw → s₂ ∈ Tw → s₁ ≠ s₂ →
    inOpenTriBool (S k') (w Tw) (S s₁) (S s₂) = false
  /-- Clause `(C5)` Part 1: Exit-edge cone containment on `W({d_i, d_{i+1}})`. -/
  c5_exit_cone : 3 ≤ n → 3 ≤ (PolygonCore.hullVertices S \ PolygonCore.certifiedSet P S w).card →
    ∀ (dc : PolygonCore.CyclicSubsetBoundary S (PolygonCore.hullVertices S \ PolygonCore.certifiedSet P S w))
    {y : Fin n}, y ∈ PolygonCore.interiorPoints S ∪ PolygonCore.certifiedSet P S w →
    ∃ i : Fin (dc.m + 3),
      inOpenTriBool (S y) (w (PolygonCore.hullVertices S \ PolygonCore.certifiedSet P S w))
        (S (dc.p_idx i)) (S (dc.p_idx (i + 1))) = true ∧
      ∀ Tw : Finset (Fin n), dc.p_idx i ∈ Tw → dc.p_idx (i + 1) ∈ Tw →
        inOpenTriBool (S y) (w Tw) (S (dc.p_idx i)) (S (dc.p_idx (i + 1))) = true
  /-- Clause `(C5)` Part 2: Convex wedge separation on `W({u, v})`. -/
  c5_wedge_sep : ∀ {y u v : Fin n}, y ≠ u → y ≠ v → u ≠ v →
    ∀ {T₁ T₂ Tm : Finset (Fin n)}, T₁ ≠ T₂ →
      u ∈ T₁ → v ∈ T₁ → y ∈ T₁ →
      u ∈ T₂ → v ∈ T₂ → y ∈ T₂ →
      u ∈ Tm → v ∈ Tm → y ∉ Tm →
      inOpenTriBool (S y) (w T₁) (S u) (S v) = true →
      inOpenTriBool (S y) (w T₂) (S u) (S v) = true →
      ∀ s : Bool,
        ¬ (orientSign (S y) (w T₁) (w T₂) = s ∧
           orientSign (S y) (w T₁) (w Tm) = s ∧
           orientSign (S y) (w Tm) (w T₂) = s)
  /-- Clause `(C7)`: Source-gap disjunctions across all five source families. -/
  c7_source_gaps : SourceGapSoundnessBundle P S w

/-- **Complete Theorem 8.1 (`complete_theorem_8_1_chirotope_soundness`)**:
    Every `ShatteredSimplePolygon P S w` and finite witness subcollection `W₀` satisfies all
    eleven clause families `(C1)`–`(C11)` of Theorem 8.1 in pure `orientSign` form! -/
theorem complete_theorem_8_1_chirotope_soundness {n k : ℕ} {P : Set (ℝ × ℝ)}
    {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ}
    (hP : ShatteredSimplePolygon P S w) (W₀ : Fin k ↪ Finset (Fin n)) :
    CompleteTheorem81Bundle P S w W₀ where
  extended := extended_sound_chirotope_reduction hP W₀
  c3_caratheodory := by
    intro F hnc; exact caratheodory_four_subset_C3 hP F hnc
  c4_obstruction := by
    intro hn k' s₁ s₂ Tw hkD hkm hs1 hs2 hs12
    exact non_certified_obstruction_clause_C4 hP hn hkD hkm hs1 hs2 hs12
  c5_exit_cone := by
    intro hn hD3 dc y hyM
    exact exit_edge_cone_clause_C5 hP hn hD3 dc hyM
  c5_wedge_sep := by
    intro y u v hyu hyv huv T₁ T₂ Tm hT12 hu1 hv1 hy1 hu2 hv2 hy2 hum hvm hym ht1 ht2 s
    exact wedge_sep_clause_C5 hP hyu hyv huv hT12 hu1 hv1 hy1 hu2 hv2 hy2 hum hvm hym ht1 ht2 s
  c7_source_gaps := sourceGapSoundness_C7 hP


/-! ## 5. Exhaustive Structural Case-Split Theorems (`|B| ≤ 6`, `|M| ≤ 5`, `|B| ≥ 3`) -/

/-- `VC-dim_convex(P) ≤ 6`: `P` shatters no 7-point set in strictly convex position (`A = ∅`). -/
def NoConvexSevenShattered (P : Set (ℝ × ℝ)) : Prop :=
  ∀ (S₇ : Fin 7 → ℝ × ℝ) (w₇ : Finset (Fin 7) → ℝ × ℝ),
    ShatteredSimplePolygon P S₇ w₇ → interiorPoints S₇ = ∅ → False

section PartitionIdentities

variable {n : ℕ} {P : Set (ℝ × ℝ)} {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ}

lemma card_B_eq_D_add_H :
    let B := hullVertices S
    let H := PolygonCore.certifiedSet P S w
    let D := B \ H
    B.card = D.card + H.card := by
  intro B H D
  have hHB : H ⊆ B := by
    dsimp [H, PolygonCore.certifiedSet]; rw [hullVertices_eq]; exact Finset.filter_subset _ _
  have hdisj : Disjoint D H := disjoint_sdiff_self_left
  have hunion : D ∪ H = B := Finset.sdiff_union_of_subset hHB
  rw [← hunion, Finset.card_union_of_disjoint hdisj]

lemma card_M_eq_A_add_H :
    let H := PolygonCore.certifiedSet P S w
    let A := interiorPoints S
    let M := A ∪ H
    Disjoint A H ∧ M.card = A.card + H.card := by
  intro H A M
  have hHB : H ⊆ hullVertices S := by
    dsimp [H, PolygonCore.certifiedSet]; rw [hullVertices_eq]; exact Finset.filter_subset _ _
  have hdisj : Disjoint A H := by
    rw [Finset.disjoint_left]
    intro x hxA hxH
    exact (Finset.mem_sdiff.mp hxA).2 (hHB hxH)
  exact ⟨hdisj, Finset.card_union_of_disjoint hdisj⟩

lemma M_eq_univ_sdiff_D :
    let B := hullVertices S
    let H := PolygonCore.certifiedSet P S w
    let D := B \ H
    let A := interiorPoints S
    A ∪ H = Finset.univ \ D := by
  intro B H D A
  have hHB : H ⊆ B := by
    dsimp [H, PolygonCore.certifiedSet]; rw [hullVertices_eq]; exact Finset.filter_subset _ _
  ext x
  simp only [A, interiorPoints, D, B, Finset.mem_union, Finset.mem_sdiff, Finset.mem_univ, true_and]
  constructor
  · rintro (hxA | hxH)
    · exact fun ⟨hxB, _⟩ => hxA hxB
    · exact fun ⟨_, hxNH⟩ => hxNH hxH
  · intro hx
    by_cases hxB : x ∈ hullVertices S
    · exact Or.inr (by by_contra hxH; exact hx ⟨hxB, hxH⟩)
    · exact Or.inl hxB

lemma card_D_add_M_eq (S : Fin n → ℝ × ℝ) (w : Finset (Fin n) → ℝ × ℝ) (P : Set (ℝ × ℝ)) :
    let B := hullVertices S
    let H := PolygonCore.certifiedSet P S w
    let D := B \ H
    let M := interiorPoints S ∪ H
    D.card + M.card = n := by
  intro B H D M
  have hM : M = Finset.univ \ D := M_eq_univ_sdiff_D
  rw [hM]
  have hsub : D ⊆ Finset.univ := Finset.subset_univ D
  have hunion : D ∪ (Finset.univ \ D) = Finset.univ := Finset.union_sdiff_of_subset hsub
  have hdisj : Disjoint D (Finset.univ \ D) := disjoint_sdiff_self_right
  have hc := Finset.card_union_of_disjoint hdisj
  rw [hunion, Finset.card_univ, Fintype.card_fin] at hc
  exact hc.symm

lemma card_B_ge_three (hn : 3 ≤ n) (hP : ShatteredSimplePolygon P S w) :
    3 ≤ (hullVertices S).card := by
  rw [← hullVertices_eq]; exact PolygonCore.hullVertices_card_ge_three hn hP

lemma card_M_le_five (hn : 3 ≤ n) (hP : ShatteredSimplePolygon P S w) :
    (interiorPoints S ∪ PolygonCore.certifiedSet P S w).card ≤ 5 := by
  have h25 := mk_sec2To5Interface_general hn hP
  have hle := M_card_le_five h25
  rwa [certifiedVertices_eq_certifiedSet hn hP, ← M_eq_univ_sdiff_D] at hle

/-- **Theorem 7.2 (`upper9_structural_bounds`, `upper_8.tex` Theorem `upper9-struct`)**:
    For every `ShatteredSimplePolygon P S w` with `3 ≤ n`:
    `|D| ≤ 7`, `|M| ≤ 5`, `|D| = 7 → |M| ≤ 2`, and `|D| = 6 → |M| ≤ 3`. -/
theorem upper9_structural_bounds (hn : 3 ≤ n) (hP : ShatteredSimplePolygon P S w) :
    let D := hullVertices S \ PolygonCore.certifiedSet P S w
    let M := interiorPoints S ∪ PolygonCore.certifiedSet P S w
    D.card ≤ 7 ∧ M.card ≤ 5 ∧ (D.card = 7 → M.card ≤ 2) ∧ (D.card = 6 → M.card ≤ 3) := by
  intro D M
  have h25 := mk_sec2To5Interface_general hn hP
  have hc_eq := certifiedVertices_eq_certifiedSet hn hP
  have hD_eq : hullVertices S \ certifiedVertices S w = D := by rw [hc_eq]
  have hM_eq : Finset.univ \ (hullVertices S \ certifiedVertices S w) = M := by
    rw [hc_eq, ← M_eq_univ_sdiff_D]
  refine ⟨?_, card_M_le_five hn hP, ?_, ?_⟩
  · have h := card_D_le_seven hP h25; rwa [hD_eq] at h
  · intro h7; have h := card_D_seven_M_le_two hP h25 (by rwa [hD_eq]); rwa [hM_eq] at h
  · intro h6; have h := card_D_six_M_le_three hP h25 (by rwa [hD_eq]); rwa [hM_eq] at h

end PartitionIdentities

/-- Restricting a shattered set to a subset of `hullVertices S` yields a shattered set in strictly
    convex position (`interiorPoints = ∅`). -/
private lemma interiorPoints_comp_eq_empty_of_subset_hull {n m : ℕ}
    {S : Fin n → ℝ × ℝ} {ι : Fin m ↪ Fin n}
    (hsub : ∀ i : Fin m, ι i ∈ hullVertices S) :
    interiorPoints (S ∘ ι) = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro i hi
  have hi_notB : i ∉ hullVertices (S ∘ ι) := (Finset.mem_sdiff.mp hi).2
  have hi_hull : (S ∘ ι) i ∈ convexHull ℝ (((Finset.univ.erase i).image (S ∘ ι)) : Set (ℝ × ℝ)) := by
    by_contra hnot
    exact hi_notB (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hnot⟩)
  have himg_sub : (((Finset.univ.erase i).image (S ∘ ι)) : Set (ℝ × ℝ)) ⊆
      (((Finset.univ.erase (ι i)).image S) : Set (ℝ × ℝ)) := by
    intro p hp
    rcases Finset.mem_image.mp hp with ⟨j, hj, rfl⟩
    exact Finset.mem_image.mpr ⟨ι j,
      Finset.mem_erase.mpr ⟨ι.injective.ne (Finset.mem_erase.mp hj).1, Finset.mem_univ _⟩, rfl⟩
  exact (Finset.mem_filter.mp (hsub i)).2 (convexHull_mono himg_sub hi_hull)

/-- **Hereditary `|B| ≤ 6` for `|S| = 9` via `NewEnclosure.hereditary_shattered_subset`**:
    Under `NoConvexSevenShattered P`, every 9-point shattered set has `(hullVertices S).card ≤ 6`. -/
theorem hullVertices_card_le_six_fin9 {P : Set (ℝ × ℝ)}
    {S : Fin 9 → ℝ × ℝ} {w : Finset (Fin 9) → ℝ × ℝ}
    (hP : ShatteredSimplePolygon P S w) (hconv6 : NoConvexSevenShattered P) :
    (hullVertices S).card ≤ 6 := by
  by_contra hgt
  obtain ⟨S₇, hS₇_sub, hS₇_card⟩ := Finset.exists_subset_card_eq (by omega : 7 ≤ (hullVertices S).card)
  obtain ⟨ι, hι_img, hP₇⟩ := NewEnclosure.hereditary_shattered_subset hP S₇ hS₇_card
  have hsub : ∀ i : Fin 7, ι i ∈ hullVertices S := fun i =>
    hS₇_sub (hι_img ▸ Finset.mem_image_of_mem ι (Finset.mem_univ i))
  exact hconv6 (S ∘ ι) _ hP₇ (interiorPoints_comp_eq_empty_of_subset_hull hsub)

/-- **General Hereditary `|B| ≤ 6` for arbitrary `n` via `NewEnclosure.hereditary_shattered_emb`**. -/
theorem hullVertices_card_le_six_of_no_convex7 {n : ℕ} {P : Set (ℝ × ℝ)}
    {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ}
    (hP : ShatteredSimplePolygon P S w) (hconv6 : NoConvexSevenShattered P) :
    (hullVertices S).card ≤ 6 := by
  by_contra hgt
  obtain ⟨S₇, hS₇_sub, hS₇_card⟩ := Finset.exists_subset_card_eq (by omega : 7 ≤ (hullVertices S).card)
  let e : S₇ ≃ Fin 7 := S₇.equivFinOfCardEq hS₇_card
  let ι : Fin 7 ↪ Fin n := ⟨fun i => (e.symm i).1, fun i j h => e.symm.injective (Subtype.ext h)⟩
  have hP₇ := NewEnclosure.hereditary_shattered_emb hP ι
  have hsub : ∀ i : Fin 7, ι i ∈ hullVertices S := fun i => hS₇_sub (e.symm i).2
  exact hconv6 (S ∘ ι) _ hP₇ (interiorPoints_comp_eq_empty_of_subset_hull hsub)

/-- **Hereditary Clause `(C3)` on Every 7-Subset (`c3_hereditary_seven_subset`)**:
    Under `NoConvexSevenShattered P`, every 7-element subset `S₇ ⊆ Fin n` contains four distinct
    indices `x, a, b, c ∈ S₇` with `inOpenTriBool (S x) (S a) (S b) (S c) = true`. -/
theorem c3_hereditary_seven_subset {n : ℕ} {P : Set (ℝ × ℝ)}
    {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ}
    (hP : ShatteredSimplePolygon P S w) (hconv6 : NoConvexSevenShattered P)
    (S₇ : Finset (Fin n)) (hcard : S₇.card = 7) :
    ∃ x ∈ S₇, ∃ a ∈ S₇, ∃ b ∈ S₇, ∃ c ∈ S₇,
      x ≠ a ∧ x ≠ b ∧ x ≠ c ∧ a ≠ b ∧ b ≠ c ∧ a ≠ c ∧
      inOpenTriBool (S x) (S a) (S b) (S c) = true := by
  refine caratheodory_four_subset_C3 hP S₇ (fun hconv => ?_)
  let e : S₇ ≃ Fin 7 := S₇.equivFinOfCardEq hcard
  let ι : Fin 7 ↪ Fin n := ⟨fun i => (e.symm i).1, fun i j h => e.symm.injective (Subtype.ext h)⟩
  have hP₇ := NewEnclosure.hereditary_shattered_emb hP ι
  have hA_empty : interiorPoints (S ∘ ι) = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro i hi
    have hi_notB : i ∉ hullVertices (S ∘ ι) := (Finset.mem_sdiff.mp hi).2
    have hi_hull : (S ∘ ι) i ∈ convexHull ℝ (((Finset.univ.erase i).image (S ∘ ι)) : Set (ℝ × ℝ)) := by
      by_contra hnot; exact hi_notB (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hnot⟩)
    have himg_sub : (((Finset.univ.erase i).image (S ∘ ι)) : Set (ℝ × ℝ)) ⊆
        (((S₇.erase (ι i)).image S : Finset (ℝ × ℝ)) : Set (ℝ × ℝ)) := by
      intro p hp; rcases Finset.mem_image.mp hp with ⟨j, hj, rfl⟩
      exact Finset.mem_image.mpr ⟨ι j,
        Finset.mem_erase.mpr ⟨ι.injective.ne (Finset.mem_erase.mp hj).1, (e.symm j).2⟩, rfl⟩
    exact hconv (ι i) (e.symm i).2 (convexHull_mono himg_sub hi_hull)
  exact hconv6 (S ∘ ι) _ hP₇ hA_empty

/-- **Case-Split Theorem 1 (`case_split_convex_seven`, `|S| = 7` with `A = ∅`, for `Convex = 6`)**:
    For any 7-point shattered set in strictly convex position (`interiorPoints S = ∅`),
    `|H| ∈ {0, 1, 2, 3, 4, 5}`, `|D| = 7 - |H| ≥ 2`, and
    `(|D|, |H|) ∈ {(7, 0), (6, 1), (5, 2), (4, 3), (3, 4), (2, 5)}`. -/
theorem case_split_convex_seven {P : Set (ℝ × ℝ)}
    {S : Fin 7 → ℝ × ℝ} {w : Finset (Fin 7) → ℝ × ℝ}
    (hP : ShatteredSimplePolygon P S w) (hA : interiorPoints S = ∅) :
    let H := PolygonCore.certifiedSet P S w
    let D := hullVertices S \ H
    H.card ∈ ({0, 1, 2, 3, 4, 5} : Finset ℕ) ∧
    D.card = 7 - H.card ∧
    2 ≤ D.card ∧
    (D.card, H.card) ∈ ({(7, 0), (6, 1), (5, 2), (4, 3), (3, 4), (2, 5)} : Finset (ℕ × ℕ)) := by
  intro H D
  have hM5 : (interiorPoints S ∪ H).card ≤ 5 := card_M_le_five (by decide) hP
  have hH5 : H.card ≤ 5 := by simpa [hA] using hM5
  have hDM : D.card + (interiorPoints S ∪ H).card = 7 := card_D_add_M_eq S w P
  have hDH : D.card + H.card = 7 := by simpa [hA] using hDM
  refine ⟨?_, by omega, by omega, ?_⟩
  · have : H.card = 0 ∨ H.card = 1 ∨ H.card = 2 ∨ H.card = 3 ∨ H.card = 4 ∨ H.card = 5 := by omega
    rcases this with h | h | h | h | h | h <;> simp [h]
  · have : H.card = 0 ∨ H.card = 1 ∨ H.card = 2 ∨ H.card = 3 ∨ H.card = 4 ∨ H.card = 5 := by omega
    rcases this with h | h | h | h | h | h
    · have hd : D.card = 7 := by omega
      simp [h, hd]
    · have hd : D.card = 6 := by omega
      simp [h, hd]
    · have hd : D.card = 5 := by omega
      simp [h, hd]
    · have hd : D.card = 4 := by omega
      simp [h, hd]
    · have hd : D.card = 3 := by omega
      simp [h, hd]
    · have hd : D.card = 2 := by omega
      simp [h, hd]

/-- **Case-Split Theorem 2 (`case_split_nine_ub8`, `|S| = 9`, for `Upper Bound ≤ 8`)**:
    From `ShatteredSimplePolygon P S w` (`|S| = 9`) and `|B| ≤ 6` (proved from `NoConvexSevenShattered P`
    via `hereditary_shattered_subset`):
    - `(7, 2)` is ruled out (`¬ (|D| = 7 ∧ |M| = 2)`),
    - `(|D|, |M|) ∈ {(6, 3), (5, 4), (4, 5)}`,
    - `|H| = 0` on `(6, 3)`, `|H| ∈ {0, 1}` on `(5, 4)`, and `|H| ∈ {0, 1, 2}` on `(4, 5)`. -/
theorem case_split_nine_ub8 {P : Set (ℝ × ℝ)}
    {S : Fin 9 → ℝ × ℝ} {w : Finset (Fin 9) → ℝ × ℝ}
    (hP : ShatteredSimplePolygon P S w) (hB6 : (hullVertices S).card ≤ 6) :
    let B := hullVertices S
    let H := PolygonCore.certifiedSet P S w
    let D := B \ H
    let A := interiorPoints S
    let M := A ∪ H
    3 ≤ B.card ∧ B.card ≤ 6 ∧ ¬ (D.card = 7 ∧ M.card = 2) ∧
    (D.card, M.card) ∈ ({(6, 3), (5, 4), (4, 5)} : Finset (ℕ × ℕ)) ∧
    ((D.card = 6 ∧ M.card = 3 ∧ H.card = 0 ∧ A.card = 3) ∨
     (D.card = 5 ∧ M.card = 4 ∧ H.card ∈ ({0, 1} : Finset ℕ) ∧ A.card = 4 - H.card) ∨
     (D.card = 4 ∧ M.card = 5 ∧ H.card ∈ ({0, 1, 2} : Finset ℕ) ∧ A.card = 5 - H.card)) := by
  intro B H D A M
  have hB6' : B.card ≤ 6 := hB6
  have hB3 : 3 ≤ B.card := card_B_ge_three (by decide) hP
  have hM5 : M.card ≤ 5 := card_M_le_five (by decide) hP
  have hBDH : B.card = D.card + H.card := card_B_eq_D_add_H
  have hMAH : M.card = A.card + H.card := card_M_eq_A_add_H.2
  have hDM9 : D.card + M.card = 9 := card_D_add_M_eq S w P
  have hno72 : ¬ (D.card = 7 ∧ M.card = 2) := by omega
  have hD_cases : D.card = 6 ∨ D.card = 5 ∨ D.card = 4 := by omega
  refine ⟨hB3, hB6', hno72, ?_, ?_⟩
  · rcases hD_cases with hd | hd | hd
    · have hm : M.card = 3 := by omega
      simp [hd, hm]
    · have hm : M.card = 4 := by omega
      simp [hd, hm]
    · have hm : M.card = 5 := by omega
      simp [hd, hm]
  · rcases hD_cases with hd | hd | hd
    · left; exact ⟨hd, by omega, by omega, by omega⟩
    · right; left
      have hH : H.card = 0 ∨ H.card = 1 := by omega
      refine ⟨hd, by omega, ?_, by omega⟩
      rcases hH with hh | hh <;> simp [hh]
    · right; right
      have hH : H.card = 0 ∨ H.card = 1 ∨ H.card = 2 := by omega
      refine ⟨hd, by omega, ?_, by omega⟩
      rcases hH with hh | hh | hh <;> simp [hh]

theorem case_split_nine_ub8_of_no_convex7 {P : Set (ℝ × ℝ)}
    {S : Fin 9 → ℝ × ℝ} {w : Finset (Fin 9) → ℝ × ℝ}
    (hP : ShatteredSimplePolygon P S w) (hconv6 : NoConvexSevenShattered P) :
    let B := hullVertices S
    let H := PolygonCore.certifiedSet P S w
    let D := B \ H
    let A := interiorPoints S
    let M := A ∪ H
    3 ≤ B.card ∧ B.card ≤ 6 ∧ ¬ (D.card = 7 ∧ M.card = 2) ∧
    (D.card, M.card) ∈ ({(6, 3), (5, 4), (4, 5)} : Finset (ℕ × ℕ)) ∧
    ((D.card = 6 ∧ M.card = 3 ∧ H.card = 0 ∧ A.card = 3) ∨
     (D.card = 5 ∧ M.card = 4 ∧ H.card ∈ ({0, 1} : Finset ℕ) ∧ A.card = 4 - H.card) ∨
     (D.card = 4 ∧ M.card = 5 ∧ H.card ∈ ({0, 1, 2} : Finset ℕ) ∧ A.card = 5 - H.card)) :=
  case_split_nine_ub8 hP (hullVertices_card_le_six_fin9 hP hconv6)

/-- **Case-Split Theorem 3 (`case_split_eight_ub7`, `|S| = 8`, for `Upper Bound ≤ 7`)**:
    From `ShatteredSimplePolygon P S w` (`|S| = 8`) and `|B| ≤ 6`:
    `(|D|, |M|) ∈ {(6, 2), (5, 3), (4, 4), (3, 5)}` with exact `|H|` ranges
    `{0}`, `{0, 1}`, `{0, 1, 2}`, `{0, 1, 2, 3}`. -/
theorem case_split_eight_ub7 {P : Set (ℝ × ℝ)}
    {S : Fin 8 → ℝ × ℝ} {w : Finset (Fin 8) → ℝ × ℝ}
    (hP : ShatteredSimplePolygon P S w) (hB6 : (hullVertices S).card ≤ 6) :
    let B := hullVertices S
    let H := PolygonCore.certifiedSet P S w
    let D := B \ H
    let A := interiorPoints S
    let M := A ∪ H
    3 ≤ B.card ∧ B.card ≤ 6 ∧
    (D.card, M.card) ∈ ({(6, 2), (5, 3), (4, 4), (3, 5)} : Finset (ℕ × ℕ)) ∧
    ((D.card = 6 ∧ M.card = 2 ∧ H.card ∈ ({0} : Finset ℕ) ∧ A.card = 2) ∨
     (D.card = 5 ∧ M.card = 3 ∧ H.card ∈ ({0, 1} : Finset ℕ) ∧ A.card = 3 - H.card) ∨
     (D.card = 4 ∧ M.card = 4 ∧ H.card ∈ ({0, 1, 2} : Finset ℕ) ∧ A.card = 4 - H.card) ∨
     (D.card = 3 ∧ M.card = 5 ∧ H.card ∈ ({0, 1, 2, 3} : Finset ℕ) ∧ A.card = 5 - H.card)) := by
  intro B H D A M
  have hB6' : B.card ≤ 6 := hB6
  have hB3 : 3 ≤ B.card := card_B_ge_three (by decide) hP
  have hM5 : M.card ≤ 5 := card_M_le_five (by decide) hP
  have hBDH : B.card = D.card + H.card := card_B_eq_D_add_H
  have hMAH : M.card = A.card + H.card := card_M_eq_A_add_H.2
  have hDM8 : D.card + M.card = 8 := card_D_add_M_eq S w P
  have hD_cases : D.card = 6 ∨ D.card = 5 ∨ D.card = 4 ∨ D.card = 3 := by omega
  refine ⟨hB3, hB6', ?_, ?_⟩
  · rcases hD_cases with hd | hd | hd | hd
    · have hm : M.card = 2 := by omega
      simp [hd, hm]
    · have hm : M.card = 3 := by omega
      simp [hd, hm]
    · have hm : M.card = 4 := by omega
      simp [hd, hm]
    · have hm : M.card = 5 := by omega
      simp [hd, hm]
  · rcases hD_cases with hd | hd | hd | hd
    · left; have hh : H.card = 0 := by omega
      exact ⟨hd, by omega, by simp [hh], by omega⟩
    · right; left
      have hH : H.card = 0 ∨ H.card = 1 := by omega
      refine ⟨hd, by omega, ?_, by omega⟩
      rcases hH with hh | hh <;> simp [hh]
    · right; right; left
      have hH : H.card = 0 ∨ H.card = 1 ∨ H.card = 2 := by omega
      refine ⟨hd, by omega, ?_, by omega⟩
      rcases hH with hh | hh | hh <;> simp [hh]
    · right; right; right
      have hH : H.card = 0 ∨ H.card = 1 ∨ H.card = 2 ∨ H.card = 3 := by omega
      refine ⟨hd, by omega, ?_, by omega⟩
      rcases hH with hh | hh | hh | hh <;> simp [hh]

theorem case_split_eight_ub7_of_no_convex7 {P : Set (ℝ × ℝ)}
    {S : Fin 8 → ℝ × ℝ} {w : Finset (Fin 8) → ℝ × ℝ}
    (hP : ShatteredSimplePolygon P S w) (hconv6 : NoConvexSevenShattered P) :
    let B := hullVertices S
    let H := PolygonCore.certifiedSet P S w
    let D := B \ H
    let A := interiorPoints S
    let M := A ∪ H
    3 ≤ B.card ∧ B.card ≤ 6 ∧
    (D.card, M.card) ∈ ({(6, 2), (5, 3), (4, 4), (3, 5)} : Finset (ℕ × ℕ)) ∧
    ((D.card = 6 ∧ M.card = 2 ∧ H.card ∈ ({0} : Finset ℕ) ∧ A.card = 2) ∨
     (D.card = 5 ∧ M.card = 3 ∧ H.card ∈ ({0, 1} : Finset ℕ) ∧ A.card = 3 - H.card) ∨
     (D.card = 4 ∧ M.card = 4 ∧ H.card ∈ ({0, 1, 2} : Finset ℕ) ∧ A.card = 4 - H.card) ∨
     (D.card = 3 ∧ M.card = 5 ∧ H.card ∈ ({0, 1, 2, 3} : Finset ℕ) ∧ A.card = 5 - H.card)) :=
  case_split_eight_ub7 hP (hullVertices_card_le_six_of_no_convex7 hP hconv6)

/-- **Case-Split Theorem 4 (`case_split_seven_ub6`, `|S| = 7`, for `Upper Bound ≤ 6`)**:
    From `ShatteredSimplePolygon P S w` (`|S| = 7`) and `|B| ≤ 6` (with `3 ≤ |B|`):
    `(|D|, |M|) ∈ {(6, 1), (5, 2), (4, 3), (3, 4), (2, 5)}` with the exact `|H|` ranges
    `{0}`, `{0, 1}`, `{0, 1, 2}`, `{0, 1, 2, 3}`, and `{1, 2, 3, 4}`! -/
theorem case_split_seven_ub6 {P : Set (ℝ × ℝ)}
    {S : Fin 7 → ℝ × ℝ} {w : Finset (Fin 7) → ℝ × ℝ}
    (hP : ShatteredSimplePolygon P S w) (hB6 : (hullVertices S).card ≤ 6) :
    let B := hullVertices S
    let H := PolygonCore.certifiedSet P S w
    let D := B \ H
    let A := interiorPoints S
    let M := A ∪ H
    3 ≤ B.card ∧ B.card ≤ 6 ∧
    (D.card, M.card) ∈ ({(6, 1), (5, 2), (4, 3), (3, 4), (2, 5)} : Finset (ℕ × ℕ)) ∧
    ((D.card = 6 ∧ M.card = 1 ∧ H.card ∈ ({0} : Finset ℕ) ∧ A.card = 1) ∨
     (D.card = 5 ∧ M.card = 2 ∧ H.card ∈ ({0, 1} : Finset ℕ) ∧ A.card = 2 - H.card) ∨
     (D.card = 4 ∧ M.card = 3 ∧ H.card ∈ ({0, 1, 2} : Finset ℕ) ∧ A.card = 3 - H.card) ∨
     (D.card = 3 ∧ M.card = 4 ∧ H.card ∈ ({0, 1, 2, 3} : Finset ℕ) ∧ A.card = 4 - H.card) ∨
     (D.card = 2 ∧ M.card = 5 ∧ H.card ∈ ({1, 2, 3, 4} : Finset ℕ) ∧ A.card = 5 - H.card)) := by
  intro B H D A M
  have hB6' : B.card ≤ 6 := hB6
  have hB3 : 3 ≤ B.card := card_B_ge_three (by decide) hP
  have hM5 : M.card ≤ 5 := card_M_le_five (by decide) hP
  have hBDH : B.card = D.card + H.card := card_B_eq_D_add_H
  have hMAH : M.card = A.card + H.card := card_M_eq_A_add_H.2
  have hDM7 : D.card + M.card = 7 := card_D_add_M_eq S w P
  have hD_cases : D.card = 6 ∨ D.card = 5 ∨ D.card = 4 ∨ D.card = 3 ∨ D.card = 2 := by omega
  refine ⟨hB3, hB6', ?_, ?_⟩
  · rcases hD_cases with hd | hd | hd | hd | hd
    · have hm : M.card = 1 := by omega
      simp [hd, hm]
    · have hm : M.card = 2 := by omega
      simp [hd, hm]
    · have hm : M.card = 3 := by omega
      simp [hd, hm]
    · have hm : M.card = 4 := by omega
      simp [hd, hm]
    · have hm : M.card = 5 := by omega
      simp [hd, hm]
  · rcases hD_cases with hd | hd | hd | hd | hd
    · left; have hh : H.card = 0 := by omega
      exact ⟨hd, by omega, by simp [hh], by omega⟩
    · right; left
      have hH : H.card = 0 ∨ H.card = 1 := by omega
      refine ⟨hd, by omega, ?_, by omega⟩
      rcases hH with hh | hh <;> simp [hh]
    · right; right; left
      have hH : H.card = 0 ∨ H.card = 1 ∨ H.card = 2 := by omega
      refine ⟨hd, by omega, ?_, by omega⟩
      rcases hH with hh | hh | hh <;> simp [hh]
    · right; right; right; left
      have hH : H.card = 0 ∨ H.card = 1 ∨ H.card = 2 ∨ H.card = 3 := by omega
      refine ⟨hd, by omega, ?_, by omega⟩
      rcases hH with hh | hh | hh | hh <;> simp [hh]
    · right; right; right; right
      -- Here `3 ≤ B.card = 2 + H.card ≤ 6` forces `1 ≤ H.card ≤ 4`!
      have hH : H.card = 1 ∨ H.card = 2 ∨ H.card = 3 ∨ H.card = 4 := by omega
      refine ⟨hd, by omega, ?_, by omega⟩
      rcases hH with hh | hh | hh | hh <;> simp [hh]

theorem case_split_seven_ub6_of_no_convex7 {P : Set (ℝ × ℝ)}
    {S : Fin 7 → ℝ × ℝ} {w : Finset (Fin 7) → ℝ × ℝ}
    (hP : ShatteredSimplePolygon P S w) (hconv6 : NoConvexSevenShattered P) :
    let B := hullVertices S
    let H := PolygonCore.certifiedSet P S w
    let D := B \ H
    let A := interiorPoints S
    let M := A ∪ H
    3 ≤ B.card ∧ B.card ≤ 6 ∧
    (D.card, M.card) ∈ ({(6, 1), (5, 2), (4, 3), (3, 4), (2, 5)} : Finset (ℕ × ℕ)) ∧
    ((D.card = 6 ∧ M.card = 1 ∧ H.card ∈ ({0} : Finset ℕ) ∧ A.card = 1) ∨
     (D.card = 5 ∧ M.card = 2 ∧ H.card ∈ ({0, 1} : Finset ℕ) ∧ A.card = 2 - H.card) ∨
     (D.card = 4 ∧ M.card = 3 ∧ H.card ∈ ({0, 1, 2} : Finset ℕ) ∧ A.card = 3 - H.card) ∨
     (D.card = 3 ∧ M.card = 4 ∧ H.card ∈ ({0, 1, 2, 3} : Finset ℕ) ∧ A.card = 4 - H.card) ∨
     (D.card = 2 ∧ M.card = 5 ∧ H.card ∈ ({1, 2, 3, 4} : Finset ℕ) ∧ A.card = 5 - H.card)) :=
  case_split_seven_ub6 hP (hullVertices_card_le_six_of_no_convex7 hP hconv6)

end SourceGapAndCaseSplits

end
