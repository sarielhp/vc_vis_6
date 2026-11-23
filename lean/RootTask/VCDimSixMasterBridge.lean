import Mathlib
import RootTask.PolygonDefs
import RootTask.PolygonEnclosureCore
import RootTask.NewEnclosureLemmas
import RootTask.ChirotopeSoundness
import RootTask.CertifiedAndHalfPlaneSoundness

open scoped Classical BigOperators
open Finset

noncomputable section

namespace VCDimSixMasterBridge

open PolygonCore NewEnclosure ChirotopeSoundness CertifiedAndHalfPlaneSoundness

/-!
# General Certified `side-corners` Bridge `(C6)` and Hereditary `VC-dim ≤ 6` Lift

Closes Finding `#2B` for `vc_dim_6.tex`:
1. `certified_side_corners_general_oppSide_C6`: extends `certified_side_corners_hull_C6` from
   extreme hull vertices `u, v ∈ B \ {h}` to **arbitrary** points `u, v ∈ S \ {h}` (including
   interior points `u, v ∈ A = interiorPoints S`) satisfying
   `oppSideBool (zWitness w h) (S h) (S u) (S v) = true`.
2. `vcdim_le_six_of_no_seven_shattered`: lifts the non-existence of a 7-point shattered set in `P`
   to arbitrary `n ≥ 7` via `NewEnclosure.hereditary_shattered_emb`.
-/

private lemma halfspace_orient2D_convex (p₁ p₂ : ℝ × ℝ) :
    Convex ℝ {x : ℝ × ℝ | 0 ≤ orient2D p₁ p₂ x} := by
  intro a ha b hb α β hα hβ hαβ
  dsimp at ha hb ⊢
  have hid : orient2D p₁ p₂ (α • a + β • b) = α * orient2D p₁ p₂ a + β * orient2D p₁ p₂ b := by
    unfold orient2D
    simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    linear_combination (p₁.2 * p₂.1 - p₁.1 * p₂.2) * hαβ
  rw [hid]
  exact add_nonneg (mul_nonneg hα ha) (mul_nonneg hβ hb)

/-- **Clause `(C6)` General `oppSideBool` Propagation (`certified_side_corners_general_oppSide_C6`)**:
    For any `h ∈ certifiedSet P S w` (`3 ≤ n`) and **arbitrary** `u, v : Fin n` (`u ≠ h`, `v ≠ h`,
    including interior points `u, v ∈ interiorPoints S`) satisfying
    `oppSideBool (zWitness w h) (S h) (S u) (S v) = true`, every witness `w Tw` with `{u, v} ⊆ Tw`
    satisfies `inOpenTriBool (S h) (w Tw) (S u) (S v) = true`. -/
theorem certified_side_corners_general_oppSide_C6 {n : ℕ} {P : Set (ℝ × ℝ)}
    {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ}
    (hP : ShatteredSimplePolygon P S w) (hn : 3 ≤ n)
    {h u v : Fin n} (hh : h ∈ certifiedSet P S w)
    (huh : u ≠ h) (hvh : v ≠ h)
    (hopp : oppSideBool (zWitness w h) (S h) (S u) (S v) = true)
    {Tw : Finset (Fin n)} (hsub : {u, v} ⊆ Tw) :
    inOpenTriBool (S h) (w Tw) (S u) (S v) = true := by
  have huv : u ≠ v := by
    intro heq; subst heq; unfold oppSideBool at hopp; simp at hopp
  let zh := zWitness w h
  have hmul : orient2D zh (S h) (S u) * orient2D zh (S h) (S v) < 0 :=
    (oppSideBool_iff_mul_neg
      (orient_w_S_S_ne hP (Finset.univ.erase h) huh.symm)
      (orient_w_S_S_ne hP (Finset.univ.erase h) hvh.symm)).mp hopp
  have hcert : IsCertified P S w h := (Finset.mem_filter.mp hh).2
  obtain ⟨b₀, c₀, _, _, hb0h, hc0h, hb0c0, hb0h_edge, hhc0_edge, hall⟩ :=
    certified_neighbors_and_front hP hn hcert
  have hzh_b0 : Sees P zh (S b₀) :=
    (hP.shatters (Finset.univ.erase h) b₀).mpr (Finset.mem_erase.mpr ⟨hb0h, Finset.mem_univ _⟩)
  have hzh_c0 : Sees P zh (S c₀) :=
    (hP.shatters (Finset.univ.erase h) c₀).mpr (Finset.mem_erase.mpr ⟨hc0h, Finset.mem_univ _⟩)
  obtain ⟨_, ⟨b0', c0', hb0', hc0', hzb0, hzc0⟩⟩ := hall (Finset.univ.erase h) hzh_b0 hzh_c0
  rw [isCCWHullEdge_pred_unique hb0' hb0h_edge] at hzb0
  rw [isCCWHullEdge_succ_unique hc0' hhc0_edge] at hzc0
  have hmem_hull : ∀ i : Fin n,
      S i ∈ convexHull ℝ (((hullVertices S).image S : Finset (ℝ × ℝ)) : Set (ℝ × ℝ)) := fun i => by
    rw [hullVertices_convexHull_eq S hP.s_inj]
    exact subset_convexHull ℝ _ ⟨i, rfl⟩
  have h_b0h_nn : ∀ i : Fin n, 0 ≤ orient2D (S b₀) (S h) (S i) := fun i => by
    refine convexHull_min (fun x hx => ?_) (halfspace_orient2D_convex (S b₀) (S h)) (hmem_hull i)
    rcases Finset.mem_image.mp hx with ⟨q, hqB, rfl⟩
    dsimp
    by_cases hqb0 : q = b₀
    · rw [hqb0, orient2D_self_outer]
    · by_cases hqh : q = h
      · rw [hqh, orient2D_self_right]
      · exact le_of_lt (hb0h_edge.2.2.2 (S q) (Finset.mem_image_of_mem S hqB)
          (hP.s_inj.ne hqb0) (hP.s_inj.ne hqh))
  have h_hc0_nn : ∀ i : Fin n, 0 ≤ orient2D (S h) (S c₀) (S i) := fun i => by
    refine convexHull_min (fun x hx => ?_) (halfspace_orient2D_convex (S h) (S c₀)) (hmem_hull i)
    rcases Finset.mem_image.mp hx with ⟨q, hqB, rfl⟩
    dsimp
    by_cases hqh : q = h
    · rw [hqh, orient2D_self_outer]
    · by_cases hqc0 : q = c₀
      · rw [hqc0, orient2D_self_right]
      · exact le_of_lt (hhc0_edge.2.2.2 (S q) (Finset.mem_image_of_mem S hqB)
          (hP.s_inj.ne hqh) (hP.s_inj.ne hqc0))
  let da := orient2D zh (S h) (S u)
  let db := orient2D zh (S h) (S v)
  have hden_ne : da - db ≠ 0 := by
    intro h0; have heq : da = db := sub_eq_zero.mp h0
    have : 0 ≤ db * db := mul_self_nonneg db
    have hopp' : da * db < 0 := hmul
    rw [heq] at hopp'; linarith
  let t := da / (da - db)
  have ht01 : 0 < t ∧ t < 1 := by
    have hopp' : da * db < 0 := hmul
    rcases lt_or_gt_of_ne (mul_ne_zero_iff.mp (ne_of_lt hopp')).1 with hda | hda
    · have hdb : 0 < db := by nlinarith
      have hdd : da - db < 0 := by linarith
      exact ⟨div_pos_of_neg_of_neg hda hdd, (div_lt_one_of_neg hdd).mpr (by linarith)⟩
    · have hdb : db < 0 := by nlinarith
      have hdd : 0 < da - db := by linarith
      exact ⟨div_pos hda hdd, (div_lt_one hdd).mpr (by linarith)⟩
  let y : ℝ × ℝ := ((1 - t) * (S u).1 + t * (S v).1, (1 - t) * (S u).2 + t * (S v).2)
  have hy_col : orient2D zh (S h) y = 0 := by
    rw [orient2D_affine_comb zh (S h) (S u) (S v) y t rfl rfl]
    change (1 - t) * da + t * db = 0
    dsimp [t]; field_simp [hden_ne]; ring
  have hy_ne_h : y ≠ S h := by
    intro hyh
    have hcol : orient2D (S u) (S v) (S h) = 0 := by
      rw [← hyh]; unfold orient2D; dsimp [y]; ring
    exact orient_S_S_S_ne hP huv hvh huh hcol
  have hy_b0h_nn : 0 ≤ orient2D (S b₀) (S h) y := by
    rw [orient2D_affine_comb (S b₀) (S h) (S u) (S v) y t rfl rfl]
    exact add_nonneg (mul_nonneg (by linarith) (h_b0h_nn u))
      (mul_nonneg (le_of_lt ht01.1) (h_b0h_nn v))
  have hy_hc0_nn : 0 ≤ orient2D (S h) (S c₀) y := by
    rw [orient2D_affine_comb (S h) (S c₀) (S u) (S v) y t rfl rfl]
    exact add_nonneg (mul_nonneg (by linarith) (h_hc0_nn u))
      (mul_nonneg (le_of_lt ht01.1) (h_hc0_nn v))
  have hy_pos_one : 0 < orient2D (S b₀) (S h) y ∨ 0 < orient2D (S h) (S c₀) y := by
    by_contra hboth; push Not at hboth
    have hz1 : orient2D (S b₀) (S h) y = 0 := le_antisymm hboth.1 hy_b0h_nn
    have hz2 : orient2D (S h) (S c₀) y = 0 := le_antisymm hboth.2 hy_hc0_nn
    have hc_pos : 0 < orient2D (S b₀) (S h) (S c₀) :=
      hb0h_edge.2.2.2 (S c₀) hhc0_edge.2.1 (fun e => hb0c0 (hP.s_inj e).symm)
        (fun e => hc0h (hP.s_inj e))
    have h_id1 : orient2D (S b₀) (S h) (S c₀) * (y.1 - (S h).1) =
        ((S c₀).1 - (S h).1) * orient2D (S b₀) (S h) y +
        ((S b₀).1 - (S h).1) * orient2D (S h) (S c₀) y := by unfold orient2D; ring
    have h_id2 : orient2D (S b₀) (S h) (S c₀) * (y.2 - (S h).2) =
        ((S c₀).2 - (S h).2) * orient2D (S b₀) (S h) y +
        ((S b₀).2 - (S h).2) * orient2D (S h) (S c₀) y := by unfold orient2D; ring
    rw [hz1, hz2, mul_zero, mul_zero, add_zero] at h_id1 h_id2
    have hdx : y.1 - (S h).1 = 0 := (mul_eq_zero.mp h_id1).resolve_left (ne_of_gt hc_pos)
    have hdy : y.2 - (S h).2 = 0 := (mul_eq_zero.mp h_id2).resolve_left (ne_of_gt hc_pos)
    exact hy_ne_h (by ext <;> linarith)
  have hzh_ne_h : zh ≠ S h := (hP.s_ne_w h (Finset.univ.erase h)).symm
  have hzh_coord : (S h).1 - zh.1 ≠ 0 ∨ (S h).2 - zh.2 ≠ 0 := by
    by_contra hc; push Not at hc; exact hzh_ne_h (by ext <;> linarith)
  obtain ⟨lam, hlam1, hlam2⟩ : ∃ lam : ℝ,
      y.1 - (S h).1 = lam * ((S h).1 - zh.1) ∧
      y.2 - (S h).2 = lam * ((S h).2 - zh.2) := by
    unfold orient2D at hy_col
    rcases hzh_coord with hx | hyc
    · exact ⟨(y.1 - (S h).1) / ((S h).1 - zh.1), by field_simp [hx], by field_simp [hx]; linarith⟩
    · exact ⟨(y.2 - (S h).2) / ((S h).2 - zh.2), by field_simp [hyc]; linarith, by field_simp [hyc]⟩
  have hlam_pos : 0 < lam := by
    have hzb0' : orient2D (S b₀) (S h) zh < 0 := hzb0
    have hzc0' : orient2D (S h) (S c₀) zh < 0 := hzc0
    have hid1 : orient2D (S b₀) (S h) y = -lam * orient2D (S b₀) (S h) zh := by
      unfold orient2D
      have hy1 : y.1 = (S h).1 + lam * ((S h).1 - zh.1) := by linarith
      have hy2 : y.2 = (S h).2 + lam * ((S h).2 - zh.2) := by linarith
      rw [hy1, hy2]; ring
    have hid2 : orient2D (S h) (S c₀) y = -lam * orient2D (S h) (S c₀) zh := by
      unfold orient2D
      have hy1 : y.1 = (S h).1 + lam * ((S h).1 - zh.1) := by linarith
      have hy2 : y.2 = (S h).2 + lam * ((S h).2 - zh.2) := by linarith
      rw [hy1, hy2]; ring
    rcases hy_pos_one with hpos1 | hpos2
    · rw [hid1] at hpos1; nlinarith
    · rw [hid2] at hpos2; nlinarith
  have h1lam : 0 < 1 + lam := by linarith
  have h1lam_ne : 1 + lam ≠ 0 := ne_of_gt h1lam
  have htri_zh : InOpenTri zh (S u) (S v) (S h) := by
    refine ⟨lam / (1 + lam), (1 - t) / (1 + lam), t / (1 + lam),
      div_pos hlam_pos h1lam, div_pos (by linarith) h1lam, div_pos ht01.1 h1lam, ?_, ?_, ?_⟩
    · field_simp [h1lam_ne]; ring
    · have hy1 : y.1 = (S h).1 + lam * ((S h).1 - zh.1) := by linarith
      dsimp [y] at hy1; field_simp [h1lam_ne]; linarith
    · have hy2 : y.2 = (S h).2 + lam * ((S h).2 - zh.2) := by linarith
      dsimp [y] at hy2; field_simp [h1lam_ne]; linarith
  have htri_bool : inOpenTriBool (S h) zh (S u) (S v) = true :=
    (inOpenTriBool_S_w_S_S hP huh.symm hvh.symm huv (Finset.univ.erase h)).mpr htri_zh
  exact (certified_side_corners_cone_C6 hP huh hvh huv htri_bool).2 Tw hsub

/-- Explicit `s : Bool` sign-literal form of `certified_side_corners_general_oppSide_C6`. -/
theorem certified_side_corners_general_orientSign_C6 {n : ℕ} {P : Set (ℝ × ℝ)}
    {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ}
    (hP : ShatteredSimplePolygon P S w) (hn : 3 ≤ n)
    {h u v : Fin n} (hh : h ∈ certifiedSet P S w)
    (huh : u ≠ h) (hvh : v ≠ h) {s : Bool}
    (hsu : orientSign (zWitness w h) (S h) (S u) = s)
    (hsv : orientSign (zWitness w h) (S h) (S v) = !s)
    {Tw : Finset (Fin n)} (hsub : {u, v} ⊆ Tw) :
    inOpenTriBool (S h) (w Tw) (S u) (S v) = true := by
  apply certified_side_corners_general_oppSide_C6 hP hn hh huh hvh _ hsub
  unfold oppSideBool
  rw [hsu, hsv]
  cases s <;> rfl

/-- **Hereditary `VC-dim ≤ 6` Lift (`vcdim_le_six_of_no_seven_shattered`)**:
    If `P` shatters no 7-point set under `(G1)–(G2)`, then `P` shatters no `n`-point set
    under `(G1)–(G2)` for any `n ≥ 7`. -/
theorem vcdim_le_six_of_no_seven_shattered {P : Set (ℝ × ℝ)}
    (hno7 : ∀ (S7 : Fin 7 → ℝ × ℝ) (w7 : Finset (Fin 7) → ℝ × ℝ),
      ShatteredSimplePolygon P S7 w7 → False) :
    ∀ {n : ℕ}, 7 ≤ n →
      ∀ (S : Fin n → ℝ × ℝ) (w : Finset (Fin n) → ℝ × ℝ),
        ShatteredSimplePolygon P S w → False := by
  intro n hn S w hP
  let ι : Fin 7 ↪ Fin n := ⟨fun i => ⟨i.val, by omega⟩, fun i j h => Fin.ext (Fin.mk.inj h)⟩
  exact hno7 (S ∘ ι) (fun T' => w (T'.image ι)) (NewEnclosure.hereditary_shattered_emb hP ι)

end VCDimSixMasterBridge

end
