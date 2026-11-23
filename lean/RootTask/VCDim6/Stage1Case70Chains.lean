import Mathlib
import RootTask.PolygonDefs
import RootTask.PolygonEnclosureCore
import RootTask.ChirotopeSoundness
import RootTask.CertifiedAndHalfPlaneSoundness
import RootTask.SourceGapAndCaseSplits
import RootTask.VCDim6.Stage1Case70Polarization

open scoped Classical BigOperators
open Finset
open PolygonCore ChirotopeSoundness CertifiedAndHalfPlaneSoundness

noncomputable section

namespace VCDim6

/-!
# Section 3.1 Helpers: `CCWConvexSeven`, `(C4)` Wedge Exclusion, and Crossing-Good Chains (`Lemma 3.3`)

Formalizes the coordinate-free determinant and `VisibleContour` chain lemmas for Stage 1 Case `(7, 0)`
(`ideation_FINAL_SOLUTION.md` Lemma 3.3(a)–(c), 100% computer-free and RUP-free).
-/

private lemma fin7_ne_succ (u : Fin 7) : u ≠ u + 1 := by revert u; decide
private lemma fin7_pred_ne_succ (m : Fin 7) : m - 1 ≠ m + 1 := by revert m; decide
private lemma fin7_sub_pred_one (m : Fin 7) : (m - (m - 1)).val = 1 := by revert m; decide
private lemma fin7_succ_sub_pred_two (m : Fin 7) : ((m + 1) - (m - 1)).val = 2 := by revert m; decide

private lemma fin7_step_val (x a : Fin 7) :
    (x - a).val < 6 → ((x + 1) - a).val = (x - a).val + 1 := by
  revert x a; decide

private lemma fin7_diff_of_lt (a x y : Fin 7) :
    (x - a).val ≤ (y - a).val → (y - x).val = (y - a).val - (x - a).val := by
  revert a x y; decide

private lemma fin7_diff_wrap (a x d : Fin 7) :
    0 < (x - a).val → d = a → (d - x).val = 7 - (x - a).val := by
  revert a x d; decide

private lemma fin7_sum_step (a c d : Fin 7) :
    c ≠ d → (c - a).val + (d - c).val ≤ 7 →
      ((c - a).val < (d - a).val) ∨ ((c - a).val + (d - c).val = 7 ∧ d = a) := by
  revert a c d; decide

private lemma fin7_ccw_pred1 (a m b : Fin 7) :
    0 < (m - a).val → (m - a).val < (b - a).val → a ≠ m - 1 →
      0 < ((m - 1) - a).val ∧ ((m - 1) - a).val < (m - a).val ∧
      0 < (m - (m - 1)).val ∧ (m - (m - 1)).val < (b - (m - 1)).val := by
  revert a m b; decide

private lemma fin7_ccw_succ1 (a m b : Fin 7) :
    0 < (m - a).val → (m - a).val < (b - a).val → b ≠ m + 1 →
      0 < ((m + 1) - m).val ∧ ((m + 1) - m).val < (b - m).val ∧
      0 < (m - a).val ∧ (m - a).val < ((m + 1) - a).val := by
  revert a m b; decide

private lemma fin7_chain_left (a p b : Fin 7) :
    0 < (p - a).val → (p - a).val < (b - a).val → p ≠ a + 1 →
      0 < ((a + 1) - a).val ∧ ((a + 1) - a).val < (p - a).val ∧
      0 < (p - (a + 1)).val ∧ (p - (a + 1)).val < (b - (a + 1)).val := by
  revert a p b; decide

private lemma fin7_chain_right (a p b : Fin 7) :
    0 < (p - a).val → (p - a).val < (b - a).val → p ≠ b - 1 →
      0 < ((b - 1) - a).val ∧ ((b - 1) - a).val < (b - a).val ∧
      0 < (p - a).val ∧ (p - a).val < ((b - 1) - a).val ∧
      0 < ((b - 1) - p).val ∧ ((b - 1) - p).val < (b - p).val := by
  revert a p b; decide

private lemma fin7_quad_sub (x u y z : Fin 7) :
    0 < (u - x).val → (u - x).val < (y - x).val → (y - x).val < (z - x).val →
      0 < (y - u).val ∧ (y - u).val < (z - u).val := by
  revert x u y z; decide

/-- Strict counterclockwise convex position for `S : Fin 7 → ℝ × ℝ`:
    `orientSign (S i) (S j) (S k) = true` whenever `0 < (j - i).val < (k - i).val`. -/
def CCWConvexSeven (S : Fin 7 → ℝ × ℝ) : Prop :=
  ∀ i j k : Fin 7, 0 < (j - i).val → (j - i).val < (k - i).val →
    orientSign (S i) (S j) (S k) = true

lemma orient2D_pos_of_ccw {S : Fin 7 → ℝ × ℝ} (hccw : CCWConvexSeven S)
    {i j k : Fin 7} (h1 : 0 < (j - i).val) (h2 : (j - i).val < (k - i).val) :
    0 < orient2D (S i) (S j) (S k) :=
  (orientSign_eq_true_iff _ _ _).mp (hccw i j k h1 h2)

lemma orient2D_neg_of_cw {S : Fin 7 → ℝ × ℝ} (hccw : CCWConvexSeven S)
    {i j k : Fin 7} (h1 : 0 < (k - i).val) (h2 : (k - i).val < (j - i).val) :
    orient2D (S i) (S j) (S k) < 0 := by
  have hp := orient2D_pos_of_ccw hccw h1 h2
  rw [orient2D_swap23]
  linarith

lemma orientSign_false_of_cw {S : Fin 7 → ℝ × ℝ} (hccw : CCWConvexSeven S)
    {i j k : Fin 7} (h1 : 0 < (k - i).val) (h2 : (k - i).val < (j - i).val) :
    orientSign (S i) (S j) (S k) = false :=
  (orientSign_eq_false_iff _ _ _).mpr (le_of_lt (orient2D_neg_of_cw hccw h1 h2))

lemma strictConvexCCWPoly_of_ccwConvexSeven {S : Fin 7 → ℝ × ℝ} (hccw : CCWConvexSeven S) :
    StrictConvexCCWPoly S := by
  intro i j hji hj1
  have h0 : 0 < (j - i).val := by
    by_contra hle
    have hz : (j - i).val = 0 := by omega
    exact hji (sub_eq_zero.mp (Fin.ext hz))
  have h1val : ((i + 1) - i).val = 1 := by
    rw [add_sub_cancel_left]; rfl
  have hgt1 : 1 < (j - i).val := by
    by_contra hle
    have he1 : (j - i).val = 1 := by omega
    have h1eq : j - i = (1 : Fin (4 + 3)) := Fin.ext he1
    exact hj1 (by calc j = i + (j - i) := (add_sub_cancel i j).symm
      _ = i + 1 := congrArg (i + ·) h1eq)
  exact orient2D_pos_of_ccw hccw (by rw [h1val]; omega) (by rw [h1val]; exact hgt1)

/-- Additive area-sum identity on any triangle `(a, b, c)` and point `v`. -/
lemma orient2D_tri_sum (a b c v : ℝ × ℝ) :
    orient2D a b v + orient2D b c v + orient2D c a v = orient2D a b c := by
  unfold orient2D; ring

/-- `(C4)` at an unmarked hull vertex `m ∉ Tv` whose hull neighbors `m - 1, m + 1` belong to `Tv`:
    the two hull edges `(m - 1, m)` and `(m, m + 1)` cannot both face `w Tv`. -/
lemma c4_missed_neighbors {P : Set (ℝ × ℝ)} {S : Fin 7 → ℝ × ℝ} {w : Finset (Fin 7) → ℝ × ℝ}
    (hP : ShatteredSimplePolygon P S w) (hccw : CCWConvexSeven S)
    (hA : PolygonCore.interiorPoints S = ∅) (hH : PolygonCore.certifiedSet P S w = ∅)
    {Tv : Finset (Fin 7)} {m : Fin 7}
    (hm_out : m ∉ Tv) (hm_prev : m - 1 ∈ Tv) (hm_next : m + 1 ∈ Tv) :
    ¬ (orientSign (S (m - 1)) (S m) (w Tv) = false ∧
       orientSign (S m) (S (m + 1)) (w Tv) = false) := by
  rintro ⟨hf1, hf2⟩
  have hmD : m ∈ _root_.hullVertices S \ PolygonCore.certifiedSet P S w := by
    rw [← SourceGapAndCaseSplits.hullVertices_eq, hH]
    have hB_univ : PolygonCore.hullVertices S = Finset.univ := by
      ext x; simp only [Finset.mem_univ, iff_true]
      by_contra hx
      have hxA : x ∈ PolygonCore.interiorPoints S := Finset.mem_sdiff.mpr ⟨Finset.mem_univ x, hx⟩
      rw [hA] at hxA; exact Finset.notMem_empty x hxA
    simp [hB_univ]
  have hc4 := non_certified_obstruction_clause_C4 hP (by decide : 3 ≤ 7)
    hmD hm_out hm_prev hm_next (fin7_pred_ne_succ m)
  have hside : inOpenTriSideBool false (S m) (w Tv) (S (m - 1)) (S (m + 1)) = true := by
    unfold inOpenTriSideBool
    have h1 : orientSign (w Tv) (S (m - 1)) (S m) = false := by
      rw [orientSign_cycle2 (S (m - 1)) (S m) (w Tv), hf1]
    have h2 : orientSign (S (m - 1)) (S (m + 1)) (S m) = false := by
      apply orientSign_false_of_cw hccw
      · rw [fin7_sub_pred_one]; omega
      · rw [fin7_sub_pred_one, fin7_succ_sub_pred_two]; omega
    have h3 : orientSign (S (m + 1)) (w Tv) (S m) = false := by
      rw [orientSign_cycle (S m) (S (m + 1)) (w Tv), hf2]
    simp [h1, h2, h3]
  have htri : inOpenTriBool (S m) (w Tv) (S (m - 1)) (S (m + 1)) = true := by
    unfold inOpenTriBool; simp [hside]
  rw [hc4] at htri
  exact Bool.noConfusion htri

/-- **Super-Lemma (`c4_chord_wedge_excl`)**:
    If `m ∉ Tv`, `m - 1 ∈ Tv`, `m + 1 ∈ Tv`, and `(a, m, b)` is in strict CCW cyclic order on `Fin 7`,
    then `orientSign (S a) (S m) (w Tv) = false` and `orientSign (S m) (S b) (w Tv) = false`
    cannot hold simultaneously. -/
theorem c4_chord_wedge_excl {P : Set (ℝ × ℝ)} {S : Fin 7 → ℝ × ℝ} {w : Finset (Fin 7) → ℝ × ℝ}
    (hP : ShatteredSimplePolygon P S w) (hccw : CCWConvexSeven S)
    (hA : PolygonCore.interiorPoints S = ∅) (hH : PolygonCore.certifiedSet P S w = ∅)
    {Tv : Finset (Fin 7)} {a m b : Fin 7}
    (hm_out : m ∉ Tv) (hm_prev : m - 1 ∈ Tv) (hm_next : m + 1 ∈ Tv)
    (h1 : 0 < (m - a).val) (h2 : (m - a).val < (b - a).val) :
    ¬ (orientSign (S a) (S m) (w Tv) = false ∧ orientSign (S m) (S b) (w Tv) = false) := by
  rintro ⟨ham_f, hmb_f⟩
  have ham_ne : a ≠ m := fun h => by subst h; simp at h1
  have hmb_ne : m ≠ b := fun h => by subst h; omega
  have ham_neg : orient2D (S a) (S m) (w Tv) < 0 :=
    (orientSign_eq_false_iff_of_ne_zero (orient_S_S_w_ne hP ham_ne Tv)).mp ham_f
  have hmb_neg : orient2D (S m) (S b) (w Tv) < 0 :=
    (orientSign_eq_false_iff_of_ne_zero (orient_S_S_w_ne hP hmb_ne Tv)).mp hmb_f
  have hmba_pos : 0 < orient2D (S m) (S b) (S a) := by
    have := orient2D_pos_of_ccw hccw h1 h2
    have hid : orient2D (S m) (S b) (S a) = orient2D (S a) (S m) (S b) := by unfold orient2D; ring
    linarith
  have h_prev_f : orientSign (S (m - 1)) (S m) (w Tv) = false := by
    by_cases ha_eq : a = m - 1
    · rwa [← ha_eq]
    · obtain ⟨c1, c2, c3, c4⟩ := fin7_ccw_pred1 a m b h1 h2 ha_eq
      have h_am1m : 0 < orient2D (S m) (S a) (S (m - 1)) := by
        have hp := orient2D_pos_of_ccw hccw c1 c2
        have hid : orient2D (S m) (S a) (S (m - 1)) = orient2D (S a) (S (m - 1)) (S m) := by
          unfold orient2D; ring
        linarith
      have h_bm1 : 0 < orient2D (S m) (S b) (S (m - 1)) := by
        have hp := orient2D_pos_of_ccw hccw c3 c4
        have hid : orient2D (S m) (S b) (S (m - 1)) = orient2D (S (m - 1)) (S m) (S b) := by
          unfold orient2D; ring
        linarith
      have hpl := plucker_around_origin (S m) (S b) (w Tv) (S a) (S (m - 1))
      have hmva : orient2D (S m) (w Tv) (S a) = orient2D (S a) (S m) (w Tv) := by
        unfold orient2D; ring
      have hvm1 : orient2D (S m) (w Tv) (S (m - 1)) = orient2D (S (m - 1)) (S m) (w Tv) := by
        unfold orient2D; ring
      rw [hmva, hvm1] at hpl
      have hneg : orient2D (S (m - 1)) (S m) (w Tv) < 0 := by nlinarith
      exact (orientSign_eq_false_iff _ _ _).mpr (le_of_lt hneg)
  have h_next_f : orientSign (S m) (S (m + 1)) (w Tv) = false := by
    by_cases hb_eq : b = m + 1
    · rwa [← hb_eq]
    · obtain ⟨c1, c2, c3, c4⟩ := fin7_ccw_succ1 a m b h1 h2 hb_eq
      have h_mm1b : 0 < orient2D (S m) (S (m + 1)) (S b) := orient2D_pos_of_ccw hccw c1 c2
      have h_mm1a : 0 < orient2D (S m) (S (m + 1)) (S a) := by
        have hp := orient2D_pos_of_ccw hccw c3 c4
        have hid : orient2D (S m) (S (m + 1)) (S a) = orient2D (S a) (S m) (S (m + 1)) := by
          unfold orient2D; ring
        linarith
      have hpl := plucker_around_origin (S m) (S (m + 1)) (w Tv) (S b) (S a)
      have hmvb : orient2D (S m) (w Tv) (S b) = -orient2D (S m) (S b) (w Tv) := by
        unfold orient2D; ring
      have hmva : orient2D (S m) (w Tv) (S a) = orient2D (S a) (S m) (w Tv) := by
        unfold orient2D; ring
      rw [hmvb, hmva] at hpl
      have hneg : orient2D (S m) (S (m + 1)) (w Tv) < 0 := by nlinarith
      exact (orientSign_eq_false_iff _ _ _).mpr (le_of_lt hneg)
  exact c4_missed_neighbors hP hccw hA hH hm_out hm_prev hm_next ⟨h_prev_f, h_next_f⟩

/-- Crossing-good chain predicate on `Fin 7` from `a` to `b` (`2 ≤ (b - a).val`):
    neither boundary hull edge `(a, a + 1)`, `(b - 1, b)` nor the closing chord `(a, b)` faces `v`. -/
def ChainGood (S : Fin 7 → ℝ × ℝ) (v : ℝ × ℝ) (a b : Fin 7) : Prop :=
  orientSign (S a) (S (a + 1)) v = true ∧
  orientSign (S (b - 1)) (S b) v = true ∧
  orientSign (S a) (S b) v = true

/-- **Lemma 3.3(b) (`chainGood_inner_signs`)**:
    If `ChainGood S v a b` holds and `p` is an inner vertex of `(a, ..., b)`
    (`0 < (p - a).val < (b - a).val`), then `orientSign v (S a) (S p) = true`,
    `orientSign v (S p) (S b) = true`, and `oppSideBool (S a) (S b) v (S p) = true`. -/
theorem chainGood_inner_signs {S : Fin 7 → ℝ × ℝ} (hccw : CCWConvexSeven S)
    {v : ℝ × ℝ} {a p b : Fin 7}
    (hgood : ChainGood S v a b)
    (hp1 : 0 < (p - a).val) (hp2 : (p - a).val < (b - a).val) :
    orientSign v (S a) (S p) = true ∧
    orientSign v (S p) (S b) = true ∧
    oppSideBool (S a) (S b) v (S p) = true := by
  rcases hgood with ⟨ha1, hb1, hab⟩
  have ha1_pos : 0 < orient2D (S a) (S (a + 1)) v := (orientSign_eq_true_iff _ _ _).mp ha1
  have hb1_pos : 0 < orient2D (S (b - 1)) (S b) v := (orientSign_eq_true_iff _ _ _).mp hb1
  have hab_pos : 0 < orient2D (S a) (S b) v := (orientSign_eq_true_iff _ _ _).mp hab
  have hap_pos : 0 < orient2D v (S a) (S p) := by
    have hid : orient2D v (S a) (S p) = orient2D (S a) (S p) v := by unfold orient2D; ring
    rw [hid]
    by_cases hp_eq : p = a + 1
    · rwa [hp_eq]
    · obtain ⟨c1, c2, _, _⟩ := fin7_chain_left a p b hp1 hp2 hp_eq
      have t1 := orient2D_pos_of_ccw hccw c1 (lt_trans c2 hp2)
      have t2 := orient2D_pos_of_ccw hccw c1 c2
      have t3 : 0 < orient2D (S a) (S p) (S b) := orient2D_pos_of_ccw hccw hp1 hp2
      have hpl := plucker_around_origin (S a) (S (a + 1)) (S p) (S b) v
      nlinarith
  have hpb_pos : 0 < orient2D v (S p) (S b) := by
    have hid : orient2D v (S p) (S b) = orient2D (S p) (S b) v := by unfold orient2D; ring
    rw [hid]
    by_cases hp_eq : p = b - 1
    · rwa [hp_eq]
    · obtain ⟨c1, c2, _, _, c5, c6⟩ := fin7_chain_right a p b hp1 hp2 hp_eq
      have t1 : 0 < orient2D (S b) (S a) (S (b - 1)) := by
        have := orient2D_pos_of_ccw hccw c1 c2
        have h' : orient2D (S b) (S a) (S (b - 1)) = orient2D (S a) (S (b - 1)) (S b) := by
          unfold orient2D; ring
        linarith
      have t2 : 0 < orient2D (S b) (S a) (S p) := by
        have := orient2D_pos_of_ccw hccw hp1 hp2
        have h' : orient2D (S b) (S a) (S p) = orient2D (S a) (S p) (S b) := by
          unfold orient2D; ring
        linarith
      have t3 : 0 < orient2D (S b) (S p) (S (b - 1)) := by
        have := orient2D_pos_of_ccw hccw c5 c6
        have h' : orient2D (S b) (S p) (S (b - 1)) = orient2D (S p) (S (b - 1)) (S b) := by
          unfold orient2D; ring
        linarith
      have hpl := plucker_around_origin (S b) (S a) (S p) (S (b - 1)) v
      have hbav : orient2D (S b) (S a) v = -orient2D (S a) (S b) v := by unfold orient2D; ring
      have hbb1v : orient2D (S b) (S (b - 1)) v = -orient2D (S (b - 1)) (S b) v := by
        unfold orient2D; ring
      have hbpv : orient2D (S b) (S p) v = -orient2D (S p) (S b) v := by unfold orient2D; ring
      rw [hbav, hbb1v, hbpv] at hpl
      nlinarith
  have hopp : oppSideBool (S a) (S b) v (S p) = true := by
    unfold oppSideBool
    have hab_p : orientSign (S a) (S b) (S p) = false := orientSign_false_of_cw hccw hp1 hp2
    rw [hab, hab_p]; rfl
  exact ⟨(orientSign_eq_true_iff _ _ _).mpr hap_pos,
    (orientSign_eq_true_iff _ _ _).mpr hpb_pos, hopp⟩

/-- Builds `HalfPlaneChirotopeConfig` (`FiresOrdered`) from `ChainGood S (w Tv) a b` when all vertices
    of `[a .. b]` lie on side `s` of `line(w Tv, w Finset.univ)`. -/
theorem chainGood_firesOrdered {P : Set (ℝ × ℝ)} {S : Fin 7 → ℝ × ℝ} {w : Finset (Fin 7) → ℝ × ℝ}
    (hP : ShatteredSimplePolygon P S w) (hccw : CCWConvexSeven S)
    {Tv : Finset (Fin 7)} {a p b : Fin 7} {s : Bool}
    (hgood : ChainGood S (w Tv) a b)
    (ha_out : a ∉ Tv) (hb_out : b ∉ Tv) (hp_in : p ∈ Tv)
    (hp1 : 0 < (p - a).val) (hp2 : (p - a).val < (b - a).val)
    (hside_a : orientSign (w Tv) (w Finset.univ) (S a) = s)
    (hside_p : orientSign (w Tv) (w Finset.univ) (S p) = s)
    (hside_b : orientSign (w Tv) (w Finset.univ) (S b) = s)
    (hiv : (∃ s₂ ∈ Tv, orientSign (w Tv) (w Finset.univ) (S s₂) = !s) ∨
      (∃ ie ∈ Tv, orientSign (w Tv) (w Finset.univ) (S ie) = s ∧
        orientSign (w Tv) (S ie) (S (if s then a else b)) = s)) :
    FiresOrdered P S w Tv (if s then a else b) p (if s then b else a) := by
  obtain ⟨hap, hpb, hcross⟩ := chainGood_inner_signs hccw hgood hp1 hp2
  have hap_ne : a ≠ p := fun h => ha_out (h ▸ hp_in)
  have hbp_ne : b ≠ p := fun h => hb_out (h ▸ hp_in)
  have hab_ne : a ≠ b := fun h => by subst h; simp at hp2
  have hcond : Sees P (w Tv) (w Finset.univ) ∨
      (∃ s₁ s₂ : Fin 7, s₁ ∈ Tv ∧ s₁ ∈ (Finset.univ : Finset (Fin 7)) ∧
        s₂ ∈ Tv ∧ s₂ ∈ (Finset.univ : Finset (Fin 7)) ∧
        oppSideBool (w Tv) (w Finset.univ) (S s₁) (S s₂) = true) ∨
      (∃ ie : Fin 7, ie ∈ Tv ∧ ie ∈ (Finset.univ : Finset (Fin 7)) ∧
        orientSign (w Tv) (w Finset.univ) (S ie) = orientSign (w Tv) (w Finset.univ) (S p) ∧
        orientSign (w Tv) (S ie) (S (if s then a else b)) =
          orientSign (w Tv) (w Finset.univ) (S p)) := by
    rcases hiv with ⟨s₂, hs₂, hopp₂⟩ | ⟨ie, hie, hs_ie, h_ieg⟩
    · refine Or.inr (Or.inl ⟨p, s₂, hp_in, Finset.mem_univ _, hs₂, Finset.mem_univ _, ?_⟩)
      unfold oppSideBool; rw [hside_p, hopp₂]; cases s <;> rfl
    · exact Or.inr (Or.inr ⟨ie, hie, Finset.mem_univ _, hs_ie.trans hside_p.symm,
        h_ieg.trans hside_p.symm⟩)
  cases s
  · simp only [Bool.false_eq_true, ↓reduceIte] at hcond ⊢
    refine {
      hp_v := hp_in, ha_not_v := hb_out, hc_not_v := ha_out
      ha_q := Finset.mem_univ _, hp_q := Finset.mem_univ _, hc_q := Finset.mem_univ _
      h_vqa := hside_b.trans hside_p.symm
      h_vqc := hside_a.trans hside_p.symm
      h_vap := by
        rw [orientSign_swap23 (orient_w_S_S_ne hP Tv hbp_ne.symm), hpb, hside_p]; rfl
      h_vpc := by
        rw [orientSign_swap23 (orient_w_S_S_ne hP Tv hap_ne), hap, hside_p]; rfl
      h_cross_ac := by
        unfold oppSideBool at hcross ⊢
        rw [orientSign_swap12 (orient_S_S_w_ne hP hab_ne Tv),
            orientSign_swap12 (orient_S_S_S_ne hP hab_ne hbp_ne hap_ne)]
        simpa using hcross
      h_cond_iv := hcond
    }
  · simp only [↓reduceIte] at hcond ⊢
    exact {
      hp_v := hp_in, ha_not_v := ha_out, hc_not_v := hb_out
      ha_q := Finset.mem_univ _, hp_q := Finset.mem_univ _, hc_q := Finset.mem_univ _
      h_vqa := hside_a.trans hside_p.symm
      h_vqc := hside_b.trans hside_p.symm
      h_vap := hap.trans hside_p.symm
      h_vpc := hpb.trans hside_p.symm
      h_cross_ac := hcross
      h_cond_iv := hcond
    }

/-- If any hull edge `(i, i + 1)` faces `w Tv` (`orientSign (S i) (S (i + 1)) (w Tv) = false`),
    then `w Tv` lies outside `convexHull S` and admits `VisibleContour (m := 4) S (w Tv)`. -/
lemma exists_vc_of_facing_edge {P : Set (ℝ × ℝ)} {S : Fin 7 → ℝ × ℝ} {w : Finset (Fin 7) → ℝ × ℝ}
    (hP : ShatteredSimplePolygon P S w) (hccw : CCWConvexSeven S)
    {Tv : Finset (Fin 7)} {i₀ : Fin 7}
    (hface : orientSign (S i₀) (S (i₀ + 1)) (w Tv) = false) :
    Nonempty (VisibleContour (m := 4) S (w Tv)) := by
  have hi_ne : i₀ ≠ i₀ + 1 := fin7_ne_succ i₀
  have hneg : orient2D (S i₀) (S (i₀ + 1)) (w Tv) < 0 :=
    (orientSign_eq_false_iff_of_ne_zero (orient_S_S_w_ne hP hi_ne Tv)).mp hface
  have hconv_half : Convex ℝ {x : ℝ × ℝ | 0 ≤ orient2D (S i₀) (S (i₀ + 1)) x} := by
    intro x hx y hy α β hα hβ hαβ
    dsimp at hx hy ⊢
    have hid : orient2D (S i₀) (S (i₀ + 1)) (α • x + β • y) =
        α * orient2D (S i₀) (S (i₀ + 1)) x + β * orient2D (S i₀) (S (i₀ + 1)) y := by
      unfold orient2D
      simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
      linear_combination ((S i₀).2 * (S (i₀ + 1)).1 - (S i₀).1 * (S (i₀ + 1)).2) * hαβ
    rw [hid]
    exact add_nonneg (mul_nonneg hα hx) (mul_nonneg hβ hy)
  have hout : w Tv ∉ convexHull ℝ (((Finset.univ : Finset (Fin 7)).image S : Finset (ℝ × ℝ)) : Set (ℝ × ℝ)) := by
    intro hmem
    have hnn : 0 ≤ orient2D (S i₀) (S (i₀ + 1)) (w Tv) := by
      refine convexHull_min (fun p hp => ?_) hconv_half hmem
      rcases Finset.mem_image.mp hp with ⟨j, _, rfl⟩
      dsimp
      by_cases hj0 : j = i₀
      · subst hj0; exact le_of_eq (by unfold orient2D; ring)
      · by_cases hj1 : j = i₀ + 1
        · subst hj1; exact le_of_eq (by unfold orient2D; ring)
        · exact le_of_lt (strictConvexCCWPoly_of_ccwConvexSeven hccw i₀ j hj0 hj1)
    linarith
  exact exists_visibleContour (m := 4) S (strictConvexCCWPoly_of_ccwConvexSeven hccw) hP.s_inj
    hout (fun i j hij => orient_S_S_w_ne hP hij Tv)

/-- Exact characterization of facing edges under `vc : VisibleContour (m := 4) S (w Tv)`:
    `orientSign (S u) (S (u + 1)) (w Tv) = false ↔ (u - vc.i_max).val < vc.d_near`. -/
lemma vc_facing_iff {P : Set (ℝ × ℝ)} {S : Fin 7 → ℝ × ℝ} {w : Finset (Fin 7) → ℝ × ℝ}
    (hP : ShatteredSimplePolygon P S w) {Tv : Finset (Fin 7)}
    (vc : VisibleContour (m := 4) S (w Tv)) (u : Fin 7) :
    orientSign (S u) (S (u + 1)) (w Tv) = false ↔ (u - vc.i_max).val < vc.d_near := by
  let k := (u - vc.i_max).val
  have hk7 : k < 7 := (u - vc.i_max).isLt
  have hu_eq : finShift vc.i_max k = u := finShift_sub vc.i_max u
  have hu1_eq : finShift vc.i_max (k + 1) = u + 1 := by
    rw [← finShift_succ (by decide : 2 ≤ 7) vc.i_max k, hu_eq]
  have hne : u ≠ u + 1 := fin7_ne_succ u
  constructor
  · intro hf
    have hneg : orient2D (S u) (S (u + 1)) (w Tv) < 0 :=
      (orientSign_eq_false_iff_of_ne_zero (orient_S_S_w_ne hP hne Tv)).mp hf
    by_contra hge
    have hpos := (vc.h_far_nofacing k (Nat.le_of_not_lt hge) hk7).1
    rw [hu_eq, hu1_eq] at hpos
    linarith
  · intro hlt
    have hneg := (vc.h_near_face k hlt).1
    rw [hu_eq, hu1_eq] at hneg
    exact (orientSign_eq_false_iff _ _ _).mpr (le_of_lt hneg)

/-- Alternating signs `(s, !s, s, !s)` around a CCW quadrilateral `(x, u, y, z)` on `line(w Tv, w univ)`
    are impossible. -/
lemma quad_line_sep_false {P : Set (ℝ × ℝ)} {S : Fin 7 → ℝ × ℝ} {w : Finset (Fin 7) → ℝ × ℝ}
    (hP : ShatteredSimplePolygon P S w) (hccw : CCWConvexSeven S)
    {Tv : Finset (Fin 7)} (hTv : Tv ≠ Finset.univ)
    {x u y z : Fin 7} {s : Bool}
    (h1 : 0 < (u - x).val) (h2 : (u - x).val < (y - x).val) (h3 : (y - x).val < (z - x).val)
    (hx : orientSign (w Tv) (w Finset.univ) (S x) = s)
    (hy : orientSign (w Tv) (w Finset.univ) (S y) = s)
    (hu : orientSign (w Tv) (w Finset.univ) (S u) = !s)
    (hz : orientSign (w Tv) (w Finset.univ) (S z) = !s) : False := by
  have c_xuy : 0 < orient2D (S x) (S u) (S y) := orient2D_pos_of_ccw hccw h1 h2
  have c_yzx : 0 < orient2D (S y) (S z) (S x) := by
    have hp := orient2D_pos_of_ccw hccw (lt_trans h1 h2) h3
    have hid : orient2D (S y) (S z) (S x) = orient2D (S x) (S y) (S z) := by unfold orient2D; ring
    linarith
  obtain ⟨c1, c2⟩ := fin7_quad_sub x u y z h1 h2 h3
  have c_uyz : 0 < orient2D (S u) (S y) (S z) := orient2D_pos_of_ccw hccw c1 c2
  have c_zxu : 0 < orient2D (S z) (S x) (S u) := by
    have hp := orient2D_pos_of_ccw hccw h1 (lt_trans h2 h3)
    have hid : orient2D (S z) (S x) (S u) = orient2D (S x) (S u) (S z) := by unfold orient2D; ring
    linarith
  have hid : orient2D (S u) (S y) (S z) * orient2D (w Tv) (w Finset.univ) (S x) +
      orient2D (S z) (S x) (S u) * orient2D (w Tv) (w Finset.univ) (S y) =
      orient2D (S y) (S z) (S x) * orient2D (w Tv) (w Finset.univ) (S u) +
      orient2D (S x) (S u) (S y) * orient2D (w Tv) (w Finset.univ) (S z) := by
    unfold orient2D; ring
  cases s
  · simp only [Bool.not_false] at hu hz
    have lx := (orientSign_eq_false_iff_of_ne_zero (orient_w_w_S_ne hP hTv x)).mp hx
    have ly := (orientSign_eq_false_iff_of_ne_zero (orient_w_w_S_ne hP hTv y)).mp hy
    have lu := (orientSign_eq_true_iff _ _ _).mp hu
    have lz := (orientSign_eq_true_iff _ _ _).mp hz
    nlinarith
  · simp only [Bool.not_true] at hu hz
    have lx := (orientSign_eq_true_iff _ _ _).mp hx
    have ly := (orientSign_eq_true_iff _ _ _).mp hy
    have lu := (orientSign_eq_false_iff_of_ne_zero (orient_w_w_S_ne hP hTv u)).mp hu
    have lz := (orientSign_eq_false_iff_of_ne_zero (orient_w_w_S_ne hP hTv z)).mp hz
    nlinarith

/-- If both tangent vertices `vc.i_max` and `vc.i_min` lie on side `s` of `line(w Tv, w univ)`,
    then **every** vertex `z : Fin 7` lies on side `s` of `line(w Tv, w univ)`. -/
lemma vc_all_side_of_tangents {P : Set (ℝ × ℝ)} {S : Fin 7 → ℝ × ℝ} {w : Finset (Fin 7) → ℝ × ℝ}
    (hP : ShatteredSimplePolygon P S w)
    {Tv : Finset (Fin 7)} (hTv : Tv ≠ Finset.univ)
    (vc : VisibleContour (m := 4) S (w Tv)) {s : Bool}
    (hmax : orientSign (w Tv) (w Finset.univ) (S vc.i_max) = s)
    (hmin : orientSign (w Tv) (w Finset.univ) (S vc.i_min) = s)
    (z : Fin 7) :
    orientSign (w Tv) (w Finset.univ) (S z) = s := by
  by_cases hz_min : z = vc.i_min
  · rwa [hz_min]
  · by_cases hz_max : z = vc.i_max
    · rwa [hz_max]
    · have hmin_lt : vc.slope vc.i_min < vc.slope z :=
        lt_of_le_of_ne (vc.h_extrema z).1 (fun h => hz_min (vc.h_slope_inj h).symm)
      have hlt_max : vc.slope z < vc.slope vc.i_max :=
        lt_of_le_of_ne (vc.h_extrema z).2 (fun h => hz_max (vc.h_slope_inj h))
      have hlt_mm : vc.slope vc.i_min < vc.slope vc.i_max := lt_trans hmin_lt hlt_max
      have o1 : 0 < orient2D (w Tv) (S vc.i_min) (S z) := (vc.h_orient vc.i_min z).mpr hmin_lt
      have o2 : 0 < orient2D (w Tv) (S z) (S vc.i_max) := (vc.h_orient z vc.i_max).mpr hlt_max
      have o3 : 0 < orient2D (w Tv) (S vc.i_min) (S vc.i_max) :=
        (vc.h_orient vc.i_min vc.i_max).mpr hlt_mm
      have hpl := plucker_around_origin (w Tv) (S vc.i_min) (w Finset.univ) (S z) (S vc.i_max)
      have hswap : orient2D (w Tv) (S vc.i_min) (w Finset.univ) =
          -orient2D (w Tv) (w Finset.univ) (S vc.i_min) := by unfold orient2D; ring
      rw [hswap] at hpl
      cases s
      · have lmax := (orientSign_eq_false_iff_of_ne_zero (orient_w_w_S_ne hP hTv vc.i_max)).mp hmax
        have lmin := (orientSign_eq_false_iff_of_ne_zero (orient_w_w_S_ne hP hTv vc.i_min)).mp hmin
        have hneg : orient2D (w Tv) (w Finset.univ) (S z) < 0 := by nlinarith
        exact (orientSign_eq_false_iff _ _ _).mpr (le_of_lt hneg)
      · have lmax := (orientSign_eq_true_iff _ _ _).mp hmax
        have lmin := (orientSign_eq_true_iff _ _ _).mp hmin
        have hpos : 0 < orient2D (w Tv) (w Finset.univ) (S z) := by nlinarith
        exact (orientSign_eq_true_iff _ _ _).mpr hpos

/-- When `S` lies strictly on one side `s` of `line(w Tv, w univ)` (or even when `(a, p, b)` lies on side `s`
    with `(a, p, b)` CCW), `w Tv` cannot lie inside `△(S a, S p, S b)`. In particular, if all 7 vertices
    lie on side `s`, at least one hull edge `(i, i + 1)` faces `w Tv`. -/
lemma not_in_tri_of_same_line_side {P : Set (ℝ × ℝ)} {S : Fin 7 → ℝ × ℝ} {w : Finset (Fin 7) → ℝ × ℝ}
    (hP : ShatteredSimplePolygon P S w)
    {Tv : Finset (Fin 7)} (hTv : Tv ≠ Finset.univ)
    {a p b : Fin 7} {s : Bool}
    (ha : orientSign (w Tv) (w Finset.univ) (S a) = s)
    (hp : orientSign (w Tv) (w Finset.univ) (S p) = s)
    (hb : orientSign (w Tv) (w Finset.univ) (S b) = s) :
    ¬ (0 < orient2D (S a) (S p) (w Tv) ∧
       0 < orient2D (S p) (S b) (w Tv) ∧
       0 < orient2D (S b) (S a) (w Tv)) := by
  rintro ⟨t1, t2, t3⟩
  have hid : orient2D (S a) (S p) (w Tv) * orient2D (w Tv) (w Finset.univ) (S b) +
      orient2D (S p) (S b) (w Tv) * orient2D (w Tv) (w Finset.univ) (S a) +
      orient2D (S b) (S a) (w Tv) * orient2D (w Tv) (w Finset.univ) (S p) = 0 := by
    unfold orient2D; ring
  cases s
  · have la := (orientSign_eq_false_iff_of_ne_zero (orient_w_w_S_ne hP hTv a)).mp ha
    have lp := (orientSign_eq_false_iff_of_ne_zero (orient_w_w_S_ne hP hTv p)).mp hp
    have lb := (orientSign_eq_false_iff_of_ne_zero (orient_w_w_S_ne hP hTv b)).mp hb
    nlinarith
  · have la := (orientSign_eq_true_iff _ _ _).mp ha
    have lp := (orientSign_eq_true_iff _ _ _).mp hp
    have lb := (orientSign_eq_true_iff _ _ _).mp hb
    nlinarith

lemma exists_facing_edge_of_all_same_side {P : Set (ℝ × ℝ)} {S : Fin 7 → ℝ × ℝ} {w : Finset (Fin 7) → ℝ × ℝ}
    (hP : ShatteredSimplePolygon P S w)
    {Tv : Finset (Fin 7)} (hTv : Tv ≠ Finset.univ) {s : Bool}
    (hall : ∀ z : Fin 7, orientSign (w Tv) (w Finset.univ) (S z) = s) :
    ∃ i : Fin 7, orientSign (S i) (S (i + 1)) (w Tv) = false := by
  by_contra hnone
  push Not at hnone
  have hall_t : ∀ i : Fin 7, 0 < orient2D (S i) (S (i + 1)) (w Tv) := fun i =>
    (orientSign_eq_true_iff _ _ _).mp (Bool.eq_true_of_not_eq_false (hnone i))
  by_cases h02 : 0 < orient2D (S 0) (S 2) (w Tv)
  · by_cases h04 : 0 < orient2D (S 0) (S 4) (w Tv)
    · by_cases h05 : 0 < orient2D (S 0) (S 5) (w Tv)
      · exact not_in_tri_of_same_line_side hP hTv (hall 0) (hall 5) (hall 6)
          ⟨h05, hall_t 5, hall_t 6⟩
      · have h50 : 0 < orient2D (S 5) (S 0) (w Tv) := by
          have hne := orient_S_S_w_ne hP (by decide : (0 : Fin 7) ≠ 5) Tv
          rw [orient2D_swap12]; linarith [lt_of_le_of_ne (not_lt.mp h05) hne]
        exact not_in_tri_of_same_line_side hP hTv (hall 0) (hall 4) (hall 5)
          ⟨h04, hall_t 4, h50⟩
    · have h40 : 0 < orient2D (S 4) (S 0) (w Tv) := by
        have hne := orient_S_S_w_ne hP (by decide : (0 : Fin 7) ≠ 4) Tv
        rw [orient2D_swap12]; linarith [lt_of_le_of_ne (not_lt.mp h04) hne]
      by_cases h03 : 0 < orient2D (S 0) (S 3) (w Tv)
      · exact not_in_tri_of_same_line_side hP hTv (hall 0) (hall 3) (hall 4)
          ⟨h03, hall_t 3, h40⟩
      · have h30 : 0 < orient2D (S 3) (S 0) (w Tv) := by
          have hne := orient_S_S_w_ne hP (by decide : (0 : Fin 7) ≠ 3) Tv
          rw [orient2D_swap12]; linarith [lt_of_le_of_ne (not_lt.mp h03) hne]
        exact not_in_tri_of_same_line_side hP hTv (hall 0) (hall 2) (hall 3)
          ⟨h02, hall_t 2, h30⟩
  · have h20 : 0 < orient2D (S 2) (S 0) (w Tv) := by
      have hne := orient_S_S_w_ne hP (by decide : (0 : Fin 7) ≠ 2) Tv
      rw [orient2D_swap12]; linarith [lt_of_le_of_ne (not_lt.mp h02) hne]
    exact not_in_tri_of_same_line_side hP hTv (hall 0) (hall 1) (hall 2)
      ⟨hall_t 0, hall_t 1, h20⟩

/-- If `vc : VisibleContour (m := 4) S (w Tv)` has `(vc.i_max - a).val < (b - a).val` and no inner vertex
    `finShift vc.i_max k` (`0 < k < vc.d_near`) equals `b`, then every facing edge lies in `[a .. b]`,
    `(vc.i_min - a).val ≤ (b - a).val`, and every chord `(c, d)` along the far arc `[b .. a]`
    satisfies `orientSign (S c) (S d) (w Tv) = true`. -/
lemma vc_confined_to_chain {P : Set (ℝ × ℝ)} {S : Fin 7 → ℝ × ℝ} {w : Finset (Fin 7) → ℝ × ℝ}
    (hP : ShatteredSimplePolygon P S w)
    {Tv : Finset (Fin 7)} (vc : VisibleContour (m := 4) S (w Tv))
    {a b : Fin 7} (hmax_in : (vc.i_max - a).val < (b - a).val)
    (hno_b : ∀ k : ℕ, 0 < k → k < vc.d_near → finShift vc.i_max k ≠ b) :
    (vc.i_min - a).val = (vc.i_max - a).val + vc.d_near ∧
    (vc.i_min - a).val ≤ (b - a).val ∧
    (∀ u : Fin 7, orientSign (S u) (S (u + 1)) (w Tv) = false ↔
      (vc.i_max - a).val ≤ (u - a).val ∧ (u - a).val < (vc.i_min - a).val) ∧
    (∀ c d : Fin 7, c ≠ d → (b - a).val ≤ (c - a).val →
      (c - a).val + (d - c).val ≤ 7 →
      orientSign (S c) (S d) (w Tv) = true) := by
  have hba_lt7 : (b - a).val < 7 := (b - a).isLt
  have hstep : ∀ k : ℕ, k ≤ vc.d_near →
      (finShift vc.i_max k - a).val = (vc.i_max - a).val + k ∧
      (k < vc.d_near → (finShift vc.i_max k - a).val < (b - a).val) := by
    intro k hk
    induction k with
    | zero =>
      rw [finShift_zero]
      exact ⟨by omega, fun _ => hmax_in⟩
    | succ k ih =>
      obtain ⟨heq_k, hlt_k⟩ := ih (by omega)
      have hlt_b : (finShift vc.i_max k - a).val < (b - a).val := hlt_k (by omega)
      have hsucc_eq : finShift vc.i_max (k + 1) = finShift vc.i_max k + 1 :=
        (finShift_succ (by decide : 2 ≤ 7) vc.i_max k).symm
      have hval_add1 : ((finShift vc.i_max k + 1) - a).val = (finShift vc.i_max k - a).val + 1 :=
        fin7_step_val (finShift vc.i_max k) a (lt_of_lt_of_le hlt_b (Nat.le_of_lt_succ hba_lt7))
      rw [hsucc_eq, hval_add1, heq_k]
      refine ⟨by omega, fun hk1_lt => ?_⟩
      have hne_b : finShift vc.i_max (k + 1) ≠ b := hno_b (k + 1) (by omega) hk1_lt
      have hval_ne : ((finShift vc.i_max k + 1) - a).val ≠ (b - a).val := by
        rw [← hsucc_eq]
        exact fun hv => hne_b (sub_left_injective (Fin.ext hv))
      rw [hval_add1, heq_k] at hval_ne
      omega
  have hmin_le : (vc.i_min - a).val ≤ (b - a).val := by
    rw [← vc.hmin_eq]
    have ⟨heq_d, _⟩ := hstep vc.d_near le_rfl
    by_cases hd0 : vc.d_near = 1
    · rw [hd0] at heq_d ⊢; rw [heq_d]; exact Nat.succ_le_of_lt hmax_in
    · have hpos := vc.hd_pos
      have ⟨heq_dm1, hlt_dm1⟩ := hstep (vc.d_near - 1) (by omega)
      have hlt' := hlt_dm1 (by omega)
      have h1 : (vc.i_max - a).val + vc.d_near = ((vc.i_max - a).val + (vc.d_near - 1)) + 1 := by omega
      rw [heq_d, h1, ← heq_dm1]
      exact Nat.succ_le_of_lt hlt'
  have ⟨heq_d, _⟩ := hstep vc.d_near le_rfl
  rw [vc.hmin_eq] at heq_d
  have hface_iff : ∀ u : Fin 7, orientSign (S u) (S (u + 1)) (w Tv) = false ↔
      (vc.i_max - a).val ≤ (u - a).val ∧ (u - a).val < (vc.i_min - a).val := by
    intro u
    rw [vc_facing_iff hP vc u]
    constructor
    · intro hk_lt
      have hu_sh : finShift vc.i_max (u - vc.i_max).val = u := finShift_sub vc.i_max u
      have ⟨heq_u, _⟩ := hstep (u - vc.i_max).val (le_of_lt hk_lt)
      rw [hu_sh] at heq_u
      exact ⟨by rw [heq_u]; exact Nat.le_add_right _ _,
        by rw [heq_u, heq_d]; exact Nat.add_lt_add_left hk_lt _⟩
    · rintro ⟨hlo, hhi⟩
      have hu_diff := fin7_diff_of_lt a vc.i_max u hlo
      rw [hu_diff]
      have hhi' : (u - a).val < (vc.i_max - a).val + vc.d_near :=
        calc (u - a).val < (vc.i_min - a).val := hhi
          _ = (vc.i_max - a).val + vc.d_near := heq_d
      exact Nat.sub_lt_left_of_lt_add hlo hhi'
  refine ⟨heq_d, hmin_le, hface_iff, fun c d hcd hbc hsum => ?_⟩
  have hc_sub_eq : (c - vc.i_max).val = (c - a).val - (vc.i_max - a).val :=
    fin7_diff_of_lt a vc.i_max c (le_of_lt (lt_of_lt_of_le hmax_in hbc))
  have hk_c_ge : vc.d_near ≤ (c - vc.i_max).val := by omega
  by_cases hd_max : d = vc.i_max
  · rw [hd_max] at hcd ⊢
    have hlt_sl : vc.slope c < vc.slope vc.i_max :=
      lt_of_le_of_ne (vc.h_extrema c).2 (fun h => hcd (vc.h_slope_inj h))
    have hpos : 0 < orient2D (w Tv) (S c) (S vc.i_max) := (vc.h_orient c vc.i_max).mpr hlt_sl
    have hid : orient2D (S c) (S vc.i_max) (w Tv) = orient2D (w Tv) (S c) (S vc.i_max) := by
      unfold orient2D; ring
    exact (orientSign_eq_true_iff _ _ _).mpr (by linarith)
  · have hk_cd : (c - vc.i_max).val < (d - vc.i_max).val := by
      rcases fin7_sum_step a c d hcd hsum with hlt_cd | ⟨_, hda⟩
      · have hd_sub_eq : (d - vc.i_max).val = (d - a).val - (vc.i_max - a).val :=
          fin7_diff_of_lt a vc.i_max d (le_of_lt (lt_trans (lt_of_lt_of_le hmax_in hbc) hlt_cd))
        omega
      · have hm_pos : 0 < (vc.i_max - a).val := by
          by_contra hz
          have hm0 : (vc.i_max - a).val = 0 := by omega
          exact hd_max (hda.trans (sub_eq_zero.mp (Fin.ext hm0)).symm)
        have hd_wrap := fin7_diff_wrap a vc.i_max d hm_pos hda
        have hc_lt7 : (c - a).val < 7 := (c - a).isLt
        omega
    have hsl_mono : ∀ k₁ k₂ : ℕ, vc.d_near ≤ k₁ → k₁ < k₂ → k₂ < 7 →
        vc.slope (finShift vc.i_max k₁) < vc.slope (finShift vc.i_max k₂) := by
      intro k₁ k₂ hge hlt hk2
      obtain ⟨t, rfl⟩ : ∃ t : ℕ, k₂ = k₁ + (t + 1) := ⟨k₂ - k₁ - 1, by omega⟩
      induction t with
      | zero => exact (vc.h_far_nofacing k₁ hge (by omega)).2
      | succ t ih =>
        exact lt_trans (ih (by omega) (by omega))
          (vc.h_far_nofacing (k₁ + (t + 1)) (by omega) (by omega)).2
    have hlt_sl := hsl_mono (c - vc.i_max).val (d - vc.i_max).val hk_c_ge hk_cd (d - vc.i_max).isLt
    rw [finShift_sub vc.i_max c, finShift_sub vc.i_max d] at hlt_sl
    have hpos : 0 < orient2D (w Tv) (S c) (S d) := (vc.h_orient c d).mpr hlt_sl
    have hid : orient2D (S c) (S d) (w Tv) = orient2D (w Tv) (S c) (S d) := by unfold orient2D; ring
    exact (orientSign_eq_true_iff _ _ _).mpr (by linarith)

/-- Along any contiguous arc `[x .. y]` (`0 < (y - x).val`) whose hull edges all face `w Tv`,
    `vc.slope y < vc.slope x` and therefore `orientSign (S x) (S y) (w Tv) = false`. -/
lemma facing_arc_chord_false {P : Set (ℝ × ℝ)} {S : Fin 7 → ℝ × ℝ} {w : Finset (Fin 7) → ℝ × ℝ}
    (hP : ShatteredSimplePolygon P S w) (hccw : CCWConvexSeven S)
    {Tv : Finset (Fin 7)} {x y : Fin 7}
    (hxy : 0 < (y - x).val)
    (hface : ∀ u : Fin 7, (u - x).val < (y - x).val →
      orientSign (S u) (S (u + 1)) (w Tv) = false) :
    orientSign (S x) (S y) (w Tv) = false := by
  have hx0 : orientSign (S x) (S (x + 1)) (w Tv) = false := hface x (by simp [hxy])
  obtain ⟨vc⟩ := exists_vc_of_facing_edge hP hccw hx0
  have hsl : ∀ t : ℕ, 0 < t → t ≤ (y - x).val →
      vc.slope (finShift x t) < vc.slope x := by
    intro t ht0 htle
    induction t with
    | zero => omega
    | succ t ih =>
      have ht_lt : (finShift x t - x).val < (y - x).val := by
        have ht7 : t < 7 := lt_of_lt_of_le (Nat.lt_of_succ_le htle) (le_of_lt (y - x).isLt)
        rw [finShift_eq_add x ht7, add_sub_cancel_left]
        exact Nat.lt_of_succ_le htle
      have hf_t := hface (finShift x t) ht_lt
      have hk_lt := (vc_facing_iff hP vc (finShift x t)).mp hf_t
      have hstep := (vc.h_near_face (finShift x t - vc.i_max).val hk_lt).2
      rw [← finShift_succ (by decide : 2 ≤ 7), finShift_sub,
          finShift_succ (by decide : 2 ≤ 7) x t] at hstep
      by_cases ht_z : t = 0
      · subst ht_z; simpa using hstep
      · exact lt_trans hstep (ih (by omega) (by omega))
  have hlt := hsl (y - x).val hxy le_rfl
  rw [finShift_sub x y] at hlt
  have hpos : 0 < orient2D (w Tv) (S y) (S x) := (vc.h_orient y x).mpr hlt
  have hneg : orient2D (S x) (S y) (w Tv) < 0 := by
    have : orient2D (S x) (S y) (w Tv) = -orient2D (w Tv) (S y) (S x) := by unfold orient2D; ring
    linarith
  exact (orientSign_eq_false_iff _ _ _).mpr (le_of_lt hneg)

end VCDim6

end
