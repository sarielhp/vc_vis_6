import Mathlib
import RootTask.PolygonDefs
import RootTask.PolygonEnclosureCore
import RootTask.NewEnclosureLemmas

open scoped Classical BigOperators
open Finset

noncomputable section

namespace ChirotopeSoundness

open PolygonCore NewEnclosure

/-!
# Sound Chirotope Reduction (`upper_8.tex` Section 8, Theorem 8.1)

Formalizes the real-point chirotope sign extraction `orientSign : (ℝ × ℝ) → (ℝ × ℝ) → (ℝ × ℝ) → Bool`
under general position (`NoThreeCollinear`) and proves the soundness bridge from
`ShatteredSimplePolygon P S w` + `NewEnclosureLemmas` to the Boolean clause schemas of Section 8:

1. **Chirotope Sign Extraction & Alternating Symmetry**:
   - `orientSign`, `NoThreeCollinear`, `pointSeq` (`X = S ∪ W₀`), and `noThreeCollinear_pointSeq`;
   - Exact cyclic invariance (`orientSign_cycle`, `orientSign_cycle2`) and odd-permutation
     sign negation (`orientSign_swap23`, `orientSign_swap12`, `orientSign_swap13`);
   - Exact Boolean geometric predicates (`sameSideBool`, `oppSideBool`, `segsCrossBool`,
     `inOpenTriSideBool`, `inOpenTriBool`, `strictConvexQuadSideBool`, `inConvexQuadSideBool`),
     including soundness of the omitted outer-triangle literal (`inOpenTri_and_orientSign_of_side`).
2. **Rank-3 Grassmann–Plücker `gp5` & 4-Point Affine Sign Exclusions (`(C1)`)**:
   - Polynomial identities `orient2D_gp5_identity` and `orient2D_affine4_identity`;
   - Full 16-clause parameterized `gp5` sign exclusions (`gp5_clause_pos`, `gp5_clause_neg`,
     `gp5_not_all_same_product_sign`, `gp5_concrete_pos_exclusion`, and indexed `NoThreeCollinear`
     forms across all 5 pivots) plus `affine4_sign_exclusion`, proved via `nlinarith`.
3. **Convex-Polygon (`conv(D)` / `conv(B)`) Interior Characterization & Carathéodory (`(C2)`–`(C3)`)**:
   - Exact equivalence `convex_poly_mem_convexHull_iff_orientSign` for strict CCW `(m + 3)`-gons;
   - Hull & interior chirotope extraction `shattered_hull_and_interior_orientSign_C2` (`conv(B)`
     and `conv(D)`) and 4-point Carathéodory triangle extraction `caratheodory_four_subset_C3`.
4. **Visibility Chord, Non-Certified Obstruction, Wedge & Two-Sided Separation (`(C4)`, `(C5)`, `(C8)`)**:
   - `vis_chord_one_side_of_misses` (visibility chord separation across `v -> q`);
   - `non_certified_obstruction_clause_C4` (`k ∈ D \ vis(w) => k ∉ int tri(w, s₁, s₂)`);
   - `exit_edge_cone_clause_C5` and `wedge_sep_clause_C5` (convex wedge separation);
   - `asymmetric_two_sided_clause_C8` (Lemma 2.12 4-literal forbidden sign clauses).
5. **Extended Enclosure Soundness Bridges (`(C10)` & `(C11)`)**:
   - `vis_SS` Round-1 chord (`vis_SS_chord_bool`) and Round-2 triangle clauses
     (`vis_SS_tri_vertex_clause`, `vis_SS_tri_vertex_omitted_outer_clause`, `vis_SS_tri_pair_clause`),
     plus multi-round inductive `(E1)`/`(E2)` closure soundness (`iterated_enclosure_soundness_C11`);
   - Crossed-segment triangle clauses `crossed_tri_T1_vertex_clause`, `crossed_tri_T1_pair_clause`,
     and `crossed_tri_T2_pair_clause`;
   - `N1` convex-quadrilateral & all 4 reflex-dart star-kernel positions (including omitted outer
     triangle literal and 4-cycle pair clauses): `n1_convex_quad_vertex_clause`,
     `n1_convex_quad_pair_clause`, `n1_dart_r0_clause`, `n1_dart_r1_clause`, `n1_dart_r2_clause`,
     `n1_dart_r3_clause`, and `four_cycle_dart_pair_clause`;
   - Unified Theorem 8.1 record `sound_chirotope_reduction`.
-/

/-! ## 1. Chirotope Sign Extraction, `NoThreeCollinear`, and Alternating Symmetry -/

/-- Boolean orientation sign predicate: `true` iff `(a, b, c)` makes a strict left turn (`orient2D a b c > 0`). -/
def orientSign (a b c : ℝ × ℝ) : Bool :=
  decide (0 < orient2D a b c)

/-- General position (`(G1)`) for an indexed planar point family `X : ι → ℝ × ℝ`:
    all indexed points are distinct and no three distinct indices are collinear. -/
def NoThreeCollinear {ι : Type*} (X : ι → ℝ × ℝ) : Prop :=
  Function.Injective X ∧
  ∀ i j k : ι, i ≠ j → j ≠ k → i ≠ k → orient2D (X i) (X j) (X k) ≠ 0

/-- Combined finite point sequence `X = S ∪ W₀ : Fin (n + k) → ℝ × ℝ` of Section 8. -/
def pointSeq {n k : ℕ} (S : Fin n → ℝ × ℝ) (w : Finset (Fin n) → ℝ × ℝ)
    (W₀ : Fin k ↪ Finset (Fin n)) : Fin (n + k) → ℝ × ℝ :=
  Fin.addCases S (fun j => w (W₀ j))

/-- Every ShatteredSimplePolygon under `(G1)–(G2)` induces `NoThreeCollinear` on `X = S ∪ W₀`. -/
theorem noThreeCollinear_pointSeq {n k : ℕ} {P : Set (ℝ × ℝ)}
    {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ}
    (hP : ShatteredSimplePolygon P S w) (W₀ : Fin k ↪ Finset (Fin n)) :
    NoThreeCollinear (pointSeq S w W₀) := by
  have hinj : Function.Injective (pointSeq S w W₀) := by
    intro u v huv
    refine Fin.addCases (fun i => Fin.addCases (fun i' h => ?_) (fun j' h => ?_) v)
      (fun j => Fin.addCases (fun i' h => ?_) (fun j' h => ?_) v) u huv
    · simp only [pointSeq, Fin.addCases_left] at h
      exact congrArg (Fin.castAdd k) (hP.s_inj h)
    · simp only [pointSeq, Fin.addCases_left, Fin.addCases_right] at h
      exact False.elim (hP.s_ne_w i (W₀ j') h)
    · simp only [pointSeq, Fin.addCases_left, Fin.addCases_right] at h
      exact False.elim (hP.s_ne_w i' (W₀ j) h.symm)
    · simp only [pointSeq, Fin.addCases_right] at h
      exact congrArg (Fin.natAdd n) (W₀.injective (hP.w_inj h))
  have hmem : ∀ u : Fin (n + k), pointSeq S w W₀ u ∈ Set.range S ∪ Set.range w := by
    refine Fin.addCases (fun i => ?_) (fun j => ?_)
    · simp only [pointSeq, Fin.addCases_left]; exact Or.inl ⟨i, rfl⟩
    · simp only [pointSeq, Fin.addCases_right]; exact Or.inr ⟨W₀ j, rfl⟩
  refine ⟨hinj, fun u v z huv hvz huz => ?_⟩
  exact hP.no_three_collinear _ _ _ (hmem u) (hmem v) (hmem z)
    (hinj.ne huv) (hinj.ne hvz) (hinj.ne huz)

@[simp]
lemma orientSign_eq_true_iff (a b c : ℝ × ℝ) :
    orientSign a b c = true ↔ 0 < orient2D a b c := by
  simp [orientSign]

@[simp]
lemma orientSign_eq_false_iff (a b c : ℝ × ℝ) :
    orientSign a b c = false ↔ orient2D a b c ≤ 0 := by
  simp [orientSign]

lemma orientSign_eq_false_iff_of_ne_zero {a b c : ℝ × ℝ} (h : orient2D a b c ≠ 0) :
    orientSign a b c = false ↔ orient2D a b c < 0 := by
  rw [orientSign_eq_false_iff]
  exact ⟨fun hle => lt_of_le_of_ne hle h, le_of_lt⟩

/-- Cyclic shift `(a, b, c) ↦ (b, c, a)` preserves `orientSign`. -/
lemma orientSign_cycle (a b c : ℝ × ℝ) :
    orientSign b c a = orientSign a b c := by
  unfold orientSign
  rw [orient2D_cycle]

/-- Double cyclic shift `(a, b, c) ↦ (c, a, b)` preserves `orientSign`. -/
lemma orientSign_cycle2 (a b c : ℝ × ℝ) :
    orientSign c a b = orientSign a b c := by
  rw [orientSign_cycle, orientSign_cycle]

/-- Odd transposition `(a, b, c) ↦ (a, c, b)` negates `orientSign` for non-collinear triples. -/
lemma orientSign_swap23 {a b c : ℝ × ℝ} (h : orient2D a b c ≠ 0) :
    orientSign a c b = !orientSign a b c := by
  cases hsb : orientSign a b c
  · have hlt : orient2D a b c < 0 := (orientSign_eq_false_iff_of_ne_zero h).mp hsb
    rw [Bool.not_false, orientSign_eq_true_iff, orient2D_swap23]
    linarith
  · have hgt : 0 < orient2D a b c := (orientSign_eq_true_iff a b c).mp hsb
    rw [Bool.not_true, orientSign_eq_false_iff, orient2D_swap23]
    linarith

/-- Odd transposition `(a, b, c) ↦ (b, a, c)` negates `orientSign` for non-collinear triples. -/
lemma orientSign_swap12 {a b c : ℝ × ℝ} (h : orient2D a b c ≠ 0) :
    orientSign b a c = !orientSign a b c := by
  have hid : orient2D b a c = orient2D a c b := by unfold orient2D; ring
  have hcb : orientSign b a c = orientSign a c b := by unfold orientSign; rw [hid]
  rw [hcb, orientSign_swap23 h]

/-- Odd transposition `(a, b, c) ↦ (c, b, a)` negates `orientSign` for non-collinear triples. -/
lemma orientSign_swap13 {a b c : ℝ × ℝ} (h : orient2D a b c ≠ 0) :
    orientSign c b a = !orientSign a b c := by
  have hid : orient2D c b a = orient2D a c b := by unfold orient2D; ring
  have hcb : orientSign c b a = orientSign a c b := by unfold orientSign; rw [hid]
  rw [hcb, orientSign_swap23 h]

lemma NoThreeCollinear.orientSign_swap23 {ι : Type*} {X : ι → ℝ × ℝ} (hX : NoThreeCollinear X)
    {i j k : ι} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    orientSign (X i) (X k) (X j) = !orientSign (X i) (X j) (X k) :=
  ChirotopeSoundness.orientSign_swap23 (hX.2 i j k hij hjk hik)

lemma NoThreeCollinear.orientSign_swap12 {ι : Type*} {X : ι → ℝ × ℝ} (hX : NoThreeCollinear X)
    {i j k : ι} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    orientSign (X j) (X i) (X k) = !orientSign (X i) (X j) (X k) :=
  ChirotopeSoundness.orientSign_swap12 (hX.2 i j k hij hjk hik)

lemma NoThreeCollinear.orientSign_swap13 {ι : Type*} {X : ι → ℝ × ℝ} (hX : NoThreeCollinear X)
    {i j k : ι} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    orientSign (X k) (X j) (X i) = !orientSign (X i) (X j) (X k) :=
  ChirotopeSoundness.orientSign_swap13 (hX.2 i j k hij hjk hik)

/-! ### General-Position Non-Collinearity Helpers on `ShatteredSimplePolygon` -/

section ShatteredGPHelpers

variable {n : ℕ} {P : Set (ℝ × ℝ)} {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ}

lemma orient_S_S_S_ne (hP : ShatteredSimplePolygon P S w)
    {a b c : Fin n} (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    orient2D (S a) (S b) (S c) ≠ 0 :=
  hP.no_three_collinear (S a) (S b) (S c)
    (Or.inl ⟨a, rfl⟩) (Or.inl ⟨b, rfl⟩) (Or.inl ⟨c, rfl⟩)
    (hP.s_inj.ne hab) (hP.s_inj.ne hbc) (hP.s_inj.ne hac)

lemma orient_S_S_w_ne (hP : ShatteredSimplePolygon P S w)
    {a b : Fin n} (hab : a ≠ b) (T : Finset (Fin n)) :
    orient2D (S a) (S b) (w T) ≠ 0 :=
  hP.no_three_collinear (S a) (S b) (w T)
    (Or.inl ⟨a, rfl⟩) (Or.inl ⟨b, rfl⟩) (Or.inr ⟨T, rfl⟩)
    (hP.s_inj.ne hab) (hP.s_ne_w b T) (hP.s_ne_w a T)

lemma orient_w_S_S_ne (hP : ShatteredSimplePolygon P S w)
    (T : Finset (Fin n)) {a b : Fin n} (hab : a ≠ b) :
    orient2D (w T) (S a) (S b) ≠ 0 :=
  hP.no_three_collinear (w T) (S a) (S b)
    (Or.inr ⟨T, rfl⟩) (Or.inl ⟨a, rfl⟩) (Or.inl ⟨b, rfl⟩)
    (hP.s_ne_w a T).symm (hP.s_inj.ne hab) (hP.s_ne_w b T).symm

lemma orient_S_w_S_ne (hP : ShatteredSimplePolygon P S w)
    {a b : Fin n} (hab : a ≠ b) (T : Finset (Fin n)) :
    orient2D (S a) (w T) (S b) ≠ 0 :=
  hP.no_three_collinear (S a) (w T) (S b)
    (Or.inl ⟨a, rfl⟩) (Or.inr ⟨T, rfl⟩) (Or.inl ⟨b, rfl⟩)
    (hP.s_ne_w a T) (hP.s_ne_w b T).symm (hP.s_inj.ne hab)

lemma orient_w_S_w_ne (hP : ShatteredSimplePolygon P S w)
    {T₁ T₂ : Finset (Fin n)} (hT : T₁ ≠ T₂) (a : Fin n) :
    orient2D (w T₁) (S a) (w T₂) ≠ 0 :=
  hP.no_three_collinear (w T₁) (S a) (w T₂)
    (Or.inr ⟨T₁, rfl⟩) (Or.inl ⟨a, rfl⟩) (Or.inr ⟨T₂, rfl⟩)
    (hP.s_ne_w a T₁).symm (hP.s_ne_w a T₂) (hP.w_inj.ne hT)

lemma orient_S_w_w_ne (hP : ShatteredSimplePolygon P S w)
    (a : Fin n) {T₁ T₂ : Finset (Fin n)} (hT : T₁ ≠ T₂) :
    orient2D (S a) (w T₁) (w T₂) ≠ 0 :=
  hP.no_three_collinear (S a) (w T₁) (w T₂)
    (Or.inl ⟨a, rfl⟩) (Or.inr ⟨T₁, rfl⟩) (Or.inr ⟨T₂, rfl⟩)
    (hP.s_ne_w a T₁) (hP.w_inj.ne hT) (hP.s_ne_w a T₂)

lemma orient_w_w_S_ne (hP : ShatteredSimplePolygon P S w)
    {T₁ T₂ : Finset (Fin n)} (hT : T₁ ≠ T₂) (a : Fin n) :
    orient2D (w T₁) (w T₂) (S a) ≠ 0 :=
  hP.no_three_collinear (w T₁) (w T₂) (S a)
    (Or.inr ⟨T₁, rfl⟩) (Or.inr ⟨T₂, rfl⟩) (Or.inl ⟨a, rfl⟩)
    (hP.w_inj.ne hT) (hP.s_ne_w a T₂).symm (hP.s_ne_w a T₁).symm

lemma orient_w_w_w_ne (hP : ShatteredSimplePolygon P S w)
    {T₁ T₂ T₃ : Finset (Fin n)} (h12 : T₁ ≠ T₂) (h23 : T₂ ≠ T₃) (h13 : T₁ ≠ T₃) :
    orient2D (w T₁) (w T₂) (w T₃) ≠ 0 :=
  hP.no_three_collinear (w T₁) (w T₂) (w T₃)
    (Or.inr ⟨T₁, rfl⟩) (Or.inr ⟨T₂, rfl⟩) (Or.inr ⟨T₃, rfl⟩)
    (hP.w_inj.ne h12) (hP.w_inj.ne h23) (hP.w_inj.ne h13)

end ShatteredGPHelpers

/-! ### Boolean Geometric Predicates & Exact Equivalences -/

/-- Boolean same-side test (`mk_same_side` in `gen_chiro_*.cpp`). -/
def sameSideBool (a b p q : ℝ × ℝ) : Bool :=
  orientSign a b p == orientSign a b q

/-- Boolean opposite-side test (`mk_eq(pos(a,b,p), -pos(a,b,q))` in `gen_chiro_*.cpp`). -/
def oppSideBool (a b p q : ℝ × ℝ) : Bool :=
  orientSign a b p != orientSign a b q

/-- Boolean proper segment crossing test (`mk_segs_cross` in `gen_chiro_*.cpp`). -/
def segsCrossBool (a b c d : ℝ × ℝ) : Bool :=
  oppSideBool a b c d && oppSideBool c d a b

/-- Boolean open-triangle containment for a fixed orientation sign `sd` (omitting `orientSign a b c`,
    matching `bulk_cegar_enclosure` and `find_violated_n1_cuts`). -/
def inOpenTriSideBool (sd : Bool) (p a b c : ℝ × ℝ) : Bool :=
  (orientSign a b p == sd) && (orientSign b c p == sd) && (orientSign c a p == sd)

/-- Unoriented open-triangle containment (`mk_in_int_tri_any` in `gen_chiro_*.cpp`). -/
def inOpenTriBool (p a b c : ℝ × ℝ) : Bool :=
  inOpenTriSideBool true p a b c || inOpenTriSideBool false p a b c

/-- Strict convex quadrilateral test for orientation `s` (`true` = CCW, `false` = CW). -/
def strictConvexQuadSideBool (s : Bool) (p₀ p₁ p₂ p₃ : ℝ × ℝ) : Bool :=
  (orientSign p₀ p₁ p₂ == s) && (orientSign p₁ p₂ p₃ == s) &&
  (orientSign p₂ p₃ p₀ == s) && (orientSign p₃ p₀ p₁ == s)

/-- Interior of convex quadrilateral test for orientation `s` (`true` = CCW, `false` = CW). -/
def inConvexQuadSideBool (s : Bool) (z p₀ p₁ p₂ p₃ : ℝ × ℝ) : Bool :=
  (orientSign p₀ p₁ z == s) && (orientSign p₁ p₂ z == s) &&
  (orientSign p₂ p₃ z == s) && (orientSign p₃ p₀ z == s)

lemma mul_pos_of_orientSign_eq {x₁ y₁ z₁ x₂ y₂ z₂ : ℝ × ℝ} {s : Bool}
    (h1 : orient2D x₁ y₁ z₁ ≠ 0) (h2 : orient2D x₂ y₂ z₂ ≠ 0)
    (hs1 : orientSign x₁ y₁ z₁ = s) (hs2 : orientSign x₂ y₂ z₂ = s) :
    0 < orient2D x₁ y₁ z₁ * orient2D x₂ y₂ z₂ := by
  cases s
  · exact mul_pos_of_neg_of_neg
      ((orientSign_eq_false_iff_of_ne_zero h1).mp hs1)
      ((orientSign_eq_false_iff_of_ne_zero h2).mp hs2)
  · exact mul_pos
      ((orientSign_eq_true_iff _ _ _).mp hs1)
      ((orientSign_eq_true_iff _ _ _).mp hs2)

lemma mul_neg_of_orientSign_opp {x₁ y₁ z₁ x₂ y₂ z₂ : ℝ × ℝ} {s : Bool}
    (h1 : orient2D x₁ y₁ z₁ ≠ 0) (h2 : orient2D x₂ y₂ z₂ ≠ 0)
    (hs1 : orientSign x₁ y₁ z₁ = s) (hs2 : orientSign x₂ y₂ z₂ = !s) :
    orient2D x₁ y₁ z₁ * orient2D x₂ y₂ z₂ < 0 := by
  cases s
  · exact mul_neg_of_neg_of_pos
      ((orientSign_eq_false_iff_of_ne_zero h1).mp hs1)
      ((orientSign_eq_true_iff _ _ _).mp hs2)
  · exact mul_neg_of_pos_of_neg
      ((orientSign_eq_true_iff _ _ _).mp hs1)
      ((orientSign_eq_false_iff_of_ne_zero h2).mp hs2)

lemma sameSideBool_iff_sameSide {a b p q : ℝ × ℝ}
    (hp : orient2D a b p ≠ 0) (hq : orient2D a b q ≠ 0) :
    sameSideBool a b p q = true ↔ SameSide a b p q := by
  unfold sameSideBool SameSide
  rw [beq_iff_eq]
  constructor
  · intro heq
    exact mul_pos_of_orientSign_eq hp hq rfl heq.symm
  · intro hmul
    cases hsp : orientSign a b p <;> cases hsq : orientSign a b q
    · rfl
    · have hp' := (orientSign_eq_false_iff_of_ne_zero hp).mp hsp
      have hq' := (orientSign_eq_true_iff a b q).mp hsq
      linarith [mul_neg_of_neg_of_pos hp' hq']
    · have hp' := (orientSign_eq_true_iff a b p).mp hsp
      have hq' := (orientSign_eq_false_iff_of_ne_zero hq).mp hsq
      linarith [mul_neg_of_pos_of_neg hp' hq']
    · rfl

private lemma bool_eq_not_of_ne {a b : Bool} (h : a ≠ b) : b = !a := by
  cases a <;> cases b <;> simp_all

lemma oppSideBool_iff_mul_neg {a b p q : ℝ × ℝ}
    (hp : orient2D a b p ≠ 0) (hq : orient2D a b q ≠ 0) :
    oppSideBool a b p q = true ↔ orient2D a b p * orient2D a b q < 0 := by
  unfold oppSideBool
  rw [bne_iff_ne]
  constructor
  · intro hne
    exact mul_neg_of_orientSign_opp hp hq rfl (bool_eq_not_of_ne hne)
  · intro hneg heq
    have hpos := mul_pos_of_orientSign_eq hp hq rfl heq.symm
    linarith

lemma segsCrossBool_iff_properCross {a b c d : ℝ × ℝ}
    (h1 : orient2D a b c ≠ 0) (h2 : orient2D a b d ≠ 0)
    (h3 : orient2D c d a ≠ 0) (h4 : orient2D c d b ≠ 0) :
    segsCrossBool a b c d = true ↔ ProperCross a b c d := by
  unfold segsCrossBool ProperCross
  rw [Bool.and_eq_true, oppSideBool_iff_mul_neg h1 h2, oppSideBool_iff_mul_neg h3 h4]

/-- Signed area decomposition `orient2D a b c = orient2D a b p + orient2D b c p + orient2D c a p`. -/
lemma orient2D_area_sum (a b c p : ℝ × ℝ) :
    orient2D a b c = orient2D a b p + orient2D b c p + orient2D c a p := by
  unfold orient2D; ring

/-- **Soundness of omitted outer-triangle literal** (`LOGIC_AUDIT.md` #2):
    If `inOpenTriSideBool sd p a b c = true` under non-collinearity of `(a,b,p)`, `(b,c,p)`, `(c,a,p)`,
    then `orient2D a b c ≠ 0`, `orientSign a b c = sd`, and `InOpenTri a b c p` all follow automatically. -/
lemma inOpenTri_and_orientSign_of_side {sd : Bool} {p a b c : ℝ × ℝ}
    (h1 : orient2D a b p ≠ 0) (h2 : orient2D b c p ≠ 0) (h3 : orient2D c a p ≠ 0)
    (hs : inOpenTriSideBool sd p a b c = true) :
    InOpenTri a b c p ∧ orient2D a b c ≠ 0 ∧ orientSign a b c = sd := by
  unfold inOpenTriSideBool at hs
  simp only [Bool.and_eq_true, beq_iff_eq] at hs
  rcases hs with ⟨⟨hs1, hs2⟩, hs3⟩
  have hsum := orient2D_area_sum a b c p
  cases sd
  · have hn1 := (orientSign_eq_false_iff_of_ne_zero h1).mp hs1
    have hn2 := (orientSign_eq_false_iff_of_ne_zero h2).mp hs2
    have hn3 := (orientSign_eq_false_iff_of_ne_zero h3).mp hs3
    have habc_neg : orient2D a b c < 0 := by linarith
    refine ⟨inOpenTri_perm_23 (inOpenTri_of_orient_pos ?_ ?_ ?_ ?_), ne_of_lt habc_neg,
      (orientSign_eq_false_iff a b c).mpr (le_of_lt habc_neg)⟩
    · rw [orient2D_swap23]; linarith
    · rw [show orient2D a c p = -orient2D c a p by unfold orient2D; ring]; linarith
    · rw [show orient2D c b p = -orient2D b c p by unfold orient2D; ring]; linarith
    · rw [show orient2D b a p = -orient2D a b p by unfold orient2D; ring]; linarith
  · have hp1 := (orientSign_eq_true_iff a b p).mp hs1
    have hp2 := (orientSign_eq_true_iff b c p).mp hs2
    have hp3 := (orientSign_eq_true_iff c a p).mp hs3
    have habc_pos : 0 < orient2D a b c := by linarith
    exact ⟨inOpenTri_of_orient_pos habc_pos hp1 hp2 hp3, ne_of_gt habc_pos,
      (orientSign_eq_true_iff a b c).mpr habc_pos⟩

/-- Exact equivalence between `inOpenTriBool p a b c = true` and `InOpenTri a b c p` under general position. -/
lemma inOpenTriBool_iff_inOpenTri {p a b c : ℝ × ℝ}
    (h1 : orient2D a b p ≠ 0) (h2 : orient2D b c p ≠ 0) (h3 : orient2D c a p ≠ 0) :
    inOpenTriBool p a b c = true ↔ InOpenTri a b c p := by
  unfold inOpenTriBool
  rw [Bool.or_eq_true]
  constructor
  · rintro (ht | hf)
    · exact (inOpenTri_and_orientSign_of_side h1 h2 h3 ht).1
    · exact (inOpenTri_and_orientSign_of_side h1 h2 h3 hf).1
  · intro htri
    rcases htri with ⟨μ₁, μ₂, μ₃, hμ1, hμ2, hμ3, hμsum, hp1, hp2⟩
    have hμ1_eq : μ₁ = 1 - μ₂ - μ₃ := by linarith
    have habp : orient2D a b p = μ₃ * orient2D a b c := by
      unfold orient2D; rw [hp1, hp2, hμ1_eq]; ring
    have hbcp : orient2D b c p = μ₁ * orient2D a b c := by
      unfold orient2D; rw [hp1, hp2, hμ1_eq]; ring
    have hcap : orient2D c a p = μ₂ * orient2D a b c := by
      unfold orient2D; rw [hp1, hp2, hμ1_eq]; ring
    have habc_ne : orient2D a b c ≠ 0 := by
      intro h0; rw [h0, mul_zero] at habp; exact h1 habp
    rcases lt_or_gt_of_ne habc_ne with hneg | hpos
    · right
      unfold inOpenTriSideBool
      simp only [Bool.and_eq_true, beq_iff_eq]
      exact ⟨⟨(orientSign_eq_false_iff a b p).mpr (by rw [habp]; nlinarith),
              (orientSign_eq_false_iff b c p).mpr (by rw [hbcp]; nlinarith)⟩,
             (orientSign_eq_false_iff c a p).mpr (by rw [hcap]; nlinarith)⟩
    · left
      unfold inOpenTriSideBool
      simp only [Bool.and_eq_true, beq_iff_eq]
      exact ⟨⟨(orientSign_eq_true_iff a b p).mpr (by rw [habp]; exact mul_pos hμ3 hpos),
              (orientSign_eq_true_iff b c p).mpr (by rw [hbcp]; exact mul_pos hμ1 hpos)⟩,
             (orientSign_eq_true_iff c a p).mpr (by rw [hcap]; exact mul_pos hμ2 hpos)⟩


/-! ## 2. Clause `(C1)`: Rank-3 Grassmann–Plücker `gp5` & 4-Point Affine Sign Exclusion -/

/-- **3-Term Rank-3 Grassmann–Plücker Polynomial Identity** on `ℝ × ℝ` at pivot `p`:
    `[p,a,b][p,c,d] - [p,a,c][p,b,d] + [p,a,d][p,b,c] = 0`. -/
lemma orient2D_gp5_identity (p a b c d : ℝ × ℝ) :
    orient2D p a b * orient2D p c d -
    orient2D p a c * orient2D p b d +
    orient2D p a d * orient2D p b c = 0 := by
  unfold orient2D; ring

/-- **4-Point Affine Determinant Identity** on `ℝ × ℝ`:
    `[b,c,d] - [a,c,d] + [a,b,d] - [a,b,c] = 0`. -/
lemma orient2D_affine4_identity (a b c d : ℝ × ℝ) :
    orient2D b c d - orient2D a c d + orient2D a b d - orient2D a b c = 0 := by
  unfold orient2D; ring

/-- **Grassmann–Plücker `gp5` Positive-Sum Sign Exclusion** (first 8 of the 16 CNF clauses per pivot in `add_gp`):
    For any `(s₁, s₂, s₃ : Bool)`, the three Plücker products cannot all be strictly positive. -/
theorem gp5_clause_pos {p a b c d : ℝ × ℝ}
    (h1 : orient2D p a b ≠ 0) (h2 : orient2D p c d ≠ 0)
    (h3 : orient2D p a c ≠ 0) (h4 : orient2D p b d ≠ 0)
    (h5 : orient2D p a d ≠ 0) (h6 : orient2D p b c ≠ 0)
    (s₁ s₂ s₃ : Bool) :
    ¬ (orientSign p a b = s₁ ∧ orientSign p c d = s₁ ∧
       orientSign p a c = s₂ ∧ orientSign p b d = !s₂ ∧
       orientSign p a d = s₃ ∧ orientSign p b c = s₃) := by
  rintro ⟨e1, e2, e3, e4, e5, e6⟩
  have hp1 := mul_pos_of_orientSign_eq h1 h2 e1 e2
  have hn2 := mul_neg_of_orientSign_opp h3 h4 e3 e4
  have hp3 := mul_pos_of_orientSign_eq h5 h6 e5 e6
  have hid := orient2D_gp5_identity p a b c d
  nlinarith

/-- **Grassmann–Plücker `gp5` Negative-Sum Sign Exclusion** (remaining 8 of the 16 CNF clauses per pivot in `add_gp`):
    For any `(s₁, s₂, s₃ : Bool)`, the three Plücker products cannot all be strictly negative. -/
theorem gp5_clause_neg {p a b c d : ℝ × ℝ}
    (h1 : orient2D p a b ≠ 0) (h2 : orient2D p c d ≠ 0)
    (h3 : orient2D p a c ≠ 0) (h4 : orient2D p b d ≠ 0)
    (h5 : orient2D p a d ≠ 0) (h6 : orient2D p b c ≠ 0)
    (s₁ s₂ s₃ : Bool) :
    ¬ (orientSign p a b = s₁ ∧ orientSign p c d = !s₁ ∧
       orientSign p a c = s₂ ∧ orientSign p b d = s₂ ∧
       orientSign p a d = s₃ ∧ orientSign p b c = !s₃) := by
  rintro ⟨e1, e2, e3, e4, e5, e6⟩
  have hn1 := mul_neg_of_orientSign_opp h1 h2 e1 e2
  have hp2 := mul_pos_of_orientSign_eq h3 h4 e3 e4
  have hn3 := mul_neg_of_orientSign_opp h5 h6 e5 e6
  have hid := orient2D_gp5_identity p a b c d
  nlinarith

/-- Compact parameter-free form of `gp5_clause_pos` & `gp5_clause_neg` on Boolean equality/inequality. -/
theorem gp5_not_unanimous_plucker_terms {p a b c d : ℝ × ℝ}
    (h1 : orient2D p a b ≠ 0) (h2 : orient2D p c d ≠ 0)
    (h3 : orient2D p a c ≠ 0) (h4 : orient2D p b d ≠ 0)
    (h5 : orient2D p a d ≠ 0) (h6 : orient2D p b c ≠ 0) :
    ¬ ((orientSign p a b == orientSign p c d) = true ∧
       (orientSign p a c != orientSign p b d) = true ∧
       (orientSign p a d == orientSign p b c) = true) ∧
    ¬ ((orientSign p a b != orientSign p c d) = true ∧
       (orientSign p a c == orientSign p b d) = true ∧
       (orientSign p a d != orientSign p b c) = true) := by
  refine ⟨?_, ?_⟩
  · rintro ⟨h12, h34, h56⟩
    rw [beq_iff_eq] at h12 h56
    rw [bne_iff_ne] at h34
    exact gp5_clause_pos h1 h2 h3 h4 h5 h6
      (orientSign p a b) (orientSign p a c) (orientSign p a d)
      ⟨rfl, h12.symm, rfl, bool_eq_not_of_ne h34, rfl, h56.symm⟩
  · rintro ⟨h12, h34, h56⟩
    rw [bne_iff_ne] at h12 h56
    rw [beq_iff_eq] at h34
    exact gp5_clause_neg h1 h2 h3 h4 h5 h6
      (orientSign p a b) (orientSign p a c) (orientSign p a d)
      ⟨rfl, bool_eq_not_of_ne h12, rfl, h34.symm, rfl, bool_eq_not_of_ne h56⟩

/-- Concrete unparameterized instance (`s₁ = s₂ = s₃ = true` at pivot `p₀`):
    `¬ (s012 ∧ s034 ∧ s013 ∧ ¬s024 ∧ s014 ∧ s023)`. -/
theorem gp5_concrete_pos_exclusion {p₀ p₁ p₂ p₃ p₄ : ℝ × ℝ}
    (h012 : orient2D p₀ p₁ p₂ ≠ 0) (h034 : orient2D p₀ p₃ p₄ ≠ 0)
    (h013 : orient2D p₀ p₁ p₃ ≠ 0) (h024 : orient2D p₀ p₂ p₄ ≠ 0)
    (h014 : orient2D p₀ p₁ p₄ ≠ 0) (h023 : orient2D p₀ p₂ p₃ ≠ 0) :
    ¬ (orientSign p₀ p₁ p₂ = true ∧ orientSign p₀ p₃ p₄ = true ∧
       orientSign p₀ p₁ p₃ = true ∧ orientSign p₀ p₂ p₄ = false ∧
       orientSign p₀ p₁ p₄ = true ∧ orientSign p₀ p₂ p₃ = true) :=
  gp5_clause_pos h012 h034 h013 h024 h014 h023 true true true

/-- Indexed `NoThreeCollinear` form of `gp5` (Clause `(C1)`) for any 5 distinct indices `(ip, ia, ib, ic, id)`. -/
theorem NoThreeCollinear.gp5_clauses {ι : Type*} {X : ι → ℝ × ℝ} (hX : NoThreeCollinear X)
    {ip ia ib ic id_ : ι}
    (hpa : ip ≠ ia) (hpb : ip ≠ ib) (hpc : ip ≠ ic) (hpd : ip ≠ id_)
    (hab : ia ≠ ib) (hac : ia ≠ ic) (had : ia ≠ id_)
    (hbc : ib ≠ ic) (hbd : ib ≠ id_) (hcd : ic ≠ id_)
    (s₁ s₂ s₃ : Bool) :
    ¬ (orientSign (X ip) (X ia) (X ib) = s₁ ∧ orientSign (X ip) (X ic) (X id_) = s₁ ∧
       orientSign (X ip) (X ia) (X ic) = s₂ ∧ orientSign (X ip) (X ib) (X id_) = !s₂ ∧
       orientSign (X ip) (X ia) (X id_) = s₃ ∧ orientSign (X ip) (X ib) (X ic) = s₃) ∧
    ¬ (orientSign (X ip) (X ia) (X ib) = s₁ ∧ orientSign (X ip) (X ic) (X id_) = !s₁ ∧
       orientSign (X ip) (X ia) (X ic) = s₂ ∧ orientSign (X ip) (X ib) (X id_) = s₂ ∧
       orientSign (X ip) (X ia) (X id_) = s₃ ∧ orientSign (X ip) (X ib) (X ic) = !s₃) :=
  ⟨gp5_clause_pos
      (hX.2 ip ia ib hpa hab hpb) (hX.2 ip ic id_ hpc hcd hpd)
      (hX.2 ip ia ic hpa hac hpc) (hX.2 ip ib id_ hpb hbd hpd)
      (hX.2 ip ia id_ hpa had hpd) (hX.2 ip ib ic hpb hbc hpc) s₁ s₂ s₃,
   gp5_clause_neg
      (hX.2 ip ia ib hpa hab hpb) (hX.2 ip ic id_ hpc hcd hpd)
      (hX.2 ip ia ic hpa hac hpc) (hX.2 ip ib id_ hpb hbd hpd)
      (hX.2 ip ia id_ hpa had hpd) (hX.2 ip ib ic hpb hbc hpc) s₁ s₂ s₃⟩

/-- **4-Point Affine Sign Exclusion** (`add_affine4`):
    In `ℝ²`, the alternating orientation signs `(s, !s, s, !s)` on `(bcd, acd, abd, abc)` are impossible. -/
theorem affine4_sign_exclusion {a b c d : ℝ × ℝ}
    (h1 : orient2D b c d ≠ 0) (h2 : orient2D a c d ≠ 0)
    (h3 : orient2D a b d ≠ 0) (h4 : orient2D a b c ≠ 0)
    (s : Bool) :
    ¬ (orientSign b c d = s ∧ orientSign a c d = !s ∧
       orientSign a b d = s ∧ orientSign a b c = !s) := by
  rintro ⟨e1, e2, e3, e4⟩
  have hid := orient2D_affine4_identity a b c d
  cases s
  · have n1 := (orientSign_eq_false_iff_of_ne_zero h1).mp e1
    have p2 := (orientSign_eq_true_iff a c d).mp e2
    have n3 := (orientSign_eq_false_iff_of_ne_zero h3).mp e3
    have p4 := (orientSign_eq_true_iff a b c).mp e4
    linarith
  · have p1 := (orientSign_eq_true_iff b c d).mp e1
    have n2 := (orientSign_eq_false_iff_of_ne_zero h2).mp e2
    have p3 := (orientSign_eq_true_iff a b d).mp e3
    have n4 := (orientSign_eq_false_iff_of_ne_zero h4).mp e4
    linarith


/-! ## 3. Clauses `(C2)` & `(C3)`: Convex Polygon (`conv(D)` / `conv(B)`) & Carathéodory -/

lemma convex_halfplane_orient_nonneg (a b : ℝ × ℝ) :
    Convex ℝ {q : ℝ × ℝ | 0 ≤ orient2D a b q} := by
  intro x hx y hy α β hα hβ hαβ
  change 0 ≤ orient2D a b (α • x + β • y)
  have hid : orient2D a b (α • x + β • y) = α * orient2D a b x + β * orient2D a b y := by
    unfold orient2D
    simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    rw [show β = 1 - α by linarith [hαβ]]
    ring
  rw [hid]
  exact add_nonneg (mul_nonneg hα hx) (mul_nonneg hβ hy)

private lemma fin_add_one_val {N : ℕ} [NeZero N] (hN : 2 ≤ N) (i : Fin N) :
    (i + 1).val = (i.val + 1) % N := by
  rw [← finShift_one hN i]; rfl

private lemma fin_succ_ne_self {N : ℕ} [NeZero N] (hN : 2 ≤ N) (s : Fin N) :
    s ≠ s + 1 := by
  intro heq
  have hv : s.val = (s + 1).val := congrArg Fin.val heq
  rw [fin_add_one_val hN s] at hv
  have hs_lt := s.isLt
  by_cases hw : s.val + 1 < N
  · rw [Nat.mod_eq_of_lt hw] at hv; omega
  · rw [show s.val + 1 = N by omega, Nat.mod_self] at hv; omega

/-- Every vertex `p s` (`s ∉ {r, r + 1}`) of a strict CCW `(m + 3)`-gon lies strictly left of `p r -> p (r + 1)`. -/
lemma ccw_poly_edge_orient_pos {m : ℕ} {p : Fin (m + 3) → ℝ × ℝ}
    (hccw : ∀ i j k : Fin (m + 3), i < j → j < k → orientSign (p i) (p j) (p k) = true)
    (r s : Fin (m + 3)) (hsr : s ≠ r) (hsr1 : s ≠ r + 1) :
    0 < orient2D (p r) (p (r + 1)) (p s) := by
  have hr1_mod := fin_add_one_val (by omega : 2 ≤ m + 3) r
  have hr_lt := r.isLt
  by_cases hwrap : r.val + 1 < m + 3
  · have hr1_val : (r + 1).val = r.val + 1 := by rw [hr1_mod, Nat.mod_eq_of_lt hwrap]
    have hs_ne_r : s.val ≠ r.val := Fin.val_ne_of_ne hsr
    have hs_ne_r1 : s.val ≠ r.val + 1 := by rw [← hr1_val]; exact Fin.val_ne_of_ne hsr1
    by_cases hlt : s.val < r.val
    · have h1 : s < r := Fin.lt_def.mpr hlt
      have h2 : r < r + 1 := Fin.lt_def.mpr (by omega)
      have ho := (orientSign_eq_true_iff _ _ _).mp (hccw s r (r + 1) h1 h2)
      rwa [← orient2D_cycle] at ho
    · have h1 : r < r + 1 := Fin.lt_def.mpr (by omega)
      have h2 : r + 1 < s := Fin.lt_def.mpr (by omega)
      exact (orientSign_eq_true_iff _ _ _).mp (hccw r (r + 1) s h1 h2)
  · have hr_eq : r.val = m + 2 := by omega
    have hr1_zero : r + 1 = 0 := by
      ext
      rw [hr1_mod, show r.val + 1 = m + 3 by omega, Nat.mod_self]
      rfl
    rw [hr1_zero]
    have hs0 : (0 : Fin (m + 3)) < s := by
      have hs_ne0 : s ≠ 0 := by rwa [← hr1_zero]
      exact Fin.pos_iff_ne_zero.mpr hs_ne0
    have hsr_lt : s < r := by
      have hs_ne_r : s.val ≠ r.val := Fin.val_ne_of_ne hsr
      exact Fin.lt_def.mpr (by omega)
    have ho := (orientSign_eq_true_iff _ _ _).mp (hccw 0 s r hs0 hsr_lt)
    rw [← orient2D_cycle (p r) (p 0) (p s)]
    exact ho

/-- **Exact Convex-Polygon Interior Equivalence**:
    For any strict CCW `(m + 3)`-gon `p` and any `z` non-collinear with every boundary edge `(p r, p (r + 1))`,
    `z ∈ conv(range p)` iff `orientSign (p r) (p (r + 1)) z = true` for all `r : Fin (m + 3)`. -/
theorem convex_poly_mem_convexHull_iff_orientSign {m : ℕ} {p : Fin (m + 3) → ℝ × ℝ}
    (hccw : ∀ i j k : Fin (m + 3), i < j → j < k → orientSign (p i) (p j) (p k) = true)
    {z : ℝ × ℝ}
    (hgp : ∀ r : Fin (m + 3), orient2D (p r) (p (r + 1)) z ≠ 0) :
    z ∈ convexHull ℝ (Set.range p) ↔
      ∀ r : Fin (m + 3), orientSign (p r) (p (r + 1)) z = true := by
  constructor
  · intro hz r
    rw [orientSign_eq_true_iff]
    have hsub : Set.range p ⊆ {q : ℝ × ℝ | 0 ≤ orient2D (p r) (p (r + 1)) q} := by
      rintro _ ⟨s, rfl⟩
      change 0 ≤ orient2D (p r) (p (r + 1)) (p s)
      by_cases hsr : s = r
      · rw [hsr]; exact le_of_eq (by unfold orient2D; ring)
      · by_cases hsr1 : s = r + 1
        · rw [hsr1]; exact le_of_eq (by unfold orient2D; ring)
        · exact le_of_lt (ccw_poly_edge_orient_pos hccw r s hsr hsr1)
    have hnn : 0 ≤ orient2D (p r) (p (r + 1)) z :=
      convexHull_min hsub (convex_halfplane_orient_nonneg (p r) (p (r + 1))) hz
    exact lt_of_le_of_ne hnn (hgp r).symm
  · revert p
    induction m with
    | zero =>
      intro p hccw _ hall
      have h012 : 0 < orient2D (p 0) (p 1) (p 2) :=
        (orientSign_eq_true_iff _ _ _).mp (hccw 0 1 2 (by decide) (by decide))
      have h01 : 0 < orient2D (p 0) (p 1) z := (orientSign_eq_true_iff _ _ _).mp (hall 0)
      have h12 : 0 < orient2D (p 1) (p 2) z := (orientSign_eq_true_iff _ _ _).mp (hall 1)
      have h20 : 0 < orient2D (p 2) (p 0) z := (orientSign_eq_true_iff _ _ _).mp (hall 2)
      have htri : z ∈ convexHull ℝ ({p 0, p 1, p 2} : Set (ℝ × ℝ)) :=
        inOpenTri_mem_convexHull (inOpenTri_of_orient_pos h012 h01 h12 h20)
      refine convexHull_mono ?_ htri
      rintro _ (rfl | rfl | rfl) <;> exact ⟨_, rfl⟩
    | succ m ih =>
      intro p hccw _ hall
      let i_prev : Fin (m + 4) := ⟨m + 2, by omega⟩
      let i_last : Fin (m + 4) := ⟨m + 3, by omega⟩
      have hprev_succ : i_prev + 1 = i_last := by
        ext
        rw [fin_add_one_val (by omega : 2 ≤ m + 4) i_prev]
        dsimp [i_prev, i_last]
        exact Nat.mod_eq_of_lt (by omega)
      have hlast_succ : i_last + 1 = 0 := by
        ext
        rw [fin_add_one_val (by omega : 2 ≤ m + 4) i_last]
        dsimp [i_last]
        exact Nat.mod_self (m + 4)
      rcases le_or_gt 0 (orient2D (p 0) (p i_prev) z) with hchord_nn | hchord_neg
      · have h0_prev_last : 0 < orient2D (p 0) (p i_prev) (p i_last) :=
          (orientSign_eq_true_iff _ _ _).mp
            (hccw 0 i_prev i_last (Fin.lt_def.mpr (by simp [i_prev]))
              (Fin.lt_def.mpr (by simp [i_prev, i_last])))
        have h_prev_last : 0 ≤ orient2D (p i_prev) (p i_last) z := by
          have := (orientSign_eq_true_iff _ _ _).mp (hall i_prev)
          rw [hprev_succ] at this
          exact le_of_lt this
        have h_last_0 : 0 ≤ orient2D (p i_last) (p 0) z := by
          have := (orientSign_eq_true_iff _ _ _).mp (hall i_last)
          rw [hlast_succ] at this
          exact le_of_lt this
        have hin : z ∈ convexHull ℝ ({p 0, p i_prev, p i_last} : Set (ℝ × ℝ)) :=
          (inClosedTri_iff_mem_convexHull _ _ _ _).mp
            (inClosedTri_of_orient_nonneg h0_prev_last hchord_nn h_prev_last h_last_0)
        refine convexHull_mono ?_ hin
        rintro _ (rfl | rfl | rfl) <;> exact ⟨_, rfl⟩
      · let q : Fin (m + 3) → ℝ × ℝ := fun i => p i.castSucc
        have hq_ccw : ∀ i j k : Fin (m + 3), i < j → j < k → orientSign (q i) (q j) (q k) = true :=
          fun i j k hij hjk => hccw i.castSucc j.castSucc k.castSucc
            (Fin.castSucc_lt_castSucc_iff.mpr hij) (Fin.castSucc_lt_castSucc_iff.mpr hjk)
        have hq_all : ∀ r : Fin (m + 3), orientSign (q r) (q (r + 1)) z = true := by
          intro r
          have hr_bound := r.isLt
          by_cases hr_lt : r.val + 1 < m + 3
          · have hcast : (r + 1).castSucc = r.castSucc + 1 := by
              ext
              rw [Fin.val_castSucc, fin_add_one_val (by omega : 2 ≤ m + 3) r,
                  fin_add_one_val (by omega : 2 ≤ m + 4) r.castSucc, Fin.val_castSucc,
                  Nat.mod_eq_of_lt hr_lt, Nat.mod_eq_of_lt (by omega : r.val + 1 < m + 4)]
            dsimp [q]
            rw [hcast]
            exact hall r.castSucc
          · have hr_eq : r.castSucc = i_prev := by ext; dsimp [i_prev]; omega
            have hr1_eq : r + 1 = 0 := by
              ext
              rw [fin_add_one_val (by omega : 2 ≤ m + 3) r, show r.val + 1 = m + 3 by omega, Nat.mod_self]
              rfl
            dsimp [q]
            rw [hr_eq, hr1_eq, Fin.castSucc_zero, orientSign_eq_true_iff]
            rw [show orient2D (p i_prev) (p 0) z = -orient2D (p 0) (p i_prev) z by unfold orient2D; ring]
            linarith
        have hq_gp : ∀ r : Fin (m + 3), orient2D (q r) (q (r + 1)) z ≠ 0 := fun r =>
          ne_of_gt ((orientSign_eq_true_iff _ _ _).mp (hq_all r))
        have hz_q : z ∈ convexHull ℝ (Set.range q) := ih hq_ccw hq_gp hq_all
        refine convexHull_mono ?_ hz_q
        rintro _ ⟨i, rfl⟩
        exact ⟨i.castSucc, rfl⟩

/-- **Clause `(C2)` (`shattered_hull_and_interior_orientSign_C2`)**:
    On any `ShatteredSimplePolygon P S w` with CCW hull enumeration `cb : CyclicSubsetBoundary S (hullVertices S)`:
    1. `orientSign (b_i, b_j, b_k) = true` for all `0 ≤ i < j < k < |B|`, and
    2. `orientSign (b_r, b_{r+1}, a) = true` for every interior point `a ∈ interiorPoints S` and every `r`. -/
theorem shattered_hull_and_interior_orientSign_C2 {n : ℕ} {P : Set (ℝ × ℝ)}
    {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ}
    (hP : ShatteredSimplePolygon P S w)
    (cb : CyclicSubsetBoundary S (hullVertices S)) :
    (∀ i j k : Fin (cb.m + 3), i < j → j < k →
      orientSign (S (cb.p_idx i)) (S (cb.p_idx j)) (S (cb.p_idx k)) = true) ∧
    (∀ a ∈ interiorPoints S, ∀ r : Fin (cb.m + 3),
      orientSign (S (cb.p_idx r)) (S (cb.p_idx (r + 1))) (S a) = true) := by
  have hccw : ∀ i j k : Fin (cb.m + 3), i < j → j < k →
      orientSign (S (cb.p_idx i)) (S (cb.p_idx j)) (S (cb.p_idx k)) = true :=
    fun i j k hij hjk => (orientSign_eq_true_iff _ _ _).mpr (cb.hcyc i j k (Or.inl ⟨hij, hjk⟩))
  refine ⟨hccw, fun a ha r => ?_⟩
  have ha_notin_B : a ∉ hullVertices S := (Finset.mem_sdiff.mp ha).2
  have hb_mem : ∀ s : Fin (cb.m + 3), cb.p_idx s ∈ hullVertices S := fun s => by
    have hm : cb.p_idx s ∈ Finset.univ.image cb.p_idx :=
      Finset.mem_image.mpr ⟨s, Finset.mem_univ _, rfl⟩
    rwa [cb.hp_idx_img] at hm
  have hgp : ∀ s : Fin (cb.m + 3), orient2D ((S ∘ cb.p_idx) s) ((S ∘ cb.p_idx) (s + 1)) (S a) ≠ 0 := by
    intro s
    have hs_ne : cb.p_idx s ≠ cb.p_idx (s + 1) :=
      cb.hp_idx_inj.ne (fin_succ_ne_self (by omega : 2 ≤ cb.m + 3) s)
    exact orient_S_S_S_ne hP hs_ne
      (fun h => ha_notin_B (by rw [← h]; exact hb_mem (s + 1)))
      (fun h => ha_notin_B (by rw [← h]; exact hb_mem s))
  have hrange_eq : Set.range (S ∘ cb.p_idx) = ((hullVertices S).image S : Set (ℝ × ℝ)) := by
    have himg : Finset.univ.image (S ∘ cb.p_idx) = (hullVertices S).image S := by
      calc Finset.univ.image (S ∘ cb.p_idx)
          = (Finset.univ.image cb.p_idx).image S := Finset.image_image.symm
        _ = (hullVertices S).image S := by rw [cb.hp_idx_img]
    rw [← himg]
    ext x; simp
  have ha_hull : S a ∈ convexHull ℝ (Set.range (S ∘ cb.p_idx)) := by
    rw [hrange_eq, hullVertices_convexHull_eq S hP.s_inj]
    exact subset_convexHull ℝ (Set.range S) ⟨a, rfl⟩
  exact (convex_poly_mem_convexHull_iff_orientSign hccw hgp).mp ha_hull r

/-- Same interior-in-`conv(D)` sign extraction for any `C ⊆ hullVertices S` (`dc : CyclicSubsetBoundary S C`). -/
theorem shattered_subhull_interior_orientSign {n : ℕ} {P : Set (ℝ × ℝ)}
    {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ}
    (hP : ShatteredSimplePolygon P S w)
    {C : Finset (Fin n)} (dc : CyclicSubsetBoundary S C)
    {y : Fin n} (hy_not : y ∉ C)
    (hy_hull : S y ∈ convexHull ℝ ((C.image S : Finset (ℝ × ℝ)) : Set (ℝ × ℝ))) :
    ∀ r : Fin (dc.m + 3), orientSign (S (dc.p_idx r)) (S (dc.p_idx (r + 1))) (S y) = true := by
  have hccw : ∀ i j k : Fin (dc.m + 3), i < j → j < k →
      orientSign (S (dc.p_idx i)) (S (dc.p_idx j)) (S (dc.p_idx k)) = true :=
    fun i j k hij hjk => (orientSign_eq_true_iff _ _ _).mpr (dc.hcyc i j k (Or.inl ⟨hij, hjk⟩))
  have hc_mem : ∀ s : Fin (dc.m + 3), dc.p_idx s ∈ C := fun s => by
    have hm : dc.p_idx s ∈ Finset.univ.image dc.p_idx :=
      Finset.mem_image.mpr ⟨s, Finset.mem_univ _, rfl⟩
    rwa [dc.hp_idx_img] at hm
  have hgp : ∀ s : Fin (dc.m + 3), orient2D ((S ∘ dc.p_idx) s) ((S ∘ dc.p_idx) (s + 1)) (S y) ≠ 0 := by
    intro s
    have hs_ne : dc.p_idx s ≠ dc.p_idx (s + 1) :=
      dc.hp_idx_inj.ne (fin_succ_ne_self (by omega : 2 ≤ dc.m + 3) s)
    exact orient_S_S_S_ne hP hs_ne
      (fun h => hy_not (by rw [← h]; exact hc_mem (s + 1)))
      (fun h => hy_not (by rw [← h]; exact hc_mem s))
  have hrange_eq : Set.range (S ∘ dc.p_idx) = (C.image S : Set (ℝ × ℝ)) := by
    have himg : Finset.univ.image (S ∘ dc.p_idx) = C.image S := by
      calc Finset.univ.image (S ∘ dc.p_idx)
          = (Finset.univ.image dc.p_idx).image S := Finset.image_image.symm
        _ = C.image S := by rw [dc.hp_idx_img]
    rw [← himg]
    ext x; simp
  rw [← hrange_eq] at hy_hull
  exact (convex_poly_mem_convexHull_iff_orientSign hccw hgp).mp hy_hull

/-- **Clause `(C3)` (`caratheodory_four_subset_C3`)**:
    If a subset `F ⊆ Fin n` of a shattered set `S` is NOT in strictly convex position
    (e.g., any 7-subset `S₇` once `VC-dim_convex ≤ 6` is established), then `F` contains four
    distinct indices `x, a, b, c` with `inOpenTriBool (S x) (S a) (S b) (S c) = true`. -/
theorem caratheodory_four_subset_C3 {n : ℕ} {P : Set (ℝ × ℝ)}
    {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ}
    (hP : ShatteredSimplePolygon P S w)
    (F : Finset (Fin n))
    (h_not_conv : ¬ ∀ i ∈ F, S i ∉ convexHull ℝ (((F.erase i).image S : Finset (ℝ × ℝ)) : Set (ℝ × ℝ))) :
    ∃ x ∈ F, ∃ a ∈ F, ∃ b ∈ F, ∃ c ∈ F,
      x ≠ a ∧ x ≠ b ∧ x ≠ c ∧ a ≠ b ∧ b ≠ c ∧ a ≠ c ∧
      inOpenTriBool (S x) (S a) (S b) (S c) = true := by
  push Not at h_not_conv
  rcases h_not_conv with ⟨x, hxF, hx_hull⟩
  obtain ⟨p₁, hp1, p₂, hp2, p₃, hp3, hclosed⟩ := planar_caratheodory hx_hull
  simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_erase] at hp1 hp2 hp3
  rcases hp1 with ⟨a, ⟨hax, haF⟩, rfl⟩
  rcases hp2 with ⟨b, ⟨hbx, hbF⟩, rfl⟩
  rcases hp3 with ⟨c, ⟨hcx, hcF⟩, rfl⟩
  rcases hclosed with ⟨μ₁, μ₂, μ₃, hμ1, hμ2, hμ3, hμsum, hx1, hx2⟩
  have h_eq_of_col : ∀ {u v : Fin n}, u ≠ x → v ≠ x → orient2D (S u) (S v) (S x) = 0 → u = v := by
    intro u v hux hvx hcol
    by_contra huv
    exact orient_S_S_S_ne hP huv hvx hux hcol
  have hμ1_ne0 : μ₁ ≠ 0 := by
    intro h0
    have hbc_eq : b = c := h_eq_of_col hbx hcx (by
      unfold orient2D
      rw [hx1, hx2, show μ₃ = 1 - μ₁ - μ₂ by linarith, h0]
      ring)
    have hxs : S x = S b := by
      ext
      · rw [hx1, hbc_eq, show μ₃ = 1 - μ₁ - μ₂ by linarith, h0]; ring
      · rw [hx2, hbc_eq, show μ₃ = 1 - μ₁ - μ₂ by linarith, h0]; ring
    exact hbx (hP.s_inj hxs).symm
  have hμ2_ne0 : μ₂ ≠ 0 := by
    intro h0
    have hac_eq : a = c := h_eq_of_col hax hcx (by
      unfold orient2D
      rw [hx1, hx2, show μ₃ = 1 - μ₁ - μ₂ by linarith, h0]
      ring)
    have hxs : S x = S a := by
      ext
      · rw [hx1, ← hac_eq, show μ₃ = 1 - μ₁ - μ₂ by linarith, h0]; ring
      · rw [hx2, ← hac_eq, show μ₃ = 1 - μ₁ - μ₂ by linarith, h0]; ring
    exact hax (hP.s_inj hxs).symm
  have hμ3_ne0 : μ₃ ≠ 0 := by
    intro h0
    have hab_eq : a = b := h_eq_of_col hax hbx (by
      unfold orient2D
      rw [hx1, hx2, h0, show μ₂ = 1 - μ₁ by linarith]
      ring)
    have hxs : S x = S a := by
      ext
      · rw [hx1, ← hab_eq, h0, show μ₂ = 1 - μ₁ by linarith]; ring
      · rw [hx2, ← hab_eq, h0, show μ₂ = 1 - μ₁ by linarith]; ring
    exact hax (hP.s_inj hxs).symm
  have hμ1_pos : 0 < μ₁ := lt_of_le_of_ne hμ1 hμ1_ne0.symm
  have hμ2_pos : 0 < μ₂ := lt_of_le_of_ne hμ2 hμ2_ne0.symm
  have hμ3_pos : 0 < μ₃ := lt_of_le_of_ne hμ3 hμ3_ne0.symm
  have hab : a ≠ b := by
    intro heq
    have hac_eq : a = c := h_eq_of_col hax hcx (by
      unfold orient2D
      rw [hx1, hx2, ← heq, show μ₃ = 1 - μ₁ - μ₂ by linarith]
      ring)
    have hxs : S x = S a := by
      ext
      · rw [hx1, ← heq, ← hac_eq, show μ₃ = 1 - μ₁ - μ₂ by linarith]; ring
      · rw [hx2, ← heq, ← hac_eq, show μ₃ = 1 - μ₁ - μ₂ by linarith]; ring
    exact hax (hP.s_inj hxs).symm
  have hbc : b ≠ c := by
    intro heq
    exact hab (h_eq_of_col hax hbx (by
      unfold orient2D
      rw [hx1, hx2, ← heq, show μ₃ = 1 - μ₁ - μ₂ by linarith]
      ring))
  have hac : a ≠ c := by
    intro heq
    exact hab (h_eq_of_col hax hbx (by
      unfold orient2D
      rw [hx1, hx2, ← heq, show μ₃ = 1 - μ₁ - μ₂ by linarith]
      ring))
  have hopen : InOpenTri (S a) (S b) (S c) (S x) :=
    ⟨μ₁, μ₂, μ₃, hμ1_pos, hμ2_pos, hμ3_pos, hμsum, hx1, hx2⟩
  refine ⟨x, hxF, a, haF, b, hbF, c, hcF, hax.symm, hbx.symm, hcx.symm, hab, hbc, hac, ?_⟩
  exact (inOpenTriBool_iff_inOpenTri
    (orient_S_S_S_ne hP hab hbx hax)
    (orient_S_S_S_ne hP hbc hcx hbx)
    (orient_S_S_S_ne hP hac.symm hax hcx)).mpr hopen


/-! ## 4. Clauses `(C4)`, `(C5)`, `(C8)`: Visibility Chord & Wedge Separation Clauses -/

/-- **Visibility Chord Separation (`vis_chord_one_side_of_misses`, Section 6 / `(C7)`–`(C9)` `cond_iv`)**:
    If `w Tv` and `w Tq` (`Tv ≠ Tq`) both see `S s₁` and `S s₂` and `oppSideBool (w Tv) (w Tq) (S s₁) (S s₂) = true`,
    then `Sees P (w Tv) (w Tq)`. Consequently, if `¬ Sees P (w Tv) (w Tq)`, all points of `S` seen by both
    `w Tv` and `w Tq` lie on the same open side of `w Tv -> w Tq`. -/
theorem vis_chord_sees_of_oppSide {n : ℕ} {P : Set (ℝ × ℝ)}
    {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ}
    (hP : ShatteredSimplePolygon P S w)
    {Tv Tq : Finset (Fin n)} (hTq : Tv ≠ Tq) {s₁ s₂ : Fin n}
    (hs1_v : s₁ ∈ Tv) (hs1_q : s₁ ∈ Tq) (hs2_v : s₂ ∈ Tv) (hs2_q : s₂ ∈ Tq)
    (hopp : oppSideBool (w Tv) (w Tq) (S s₁) (S s₂) = true) :
    Sees P (w Tv) (w Tq) := by
  have hm := (oppSideBool_iff_mul_neg (orient_w_w_S_ne hP hTq s₁) (orient_w_w_S_ne hP hTq s₂)).mp hopp
  have hp1 : IsPolygonalPathIn P (w Tv) (w Tq) [w Tv, S s₁, w Tq] :=
    isPolygonalPathIn_three ((hP.shatters Tv s₁).mpr hs1_v) (sees_symm ((hP.shatters Tq s₁).mpr hs1_q))
  have hp2 : IsPolygonalPathIn P (w Tv) (w Tq) [w Tv, S s₂, w Tq] :=
    isPolygonalPathIn_three ((hP.shatters Tv s₂).mpr hs2_v) (sees_symm ((hP.shatters Tq s₂).mpr hs2_q))
  have hne0 := orient2D_ne_zero_of_mul_neg hm
  rcases lt_or_gt_of_ne hne0.1 with hneg | hpos
  · exact two_path_enclosure_either hP.toEnclosureDomain (hP.w_inj.ne hTq) hp1 hp2
      (Or.inr ⟨interiorOnRight_three hneg, interiorOnLeft_three (by nlinarith)⟩)
  · exact two_path_enclosure_either hP.toEnclosureDomain (hP.w_inj.ne hTq) hp1 hp2
      (Or.inl ⟨interiorOnLeft_three hpos, interiorOnRight_three (by nlinarith)⟩)

theorem vis_chord_one_side_of_misses {n : ℕ} {P : Set (ℝ × ℝ)}
    {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ}
    (hP : ShatteredSimplePolygon P S w)
    {Tv Tq : Finset (Fin n)} (hTq : Tv ≠ Tq) (hmiss : ¬ Sees P (w Tv) (w Tq))
    {s₁ s₂ : Fin n}
    (hs1_v : s₁ ∈ Tv) (hs1_q : s₁ ∈ Tq) (hs2_v : s₂ ∈ Tv) (hs2_q : s₂ ∈ Tq) :
    oppSideBool (w Tv) (w Tq) (S s₁) (S s₂) = false := by
  cases h : oppSideBool (w Tv) (w Tq) (S s₁) (S s₂)
  · rfl
  · exact False.elim (hmiss (vis_chord_sees_of_oppSide hP hTq hs1_v hs1_q hs2_v hs2_q h))

/-- Helper avoiding `Tz = Tw` case split: `S k ∈ int tri(zWitness w k, S s₁, S s₂)` holds whether `Tw = univ.erase k` or not. -/
private lemma zk_in_uCone_of_missed_tri {n : ℕ} {P : Set (ℝ × ℝ)}
    {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ}
    (hP : ShatteredSimplePolygon P S w)
    {k s₁ s₂ : Fin n} {Tw : Finset (Fin n)}
    (hk_miss : k ∉ Tw) (hs1 : s₁ ∈ Tw) (hs2 : s₂ ∈ Tw)
    (htri : InOpenTri (w Tw) (S s₁) (S s₂) (S k)) :
    zWitness w k ∈ UCone (S k) (S s₁) (S s₂) := by
  have hs1_ne_k : s₁ ≠ k := fun h => hk_miss (h ▸ hs1)
  have hs2_ne_k : s₂ ≠ k := fun h => hk_miss (h ▸ hs2)
  rw [mem_uCone_iff_inOpenTri]
  by_cases heq : Tw = Finset.univ.erase k
  · rw [zWitness, ← heq]; exact htri
  · exact (mem_uCone_iff_inOpenTri _ _ _ _).mp
      (cone hP.toEnclosureDomain
        ((hP.shatters Tw s₁).mpr hs1)
        ((hP.shatters Tw s₂).mpr hs2)
        (fun hs => hk_miss ((hP.shatters Tw k).mp hs))
        htri
        ((hP.shatters (Finset.univ.erase k) s₁).mpr (Finset.mem_erase.mpr ⟨hs1_ne_k, Finset.mem_univ _⟩))
        ((hP.shatters (Finset.univ.erase k) s₂).mpr (Finset.mem_erase.mpr ⟨hs2_ne_k, Finset.mem_univ _⟩))
        (orient_S_S_w_ne hP hs1_ne_k.symm (Finset.univ.erase k))
        (orient_S_S_w_ne hP hs2_ne_k.symm (Finset.univ.erase k))
        (orient_w_S_w_ne hP heq k))

/-- **Clause `(C4)` (`non_certified_obstruction_clause_C4`)**:
    For every witness `w Tw`, every non-certified hull vertex `k ∈ D = hullVertices S \ certifiedSet P S w`
    missed by `w Tw` (`k ∉ Tw`), and every distinct pair `s₁, s₂ ∈ Tw`, `k ∉ int tri(w Tw, S s₁, S s₂)`. -/
theorem non_certified_obstruction_clause_C4 {n : ℕ} {P : Set (ℝ × ℝ)}
    {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ}
    (hP : ShatteredSimplePolygon P S w) (hn : 3 ≤ n)
    {k s₁ s₂ : Fin n} {Tw : Finset (Fin n)}
    (hkD : k ∈ hullVertices S \ certifiedSet P S w)
    (hk_miss : k ∉ Tw) (hs1 : s₁ ∈ Tw) (hs2 : s₂ ∈ Tw) (hs12 : s₁ ≠ s₂) :
    inOpenTriBool (S k) (w Tw) (S s₁) (S s₂) = false := by
  have hkB : k ∈ hullVertices S := (Finset.mem_sdiff.mp hkD).1
  have hk_not_H : k ∉ certifiedSet P S w := (Finset.mem_sdiff.mp hkD).2
  have hs1_ne_k : s₁ ≠ k := fun h => hk_miss (h ▸ hs1)
  have hs2_ne_k : s₂ ≠ k := fun h => hk_miss (h ▸ hs2)
  cases htri_b : inOpenTriBool (S k) (w Tw) (S s₁) (S s₂)
  · rfl
  · exfalso
    have htri : InOpenTri (w Tw) (S s₁) (S s₂) (S k) :=
      (inOpenTriBool_iff_inOpenTri
        (orient_w_S_S_ne hP Tw hs1_ne_k)
        (orient_S_S_S_ne hP hs12 hs2_ne_k hs1_ne_k)
        (orient_S_w_S_ne hP hs2_ne_k Tw)).mp htri_b
    obtain ⟨α, β, hα, hβ, hzk_eq⟩ := zk_in_uCone_of_missed_tri hP hk_miss hs1 hs2 htri
    have hB3 : 3 ≤ (hullVertices S).card := hullVertices_card_ge_three hn hP
    obtain ⟨cb⟩ := exists_cyclicSubsetBoundary hP (Finset.Subset.refl _) hB3
    have hk_img : k ∈ Finset.univ.image cb.p_idx := by rwa [cb.hp_idx_img]
    rcases Finset.mem_image.mp hk_img with ⟨ik, _, hik_eq⟩
    let p := S ∘ cb.p_idx
    have hp_inj : Function.Injective p := hP.s_inj.comp cb.hp_idx_inj
    have himg_eq : Finset.univ.image p = (hullVertices S).image S := by
      calc Finset.univ.image (S ∘ cb.p_idx)
          = (Finset.univ.image cb.p_idx).image S := Finset.image_image.symm
        _ = (hullVertices S).image S := by rw [cb.hp_idx_img]
    have hedge_l : IsCCWHullEdge ((hullVertices S).image S) (p (ik - 1)) (S k) := by
      rw [← himg_eq, ← hik_eq]
      exact (isCCWHullEdge_iff_succ cb.hstrict hp_inj).mpr
        ⟨ik - 1, rfl, congrArg p (sub_add_cancel ik 1)⟩
    have hedge_r : IsCCWHullEdge ((hullVertices S).image S) (S k) (p (ik + 1)) := by
      rw [← himg_eq, ← hik_eq]
      exact (isCCWHullEdge_iff_succ cb.hstrict hp_inj).mpr ⟨ik, rfl, rfl⟩
    have h_edge_face : ∀ a b : ℝ × ℝ, IsCCWHullEdge ((hullVertices S).image S) a b →
        (a = S k ∨ b = S k) → orient2D a b (zWitness w k) < 0 := by
      intro a b hedge hk_end
      have hsub_B : ((hullVertices S).image S : Set (ℝ × ℝ)) ⊆ {q : ℝ × ℝ | 0 ≤ orient2D a b q} := by
        intro q hq
        have hq' : q ∈ (hullVertices S).image S := hq
        change 0 ≤ orient2D a b q
        by_cases hqa : q = a
        · rw [hqa]; exact le_of_eq (by unfold orient2D; ring)
        · by_cases hqb : q = b
          · rw [hqb]; exact le_of_eq (by unfold orient2D; ring)
          · exact le_of_lt (hedge.2.2.2 q hq' hqa hqb)
      have h_all_S : ∀ j : Fin n, 0 ≤ orient2D a b (S j) := by
        intro j
        have hj_hull : S j ∈ convexHull ℝ (((hullVertices S).image S : Finset (ℝ × ℝ)) : Set (ℝ × ℝ)) := by
          rw [hullVertices_convexHull_eq S hP.s_inj]
          exact subset_convexHull ℝ (Set.range S) ⟨j, rfl⟩
        exact convexHull_min hsub_B (convex_halfplane_orient_nonneg a b) hj_hull
      have hs1_nn := h_all_S s₁
      have hs2_nn := h_all_S s₂
      have hnot_both_zero : ¬ (orient2D a b (S s₁) = 0 ∧ orient2D a b (S s₂) = 0) := by
        rintro ⟨hz1, hz2⟩
        have hab_ne : a ≠ b := hedge.2.2.1
        have hcol_ks : orient2D (S k) (S s₁) (S s₂) = 0 := by
          have hnorm : (b.1 - a.1) ^ 2 + (b.2 - a.2) ^ 2 ≠ 0 := by
            intro h0
            have hx : b.1 - a.1 = 0 := by nlinarith [sq_nonneg (b.1 - a.1), sq_nonneg (b.2 - a.2)]
            have hy : b.2 - a.2 = 0 := by nlinarith [sq_nonneg (b.1 - a.1), sq_nonneg (b.2 - a.2)]
            exact hab_ne (by ext <;> linarith)
          rcases hk_end with rfl | rfl
          · have hid : ((b.1 - (S k).1) ^ 2 + (b.2 - (S k).2) ^ 2) * orient2D (S k) (S s₁) (S s₂) =
                ((b.1 - (S k).1) * ((S s₁).1 - (S k).1) + (b.2 - (S k).2) * ((S s₁).2 - (S k).2)) *
                  orient2D (S k) b (S s₂) -
                ((b.1 - (S k).1) * ((S s₂).1 - (S k).1) + (b.2 - (S k).2) * ((S s₂).2 - (S k).2)) *
                  orient2D (S k) b (S s₁) := by unfold orient2D; ring
            rw [hz1, hz2, mul_zero, mul_zero, sub_zero] at hid
            exact (mul_eq_zero.mp hid).resolve_left hnorm
          · have hid : (((S k).1 - a.1) ^ 2 + ((S k).2 - a.2) ^ 2) * orient2D (S k) (S s₁) (S s₂) =
                (((S k).1 - a.1) * ((S s₁).1 - (S k).1) + ((S k).2 - a.2) * ((S s₁).2 - (S k).2)) *
                  orient2D a (S k) (S s₂) -
                (((S k).1 - a.1) * ((S s₂).1 - (S k).1) + ((S k).2 - a.2) * ((S s₂).2 - (S k).2)) *
                  orient2D a (S k) (S s₁) := by unfold orient2D; ring
            rw [hz1, hz2, mul_zero, mul_zero, sub_zero] at hid
            exact (mul_eq_zero.mp hid).resolve_left hnorm
        exact orient_S_S_S_ne hP hs1_ne_k.symm hs12 hs2_ne_k.symm hcol_ks
      have hzk_coords : (zWitness w k).1 = (S k).1 + α * ((S k).1 - (S s₁).1) + β * ((S k).1 - (S s₂).1) ∧
                        (zWitness w k).2 = (S k).2 + α * ((S k).2 - (S s₁).2) + β * ((S k).2 - (S s₂).2) := by
        rw [hzk_eq]; simp
      have hor_zk : orient2D a b (zWitness w k) =
          (1 + α + β) * orient2D a b (S k) - α * orient2D a b (S s₁) - β * orient2D a b (S s₂) := by
        unfold orient2D; rw [hzk_coords.1, hzk_coords.2]; ring
      have hor_k_zero : orient2D a b (S k) = 0 := by
        rcases hk_end with rfl | rfl <;> (unfold orient2D; ring)
      rw [hor_zk, hor_k_zero, mul_zero, zero_sub]
      by_cases hz1 : orient2D a b (S s₁) = 0
      · have hz2 : 0 < orient2D a b (S s₂) :=
          lt_of_le_of_ne hs2_nn (fun h => hnot_both_zero ⟨hz1, h.symm⟩)
        rw [hz1, mul_zero, neg_zero, zero_sub]
        exact neg_lt_zero.mpr (mul_pos hβ hz2)
      · have hp1 : 0 < orient2D a b (S s₁) := lt_of_le_of_ne hs1_nn (Ne.symm hz1)
        linarith [mul_pos hα hp1, mul_nonneg (le_of_lt hβ) hs2_nn]
    have hcert : IsCertified P S w k := by
      refine ⟨hkB, Finset.univ.erase k, ?_, ?_, ?_⟩
      · intro hs
        exact (Finset.mem_erase.mp ((hP.shatters (Finset.univ.erase k) k).mp hs)).1 rfl
      · intro b hbB h_inc
        have hbk : b ≠ k := by
          rcases h_inc with he1 | he2
          · exact fun h => he1.2.2.1 (congrArg S h)
          · exact fun h => he2.2.2.1 (congrArg S h).symm
        exact (hP.shatters (Finset.univ.erase k) b).mpr (Finset.mem_erase.mpr ⟨hbk, Finset.mem_univ _⟩)
      · exact ⟨p (ik - 1), p (ik + 1), hedge_l, hedge_r,
          h_edge_face _ _ hedge_l (Or.inr rfl), h_edge_face _ _ hedge_r (Or.inl rfl)⟩
    exact hk_not_H (Finset.mem_filter.mpr ⟨hkB, hcert⟩)

/-- **Clause `(C5)` Part 1 (`exit_edge_cone_clause_C5`)**:
    When `3 ≤ |D|` (`dc : CyclicSubsetBoundary S D`), each `y ∈ M = interiorPoints S ∪ certifiedSet P S w`
    has a unique exit edge `e_i = (d_i, d_{i+1})` of `D` such that every witness `w Tw` seeing `d_i` and `d_{i+1}`
    satisfies `inOpenTriBool (S y) (w Tw) (S d_i) (S d_{i+1}) = true`. -/
theorem exit_edge_cone_clause_C5 {n : ℕ} {P : Set (ℝ × ℝ)}
    {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ}
    (hP : ShatteredSimplePolygon P S w) (hn : 3 ≤ n)
    (hD3 : 3 ≤ (hullVertices S \ certifiedSet P S w).card)
    (dc : CyclicSubsetBoundary S (hullVertices S \ certifiedSet P S w))
    {y : Fin n} (hyM : y ∈ interiorPoints S ∪ certifiedSet P S w) :
    ∃ i : Fin (dc.m + 3),
      inOpenTriBool (S y) (w (hullVertices S \ certifiedSet P S w))
        (S (dc.p_idx i)) (S (dc.p_idx (i + 1))) = true ∧
      ∀ Tw : Finset (Fin n), dc.p_idx i ∈ Tw → dc.p_idx (i + 1) ∈ Tw →
        inOpenTriBool (S y) (w Tw) (S (dc.p_idx i)) (S (dc.p_idx (i + 1))) = true := by
  obtain ⟨⟨i, ⟨hu_pos, hy_tri⟩, _⟩, hall⟩ := exit_edge hP hn hD3 dc y hyM
  have hdc_mem : ∀ j : Fin (dc.m + 3), dc.p_idx j ∈ hullVertices S \ certifiedSet P S w := fun j => by
    have hm : dc.p_idx j ∈ Finset.univ.image dc.p_idx :=
      Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
    rwa [dc.hp_idx_img] at hm
  have hy_notin_D : y ∉ hullVertices S \ certifiedSet P S w := by
    rcases Finset.mem_union.mp hyM with hyA | hyH
    · exact fun hyD => (Finset.mem_sdiff.mp hyA).2 (Finset.mem_sdiff.mp hyD).1
    · exact fun hyD => (Finset.mem_sdiff.mp hyD).2 hyH
  have hi_ne : dc.p_idx i ≠ dc.p_idx (i + 1) :=
    dc.hp_idx_inj.ne (fin_succ_ne_self (by omega : 2 ≤ dc.m + 3) i)
  have h_to_bool : ∀ T : Finset (Fin n),
      InOpenTri (w T) (S (dc.p_idx i)) (S (dc.p_idx (i + 1))) (S y) →
      inOpenTriBool (S y) (w T) (S (dc.p_idx i)) (S (dc.p_idx (i + 1))) = true := fun T ht =>
    (inOpenTriBool_iff_inOpenTri
      (orient_w_S_S_ne hP T (fun h => hy_notin_D (by rw [← h]; exact hdc_mem i)))
      (orient_S_S_S_ne hP hi_ne
        (fun h => hy_notin_D (by rw [← h]; exact hdc_mem (i + 1)))
        (fun h => hy_notin_D (by rw [← h]; exact hdc_mem i)))
      (orient_S_w_S_ne hP (fun h => hy_notin_D (by rw [← h]; exact hdc_mem (i + 1))) T)).mpr ht
  refine ⟨i, h_to_bool _ hy_tri, fun Tw hi1 hi2 => ?_⟩
  exact h_to_bool Tw ((hall i hu_pos hy_tri).1 Tw
    ((hP.shatters Tw _).mpr hi1) ((hP.shatters Tw _).mpr hi2))

/-- **Clause `(C5)` Part 2 (`wedge_sep_clause_C5`, Convex Wedge Separation, Lemma 2.9)**:
    Suppose `u, v, y` are distinct in `Fin n`, `w T₁` and `w T₂` (`T₁ ≠ T₂`) both see `u, v, y`,
    `w Tm` sees `u, v` and misses `y`, and `S y ∈ int tri(w T₁, S u, S v) ∩ int tri(w T₂, S u, S v)`.
    Then `w Tm` cannot lie in `S y + cone(w T₁ - S y, w T₂ - S y)`:
    for both `s = true` and `s = false`,
    `¬ (orientSign (S y) (w T₁) (w T₂) = s ∧ orientSign (S y) (w T₁) (w Tm) = s ∧ orientSign (S y) (w Tm) (w T₂) = s)`. -/
theorem wedge_sep_clause_C5 {n : ℕ} {P : Set (ℝ × ℝ)}
    {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ}
    (hP : ShatteredSimplePolygon P S w)
    {y u v : Fin n} (hyu : y ≠ u) (hyv : y ≠ v) (huv : u ≠ v)
    {T₁ T₂ Tm : Finset (Fin n)} (hT12 : T₁ ≠ T₂)
    (hu1 : u ∈ T₁) (hv1 : v ∈ T₁) (hy1 : y ∈ T₁)
    (hu2 : u ∈ T₂) (hv2 : v ∈ T₂) (hy2 : y ∈ T₂)
    (hum : u ∈ Tm) (hvm : v ∈ Tm) (hym_not : y ∉ Tm)
    (htri1 : inOpenTriBool (S y) (w T₁) (S u) (S v) = true)
    (htri2 : inOpenTriBool (S y) (w T₂) (S u) (S v) = true)
    (s : Bool) :
    ¬ (orientSign (S y) (w T₁) (w T₂) = s ∧
       orientSign (S y) (w T₁) (w Tm) = s ∧
       orientSign (S y) (w Tm) (w T₂) = s) := by
  have hTm_ne1 : Tm ≠ T₁ := fun h => hym_not (h ▸ hy1)
  have hTm_ne2 : Tm ≠ T₂ := fun h => hym_not (h ▸ hy2)
  have ho1 : InOpenTri (w T₁) (S u) (S v) (S y) :=
    (inOpenTriBool_iff_inOpenTri
      (orient_w_S_S_ne hP T₁ hyu.symm)
      (orient_S_S_S_ne hP huv hyv.symm hyu.symm)
      (orient_S_w_S_ne hP hyv.symm T₁)).mp htri1
  have ho2 : InOpenTri (w T₂) (S u) (S v) (S y) :=
    (inOpenTriBool_iff_inOpenTri
      (orient_w_S_S_ne hP T₂ hyu.symm)
      (orient_S_S_S_ne hP huv hyv.symm hyu.symm)
      (orient_S_w_S_ne hP hyv.symm T₂)).mp htri2
  obtain ⟨α₁, β₁, hα1, hβ1, hw1_eq⟩ := (mem_uCone_iff_inOpenTri (S y) (S u) (S v) (w T₁)).mpr ho1
  obtain ⟨α₂, β₂, hα2, hβ2, hw2_eq⟩ := (mem_uCone_iff_inOpenTri (S y) (S u) (S v) (w T₂)).mpr ho2
  rintro ⟨hs12, hs1m, hsm2⟩
  have hd_ne : orient2D (S y) (w T₁) (w T₂) ≠ 0 := orient_S_w_w_ne hP y hT12
  have h_pos_a : 0 < orient2D (S y) (w Tm) (w T₂) * orient2D (S y) (w T₁) (w T₂) := by
    have hswap : orientSign (S y) (w Tm) (w T₂) = s := hsm2
    exact mul_pos_of_orientSign_eq (orient_S_w_w_ne hP y hTm_ne2) hd_ne hswap hs12
  have h_pos_b : 0 < orient2D (S y) (w T₁) (w Tm) * orient2D (S y) (w T₁) (w T₂) :=
    mul_pos_of_orientSign_eq (orient_S_w_w_ne hP y hTm_ne1.symm) hd_ne hs1m hs12
  let c₁ : ℝ := orient2D (S y) (w Tm) (w T₂) / orient2D (S y) (w T₁) (w T₂)
  let c₂ : ℝ := orient2D (S y) (w T₁) (w Tm) / orient2D (S y) (w T₁) (w T₂)
  have hc1_pos : 0 < c₁ := by
    dsimp [c₁]
    rcases lt_or_gt_of_ne hd_ne with hneg | hpos
    · exact div_pos_of_neg_of_neg (by nlinarith) hneg
    · exact div_pos (by nlinarith) hpos
  have hc2_pos : 0 < c₂ := by
    dsimp [c₂]
    rcases lt_or_gt_of_ne hd_ne with hneg | hpos
    · exact div_pos_of_neg_of_neg (by nlinarith) hneg
    · exact div_pos (by nlinarith) hpos
  have hwm_comb :
      (w Tm).1 - (S y).1 = c₁ * ((w T₁).1 - (S y).1) + c₂ * ((w T₂).1 - (S y).1) ∧
      (w Tm).2 - (S y).2 = c₁ * ((w T₁).2 - (S y).2) + c₂ * ((w T₂).2 - (S y).2) := by
    have e1 : orient2D (S y) (w T₁) (w T₂) * ((w Tm).1 - (S y).1) =
        orient2D (S y) (w Tm) (w T₂) * ((w T₁).1 - (S y).1) +
        orient2D (S y) (w T₁) (w Tm) * ((w T₂).1 - (S y).1) := by unfold orient2D; ring
    have e2 : orient2D (S y) (w T₁) (w T₂) * ((w Tm).2 - (S y).2) =
        orient2D (S y) (w Tm) (w T₂) * ((w T₁).2 - (S y).2) +
        orient2D (S y) (w T₁) (w Tm) * ((w T₂).2 - (S y).2) := by unfold orient2D; ring
    constructor <;> { dsimp [c₁, c₂]; field_simp [hd_ne]; linarith }
  have hw1_c : (w T₁).1 - (S y).1 = α₁ * ((S y).1 - (S u).1) + β₁ * ((S y).1 - (S v).1) ∧
               (w T₁).2 - (S y).2 = α₁ * ((S y).2 - (S u).2) + β₁ * ((S y).2 - (S v).2) := by
    constructor <;> { have := congrArg Prod.fst hw1_eq; have := congrArg Prod.snd hw1_eq; simp at *; linarith }
  have hw2_c : (w T₂).1 - (S y).1 = α₂ * ((S y).1 - (S u).1) + β₂ * ((S y).1 - (S v).1) ∧
               (w T₂).2 - (S y).2 = α₂ * ((S y).2 - (S u).2) + β₂ * ((S y).2 - (S v).2) := by
    constructor <;> { have := congrArg Prod.fst hw2_eq; have := congrArg Prod.snd hw2_eq; simp at *; linarith }
  let αm : ℝ := c₁ * α₁ + c₂ * α₂
  let βm : ℝ := c₁ * β₁ + c₂ * β₂
  have hαm : 0 < αm := add_pos (mul_pos hc1_pos hα1) (mul_pos hc2_pos hα2)
  have hβm : 0 < βm := add_pos (mul_pos hc1_pos hβ1) (mul_pos hc2_pos hβ2)
  have hor_u : orient2D (S y) (w Tm) (S u) = βm * orient2D (S y) (S u) (S v) := by
    unfold orient2D
    have hx : (w Tm).1 - (S y).1 = αm * ((S y).1 - (S u).1) + βm * ((S y).1 - (S v).1) := by
      rw [hwm_comb.1, hw1_c.1, hw2_c.1]; dsimp [αm, βm]; ring
    have hy : (w Tm).2 - (S y).2 = αm * ((S y).2 - (S u).2) + βm * ((S y).2 - (S v).2) := by
      rw [hwm_comb.2, hw1_c.2, hw2_c.2]; dsimp [αm, βm]; ring
    rw [hx, hy]; ring
  have hor_v : orient2D (S y) (w Tm) (S v) = -αm * orient2D (S y) (S u) (S v) := by
    unfold orient2D
    have hx : (w Tm).1 - (S y).1 = αm * ((S y).1 - (S u).1) + βm * ((S y).1 - (S v).1) := by
      rw [hwm_comb.1, hw1_c.1, hw2_c.1]; dsimp [αm, βm]; ring
    have hy : (w Tm).2 - (S y).2 = αm * ((S y).2 - (S u).2) + βm * ((S y).2 - (S v).2) := by
      rw [hwm_comb.2, hw1_c.2, hw2_c.2]; dsimp [αm, βm]; ring
    rw [hx, hy]; ring
  have hor_w1_w2_opp : orient2D (S y) (w Tm) (w T₁) * orient2D (S y) (w Tm) (w T₂) < 0 := by
    have h1 : orient2D (S y) (w Tm) (w T₁) = -orient2D (S y) (w T₁) (w Tm) := orient2D_swap23 _ _ _
    rw [h1]
    have hp := mul_pos_of_orientSign_eq (orient_S_w_w_ne hP y hTm_ne1.symm)
      (orient_S_w_w_ne hP y hTm_ne2) hs1m hsm2
    linarith
  have hyuv_ne : orient2D (S y) (S u) (S v) ≠ 0 := orient_S_S_S_ne hP hyu huv hyv
  have hy_sees_wm : Sees P (S y) (w Tm) := by
    have hne_y_wm : S y ≠ w Tm := hP.s_ne_w y Tm
    have hp_w1_u : IsPolygonalPathIn P (S y) (w Tm) [S y, w T₁, S u, w Tm] :=
      isPolygonalPathIn_four (sees_symm ((hP.shatters T₁ y).mpr hy1))
        ((hP.shatters T₁ u).mpr hu1) (sees_symm ((hP.shatters Tm u).mpr hum))
    have hp_w1_v : IsPolygonalPathIn P (S y) (w Tm) [S y, w T₁, S v, w Tm] :=
      isPolygonalPathIn_four (sees_symm ((hP.shatters T₁ y).mpr hy1))
        ((hP.shatters T₁ v).mpr hv1) (sees_symm ((hP.shatters Tm v).mpr hvm))
    have hp_w2_u : IsPolygonalPathIn P (S y) (w Tm) [S y, w T₂, S u, w Tm] :=
      isPolygonalPathIn_four (sees_symm ((hP.shatters T₂ y).mpr hy2))
        ((hP.shatters T₂ u).mpr hu2) (sees_symm ((hP.shatters Tm u).mpr hum))
    have hp_w2_v : IsPolygonalPathIn P (S y) (w Tm) [S y, w T₂, S v, w Tm] :=
      isPolygonalPathIn_four (sees_symm ((hP.shatters T₂ y).mpr hy2))
        ((hP.shatters T₂ v).mpr hv2) (sees_symm ((hP.shatters Tm v).mpr hvm))
    rcases lt_or_gt_of_ne ((orient2D_ne_zero_of_mul_neg hor_w1_w2_opp).1) with hw1_neg | hw1_pos
    · have hw2_pos : 0 < orient2D (S y) (w Tm) (w T₂) := by
        by_contra hle; push Not at hle
        linarith [mul_nonneg_of_nonpos_of_nonpos (le_of_lt hw1_neg) hle]
      rcases lt_or_gt_of_ne hyuv_ne with hyuv_neg | hyuv_pos
      · have hu_neg : orient2D (S y) (w Tm) (S u) < 0 := by
          rw [hor_u]; exact mul_neg_of_pos_of_neg hβm hyuv_neg
        have hv_pos : 0 < orient2D (S y) (w Tm) (S v) := by
          rw [hor_v]; linarith [mul_neg_of_pos_of_neg hαm hyuv_neg]
        exact two_path_enclosure_either hP.toEnclosureDomain hne_y_wm hp_w2_v hp_w1_u
          (Or.inl ⟨interiorOnLeft_four hw2_pos hv_pos, interiorOnRight_four hw1_neg hu_neg⟩)
      · have hu_pos : 0 < orient2D (S y) (w Tm) (S u) := by
          rw [hor_u]; exact mul_pos hβm hyuv_pos
        have hv_neg : orient2D (S y) (w Tm) (S v) < 0 := by
          rw [hor_v]; linarith [mul_pos hαm hyuv_pos]
        exact two_path_enclosure_either hP.toEnclosureDomain hne_y_wm hp_w2_u hp_w1_v
          (Or.inl ⟨interiorOnLeft_four hw2_pos hu_pos, interiorOnRight_four hw1_neg hv_neg⟩)
    · have hw2_neg : orient2D (S y) (w Tm) (w T₂) < 0 := by
        by_contra hge; push Not at hge
        linarith [mul_nonneg (le_of_lt hw1_pos) hge]
      rcases lt_or_gt_of_ne hyuv_ne with hyuv_neg | hyuv_pos
      · have hu_neg : orient2D (S y) (w Tm) (S u) < 0 := by
          rw [hor_u]; exact mul_neg_of_pos_of_neg hβm hyuv_neg
        have hv_pos : 0 < orient2D (S y) (w Tm) (S v) := by
          rw [hor_v]; linarith [mul_neg_of_pos_of_neg hαm hyuv_neg]
        exact two_path_enclosure_either hP.toEnclosureDomain hne_y_wm hp_w1_v hp_w2_u
          (Or.inl ⟨interiorOnLeft_four hw1_pos hv_pos, interiorOnRight_four hw2_neg hu_neg⟩)
      · have hu_pos : 0 < orient2D (S y) (w Tm) (S u) := by
          rw [hor_u]; exact mul_pos hβm hyuv_pos
        have hv_neg : orient2D (S y) (w Tm) (S v) < 0 := by
          rw [hor_v]; linarith [mul_pos hαm hyuv_pos]
        exact two_path_enclosure_either hP.toEnclosureDomain hne_y_wm hp_w1_u hp_w2_v
          (Or.inl ⟨interiorOnLeft_four hw1_pos hu_pos, interiorOnRight_four hw2_neg hv_neg⟩)
  exact hym_not ((hP.shatters Tm y).mp (sees_symm hy_sees_wm))

/-- **Clause `(C8)` (`asymmetric_two_sided_clause_C8`, Lemma 2.12, `gen_chiro_*.cpp` lines 449–450)**:
    If `w Tx` misses `S d` and sees `S u, S v` (`u ≠ v`), while `w T₁` sees `S d, S u` and `w T₂` sees `S d, S v`,
    then for both `s = true` and `s = false` the 4-literal sign pattern is impossible:
    `¬ (orientSign (S d) (w Tx) (S u) = s ∧ orientSign (S d) (w Tx) (S v) = !s ∧ orientSign (S d) (w Tx) (w T₁) = s ∧ orientSign (S d) (w Tx) (w T₂) = !s)`. -/
theorem asymmetric_two_sided_clause_C8 {n : ℕ} {P : Set (ℝ × ℝ)}
    {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ}
    (hP : ShatteredSimplePolygon P S w)
    {d u v : Fin n} {Tx T₁ T₂ : Finset (Fin n)}
    (hd_miss : d ∉ Tx) (hu_x : u ∈ Tx) (hv_x : v ∈ Tx)
    (hd_1 : d ∈ T₁) (hu_1 : u ∈ T₁) (hd_2 : d ∈ T₂) (hv_2 : v ∈ T₂)
    (s : Bool) :
    ¬ (orientSign (S d) (w Tx) (S u) = s ∧
       orientSign (S d) (w Tx) (S v) = !s ∧
       orientSign (S d) (w Tx) (w T₁) = s ∧
       orientSign (S d) (w Tx) (w T₂) = !s) := by
  have hdu : d ≠ u := fun h => hd_miss (h ▸ hu_x)
  have hdv : d ≠ v := fun h => hd_miss (h ▸ hv_x)
  have hTx1 : Tx ≠ T₁ := fun h => hd_miss (h ▸ hd_1)
  have hTx2 : Tx ≠ T₂ := fun h => hd_miss (h ▸ hd_2)
  have hp1 : IsPolygonalPathIn P (S d) (w Tx) [S d, w T₁, S u, w Tx] :=
    isPolygonalPathIn_four (sees_symm ((hP.shatters T₁ d).mpr hd_1))
      ((hP.shatters T₁ u).mpr hu_1) (sees_symm ((hP.shatters Tx u).mpr hu_x))
  have hp2 : IsPolygonalPathIn P (S d) (w Tx) [S d, w T₂, S v, w Tx] :=
    isPolygonalPathIn_four (sees_symm ((hP.shatters T₂ d).mpr hd_2))
      ((hP.shatters T₂ v).mpr hv_2) (sees_symm ((hP.shatters Tx v).mpr hv_x))
  rintro ⟨hsu, hsv, hw1, hw2⟩
  have hsees : Sees P (S d) (w Tx) := by
    cases s
    · have nu := (orientSign_eq_false_iff_of_ne_zero (orient_S_w_S_ne hP hdu Tx)).mp hsu
      have pv := (orientSign_eq_true_iff _ _ _).mp hsv
      have nw1 := (orientSign_eq_false_iff_of_ne_zero (orient_S_w_w_ne hP d hTx1)).mp hw1
      have pw2 := (orientSign_eq_true_iff _ _ _).mp hw2
      exact two_path_enclosure_either hP.toEnclosureDomain (hP.s_ne_w d Tx) hp1 hp2
        (Or.inr ⟨interiorOnRight_four nw1 nu, interiorOnLeft_four pw2 pv⟩)
    · have pu := (orientSign_eq_true_iff _ _ _).mp hsu
      have nv := (orientSign_eq_false_iff_of_ne_zero (orient_S_w_S_ne hP hdv Tx)).mp hsv
      have pw1 := (orientSign_eq_true_iff _ _ _).mp hw1
      have nw2 := (orientSign_eq_false_iff_of_ne_zero (orient_S_w_w_ne hP d hTx2)).mp hw2
      exact two_path_enclosure_either hP.toEnclosureDomain (hP.s_ne_w d Tx) hp1 hp2
        (Or.inl ⟨interiorOnLeft_four pw1 pu, interiorOnRight_four nw2 nv⟩)
  exact hd_miss ((hP.shatters Tx d).mp (sees_symm hsees))


/-! ## 5. Clauses `(C10)` & `(C11)`: Soundness Bridges from `NewEnclosureLemmas` to Boolean Clauses -/

/-! ### 5A. `vis_SS` Round-1 Chord, Round-2 Triangle, and Multi-Round Iterated Closure `(C11)` -/

/-- **Round 1 (`vis_SS_chord_bool`)**: Boolean chirotope trigger for `vis_SS_chord_enclosure`. -/
theorem vis_SS_chord_bool {n : ℕ} {P : Set (ℝ × ℝ)}
    {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ}
    (hP : ShatteredSimplePolygon P S w)
    {a b : Fin n} (hab : a ≠ b) {T₁ T₂ : Finset (Fin n)}
    (ha1 : a ∈ T₁) (hb1 : b ∈ T₁) (ha2 : a ∈ T₂) (hb2 : b ∈ T₂)
    (hopp : oppSideBool (S a) (S b) (w T₁) (w T₂) = true) :
    Sees P (S a) (S b) :=
  vis_SS_chord_enclosure hP hab ha1 hb1 ha2 hb2
    ((oppSideBool_iff_mul_neg (orient_S_S_w_ne hP hab T₁) (orient_S_S_w_ne hP hab T₂)).mp hopp)

/-- **Round 2 Vertex Clause (`vis_SS_tri_vertex_omitted_outer_clause`)**:
    Even with the outer-triangle sign `orientSign (w T₃) (S a) (S b)` omitted (as in `bulk_cegar_enclosure`),
    if `oppSideBool (S a) (S b) (w T₁) (w T₂) = true` (`a, b ∈ T₁ ∩ T₂ ∩ T₃`) and `Tf` misses `a` (or `b`),
    `w Tf` cannot satisfy `inOpenTriSideBool sd (w Tf) (w T₃) (S a) (S b) = true`. -/
theorem vis_SS_tri_vertex_omitted_outer_clause {n : ℕ} {P : Set (ℝ × ℝ)}
    {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ}
    (hP : ShatteredSimplePolygon P S w)
    {a b : Fin n} (hab : a ≠ b) {T₁ T₂ T₃ Tf : Finset (Fin n)}
    (ha1 : a ∈ T₁) (hb1 : b ∈ T₁) (ha2 : a ∈ T₂) (hb2 : b ∈ T₂)
    (ha3 : a ∈ T₃) (hb3 : b ∈ T₃) (hmiss : a ∉ Tf ∨ b ∉ Tf)
    (sd : Bool) :
    ¬ (oppSideBool (S a) (S b) (w T₁) (w T₂) = true ∧
       inOpenTriSideBool sd (w Tf) (w T₃) (S a) (S b) = true) := by
  have hTf_ne3 : T₃ ≠ Tf := by
    rintro rfl
    rcases hmiss with ha | hb
    · exact ha ha3
    · exact hb hb3
  rintro ⟨hopp, hside⟩
  have hmul := (oppSideBool_iff_mul_neg (orient_S_S_w_ne hP hab T₁) (orient_S_S_w_ne hP hab T₂)).mp hopp
  have htri_f : InOpenTri (w T₃) (S a) (S b) (w Tf) :=
    (inOpenTri_and_orientSign_of_side
      (orient_w_S_w_ne hP hTf_ne3 a)
      (orient_S_S_w_ne hP hab Tf)
      (orient_S_w_w_ne hP b hTf_ne3) hside).1
  obtain ⟨_, hsees⟩ := vis_SS_triangle_enclosure hP hab ha1 hb1 ha2 hb2 hmul ha3 hb3
  obtain ⟨hfa, hfb⟩ := hsees (w Tf) (inOpenTri_mem_convexHull htri_f)
  rcases hmiss with ha_not | hb_not
  · exact ha_not ((hP.shatters Tf a).mp hfa)
  · exact hb_not ((hP.shatters Tf b).mp hfb)

/-- **Round 2 Vertex Clause (`vis_SS_tri_vertex_clause`, `inOpenTriBool` form)**. -/
theorem vis_SS_tri_vertex_clause {n : ℕ} {P : Set (ℝ × ℝ)}
    {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ}
    (hP : ShatteredSimplePolygon P S w)
    {a b : Fin n} (hab : a ≠ b) {T₁ T₂ T₃ Tf : Finset (Fin n)}
    (ha1 : a ∈ T₁) (hb1 : b ∈ T₁) (ha2 : a ∈ T₂) (hb2 : b ∈ T₂)
    (ha3 : a ∈ T₃) (hb3 : b ∈ T₃) (hmiss : a ∉ Tf ∨ b ∉ Tf) :
    ¬ (oppSideBool (S a) (S b) (w T₁) (w T₂) = true ∧
       inOpenTriBool (w Tf) (w T₃) (S a) (S b) = true) := by
  rintro ⟨hopp, htri⟩
  unfold inOpenTriBool at htri
  rw [Bool.or_eq_true] at htri
  rcases htri with ht | hf
  · exact vis_SS_tri_vertex_omitted_outer_clause hP hab ha1 hb1 ha2 hb2 ha3 hb3 hmiss true ⟨hopp, ht⟩
  · exact vis_SS_tri_vertex_omitted_outer_clause hP hab ha1 hb1 ha2 hb2 ha3 hb3 hmiss false ⟨hopp, hf⟩

/-- **Round 2 Pair Clause (`vis_SS_tri_pair_clause`)**:
    Under `vis_SS` Round-2 enclosure of `tri(w T₃, S a, S b)`, no witness `w Tf` and missed point `S fj` (`fj ∉ Tf`)
    can both lie inside `int tri(w T₃, S a, S b)`. -/
theorem vis_SS_tri_pair_clause {n : ℕ} {P : Set (ℝ × ℝ)}
    {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ}
    (hP : ShatteredSimplePolygon P S w)
    {a b fj : Fin n} (hab : a ≠ b) (hfja : fj ≠ a) (hfjb : fj ≠ b)
    {T₁ T₂ T₃ Tf : Finset (Fin n)} (hT3f : T₃ ≠ Tf)
    (ha1 : a ∈ T₁) (hb1 : b ∈ T₁) (ha2 : a ∈ T₂) (hb2 : b ∈ T₂)
    (ha3 : a ∈ T₃) (hb3 : b ∈ T₃) (hfj_miss : fj ∉ Tf) :
    ¬ (oppSideBool (S a) (S b) (w T₁) (w T₂) = true ∧
       inOpenTriBool (w Tf) (w T₃) (S a) (S b) = true ∧
       inOpenTriBool (S fj) (w T₃) (S a) (S b) = true) := by
  rintro ⟨hopp, hfw_b, hfj_b⟩
  have hmul := (oppSideBool_iff_mul_neg (orient_S_S_w_ne hP hab T₁) (orient_S_S_w_ne hP hab T₂)).mp hopp
  obtain ⟨htri_sub, _⟩ := vis_SS_triangle_enclosure hP hab ha1 hb1 ha2 hb2 hmul ha3 hb3
  have hfw_in : w Tf ∈ convexHull ℝ ({w T₃, S a, S b} : Set (ℝ × ℝ)) :=
    inOpenTri_mem_convexHull ((inOpenTriBool_iff_inOpenTri
      (orient_w_S_w_ne hP hT3f a) (orient_S_S_w_ne hP hab Tf) (orient_S_w_w_ne hP b hT3f)).mp hfw_b)
  have hfj_in : S fj ∈ convexHull ℝ ({w T₃, S a, S b} : Set (ℝ × ℝ)) :=
    inOpenTri_mem_convexHull ((inOpenTriBool_iff_inOpenTri
      (orient_w_S_S_ne hP T₃ hfja.symm)
      (orient_S_S_S_ne hP hab hfjb.symm hfja.symm)
      (orient_S_w_S_ne hP hfjb.symm T₃)).mp hfj_b)
  exact hfj_miss ((hP.shatters Tf fj).mp (sees_of_mem_convexHull_tri htri_sub hfw_in hfj_in))

/-- Round-indexed pure-chirotope visibility closure `G_0 ⊆ G_1 ⊆ ... ⊆ G_r` (`Lemma 2.11`, `(C11)`,
    and `bulk_cegar_enclosure`):
    Starting from any base visibility graph `G₀` on `X : ι → ℝ × ℝ`, round `r + 1` adds edges by:
    - `(E1)` two `G_r`-paths `[u, ..., v]` whose internal vertices have `orientSign = true` and `orientSign = false` wrt `(X u, X v)`,
    - `(E2)` a `G_r`-triangle `(a, b, c)` containing `u` (`inOpenTriSideBool sd`) and `v` (`v ∈ {a, b, c}` or `inOpenTriSideBool sd'`), or symmetrically swapping `u, v`. -/
def IteratedVisAtRound {ι : Type*} (X : ι → ℝ × ℝ) (G₀ : ι → ι → Prop) : ℕ → ι → ι → Prop
  | 0, u, v => G₀ u v ∨ G₀ v u
  | r + 1, u, v =>
      IteratedVisAtRound X G₀ r u v ∨
      (u ≠ v ∧ ∃ (π₁ π₂ : List ι) (hne₁ : π₁ ≠ []) (hne₂ : π₂ ≠ []),
        π₁.head hne₁ = u ∧ π₁.getLast hne₁ = v ∧ 3 ≤ π₁.length ∧
        π₁.IsChain (IteratedVisAtRound X G₀ r) ∧
        (∀ (m : ℕ) (hm : m < π₁.length), 0 < m → m + 1 < π₁.length →
          π₁[m]'hm ≠ u ∧ π₁[m]'hm ≠ v ∧ orientSign (X u) (X v) (X (π₁[m]'hm)) = true) ∧
        π₂.head hne₂ = u ∧ π₂.getLast hne₂ = v ∧ 3 ≤ π₂.length ∧
        π₂.IsChain (IteratedVisAtRound X G₀ r) ∧
        (∀ (m : ℕ) (hm : m < π₂.length), 0 < m → m + 1 < π₂.length →
          π₂[m]'hm ≠ u ∧ π₂[m]'hm ≠ v ∧ orientSign (X u) (X v) (X (π₂[m]'hm)) = false)) ∨
      (∃ (a b c : ι) (sd : Bool),
        a ≠ b ∧ b ≠ c ∧ c ≠ a ∧
        IteratedVisAtRound X G₀ r a b ∧
        IteratedVisAtRound X G₀ r b c ∧
        IteratedVisAtRound X G₀ r c a ∧
        ((u ≠ a ∧ u ≠ b ∧ u ≠ c ∧ inOpenTriSideBool sd (X u) (X a) (X b) (X c) = true ∧
          ((v = a ∨ v = b ∨ v = c) ∨
           (v ≠ a ∧ v ≠ b ∧ v ≠ c ∧ ∃ sd' : Bool, inOpenTriSideBool sd' (X v) (X a) (X b) (X c) = true))) ∨
         (v ≠ a ∧ v ≠ b ∧ v ≠ c ∧ inOpenTriSideBool sd (X v) (X a) (X b) (X c) = true ∧
          (u = a ∨ u = b ∨ u = c))))

private lemma isChain_map_of_rel {α β : Type*} {R : α → α → Prop} {Q : β → β → Prop}
    (f : α → β) (himp : ∀ x y, R x y → Q (f x) (f y)) :
    ∀ l : List α, l.IsChain R → (l.map f).IsChain Q
  | [], _ => List.isChain_nil
  | [_], _ => List.isChain_singleton _
  | x :: y :: xs, h => by
    rw [List.isChain_cons_cons] at h
    exact List.isChain_cons_cons.mpr ⟨himp x y h.1, isChain_map_of_rel f himp (y :: xs) h.2⟩

/-- **Clause `(C11)` Soundness (`iterated_enclosure_soundness_C11`)**:
    For every round `r : ℕ`, every edge derived in `IteratedVisAtRound (pointSeq S w W₀) G₀ r`
    is a genuine visible segment in `P`, so no witness `w (W₀ j)` and missed point `i ∉ W₀ j`
    can ever become connected at any round `r`. -/
theorem iterated_enclosure_soundness_C11 {n k : ℕ} {P : Set (ℝ × ℝ)}
    {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ}
    (hP : ShatteredSimplePolygon P S w) (W₀ : Fin k ↪ Finset (Fin n))
    {G₀ : Fin (n + k) → Fin (n + k) → Prop}
    (hG₀ : ∀ u v, G₀ u v → Sees P (pointSeq S w W₀ u) (pointSeq S w W₀ v)) :
    (∀ r u v, IteratedVisAtRound (pointSeq S w W₀) G₀ r u v →
      Sees P (pointSeq S w W₀ u) (pointSeq S w W₀ v)) ∧
    (∀ (r : ℕ) (i : Fin n) (j : Fin k), i ∉ W₀ j →
      ¬ IteratedVisAtRound (pointSeq S w W₀) G₀ r (Fin.castAdd k i) (Fin.natAdd n j)) := by
  let X := pointSeq S w W₀
  have hX : NoThreeCollinear X := noThreeCollinear_pointSeq hP W₀
  have hX_in_P : ∀ u : Fin (n + k), X u ∈ P := by
    refine Fin.addCases (fun i => ?_) (fun j => ?_)
    · simp only [X, pointSeq, Fin.addCases_left]; exact hP.s_in_P i
    · simp only [X, pointSeq, Fin.addCases_right]; exact hP.w_in_P (W₀ j)
  have h_sound : ∀ r u v, IteratedVisAtRound X G₀ r u v → Sees P (X u) (X v) := by
    intro r
    induction r with
    | zero =>
      intro u v h0
      rcases h0 with huv | hvu
      · exact hG₀ u v huv
      · exact sees_symm (hG₀ v u hvu)
    | succ r ih =>
      intro u v hstep
      rcases hstep with hprev | ⟨huv, π₁, π₂, hne₁, hne₂, hhd₁, hlst₁, hlen₁, hch₁, hleft,
          hhd₂, hlst₂, hlen₂, hch₂, hright⟩ |
        ⟨a, b, c, sd, hab, hbc, hca, hab_e, hbc_e, hca_e, htri_cases⟩
      · exact ih u v hprev
      · have hp₁ : IsPolygonalPathIn P (X u) (X v) (π₁.map X) := by
          refine ⟨by cases π₁ with | nil => exact False.elim (hne₁ rfl) | cons _ _ => exact List.cons_ne_nil _ _,
            ?_, ?_, ?_, isChain_map_of_rel X ih π₁ hch₁⟩
          · rw [List.head_map, hhd₁]
          · rw [List.getLast_map, hlst₁]
          · intro pt hpt
            rcases List.mem_map.mp hpt with ⟨idx, _, rfl⟩
            exact hX_in_P idx
        have hp₂ : IsPolygonalPathIn P (X u) (X v) (π₂.map X) := by
          refine ⟨by cases π₂ with | nil => exact False.elim (hne₂ rfl) | cons _ _ => exact List.cons_ne_nil _ _,
            ?_, ?_, ?_, isChain_map_of_rel X ih π₂ hch₂⟩
          · rw [List.head_map, hhd₂]
          · rw [List.getLast_map, hlst₂]
          · intro pt hpt
            rcases List.mem_map.mp hpt with ⟨idx, _, rfl⟩
            exact hX_in_P idx
        have hL : InteriorOnLeft (X u) (X v) (π₁.map X) := by
          refine ⟨by simpa using hlen₁, fun idx hidx h0 hlt => ?_⟩
          rw [List.length_map] at hidx hlt
          rw [List.getElem_map]
          exact (orientSign_eq_true_iff _ _ _).mp (hleft idx hidx h0 hlt).2.2
        have hR : InteriorOnRight (X u) (X v) (π₂.map X) := by
          refine ⟨by simpa using hlen₂, fun idx hidx h0 hlt => ?_⟩
          rw [List.length_map] at hidx hlt
          rw [List.getElem_map]
          obtain ⟨hku, hkv, hfalse⟩ := hright idx hidx h0 hlt
          exact (orientSign_eq_false_iff_of_ne_zero (hX.2 u v (π₂[idx]'hidx) huv hkv.symm hku.symm)).mp hfalse
        exact hP.two_path_enclosure (X u) (X v) (π₁.map X) (π₂.map X) (hX.1.ne huv) hp₁ hp₂ hL hR
      · have htri_P : convexHull ℝ ({X a, X b, X c} : Set (ℝ × ℝ)) ⊆ P :=
          hP.triangle_enclosure (X a) (hX_in_P a) (X b) (hX_in_P b) (X c) (hX_in_P c)
            (ih a b hab_e) (ih b c hbc_e) (sees_symm (ih c a hca_e))
        rcases htri_cases with ⟨hua, hub, huc, hu_in, hv⟩ | ⟨hva, hvb, hvc, hv_in, hu⟩
        · have hu_hull : X u ∈ convexHull ℝ ({X a, X b, X c} : Set (ℝ × ℝ)) :=
            inOpenTri_mem_convexHull
              (inOpenTri_and_orientSign_of_side
                (hX.2 a b u hab hub.symm hua.symm)
                (hX.2 b c u hbc huc.symm hub.symm)
                (hX.2 c a u hca hua.symm huc.symm) hu_in).1
          have hv_hull : X v ∈ convexHull ℝ ({X a, X b, X c} : Set (ℝ × ℝ)) := by
            rcases hv with (rfl | rfl | rfl) | ⟨hva, hvb, hvc, sd', hv_in⟩
            · exact mem_convexHull_tri_left
            · exact mem_convexHull_tri_mid
            · exact mem_convexHull_tri_right
            · exact inOpenTri_mem_convexHull
                (inOpenTri_and_orientSign_of_side
                  (hX.2 a b v hab hvb.symm hva.symm)
                  (hX.2 b c v hbc hvc.symm hvb.symm)
                  (hX.2 c a v hca hva.symm hvc.symm) hv_in).1
          exact sees_of_mem_convexHull_tri htri_P hu_hull hv_hull
        · have hv_hull : X v ∈ convexHull ℝ ({X a, X b, X c} : Set (ℝ × ℝ)) :=
            inOpenTri_mem_convexHull
              (inOpenTri_and_orientSign_of_side
                (hX.2 a b v hab hvb.symm hva.symm)
                (hX.2 b c v hbc hvc.symm hvb.symm)
                (hX.2 c a v hca hva.symm hvc.symm) hv_in).1
          have hu_hull : X u ∈ convexHull ℝ ({X a, X b, X c} : Set (ℝ × ℝ)) := by
            rcases hu with rfl | rfl | rfl
            · exact mem_convexHull_tri_left
            · exact mem_convexHull_tri_mid
            · exact mem_convexHull_tri_right
          exact sees_of_mem_convexHull_tri htri_P hu_hull hv_hull
  refine ⟨h_sound, fun r i j hi_not he => ?_⟩
  have hs := h_sound r (Fin.castAdd k i) (Fin.natAdd n j) he
  simp only [X, pointSeq, Fin.addCases_left, Fin.addCases_right] at hs
  exact hi_not ((hP.shatters (W₀ j) i).mp (sees_symm hs))


/-! ### 5B. Crossed-Segment Triangle `T1` and `T2` Boolean Clauses (`(C10)`) -/

/-- **Rule `T1_b` (`crossed_tri_T1_vertex_clause`, `gen_chiro_*.cpp` line 624)**:
    If `w T₁` sees `S a, S b` (`a ≠ b`), `w T₂` sees `S b` (`T₁ ≠ T₂`), and `w Tf` (`Tf ≠ T₁, T₂`) misses `S b`,
    then `segsCrossBool (w T₁) (S a) (w T₂) (S b)` and the three `sameSideBool` tests on `w Tf` cannot all hold. -/
theorem crossed_tri_T1_vertex_clause {n : ℕ} {P : Set (ℝ × ℝ)}
    {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ}
    (hP : ShatteredSimplePolygon P S w)
    {a b : Fin n} (hab : a ≠ b)
    {T₁ T₂ Tf : Finset (Fin n)} (hT12 : T₁ ≠ T₂) (hTf1 : Tf ≠ T₁) (hTf2 : Tf ≠ T₂)
    (ha1 : a ∈ T₁) (hb1 : b ∈ T₁) (hb2 : b ∈ T₂) (hb_miss : b ∉ Tf) :
    ¬ (segsCrossBool (w T₁) (S a) (w T₂) (S b) = true ∧
       sameSideBool (w T₁) (S a) (w Tf) (S b) = true ∧
       sameSideBool (w T₂) (S b) (w Tf) (w T₁) = true ∧
       sameSideBool (w T₁) (S b) (w Tf) (S a) = true) := by
  rintro ⟨hcr, hs1, hs2, hs3⟩
  have hcross : ProperCross (w T₁) (S a) (w T₂) (S b) :=
    (segsCrossBool_iff_properCross
      (orient_w_S_w_ne hP hT12 a) (orient_w_S_S_ne hP T₁ hab)
      (orient_w_S_w_ne hP hT12.symm b) (orient_w_S_S_ne hP T₂ hab.symm)).mp hcr
  obtain ⟨_, _, _, _, htrap⟩ := crossed_segment_tri_T1 hP ha1 hb1 hb2 hcross
  have hsees := (htrap (w Tf)
    ((sameSideBool_iff_sameSide (orient_w_S_w_ne hP hTf1.symm a) (orient_w_S_S_ne hP T₁ hab)).mp hs1)
    ((sameSideBool_iff_sameSide (orient_w_S_w_ne hP hTf2.symm b) (orient_w_S_w_ne hP hT12.symm b)).mp hs2)
    ((sameSideBool_iff_sameSide (orient_w_S_w_ne hP hTf1.symm b) (orient_w_S_S_ne hP T₁ hab.symm)).mp hs3)).2.2
  exact hb_miss ((hP.shatters Tf b).mp hsees)

/-- **Rule `T1_both` (`crossed_tri_T1_pair_clause`, `gen_chiro_*.cpp` line 632)**:
    If `[w T₁, S a]` crosses `[w T₂, S b]`, no witness `w Tf` and missed point `S fj` (`fj ∉ Tf`)
    can both satisfy the three `sameSideBool` tests of `tri(w T₁, S b, X)`. -/
theorem crossed_tri_T1_pair_clause {n : ℕ} {P : Set (ℝ × ℝ)}
    {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ}
    (hP : ShatteredSimplePolygon P S w)
    {a b fj : Fin n} (hab : a ≠ b) (hfja : fj ≠ a) (hfjb : fj ≠ b)
    {T₁ T₂ Tf : Finset (Fin n)} (hT12 : T₁ ≠ T₂) (hTf1 : Tf ≠ T₁) (hTf2 : Tf ≠ T₂)
    (ha1 : a ∈ T₁) (hb1 : b ∈ T₁) (hb2 : b ∈ T₂) (hfj_miss : fj ∉ Tf) :
    ¬ (segsCrossBool (w T₁) (S a) (w T₂) (S b) = true ∧
       sameSideBool (w T₁) (S a) (w Tf) (S b) = true ∧
       sameSideBool (w T₂) (S b) (w Tf) (w T₁) = true ∧
       sameSideBool (w T₁) (S b) (w Tf) (S a) = true ∧
       sameSideBool (w T₁) (S a) (S fj) (S b) = true ∧
       sameSideBool (w T₂) (S b) (S fj) (w T₁) = true ∧
       sameSideBool (w T₁) (S b) (S fj) (S a) = true) := by
  rintro ⟨hcr, hw1, hw2, hw3, hj1, hj2, hj3⟩
  have hcross : ProperCross (w T₁) (S a) (w T₂) (S b) :=
    (segsCrossBool_iff_properCross
      (orient_w_S_w_ne hP hT12 a) (orient_w_S_S_ne hP T₁ hab)
      (orient_w_S_w_ne hP hT12.symm b) (orient_w_S_S_ne hP T₂ hab.symm)).mp hcr
  obtain ⟨X, _, _, htri, htrap⟩ := crossed_segment_tri_T1 hP ha1 hb1 hb2 hcross
  have hfw_open := (htrap (w Tf)
    ((sameSideBool_iff_sameSide (orient_w_S_w_ne hP hTf1.symm a) (orient_w_S_S_ne hP T₁ hab)).mp hw1)
    ((sameSideBool_iff_sameSide (orient_w_S_w_ne hP hTf2.symm b) (orient_w_S_w_ne hP hT12.symm b)).mp hw2)
    ((sameSideBool_iff_sameSide (orient_w_S_w_ne hP hTf1.symm b) (orient_w_S_S_ne hP T₁ hab.symm)).mp hw3)).1
  have hfj_open := (htrap (S fj)
    ((sameSideBool_iff_sameSide (orient_w_S_S_ne hP T₁ hfja.symm) (orient_w_S_S_ne hP T₁ hab)).mp hj1)
    ((sameSideBool_iff_sameSide (orient_w_S_S_ne hP T₂ hfjb.symm) (orient_w_S_w_ne hP hT12.symm b)).mp hj2)
    ((sameSideBool_iff_sameSide (orient_w_S_S_ne hP T₁ hfjb.symm) (orient_w_S_S_ne hP T₁ hab.symm)).mp hj3)).1
  exact hfj_miss ((hP.shatters Tf fj).mp
    (sees_of_mem_convexHull_tri htri (inOpenTri_mem_convexHull hfw_open) (inOpenTri_mem_convexHull hfj_open)))

/-- **Rule `T2` (`crossed_tri_T2_pair_clause`, `gen_chiro_*.cpp` line 664)**:
    If `w T₂` sees `S b, S c` (`b ≠ c`), `w T₁` sees `S a`, and `[w T₁, S a]` crosses both
    `[w T₂, S b]` and `[w T₂, S c]`, no witness `w Tf` and missed point `S fj` (`fj ∉ Tf`)
    can both satisfy the three `sameSideBool` tests of `tri(w T₂, Xb, Xc)`. -/
theorem crossed_tri_T2_pair_clause {n : ℕ} {P : Set (ℝ × ℝ)}
    {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ}
    (hP : ShatteredSimplePolygon P S w)
    {a b c fj : Fin n} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hfja : fj ≠ a) (hfjb : fj ≠ b) (hfjc : fj ≠ c)
    {T₁ T₂ Tf : Finset (Fin n)} (hT12 : T₁ ≠ T₂) (hTf1 : Tf ≠ T₁) (hTf2 : Tf ≠ T₂)
    (ha1 : a ∈ T₁) (hb2 : b ∈ T₂) (hc2 : c ∈ T₂) (hfj_miss : fj ∉ Tf) :
    ¬ (segsCrossBool (w T₁) (S a) (w T₂) (S b) = true ∧
       segsCrossBool (w T₁) (S a) (w T₂) (S c) = true ∧
       sameSideBool (w T₁) (S a) (w Tf) (w T₂) = true ∧
       sameSideBool (w T₂) (S b) (w Tf) (S c) = true ∧
       sameSideBool (w T₂) (S c) (w Tf) (S b) = true ∧
       sameSideBool (w T₁) (S a) (S fj) (w T₂) = true ∧
       sameSideBool (w T₂) (S b) (S fj) (S c) = true ∧
       sameSideBool (w T₂) (S c) (S fj) (S b) = true) := by
  rintro ⟨hcr_b, hcr_c, hw1, hw2, hw3, hj1, hj2, hj3⟩
  have hcross_b : ProperCross (w T₁) (S a) (w T₂) (S b) :=
    (segsCrossBool_iff_properCross
      (orient_w_S_w_ne hP hT12 a) (orient_w_S_S_ne hP T₁ hab)
      (orient_w_S_w_ne hP hT12.symm b) (orient_w_S_S_ne hP T₂ hab.symm)).mp hcr_b
  have hcross_c : ProperCross (w T₁) (S a) (w T₂) (S c) :=
    (segsCrossBool_iff_properCross
      (orient_w_S_w_ne hP hT12 a) (orient_w_S_S_ne hP T₁ hac)
      (orient_w_S_w_ne hP hT12.symm c) (orient_w_S_S_ne hP T₂ hac.symm)).mp hcr_c
  obtain ⟨Xb, Xc, _, _, _, _, htri, htrap⟩ := crossed_segment_tri_T2 hP hbc ha1 hb2 hc2 hcross_b hcross_c
  have hfw_open := (htrap (w Tf)
    ((sameSideBool_iff_sameSide (orient_w_S_w_ne hP hTf1.symm a) (orient_w_S_w_ne hP hT12 a)).mp hw1)
    ((sameSideBool_iff_sameSide (orient_w_S_w_ne hP hTf2.symm b) (orient_w_S_S_ne hP T₂ hbc)).mp hw2)
    ((sameSideBool_iff_sameSide (orient_w_S_w_ne hP hTf2.symm c) (orient_w_S_S_ne hP T₂ hbc.symm)).mp hw3)).1
  have hfj_open := (htrap (S fj)
    ((sameSideBool_iff_sameSide (orient_w_S_S_ne hP T₁ hfja.symm) (orient_w_S_w_ne hP hT12 a)).mp hj1)
    ((sameSideBool_iff_sameSide (orient_w_S_S_ne hP T₂ hfjb.symm) (orient_w_S_S_ne hP T₂ hbc)).mp hj2)
    ((sameSideBool_iff_sameSide (orient_w_S_S_ne hP T₂ hfjc.symm) (orient_w_S_S_ne hP T₂ hbc.symm)).mp hj3)).1
  exact hfj_miss ((hP.shatters Tf fj).mp
    (sees_of_mem_convexHull_tri htri (inOpenTri_mem_convexHull hfw_open) (inOpenTri_mem_convexHull hfj_open)))


/-! ### 5C. `N1` Convex-Quad & All 4 Reflex-Dart Star-Kernel Boolean Clauses (`(C10)`) -/

private lemma strictConvexQuad_and_mem_of_sideBool {s : Bool} {p₀ p₁ p₂ p₃ z : ℝ × ℝ}
    (hq0 : orient2D p₀ p₁ p₂ ≠ 0) (hq1 : orient2D p₁ p₂ p₃ ≠ 0)
    (hq2 : orient2D p₂ p₃ p₀ ≠ 0) (hq3 : orient2D p₃ p₀ p₁ ≠ 0)
    (hz0 : orient2D p₀ p₁ z ≠ 0) (hz1 : orient2D p₁ p₂ z ≠ 0)
    (hz2 : orient2D p₂ p₃ z ≠ 0) (hz3 : orient2D p₃ p₀ z ≠ 0)
    (hquad_b : strictConvexQuadSideBool s p₀ p₁ p₂ p₃ = true)
    (hz_b : inConvexQuadSideBool s z p₀ p₁ p₂ p₃ = true) :
    StrictConvexQuad p₀ p₁ p₂ p₃ ∧ z ∈ convexHull ℝ ({p₀, p₁, p₂, p₃} : Set (ℝ × ℝ)) := by
  unfold strictConvexQuadSideBool at hquad_b
  unfold inConvexQuadSideBool at hz_b
  simp only [Bool.and_eq_true, beq_iff_eq] at hquad_b hz_b
  rcases hquad_b with ⟨⟨⟨hq0_s, hq1_s⟩, hq2_s⟩, hq3_s⟩
  rcases hz_b with ⟨⟨⟨hz0_s, hz1_s⟩, hz2_s⟩, hz3_s⟩
  have hmem_of_ccw : ∀ {q₀ q₁ q₂ q₃ x : ℝ × ℝ},
      0 < orient2D q₀ q₁ q₂ → 0 < orient2D q₁ q₂ q₃ →
      0 < orient2D q₂ q₃ q₀ → 0 < orient2D q₃ q₀ q₁ →
      0 ≤ orient2D q₀ q₁ x → 0 ≤ orient2D q₁ q₂ x →
      0 ≤ orient2D q₂ q₃ x → 0 ≤ orient2D q₃ q₀ x →
      x ∈ convexHull ℝ ({q₀, q₁, q₂, q₃} : Set (ℝ × ℝ)) := by
    intro q₀ q₁ q₂ q₃ x c0 c1 c2 c3 x0 x1 x2 x3
    rcases le_total 0 (orient2D q₀ q₂ x) with hdiag | hdiag
    · have hc2' : 0 < orient2D q₀ q₂ q₃ := by rw [← orient2D_cycle]; exact c2
      have hin := (inClosedTri_iff_mem_convexHull _ _ _ _).mp
        (inClosedTri_of_orient_nonneg hc2' hdiag x2 x3)
      refine convexHull_mono ?_ hin
      intro u hu; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu ⊢
      rcases hu with rfl | rfl | rfl <;> simp
    · have hx20 : 0 ≤ orient2D q₂ q₀ x := by
        rw [show orient2D q₂ q₀ x = -orient2D q₀ q₂ x by unfold orient2D; ring]; linarith
      have hin := (inClosedTri_iff_mem_convexHull _ _ _ _).mp
        (inClosedTri_of_orient_nonneg c0 x0 x1 hx20)
      refine convexHull_mono ?_ hin
      intro u hu; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu ⊢
      rcases hu with rfl | rfl | rfl <;> simp
  cases s
  · have n0 := (orientSign_eq_false_iff_of_ne_zero hq0).mp hq0_s
    have n1 := (orientSign_eq_false_iff_of_ne_zero hq1).mp hq1_s
    have n2 := (orientSign_eq_false_iff_of_ne_zero hq2).mp hq2_s
    have n3 := (orientSign_eq_false_iff_of_ne_zero hq3).mp hq3_s
    have zn0 := (orientSign_eq_false_iff_of_ne_zero hz0).mp hz0_s
    have zn1 := (orientSign_eq_false_iff_of_ne_zero hz1).mp hz1_s
    have zn2 := (orientSign_eq_false_iff_of_ne_zero hz2).mp hz2_s
    have zn3 := (orientSign_eq_false_iff_of_ne_zero hz3).mp hz3_s
    have hcw : StrictConvexCCWQuad p₃ p₂ p₁ p₀ :=
      ⟨by rw [show orient2D p₃ p₂ p₁ = -orient2D p₁ p₂ p₃ by unfold orient2D; ring]; linarith,
       by rw [show orient2D p₂ p₁ p₀ = -orient2D p₀ p₁ p₂ by unfold orient2D; ring]; linarith,
       by rw [show orient2D p₁ p₀ p₃ = -orient2D p₃ p₀ p₁ by unfold orient2D; ring]; linarith,
       by rw [show orient2D p₀ p₃ p₂ = -orient2D p₂ p₃ p₀ by unfold orient2D; ring]; linarith⟩
    refine ⟨Or.inr hcw, ?_⟩
    have hm := hmem_of_ccw hcw.1 hcw.2.1 hcw.2.2.1 hcw.2.2.2
      (by rw [show orient2D p₃ p₂ z = -orient2D p₂ p₃ z by unfold orient2D; ring]; linarith)
      (by rw [show orient2D p₂ p₁ z = -orient2D p₁ p₂ z by unfold orient2D; ring]; linarith)
      (by rw [show orient2D p₁ p₀ z = -orient2D p₀ p₁ z by unfold orient2D; ring]; linarith)
      (by rw [show orient2D p₀ p₃ z = -orient2D p₃ p₀ z by unfold orient2D; ring]; linarith)
    have hset : ({p₃, p₂, p₁, p₀} : Set (ℝ × ℝ)) = {p₀, p₁, p₂, p₃} := by
      ext u; simp [or_comm, or_left_comm]
    rwa [hset] at hm
  · have c0 := (orientSign_eq_true_iff _ _ _).mp hq0_s
    have c1 := (orientSign_eq_true_iff _ _ _).mp hq1_s
    have c2 := (orientSign_eq_true_iff _ _ _).mp hq2_s
    have c3 := (orientSign_eq_true_iff _ _ _).mp hq3_s
    have zc0 := le_of_lt ((orientSign_eq_true_iff _ _ _).mp hz0_s)
    have zc1 := le_of_lt ((orientSign_eq_true_iff _ _ _).mp hz1_s)
    have zc2 := le_of_lt ((orientSign_eq_true_iff _ _ _).mp hz2_s)
    have zc3 := le_of_lt ((orientSign_eq_true_iff _ _ _).mp hz3_s)
    exact ⟨Or.inl ⟨c0, c1, c2, c3⟩, hmem_of_ccw c0 c1 c2 c3 zc0 zc1 zc2 zc3⟩

/-- **Rule `N1` Convex-Quad Vertex Clause (`n1_convex_quad_vertex_clause`, `gen_chiro_*.cpp` lines 176–177 & `find_violated_n1_cuts` line 229)**:
    If `w T₁, w T₂` (`T₁ ≠ T₂`) both see `S a, S b` (`a ≠ b`), `(w T₁, S a, w T₂, S b)` is strictly convex
    with orientation `s`, and `Tf` (`Tf ≠ T₁, T₂`) misses `a` (or `b`), then `w Tf` cannot lie inside the quad. -/
theorem n1_convex_quad_vertex_clause {n : ℕ} {P : Set (ℝ × ℝ)}
    {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ}
    (hP : ShatteredSimplePolygon P S w)
    {a b : Fin n} (hab : a ≠ b)
    {T₁ T₂ Tf : Finset (Fin n)} (hT12 : T₁ ≠ T₂) (hTf1 : Tf ≠ T₁) (hTf2 : Tf ≠ T₂)
    (ha1 : a ∈ T₁) (hb1 : b ∈ T₁) (ha2 : a ∈ T₂) (hb2 : b ∈ T₂)
    (hmiss : a ∉ Tf ∨ b ∉ Tf) (s : Bool) :
    ¬ (strictConvexQuadSideBool s (w T₁) (S a) (w T₂) (S b) = true ∧
       inConvexQuadSideBool s (w Tf) (w T₁) (S a) (w T₂) (S b) = true) := by
  rintro ⟨hq_b, hf_b⟩
  obtain ⟨hquad, hf_mem⟩ := strictConvexQuad_and_mem_of_sideBool
    (orient_w_S_w_ne hP hT12 a) (orient_S_w_S_ne hP hab T₂)
    (orient_w_S_w_ne hP hT12.symm b) (orient_S_w_S_ne hP hab.symm T₁)
    (orient_w_S_w_ne hP hTf1.symm a) (orient_S_w_w_ne hP a hTf2.symm)
    (orient_w_S_w_ne hP hTf2.symm b) (orient_S_w_w_ne hP b hTf1.symm) hq_b hf_b
  obtain ⟨_, hsees⟩ := convex_quad_vertex_enclosure_N1 hP ha1 hb1 ha2 hb2 hquad
  obtain ⟨hsa, hsb⟩ := hsees (w Tf) hf_mem
  rcases hmiss with ha_not | hb_not
  · exact ha_not ((hP.shatters Tf a).mp hsa)
  · exact hb_not ((hP.shatters Tf b).mp hsb)

/-- **Convex-Quad 4-Cycle Pair Clause (`n1_convex_quad_pair_clause`, `gen_chiro_*.cpp` lines 151, 154)**:
    If `(w T₁, S a, w T₂, S b)` is strictly convex (`s`), no witness `w Tf` and missed point `S fj` (`fj ∉ Tf`)
    can both lie inside the convex quadrilateral. -/
theorem n1_convex_quad_pair_clause {n : ℕ} {P : Set (ℝ × ℝ)}
    {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ}
    (hP : ShatteredSimplePolygon P S w)
    {a b fj : Fin n} (hab : a ≠ b) (hfja : fj ≠ a) (hfjb : fj ≠ b)
    {T₁ T₂ Tf : Finset (Fin n)} (hT12 : T₁ ≠ T₂) (hTf1 : Tf ≠ T₁) (hTf2 : Tf ≠ T₂)
    (ha1 : a ∈ T₁) (hb1 : b ∈ T₁) (ha2 : a ∈ T₂) (hb2 : b ∈ T₂)
    (hfj_miss : fj ∉ Tf) (s : Bool) :
    ¬ (strictConvexQuadSideBool s (w T₁) (S a) (w T₂) (S b) = true ∧
       inConvexQuadSideBool s (w Tf) (w T₁) (S a) (w T₂) (S b) = true ∧
       inConvexQuadSideBool s (S fj) (w T₁) (S a) (w T₂) (S b) = true) := by
  rintro ⟨hq_b, hf_b, hj_b⟩
  obtain ⟨hquad, hf_mem⟩ := strictConvexQuad_and_mem_of_sideBool
    (orient_w_S_w_ne hP hT12 a) (orient_S_w_S_ne hP hab T₂)
    (orient_w_S_w_ne hP hT12.symm b) (orient_S_w_S_ne hP hab.symm T₁)
    (orient_w_S_w_ne hP hTf1.symm a) (orient_S_w_w_ne hP a hTf2.symm)
    (orient_w_S_w_ne hP hTf2.symm b) (orient_S_w_w_ne hP b hTf1.symm) hq_b hf_b
  obtain ⟨_, hj_mem⟩ := strictConvexQuad_and_mem_of_sideBool
    (orient_w_S_w_ne hP hT12 a) (orient_S_w_S_ne hP hab T₂)
    (orient_w_S_w_ne hP hT12.symm b) (orient_S_w_S_ne hP hab.symm T₁)
    (orient_w_S_S_ne hP T₁ hfja.symm) (orient_S_w_S_ne hP hfja.symm T₂)
    (orient_w_S_S_ne hP T₂ hfjb.symm) (orient_S_w_S_ne hP hfjb.symm T₁) hq_b hj_b
  obtain ⟨hsub, _⟩ := convex_quad_vertex_enclosure_N1 hP ha1 hb1 ha2 hb2 hquad
  exact hfj_miss ((hP.shatters Tf fj).mp
    (((convex_convexHull ℝ _).segment_subset hf_mem hj_mem).trans hsub))

/-- **Reflex-Dart `N1` Position `r = 0` (`vr = w T₁, vp = S a, vq = w T₂, vs = S b`, `i1 == 1`)**:
    With omitted outer-triangle literal `sd`, if `w T₁ ∈ int tri(S a, w T₂, S b)` and `a ∉ Tf`,
    `w Tf` cannot lie in `int tri(S a, w T₂, S b)` on the `w T₂`-side of `w T₁ -> S a`. -/
theorem n1_dart_r0_clause {n : ℕ} {P : Set (ℝ × ℝ)}
    {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ}
    (hP : ShatteredSimplePolygon P S w)
    {a b : Fin n} (hab : a ≠ b)
    {T₁ T₂ Tf : Finset (Fin n)} (hT12 : T₁ ≠ T₂) (hTf1 : Tf ≠ T₁) (hTf2 : Tf ≠ T₂)
    (ha1 : a ∈ T₁) (hb1 : b ∈ T₁) (ha2 : a ∈ T₂) (hb2 : b ∈ T₂)
    (ha_miss : a ∉ Tf) (sd : Bool) :
    ¬ (inOpenTriSideBool sd (w T₁) (S a) (w T₂) (S b) = true ∧
       inOpenTriSideBool sd (w Tf) (S a) (w T₂) (S b) = true ∧
       sameSideBool (w T₁) (S a) (w Tf) (w T₂) = true) := by
  rintro ⟨hd_b, hf_b, hsp_b⟩
  have h_dart := (inOpenTri_and_orientSign_of_side
    (orient_S_w_w_ne hP a hT12.symm) (orient_w_S_w_ne hP hT12.symm b)
    (orient_S_S_w_ne hP hab.symm T₁) hd_b).1
  have hf_tri := (inOpenTri_and_orientSign_of_side
    (orient_S_w_w_ne hP a hTf2.symm) (orient_w_S_w_ne hP hTf2.symm b)
    (orient_S_S_w_ne hP hab.symm Tf) hf_b).1
  have hsame := (sameSideBool_iff_sameSide
    (orient_w_S_w_ne hP hTf1.symm a) (orient_w_S_w_ne hP hT12 a)).mp hsp_b
  obtain ⟨_, _, _, hvp, _⟩ := dart_star_kernel_enclosure hP
    ⟨Or.inr ⟨T₁, rfl⟩, Or.inl ⟨a, rfl⟩, Or.inr ⟨T₂, rfl⟩, Or.inl ⟨b, rfl⟩⟩
    ⟨hP.s_ne_w a T₂, (hP.s_ne_w b T₂).symm, hP.s_inj.ne hab⟩
    ((hP.shatters T₁ a).mpr ha1) (sees_symm ((hP.shatters T₂ a).mpr ha2))
    ((hP.shatters T₂ b).mpr hb2) (sees_symm ((hP.shatters T₁ b).mpr hb1)) h_dart
  exact ha_miss ((hP.shatters Tf a).mp
    (hvp (w Tf) (inOpenTri_mem_convexHull hf_tri) (le_of_lt hsame)))

/-- **Reflex-Dart `N1` Position `r = 1` (`vr = S a, vp = w T₂, vq = S b, vs = w T₁`, `i0 == 1`)**:
    With omitted outer-triangle literal `sd, st`, if `S a ∈ int tri(w T₂, S b, w T₁)` and `a ∉ Tf`,
    `w Tf` cannot lie in `int tri(S a, w T₂, S b)` nor in `int tri(S a, S b, w T₁)`. -/
theorem n1_dart_r1_clause {n : ℕ} {P : Set (ℝ × ℝ)}
    {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ}
    (hP : ShatteredSimplePolygon P S w)
    {a b : Fin n} (hab : a ≠ b)
    {T₁ T₂ Tf : Finset (Fin n)} (hT12 : T₁ ≠ T₂) (hTf1 : Tf ≠ T₁) (hTf2 : Tf ≠ T₂)
    (ha1 : a ∈ T₁) (hb1 : b ∈ T₁) (ha2 : a ∈ T₂) (hb2 : b ∈ T₂)
    (ha_miss : a ∉ Tf) (sd st : Bool) :
    ¬ (inOpenTriSideBool sd (S a) (w T₂) (S b) (w T₁) = true ∧
       (inOpenTriSideBool st (w Tf) (S a) (w T₂) (S b) = true ∨
        inOpenTriSideBool st (w Tf) (S a) (S b) (w T₁) = true)) := by
  rintro ⟨hd_b, hsub⟩
  have h_dart := (inOpenTri_and_orientSign_of_side
    (orient_w_S_S_ne hP T₂ hab.symm) (orient_S_w_S_ne hP hab.symm T₁)
    (orient_w_w_S_ne hP hT12 a) hd_b).1
  obtain ⟨_, _, hrq, _, _⟩ := dart_star_kernel_enclosure hP
    ⟨Or.inl ⟨a, rfl⟩, Or.inr ⟨T₂, rfl⟩, Or.inl ⟨b, rfl⟩, Or.inr ⟨T₁, rfl⟩⟩
    ⟨(hP.s_ne_w b T₂).symm, hP.s_ne_w b T₁, hP.w_inj.ne hT12.symm⟩
    (sees_symm ((hP.shatters T₂ a).mpr ha2)) ((hP.shatters T₂ b).mpr hb2)
    (sees_symm ((hP.shatters T₁ b).mpr hb1)) ((hP.shatters T₁ a).mpr ha1) h_dart
  have hmem : w Tf ∈ convexHull ℝ ({S a, w T₂, S b} : Set (ℝ × ℝ)) ∨
              w Tf ∈ convexHull ℝ ({S a, S b, w T₁} : Set (ℝ × ℝ)) := by
    rcases hsub with h1 | h2
    · exact Or.inl (inOpenTri_mem_convexHull (inOpenTri_and_orientSign_of_side
        (orient_S_w_w_ne hP a hTf2.symm) (orient_w_S_w_ne hP hTf2.symm b)
        (orient_S_S_w_ne hP hab.symm Tf) h1).1)
    · exact Or.inr (inOpenTri_mem_convexHull (inOpenTri_and_orientSign_of_side
        (orient_S_S_w_ne hP hab Tf) (orient_S_w_w_ne hP b hTf1.symm)
        (orient_w_S_w_ne hP hTf1.symm a) h2).1)
  exact ha_miss ((hP.shatters Tf a).mp (hrq (w Tf) hmem).1)

/-- **Reflex-Dart `N1` Position `r = 2` (`vr = w T₂, vp = S b, vq = w T₁, vs = S a`, `i3 == 1`)**:
    With omitted outer-triangle literal `sd`, if `w T₂ ∈ int tri(S b, w T₁, S a)` and `a ∉ Tf`,
    `w Tf` cannot lie in `int tri(S b, w T₁, S a)` on the `w T₁`-side of `w T₂ -> S a`. -/
theorem n1_dart_r2_clause {n : ℕ} {P : Set (ℝ × ℝ)}
    {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ}
    (hP : ShatteredSimplePolygon P S w)
    {a b : Fin n} (hab : a ≠ b)
    {T₁ T₂ Tf : Finset (Fin n)} (hT12 : T₁ ≠ T₂) (hTf1 : Tf ≠ T₁) (hTf2 : Tf ≠ T₂)
    (ha1 : a ∈ T₁) (hb1 : b ∈ T₁) (ha2 : a ∈ T₂) (hb2 : b ∈ T₂)
    (ha_miss : a ∉ Tf) (sd : Bool) :
    ¬ (inOpenTriSideBool sd (w T₂) (S b) (w T₁) (S a) = true ∧
       inOpenTriSideBool sd (w Tf) (S b) (w T₁) (S a) = true ∧
       sameSideBool (w T₂) (S a) (w Tf) (w T₁) = true) := by
  rintro ⟨hd_b, hf_b, hss_b⟩
  have h_dart := (inOpenTri_and_orientSign_of_side
    (orient_S_w_w_ne hP b hT12) (orient_w_S_w_ne hP hT12 a)
    (orient_S_S_w_ne hP hab T₂) hd_b).1
  have hf_tri := (inOpenTri_and_orientSign_of_side
    (orient_S_w_w_ne hP b hTf1.symm) (orient_w_S_w_ne hP hTf1.symm a)
    (orient_S_S_w_ne hP hab Tf) hf_b).1
  have hsame := (sameSideBool_iff_sameSide
    (orient_w_S_w_ne hP hTf2.symm a) (orient_w_S_w_ne hP hT12.symm a)).mp hss_b
  obtain ⟨_, _, _, _, hvs⟩ := dart_star_kernel_enclosure hP
    ⟨Or.inr ⟨T₂, rfl⟩, Or.inl ⟨b, rfl⟩, Or.inr ⟨T₁, rfl⟩, Or.inl ⟨a, rfl⟩⟩
    ⟨hP.s_ne_w b T₁, (hP.s_ne_w a T₁).symm, hP.s_inj.ne hab.symm⟩
    ((hP.shatters T₂ b).mpr hb2) (sees_symm ((hP.shatters T₁ b).mpr hb1))
    ((hP.shatters T₁ a).mpr ha1) (sees_symm ((hP.shatters T₂ a).mpr ha2)) h_dart
  exact ha_miss ((hP.shatters Tf a).mp
    (hvs (w Tf) (inOpenTri_mem_convexHull hf_tri) (le_of_lt hsame)))

/-- **Reflex-Dart `N1` Position `r = 3` (`vr = S b, vp = w T₁, vq = S a, vs = w T₂`, `i2 == 1`)**:
    With omitted outer-triangle literal `sd, st`, if `S b ∈ int tri(w T₁, S a, w T₂)` and `a ∉ Tf`,
    `w Tf` cannot lie in `int tri(S b, w T₁, S a)` nor in `int tri(S b, S a, w T₂)`. -/
theorem n1_dart_r3_clause {n : ℕ} {P : Set (ℝ × ℝ)}
    {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ}
    (hP : ShatteredSimplePolygon P S w)
    {a b : Fin n} (hab : a ≠ b)
    {T₁ T₂ Tf : Finset (Fin n)} (hT12 : T₁ ≠ T₂) (hTf1 : Tf ≠ T₁) (hTf2 : Tf ≠ T₂)
    (ha1 : a ∈ T₁) (hb1 : b ∈ T₁) (ha2 : a ∈ T₂) (hb2 : b ∈ T₂)
    (ha_miss : a ∉ Tf) (sd st : Bool) :
    ¬ (inOpenTriSideBool sd (S b) (w T₁) (S a) (w T₂) = true ∧
       (inOpenTriSideBool st (w Tf) (S b) (w T₁) (S a) = true ∨
        inOpenTriSideBool st (w Tf) (S b) (S a) (w T₂) = true)) := by
  rintro ⟨hd_b, hsub⟩
  have h_dart := (inOpenTri_and_orientSign_of_side
    (orient_w_S_S_ne hP T₁ hab) (orient_S_w_S_ne hP hab T₂)
    (orient_w_w_S_ne hP hT12.symm b) hd_b).1
  obtain ⟨_, _, hrq, _, _⟩ := dart_star_kernel_enclosure hP
    ⟨Or.inl ⟨b, rfl⟩, Or.inr ⟨T₁, rfl⟩, Or.inl ⟨a, rfl⟩, Or.inr ⟨T₂, rfl⟩⟩
    ⟨(hP.s_ne_w a T₁).symm, hP.s_ne_w a T₂, hP.w_inj.ne hT12⟩
    (sees_symm ((hP.shatters T₁ b).mpr hb1)) ((hP.shatters T₁ a).mpr ha1)
    (sees_symm ((hP.shatters T₂ a).mpr ha2)) ((hP.shatters T₂ b).mpr hb2) h_dart
  have hmem : w Tf ∈ convexHull ℝ ({S b, w T₁, S a} : Set (ℝ × ℝ)) ∨
              w Tf ∈ convexHull ℝ ({S b, S a, w T₂} : Set (ℝ × ℝ)) := by
    rcases hsub with h1 | h2
    · exact Or.inl (inOpenTri_mem_convexHull (inOpenTri_and_orientSign_of_side
        (orient_S_w_w_ne hP b hTf1.symm) (orient_w_S_w_ne hP hTf1.symm a)
        (orient_S_S_w_ne hP hab Tf) h1).1)
    · exact Or.inr (inOpenTri_mem_convexHull (inOpenTri_and_orientSign_of_side
        (orient_S_S_w_ne hP hab.symm Tf) (orient_S_w_w_ne hP a hTf2.symm)
        (orient_w_S_w_ne hP hTf2.symm b) h2).1)
  exact ha_miss ((hP.shatters Tf a).mp (hrq (w Tf) hmem).2)

/-- General pair-visibility helper inside either star-kernel lobe of a reflex dart `(vr, vp, vq, vs)`. -/
lemma dart_star_kernel_pair_sees {P : Set (ℝ × ℝ)} (hEnc : EnclosureDomain P)
    {vr vp vq vs z₁ z₂ : ℝ × ℝ}
    (hrp : Sees P vr vp) (hpq : Sees P vp vq) (hqs : Sees P vq vs) (hsr : Sees P vs vr)
    (h_dart : InOpenTri vp vq vs vr) (h_nondeg : orient2D vp vq vs ≠ 0)
    (hz1 : z₁ ∈ convexHull ℝ ({vp, vq, vs} : Set (ℝ × ℝ)))
    (hz2 : z₂ ∈ convexHull ℝ ({vp, vq, vs} : Set (ℝ × ℝ)))
    (hlobe : (0 ≤ orient2D vr vp z₁ * orient2D vr vp vq ∧
              0 ≤ orient2D vr vp z₂ * orient2D vr vp vq) ∨
             (0 ≤ orient2D vr vs z₁ * orient2D vr vs vq ∧
              0 ≤ orient2D vr vs z₂ * orient2D vr vs vq)) :
    Sees P z₁ z₂ := by
  obtain ⟨_, htri1, htri2, _, hvp, hvs⟩ :=
    dart_star_kernel_of_4cycle hEnc hrp hpq hqs hsr h_dart h_nondeg
  intro u hu
  have hu_hull : u ∈ convexHull ℝ ({vp, vq, vs} : Set (ℝ × ℝ)) :=
    (convex_convexHull ℝ _).segment_subset hz1 hz2 hu
  rw [segment_eq_image] at hu
  rcases hu with ⟨t, ⟨ht0, ht1⟩, rfl⟩
  have ht1' : 0 ≤ 1 - t := sub_nonneg.mpr ht1
  rcases hlobe with ⟨hp1, hp2⟩ | ⟨hs1, hs2⟩
  · have hu_side : 0 ≤ orient2D vr vp ((1 - t) • z₁ + t • z₂) * orient2D vr vp vq := by
      rw [orient2D_affine_comb vr vp z₁ z₂ _ t (by simp [smul_eq_mul]) (by simp [smul_eq_mul])]
      have hid : ((1 - t) * orient2D vr vp z₁ + t * orient2D vr vp z₂) * orient2D vr vp vq =
          (1 - t) * (orient2D vr vp z₁ * orient2D vr vp vq) +
          t * (orient2D vr vp z₂ * orient2D vr vp vq) := by ring
      rw [hid]
      exact add_nonneg (mul_nonneg ht1' hp1) (mul_nonneg ht0 hp2)
    rcases (hvp _ hu_hull hu_side).1 with h1 | h2
    · exact htri1 h1
    · exact htri2 h2
  · have hu_side : 0 ≤ orient2D vr vs ((1 - t) • z₁ + t • z₂) * orient2D vr vs vq := by
      rw [orient2D_affine_comb vr vs z₁ z₂ _ t (by simp [smul_eq_mul]) (by simp [smul_eq_mul])]
      have hid : ((1 - t) * orient2D vr vs z₁ + t * orient2D vr vs z₂) * orient2D vr vs vq =
          (1 - t) * (orient2D vr vs z₁ * orient2D vr vs vq) +
          t * (orient2D vr vs z₂ * orient2D vr vs vq) := by ring
      rw [hid]
      exact add_nonneg (mul_nonneg ht1' hs1) (mul_nonneg ht0 hs2)
    rcases (hvs _ hu_hull hu_side).1 with h1 | h2
    · exact htri1 h1
    · exact htri2 h2

/-- **Reflex-Dart 4-Cycle Pair Clause (`four_cycle_dart_pair_clause`, `gen_chiro_*.cpp` lines 165–166)**:
    For ANY cyclic rotation `(vr, vp, vq, vs)` of a visibility 4-cycle in `X = S ∪ W₀`,
    if `vr ∈ int tri(vp, vq, vs)`, no witness `w Tf` and missed point `S fj` (`fj ∉ Tf`) can both
    lie in `int tri(vp, vq, vs)` on the `vq`-side of `vr -> vp` (or both on the `vq`-side of `vr -> vs`). -/
theorem four_cycle_dart_pair_clause {n k : ℕ} {P : Set (ℝ × ℝ)}
    {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ}
    (hP : ShatteredSimplePolygon P S w) (W₀ : Fin k ↪ Finset (Fin n))
    {ir ip iq is_ : Fin (n + k)}
    (hrp_ne : ir ≠ ip) (hpq_ne : ip ≠ iq) (hqs_ne : iq ≠ is_) (hsr_ne : is_ ≠ ir)
    (hrq_ne : ir ≠ iq) (hps_ne : ip ≠ is_)
    (hrp : Sees P (pointSeq S w W₀ ir) (pointSeq S w W₀ ip))
    (hpq : Sees P (pointSeq S w W₀ ip) (pointSeq S w W₀ iq))
    (hqs : Sees P (pointSeq S w W₀ iq) (pointSeq S w W₀ is_))
    (hsr : Sees P (pointSeq S w W₀ is_) (pointSeq S w W₀ ir))
    {fj : Fin n} {jf : Fin k} (hfj_miss : fj ∉ W₀ jf)
    (hfw_ne : ∀ u ∈ ({ir, ip, iq, is_} : Finset (Fin (n + k))), Fin.natAdd n jf ≠ u)
    (hfj_ne : ∀ u ∈ ({ir, ip, iq, is_} : Finset (Fin (n + k))), Fin.castAdd k fj ≠ u) :
    let X := pointSeq S w W₀
    let u_fw := Fin.natAdd n jf
    let u_fj := Fin.castAdd k fj
    ¬ (inOpenTriBool (X ir) (X ip) (X iq) (X is_) = true ∧
       inOpenTriBool (X u_fw) (X ip) (X iq) (X is_) = true ∧
       inOpenTriBool (X u_fj) (X ip) (X iq) (X is_) = true ∧
       ((sameSideBool (X ir) (X ip) (X u_fw) (X iq) = true ∧
         sameSideBool (X ir) (X ip) (X u_fj) (X iq) = true) ∨
        (sameSideBool (X ir) (X is_) (X u_fw) (X iq) = true ∧
         sameSideBool (X ir) (X is_) (X u_fj) (X iq) = true))) := by
  intro X u_fw u_fj
  have hX : NoThreeCollinear X := noThreeCollinear_pointSeq hP W₀
  rintro ⟨hdart_b, hfw_b, hfj_b, hlobe_b⟩
  have h_dart : InOpenTri (X ip) (X iq) (X is_) (X ir) :=
    (inOpenTriBool_iff_inOpenTri
      (hX.2 ip iq ir hpq_ne hrq_ne.symm hrp_ne.symm)
      (hX.2 iq is_ ir hqs_ne hsr_ne hrq_ne.symm)
      (hX.2 is_ ip ir hps_ne.symm hrp_ne.symm hsr_ne)).mp hdart_b
  have hfw_tri : InOpenTri (X ip) (X iq) (X is_) (X u_fw) :=
    (inOpenTriBool_iff_inOpenTri
      (hX.2 ip iq u_fw hpq_ne (hfw_ne iq (by simp)).symm (hfw_ne ip (by simp)).symm)
      (hX.2 iq is_ u_fw hqs_ne (hfw_ne is_ (by simp)).symm (hfw_ne iq (by simp)).symm)
      (hX.2 is_ ip u_fw hps_ne.symm (hfw_ne ip (by simp)).symm (hfw_ne is_ (by simp)).symm)).mp hfw_b
  have hfj_tri : InOpenTri (X ip) (X iq) (X is_) (X u_fj) :=
    (inOpenTriBool_iff_inOpenTri
      (hX.2 ip iq u_fj hpq_ne (hfj_ne iq (by simp)).symm (hfj_ne ip (by simp)).symm)
      (hX.2 iq is_ u_fj hqs_ne (hfj_ne is_ (by simp)).symm (hfj_ne iq (by simp)).symm)
      (hX.2 is_ ip u_fj hps_ne.symm (hfj_ne ip (by simp)).symm (hfj_ne is_ (by simp)).symm)).mp hfj_b
  have hlobe :
      (0 ≤ orient2D (X ir) (X ip) (X u_fw) * orient2D (X ir) (X ip) (X iq) ∧
       0 ≤ orient2D (X ir) (X ip) (X u_fj) * orient2D (X ir) (X ip) (X iq)) ∨
      (0 ≤ orient2D (X ir) (X is_) (X u_fw) * orient2D (X ir) (X is_) (X iq) ∧
       0 ≤ orient2D (X ir) (X is_) (X u_fj) * orient2D (X ir) (X is_) (X iq)) := by
    rcases hlobe_b with ⟨sp1, sp2⟩ | ⟨ss1, ss2⟩
    · left
      exact ⟨le_of_lt ((sameSideBool_iff_sameSide
                (hX.2 ir ip u_fw hrp_ne (hfw_ne ip (by simp)).symm (hfw_ne ir (by simp)).symm)
                (hX.2 ir ip iq hrp_ne hpq_ne hrq_ne)).mp sp1),
             le_of_lt ((sameSideBool_iff_sameSide
                (hX.2 ir ip u_fj hrp_ne (hfj_ne ip (by simp)).symm (hfj_ne ir (by simp)).symm)
                (hX.2 ir ip iq hrp_ne hpq_ne hrq_ne)).mp sp2)⟩
    · right
      exact ⟨le_of_lt ((sameSideBool_iff_sameSide
                (hX.2 ir is_ u_fw hsr_ne.symm (hfw_ne is_ (by simp)).symm (hfw_ne ir (by simp)).symm)
                (hX.2 ir is_ iq hsr_ne.symm hqs_ne.symm hrq_ne)).mp ss1),
             le_of_lt ((sameSideBool_iff_sameSide
                (hX.2 ir is_ u_fj hsr_ne.symm (hfj_ne is_ (by simp)).symm (hfj_ne ir (by simp)).symm)
                (hX.2 ir is_ iq hsr_ne.symm hqs_ne.symm hrq_ne)).mp ss2)⟩
  have hsees := dart_star_kernel_pair_sees hP.toEnclosureDomain hrp hpq hqs hsr h_dart
    (hX.2 ip iq is_ hpq_ne hqs_ne hps_ne)
    (inOpenTri_mem_convexHull hfw_tri) (inOpenTri_mem_convexHull hfj_tri) hlobe
  simp only [X, u_fw, u_fj, pointSeq, Fin.addCases_left, Fin.addCases_right] at hsees
  exact hfj_miss ((hP.shatters (W₀ jf) fj).mp hsees)


/-! ## 6. Unified Theorem 8.1 Soundness Bundle (`sound_chirotope_reduction`) -/

/-- Bundled chirotope soundness certificate for `X = pointSeq S w W₀` over any
    `ShatteredSimplePolygon P S w` (`upper_8.tex` Theorem 8.1). -/
structure SoundChirotopeBundle {n k : ℕ} (P : Set (ℝ × ℝ))
    (S : Fin n → ℝ × ℝ) (w : Finset (Fin n) → ℝ × ℝ)
    (W₀ : Fin k ↪ Finset (Fin n)) : Prop where
  /-- `(G1)` General position on `X = S ∪ W₀`. -/
  gp : NoThreeCollinear (pointSeq S w W₀)
  /-- `(C1)` Rank-3 Grassmann–Plücker 16-clause sign exclusions on every 5-tuple of `X`. -/
  c1_gp5 : ∀ {ip ia ib ic id_ : Fin (n + k)},
    ip ≠ ia → ip ≠ ib → ip ≠ ic → ip ≠ id_ →
    ia ≠ ib → ia ≠ ic → ia ≠ id_ → ib ≠ ic → ib ≠ id_ → ic ≠ id_ →
    ∀ s₁ s₂ s₃ : Bool,
      ¬ (orientSign (pointSeq S w W₀ ip) (pointSeq S w W₀ ia) (pointSeq S w W₀ ib) = s₁ ∧
         orientSign (pointSeq S w W₀ ip) (pointSeq S w W₀ ic) (pointSeq S w W₀ id_) = s₁ ∧
         orientSign (pointSeq S w W₀ ip) (pointSeq S w W₀ ia) (pointSeq S w W₀ ic) = s₂ ∧
         orientSign (pointSeq S w W₀ ip) (pointSeq S w W₀ ib) (pointSeq S w W₀ id_) = !s₂ ∧
         orientSign (pointSeq S w W₀ ip) (pointSeq S w W₀ ia) (pointSeq S w W₀ id_) = s₃ ∧
         orientSign (pointSeq S w W₀ ip) (pointSeq S w W₀ ib) (pointSeq S w W₀ ic) = s₃) ∧
      ¬ (orientSign (pointSeq S w W₀ ip) (pointSeq S w W₀ ia) (pointSeq S w W₀ ib) = s₁ ∧
         orientSign (pointSeq S w W₀ ip) (pointSeq S w W₀ ic) (pointSeq S w W₀ id_) = !s₁ ∧
         orientSign (pointSeq S w W₀ ip) (pointSeq S w W₀ ia) (pointSeq S w W₀ ic) = s₂ ∧
         orientSign (pointSeq S w W₀ ip) (pointSeq S w W₀ ib) (pointSeq S w W₀ id_) = s₂ ∧
         orientSign (pointSeq S w W₀ ip) (pointSeq S w W₀ ia) (pointSeq S w W₀ id_) = s₃ ∧
         orientSign (pointSeq S w W₀ ip) (pointSeq S w W₀ ib) (pointSeq S w W₀ ic) = !s₃)
  /-- `(C2)` Hull CCW orientation & interior-in-`conv(B)` orientation signs. -/
  c2_hull_interior : ∀ cb : CyclicSubsetBoundary S (hullVertices S),
    (∀ i j k' : Fin (cb.m + 3), i < j → j < k' →
      orientSign (S (cb.p_idx i)) (S (cb.p_idx j)) (S (cb.p_idx k')) = true) ∧
    (∀ a ∈ interiorPoints S, ∀ r : Fin (cb.m + 3),
      orientSign (S (cb.p_idx r)) (S (cb.p_idx (r + 1))) (S a) = true)
  /-- `(C8)` Asymmetric two-sided visibility separation clauses. -/
  c8_two_sided : ∀ {d u v : Fin n} {Tx T₁ T₂ : Finset (Fin n)},
    d ∉ Tx → u ∈ Tx → v ∈ Tx → d ∈ T₁ → u ∈ T₁ → d ∈ T₂ → v ∈ T₂ →
    ∀ s : Bool,
      ¬ (orientSign (S d) (w Tx) (S u) = s ∧ orientSign (S d) (w Tx) (S v) = !s ∧
         orientSign (S d) (w Tx) (w T₁) = s ∧ orientSign (S d) (w Tx) (w T₂) = !s)
  /-- `(C10)` `T1`, `T2`, and `N1` (convex-quad + all 4 reflex-dart positions) soundness. -/
  c10_T1_vertex : ∀ {a b : Fin n} {T₁ T₂ Tf : Finset (Fin n)},
    a ≠ b → T₁ ≠ T₂ → Tf ≠ T₁ → Tf ≠ T₂ → a ∈ T₁ → b ∈ T₁ → b ∈ T₂ → b ∉ Tf →
    ¬ (segsCrossBool (w T₁) (S a) (w T₂) (S b) = true ∧
       sameSideBool (w T₁) (S a) (w Tf) (S b) = true ∧
       sameSideBool (w T₂) (S b) (w Tf) (w T₁) = true ∧
       sameSideBool (w T₁) (S b) (w Tf) (S a) = true)
  c10_T2_pair : ∀ {a b c fj : Fin n} {T₁ T₂ Tf : Finset (Fin n)},
    a ≠ b → a ≠ c → b ≠ c → fj ≠ a → fj ≠ b → fj ≠ c →
    T₁ ≠ T₂ → Tf ≠ T₁ → Tf ≠ T₂ →
    a ∈ T₁ → b ∈ T₂ → c ∈ T₂ → fj ∉ Tf →
    ¬ (segsCrossBool (w T₁) (S a) (w T₂) (S b) = true ∧
       segsCrossBool (w T₁) (S a) (w T₂) (S c) = true ∧
       sameSideBool (w T₁) (S a) (w Tf) (w T₂) = true ∧
       sameSideBool (w T₂) (S b) (w Tf) (S c) = true ∧
       sameSideBool (w T₂) (S c) (w Tf) (S b) = true ∧
       sameSideBool (w T₁) (S a) (S fj) (w T₂) = true ∧
       sameSideBool (w T₂) (S b) (S fj) (S c) = true ∧
       sameSideBool (w T₂) (S c) (S fj) (S b) = true)
  c10_N1_quad : ∀ {a b : Fin n} {T₁ T₂ Tf : Finset (Fin n)},
    a ≠ b → T₁ ≠ T₂ → Tf ≠ T₁ → Tf ≠ T₂ → a ∈ T₁ → b ∈ T₁ → a ∈ T₂ → b ∈ T₂ → (a ∉ Tf ∨ b ∉ Tf) →
    ∀ s : Bool,
      ¬ (strictConvexQuadSideBool s (w T₁) (S a) (w T₂) (S b) = true ∧
         inConvexQuadSideBool s (w Tf) (w T₁) (S a) (w T₂) (S b) = true)
  c10_N1_dart_r0 : ∀ {a b : Fin n} {T₁ T₂ Tf : Finset (Fin n)},
    a ≠ b → T₁ ≠ T₂ → Tf ≠ T₁ → Tf ≠ T₂ → a ∈ T₁ → b ∈ T₁ → a ∈ T₂ → b ∈ T₂ → a ∉ Tf →
    ∀ sd : Bool,
      ¬ (inOpenTriSideBool sd (w T₁) (S a) (w T₂) (S b) = true ∧
         inOpenTriSideBool sd (w Tf) (S a) (w T₂) (S b) = true ∧
         sameSideBool (w T₁) (S a) (w Tf) (w T₂) = true)
  c10_N1_dart_r1 : ∀ {a b : Fin n} {T₁ T₂ Tf : Finset (Fin n)},
    a ≠ b → T₁ ≠ T₂ → Tf ≠ T₁ → Tf ≠ T₂ → a ∈ T₁ → b ∈ T₁ → a ∈ T₂ → b ∈ T₂ → a ∉ Tf →
    ∀ sd st : Bool,
      ¬ (inOpenTriSideBool sd (S a) (w T₂) (S b) (w T₁) = true ∧
         (inOpenTriSideBool st (w Tf) (S a) (w T₂) (S b) = true ∨
          inOpenTriSideBool st (w Tf) (S a) (S b) (w T₁) = true))
  c10_N1_dart_r2 : ∀ {a b : Fin n} {T₁ T₂ Tf : Finset (Fin n)},
    a ≠ b → T₁ ≠ T₂ → Tf ≠ T₁ → Tf ≠ T₂ → a ∈ T₁ → b ∈ T₁ → a ∈ T₂ → b ∈ T₂ → a ∉ Tf →
    ∀ sd : Bool,
      ¬ (inOpenTriSideBool sd (w T₂) (S b) (w T₁) (S a) = true ∧
         inOpenTriSideBool sd (w Tf) (S b) (w T₁) (S a) = true ∧
         sameSideBool (w T₂) (S a) (w Tf) (w T₁) = true)
  c10_N1_dart_r3 : ∀ {a b : Fin n} {T₁ T₂ Tf : Finset (Fin n)},
    a ≠ b → T₁ ≠ T₂ → Tf ≠ T₁ → Tf ≠ T₂ → a ∈ T₁ → b ∈ T₁ → a ∈ T₂ → b ∈ T₂ → a ∉ Tf →
    ∀ sd st : Bool,
      ¬ (inOpenTriSideBool sd (S b) (w T₁) (S a) (w T₂) = true ∧
         (inOpenTriSideBool st (w Tf) (S b) (w T₁) (S a) = true ∨
          inOpenTriSideBool st (w Tf) (S b) (S a) (w T₂) = true))
  /-- `(C11)` `vis_SS` Round-2 triangle enclosure & multi-round `(E1)`/`(E2)` closure soundness. -/
  c11_vis_SS_tri : ∀ {a b : Fin n} {T₁ T₂ T₃ Tf : Finset (Fin n)},
    a ≠ b → a ∈ T₁ → b ∈ T₁ → a ∈ T₂ → b ∈ T₂ → a ∈ T₃ → b ∈ T₃ → (a ∉ Tf ∨ b ∉ Tf) →
    ∀ sd : Bool,
      ¬ (oppSideBool (S a) (S b) (w T₁) (w T₂) = true ∧
         inOpenTriSideBool sd (w Tf) (w T₃) (S a) (S b) = true)
  c11_iterated_closure : ∀ {G₀ : Fin (n + k) → Fin (n + k) → Prop},
    (∀ u v, G₀ u v → Sees P (pointSeq S w W₀ u) (pointSeq S w W₀ v)) →
    ∀ (r : ℕ) (i : Fin n) (j : Fin k), i ∉ W₀ j →
      ¬ IteratedVisAtRound (pointSeq S w W₀) G₀ r (Fin.castAdd k i) (Fin.natAdd n j)

/-- **Theorem 8.1 (`sound_chirotope_reduction`)**:
    Every `ShatteredSimplePolygon P S w` and finite witness subcollection `W₀` satisfies
    `SoundChirotopeBundle P S w W₀`. -/
theorem sound_chirotope_reduction {n k : ℕ} {P : Set (ℝ × ℝ)}
    {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ}
    (hP : ShatteredSimplePolygon P S w) (W₀ : Fin k ↪ Finset (Fin n)) :
    SoundChirotopeBundle P S w W₀ where
  gp := noThreeCollinear_pointSeq hP W₀
  c1_gp5 := (noThreeCollinear_pointSeq hP W₀).gp5_clauses
  c2_hull_interior := shattered_hull_and_interior_orientSign_C2 hP
  c8_two_sided hd hu hv hd1 hu1 hd2 hv2 s :=
    asymmetric_two_sided_clause_C8 hP hd hu hv hd1 hu1 hd2 hv2 s
  c10_T1_vertex hab hT12 hTf1 hTf2 ha1 hb1 hb2 hbm :=
    crossed_tri_T1_vertex_clause hP hab hT12 hTf1 hTf2 ha1 hb1 hb2 hbm
  c10_T2_pair hab hac hbc hfja hfjb hfjc hT12 hTf1 hTf2 ha1 hb2 hc2 hjm :=
    crossed_tri_T2_pair_clause hP hab hac hbc hfja hfjb hfjc hT12 hTf1 hTf2 ha1 hb2 hc2 hjm
  c10_N1_quad hab hT12 hTf1 hTf2 ha1 hb1 ha2 hb2 hmiss s :=
    n1_convex_quad_vertex_clause hP hab hT12 hTf1 hTf2 ha1 hb1 ha2 hb2 hmiss s
  c10_N1_dart_r0 hab hT12 hTf1 hTf2 ha1 hb1 ha2 hb2 ham sd :=
    n1_dart_r0_clause hP hab hT12 hTf1 hTf2 ha1 hb1 ha2 hb2 ham sd
  c10_N1_dart_r1 hab hT12 hTf1 hTf2 ha1 hb1 ha2 hb2 ham sd st :=
    n1_dart_r1_clause hP hab hT12 hTf1 hTf2 ha1 hb1 ha2 hb2 ham sd st
  c10_N1_dart_r2 hab hT12 hTf1 hTf2 ha1 hb1 ha2 hb2 ham sd :=
    n1_dart_r2_clause hP hab hT12 hTf1 hTf2 ha1 hb1 ha2 hb2 ham sd
  c10_N1_dart_r3 hab hT12 hTf1 hTf2 ha1 hb1 ha2 hb2 ham sd st :=
    n1_dart_r3_clause hP hab hT12 hTf1 hTf2 ha1 hb1 ha2 hb2 ham sd st
  c11_vis_SS_tri hab ha1 hb1 ha2 hb2 ha3 hb3 hmiss sd :=
    vis_SS_tri_vertex_omitted_outer_clause hP hab ha1 hb1 ha2 hb2 ha3 hb3 hmiss sd
  c11_iterated_closure hG₀ := (iterated_enclosure_soundness_C11 hP W₀ hG₀).2

end ChirotopeSoundness

end
