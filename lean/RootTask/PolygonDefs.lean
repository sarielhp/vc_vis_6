import Mathlib
import RootTask.Defs
import RootTask.UnconditionalBridge
import RootTask.Sec7Combination

open scoped Classical BigOperators
open Finset

noncomputable section

/-!
# Shared Polygon Visibility & Prior-Literature Interface (`upper_9.tex` Sections 1–2)

Defines segment visibility `Sees P x y := segment ℝ x y ⊆ P`, polygonal paths,
half-plane and wedge tests (`Definition 2.4`), and the exact prior-literature axioms
stated in Section 1 ("What is used", `upper_9.tex` lines 74–76):
1. Simple-polygon Enclosure (`Lemma 2.1(i)–(ii)`),
2. General-position reduction `(G1)–(G2)` (`Gilbers & Klein 2014, Section 3`),
3. No 10 shattered points in convex position (`Gilbers & Klein 2014, Lemma 2`),
4. Six wedges realize `< 64` patterns (`Isler et al. 2004, Theorem 3`).
-/

/-- Two points `x, y` see each other in `P ⊆ ℝ²` iff the closed segment `[x, y]` lies in `P`. -/
def Sees (P : Set (ℝ × ℝ)) (x y : ℝ × ℝ) : Prop :=
  segment ℝ x y ⊆ P

lemma sees_refl {P : Set (ℝ × ℝ)} {x : ℝ × ℝ} (hx : x ∈ P) : Sees P x x := by
  unfold Sees
  rw [segment_same]
  exact Set.singleton_subset_iff.mpr hx

lemma sees_symm {P : Set (ℝ × ℝ)} {x y : ℝ × ℝ} (h : Sees P x y) : Sees P y x := by
  unfold Sees at *
  rwa [segment_symm]

/-- A polygonal path `[v_0, v_1, ..., v_m]` in `P` from `s` to `t`: non-empty vertex list with
    `head = s`, `last = t`, and every consecutive segment `[v_k, v_{k+1}] ⊆ P`. -/
def IsPolygonalPathIn (P : Set (ℝ × ℝ)) (s t : ℝ × ℝ) (verts : List (ℝ × ℝ)) : Prop :=
  ∃ hne : verts ≠ [],
    verts.head hne = s ∧
    verts.getLast hne = t ∧
    (∀ x ∈ verts, x ∈ P) ∧
    verts.IsChain (fun u v => Sees P u v)

/-- Apart from the endpoints `s` and `t` at the ends of `verts`, all interior points of all edges of
    `verts` lie strictly in the open left half-plane `H^+(s, t) = {z : orient2D s t z > 0}`.
    Equivalently, every interior vertex `v_k` (`0 < k < verts.length - 1`) satisfies
    `0 < orient2D s t v_k` (and `verts.length ≥ 3` so the path has at least one interior vertex). -/
def InteriorOnLeft (s t : ℝ × ℝ) (verts : List (ℝ × ℝ)) : Prop :=
  3 ≤ verts.length ∧
  ∀ (k : ℕ) (hk : k < verts.length), 0 < k → k + 1 < verts.length →
    0 < orient2D s t (verts[k]'hk)

/-- Symmetrically, all interior vertices of `verts` lie strictly in `H^-(s, t) = {z : orient2D s t z < 0}`. -/
def InteriorOnRight (s t : ℝ × ℝ) (verts : List (ℝ × ℝ)) : Prop :=
  3 ≤ verts.length ∧
  ∀ (k : ℕ) (hk : k < verts.length), 0 < k → k + 1 < verts.length →
    orient2D s t (verts[k]'hk) < 0

/-- Witness sub-family `W(F; N) = {w_T : F ⊆ T ⊆ S \ N}` (`upper_9.tex` equation (1), line 89). -/
def WitnessSet {n : ℕ} (F N : Finset (Fin n)) (w : Finset (Fin n) → ℝ × ℝ) : Set (ℝ × ℝ) :=
  {x : ℝ × ℝ | ∃ T : Finset (Fin n), F ⊆ T ∧ Disjoint T N ∧ x = w T}

/-- Open half-plane test (`Definition 2.4`): `H` decides `Sees P x a` strictly on `W'`. -/
def IsHalfPlaneTest (P : Set (ℝ × ℝ)) (W' : Set (ℝ × ℝ)) (a : ℝ × ℝ) (H : OpenHalfPlane) : Prop :=
  ∀ x ∈ W', (H.MemPos x ∨ H.MemNeg x) ∧ (Sees P x a ↔ H.MemPos x)

/-- Open wedge test (`Definition 2.4`): `R` decides `Sees P x a` strictly on `W'`. -/
def IsWedgeTest (P : Set (ℝ × ℝ)) (W' : Set (ℝ × ℝ)) (a : ℝ × ℝ) (R : OpenWedge) : Prop :=
  ∀ x ∈ W', (R.MemOpen x ∨ R.MemExt x) ∧ (Sees P x a ↔ R.MemOpen x)

/-- Open cone `U(a; b, c) = a + cone(a - b, a - c) = H^-(c, a) ∩ H^-(a, b)` opposite to `b, c`
    at apex `a` when `orient2D a b c > 0` (`upper_9.tex` lines 215–220). -/
def oppositeConeWedge (a b c : ℝ × ℝ) (h_ccw : 0 < orient2D a b c) : OpenWedge where
  y := a
  u₁ := (a.2 - c.2, -(a.1 - c.1))
  u₂ := (b.2 - a.2, -(b.1 - a.1))
  h_nondeg := by
    unfold orient2D at h_ccw
    linarith [show (a.2 - c.2) * (-(b.1 - a.1)) - (-(a.1 - c.1)) * (b.2 - a.2) =
      (b.1 - a.1) * (c.2 - a.2) - (b.2 - a.2) * (c.1 - a.1) by ring]

/-- Prior-literature axioms & simple-polygon setting from Section 1 ("What is used") and Section 2.1–2.2
    of `upper_9.tex` for an `n`-point shattered set `S : Fin n → ℝ × ℝ` with witnesses `w : Finset (Fin n) → ℝ × ℝ`:
    - `Sees P (w T) (S i) ↔ i ∈ T` (shattering),
    - `(G1)` General position: all points of `range S` and `range w` are distinct (except possibly `w {i} = S i` avoided by perturbation) and no three distinct points in `range S ∪ range w` are collinear,
    - `(G2)` Open witness neighborhoods: if `T.Nonempty`, `w T` has an open ball in `P` seeing all `S i` (`i ∈ T`),
    - `Enclosure` (`Lemma 2.1(i)–(ii)`),
    - `Gilbers & Klein 2014, Lemma 2` (`no 10 points in convex position are shattered`),
    - `Isler et al. 2004, Theorem 3` (`six wedges cannot realize all 64 strict bitmasks`). -/
structure ShatteredSimplePolygon {n : ℕ} (P : Set (ℝ × ℝ))
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
  gk14_no_ten_convex : ∀ B : Finset (Fin n),
    (∀ i ∈ B, S i ∉ convexHull ℝ ((B.erase i).image S : Set (ℝ × ℝ))) → B.card ≤ 9
  isler_six_wedges : ∀ R : Fin 6 → OpenWedge,
    ¬ (∀ m : Fin 6 → Bool, ∃ p : ℝ × ℝ, ∀ i : Fin 6, if m i then (R i).MemOpen p else (R i).MemExt p)

end
