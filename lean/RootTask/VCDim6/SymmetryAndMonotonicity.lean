import Mathlib
import RootTask.PolygonDefs
import RootTask.PolygonEnclosureCore
import RootTask.NewEnclosureLemmas
import RootTask.ChirotopeSoundness
import RootTask.CertifiedAndHalfPlaneSoundness
import RootTask.SourceGapAndCaseSplits

open scoped Classical BigOperators
open Finset
open PolygonCore NewEnclosure ChirotopeSoundness CertifiedAndHalfPlaneSoundness SourceGapAndCaseSplits

noncomputable section

namespace VCDim6

/-!
# Dihedral Symmetries, Unmarked Hull-Slice Inheritance (`VC-dim ≤ 11`), and Pocket Exit-Edge Monotonicity

Formalizes the three structural pillars from `vc_dim_6_simplified.tex` Sections 3.1–3.4:
1. **Index Relabeling & Planar Reflection Invariance (`shattered_relabel`, `shattered_reflX`)**:
   Preserves `ShatteredSimplePolygon`, `hullVertices`, `interiorPoints`, and `certifiedSet`,
   allowing every configuration on `Fin 7` to be mapped into a canonical dihedral orbit.
2. **Unmarked Hull-Slice Inheritance (`unmarked_hull_slice_inheritance`, Corollary 3.3)**:
   Every subset `D' ⊆ D = B \ H` (`3 ≤ |D'|`) with slice `A₀` disjoint from `D'` induces a
   shattered set in strictly convex position with `certifiedSet = ∅`. Combined with `|M| ≤ 5`,
   eliminating Stage 1 Case `(7, 0)` immediately implies `VC-dim(P) ≤ 11` with zero SAT/RUP certificates.
3. **Pocket Exit-Edge Exclusion & Monotonicity (`exit_edge_ne_pocket_lr`, `pocket_exit_edge_monotonicity`,
   Lemma 3.4(i)–(ii))**:
   When `3 ≤ |D|` and `H ≠ ∅`, no point of `A ∪ H` has exit edge `(l, r)`, and along the CCW
   pocket arc `(l, h₁, ..., h_k, r)` on `∂ conv(B)`, the exit-edge indices in `{0, ..., ν - 2}`
   from `r` to `l` satisfy `ν - 2 ≥ m(h₁) ≥ ... ≥ m(h_k) ≥ 0`, geometrically eliminating all 11
   non-monotone Stage-2 orbits without SAT/RUP certificates.
-/

/-! ## 1. Index Relabeling (`Equiv.Perm (Fin n)`) and Planar Reflection (`reflX`) -/

/-- Relabeling of `S` by a permutation `σ : Equiv.Perm (Fin n)`. -/
def relabelS {n : ℕ} (σ : Equiv.Perm (Fin n)) (S : Fin n → ℝ × ℝ) : Fin n → ℝ × ℝ :=
  S ∘ σ

/-- Induced relabeling of the witness map `w` by `σ : Equiv.Perm (Fin n)`. -/
def relabelW {n : ℕ} (σ : Equiv.Perm (Fin n)) (w : Finset (Fin n) → ℝ × ℝ)
    (T' : Finset (Fin n)) : ℝ × ℝ :=
  w (T'.image σ)

theorem shattered_relabel {n : ℕ} {P : Set (ℝ × ℝ)}
    {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ}
    (hP : ShatteredSimplePolygon P S w) (σ : Equiv.Perm (Fin n)) :
    ShatteredSimplePolygon P (relabelS σ S) (relabelW σ w) :=
  NewEnclosure.hereditary_shattered_emb hP σ.toEmbedding

private lemma erase_image_perm {n : ℕ} (σ : Equiv.Perm (Fin n))
    (S : Fin n → ℝ × ℝ) (B' : Finset (Fin n)) (i : Fin n) :
    (B'.erase i).image (relabelS σ S) = ((B'.image σ).erase (σ i)).image S := by
  ext x
  simp only [Finset.mem_image, Finset.mem_erase, relabelS, Function.comp_apply]
  constructor
  · rintro ⟨j, ⟨hji, hjB⟩, rfl⟩
    exact ⟨σ j, ⟨σ.injective.ne hji, ⟨j, hjB, rfl⟩⟩, rfl⟩
  · rintro ⟨k, ⟨hksi, ⟨j, hjB, rfl⟩⟩, rfl⟩
    exact ⟨j, ⟨fun h => hksi (congrArg σ h), hjB⟩, rfl⟩

private lemma univ_image_perm {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    (Finset.univ : Finset (Fin n)).image σ = Finset.univ := by
  ext k
  simp only [Finset.mem_image, Finset.mem_univ, true_and, iff_true]
  exact ⟨σ.symm k, σ.apply_symm_apply k⟩

theorem mem_hullVertices_relabel {n : ℕ} (σ : Equiv.Perm (Fin n))
    (S : Fin n → ℝ × ℝ) (i : Fin n) :
    i ∈ PolygonCore.hullVertices (relabelS σ S) ↔ σ i ∈ PolygonCore.hullVertices S := by
  simp only [PolygonCore.hullVertices, Finset.mem_filter, Finset.mem_univ, true_and]
  have heq : ((Finset.univ.erase i).image (relabelS σ S)) =
      ((Finset.univ.erase (σ i)).image S) := by
    rw [erase_image_perm σ S Finset.univ i, univ_image_perm]
  rw [heq]
  rfl

theorem hullVertices_image_relabel {n : ℕ} (σ : Equiv.Perm (Fin n)) (S : Fin n → ℝ × ℝ) :
    (PolygonCore.hullVertices (relabelS σ S)).image (relabelS σ S) =
      (PolygonCore.hullVertices S).image S := by
  ext x
  simp only [Finset.mem_image]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨σ i, (mem_hullVertices_relabel σ S i).mp hi, rfl⟩
  · rintro ⟨k, hk, rfl⟩
    refine ⟨σ.symm k, (mem_hullVertices_relabel σ S (σ.symm k)).mpr ?_, ?_⟩
    · rwa [σ.apply_symm_apply]
    · change S (σ (σ.symm k)) = S k
      rw [σ.apply_symm_apply]

theorem mem_interiorPoints_relabel {n : ℕ} (σ : Equiv.Perm (Fin n))
    (S : Fin n → ℝ × ℝ) (i : Fin n) :
    i ∈ PolygonCore.interiorPoints (relabelS σ S) ↔ σ i ∈ PolygonCore.interiorPoints S := by
  simp only [PolygonCore.interiorPoints, Finset.mem_sdiff, Finset.mem_univ, true_and,
    mem_hullVertices_relabel]

theorem mem_certifiedSet_relabel {n : ℕ} {P : Set (ℝ × ℝ)}
    {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ}
    (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    i ∈ PolygonCore.certifiedSet P (relabelS σ S) (relabelW σ w) ↔
      σ i ∈ PolygonCore.certifiedSet P S w := by
  simp only [PolygonCore.certifiedSet, PolygonCore.IsCertified, Finset.mem_filter,
    mem_hullVertices_relabel, hullVertices_image_relabel]
  constructor
  · rintro ⟨hiB, _, T', hmiss, hnb, hfront⟩
    refine ⟨hiB, hiB, T'.image σ, hmiss, ?_, hfront⟩
    intro b hbB hedge
    have hb_eq : σ (σ.symm b) = b := σ.apply_symm_apply b
    have hb_mem : σ (σ.symm b) ∈ PolygonCore.hullVertices S := by rwa [hb_eq]
    have hedge' : IsCCWHullEdge ((PolygonCore.hullVertices S).image S)
        (relabelS σ S (σ.symm b)) (relabelS σ S i) ∨
        IsCCWHullEdge ((PolygonCore.hullVertices S).image S)
        (relabelS σ S i) (relabelS σ S (σ.symm b)) := by
      change IsCCWHullEdge _ (S (σ (σ.symm b))) (S (σ i)) ∨
          IsCCWHullEdge _ (S (σ i)) (S (σ (σ.symm b)))
      rwa [hb_eq]
    have h1 : Sees P (w (T'.image σ)) (S (σ (σ.symm b))) := hnb (σ.symm b) hb_mem hedge'
    rwa [hb_eq] at h1
  · rintro ⟨hiB, _, T, hmiss, hnb, hfront⟩
    let T' := T.image σ.symm
    have hT_eq : T'.image σ = T := by
      ext k; simp [T', Finset.mem_image]
    refine ⟨hiB, hiB, T', ?_, ?_, ?_⟩
    · change ¬ Sees P (w (T'.image σ)) (S (σ i))
      rwa [hT_eq]
    · intro b' hb'B hedge'
      have h1 := hnb (σ b') hb'B hedge'
      change Sees P (w (T'.image σ)) (S (σ b'))
      rwa [hT_eq]
    · change IsFrontVertex _ (w (T'.image σ)) (S (σ i))
      rwa [hT_eq]

/-- Horizontal reflection `(x, y) ↦ (-x, y)`, negating `orient2D` and reversing CCW cyclic order. -/
def reflX (p : ℝ × ℝ) : ℝ × ℝ := (-p.1, p.2)

@[simp] theorem reflX_invol (p : ℝ × ℝ) : reflX (reflX p) = p := by
  ext <;> simp [reflX]

theorem reflX_inj : Function.Injective reflX := fun p q h => by
  have := congrArg reflX h; simpa using this

@[simp] theorem orient2D_reflX (a b c : ℝ × ℝ) :
    orient2D (reflX a) (reflX b) (reflX c) = -orient2D a b c := by
  unfold orient2D reflX; ring

theorem orientSign_reflX {a b c : ℝ × ℝ} (hne : orient2D a b c ≠ 0) :
    orientSign (reflX a) (reflX b) (reflX c) = !orientSign a b c := by
  cases hs : orientSign a b c
  · have hlt : orient2D a b c < 0 := (orientSign_eq_false_iff_of_ne_zero hne).mp hs
    rw [Bool.not_false, orientSign_eq_true_iff, orient2D_reflX]; linarith
  · have hgt : 0 < orient2D a b c := (orientSign_eq_true_iff a b c).mp hs
    rw [Bool.not_true, orientSign_eq_false_iff, orient2D_reflX]; linarith

private lemma dist_reflX (u v : ℝ × ℝ) : dist (reflX u) (reflX v) = dist u v := by
  simp only [Prod.dist_eq, reflX, Real.dist_eq]
  have h1 : |-u.1 - -v.1| = |u.1 - v.1| := by
    rw [show -u.1 - -v.1 = -(u.1 - v.1) by ring, abs_neg]
  rw [h1]

private lemma segment_reflX (x y : ℝ × ℝ) :
    segment ℝ (reflX x) (reflX y) = reflX '' segment ℝ x y := by
  ext p
  simp only [segment_eq_image, Set.mem_image]
  constructor
  · rintro ⟨t, ht, rfl⟩
    refine ⟨(1 - t) • x + t • y, ⟨t, ht, rfl⟩, ?_⟩
    ext <;> simp [reflX, smul_eq_mul] <;> ring
  · rintro ⟨q, ⟨t, ht, rfl⟩, rfl⟩
    refine ⟨t, ht, ?_⟩
    ext <;> simp [reflX, smul_eq_mul] <;> ring

theorem sees_reflX_iff {P : Set (ℝ × ℝ)} {x y : ℝ × ℝ} :
    Sees (reflX '' P) (reflX x) (reflX y) ↔ Sees P x y := by
  constructor
  · intro h p hp
    have hmem : reflX p ∈ reflX '' P := h (by rw [segment_reflX]; exact ⟨p, hp, rfl⟩)
    rcases hmem with ⟨q, hqP, hqp⟩
    rwa [← reflX_inj hqp]
  · intro h p hp
    rw [segment_reflX] at hp
    rcases hp with ⟨q, hq, rfl⟩
    exact ⟨q, h hq, rfl⟩

private def reflXLinear : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ) where
  toFun := reflX
  map_add' p q := by ext <;> simp [reflX] <;> ring
  map_smul' r p := by ext <;> simp [reflX]

private lemma mem_convexHull_reflX_iff {E : Set (ℝ × ℝ)} {p : ℝ × ℝ} :
    reflX p ∈ convexHull ℝ (reflX '' E) ↔ p ∈ convexHull ℝ E := by
  have heq : reflX '' convexHull ℝ E = convexHull ℝ (reflX '' E) :=
    reflXLinear.toAffineMap.image_convexHull E
  rw [← heq]
  exact ⟨fun ⟨q, hq, hqp⟩ => reflX_inj hqp ▸ hq, fun hp => ⟨p, hp, rfl⟩⟩

private def reflXWedge (R : OpenWedge) : OpenWedge where
  y := reflX R.y
  u₁ := (-R.u₂.1, R.u₂.2)
  u₂ := (-R.u₁.1, R.u₁.2)
  h_nondeg := by
    have h := R.h_nondeg
    linarith [show (-R.u₂.1) * R.u₁.2 - R.u₂.2 * (-R.u₁.1) =
      R.u₁.1 * R.u₂.2 - R.u₁.2 * R.u₂.1 by ring]

private lemma reflXWedge_memOpen (R : OpenWedge) (p : ℝ × ℝ) :
    (reflXWedge R).MemOpen (reflX p) ↔ R.MemOpen p := by
  dsimp [OpenWedge.MemOpen, reflXWedge, reflX]
  constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨by linarith, by linarith⟩

private lemma reflXWedge_memExt (R : OpenWedge) (p : ℝ × ℝ) :
    (reflXWedge R).MemExt (reflX p) ↔ R.MemExt p := by
  dsimp [OpenWedge.MemExt, reflXWedge, reflX]
  constructor
  · rintro (h1 | h2)
    · exact Or.inr (by linarith)
    · exact Or.inl (by linarith)
  · rintro (h1 | h2)
    · exact Or.inr (by linarith)
    · exact Or.inl (by linarith)

theorem shattered_reflX {n : ℕ} {P : Set (ℝ × ℝ)}
    {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ}
    (hP : ShatteredSimplePolygon P S w) :
    ShatteredSimplePolygon (reflX '' P) (reflX ∘ S) (reflX ∘ w) where
  s_in_P i := ⟨S i, hP.s_in_P i, rfl⟩
  w_in_P T := ⟨w T, hP.w_in_P T, rfl⟩
  shatters T i := by simp only [Function.comp_apply, sees_reflX_iff, hP.shatters]
  s_inj := reflX_inj.comp hP.s_inj
  w_inj := reflX_inj.comp hP.w_inj
  s_ne_w i T h := hP.s_ne_w i T (reflX_inj h)
  no_three_collinear p q r hp hq hr hpq hqr hpr := by
    have hmem : ∀ z, z ∈ Set.range (reflX ∘ S) ∪ Set.range (reflX ∘ w) →
        reflX z ∈ Set.range S ∪ Set.range w := by
      rintro _ (⟨i, rfl⟩ | ⟨T, rfl⟩)
      · exact Or.inl ⟨i, by simp⟩
      · exact Or.inr ⟨T, by simp⟩
    have h0 := hP.no_three_collinear (reflX p) (reflX q) (reflX r)
      (hmem p hp) (hmem q hq) (hmem r hr)
      (reflX_inj.ne hpq) (reflX_inj.ne hqr) (reflX_inj.ne hpr)
    intro hc; apply h0; rw [orient2D_reflX, hc, neg_zero]
  open_vis_nbhd T hT := by
    obtain ⟨ε, hε, hball⟩ := hP.open_vis_nbhd T hT
    refine ⟨ε, hε, fun u hu => ?_⟩
    have hu' : dist (reflX u) (w T) < ε := by
      have := dist_reflX u (reflX (w T))
      simpa using this.trans_lt hu
    obtain ⟨huP, hsees⟩ := hball (reflX u) hu'
    refine ⟨⟨reflX u, huP, reflX_invol u⟩, fun i hi => ?_⟩
    have hs := hsees i hi
    have := sees_reflX_iff.mpr hs
    simpa using this
  triangle_enclosure x hx y hy z hz hxy hyz hxz := by
    rcases hx with ⟨x', hx', rfl⟩
    rcases hy with ⟨y', hy', rfl⟩
    rcases hz with ⟨z', hz', rfl⟩
    have htri := hP.triangle_enclosure x' hx' y' hy' z' hz'
      (sees_reflX_iff.mp hxy) (sees_reflX_iff.mp hyz) (sees_reflX_iff.mp hxz)
    intro p hp
    have hset : ({reflX x', reflX y', reflX z'} : Set (ℝ × ℝ)) =
        reflX '' ({x', y', z'} : Set (ℝ × ℝ)) := by
      ext u; simp [eq_comm]
    have hp1 : reflX (reflX p) ∈ convexHull ℝ (reflX '' ({x', y', z'} : Set (ℝ × ℝ))) := by
      rwa [reflX_invol, ← hset]
    have hp' : reflX p ∈ convexHull ℝ ({x', y', z'} : Set (ℝ × ℝ)) :=
      mem_convexHull_reflX_iff.mp hp1
    exact ⟨reflX p, htri hp', reflX_invol p⟩
  two_path_enclosure s t π₁ π₂ hst hp₁ hp₂ hL hR := by
    have hst' : reflX s ≠ reflX t := reflX_inj.ne hst
    have hpath : ∀ {π : List (ℝ × ℝ)}, IsPolygonalPathIn (reflX '' P) s t π →
        IsPolygonalPathIn P (reflX s) (reflX t) (π.map reflX) := by
      intro π ⟨hne, hhd, hlst, hmem, hch⟩
      refine ⟨by simp [hne], ?_, ?_, ?_, ?_⟩
      · cases π with | nil => contradiction | cons a l => simpa using congrArg reflX hhd
      · rw [List.getLast_map]; exact congrArg reflX hlst
      · intro x hx
        rcases List.mem_map.mp hx with ⟨y, hy, rfl⟩
        rcases hmem y hy with ⟨z, hz, hyz⟩
        have hzy : z = reflX y := by simpa using congrArg reflX hyz
        rwa [← hzy]
      · rw [List.isChain_map]
        exact hch.imp (fun u v huv => sees_reflX_iff.mp (by simpa using huv))
    have hL' : InteriorOnRight (reflX s) (reflX t) (π₁.map reflX) := by
      refine ⟨by simpa using hL.1, fun k hk hk0 hk1 => ?_⟩
      simp only [List.length_map] at hk hk1
      rw [List.getElem_map, orient2D_reflX]
      exact neg_lt_zero.mpr (hL.2 k hk hk0 hk1)
    have hR' : InteriorOnLeft (reflX s) (reflX t) (π₂.map reflX) := by
      refine ⟨by simpa using hR.1, fun k hk hk0 hk1 => ?_⟩
      simp only [List.length_map] at hk hk1
      rw [List.getElem_map, orient2D_reflX]
      exact neg_pos.mpr (hR.2 k hk hk0 hk1)
    have hsees := hP.two_path_enclosure (reflX s) (reflX t) (π₂.map reflX) (π₁.map reflX)
      hst' (hpath hp₂) (hpath hp₁) hR' hL'
    simpa using sees_reflX_iff.mpr hsees
  gk14_no_ten_convex B hconv := by
    refine hP.gk14_no_ten_convex B (fun i hi hm => hconv i hi ?_)
    have himg : (((B.erase i).image (reflX ∘ S) : Finset (ℝ × ℝ)) : Set (ℝ × ℝ)) =
        reflX '' (((B.erase i).image S : Finset (ℝ × ℝ)) : Set (ℝ × ℝ)) := by
      ext u; simp
    rw [himg]
    exact mem_convexHull_reflX_iff.mpr hm
  isler_six_wedges R h_all := by
    refine hP.isler_six_wedges (fun i => reflXWedge (R i)) (fun m => ?_)
    obtain ⟨p, hp⟩ := h_all m
    refine ⟨reflX p, fun i => ?_⟩
    have hi := hp i
    cases hmi : m i
    · rw [hmi] at hi
      simpa using (reflXWedge_memExt (R i) p).mpr (by simpa using hi)
    · rw [hmi] at hi
      simpa using (reflXWedge_memOpen (R i) p).mpr (by simpa using hi)

theorem hullVertices_reflX {n : ℕ} (S : Fin n → ℝ × ℝ) :
    PolygonCore.hullVertices (reflX ∘ S) = PolygonCore.hullVertices S := by
  ext i
  simp only [PolygonCore.hullVertices, Finset.mem_filter, Finset.mem_univ, true_and]
  have himg : (((Finset.univ.erase i).image (reflX ∘ S) : Finset (ℝ × ℝ)) : Set (ℝ × ℝ)) =
      reflX '' (((Finset.univ.erase i).image S : Finset (ℝ × ℝ)) : Set (ℝ × ℝ)) := by
    ext u; simp
  rw [himg]
  exact not_congr mem_convexHull_reflX_iff

theorem interiorPoints_reflX {n : ℕ} (S : Fin n → ℝ × ℝ) :
    PolygonCore.interiorPoints (reflX ∘ S) = PolygonCore.interiorPoints S := by
  simp only [PolygonCore.interiorPoints, hullVertices_reflX]

private lemma isCCWHullEdge_reflX_iff {C : Finset (ℝ × ℝ)} {a b : ℝ × ℝ} :
    IsCCWHullEdge (C.image reflX) (reflX a) (reflX b) ↔ IsCCWHullEdge C b a := by
  constructor
  · rintro ⟨ha, hb, hab, hall⟩
    have haC : a ∈ C := by
      rcases Finset.mem_image.mp ha with ⟨x, hx, hxa⟩
      rwa [← reflX_inj hxa]
    have hbC : b ∈ C := by
      rcases Finset.mem_image.mp hb with ⟨x, hx, hxb⟩
      rwa [← reflX_inj hxb]
    refine ⟨hbC, haC, fun h => hab (congrArg reflX h.symm), fun c hc hcb hca => ?_⟩
    have h1 := hall (reflX c) (Finset.mem_image_of_mem reflX hc)
      (reflX_inj.ne hca) (reflX_inj.ne hcb)
    rw [orient2D_reflX, orient2D_swap12] at h1
    linarith
  · rintro ⟨hbC, haC, hba, hall⟩
    refine ⟨Finset.mem_image_of_mem reflX haC, Finset.mem_image_of_mem reflX hbC,
      reflX_inj.ne hba.symm, fun c' hc' hc'a hc'b => ?_⟩
    rcases Finset.mem_image.mp hc' with ⟨c, hcC, rfl⟩
    have h1 := hall c hcC (fun h => hc'b (congrArg reflX h)) (fun h => hc'a (congrArg reflX h))
    rw [orient2D_reflX, orient2D_swap12]
    linarith

private lemma isFrontVertex_reflX_iff {C : Finset (ℝ × ℝ)} {v f : ℝ × ℝ} :
    IsFrontVertex (C.image reflX) (reflX v) (reflX f) ↔ IsFrontVertex C v f := by
  have himg_invol : (C.image reflX).image reflX = C := by
    rw [Finset.image_image]
    ext x
    simp only [Finset.mem_image, Function.comp_apply, reflX_invol, exists_eq_right]
  have hf_imp : ∀ {D : Finset (ℝ × ℝ)} {u g : ℝ × ℝ},
      IsFrontVertex D u g → IsFrontVertex (D.image reflX) (reflX u) (reflX g) := by
    rintro D u g ⟨b, c, hbg, hgc, hbv, hcv⟩
    refine ⟨reflX c, reflX b, isCCWHullEdge_reflX_iff.mpr hgc, isCCWHullEdge_reflX_iff.mpr hbg, ?_, ?_⟩
    · rw [orient2D_reflX, orient2D_swap12]; linarith
    · rw [orient2D_reflX, orient2D_swap12]; linarith
  refine ⟨fun h => ?_, fun h => hf_imp h⟩
  have h' := hf_imp h
  rwa [himg_invol, reflX_invol, reflX_invol] at h'

theorem certifiedSet_reflX {n : ℕ} {P : Set (ℝ × ℝ)}
    {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ} :
    PolygonCore.certifiedSet (reflX '' P) (reflX ∘ S) (reflX ∘ w) =
      PolygonCore.certifiedSet P S w := by
  ext f
  simp only [PolygonCore.certifiedSet, PolygonCore.IsCertified, Finset.mem_filter,
    hullVertices_reflX]
  have himg : (PolygonCore.hullVertices S).image (reflX ∘ S) =
      ((PolygonCore.hullVertices S).image S).image reflX := Finset.image_image.symm
  rw [himg]
  constructor
  · rintro ⟨hfB, _, T, hmiss, hnb, hfront⟩
    refine ⟨hfB, hfB, T, fun hs => hmiss (sees_reflX_iff.mpr hs), ?_,
      isFrontVertex_reflX_iff.mp hfront⟩
    intro b hbB hedge
    have hedge' : IsCCWHullEdge (((PolygonCore.hullVertices S).image S).image reflX)
        (reflX (S b)) (reflX (S f)) ∨
        IsCCWHullEdge (((PolygonCore.hullVertices S).image S).image reflX)
        (reflX (S f)) (reflX (S b)) := by
      rcases hedge with h1 | h2
      · exact Or.inr (isCCWHullEdge_reflX_iff.mpr h1)
      · exact Or.inl (isCCWHullEdge_reflX_iff.mpr h2)
    exact sees_reflX_iff.mp (hnb b hbB hedge')
  · rintro ⟨hfB, _, T, hmiss, hnb, hfront⟩
    refine ⟨hfB, hfB, T, fun hs => hmiss (sees_reflX_iff.mp hs), ?_,
      isFrontVertex_reflX_iff.mpr hfront⟩
    intro b hbB hedge'
    have hedge : IsCCWHullEdge ((PolygonCore.hullVertices S).image S) (S b) (S f) ∨
        IsCCWHullEdge ((PolygonCore.hullVertices S).image S) (S f) (S b) := by
      rcases hedge' with h1 | h2
      · exact Or.inr (isCCWHullEdge_reflX_iff.mp h1)
      · exact Or.inl (isCCWHullEdge_reflX_iff.mp h2)
    exact sees_reflX_iff.mpr (hnb b hbB hedge)


/-! ## 2. Unmarked Hull-Slice Inheritance (`Corollary 3.3` & `VC-dim ≤ 11`) -/

/-- Witness slice `w'(T') := w(T'.image ι ∪ A₀)` for an embedded subset `ι : Fin m ↪ Fin n`
    and fixed auxiliary slice `A₀` disjoint from `range ι`. -/
def sliceWitness {n m : ℕ} (ι : Fin m ↪ Fin n) (A₀ : Finset (Fin n))
    (w : Finset (Fin n) → ℝ × ℝ) (T' : Finset (Fin m)) : ℝ × ℝ :=
  w (T'.image ι ∪ A₀)

/-- Shattering under `(G1)–(G2)` is preserved on any slice `w'(T') = w(T'.image ι ∪ A₀)`
    with `A₀` disjoint from `univ.image ι`. -/
theorem shattered_slice_emb {n m : ℕ} {P : Set (ℝ × ℝ)}
    {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ}
    (hP : ShatteredSimplePolygon P S w)
    (ι : Fin m ↪ Fin n) (A₀ : Finset (Fin n))
    (hdisj : Disjoint (Finset.univ.image ι) A₀) :
    ShatteredSimplePolygon P (S ∘ ι) (sliceWitness ι A₀ w) where
  s_in_P j := hP.s_in_P (ι j)
  w_in_P T' := hP.w_in_P (T'.image ι ∪ A₀)
  shatters T' j := by
    change Sees P (w (T'.image ι ∪ A₀)) (S (ι j)) ↔ j ∈ T'
    rw [hP.shatters]
    have hj_notA : ι j ∉ A₀ :=
      Finset.disjoint_left.mp hdisj (Finset.mem_image_of_mem ι (Finset.mem_univ j))
    simp [Finset.mem_union, Finset.mem_image, ι.injective.eq_iff, hj_notA]
  s_inj := hP.s_inj.comp ι.injective
  w_inj T₁ T₂ heq := by
    have hu := hP.w_inj heq
    ext j
    have hj_notA : ι j ∉ A₀ :=
      Finset.disjoint_left.mp hdisj (Finset.mem_image_of_mem ι (Finset.mem_univ j))
    have hmem : ι j ∈ T₁.image ι ∪ A₀ ↔ ι j ∈ T₂.image ι ∪ A₀ := by rw [hu]
    simpa [Finset.mem_union, Finset.mem_image, ι.injective.eq_iff, hj_notA] using hmem
  s_ne_w j T' := hP.s_ne_w (ι j) (T'.image ι ∪ A₀)
  no_three_collinear p q r hp hq hr hpq hqr hpr := by
    have hsub : Set.range (S ∘ ι) ∪ Set.range (sliceWitness ι A₀ w) ⊆
        Set.range S ∪ Set.range w := by
      rintro x (⟨j, rfl⟩ | ⟨T', rfl⟩)
      · exact Or.inl ⟨ι j, rfl⟩
      · exact Or.inr ⟨T'.image ι ∪ A₀, rfl⟩
    exact hP.no_three_collinear p q r (hsub hp) (hsub hq) (hsub hr) hpq hqr hpr
  open_vis_nbhd T' hT' := by
    have hne : (T'.image ι ∪ A₀).Nonempty :=
      (Finset.image_nonempty.mpr hT').mono Finset.subset_union_left
    obtain ⟨ε, hε, hball⟩ := hP.open_vis_nbhd (T'.image ι ∪ A₀) hne
    refine ⟨ε, hε, fun u hu => ?_⟩
    obtain ⟨huP, hsees⟩ := hball u hu
    exact ⟨huP, fun j hj => hsees (ι j) (Finset.mem_union_left _ (Finset.mem_image_of_mem ι hj))⟩
  triangle_enclosure := hP.triangle_enclosure
  two_path_enclosure := hP.two_path_enclosure
  gk14_no_ten_convex B' hconv :=
    (NewEnclosure.hereditary_shattered_emb hP ι).gk14_no_ten_convex B' hconv
  isler_six_wedges := hP.isler_six_wedges

/-- **Corollary 3.3 (`unmarked_hull_slice_inheritance`, `vc_dim_6_simplified.tex` lines 239–248)**:
    For any `ShatteredSimplePolygon P S w` (`3 ≤ n`), any subset `D' ⊆ D = hullVertices S \ certifiedSet P S w`
    of size `m ≥ 3` (`ι : Fin m ↪ Fin n`), and any slice `A₀` disjoint from `D'`, the induced
    instance `(S ∘ ι, sliceWitness ι A₀ w)` is shattered in `P`, lies in strictly convex position
    (`interiorPoints = ∅`), and has **empty certified set** (`certifiedSet = ∅`). -/
theorem unmarked_hull_slice_inheritance {n m : ℕ} {P : Set (ℝ × ℝ)}
    {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ}
    (hP : ShatteredSimplePolygon P S w) (hm : 3 ≤ m)
    (ι : Fin m ↪ Fin n)
    (hιD : ∀ j : Fin m, ι j ∈ PolygonCore.hullVertices S \ PolygonCore.certifiedSet P S w)
    (A₀ : Finset (Fin n)) (hdisj : Disjoint (Finset.univ.image ι) A₀) :
    let S' := S ∘ ι
    let w' := sliceWitness ι A₀ w
    ShatteredSimplePolygon P S' w' ∧
    PolygonCore.interiorPoints S' = ∅ ∧
    PolygonCore.certifiedSet P S' w' = ∅ := by
  have hn : 3 ≤ n := le_trans hm (by simpa using Fintype.card_le_of_injective ι ι.injective)
  let S' := S ∘ ι
  let w' := sliceWitness ι A₀ w
  have hP' : ShatteredSimplePolygon P S' w' := shattered_slice_emb hP ι A₀ hdisj
  have hA_empty : PolygonCore.interiorPoints S' = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro j hj
    have hj_notB : j ∉ PolygonCore.hullVertices S' := (Finset.mem_sdiff.mp hj).2
    have hj_hull : S' j ∈ convexHull ℝ (((Finset.univ.erase j).image S') : Set (ℝ × ℝ)) := by
      by_contra hnot
      exact hj_notB (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hnot⟩)
    have himg_sub : (((Finset.univ.erase j).image S') : Set (ℝ × ℝ)) ⊆
        (((Finset.univ.erase (ι j)).image S : Finset (ℝ × ℝ)) : Set (ℝ × ℝ)) := by
      intro p hp
      rcases Finset.mem_image.mp hp with ⟨k, hk, rfl⟩
      exact Finset.mem_image.mpr ⟨ι k,
        Finset.mem_erase.mpr ⟨ι.injective.ne (Finset.mem_erase.mp hk).1, Finset.mem_univ _⟩, rfl⟩
    have hjB : ι j ∈ PolygonCore.hullVertices S := (Finset.mem_sdiff.mp (hιD j)).1
    exact (Finset.mem_filter.mp hjB).2 (convexHull_mono himg_sub hj_hull)
  have hH_empty : PolygonCore.certifiedSet P S' w' = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro j hj
    have hcert : IsCertified P S' w' j := (Finset.mem_filter.mp hj).2
    obtain ⟨b, c, _, _, hbj, hcj, hbc, _, _, hall⟩ :=
      certified_neighbors_and_front hP' hm hcert
    let Tz' : Finset (Fin m) := Finset.univ.erase j
    have hzb : Sees P (w' Tz') (S' b) :=
      (hP'.shatters Tz' b).mpr (Finset.mem_erase.mpr ⟨hbj, Finset.mem_univ b⟩)
    have hzc : Sees P (w' Tz') (S' c) :=
      (hP'.shatters Tz' c).mpr (Finset.mem_erase.mpr ⟨hcj, Finset.mem_univ c⟩)
    have htri : InOpenTri (w' Tz') (S' b) (S' c) (S' j) := (hall Tz' hzb hzc).1
    let Tw : Finset (Fin n) := Tz'.image ι ∪ A₀
    have hj_notA : ι j ∉ A₀ :=
      Finset.disjoint_left.mp hdisj (Finset.mem_image_of_mem ι (Finset.mem_univ j))
    have hj_miss : ι j ∉ Tw := by
      simp [Tw, Tz', Finset.mem_union, Finset.mem_image, ι.injective.eq_iff, hj_notA]
    have hb_in : ι b ∈ Tw :=
      Finset.mem_union_left _ (Finset.mem_image_of_mem ι (Finset.mem_erase.mpr ⟨hbj, Finset.mem_univ b⟩))
    have hc_in : ι c ∈ Tw :=
      Finset.mem_union_left _ (Finset.mem_image_of_mem ι (Finset.mem_erase.mpr ⟨hcj, Finset.mem_univ c⟩))
    have htri_bool : inOpenTriBool (S (ι j)) (w Tw) (S (ι b)) (S (ι c)) = true :=
      (inOpenTriBool_S_w_S_S hP (ι.injective.ne hbj.symm) (ι.injective.ne hcj.symm)
        (ι.injective.ne hbc) Tw).mpr htri
    have hjD : ι j ∈ _root_.hullVertices S \ PolygonCore.certifiedSet P S w := by
      simpa [hullVertices_eq] using hιD j
    have hfalse := non_certified_obstruction_clause_C4 hP hn hjD hj_miss hb_in hc_in (ι.injective.ne hbc)
    rw [htri_bool] at hfalse
    exact Bool.noConfusion hfalse
  exact ⟨hP', hA_empty, hH_empty⟩

/-- **Immediate `VC-dim(P) ≤ 11` Corollary**:
    Once Stage 1 Case `(7, 0)` (7 convex shattered points with `certifiedSet = ∅`) is ruled out,
    `card_M_le_five` (`|A ∪ H| ≤ 5`) + `unmarked_hull_slice_inheritance` immediately rules out
    every shattered set of size `n ≥ 12` with zero RUP certificates! -/
theorem vcdim_le_eleven_of_no_unmarked_convex_seven {P : Set (ℝ × ℝ)}
    (hno70 : ∀ (S7 : Fin 7 → ℝ × ℝ) (w7 : Finset (Fin 7) → ℝ × ℝ),
      ShatteredSimplePolygon P S7 w7 →
      PolygonCore.interiorPoints S7 = ∅ →
      PolygonCore.certifiedSet P S7 w7 = ∅ → False)
    {n : ℕ} (hn : 12 ≤ n)
    {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ}
    (hP : ShatteredSimplePolygon P S w) : False := by
  let H := PolygonCore.certifiedSet P S w
  let D := PolygonCore.hullVertices S \ H
  have hM5 : (_root_.interiorPoints S ∪ H).card ≤ 5 :=
    SourceGapAndCaseSplits.card_M_le_five (by omega) hP
  have hDM : (_root_.hullVertices S \ H).card + (_root_.interiorPoints S ∪ H).card = n :=
    SourceGapAndCaseSplits.card_D_add_M_eq S w P
  have hD7 : 7 ≤ D.card := by
    have : D.card = (_root_.hullVertices S \ H).card := by simp [D, hullVertices_eq]
    omega
  obtain ⟨D₇, hD₇_sub, hD₇_card⟩ := Finset.exists_subset_card_eq hD7
  let e : D₇ ≃ Fin 7 := D₇.equivFinOfCardEq hD₇_card
  let ι : Fin 7 ↪ Fin n := ⟨fun j => (e.symm j).1, fun i j h => e.symm.injective (Subtype.ext h)⟩
  have hιD : ∀ j : Fin 7, ι j ∈ D := fun j => hD₇_sub (e.symm j).2
  obtain ⟨hP7, hA7, hH7⟩ :=
    unmarked_hull_slice_inheritance hP (by decide : 3 ≤ 7) ι hιD ∅ (Finset.disjoint_empty_right _)
  exact hno70 _ _ hP7 hA7 hH7


/-! ## 3. Pocket Exit-Edge Exclusion and Monotonicity (`Lemma 3.4(i)–(ii)`) -/

/-- **Lemma 3.4(i) (`exit_edge_ne_pocket_lr`, `vc_dim_6_simplified.tex` lines 250–259)**:
    Suppose `3 ≤ |D|` and `H = certifiedSet P S w` is nonempty, bounded on `∂ conv(B)` by `(l, r)`
    with `dc.p_idx i_lr = l`, `dc.p_idx (i_lr + 1) = r`, and some `h₀ ∈ H` satisfying
    `0 < orient2D (S l) (S h₀) (S r)` and `InOpenTri (w D) (S l) (S r) (S h₀)`.
    Then for **every** `y ∈ interiorPoints S ∪ H` (both interior points `A` and certified vertices `H`),
    its exit edge `i` on `dc` satisfies `i ≠ i_lr`. -/
theorem exit_edge_ne_pocket_lr {n : ℕ} {D₀ : Finset (Fin n)}
    {S : Fin n → ℝ × ℝ} {u : ℝ × ℝ}
    (dc : CyclicSubsetBoundary S D₀)
    {l r h₀ : Fin n} {i_lr : Fin (dc.m + 3)}
    (hil : dc.p_idx i_lr = l) (hir : dc.p_idx (i_lr + 1) = r)
    (hlhr : 0 < orient2D (S l) (S h₀) (S r))
    (htri_h₀ : InOpenTri u (S l) (S r) (S h₀))
    {i : Fin (dc.m + 3)}
    (hui : 0 < orient2D (S (dc.p_idx i)) (S (dc.p_idx (i + 1))) u) :
    i ≠ i_lr := by
  intro heq
  subst heq
  rw [hil, hir] at hui
  rcases htri_h₀ with ⟨μ₁, μ₂, μ₃, h1, _, _, hsum, hx1, hx2⟩
  have hor : orient2D (S l) (S r) (S h₀) = μ₁ * orient2D (S l) (S r) u := by
    have h1m : μ₁ = 1 - μ₂ - μ₃ := by linarith
    unfold orient2D; rw [hx1, hx2, h1m]; ring
  have hneg : orient2D (S l) (S r) (S h₀) < 0 := by
    rw [orient2D_swap23]; linarith
  have hu_neg : orient2D (S l) (S r) u < 0 :=
    neg_of_mul_neg_right (by linarith) (le_of_lt h1)
  linarith

/-- Step offset `m(e) ∈ {0, ..., ν - 2}` of a non-`(l, r)` edge `i` of `D` counted CCW starting
    at `r = dc.p_idx (i_lr + 1)`. -/
def stepFromR {N : ℕ} [NeZero N] (i_lr i : Fin N) : ℕ :=
  (i - (i_lr + 1)).val

/-- **Lemma 3.4(ii) (`pocket_exit_edge_monotonicity`, `vc_dim_6_simplified.tex` lines 253–266,
    `ideation_FINAL_SOLUTION.md` Theorem 4.1)**:
    Let `(l, h₁, h₂, r)` lie in strict CCW order along the pocket arc of `∂ conv(B)`
    (`0 < orient2D (S l) (S h₁) (S h₂)` and `0 < orient2D (S h₁) (S h₂) (S r)`), with
    `InOpenTri u (S l) (S r) (S h₁)` and `InOpenTri u (S l) (S r) (S h₂)` (where `u = w D`).
    If `i₁, i₂` are the exit edges of `h₁, h₂` on `dc` (`dc.p_idx i_lr = l`, `dc.p_idx (i_lr + 1) = r`),
    then `stepFromR i_lr i₂ ≤ stepFromR i_lr i₁` (`ν - 2 ≥ m(h₁) ≥ m(h₂) ≥ 0`). -/
theorem pocket_exit_edge_monotonicity {n : ℕ} {D₀ : Finset (Fin n)}
    {S : Fin n → ℝ × ℝ} {u : ℝ × ℝ}
    (dc : CyclicSubsetBoundary S D₀)
    {l r h₁ h₂ : Fin n} {i_lr i₁ i₂ : Fin (dc.m + 3)}
    (hil : dc.p_idx i_lr = l) (hir : dc.p_idx (i_lr + 1) = r)
    (hl12 : 0 < orient2D (S l) (S h₁) (S h₂))
    (h12r : 0 < orient2D (S h₁) (S h₂) (S r))
    (hl1r : 0 < orient2D (S l) (S h₁) (S r))
    (htri_lr1 : InOpenTri u (S l) (S r) (S h₁))
    (htri_lr2 : InOpenTri u (S l) (S r) (S h₂))
    (hu1 : 0 < orient2D (S (dc.p_idx i₁)) (S (dc.p_idx (i₁ + 1))) u)
    (htri_e1 : InOpenTri u (S (dc.p_idx i₁)) (S (dc.p_idx (i₁ + 1))) (S h₁))
    (hu2 : 0 < orient2D (S (dc.p_idx i₂)) (S (dc.p_idx (i₂ + 1))) u)
    (htri_e2 : InOpenTri u (S (dc.p_idx i₂)) (S (dc.p_idx (i₂ + 1))) (S h₂)) :
    stepFromR i_lr i₂ ≤ stepFromR i_lr i₁ := by
  have hi1_ne : i₁ ≠ i_lr := exit_edge_ne_pocket_lr dc hil hir hl1r htri_lr1 hu1
  have hi2_ne : i₂ ≠ i_lr := exit_edge_ne_pocket_lr dc hil hir hl1r htri_lr1 hu2
  let a := stepFromR i_lr i₁
  let b := stepFromR i_lr i₂
  by_contra hlt_not
  have hab : a < b := Nat.lt_of_not_ge hlt_not
  haveI : NeZero (dc.m + 3) := ⟨by omega⟩
  have hb_lt_m2 : b < dc.m + 2 := by
    have hb_lt : b < dc.m + 3 := (i₂ - (i_lr + 1)).isLt
    by_contra hge
    have hb_eq : b = dc.m + 2 := by omega
    apply hi2_ne
    have hsh : finShift (i_lr + 1) b = i₂ := finShift_sub (i_lr + 1) i₂
    rw [hb_eq, ← finShift_one (by omega : 2 ≤ dc.m + 3) i_lr, finShift_add,
        show 1 + (dc.m + 2) = dc.m + 3 by omega, finShift_len] at hsh
    exact hsh.symm
  -- Step 1: 0 < orient2D u (S h₂) (S h₁)
  have hu_h2_h1 : 0 < orient2D u (S h₂) (S h₁) := by
    rcases htri_lr1 with ⟨μ₁, μ₂, μ₃, hμ1, hμ2, hμ3, hμsum, hx1, hx2⟩
    have h12l : 0 < orient2D (S h₁) (S h₂) (S l) := by
      have : orient2D (S h₁) (S h₂) (S l) = orient2D (S l) (S h₁) (S h₂) := by unfold orient2D; ring
      linarith
    have hlin : μ₁ * orient2D (S h₁) (S h₂) u + μ₂ * orient2D (S h₁) (S h₂) (S l) +
        μ₃ * orient2D (S h₁) (S h₂) (S r) = 0 := by
      have hμ1_eq : μ₁ = 1 - μ₂ - μ₃ := by linarith
      have h0 : orient2D (S h₁) (S h₂) (S h₁) = 0 := by unfold orient2D; ring
      conv_rhs => rw [← h0]
      unfold orient2D; rw [hx1, hx2, hμ1_eq]; ring
    have hneg : orient2D (S h₁) (S h₂) u < 0 :=
      neg_of_mul_neg_right (by linarith [mul_pos hμ2 h12l, mul_pos hμ3 h12r]) (le_of_lt hμ1)
    have hid : orient2D u (S h₂) (S h₁) = -orient2D (S h₁) (S h₂) u := by unfold orient2D; ring
    linarith
  -- Step 2: Construct open-edge piercing points z_a and z_b and deduce orient2D u z_a z_b < 0
  rcases htri_e1 with ⟨α₁, β₁, γ₁, hα1, hβ1, hγ1, hsum1, he1_x, he1_y⟩
  rcases htri_e2 with ⟨α₂, β₂, γ₂, hα2, hβ2, hγ2, hsum2, he2_x, he2_y⟩
  let s₁ := β₁ + γ₁
  let s₂ := β₂ + γ₂
  have hs1_pos : 0 < s₁ := add_pos hβ1 hγ1
  have hs2_pos : 0 < s₂ := add_pos hβ2 hγ2
  let wa0 := β₁ / s₁
  let wa1 := γ₁ / s₁
  let wb0 := β₂ / s₂
  let wb1 := γ₂ / s₂
  have hwa0 : 0 < wa0 := div_pos hβ1 hs1_pos
  have hwa1 : 0 < wa1 := div_pos hγ1 hs1_pos
  have hwb0 : 0 < wb0 := div_pos hβ2 hs2_pos
  have hwb1 : 0 < wb1 := div_pos hγ2 hs2_pos
  have hwa_sum : wa0 + wa1 = 1 := by dsimp [wa0, wa1, s₁]; field_simp [ne_of_gt hs1_pos]
  have hwb_sum : wb0 + wb1 = 1 := by dsimp [wb0, wb1, s₂]; field_simp [ne_of_gt hs2_pos]
  let za : ℝ × ℝ :=
    (wa0 * (S (dc.p_idx i₁)).1 + wa1 * (S (dc.p_idx (i₁ + 1))).1,
     wa0 * (S (dc.p_idx i₁)).2 + wa1 * (S (dc.p_idx (i₁ + 1))).2)
  let zb : ℝ × ℝ :=
    (wb0 * (S (dc.p_idx i₂)).1 + wb1 * (S (dc.p_idx (i₂ + 1))).1,
     wb0 * (S (dc.p_idx i₂)).2 + wb1 * (S (dc.p_idx (i₂ + 1))).2)
  have hza_ray : (S h₁).1 = α₁ * u.1 + s₁ * za.1 ∧ (S h₁).2 = α₁ * u.2 + s₁ * za.2 := by
    have hs1_ne : s₁ ≠ 0 := ne_of_gt hs1_pos
    dsimp only [za, wa0, wa1]
    constructor <;> [rw [he1_x]; rw [he1_y]] <;> field_simp [hs1_ne] <;> ring
  have hzb_ray : (S h₂).1 = α₂ * u.1 + s₂ * zb.1 ∧ (S h₂).2 = α₂ * u.2 + s₂ * zb.2 := by
    have hs2_ne : s₂ ≠ 0 := ne_of_gt hs2_pos
    dsimp only [zb, wb0, wb1]
    constructor <;> [rw [he2_x]; rw [he2_y]] <;> field_simp [hs2_ne] <;> ring
  have hu_za_zb_neg : orient2D u za zb < 0 := by
    have hid : (s₁ * s₂) * (-orient2D u za zb) = orient2D u (S h₂) (S h₁) := by
      have hα1_eq : α₁ = 1 - s₁ := by dsimp [s₁]; linarith
      have hα2_eq : α₂ = 1 - s₂ := by dsimp [s₂]; linarith
      unfold orient2D
      rw [hza_ray.1, hza_ray.2, hzb_ray.1, hzb_ray.2, hα1_eq, hα2_eq]; ring
    have hpos_neg : 0 < -orient2D u za zb :=
      pos_of_mul_pos_right (by linarith) (le_of_lt (mul_pos hs1_pos hs2_pos))
    linarith
  -- Step 3: Express q₂ ∈ openSeg(S l, S r) on ray u -> z_b and deduce orient2D q₂ z_a z_b ≤ 0
  rcases htri_lr2 with ⟨ν₁, ν₂, ν₃, hν1, hν2, hν3, hνsum, hlr2_x, hlr2_y⟩
  have h1ν : 0 < 1 - ν₁ := by linarith
  let cl := ν₂ / (1 - ν₁)
  let cr := ν₃ / (1 - ν₁)
  have hcl : 0 < cl := div_pos hν2 h1ν
  have hcr : 0 < cr := div_pos hν3 h1ν
  have hclr_sum : cl + cr = 1 := by dsimp [cl, cr]; field_simp [ne_of_gt h1ν]; linarith
  let q₂ : ℝ × ℝ := (cl * (S l).1 + cr * (S r).1, cl * (S l).2 + cr * (S r).2)
  have hq2_ray : (S h₂).1 = ν₁ * u.1 + (1 - ν₁) * q₂.1 ∧ (S h₂).2 = ν₁ * u.2 + (1 - ν₁) * q₂.2 := by
    have h1ν_ne : 1 - ν₁ ≠ 0 := ne_of_gt h1ν
    dsimp only [q₂, cl, cr]
    constructor <;> [rw [hlr2_x]; rw [hlr2_y]] <;> field_simp [h1ν_ne] <;> ring
  have hlr_u_neg : orient2D (S l) (S r) u < 0 := by
    rcases htri_lr1 with ⟨μ₁', μ₂', μ₃', hμ1', _, _, hμs', hx1', hx2'⟩
    have hor1 : orient2D (S l) (S r) (S h₁) = μ₁' * orient2D (S l) (S r) u := by
      have h1m : μ₁' = 1 - μ₂' - μ₃' := by linarith
      unfold orient2D; rw [hx1', hx2', h1m]; ring
    have hh1_neg : orient2D (S l) (S r) (S h₁) < 0 := by rw [orient2D_swap23]; linarith
    exact neg_of_mul_neg_right (by linarith) (le_of_lt hμ1')
  -- Cyclic enumeration of D₀ starting at r = dc.p_idx (i_lr + 1)
  let dIdx : ℕ → Fin (dc.m + 3) := fun k => finShift (i_lr + 1) k
  have hdIdx_0 : dc.p_idx (dIdx 0) = r := by dsimp [dIdx]; rw [finShift_zero, hir]
  have hdIdx_last : dc.p_idx (dIdx (dc.m + 2)) = l := by
    dsimp [dIdx]
    have h1 : finShift (i_lr + 1) (dc.m + 2) = i_lr := by
      rw [← finShift_one (by omega), finShift_add,
          show 1 + (dc.m + 2) = dc.m + 3 by omega, finShift_len]
    rw [h1, hil]
  have hi1_eq : i₁ = dIdx a := (finShift_sub (i_lr + 1) i₁).symm
  have hi1_succ_eq : i₁ + 1 = dIdx (a + 1) := by
    rw [hi1_eq, finShift_succ (by omega)]
  have hi2_eq : i₂ = dIdx b := (finShift_sub (i_lr + 1) i₂).symm
  have hi2_succ_eq : i₂ + 1 = dIdx (b + 1) := by
    rw [hi2_eq, finShift_succ (by omega)]
  have hccw_dIdx : ∀ k₁ k₂ k₃ : ℕ, k₁ < k₂ → k₂ < k₃ → k₃ < dc.m + 3 →
      0 < orient2D (S (dc.p_idx (dIdx k₁))) (S (dc.p_idx (dIdx k₂))) (S (dc.p_idx (dIdx k₃))) := by
    intro k₁ k₂ k₃ h12 h23 h3
    exact dc.hcyc _ _ _ (cyclicOrder_finShift (i_lr + 1) h12 h23 h3)
  have hlr_zb_nn : 0 ≤ orient2D (S l) (S r) zb := by
    have h_pt : ∀ k : ℕ, k < dc.m + 3 → 0 ≤ orient2D (S l) (S r) (S (dc.p_idx (dIdx k))) := by
      intro k hk
      rw [← hdIdx_last, ← hdIdx_0]
      by_cases hk0 : k = 0
      · subst hk0; rw [orient2D_self_right]
      · by_cases hkl : k = dc.m + 2
        · subst hkl; rw [orient2D_self_outer]
        · have hpos := hccw_dIdx 0 k (dc.m + 2) (by omega) (by omega) (by omega)
          have : orient2D (S (dc.p_idx (dIdx (dc.m + 2)))) (S (dc.p_idx (dIdx 0))) (S (dc.p_idx (dIdx k))) =
              orient2D (S (dc.p_idx (dIdx 0))) (S (dc.p_idx (dIdx k))) (S (dc.p_idx (dIdx (dc.m + 2)))) := by
            unfold orient2D; ring
          exact le_of_lt (by linarith)
    have hid : orient2D (S l) (S r) zb =
        wb0 * orient2D (S l) (S r) (S (dc.p_idx (dIdx b))) +
        wb1 * orient2D (S l) (S r) (S (dc.p_idx (dIdx (b + 1)))) := by
      have hwb0_eq : wb0 = 1 - wb1 := by linarith
      dsimp only [zb]
      rw [hi2_succ_eq, hi2_eq]
      unfold orient2D; rw [hwb0_eq]; ring
    rw [hid]
    exact add_nonneg (mul_nonneg (le_of_lt hwb0) (h_pt b (by omega)))
      (mul_nonneg (le_of_lt hwb1) (h_pt (b + 1) (by omega)))
  have hs2_le : s₂ ≤ 1 - ν₁ := by
    have hq0 : orient2D (S l) (S r) q₂ = 0 := by
      have hcl_eq : cl = 1 - cr := by linarith
      dsimp only [q₂]; unfold orient2D; rw [hcl_eq]; ring
    have h_eq1 : orient2D (S l) (S r) (S h₂) = ν₁ * orient2D (S l) (S r) u := by
      have : orient2D (S l) (S r) (S h₂) =
          ν₁ * orient2D (S l) (S r) u + (1 - ν₁) * orient2D (S l) (S r) q₂ := by
        unfold orient2D; rw [hq2_ray.1, hq2_ray.2]; ring
      rw [this, hq0, mul_zero, add_zero]
    have h_eq2 : orient2D (S l) (S r) (S h₂) =
        (1 - s₂) * orient2D (S l) (S r) u + s₂ * orient2D (S l) (S r) zb := by
      have hα2_eq : α₂ = 1 - s₂ := by dsimp [s₂]; linarith
      unfold orient2D; rw [hzb_ray.1, hzb_ray.2, hα2_eq]; ring
    have hdiff : (ν₁ - (1 - s₂)) * orient2D (S l) (S r) u = s₂ * orient2D (S l) (S r) zb := by
      linarith
    have hrhs_nn : 0 ≤ s₂ * orient2D (S l) (S r) zb := mul_nonneg (le_of_lt hs2_pos) hlr_zb_nn
    by_contra hgt
    have hpos_diff : 0 < ν₁ - (1 - s₂) := by linarith
    have hneg_prod : (ν₁ - (1 - s₂)) * orient2D (S l) (S r) u < 0 :=
      mul_neg_of_pos_of_neg hpos_diff hlr_u_neg
    linarith
  let τ := s₂ / (1 - ν₁)
  have hτ_le1 : τ ≤ 1 := (div_le_one h1ν).mpr hs2_le
  have hq2_uzb : q₂.1 = (1 - τ) * u.1 + τ * zb.1 ∧ q₂.2 = (1 - τ) * u.2 + τ * zb.2 := by
    have hα2_eq : α₂ = 1 - s₂ := by dsimp [s₂]; linarith
    have hx : ν₁ * u.1 + (1 - ν₁) * q₂.1 = (1 - s₂) * u.1 + s₂ * zb.1 :=
      hq2_ray.1.symm.trans (by rw [← hα2_eq]; exact hzb_ray.1)
    have hy : ν₁ * u.2 + (1 - ν₁) * q₂.2 = (1 - s₂) * u.2 + s₂ * zb.2 :=
      hq2_ray.2.symm.trans (by rw [← hα2_eq]; exact hzb_ray.2)
    have h1ν_ne : 1 - ν₁ ≠ 0 := ne_of_gt h1ν
    dsimp only [τ]
    constructor <;> field_simp [h1ν_ne] <;> linarith
  have hq2_za_zb_nonpos : orient2D q₂ za zb ≤ 0 := by
    have hid : orient2D q₂ za zb = (1 - τ) * orient2D u za zb := by
      unfold orient2D; rw [hq2_uzb.1, hq2_uzb.2]; ring
    rw [hid]
    exact mul_nonpos_of_nonneg_of_nonpos (by linarith) (le_of_lt hu_za_zb_neg)
  -- Step 4: On the other hand, both orient2D (S r) za zb > 0 and orient2D (S l) za zb > 0!
  have h_bilin : ∀ v : ℝ × ℝ, orient2D v za zb =
      wa0 * wb0 * orient2D v (S (dc.p_idx (dIdx a))) (S (dc.p_idx (dIdx b))) +
      wa0 * wb1 * orient2D v (S (dc.p_idx (dIdx a))) (S (dc.p_idx (dIdx (b + 1)))) +
      wa1 * wb0 * orient2D v (S (dc.p_idx (dIdx (a + 1)))) (S (dc.p_idx (dIdx b))) +
      wa1 * wb1 * orient2D v (S (dc.p_idx (dIdx (a + 1)))) (S (dc.p_idx (dIdx (b + 1)))) := by
    intro v
    have ha_s : wa0 = 1 - wa1 := by linarith
    have hb_s : wb0 = 1 - wb1 := by linarith
    dsimp only [za, zb]
    rw [hi1_succ_eq, hi1_eq, hi2_succ_eq, hi2_eq]
    unfold orient2D; rw [ha_s, hb_s]; ring
  have hr_pair_nn : ∀ x y : ℕ, x ≤ y → y < dc.m + 3 →
      0 ≤ orient2D (S r) (S (dc.p_idx (dIdx x))) (S (dc.p_idx (dIdx y))) := by
    intro x y hxy hy
    rw [← hdIdx_0]
    by_cases hx0 : x = 0
    · subst hx0; exact le_of_eq (by unfold orient2D; ring)
    · by_cases heq : x = y
      · subst heq; exact le_of_eq (by unfold orient2D; ring)
      · exact le_of_lt (hccw_dIdx 0 x y (by omega) (by omega) hy)
  have hr_strict : 0 < orient2D (S r) (S (dc.p_idx (dIdx (a + 1)))) (S (dc.p_idx (dIdx (b + 1)))) := by
    rw [← hdIdx_0]
    exact hccw_dIdx 0 (a + 1) (b + 1) (by omega) (by omega) (by omega)
  have hr_pos : 0 < orient2D (S r) za zb := by
    rw [h_bilin (S r)]
    have t1 := mul_nonneg (le_of_lt (mul_pos hwa0 hwb0)) (hr_pair_nn a b (by omega) (by omega))
    have t2 := mul_nonneg (le_of_lt (mul_pos hwa0 hwb1)) (hr_pair_nn a (b + 1) (by omega) (by omega))
    have t3 := mul_nonneg (le_of_lt (mul_pos hwa1 hwb0)) (hr_pair_nn (a + 1) b (by omega) (by omega))
    have t4 := mul_pos (mul_pos hwa1 hwb1) hr_strict
    linarith
  have hl_pair_nn : ∀ x y : ℕ, x ≤ y → y ≤ dc.m + 2 →
      0 ≤ orient2D (S l) (S (dc.p_idx (dIdx x))) (S (dc.p_idx (dIdx y))) := by
    intro x y hxy hy
    rw [← hdIdx_last]
    by_cases hyl : y = dc.m + 2
    · subst hyl; exact le_of_eq (by unfold orient2D; ring)
    · by_cases heq : x = y
      · subst heq; exact le_of_eq (by unfold orient2D; ring)
      · have hpos := hccw_dIdx x y (dc.m + 2) (by omega) (by omega) (by omega)
        have : orient2D (S (dc.p_idx (dIdx (dc.m + 2)))) (S (dc.p_idx (dIdx x))) (S (dc.p_idx (dIdx y))) =
            orient2D (S (dc.p_idx (dIdx x))) (S (dc.p_idx (dIdx y))) (S (dc.p_idx (dIdx (dc.m + 2)))) := by
          unfold orient2D; ring
        linarith
  have hl_strict : 0 < orient2D (S l) (S (dc.p_idx (dIdx a))) (S (dc.p_idx (dIdx b))) := by
    rw [← hdIdx_last]
    have hpos := hccw_dIdx a b (dc.m + 2) hab hb_lt_m2 (by omega)
    have : orient2D (S (dc.p_idx (dIdx (dc.m + 2)))) (S (dc.p_idx (dIdx a))) (S (dc.p_idx (dIdx b))) =
        orient2D (S (dc.p_idx (dIdx a))) (S (dc.p_idx (dIdx b))) (S (dc.p_idx (dIdx (dc.m + 2)))) := by
      unfold orient2D; ring
    linarith
  have hl_pos : 0 < orient2D (S l) za zb := by
    rw [h_bilin (S l)]
    have t1 := mul_pos (mul_pos hwa0 hwb0) hl_strict
    have t2 := mul_nonneg (le_of_lt (mul_pos hwa0 hwb1)) (hl_pair_nn a (b + 1) (by omega) (by omega))
    have t3 := mul_nonneg (le_of_lt (mul_pos hwa1 hwb0)) (hl_pair_nn (a + 1) b (by omega) (by omega))
    have t4 := mul_nonneg (le_of_lt (mul_pos hwa1 hwb1)) (hl_pair_nn (a + 1) (b + 1) (by omega) (by omega))
    linarith
  have hq2_pos : 0 < orient2D q₂ za zb := by
    have hid : orient2D q₂ za zb =
        cl * orient2D (S l) za zb + cr * orient2D (S r) za zb := by
      have hcl_eq : cl = 1 - cr := by linarith
      dsimp only [q₂]; unfold orient2D; rw [hcl_eq]; ring
    rw [hid]
    exact add_pos (mul_pos hcl hl_pos) (mul_pos hcr hr_pos)
  linarith

end VCDim6

end
