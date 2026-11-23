import Mathlib
import RootTask.PolygonDefs
import RootTask.PolygonEnclosureCore
import RootTask.NewEnclosureLemmas
import RootTask.ChirotopeSoundness
import RootTask.CertifiedAndHalfPlaneSoundness
import RootTask.VCDimSixMasterBridge
import RootTask.VCDim6.CaseCertFormat
import RootTask.VCDim6.CoreTrieSoundness

open scoped Classical BigOperators
open Finset
open PolygonCore NewEnclosure ChirotopeSoundness CertifiedAndHalfPlaneSoundness
open VCDimSixMasterBridge VCDim6.FastTrieRUP

noncomputable section

namespace VCDim6

/-!
# Geometric Soundness of `CaseCertFormat` (`Tags 0..19`) and Master `FastTrieRUP` Refutation Bridge

Proves that for every canonical instance `ValidCanonicalInstance P S w spec` (`|S| = 7`) and
valid 7-bit witness mask list (`validMasksBool spec.masks = true`), if the pure-kernel checker
`checkCaseCert spec varTree justTree rupTree = true` succeeds, then `False` follows unconditionally!
-/

lemma nextMod_lt_seven {u n_d : ℕ} (hnd : n_d ≤ 7) :
    (if u + 1 < n_d then u + 1 else 0) < 7 := by
  split_ifs <;> omega

lemma hm_lt_seven {n_d h_sz l hi : ℕ} (htot : n_d + h_sz ≤ 7) (hl : l < n_d) (hhi : hi < h_sz) :
    (if hi == 0 then l else (n_d + hi) - 1) < 7 := by
  cases h0 : (hi == 0) <;> simp only [↓reduceIte, Bool.false_eq_true]
  · have : hi ≠ 0 := fun e => by rw [beq_iff_eq.mpr e] at h0; nomatch h0
    omega
  · omega

lemma hp_lt_seven {n_d h_sz l hi : ℕ} (htot : n_d + h_sz ≤ 7) (hhi : hi < h_sz) :
    (if hi + 1 == h_sz then (if l + 1 < n_d then l + 1 else 0) else (n_d + hi) + 1) < 7 := by
  cases h0 : (hi + 1 == h_sz) <;> simp only [↓reduceIte, Bool.false_eq_true]
  · have : hi + 1 ≠ h_sz := fun e => by rw [beq_iff_eq.mpr e] at h0; nomatch h0
    omega
  · split_ifs <;> omega

/-- Canonical geometric assumptions for a Stage-1 or Stage-2 case `spec : CaseSpec` on `Fin 7`. -/
structure ValidCanonicalInstance (P : Set (ℝ × ℝ)) (S : Fin 7 → ℝ × ℝ)
    (w : Finset (Fin 7) → ℝ × ℝ) (spec : CaseSpec) : Prop where
  hP : ShatteredSimplePolygon P S w
  h_nd_ge2 : 2 ≤ spec.n_d
  h_tot_le7 : spec.n_d + spec.h_sz ≤ 7
  h_bsz_ge3 : 3 ≤ spec.n_d + spec.h_sz
  hD_mem : ∀ x : Fin 7,
    x ∈ PolygonCore.hullVertices S \ PolygonCore.certifiedSet P S w ↔ x.val < spec.n_d
  hH_mem : ∀ x : Fin 7,
    x ∈ PolygonCore.certifiedSet P S w ↔ spec.n_d ≤ x.val ∧ x.val < spec.n_d + spec.h_sz
  h_cb : ∃ cb : PolygonCore.CyclicSubsetBoundary S (PolygonCore.hullVertices S),
    (buildBccw spec).length = cb.m + 3 ∧
    ∀ idx : Fin (cb.m + 3),
      listGetOpt (buildBccw spec) idx.val = some (cb.p_idx idx).val
  h_pocket : spec.h_sz > 0 → ∃ l : ℕ, ∃ hl : l < spec.n_d,
    spec.lr_l = some l ∧
    let r := if l + 1 < spec.n_d then l + 1 else 0
    let fl : Fin 7 := ⟨l, by have := h_tot_le7; omega⟩
    let fr : Fin 7 := ⟨r, nextMod_lt_seven (by have := h_tot_le7; omega)⟩
    (∀ hi (hhi : hi < spec.h_sz) (Tw : Finset (Fin 7)), {fl, fr} ⊆ Tw →
      inOpenTriBool (S ⟨spec.n_d + hi, by have := h_tot_le7; omega⟩) (w Tw) (S fl) (S fr) = true) ∧
    (spec.h_sz > 1 → ∀ hi (hhi : hi < spec.h_sz),
      let hm := if hi == 0 then l else (spec.n_d + hi) - 1
      let hp := if hi + 1 == spec.h_sz then r else (spec.n_d + hi) + 1
      let fhm : Fin 7 := ⟨hm, hm_lt_seven h_tot_le7 hl hhi⟩
      let fhp : Fin 7 := ⟨hp, hp_lt_seven h_tot_le7 hhi⟩
      fhm ≠ ⟨spec.n_d + hi, by have := h_tot_le7; omega⟩ ∧
      fhp ≠ ⟨spec.n_d + hi, by have := h_tot_le7; omega⟩ ∧
      fhm ≠ fhp ∧
      ∀ (Tw : Finset (Fin 7)), {fhm, fhp} ⊆ Tw →
        inOpenTriBool (S ⟨spec.n_d + hi, by have := h_tot_le7; omega⟩) (w Tw) (S fhm) (S fhp) = true) ∧
    (∀ hi (hhi : hi < spec.h_sz) (target : ℕ) (ht : target < 7),
      (((spec.n_d ≤ target ∧ target < spec.n_d + hi) ∨ target = l) →
        orientSign (PolygonCore.zWitness w ⟨spec.n_d + hi, by have := h_tot_le7; omega⟩)
          (S ⟨spec.n_d + hi, by have := h_tot_le7; omega⟩) (S ⟨target, ht⟩) = true) ∧
      (((spec.n_d + hi < target ∧ target < spec.n_d + spec.h_sz) ∨ target = r) →
        orientSign (PolygonCore.zWitness w ⟨spec.n_d + hi, by have := h_tot_le7; omega⟩)
          (S ⟨spec.n_d + hi, by have := h_tot_le7; omega⟩) (S ⟨target, ht⟩) = false))
  h_edges : 3 ≤ spec.n_d → ∀ (eIdx u_y : ℕ)
    (he_lt : eIdx < 7 - spec.n_d)
    (_hed : listGetOpt spec.edges eIdx = some (some u_y))
    (huy_lt : u_y < spec.n_d),
    let v_y := if u_y + 1 < spec.n_d then u_y + 1 else 0
    let fu : Fin 7 := ⟨u_y, by have := h_tot_le7; omega⟩
    let fv : Fin 7 := ⟨v_y, nextMod_lt_seven (by have := h_tot_le7; omega)⟩
    ∀ (Tw : Finset (Fin 7)), fu ∈ Tw → fv ∈ Tw →
      inOpenTriBool (S ⟨spec.n_d + eIdx, by have := h_tot_le7; omega⟩) (w Tw) (S fu) (S fv) = true

private lemma inOpenTriBool_of_side {s : Bool} {p a b c : ℝ × ℝ}
    (h : inOpenTriSideBool s p a b c = true) : inOpenTriBool p a b c = true := by
  unfold inOpenTriBool; cases s <;> simp [h]

private lemma oppSideBool_of_eq_not {s : Bool} {a b p q : ℝ × ℝ}
    (h1 : orientSign a b p = s) (h2 : orientSign a b q = !s) : oppSideBool a b p q = true := by
  unfold oppSideBool; rw [h1, h2]; cases s <;> rfl

private lemma ite_none_eq_some {α : Type} {c : Bool} {t : Option α} {v : α}
    (h : (if c then t else none) = some v) : c = true ∧ t = some v := by
  cases c <;> simp_all

private lemma matchOpt1 {α β : Type} {o : Option α} {f : α → Option β} {v : β}
    (h : (match o with | some x => f x | none => none) = some v) :
    ∃ x, o = some x ∧ f x = some v := by
  cases o with | none => nomatch h | some x => exact ⟨x, rfl, h⟩

private lemma matchOpt2 {α₁ α₂ β : Type} {o₁ : Option α₁} {o₂ : Option α₂}
    {f : α₁ → α₂ → Option β} {v : β}
    (h : (match o₁, o₂ with | some x₁, some x₂ => f x₁ x₂ | _, _ => none) = some v) :
    ∃ x₁ x₂, o₁ = some x₁ ∧ o₂ = some x₂ ∧ f x₁ x₂ = some v := by
  cases o₁ with | none => nomatch h | some x₁ =>
  cases o₂ with | none => nomatch h | some x₂ => exact ⟨x₁, x₂, rfl, rfl, h⟩

private lemma matchOpt3 {α₁ α₂ α₃ β : Type} {o₁ : Option α₁} {o₂ : Option α₂} {o₃ : Option α₃}
    {f : α₁ → α₂ → α₃ → Option β} {v : β}
    (h : (match o₁, o₂, o₃ with | some x₁, some x₂, some x₃ => f x₁ x₂ x₃ | _, _, _ => none) = some v) :
    ∃ x₁ x₂ x₃, o₁ = some x₁ ∧ o₂ = some x₂ ∧ o₃ = some x₃ ∧ f x₁ x₂ x₃ = some v := by
  cases o₁ with | none => nomatch h | some x₁ =>
  cases o₂ with | none => nomatch h | some x₂ =>
  cases o₃ with | none => nomatch h | some x₃ => exact ⟨x₁, x₂, x₃, rfl, rfl, rfl, h⟩

private lemma matchOpt4 {α₁ α₂ α₃ α₄ β : Type}
    {o₁ : Option α₁} {o₂ : Option α₂} {o₃ : Option α₃} {o₄ : Option α₄}
    {f : α₁ → α₂ → α₃ → α₄ → Option β} {v : β}
    (h : (match o₁, o₂, o₃, o₄ with
      | some x₁, some x₂, some x₃, some x₄ => f x₁ x₂ x₃ x₄ | _, _, _, _ => none) = some v) :
    ∃ x₁ x₂ x₃ x₄, o₁ = some x₁ ∧ o₂ = some x₂ ∧ o₃ = some x₃ ∧ o₄ = some x₄ ∧ f x₁ x₂ x₃ x₄ = some v := by
  cases o₁ with | none => nomatch h | some x₁ =>
  cases o₂ with | none => nomatch h | some x₂ =>
  cases o₃ with | none => nomatch h | some x₃ =>
  cases o₄ with | none => nomatch h | some x₄ => exact ⟨x₁, x₂, x₃, x₄, rfl, rfl, rfl, rfl, h⟩

private lemma matchPairOpt1 {α₁ α₂ β : Type*} {o : Option (α₁ × α₂)}
    {f : α₁ → α₂ → Option β} {v : β}
    (h : (match o with | none => none | some (x₁, x₂) => f x₁ x₂) = some v) :
    ∃ x₁ x₂, o = some (x₁, x₂) ∧ f x₁ x₂ = some v := by
  cases o with | none => nomatch h | some p => rcases p with ⟨x₁, x₂⟩; exact ⟨x₁, x₂, rfl, h⟩

private lemma matchTripleOpt1 {α₁ α₂ α₃ β : Type*} {o : Option (α₁ × α₂ × α₃)}
    {f : α₁ → α₂ → α₃ → Option β} {v : β}
    (h : (match o with | none => none | some (x₁, x₂, x₃) => f x₁ x₂ x₃) = some v) :
    ∃ x₁ x₂ x₃, o = some (x₁, x₂, x₃) ∧ f x₁ x₂ x₃ = some v := by
  cases o with
  | none => nomatch h
  | some p => rcases p with ⟨x₁, x₂, x₃⟩; exact ⟨x₁, x₂, x₃, rfl, h⟩

private lemma matchNats2 {β : Type*} {o : Option (List ℕ × ByteStream)}
    {f : ℕ → ℕ → ByteStream → Option β} {v : β}
    (h : (match o with | some ([x1, x2], r) => f x1 x2 r | _ => none) = some v) :
    ∃ x1 x2 r, f x1 x2 r = some v := by
  cases o with
  | none => nomatch h
  | some p =>
    rcases p with ⟨l, r⟩
    cases l with | nil => nomatch h | cons x1 l =>
    cases l with | nil => nomatch h | cons x2 l =>
    cases l with | nil => exact ⟨x1, x2, r, h⟩ | cons _ _ => nomatch h

private lemma matchNats3 {β : Type*} {o : Option (List ℕ × ByteStream)}
    {f : ℕ → ℕ → ℕ → ByteStream → Option β} {v : β}
    (h : (match o with | some ([x1, x2, x3], r) => f x1 x2 x3 r | _ => none) = some v) :
    ∃ x1 x2 x3 r, f x1 x2 x3 r = some v := by
  cases o with
  | none => nomatch h
  | some p =>
    rcases p with ⟨l, r⟩
    cases l with | nil => nomatch h | cons x1 l =>
    cases l with | nil => nomatch h | cons x2 l =>
    cases l with | nil => nomatch h | cons x3 l =>
    cases l with | nil => exact ⟨x1, x2, x3, r, h⟩ | cons _ _ => nomatch h

private lemma matchNats4 {β : Type*} {o : Option (List ℕ × ByteStream)}
    {f : ℕ → ℕ → ℕ → ℕ → ByteStream → Option β} {v : β}
    (h : (match o with | some ([x1, x2, x3, x4], r) => f x1 x2 x3 x4 r | _ => none) = some v) :
    ∃ x1 x2 x3 x4 r, f x1 x2 x3 x4 r = some v := by
  cases o with
  | none => nomatch h
  | some p =>
    rcases p with ⟨l, r⟩
    cases l with | nil => nomatch h | cons x1 l =>
    cases l with | nil => nomatch h | cons x2 l =>
    cases l with | nil => nomatch h | cons x3 l =>
    cases l with | nil => nomatch h | cons x4 l =>
    cases l with | nil => exact ⟨x1, x2, x3, x4, r, h⟩ | cons _ _ => nomatch h

private lemma matchNats5 {β : Type*} {o : Option (List ℕ × ByteStream)}
    {f : ℕ → ℕ → ℕ → ℕ → ℕ → ByteStream → Option β} {v : β}
    (h : (match o with | some ([x1, x2, x3, x4, x5], r) => f x1 x2 x3 x4 x5 r | _ => none) = some v) :
    ∃ x1 x2 x3 x4 x5 r, f x1 x2 x3 x4 x5 r = some v := by
  cases o with
  | none => nomatch h
  | some p =>
    rcases p with ⟨l, r⟩
    cases l with | nil => nomatch h | cons x1 l =>
    cases l with | nil => nomatch h | cons x2 l =>
    cases l with | nil => nomatch h | cons x3 l =>
    cases l with | nil => nomatch h | cons x4 l =>
    cases l with | nil => nomatch h | cons x5 l =>
    cases l with | nil => exact ⟨x1, x2, x3, x4, x5, r, h⟩ | cons _ _ => nomatch h

private lemma matchNats6 {β : Type*} {o : Option (List ℕ × ByteStream)}
    {f : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ByteStream → Option β} {v : β}
    (h : (match o with | some ([x1, x2, x3, x4, x5, x6], r) => f x1 x2 x3 x4 x5 x6 r | _ => none) = some v) :
    ∃ x1 x2 x3 x4 x5 x6 r, f x1 x2 x3 x4 x5 x6 r = some v := by
  cases o with
  | none => nomatch h
  | some p =>
    rcases p with ⟨l, r⟩
    cases l with | nil => nomatch h | cons x1 l =>
    cases l with | nil => nomatch h | cons x2 l =>
    cases l with | nil => nomatch h | cons x3 l =>
    cases l with | nil => nomatch h | cons x4 l =>
    cases l with | nil => nomatch h | cons x5 l =>
    cases l with | nil => nomatch h | cons x6 l =>
    cases l with | nil => exact ⟨x1, x2, x3, x4, x5, x6, r, h⟩ | cons _ _ => nomatch h

private lemma matchNats7 {β : Type*} {o : Option (List ℕ × ByteStream)}
    {f : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ByteStream → Option β} {v : β}
    (h : (match o with | some ([x1, x2, x3, x4, x5, x6, x7], r) => f x1 x2 x3 x4 x5 x6 x7 r | _ => none) = some v) :
    ∃ x1 x2 x3 x4 x5 x6 x7 r, f x1 x2 x3 x4 x5 x6 x7 r = some v := by
  cases o with
  | none => nomatch h
  | some p =>
    rcases p with ⟨l, r⟩
    cases l with | nil => nomatch h | cons x1 l =>
    cases l with | nil => nomatch h | cons x2 l =>
    cases l with | nil => nomatch h | cons x3 l =>
    cases l with | nil => nomatch h | cons x4 l =>
    cases l with | nil => nomatch h | cons x5 l =>
    cases l with | nil => nomatch h | cons x6 l =>
    cases l with | nil => nomatch h | cons x7 l =>
    cases l with | nil => exact ⟨x1, x2, x3, x4, x5, x6, x7, r, h⟩ | cons _ _ => nomatch h

private lemma matchNats8 {β : Type*} {o : Option (List ℕ × ByteStream)}
    {f : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ByteStream → Option β} {v : β}
    (h : (match o with | some ([x1, x2, x3, x4, x5, x6, x7, x8], r) => f x1 x2 x3 x4 x5 x6 x7 x8 r | _ => none) = some v) :
    ∃ x1 x2 x3 x4 x5 x6 x7 x8 r, f x1 x2 x3 x4 x5 x6 x7 x8 r = some v := by
  cases o with
  | none => nomatch h
  | some p =>
    rcases p with ⟨l, r⟩
    cases l with | nil => nomatch h | cons x1 l =>
    cases l with | nil => nomatch h | cons x2 l =>
    cases l with | nil => nomatch h | cons x3 l =>
    cases l with | nil => nomatch h | cons x4 l =>
    cases l with | nil => nomatch h | cons x5 l =>
    cases l with | nil => nomatch h | cons x6 l =>
    cases l with | nil => nomatch h | cons x7 l =>
    cases l with | nil => nomatch h | cons x8 l =>
    cases l with | nil => exact ⟨x1, x2, x3, x4, x5, x6, x7, x8, r, h⟩ | cons _ _ => nomatch h

private lemma matchNats10 {β : Type*} {o : Option (List ℕ × ByteStream)}
    {f : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ByteStream → Option β} {v : β}
    (h : (match o with
      | some ([x1, x2, x3, x4, x5, x6, x7, x8, x9, x10], r) =>
        f x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 r
      | _ => none) = some v) :
    ∃ x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 r, f x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 r = some v := by
  cases o with
  | none => nomatch h
  | some p =>
    rcases p with ⟨l, r⟩
    cases l with | nil => nomatch h | cons x1 l =>
    cases l with | nil => nomatch h | cons x2 l =>
    cases l with | nil => nomatch h | cons x3 l =>
    cases l with | nil => nomatch h | cons x4 l =>
    cases l with | nil => nomatch h | cons x5 l =>
    cases l with | nil => nomatch h | cons x6 l =>
    cases l with | nil => nomatch h | cons x7 l =>
    cases l with | nil => nomatch h | cons x8 l =>
    cases l with | nil => nomatch h | cons x9 l =>
    cases l with | nil => nomatch h | cons x10 l =>
    cases l with | nil => exact ⟨x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, r, h⟩ | cons _ _ => nomatch h

private lemma matchNats13 {β : Type*} {o : Option (List ℕ × ByteStream)}
    {f : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ByteStream → Option β} {v : β}
    (h : (match o with
      | some ([x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13], r) =>
        f x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 r
      | _ => none) = some v) :
    ∃ x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 r,
      f x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 r = some v := by
  cases o with
  | none => nomatch h
  | some p =>
    rcases p with ⟨l, r⟩
    cases l with | nil => nomatch h | cons x1 l =>
    cases l with | nil => nomatch h | cons x2 l =>
    cases l with | nil => nomatch h | cons x3 l =>
    cases l with | nil => nomatch h | cons x4 l =>
    cases l with | nil => nomatch h | cons x5 l =>
    cases l with | nil => nomatch h | cons x6 l =>
    cases l with | nil => nomatch h | cons x7 l =>
    cases l with | nil => nomatch h | cons x8 l =>
    cases l with | nil => nomatch h | cons x9 l =>
    cases l with | nil => nomatch h | cons x10 l =>
    cases l with | nil => nomatch h | cons x11 l =>
    cases l with | nil => nomatch h | cons x12 l =>
    cases l with | nil => nomatch h | cons x13 l =>
    cases l with
    | nil => exact ⟨x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, r, h⟩
    | cons _ _ => nomatch h

private lemma listGetOpt_lt_len {α : Type*} :
    ∀ (xs : List α) (i : ℕ) {v : α}, listGetOpt xs i = some v → i < xs.length
  | [], _, _, h => nomatch h
  | _ :: _, 0, _, _ => by simp
  | _ :: xs, k + 1, _, h => by
    have hk := listGetOpt_lt_len xs k h
    simp; omega

private lemma mem_hull_iff_of_valid {P : Set (ℝ × ℝ)} {S : Fin 7 → ℝ × ℝ}
    {w : Finset (Fin 7) → ℝ × ℝ} {spec : CaseSpec}
    (hV : ValidCanonicalInstance P S w spec) (x : Fin 7) :
    x ∈ PolygonCore.hullVertices S ↔ x.val < spec.n_d + spec.h_sz := by
  have hH_sub : PolygonCore.certifiedSet P S w ⊆ PolygonCore.hullVertices S :=
    Finset.filter_subset _ _
  constructor
  · intro hxB
    by_cases hxH : x ∈ PolygonCore.certifiedSet P S w
    · exact ((hV.hH_mem x).mp hxH).2
    · have hxD : x ∈ PolygonCore.hullVertices S \ PolygonCore.certifiedSet P S w :=
        Finset.mem_sdiff.mpr ⟨hxB, hxH⟩
      have := (hV.hD_mem x).mp hxD
      omega
  · intro hlt
    by_cases hnd : x.val < spec.n_d
    · exact (Finset.mem_sdiff.mp ((hV.hD_mem x).mpr hnd)).1
    · exact hH_sub ((hV.hH_mem x).mpr ⟨by omega, hlt⟩)

private lemma mem_interior_iff_of_valid {P : Set (ℝ × ℝ)} {S : Fin 7 → ℝ × ℝ}
    {w : Finset (Fin 7) → ℝ × ℝ} {spec : CaseSpec}
    (hV : ValidCanonicalInstance P S w spec) (x : Fin 7) :
    x ∈ PolygonCore.interiorPoints S ↔ spec.n_d + spec.h_sz ≤ x.val := by
  simp only [PolygonCore.interiorPoints, Finset.mem_sdiff, Finset.mem_univ, true_and,
    mem_hull_iff_of_valid hV, not_lt]

private lemma pointSeq_S_eq {k : ℕ} (S : Fin 7 → ℝ × ℝ) (w : Finset (Fin 7) → ℝ × ℝ)
    (W₀ : Fin k ↪ Finset (Fin 7)) {u : ℕ} (hu7 : u < 7) (hu : u < 7 + k) :
    pointSeq S w W₀ ⟨u, hu⟩ = S ⟨u, hu7⟩ := by
  have heq : (⟨u, hu⟩ : Fin (7 + k)) = Fin.castAdd k ⟨u, hu7⟩ := Fin.ext rfl
  unfold pointSeq; rw [heq]; exact Fin.addCases_left _

private lemma pointSeq_w_eq {k : ℕ} (S : Fin 7 → ℝ × ℝ) (w : Finset (Fin 7) → ℝ × ℝ)
    (W₀ : Fin k ↪ Finset (Fin 7)) {wIdx : ℕ} (hw : wIdx < k) :
    pointSeq S w W₀ ⟨7 + wIdx, by omega⟩ = w (W₀ ⟨wIdx, hw⟩) := by
  have heq : (⟨7 + wIdx, by omega⟩ : Fin (7 + k)) = Fin.natAdd 7 ⟨wIdx, hw⟩ :=
    Fin.ext (by simp [Fin.natAdd])
  unfold pointSeq; rw [heq]; exact Fin.addCases_right _

/-- Helper unpacking `optSequence [o1, ..., ok] = some cl` and `evalClause val cl = false`. -/
private lemma optSeq2_false {val : PIdx → Bool} {o1 o2 : Option Lit} {cl : Clause}
    (h : optSequence [o1, o2] = some cl) (hf : evalClause val cl = false) :
    ∃ l1 l2, o1 = some l1 ∧ o2 = some l2 ∧ evalLit val l1 = false ∧ evalLit val l2 = false := by
  cases o1 with | none => nomatch h | some l1 =>
  cases o2 with | none => nomatch h | some l2 =>
  injection h with heq; subst heq
  obtain ⟨f1, r1⟩ := evalClause_cons_false hf
  obtain ⟨f2, _⟩ := evalClause_cons_false r1
  exact ⟨l1, l2, rfl, rfl, f1, f2⟩

private lemma optSeq3_false {val : PIdx → Bool} {o1 o2 o3 : Option Lit} {cl : Clause}
    (h : optSequence [o1, o2, o3] = some cl) (hf : evalClause val cl = false) :
    ∃ l1 l2 l3, o1 = some l1 ∧ o2 = some l2 ∧ o3 = some l3 ∧
      evalLit val l1 = false ∧ evalLit val l2 = false ∧ evalLit val l3 = false := by
  cases o1 with | none => nomatch h | some l1 =>
  cases o2 with | none => nomatch h | some l2 =>
  cases o3 with | none => nomatch h | some l3 =>
  injection h with heq; subst heq
  obtain ⟨f1, r1⟩ := evalClause_cons_false hf
  obtain ⟨f2, r2⟩ := evalClause_cons_false r1
  obtain ⟨f3, _⟩ := evalClause_cons_false r2
  exact ⟨l1, l2, l3, rfl, rfl, rfl, f1, f2, f3⟩

private lemma optSeq4_false {val : PIdx → Bool} {o1 o2 o3 o4 : Option Lit} {cl : Clause}
    (h : optSequence [o1, o2, o3, o4] = some cl) (hf : evalClause val cl = false) :
    ∃ l1 l2 l3 l4, o1 = some l1 ∧ o2 = some l2 ∧ o3 = some l3 ∧ o4 = some l4 ∧
      evalLit val l1 = false ∧ evalLit val l2 = false ∧
      evalLit val l3 = false ∧ evalLit val l4 = false := by
  cases o1 with | none => nomatch h | some l1 =>
  cases o2 with | none => nomatch h | some l2 =>
  cases o3 with | none => nomatch h | some l3 =>
  cases o4 with | none => nomatch h | some l4 =>
  injection h with heq; subst heq
  obtain ⟨f1, r1⟩ := evalClause_cons_false hf
  obtain ⟨f2, r2⟩ := evalClause_cons_false r1
  obtain ⟨f3, r3⟩ := evalClause_cons_false r2
  obtain ⟨f4, _⟩ := evalClause_cons_false r3
  exact ⟨l1, l2, l3, l4, rfl, rfl, rfl, rfl, f1, f2, f3, f4⟩

private lemma optSeq6_false {val : PIdx → Bool} {o1 o2 o3 o4 o5 o6 : Option Lit} {cl : Clause}
    (h : optSequence [o1, o2, o3, o4, o5, o6] = some cl) (hf : evalClause val cl = false) :
    ∃ l1 l2 l3 l4 l5 l6,
      o1 = some l1 ∧ o2 = some l2 ∧ o3 = some l3 ∧
      o4 = some l4 ∧ o5 = some l5 ∧ o6 = some l6 ∧
      evalLit val l1 = false ∧ evalLit val l2 = false ∧ evalLit val l3 = false ∧
      evalLit val l4 = false ∧ evalLit val l5 = false ∧ evalLit val l6 = false := by
  cases o1 with | none => nomatch h | some l1 =>
  cases o2 with | none => nomatch h | some l2 =>
  cases o3 with | none => nomatch h | some l3 =>
  cases o4 with | none => nomatch h | some l4 =>
  cases o5 with | none => nomatch h | some l5 =>
  cases o6 with | none => nomatch h | some l6 =>
  injection h with heq; subst heq
  obtain ⟨f1, r1⟩ := evalClause_cons_false hf; obtain ⟨f2, r2⟩ := evalClause_cons_false r1
  obtain ⟨f3, r3⟩ := evalClause_cons_false r2; obtain ⟨f4, r4⟩ := evalClause_cons_false r3
  obtain ⟨f5, r5⟩ := evalClause_cons_false r4; obtain ⟨f6, _⟩ := evalClause_cons_false r5
  exact ⟨l1, l2, l3, l4, l5, l6, rfl, rfl, rfl, rfl, rfl, rfl, f1, f2, f3, f4, f5, f6⟩

private lemma optSeq7_false {val : PIdx → Bool} {o1 o2 o3 o4 o5 o6 o7 : Option Lit} {cl : Clause}
    (h : optSequence [o1, o2, o3, o4, o5, o6, o7] = some cl) (hf : evalClause val cl = false) :
    ∃ l1 l2 l3 l4 l5 l6 l7,
      o1 = some l1 ∧ o2 = some l2 ∧ o3 = some l3 ∧ o4 = some l4 ∧
      o5 = some l5 ∧ o6 = some l6 ∧ o7 = some l7 ∧
      evalLit val l1 = false ∧ evalLit val l2 = false ∧ evalLit val l3 = false ∧
      evalLit val l4 = false ∧ evalLit val l5 = false ∧ evalLit val l6 = false ∧
      evalLit val l7 = false := by
  cases o1 with | none => nomatch h | some l1 =>
  cases o2 with | none => nomatch h | some l2 =>
  cases o3 with | none => nomatch h | some l3 =>
  cases o4 with | none => nomatch h | some l4 =>
  cases o5 with | none => nomatch h | some l5 =>
  cases o6 with | none => nomatch h | some l6 =>
  cases o7 with | none => nomatch h | some l7 =>
  injection h with heq; subst heq
  obtain ⟨f1, r1⟩ := evalClause_cons_false hf; obtain ⟨f2, r2⟩ := evalClause_cons_false r1
  obtain ⟨f3, r3⟩ := evalClause_cons_false r2; obtain ⟨f4, r4⟩ := evalClause_cons_false r3
  obtain ⟨f5, r5⟩ := evalClause_cons_false r4; obtain ⟨f6, r6⟩ := evalClause_cons_false r5
  obtain ⟨f7, _⟩ := evalClause_cons_false r6
  exact ⟨l1, l2, l3, l4, l5, l6, l7, rfl, rfl, rfl, rfl, rfl, rfl, rfl, f1, f2, f3, f4, f5, f6, f7⟩

private lemma optSeq8_false {val : PIdx → Bool} {o1 o2 o3 o4 o5 o6 o7 o8 : Option Lit} {cl : Clause}
    (h : optSequence [o1, o2, o3, o4, o5, o6, o7, o8] = some cl) (hf : evalClause val cl = false) :
    ∃ l1 l2 l3 l4 l5 l6 l7 l8,
      o1 = some l1 ∧ o2 = some l2 ∧ o3 = some l3 ∧ o4 = some l4 ∧
      o5 = some l5 ∧ o6 = some l6 ∧ o7 = some l7 ∧ o8 = some l8 ∧
      evalLit val l1 = false ∧ evalLit val l2 = false ∧ evalLit val l3 = false ∧
      evalLit val l4 = false ∧ evalLit val l5 = false ∧ evalLit val l6 = false ∧
      evalLit val l7 = false ∧ evalLit val l8 = false := by
  cases o1 with | none => nomatch h | some l1 =>
  cases o2 with | none => nomatch h | some l2 =>
  cases o3 with | none => nomatch h | some l3 =>
  cases o4 with | none => nomatch h | some l4 =>
  cases o5 with | none => nomatch h | some l5 =>
  cases o6 with | none => nomatch h | some l6 =>
  cases o7 with | none => nomatch h | some l7 =>
  cases o8 with | none => nomatch h | some l8 =>
  injection h with heq; subst heq
  obtain ⟨f1, r1⟩ := evalClause_cons_false hf; obtain ⟨f2, r2⟩ := evalClause_cons_false r1
  obtain ⟨f3, r3⟩ := evalClause_cons_false r2; obtain ⟨f4, r4⟩ := evalClause_cons_false r3
  obtain ⟨f5, r5⟩ := evalClause_cons_false r4; obtain ⟨f6, r6⟩ := evalClause_cons_false r5
  obtain ⟨f7, r7⟩ := evalClause_cons_false r6; obtain ⟨f8, _⟩ := evalClause_cons_false r7
  exact ⟨l1, l2, l3, l4, l5, l6, l7, l8, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    f1, f2, f3, f4, f5, f6, f7, f8⟩

private lemma sound_tag_11 {P : Set (ℝ × ℝ)} {S : Fin 7 → ℝ × ℝ} {w : Finset (Fin 7) → ℝ × ℝ}
    {ctx : CertCtx}
    (hP : ShatteredSimplePolygon P S w)
    (hM : ValidMasks ctx.spec.masks)
    (hm_eq : ctx.maskTrie = buildMaskTrieAux .xH ctx.spec.masks .leaf)
    {X' : Fin ctx.n_pts → ℝ × ℝ} (hX' : NoThreeCollinear X')
    (hS_pt : ∀ {u : ℕ} (hu7 : u < 7) (hu : u < ctx.n_pts), X' ⟨u, hu⟩ = S ⟨u, hu7⟩)
    (hw_pt : ∀ {wi : ℕ} (hwi : wi < ctx.spec.masks.length) (hu : 7 + wi < ctx.n_pts),
      X' ⟨7 + wi, hu⟩ = w ((specWitnessEmb hM) ⟨wi, hwi⟩))
    {val : PIdx → Bool}
    (hval : ∀ {i j k : ℕ} (_hij : i < j) (_hjk : j < k) (hk : k < ctx.n_pts) {v : PIdx},
      ctx.tripleTrie.get3 (ptKey i) (ptKey j) (ptKey k) = some v →
      val v = orientSign (X' ⟨i, by omega⟩) (X' ⟨j, by omega⟩) (X' ⟨k, hk⟩))
    {cs1 rest : ByteStream} {cl : Clause}
    (hev : evalClause val cl = false)
    (hdec : (match bsReadNats 13 [] cs1 with
      | some ([wv, wq, a, p, c, sigNat, saNat, ivKind, iv1, iv2, conclKind, wx, wy], rest) =>
        match getMask ctx wv, getMask ctx wq with
        | some mv, some mq =>
          if a < 7 && p < 7 && c < 7 && a != p && p != c && a != c &&
             seesBit mv p && !seesBit mv a && !seesBit mv c &&
             seesBit mq a && seesBit mq p && seesBit mq c then
            let sig := sigNat == 1
            let sa := saNat == 1
            let v := 7 + wv
            let q := 7 + wq
            let baseOpt := optSequence [
              litForb ctx sig v q p, litForb ctx sig v q a, litForb ctx sig v q c,
              litForb ctx sig v a p, litForb ctx sig v p c,
              litForb ctx sa a c v, litForb ctx (!sa) a c p
            ]
            let ivOpt : Option (List Lit) :=
              if ivKind == 0 then
                if iv1 < 7 && seesBit mv iv1 && seesBit mq iv1 then
                  optSequence [litForb ctx sig v q iv1, litForb ctx sig v iv1 a]
                else none
              else if ivKind == 1 then
                let s1 := iv1
                let s2 := iv2 / 2
                let ss := (iv2 % 2) == 1
                if s1 < 7 && s2 < 7 && s1 != s2 &&
                   seesBit mv s1 && seesBit mq s1 && seesBit mv s2 && seesBit mq s2 then
                  optSequence [litForb ctx ss v q s1, litForb ctx (!ss) v q s2]
                else none
              else none
            let conclOpt : Option (List Lit) :=
              if conclKind == 0 then
                match getMask ctx wx with
                | some mx =>
                  if seesBit mx a && seesBit mx c then
                    optSequence [litSign ctx (!sig) v a (7 + wx)]
                  else none
                | none => none
              else if conclKind == 1 then
                match getMask ctx wx with
                | some mx =>
                  if seesBit mx a && seesBit mx c then
                    optSequence [litSign ctx (!sig) v p (7 + wx)]
                  else none
                | none => none
              else if conclKind == 2 then
                match getMask ctx wx with
                | some mx =>
                  if seesBit mx a && seesBit mx c && seesBit mx p then
                    optSequence [litSign ctx sig p (7 + wx) a]
                  else none
                | none => none
              else if conclKind == 3 then
                match getMask ctx wx, getMask ctx wy with
                | some mx, some my =>
                  if seesBit mx a && seesBit mx c && seesBit mx p &&
                     seesBit my a && seesBit my c && !seesBit my p then
                    optSequence [litSign ctx sig p (7 + wx) (7 + wy)]
                  else none
                | _, _ => none
              else none
            match baseOpt, ivOpt, conclOpt with
            | some bL, some iL, some cL => some (some (bL ++ iL ++ cL), rest)
            | _, _, _ => none
          else none
        | _, _ => none
      | _ => none) = some (some cl, rest)) : False := by
  let W₀ := specWitnessEmb hM
  obtain ⟨wv, wq, a, p, c, sigNat, saNat, ivKind, iv1, iv2, conclKind, wx, wy, _, hdec⟩ := matchNats13 hdec
  cases hmv : getMask ctx wv with | none => rw [hmv] at hdec; nomatch hdec | some mv =>
  cases hmq : getMask ctx wq with | none => rw [hmv, hmq] at hdec; nomatch hdec | some mq =>
  rw [hmv, hmq] at hdec; dsimp only at hdec
  obtain ⟨hc, hdec⟩ := ite_none_eq_some hdec
  simp only [Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne, decide_eq_true_eq] at hc
  rcases hc with ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨ha7, hp7⟩, hc7⟩, _⟩, _⟩, _⟩, svp⟩, sva_n⟩, svc_n⟩, sqa⟩, sqp⟩, sqc⟩
  revert hdec
  generalize hbo_g : optSequence [
    litForb ctx (sigNat == 1) (7 + wv) (7 + wq) p, litForb ctx (sigNat == 1) (7 + wv) (7 + wq) a,
    litForb ctx (sigNat == 1) (7 + wv) (7 + wq) c, litForb ctx (sigNat == 1) (7 + wv) a p,
    litForb ctx (sigNat == 1) (7 + wv) p c,
    litForb ctx (saNat == 1) a c (7 + wv), litForb ctx (!(saNat == 1)) a c p
  ] = baseOpt
  generalize hio_g : (if (ivKind == 0) = true then _ else _) = ivOpt
  generalize hco_g : (if (conclKind == 0) = true then _ else _) = conclOpt
  intro hdec
  cases baseOpt with | none => nomatch hdec | some bL =>
  cases ivOpt with | none => nomatch hdec | some iL =>
  cases conclOpt with | none => nomatch hdec | some cL =>
  have hbo := hbo_g; have hio := hio_g; have hco := hco_g
  injection hdec with hp_; injection (Prod.mk.inj hp_).1 with hcl; subst hcl
  obtain ⟨hwv_lt, hmv_v⟩ := getMask_sound hM hm_eq hmv
  obtain ⟨hwq_lt, hmq_v⟩ := getMask_sound hM hm_eq hmq
  obtain ⟨fbiL, fcL⟩ := evalClause_append_false hev
  obtain ⟨fbL, fiL⟩ := evalClause_append_false fbiL
  obtain ⟨_, _, _, _, _, _, _, o1, o2, o3, o4, o5, o6, o7, f1, f2, f3, f4, f5, f6, f7⟩ := optSeq7_false hbo fbL
  obtain ⟨pv, pq, pp, e_vqp⟩ := litForb_eval_false hX' hval o1 f1
  obtain ⟨_, _, pa, e_vqa⟩ := litForb_eval_false hX' hval o2 f2
  obtain ⟨_, _, pc, e_vqc⟩ := litForb_eval_false hX' hval o3 f3
  obtain ⟨_, _, _, e_vap⟩ := litForb_eval_false hX' hval o4 f4
  obtain ⟨_, _, _, e_vpc⟩ := litForb_eval_false hX' hval o5 f5
  obtain ⟨_, _, _, e_acv⟩ := litForb_eval_false hX' hval o6 f6
  obtain ⟨_, _, _, e_acp⟩ := litForb_eval_false hX' hval o7 f7
  rw [hw_pt hwv_lt pv, hw_pt hwq_lt pq, hS_pt hp7 pp] at e_vqp
  rw [hw_pt hwv_lt pv, hw_pt hwq_lt pq, hS_pt ha7 pa] at e_vqa
  rw [hw_pt hwv_lt pv, hw_pt hwq_lt pq, hS_pt hc7 pc] at e_vqc
  rw [hw_pt hwv_lt pv, hS_pt ha7 pa, hS_pt hp7 pp] at e_vap
  rw [hw_pt hwv_lt pv, hS_pt hp7 pp, hS_pt hc7 pc] at e_vpc
  rw [hS_pt ha7 pa, hS_pt hc7 pc, hw_pt hwv_lt pv] at e_acv
  rw [hS_pt ha7 pa, hS_pt hc7 pc, hS_pt hp7 pp] at e_acp
  have hiv : Sees P (w (W₀ ⟨wv, hwv_lt⟩)) (w (W₀ ⟨wq, hwq_lt⟩)) ∨
      (∃ s₁ s₂ : Fin 7, s₁ ∈ W₀ ⟨wv, hwv_lt⟩ ∧ s₁ ∈ W₀ ⟨wq, hwq_lt⟩ ∧
        s₂ ∈ W₀ ⟨wv, hwv_lt⟩ ∧ s₂ ∈ W₀ ⟨wq, hwq_lt⟩ ∧
        oppSideBool (w (W₀ ⟨wv, hwv_lt⟩)) (w (W₀ ⟨wq, hwq_lt⟩)) (S s₁) (S s₂) = true) ∨
      (∃ ie : Fin 7, ie ∈ W₀ ⟨wv, hwv_lt⟩ ∧ ie ∈ W₀ ⟨wq, hwq_lt⟩ ∧
        orientSign (w (W₀ ⟨wv, hwv_lt⟩)) (w (W₀ ⟨wq, hwq_lt⟩)) (S ie) =
          orientSign (w (W₀ ⟨wv, hwv_lt⟩)) (w (W₀ ⟨wq, hwq_lt⟩)) (S ⟨p, hp7⟩) ∧
        orientSign (w (W₀ ⟨wv, hwv_lt⟩)) (S ie) (S ⟨a, ha7⟩) =
          orientSign (w (W₀ ⟨wv, hwv_lt⟩)) (w (W₀ ⟨wq, hwq_lt⟩)) (S ⟨p, hp7⟩)) := by
    by_cases hik0 : (ivKind == 0) = true
    · rw [if_pos hik0] at hio
      obtain ⟨hivc, hio⟩ := ite_none_eq_some hio
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hivc
      obtain ⟨_, _, oi1, oi2, fi1, fi2⟩ := optSeq2_false hio fiL
      obtain ⟨_, _, piv1, ei1⟩ := litForb_eval_false hX' hval oi1 fi1
      obtain ⟨_, _, _, ei2⟩ := litForb_eval_false hX' hval oi2 fi2
      rw [hw_pt hwv_lt pv, hw_pt hwq_lt pq, hS_pt hivc.1.1 piv1] at ei1
      rw [hw_pt hwv_lt pv, hS_pt hivc.1.1 piv1, hS_pt ha7 pa] at ei2
      exact Or.inr (Or.inr ⟨⟨iv1, hivc.1.1⟩,
        by simp [W₀, specWitnessEmb, hmv_v, hivc.1.2],
        by simp [W₀, specWitnessEmb, hmq_v, hivc.2],
        ei1.trans e_vqp.symm, ei2.trans e_vqp.symm⟩)
    · rw [if_neg hik0] at hio
      by_cases hik1 : (ivKind == 1) = true
      · rw [if_pos hik1] at hio
        obtain ⟨hivc, hio⟩ := ite_none_eq_some hio
        simp only [Bool.and_eq_true, bne_iff_ne, decide_eq_true_eq] at hivc
        obtain ⟨_, _, oi1, oi2, fi1, fi2⟩ := optSeq2_false hio fiL
        obtain ⟨_, _, ps1, ei1⟩ := litForb_eval_false hX' hval oi1 fi1
        obtain ⟨_, _, ps2, ei2⟩ := litForb_eval_false hX' hval oi2 fi2
        rw [hw_pt hwv_lt pv, hw_pt hwq_lt pq, hS_pt hivc.1.1.1.1.1.1 ps1] at ei1
        rw [hw_pt hwv_lt pv, hw_pt hwq_lt pq, hS_pt hivc.1.1.1.1.1.2 ps2] at ei2
        refine Or.inr (Or.inl ⟨⟨iv1, hivc.1.1.1.1.1.1⟩, ⟨iv2 / 2, hivc.1.1.1.1.1.2⟩,
          by simp [W₀, specWitnessEmb, hmv_v, hivc.1.1.1.2],
          by simp [W₀, specWitnessEmb, hmq_v, hivc.1.1.2],
          by simp [W₀, specWitnessEmb, hmv_v, hivc.1.2],
          by simp [W₀, specWitnessEmb, hmq_v, hivc.2], ?_⟩)
        unfold oppSideBool; rw [ei1, ei2]; cases ((iv2 % 2) == 1) <;> rfl
      · rw [if_neg hik1] at hio; nomatch hio
  have hcfg : HalfPlaneChirotopeConfig P S w (W₀ ⟨wv, hwv_lt⟩) (W₀ ⟨wq, hwq_lt⟩)
      ⟨a, ha7⟩ ⟨p, hp7⟩ ⟨c, hc7⟩ :=
    { hp_v := by simp [W₀, specWitnessEmb, hmv_v, svp]
      ha_not_v := by simp [W₀, specWitnessEmb, hmv_v, sva_n]
      hc_not_v := by simp [W₀, specWitnessEmb, hmv_v, svc_n]
      ha_q := by simp [W₀, specWitnessEmb, hmq_v, sqa]
      hp_q := by simp [W₀, specWitnessEmb, hmq_v, sqp]
      hc_q := by simp [W₀, specWitnessEmb, hmq_v, sqc]
      h_vqa := e_vqa.trans e_vqp.symm
      h_vqc := e_vqc.trans e_vqp.symm
      h_vap := e_vap.trans e_vqp.symm
      h_vpc := e_vpc.trans e_vqp.symm
      h_cross_ac := by unfold oppSideBool; rw [e_acv, e_acp]; cases (saNat == 1) <;> rfl
      h_cond_iv := hiv }
  obtain ⟨hc9_a, hc9_b, hc9_c, hc9_s⟩ := half_plane_chirotope_clauses_C9 hP hcfg
  by_cases hck0 : (conclKind == 0) = true
  · rw [if_pos hck0] at hco
    cases hmx : getMask ctx wx with
    | none => rw [hmx] at hco; nomatch hco
    | some mx =>
    rw [hmx] at hco; dsimp only at hco
    obtain ⟨hxc, hco⟩ := ite_none_eq_some hco
    simp only [Bool.and_eq_true] at hxc
    cases hls : litSign ctx (!(sigNat == 1)) (7 + wv) a (7 + wx) with
    | none => rw [hls] at hco; nomatch hco
    | some lc =>
      rw [hls] at hco; injection hco with he; subst he
      obtain ⟨flc, _⟩ := evalClause_cons_false fcL
      obtain ⟨hwx_lt, hmx_v⟩ := getMask_sound hM hm_eq hmx
      obtain ⟨_, _, pwx, _, _, _, _, hf_iff⟩ := litSign_eval hX' hval hls
      have hor_f := hf_iff.mp flc
      rw [hw_pt hwv_lt pv, hS_pt ha7 pa, hw_pt hwx_lt pwx] at hor_f
      have hor_t := (hc9_a (Tx := W₀ ⟨wx, hwx_lt⟩) (fun z hz => by
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl <;> simp [W₀, specWitnessEmb, hmx_v, hxc.1, hxc.2])).1
      rw [e_vqp] at hor_t; rw [hor_t] at hor_f; exact (Bool.eq_not_self _).mp hor_f
  rw [if_neg hck0] at hco
  by_cases hck1 : (conclKind == 1) = true
  · rw [if_pos hck1] at hco
    cases hmx : getMask ctx wx with
    | none => rw [hmx] at hco; nomatch hco
    | some mx =>
    rw [hmx] at hco; dsimp only at hco
    obtain ⟨hxc, hco⟩ := ite_none_eq_some hco
    simp only [Bool.and_eq_true] at hxc
    cases hls : litSign ctx (!(sigNat == 1)) (7 + wv) p (7 + wx) with
    | none => rw [hls] at hco; nomatch hco
    | some lc =>
      rw [hls] at hco; injection hco with he; subst he
      obtain ⟨flc, _⟩ := evalClause_cons_false fcL
      obtain ⟨hwx_lt, hmx_v⟩ := getMask_sound hM hm_eq hmx
      obtain ⟨_, _, pwx, _, _, _, _, hf_iff⟩ := litSign_eval hX' hval hls
      have hor_f := hf_iff.mp flc
      rw [hw_pt hwv_lt pv, hS_pt hp7 pp, hw_pt hwx_lt pwx] at hor_f
      have hor_t := (hc9_b (Tx := W₀ ⟨wx, hwx_lt⟩) (fun z hz => by
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl <;> simp [W₀, specWitnessEmb, hmx_v, hxc.1, hxc.2])).1
      rw [e_vqp] at hor_t; rw [hor_t] at hor_f; exact (Bool.eq_not_self _).mp hor_f
  rw [if_neg hck1] at hco
  by_cases hck2 : (conclKind == 2) = true
  · rw [if_pos hck2] at hco
    cases hmx : getMask ctx wx with
    | none => rw [hmx] at hco; nomatch hco
    | some mx =>
    rw [hmx] at hco; dsimp only at hco
    obtain ⟨hxc, hco⟩ := ite_none_eq_some hco
    simp only [Bool.and_eq_true] at hxc
    cases hls : litSign ctx (sigNat == 1) p (7 + wx) a with
    | none => rw [hls] at hco; nomatch hco
    | some lc =>
      rw [hls] at hco; injection hco with he; subst he
      obtain ⟨flc, _⟩ := evalClause_cons_false fcL
      obtain ⟨hwx_lt, hmx_v⟩ := getMask_sound hM hm_eq hmx
      obtain ⟨_, pwx, _, _, _, _, _, hf_iff⟩ := litSign_eval hX' hval hls
      have hor_f := hf_iff.mp flc
      rw [hS_pt hp7 pp, hw_pt hwx_lt pwx, hS_pt ha7 pa] at hor_f
      have hor_t := (hc9_c (Tx := W₀ ⟨wx, hwx_lt⟩) (fun z hz => by
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl <;> simp [W₀, specWitnessEmb, hmx_v, hxc.1.1, hxc.1.2])
        (by simp [W₀, specWitnessEmb, hmx_v, hxc.2])).1
      rw [e_vqp] at hor_t; rw [hor_t] at hor_f; exact (Bool.eq_not_self _).mp hor_f
  rw [if_neg hck2] at hco
  by_cases hck3 : (conclKind == 3) = true
  · rw [if_pos hck3] at hco
    cases hmx : getMask ctx wx with
    | none => rw [hmx] at hco; nomatch hco
    | some mx =>
    cases hmy : getMask ctx wy with
    | none => rw [hmx, hmy] at hco; nomatch hco
    | some my =>
    rw [hmx, hmy] at hco; dsimp only at hco
    obtain ⟨hxc, hco⟩ := ite_none_eq_some hco
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hxc
    cases hls : litSign ctx (sigNat == 1) p (7 + wx) (7 + wy) with
    | none => rw [hls] at hco; nomatch hco
    | some lc =>
      rw [hls] at hco; injection hco with he; subst he
      obtain ⟨flc, _⟩ := evalClause_cons_false fcL
      obtain ⟨hwx_lt, hmx_v⟩ := getMask_sound hM hm_eq hmx
      obtain ⟨hwy_lt, hmy_v⟩ := getMask_sound hM hm_eq hmy
      obtain ⟨_, pwx, pwy, _, _, _, _, hf_iff⟩ := litSign_eval hX' hval hls
      have hor_f := hf_iff.mp flc
      rw [hS_pt hp7 pp, hw_pt hwx_lt pwx, hw_pt hwy_lt pwy] at hor_f
      have hor_t := hc9_s (Tx := W₀ ⟨wx, hwx_lt⟩) (Ty := W₀ ⟨wy, hwy_lt⟩)
        (fun z hz => by
          simp only [Finset.mem_insert, Finset.mem_singleton] at hz
          rcases hz with rfl | rfl <;> simp [W₀, specWitnessEmb, hmx_v, hxc.1.1.1.1.1, hxc.1.1.1.1.2])
        (by simp [W₀, specWitnessEmb, hmx_v, hxc.1.1.1.2])
        (fun z hz => by
          simp only [Finset.mem_insert, Finset.mem_singleton] at hz
          rcases hz with rfl | rfl <;> simp [W₀, specWitnessEmb, hmy_v, hxc.1.1.2, hxc.1.2])
        (by simp [W₀, specWitnessEmb, hmy_v, hxc.2])
      rw [e_vqp] at hor_t; rw [hor_t] at hor_f; exact (Bool.eq_not_self _).mp hor_f
  · rw [if_neg hck3] at hco; nomatch hco

set_option maxHeartbeats 1600000 in
/-- **Main Clause Generator Soundness Theorem (`decodeOneJust_sound`)**:
    Every clause `cl` emitted by `decodeOneJust ctx cs = some (some cl, rest)` (`Tags 0..19`)
    evaluates to `true` under the geometric `orientSign` valuation `val`! -/
theorem decodeOneJust_sound {P : Set (ℝ × ℝ)} {S : Fin 7 → ℝ × ℝ} {w : Finset (Fin 7) → ℝ × ℝ}
    {ctx : CertCtx}
    (hV : ValidCanonicalInstance P S w ctx.spec)
    (hM : ValidMasks ctx.spec.masks)
    (hn_pts : ctx.n_pts = 7 + ctx.spec.masks.length)
    (hbccw_eq : ctx.bccw = buildBccw ctx.spec)
    (hm_eq : ctx.maskTrie = buildMaskTrieAux .xH ctx.spec.masks .leaf)
    {val : PIdx → Bool}
    (hval : ∀ {i j k : ℕ} (hij : i < j) (hjk : j < k) (hk : k < ctx.n_pts) {v : PIdx},
      ctx.tripleTrie.get3 (ptKey i) (ptKey j) (ptKey k) = some v →
      val v = orientSign (pointSeq S w (specWitnessEmb hM) ⟨i, by omega⟩)
                         (pointSeq S w (specWitnessEmb hM) ⟨j, by omega⟩)
                         (pointSeq S w (specWitnessEmb hM) ⟨k, by omega⟩))
    {cs rest : ByteStream} {cl : Clause}
    (hdec : decodeOneJust ctx cs = some (some cl, rest)) :
    evalClause val cl = true := by
  let W₀ := specWitnessEmb hM
  let X : Fin (7 + ctx.spec.masks.length) → ℝ × ℝ := pointSeq S w W₀
  let X' : Fin ctx.n_pts → ℝ × ℝ := fun z => X ⟨z.val, by omega⟩
  have hX : NoThreeCollinear X := noThreeCollinear_pointSeq hV.hP W₀
  have hX' : NoThreeCollinear X' :=
    ⟨fun a b h => Fin.ext (Fin.mk.inj (hX.1 h)),
     fun a b c hab hbc hac => hX.2 _ _ _
       (fun e => hab (Fin.ext (Fin.mk.inj e)))
       (fun e => hbc (Fin.ext (Fin.mk.inj e)))
       (fun e => hac (Fin.ext (Fin.mk.inj e)))⟩
  have hS_pt : ∀ {u : ℕ} (hu7 : u < 7) (hu : u < ctx.n_pts), X' ⟨u, hu⟩ = S ⟨u, hu7⟩ :=
    fun hu7 hu => pointSeq_S_eq S w W₀ hu7 (by omega)
  have hw_pt : ∀ {wi : ℕ} (hwi : wi < ctx.spec.masks.length) (hu : 7 + wi < ctx.n_pts),
      X' ⟨7 + wi, hu⟩ = w (W₀ ⟨wi, hwi⟩) :=
    fun hwi _ => pointSeq_w_eq S w W₀ hwi
  cases hev : evalClause val cl
  · exfalso
    unfold decodeOneJust at hdec
    cases ht0 : bsReadNat cs with
    | none => rw [ht0] at hdec; nomatch hdec
    | some pt0 =>
    rcases pt0 with ⟨tag, cs1⟩
    rw [ht0] at hdec; dsimp only at hdec
    by_cases htag20 : (tag == 20) = true
    · rw [if_pos htag20] at hdec; nomatch hdec
    rw [if_neg htag20] at hdec
    by_cases htag01 : (tag == 0 || tag == 1) = true
    · -- Tags 0 & 1: (C1) GP5 6-literal exclusion
      rw [if_pos htag01] at hdec
      obtain ⟨ip, ia, ib, ic, id_, flags, _, hdec⟩ := matchNats6 hdec
      obtain ⟨hc, hdec⟩ := ite_none_eq_some hdec
      simp only [Bool.and_eq_true, decide_eq_true_eq, allDistinct5, bne_iff_ne] at hc
      rcases hc with ⟨⟨⟨⟨⟨_, _⟩, _⟩, _⟩, _⟩,
        ⟨⟨⟨⟨⟨⟨⟨⟨⟨hpa, hpb⟩, hpc⟩, hpd⟩, hab⟩, hac⟩, had⟩, hbc⟩, hbd⟩, hcd⟩⟩
      revert hdec
      generalize hlo_g : (if (tag == 0) = true then _ else _) = litsOpt
      intro hdec
      cases litsOpt with | none => nomatch hdec | some cl' =>
      have hlo := hlo_g
      injection hdec with hp; injection (Prod.mk.inj hp).1 with hcl; subst hcl
      by_cases ht0_b : (tag == 0) = true
      · rw [if_pos ht0_b] at hlo
        obtain ⟨_, _, _, _, _, _, o1, o2, o3, o4, o5, o6, f1, f2, f3, f4, f5, f6⟩ := optSeq6_false hlo hev
        obtain ⟨_, _, _, e1⟩ := litForb_eval_false hX' hval o1 f1
        obtain ⟨_, _, _, e2⟩ := litForb_eval_false hX' hval o2 f2
        obtain ⟨_, _, _, e3⟩ := litForb_eval_false hX' hval o3 f3
        obtain ⟨_, _, _, e4⟩ := litForb_eval_false hX' hval o4 f4
        obtain ⟨_, _, _, e5⟩ := litForb_eval_false hX' hval o5 f5
        obtain ⟨_, _, _, e6⟩ := litForb_eval_false hX' hval o6 f6
        exact (hX'.gp5_clauses
          (Fin.val_ne_iff.mp hpa) (Fin.val_ne_iff.mp hpb) (Fin.val_ne_iff.mp hpc) (Fin.val_ne_iff.mp hpd)
          (Fin.val_ne_iff.mp hab) (Fin.val_ne_iff.mp hac) (Fin.val_ne_iff.mp had)
          (Fin.val_ne_iff.mp hbc) (Fin.val_ne_iff.mp hbd) (Fin.val_ne_iff.mp hcd)
          ((flags % 2) == 1) (((flags / 2) % 2) == 1) (((flags / 4) % 2) == 1)).1
          ⟨e1, e2, e3, e4, e5, e6⟩
      · rw [if_neg ht0_b] at hlo
        obtain ⟨_, _, _, _, _, _, o1, o2, o3, o4, o5, o6, f1, f2, f3, f4, f5, f6⟩ := optSeq6_false hlo hev
        obtain ⟨_, _, _, e1⟩ := litForb_eval_false hX' hval o1 f1
        obtain ⟨_, _, _, e2⟩ := litForb_eval_false hX' hval o2 f2
        obtain ⟨_, _, _, e3⟩ := litForb_eval_false hX' hval o3 f3
        obtain ⟨_, _, _, e4⟩ := litForb_eval_false hX' hval o4 f4
        obtain ⟨_, _, _, e5⟩ := litForb_eval_false hX' hval o5 f5
        obtain ⟨_, _, _, e6⟩ := litForb_eval_false hX' hval o6 f6
        exact (hX'.gp5_clauses
          (Fin.val_ne_iff.mp hpa) (Fin.val_ne_iff.mp hpb) (Fin.val_ne_iff.mp hpc) (Fin.val_ne_iff.mp hpd)
          (Fin.val_ne_iff.mp hab) (Fin.val_ne_iff.mp hac) (Fin.val_ne_iff.mp had)
          (Fin.val_ne_iff.mp hbc) (Fin.val_ne_iff.mp hbd) (Fin.val_ne_iff.mp hcd)
          ((flags % 2) == 1) (((flags / 2) % 2) == 1) (((flags / 4) % 2) == 1)).2
          ⟨e1, e2, e3, e4, e5, e6⟩
    rw [if_neg htag01] at hdec
    by_cases htag2 : (tag == 2) = true
    · -- Tag 2: (C2) Hull CCW triple
      rw [if_pos htag2] at hdec
      obtain ⟨i, j, k, _, hdec⟩ := matchNats3 hdec
      obtain ⟨hijk, hdec⟩ := ite_none_eq_some hdec
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hijk
      cases hi : listGetOpt ctx.bccw i with | none => rw [hi] at hdec; nomatch hdec | some pi =>
      cases hj : listGetOpt ctx.bccw j with | none => rw [hi, hj] at hdec; nomatch hdec | some pj =>
      cases hk : listGetOpt ctx.bccw k with | none => rw [hi, hj, hk] at hdec; nomatch hdec | some pk =>
      rw [hi, hj, hk] at hdec; dsimp only at hdec
      cases hl : litSign ctx true pi pj pk with | none => rw [hl] at hdec; nomatch hdec | some l =>
      rw [hl] at hdec
      injection hdec with hp; injection (Prod.mk.inj hp).1 with hcl; subst hcl
      obtain ⟨hl_f, _⟩ := evalClause_cons_false hev
      obtain ⟨cb, hbccw_len, hbccw_get⟩ := hV.h_cb
      rw [hbccw_eq] at hi hj hk
      have hk_lt : k < cb.m + 3 := hbccw_len ▸ listGetOpt_lt_len _ k hk
      have hpi7 : pi < 7 := by
        have := hbccw_get ⟨i, by omega⟩; rw [hi] at this; injection this with e; rw [e]; exact (cb.p_idx _).isLt
      have hpj7 : pj < 7 := by
        have := hbccw_get ⟨j, by omega⟩; rw [hj] at this; injection this with e; rw [e]; exact (cb.p_idx _).isLt
      have hpk7 : pk < 7 := by
        have := hbccw_get ⟨k, hk_lt⟩; rw [hk] at this; injection this with e; rw [e]; exact (cb.p_idx _).isLt
      have fi_eq : cb.p_idx ⟨i, by omega⟩ = ⟨pi, hpi7⟩ :=
        Fin.ext (Option.some.inj ((hbccw_get ⟨i, by omega⟩).symm.trans hi))
      have fj_eq : cb.p_idx ⟨j, by omega⟩ = ⟨pj, hpj7⟩ :=
        Fin.ext (Option.some.inj ((hbccw_get ⟨j, by omega⟩).symm.trans hj))
      have fk_eq : cb.p_idx ⟨k, hk_lt⟩ = ⟨pk, hpk7⟩ :=
        Fin.ext (Option.some.inj ((hbccw_get ⟨k, hk_lt⟩).symm.trans hk))
      obtain ⟨hpi, hpj, hpk, _, _, _, _, hf_iff⟩ := litSign_eval hX' hval hl
      have hor_false := hf_iff.mp hl_f
      have hor_true := (shattered_hull_and_interior_orientSign_C2 hV.hP cb).1
        ⟨i, by omega⟩ ⟨j, by omega⟩ ⟨k, hk_lt⟩ hijk.1 hijk.2
      rw [hS_pt hpi7 hpi, hS_pt hpj7 hpj, hS_pt hpk7 hpk,
          ← fi_eq, ← fj_eq, ← fk_eq, hor_true] at hor_false
      exact Bool.noConfusion hor_false
    rw [if_neg htag2] at hdec
    by_cases htag3 : (tag == 3) = true
    · -- Tag 3: (C2) Interior point in conv(B)
      rw [if_pos htag3] at hdec
      obtain ⟨r, a, _, hdec⟩ := matchNats2 hdec
      obtain ⟨hra, hdec⟩ := ite_none_eq_some hdec
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hra
      rcases hra with ⟨⟨hr_lt, ha_ge⟩, ha7⟩
      cases hpr : listGetOpt ctx.bccw r with | none => rw [hpr] at hdec; nomatch hdec | some pr =>
      cases hpr1 : listGetOpt ctx.bccw (if r + 1 < ctx.bccw.length then r + 1 else 0) with
      | none => rw [hpr, hpr1] at hdec; nomatch hdec | some pr1 =>
      rw [hpr, hpr1] at hdec; dsimp only at hdec
      cases hl : litSign ctx true pr pr1 a with | none => rw [hl] at hdec; nomatch hdec | some l =>
      rw [hl] at hdec
      injection hdec with hp; injection (Prod.mk.inj hp).1 with hcl; subst hcl
      obtain ⟨hl_f, _⟩ := evalClause_cons_false hev
      obtain ⟨cb, hbccw_len, hbccw_get⟩ := hV.h_cb
      have hbsz : ctx.bccw.length = cb.m + 3 := by rw [hbccw_eq, hbccw_len]
      let fr : Fin (cb.m + 3) := ⟨r, by omega⟩
      have hr_next_eq : (fr + 1).val = (if r + 1 < ctx.bccw.length then r + 1 else 0) := by
        have hmod : (fr + 1).val = (r + 1) % (cb.m + 3) := by
          rw [← PolygonCore.finShift_one (by omega : 2 ≤ cb.m + 3) fr]; rfl
        rw [hmod, hbsz]
        split_ifs with hw
        · exact Nat.mod_eq_of_lt hw
        · rw [show r + 1 = cb.m + 3 by omega, Nat.mod_self]
      rw [← hr_next_eq] at hpr1
      rw [hbccw_eq] at hpr hpr1
      have fpr_eq : (cb.p_idx fr).val = pr := Option.some.inj ((hbccw_get fr).symm.trans hpr)
      have fpr1_eq : (cb.p_idx (fr + 1)).val = pr1 := Option.some.inj ((hbccw_get (fr + 1)).symm.trans hpr1)
      have hpr7 : pr < 7 := fpr_eq ▸ (cb.p_idx fr).isLt
      have hpr1_7 : pr1 < 7 := fpr1_eq ▸ (cb.p_idx (fr + 1)).isLt
      have ha_int : (⟨a, ha7⟩ : Fin 7) ∈ PolygonCore.interiorPoints S :=
        (mem_interior_iff_of_valid hV ⟨a, ha7⟩).mpr ha_ge
      have hor_true := (shattered_hull_and_interior_orientSign_C2 hV.hP cb).2 ⟨a, ha7⟩ ha_int fr
      obtain ⟨h1, h2, h3, _, _, _, _, hf_iff⟩ := litSign_eval hX' hval hl
      have hor_false := hf_iff.mp hl_f
      rw [hS_pt hpr7 h1, hS_pt hpr1_7 h2, hS_pt ha7 h3] at hor_false
      have c1 : (⟨pr, hpr7⟩ : Fin 7) = cb.p_idx fr := Fin.ext fpr_eq.symm
      have c2 : (⟨pr1, hpr1_7⟩ : Fin 7) = cb.p_idx (fr + 1) := Fin.ext fpr1_eq.symm
      rw [c1, c2, hor_true] at hor_false
      exact Bool.noConfusion hor_false
    rw [if_neg htag3] at hdec
    by_cases htag4 : (tag == 4) = true
    · -- Tag 4: (C4) Non-certified hull obstruction
      rw [if_pos htag4] at hdec
      obtain ⟨wIdx, k, s1, s2, sdNat, _, hdec⟩ := matchNats5 hdec
      cases hgm : getMask ctx wIdx with | none => rw [hgm] at hdec; nomatch hdec | some m =>
      rw [hgm] at hdec; dsimp only at hdec
      obtain ⟨hc, hdec⟩ := ite_none_eq_some hdec
      simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hc
      rcases hc with ⟨⟨⟨⟨⟨hk_nd, hs12⟩, hs2_7⟩, hk_miss_b⟩, hs1_b⟩, hs2_b⟩
      cases hnt : notInTriSideLits ctx (sdNat == 1) k (7 + wIdx) s1 s2 with
      | none => rw [hnt] at hdec; nomatch hdec | some cl' =>
      rw [hnt] at hdec
      injection hdec with hp; injection (Prod.mk.inj hp).1 with hcl; subst hcl
      obtain ⟨hw_lt, hm_val⟩ := getMask_sound hM hm_eq hgm
      obtain ⟨hk_p, hw_p, hs1_p, hs2_p, hside⟩ := notInTriSideLits_eval_false hX' hval hnt hev
      have hk7 : k < 7 := by have := hV.h_tot_le7; omega
      have hs1_7 : s1 < 7 := by omega
      rw [hS_pt hk7 hk_p, hw_pt hw_lt hw_p, hS_pt hs1_7 hs1_p, hS_pt hs2_7 hs2_p] at hside
      have htri_true : inOpenTriBool (S ⟨k, hk7⟩) (w (W₀ ⟨wIdx, hw_lt⟩)) (S ⟨s1, hs1_7⟩) (S ⟨s2, hs2_7⟩) = true :=
        inOpenTriBool_of_side hside
      have hkD : (⟨k, hk7⟩ : Fin 7) ∈ PolygonCore.hullVertices S \ PolygonCore.certifiedSet P S w :=
        (hV.hD_mem ⟨k, hk7⟩).mpr hk_nd
      have htri_false := non_certified_obstruction_clause_C4 hV.hP (by decide)
        (s₁ := ⟨s1, hs1_7⟩) (s₂ := ⟨s2, hs2_7⟩) (Tw := W₀ ⟨wIdx, hw_lt⟩) hkD
        (by simp [W₀, specWitnessEmb, hm_val, hk_miss_b])
        (by simp [W₀, specWitnessEmb, hm_val, hs1_b])
        (by simp [W₀, specWitnessEmb, hm_val, hs2_b])
        (Fin.ne_of_val_ne (by dsimp; omega))
      rw [htri_false] at htri_true; exact Bool.noConfusion htri_true
    rw [if_neg htag4] at hdec
    by_cases htag5 : (tag == 5) = true
    · -- Tag 5: (C5) Exit-edge triangle containment
      rw [if_pos htag5] at hdec
      obtain ⟨eIdx, wIdx, pairIdx, sNat, _, hdec⟩ := matchNats4 hdec
      cases hed : listGetOpt ctx.spec.edges eIdx with
      | none => rw [hed] at hdec; nomatch hdec
      | some uOpt =>
        cases uOpt with
        | none => rw [hed] at hdec; nomatch hdec
        | some u_y =>
          rw [hed] at hdec
          cases hgm : getMask ctx wIdx with
          | none => rw [hgm] at hdec; nomatch hdec
          | some m =>
            rw [hgm] at hdec; dsimp only at hdec
            obtain ⟨hc1, hdec⟩ := ite_none_eq_some hdec
            obtain ⟨hc2, hdec⟩ := ite_none_eq_some hdec
            simp only [Bool.and_eq_true, decide_eq_true_eq] at hc1 hc2
            rcases hc1 with ⟨⟨hnd3, huy_lt⟩, he_lt⟩
            cases htp : inTriPairLits ctx pairIdx (sNat == 1) (ctx.spec.n_d + eIdx) (7 + wIdx)
                u_y (if u_y + 1 < ctx.spec.n_d then u_y + 1 else 0) with
            | none => rw [htp] at hdec; nomatch hdec | some cl' =>
            rw [htp] at hdec
            injection hdec with hp; injection (Prod.mk.inj hp).1 with hcl; subst hcl
            obtain ⟨hw_lt, hm_val⟩ := getMask_sound hM hm_eq hgm
            have htot := hV.h_tot_le7
            have htri := hV.h_edges hnd3 eIdx u_y he_lt hed huy_lt (W₀ ⟨wIdx, hw_lt⟩)
              (by simp [W₀, specWitnessEmb, hm_val, hc2.1])
              (by simp [W₀, specWitnessEmb, hm_val, hc2.2])
            have hy_p : ctx.spec.n_d + eIdx < ctx.n_pts := by omega
            have hw_p : 7 + wIdx < ctx.n_pts := by omega
            have hu_p : u_y < ctx.n_pts := by omega
            have hv_p : (if u_y + 1 < ctx.spec.n_d then u_y + 1 else 0) < ctx.n_pts := by
              have := nextMod_lt_seven (u := u_y) (n_d := ctx.spec.n_d) (by omega); omega
            have htri_X : inOpenTriBool (X' ⟨ctx.spec.n_d + eIdx, hy_p⟩) (X' ⟨7 + wIdx, hw_p⟩)
                (X' ⟨u_y, hu_p⟩) (X' ⟨if u_y + 1 < ctx.spec.n_d then u_y + 1 else 0, hv_p⟩) = true := by
              rw [hS_pt (by omega) hy_p, hw_pt hw_lt hw_p,
                  hS_pt (by omega) hu_p, hS_pt (nextMod_lt_seven (by omega)) hv_p]
              exact htri
            have htrue := inTriPairLits_sound hX' hval hy_p hw_p hu_p hv_p htri_X htp
            rw [htrue] at hev; exact Bool.noConfusion hev
    rw [if_neg htag5] at hdec
    by_cases htag6 : (tag == 6) = true
    · -- Tag 6: (C5/C6) Wedge separation
      rw [if_pos htag6] at hdec
      obtain ⟨coneKind, idx, w1, w2, wm, sNat, _, hdec⟩ := matchNats6 hdec
      revert hdec
      generalize huv_g : (if (coneKind == 0) = true then _ else _) = uvOpt
      intro hdec
      cases uvOpt with | none => nomatch hdec | some yuv =>
      rcases yuv with ⟨y, u, v⟩
      cases hm1 : getMask ctx w1 with | none => rw [hm1] at hdec; nomatch hdec | some m1 =>
      cases hm2 : getMask ctx w2 with | none => rw [hm1, hm2] at hdec; nomatch hdec | some m2 =>
      cases hmm : getMask ctx wm with | none => rw [hm1, hm2, hmm] at hdec; nomatch hdec | some mm =>
      rw [hm1, hm2, hmm] at hdec; dsimp only at hdec
      have huv := huv_g
      obtain ⟨hc, hdec⟩ := ite_none_eq_some hdec
      simp only [Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne] at hc
      rcases hc with ⟨⟨⟨⟨⟨⟨⟨⟨⟨hw12, su1⟩, sv1⟩, sy1⟩, su2⟩, sv2⟩, sy2⟩, sum_⟩, svm⟩, sym_not⟩
      cases hlo : optSequence [litForb ctx (sNat == 1) y (7 + w1) (7 + w2),
          litForb ctx (sNat == 1) y (7 + w1) (7 + wm),
          litForb ctx (sNat == 1) y (7 + wm) (7 + w2)] with
      | none => rw [hlo] at hdec; nomatch hdec | some cl' =>
      rw [hlo] at hdec
      injection hdec with hp; injection (Prod.mk.inj hp).1 with hcl; subst hcl
      have huv_prop : ∃ (hy7 : y < 7) (hu7 : u < 7) (hv7 : v < 7),
          y ≠ u ∧ y ≠ v ∧ u ≠ v ∧
          ∀ Tw : Finset (Fin 7), ⟨u, hu7⟩ ∈ Tw → ⟨v, hv7⟩ ∈ Tw →
            inOpenTriBool (S ⟨y, hy7⟩) (w Tw) (S ⟨u, hu7⟩) (S ⟨v, hv7⟩) = true := by
        have htot := hV.h_tot_le7
        by_cases hck0 : (coneKind == 0) = true
        · rw [if_pos hck0] at huv
          cases hed : listGetOpt ctx.spec.edges idx with
          | none => rw [hed] at huv; nomatch huv
          | some uo => cases uo with
            | none => rw [hed] at huv; nomatch huv
            | some u0 =>
              rw [hed] at huv; dsimp only at huv
              obtain ⟨hc0, huv⟩ := ite_none_eq_some huv
              simp only [Bool.and_eq_true, decide_eq_true_eq] at hc0
              injection huv with hp; rcases Prod.mk.inj hp with ⟨rfl, hp2⟩; rcases Prod.mk.inj hp2 with ⟨rfl, rfl⟩
              exact ⟨by omega, by omega, nextMod_lt_seven (by omega),
                by omega, by split_ifs <;> omega, by split_ifs <;> omega,
                fun Tw huT hvT => hV.h_edges hc0.1.1 idx u0 hc0.2 hed hc0.1.2 Tw huT hvT⟩
        rw [if_neg hck0] at huv
        by_cases hck1 : (coneKind == 1) = true
        · rw [if_pos hck1] at huv
          cases hlr : ctx.spec.lr_l with
          | none => rw [hlr] at huv; nomatch huv
          | some l =>
          rw [hlr] at huv; dsimp only at huv
          obtain ⟨hc1, huv⟩ := ite_none_eq_some huv
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hc1
          injection huv with hp; rcases Prod.mk.inj hp with ⟨rfl, hp2⟩; rcases Prod.mk.inj hp2 with ⟨rfl, rfl⟩
          obtain ⟨l', _, hlr', htri_lr, _, _⟩ := hV.h_pocket hc1.1.1.1
          rw [hlr] at hlr'; injection hlr' with hll; subst hll
          refine ⟨by omega, by omega, nextMod_lt_seven (by omega),
            by omega, by split_ifs <;> omega, by split_ifs <;> omega, fun Tw huT hvT => ?_⟩
          refine htri_lr idx hc1.1.1.2 Tw (fun z hz => ?_)
          simp only [Finset.mem_insert, Finset.mem_singleton] at hz
          rcases hz with rfl | rfl <;> assumption
        rw [if_neg hck1] at huv
        by_cases hck2 : (coneKind == 2) = true
        · rw [if_pos hck2] at huv
          cases hlr : ctx.spec.lr_l with
          | none => rw [hlr] at huv; nomatch huv
          | some l =>
          rw [hlr] at huv; dsimp only at huv
          obtain ⟨hc2, huv⟩ := ite_none_eq_some huv
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hc2
          injection huv with hp; rcases Prod.mk.inj hp with ⟨rfl, hp2⟩; rcases Prod.mk.inj hp2 with ⟨rfl, rfl⟩
          obtain ⟨l', hl'_nd, hlr', _, hnb, _⟩ := hV.h_pocket (by omega)
          rw [hlr] at hlr'; injection hlr' with hll; subst hll
          obtain ⟨hne1, hne2, hne3, htri_nb⟩ := hnb hc2.1.1.1 idx hc2.1.1.2
          refine ⟨by omega, hm_lt_seven htot hl'_nd hc2.1.1.2, hp_lt_seven htot hc2.1.1.2,
            fun e => hne1 (Fin.ext e.symm), fun e => hne2 (Fin.ext e.symm), fun e => hne3 (Fin.ext e),
            fun Tw huT hvT => htri_nb Tw (fun z hz => ?_)⟩
          simp only [Finset.mem_insert, Finset.mem_singleton] at hz
          rcases hz with rfl | rfl <;> assumption
        · rw [if_neg hck2] at huv; nomatch huv
      obtain ⟨hy7, hu7, hv7, hyu, hyv, huv_ne, htri_all⟩ := huv_prop
      obtain ⟨hw1_lt, hm1_v⟩ := getMask_sound hM hm_eq hm1
      obtain ⟨hw2_lt, hm2_v⟩ := getMask_sound hM hm_eq hm2
      obtain ⟨hwm_lt, hmm_v⟩ := getMask_sound hM hm_eq hmm
      obtain ⟨_, _, _, o1, o2, o3, f1, f2, f3⟩ := optSeq3_false hlo hev
      obtain ⟨p_y1, p_w1, p_w2, e1⟩ := litForb_eval_false hX' hval o1 f1
      obtain ⟨_, _, p_wm, e2⟩ := litForb_eval_false hX' hval o2 f2
      obtain ⟨_, _, _, e3⟩ := litForb_eval_false hX' hval o3 f3
      rw [hS_pt hy7 p_y1, hw_pt hw1_lt p_w1, hw_pt hw2_lt p_w2] at e1
      rw [hS_pt hy7 p_y1, hw_pt hw1_lt p_w1, hw_pt hwm_lt p_wm] at e2
      rw [hS_pt hy7 p_y1, hw_pt hwm_lt p_wm, hw_pt hw2_lt p_w2] at e3
      exact wedge_sep_clause_C5 hV.hP
        (y := ⟨y, hy7⟩) (u := ⟨u, hu7⟩) (v := ⟨v, hv7⟩)
        (T₁ := W₀ ⟨w1, hw1_lt⟩) (T₂ := W₀ ⟨w2, hw2_lt⟩) (Tm := W₀ ⟨wm, hwm_lt⟩)
        (Fin.ne_of_val_ne hyu) (Fin.ne_of_val_ne hyv) (Fin.ne_of_val_ne huv_ne)
        (W₀.injective.ne (Fin.ne_of_val_ne hw12))
        (by simp [W₀, specWitnessEmb, hm1_v, su1]) (by simp [W₀, specWitnessEmb, hm1_v, sv1]) (by simp [W₀, specWitnessEmb, hm1_v, sy1])
        (by simp [W₀, specWitnessEmb, hm2_v, su2]) (by simp [W₀, specWitnessEmb, hm2_v, sv2]) (by simp [W₀, specWitnessEmb, hm2_v, sy2])
        (by simp [W₀, specWitnessEmb, hmm_v, sum_]) (by simp [W₀, specWitnessEmb, hmm_v, svm]) (by simp [W₀, specWitnessEmb, hmm_v, sym_not])
        (htri_all _ (by simp [W₀, specWitnessEmb, hm1_v, su1]) (by simp [W₀, specWitnessEmb, hm1_v, sv1]))
        (htri_all _ (by simp [W₀, specWitnessEmb, hm2_v, su2]) (by simp [W₀, specWitnessEmb, hm2_v, sv2]))
        (sNat == 1) ⟨e1, e2, e3⟩
    rw [if_neg htag6] at hdec
    by_cases htag7 : (tag == 7) = true
    · -- Tag 7: (C6) Pocket (l, r) or Neighbor (hm, hp) triangle containment
      rw [if_pos htag7] at hdec
      obtain ⟨isNb, hi, wIdx, pairIdx, sNat, _, hdec⟩ := matchNats5 hdec
      cases hlr : ctx.spec.lr_l with | none => rw [hlr] at hdec; nomatch hdec | some l =>
      cases hgm : getMask ctx wIdx with | none => rw [hlr, hgm] at hdec; nomatch hdec | some m =>
      rw [hlr, hgm] at hdec; dsimp only at hdec
      obtain ⟨hc0, hdec⟩ := ite_none_eq_some hdec
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc0
      have htot := hV.h_tot_le7
      obtain ⟨hw_lt, hm_val⟩ := getMask_sound hM hm_eq hgm
      by_cases hnb0 : (isNb == 0) = true
      · rw [if_pos hnb0] at hdec
        obtain ⟨hlr_sees, hdec⟩ := ite_none_eq_some hdec
        simp only [Bool.and_eq_true] at hlr_sees
        cases htp : inTriPairLits ctx pairIdx (sNat == 1) (ctx.spec.n_d + hi) (7 + wIdx)
            l (if l + 1 < ctx.spec.n_d then l + 1 else 0) with
        | none => rw [htp] at hdec; nomatch hdec | some cl' =>
        rw [htp] at hdec
        injection hdec with hp; injection (Prod.mk.inj hp).1 with hcl; subst hcl
        obtain ⟨l', _, hlr', htri_lr, _, _⟩ := hV.h_pocket hc0.1.1.1
        rw [hlr] at hlr'; injection hlr' with hll; subst hll
        have hh_p : ctx.spec.n_d + hi < ctx.n_pts := by omega
        have hw_p : 7 + wIdx < ctx.n_pts := by omega
        have hl_p : l < ctx.n_pts := by omega
        have hr_p : (if l + 1 < ctx.spec.n_d then l + 1 else 0) < ctx.n_pts := by
          have := nextMod_lt_seven (u := l) (n_d := ctx.spec.n_d) (by omega); omega
        have htri := htri_lr hi hc0.1.1.2 (W₀ ⟨wIdx, hw_lt⟩) (fun z hz => by
          simp only [Finset.mem_insert, Finset.mem_singleton] at hz
          rcases hz with rfl | rfl
          · simp [W₀, specWitnessEmb, hm_val, hlr_sees.1]
          · simp [W₀, specWitnessEmb, hm_val, hlr_sees.2])
        have htri_X : inOpenTriBool (X' ⟨ctx.spec.n_d + hi, hh_p⟩) (X' ⟨7 + wIdx, hw_p⟩)
            (X' ⟨l, hl_p⟩) (X' ⟨if l + 1 < ctx.spec.n_d then l + 1 else 0, hr_p⟩) = true := by
          rw [hS_pt (by omega) hh_p, hw_pt hw_lt hw_p,
              hS_pt (by omega) hl_p, hS_pt (nextMod_lt_seven (by omega)) hr_p]
          exact htri
        have htrue := inTriPairLits_sound hX' hval hh_p hw_p hl_p hr_p htri_X htp
        rw [htrue] at hev; exact Bool.noConfusion hev
      · rw [if_neg hnb0] at hdec
        obtain ⟨hnb1, hdec⟩ := ite_none_eq_some hdec
        obtain ⟨hnb_sees, hdec⟩ := ite_none_eq_some hdec
        simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hnb1 hnb_sees
        cases htp : inTriPairLits ctx pairIdx (sNat == 1) (ctx.spec.n_d + hi) (7 + wIdx)
            (if hi == 0 then l else (ctx.spec.n_d + hi) - 1)
            (if hi + 1 == ctx.spec.h_sz then (if l + 1 < ctx.spec.n_d then l + 1 else 0) else (ctx.spec.n_d + hi) + 1) with
        | none => rw [htp] at hdec; nomatch hdec | some cl' =>
        rw [htp] at hdec
        injection hdec with hp; injection (Prod.mk.inj hp).1 with hcl; subst hcl
        obtain ⟨l', hl'_nd, hlr', _, hnb, _⟩ := hV.h_pocket hc0.1.1.1
        rw [hlr] at hlr'; injection hlr' with hll; subst hll
        have hhm7 := hm_lt_seven htot hl'_nd hc0.1.1.2
        have hhp7 := hp_lt_seven (l := l) htot hc0.1.1.2
        have hh_p : ctx.spec.n_d + hi < ctx.n_pts := by omega
        have hw_p : 7 + wIdx < ctx.n_pts := by omega
        have hhm_p : (if hi == 0 then l else (ctx.spec.n_d + hi) - 1) < ctx.n_pts := by omega
        have hhp_p : (if hi + 1 == ctx.spec.h_sz then (if l + 1 < ctx.spec.n_d then l + 1 else 0) else (ctx.spec.n_d + hi) + 1) < ctx.n_pts := by omega
        have htri := (hnb hnb1.2 hi hc0.1.1.2).2.2.2 (W₀ ⟨wIdx, hw_lt⟩) (fun z hz => by
          simp only [Finset.mem_insert, Finset.mem_singleton] at hz
          rcases hz with rfl | rfl
          · dsimp only [W₀, specWitnessEmb, Function.Embedding.coeFn_mk, maskToFinset]
            rw [Finset.mem_filter]; refine ⟨Finset.mem_univ _, ?_⟩
            dsimp only; rw [hm_val]; exact hnb_sees.1.1
          · dsimp only [W₀, specWitnessEmb, Function.Embedding.coeFn_mk, maskToFinset]
            rw [Finset.mem_filter]; refine ⟨Finset.mem_univ _, ?_⟩
            dsimp only; rw [hm_val]; exact hnb_sees.1.2)
        have htri_X : inOpenTriBool (X' ⟨ctx.spec.n_d + hi, hh_p⟩) (X' ⟨7 + wIdx, hw_p⟩)
            (X' ⟨_, hhm_p⟩) (X' ⟨_, hhp_p⟩) = true := by
          rw [hS_pt (by omega) hh_p, hw_pt hw_lt hw_p, hS_pt hhm7 hhm_p, hS_pt hhp7 hhp_p]
          exact htri
        have htrue := inTriPairLits_sound hX' hval hh_p hw_p hhm_p hhp_p htri_X htp
        rw [htrue] at hev; exact Bool.noConfusion hev
    rw [if_neg htag7] at hdec
    by_cases htag8 : (tag == 8) = true
    · -- Tag 8: (C6) z_h separation (unit literal)
      rw [if_pos htag8] at hdec
      obtain ⟨zhIdx, hi, target, isRightNat, _, hdec⟩ := matchNats4 hdec
      cases hlr : ctx.spec.lr_l with | none => rw [hlr] at hdec; nomatch hdec | some l =>
      cases hgm : getMask ctx zhIdx with | none => rw [hlr, hgm] at hdec; nomatch hdec | some zm =>
      rw [hlr, hgm] at hdec; dsimp only at hdec
      obtain ⟨hc0, hdec⟩ := ite_none_eq_some hdec
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hc0
      rcases hc0 with ⟨⟨⟨⟨⟨hhsz, hhi_lt⟩, hh7⟩, _⟩, _⟩, hzm_eq⟩
      obtain ⟨l', _, hlr', _, _, hzh_sep⟩ := hV.h_pocket hhsz
      rw [hlr] at hlr'; injection hlr' with hll; subst hll
      obtain ⟨hzh_lt, hzm_val⟩ := getMask_sound hM hm_eq hgm
      by_cases hir : (isRightNat == 0) = true
      · rw [if_pos hir] at hdec
        obtain ⟨hleft, hdec⟩ := ite_none_eq_some hdec
        simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at hleft
        cases hl : litSign ctx true (7 + zhIdx) (ctx.spec.n_d + hi) target with
        | none => rw [hl] at hdec; nomatch hdec | some lit =>
        rw [hl] at hdec
        injection hdec with hp; injection (Prod.mk.inj hp).1 with hcl; subst hcl
        obtain ⟨hl_f, _⟩ := evalClause_cons_false hev
        obtain ⟨p1, p2, p3, _, _, _, _, hf_iff⟩ := litSign_eval hX' hval hl
        have ht7 : target < 7 := by have := hV.h_tot_le7; rcases hleft with ⟨_, h⟩ | rfl <;> omega
        have hor_f := hf_iff.mp hl_f
        rw [hw_pt hzh_lt p1, hS_pt hh7 p2, hS_pt ht7 p3] at hor_f
        have hW_zh : W₀ ⟨zhIdx, hzh_lt⟩ = Finset.univ.erase ⟨ctx.spec.n_d + hi, hh7⟩ := by
          dsimp [W₀, specWitnessEmb]; rw [hzm_val, hzm_eq, maskToFinset_zh_eq_erase hh7]
        rw [hW_zh] at hor_f
        have hor_t := (hzh_sep hi hhi_lt target ht7).1 hleft
        unfold PolygonCore.zWitness at hor_t
        rw [hor_t] at hor_f; exact Bool.noConfusion hor_f
      · rw [if_neg hir] at hdec
        obtain ⟨hright, hdec⟩ := ite_none_eq_some hdec
        simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at hright
        cases hl : litSign ctx false (7 + zhIdx) (ctx.spec.n_d + hi) target with
        | none => rw [hl] at hdec; nomatch hdec | some lit =>
        rw [hl] at hdec
        injection hdec with hp; injection (Prod.mk.inj hp).1 with hcl; subst hcl
        obtain ⟨hl_f, _⟩ := evalClause_cons_false hev
        obtain ⟨p1, p2, p3, _, _, _, _, hf_iff⟩ := litSign_eval hX' hval hl
        have ht7 : target < 7 := by
          have := hV.h_tot_le7
          rcases hright with ⟨_, h⟩ | rfl
          · omega
          · exact nextMod_lt_seven (by omega)
        have hor_f := hf_iff.mp hl_f
        rw [hw_pt hzh_lt p1, hS_pt hh7 p2, hS_pt ht7 p3] at hor_f
        have hW_zh : W₀ ⟨zhIdx, hzh_lt⟩ = Finset.univ.erase ⟨ctx.spec.n_d + hi, hh7⟩ := by
          dsimp [W₀, specWitnessEmb]; rw [hzm_val, hzm_eq, maskToFinset_zh_eq_erase hh7]
        rw [hW_zh] at hor_f
        have hor_t := (hzh_sep hi hhi_lt target ht7).2 hright
        unfold PolygonCore.zWitness at hor_t
        rw [hor_t] at hor_f; exact Bool.noConfusion hor_f
    rw [if_neg htag8] at hdec
    by_cases htag9 : (tag == 9) = true
    · -- Tag 9: (C6) General side-corners
      rw [if_pos htag9] at hdec
      obtain ⟨zhIdx, hi, u, v, wIdx, suNat, pairIdx, swNat, _, hdec⟩ := matchNats8 hdec
      cases hgm1 : getMask ctx zhIdx with | none => rw [hgm1] at hdec; nomatch hdec | some zm =>
      cases hgm2 : getMask ctx wIdx with | none => rw [hgm1, hgm2] at hdec; nomatch hdec | some mw =>
      rw [hgm1, hgm2] at hdec; dsimp only at hdec
      obtain ⟨hc, hdec⟩ := ite_none_eq_some hdec
      simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, decide_eq_true_eq] at hc
      rcases hc with ⟨⟨⟨⟨⟨⟨⟨⟨⟨_, hhi_lt⟩, hh7⟩, hzm_eq⟩, huv_lt⟩, hv7⟩, huh⟩, hvh⟩, sm_u⟩, sm_v⟩
      cases hl1 : litForb ctx (suNat == 1) (7 + zhIdx) (ctx.spec.n_d + hi) u with
      | none => rw [hl1] at hdec; nomatch hdec | some l1 =>
      cases hl2 : litForb ctx (!(suNat == 1)) (7 + zhIdx) (ctx.spec.n_d + hi) v with
      | none => rw [hl1, hl2] at hdec; nomatch hdec | some l2 =>
      cases htp : inTriPairLits ctx pairIdx (swNat == 1) (ctx.spec.n_d + hi) (7 + wIdx) u v with
      | none => rw [hl1, hl2, htp] at hdec; nomatch hdec | some ls =>
      rw [hl1, hl2, htp] at hdec
      injection hdec with hp; injection (Prod.mk.inj hp).1 with hcl; subst hcl
      obtain ⟨fl1, r1⟩ := evalClause_cons_false hev
      obtain ⟨fl2, fls⟩ := evalClause_cons_false r1
      obtain ⟨hzh_lt, hzm_val⟩ := getMask_sound hM hm_eq hgm1
      obtain ⟨hw_lt, hmw_val⟩ := getMask_sound hM hm_eq hgm2
      obtain ⟨pz1, ph1, pu1, e1⟩ := litForb_eval_false hX' hval hl1 fl1
      obtain ⟨_, _, pv1, e2⟩ := litForb_eval_false hX' hval hl2 fl2
      have hu7 : u < 7 := by omega
      rw [hw_pt hzh_lt pz1, hS_pt hh7 ph1, hS_pt hu7 pu1] at e1
      rw [hw_pt hzh_lt pz1, hS_pt hh7 ph1, hS_pt hv7 pv1] at e2
      have hW_zh : W₀ ⟨zhIdx, hzh_lt⟩ = Finset.univ.erase ⟨ctx.spec.n_d + hi, hh7⟩ := by
        dsimp [W₀, specWitnessEmb]; rw [hzm_val, hzm_eq, maskToFinset_zh_eq_erase hh7]
      rw [hW_zh] at e1 e2
      have hh_cert : (⟨ctx.spec.n_d + hi, hh7⟩ : Fin 7) ∈ PolygonCore.certifiedSet P S w :=
        (hV.hH_mem ⟨ctx.spec.n_d + hi, hh7⟩).mpr ⟨by dsimp; omega, by dsimp; omega⟩
      have htri := certified_side_corners_general_orientSign_C6 hV.hP (by decide) hh_cert
        (Fin.ne_of_val_ne (i := ⟨u, hu7⟩) (j := ⟨ctx.spec.n_d + hi, hh7⟩) huh)
        (Fin.ne_of_val_ne (i := ⟨v, hv7⟩) (j := ⟨ctx.spec.n_d + hi, hh7⟩) hvh) e1 e2
        (Tw := W₀ ⟨wIdx, hw_lt⟩) (fun z hz => by
          simp only [Finset.mem_insert, Finset.mem_singleton] at hz
          rcases hz with rfl | rfl
          · simp [W₀, specWitnessEmb, hmw_val, sm_u]
          · simp [W₀, specWitnessEmb, hmw_val, sm_v])
      have hw_p : 7 + wIdx < ctx.n_pts := by omega
      have htri_X : inOpenTriBool (X' ⟨ctx.spec.n_d + hi, ph1⟩) (X' ⟨7 + wIdx, hw_p⟩)
          (X' ⟨u, pu1⟩) (X' ⟨v, pv1⟩) = true := by
        rw [hS_pt hh7 ph1, hw_pt hw_lt hw_p, hS_pt hu7 pu1, hS_pt hv7 pv1]
        exact htri
      have htrue := inTriPairLits_sound hX' hval ph1 hw_p pu1 pv1 htri_X htp
      rw [htrue] at fls; exact Bool.noConfusion fls
    rw [if_neg htag9] at hdec
    by_cases htag10 : (tag == 10) = true
    · -- Tag 10: (C8) Asymmetric two-sided separation
      rw [if_pos htag10] at hdec
      obtain ⟨wx, d, u, v, w1, w2, sNat, _, hdec⟩ := matchNats7 hdec
      cases hmx : getMask ctx wx with | none => rw [hmx] at hdec; nomatch hdec | some mx =>
      cases hm1 : getMask ctx w1 with | none => rw [hmx, hm1] at hdec; nomatch hdec | some m1 =>
      cases hm2 : getMask ctx w2 with | none => rw [hmx, hm1, hm2] at hdec; nomatch hdec | some m2 =>
      rw [hmx, hm1, hm2] at hdec; dsimp only at hdec
      obtain ⟨hc, hdec⟩ := ite_none_eq_some hdec
      simp only [Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne, decide_eq_true_eq] at hc
      rcases hc with ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hd7, hu7⟩, hv7⟩, _⟩, sxd⟩, sxu⟩, sxv⟩, s1d⟩, s1u⟩, s2d⟩, s2v⟩
      cases hlo : optSequence [litForb ctx (sNat == 1) d (7 + wx) u,
          litForb ctx (!(sNat == 1)) d (7 + wx) v,
          litForb ctx (sNat == 1) d (7 + wx) (7 + w1),
          litForb ctx (!(sNat == 1)) d (7 + wx) (7 + w2)] with
      | none => rw [hlo] at hdec; nomatch hdec | some cl' =>
      rw [hlo] at hdec
      injection hdec with hp; injection (Prod.mk.inj hp).1 with hcl; subst hcl
      obtain ⟨hwx_lt, hmx_v⟩ := getMask_sound hM hm_eq hmx
      obtain ⟨hw1_lt, hm1_v⟩ := getMask_sound hM hm_eq hm1
      obtain ⟨hw2_lt, hm2_v⟩ := getMask_sound hM hm_eq hm2
      obtain ⟨_, _, _, _, o1, o2, o3, o4, f1, f2, f3, f4⟩ := optSeq4_false hlo hev
      obtain ⟨pd, pwx, pu, e1⟩ := litForb_eval_false hX' hval o1 f1
      obtain ⟨_, _, pv, e2⟩ := litForb_eval_false hX' hval o2 f2
      obtain ⟨_, _, pw1, e3⟩ := litForb_eval_false hX' hval o3 f3
      obtain ⟨_, _, pw2, e4⟩ := litForb_eval_false hX' hval o4 f4
      rw [hS_pt hd7 pd, hw_pt hwx_lt pwx, hS_pt hu7 pu] at e1
      rw [hS_pt hd7 pd, hw_pt hwx_lt pwx, hS_pt hv7 pv] at e2
      rw [hS_pt hd7 pd, hw_pt hwx_lt pwx, hw_pt hw1_lt pw1] at e3
      rw [hS_pt hd7 pd, hw_pt hwx_lt pwx, hw_pt hw2_lt pw2] at e4
      exact asymmetric_two_sided_clause_C8 hV.hP
        (by simp [W₀, specWitnessEmb, hmx_v, sxd]) (by simp [W₀, specWitnessEmb, hmx_v, sxu]) (by simp [W₀, specWitnessEmb, hmx_v, sxv])
        (by simp [W₀, specWitnessEmb, hm1_v, s1d]) (by simp [W₀, specWitnessEmb, hm1_v, s1u])
        (by simp [W₀, specWitnessEmb, hm2_v, s2d]) (by simp [W₀, specWitnessEmb, hm2_v, s2v])
        (sNat == 1) ⟨e1, e2, e3, e4⟩
    rw [if_neg htag10] at hdec
    by_cases htag11 : (tag == 11) = true
    · rw [if_pos htag11] at hdec
      exact sound_tag_11 hV.hP hM hm_eq hX' hS_pt hw_pt hval hev hdec
    rw [if_neg htag11] at hdec
    by_cases htag12 : (tag == 12) = true
    · -- Tag 12: (C11) vis_SS Round-2 vertex clause
      rw [if_pos htag12] at hdec
      obtain ⟨a, b, w1, w2, w3, wf, soppNat, sdNat, _, hdec⟩ := matchNats8 hdec
      cases hm1 : getMask ctx w1 with | none => rw [hm1] at hdec; nomatch hdec | some m1 =>
      cases hm2 : getMask ctx w2 with | none => rw [hm1, hm2] at hdec; nomatch hdec | some m2 =>
      cases hm3 : getMask ctx w3 with | none => rw [hm1, hm2, hm3] at hdec; nomatch hdec | some m3 =>
      cases hmf : getMask ctx wf with | none => rw [hm1, hm2, hm3, hmf] at hdec; nomatch hdec | some mf =>
      rw [hm1, hm2, hm3, hmf] at hdec; dsimp only at hdec
      obtain ⟨hc, hdec⟩ := ite_none_eq_some hdec
      simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hc
      rcases hc with ⟨⟨⟨⟨⟨⟨⟨⟨hab_lt, hb7⟩, s1a⟩, s1b⟩, s2a⟩, s2b⟩, s3a⟩, s3b⟩, hmiss_b⟩
      cases hl1 : litForb ctx (soppNat == 1) a b (7 + w1) with | none => rw [hl1] at hdec; nomatch hdec | some l1 =>
      cases hl2 : litForb ctx (!(soppNat == 1)) a b (7 + w2) with | none => rw [hl1, hl2] at hdec; nomatch hdec | some l2 =>
      cases hnt : notInTriSideLits ctx (sdNat == 1) (7 + wf) (7 + w3) a b with
      | none => rw [hl1, hl2, hnt] at hdec; nomatch hdec | some ls =>
      rw [hl1, hl2, hnt] at hdec
      injection hdec with hp_; injection (Prod.mk.inj hp_).1 with hcl; subst hcl
      obtain ⟨fl1, r1⟩ := evalClause_cons_false hev; obtain ⟨fl2, fls⟩ := evalClause_cons_false r1
      obtain ⟨hw1_lt, hm1_v⟩ := getMask_sound hM hm_eq hm1
      obtain ⟨hw2_lt, hm2_v⟩ := getMask_sound hM hm_eq hm2
      obtain ⟨hw3_lt, hm3_v⟩ := getMask_sound hM hm_eq hm3
      obtain ⟨hwf_lt, hmf_v⟩ := getMask_sound hM hm_eq hmf
      obtain ⟨pa, pb_, pw1, e1⟩ := litForb_eval_false hX' hval hl1 fl1
      obtain ⟨_, _, pw2, e2⟩ := litForb_eval_false hX' hval hl2 fl2
      obtain ⟨pwf, pw3, _, _, hside⟩ := notInTriSideLits_eval_false hX' hval hnt fls
      have ha7 : a < 7 := by omega
      rw [hS_pt ha7 pa, hS_pt hb7 pb_, hw_pt hw1_lt pw1] at e1
      rw [hS_pt ha7 pa, hS_pt hb7 pb_, hw_pt hw2_lt pw2] at e2
      rw [hw_pt hwf_lt pwf, hw_pt hw3_lt pw3, hS_pt ha7 pa, hS_pt hb7 pb_] at hside
      exact vis_SS_tri_vertex_omitted_outer_clause hV.hP
        (a := ⟨a, ha7⟩) (b := ⟨b, hb7⟩)
        (T₁ := W₀ ⟨w1, hw1_lt⟩) (T₂ := W₀ ⟨w2, hw2_lt⟩) (T₃ := W₀ ⟨w3, hw3_lt⟩) (Tf := W₀ ⟨wf, hwf_lt⟩)
        (Fin.ne_of_val_ne (by dsimp; omega))
        (by simp [W₀, specWitnessEmb, hm1_v, s1a]) (by simp [W₀, specWitnessEmb, hm1_v, s1b])
        (by simp [W₀, specWitnessEmb, hm2_v, s2a]) (by simp [W₀, specWitnessEmb, hm2_v, s2b])
        (by simp [W₀, specWitnessEmb, hm3_v, s3a]) (by simp [W₀, specWitnessEmb, hm3_v, s3b])
        (by rcases hmiss_b with hma | hmb
            · exact Or.inl (by simp [W₀, specWitnessEmb, hmf_v, hma])
            · exact Or.inr (by simp [W₀, specWitnessEmb, hmf_v, hmb]))
        (sdNat == 1) ⟨oppSideBool_of_eq_not e1 e2, hside⟩
    rw [if_neg htag12] at hdec
    by_cases htag13 : (tag == 13) = true
    · -- Tag 13: (C11) vis_SS Round-2 pair clause
      rw [if_pos htag13] at hdec
      obtain ⟨a, b, fj, w1, w2, w3, wf, soppNat, sdwNat, sdjNat, _, hdec⟩ := matchNats10 hdec
      cases hm1 : getMask ctx w1 with | none => rw [hm1] at hdec; nomatch hdec | some m1 =>
      cases hm2 : getMask ctx w2 with | none => rw [hm1, hm2] at hdec; nomatch hdec | some m2 =>
      cases hm3 : getMask ctx w3 with | none => rw [hm1, hm2, hm3] at hdec; nomatch hdec | some m3 =>
      cases hmf : getMask ctx wf with | none => rw [hm1, hm2, hm3, hmf] at hdec; nomatch hdec | some mf =>
      rw [hm1, hm2, hm3, hmf] at hdec; dsimp only at hdec
      obtain ⟨hc, hdec⟩ := ite_none_eq_some hdec
      simp only [Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne, decide_eq_true_eq] at hc
      rcases hc with ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hab_lt, hb7⟩, hfj7⟩, hfja⟩, hfjb⟩, hw3f⟩, s1a⟩, s1b⟩, s2a⟩, s2b⟩, s3a⟩, s3b⟩, sfj_n⟩
      cases hl1 : litForb ctx (soppNat == 1) a b (7 + w1) with | none => rw [hl1] at hdec; nomatch hdec | some l1 =>
      cases hl2 : litForb ctx (!(soppNat == 1)) a b (7 + w2) with | none => rw [hl1, hl2] at hdec; nomatch hdec | some l2 =>
      cases hntw : notInTriSideLits ctx (sdwNat == 1) (7 + wf) (7 + w3) a b with
      | none => rw [hl1, hl2, hntw] at hdec; nomatch hdec | some lsw =>
      cases hntj : notInTriSideLits ctx (sdjNat == 1) fj (7 + w3) a b with
      | none => rw [hl1, hl2, hntw, hntj] at hdec; nomatch hdec | some lsj =>
      rw [hl1, hl2, hntw, hntj] at hdec
      injection hdec with hp_; injection (Prod.mk.inj hp_).1 with hcl; subst hcl
      obtain ⟨fl1, r1⟩ := evalClause_cons_false hev; obtain ⟨fl2, r2⟩ := evalClause_cons_false r1
      obtain ⟨flsw, flsj⟩ := evalClause_append_false r2
      obtain ⟨hw1_lt, hm1_v⟩ := getMask_sound hM hm_eq hm1
      obtain ⟨hw2_lt, hm2_v⟩ := getMask_sound hM hm_eq hm2
      obtain ⟨hw3_lt, hm3_v⟩ := getMask_sound hM hm_eq hm3
      obtain ⟨hwf_lt, hmf_v⟩ := getMask_sound hM hm_eq hmf
      obtain ⟨pa, pb_, pw1, e1⟩ := litForb_eval_false hX' hval hl1 fl1
      obtain ⟨_, _, pw2, e2⟩ := litForb_eval_false hX' hval hl2 fl2
      obtain ⟨pwf, pw3, _, _, hsidew⟩ := notInTriSideLits_eval_false hX' hval hntw flsw
      obtain ⟨pfj, _, _, _, hsidej⟩ := notInTriSideLits_eval_false hX' hval hntj flsj
      have ha7 : a < 7 := by omega
      rw [hS_pt ha7 pa, hS_pt hb7 pb_, hw_pt hw1_lt pw1] at e1
      rw [hS_pt ha7 pa, hS_pt hb7 pb_, hw_pt hw2_lt pw2] at e2
      rw [hw_pt hwf_lt pwf, hw_pt hw3_lt pw3, hS_pt ha7 pa, hS_pt hb7 pb_] at hsidew
      rw [hS_pt hfj7 pfj, hw_pt hw3_lt pw3, hS_pt ha7 pa, hS_pt hb7 pb_] at hsidej
      exact vis_SS_tri_pair_clause hV.hP
        (a := ⟨a, ha7⟩) (b := ⟨b, hb7⟩) (fj := ⟨fj, hfj7⟩)
        (T₁ := W₀ ⟨w1, hw1_lt⟩) (T₂ := W₀ ⟨w2, hw2_lt⟩) (T₃ := W₀ ⟨w3, hw3_lt⟩) (Tf := W₀ ⟨wf, hwf_lt⟩)
        (Fin.ne_of_val_ne (by dsimp; omega))
        (Fin.ne_of_val_ne hfja) (Fin.ne_of_val_ne hfjb)
        (W₀.injective.ne (Fin.ne_of_val_ne hw3f))
        (by simp [W₀, specWitnessEmb, hm1_v, s1a]) (by simp [W₀, specWitnessEmb, hm1_v, s1b])
        (by simp [W₀, specWitnessEmb, hm2_v, s2a]) (by simp [W₀, specWitnessEmb, hm2_v, s2b])
        (by simp [W₀, specWitnessEmb, hm3_v, s3a]) (by simp [W₀, specWitnessEmb, hm3_v, s3b])
        (by simp [W₀, specWitnessEmb, hmf_v, sfj_n])
        ⟨oppSideBool_of_eq_not e1 e2,
         inOpenTriBool_of_side hsidew,
         inOpenTriBool_of_side hsidej⟩
    rw [if_neg htag13] at hdec
    by_cases htag14 : (tag == 14) = true
    · -- Tag 14: (C10) N1 convex quad
      rw [if_pos htag14] at hdec
      obtain ⟨a, b, w1, w2, wf, sNat, _, hdec⟩ := matchNats6 hdec
      cases hm1 : getMask ctx w1 with | none => rw [hm1] at hdec; nomatch hdec | some m1 =>
      cases hm2 : getMask ctx w2 with | none => rw [hm1, hm2] at hdec; nomatch hdec | some m2 =>
      cases hmf : getMask ctx wf with | none => rw [hm1, hm2, hmf] at hdec; nomatch hdec | some mf =>
      rw [hm1, hm2, hmf] at hdec; dsimp only at hdec
      obtain ⟨hc, hdec⟩ := ite_none_eq_some hdec
      simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', bne_iff_ne, decide_eq_true_eq] at hc
      rcases hc with ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨ha7, hb7⟩, hab⟩, hw12⟩, hwf1⟩, hwf2⟩, s1a⟩, s1b⟩, s2a⟩, s2b⟩, hmiss_b⟩
      cases hlo : optSequence [litForb ctx (sNat == 1) (7 + w1) a (7 + w2),
          litForb ctx (sNat == 1) a (7 + w2) b, litForb ctx (sNat == 1) (7 + w2) b (7 + w1),
          litForb ctx (sNat == 1) b (7 + w1) a, litForb ctx (sNat == 1) (7 + w1) a (7 + wf),
          litForb ctx (sNat == 1) a (7 + w2) (7 + wf), litForb ctx (sNat == 1) (7 + w2) b (7 + wf),
          litForb ctx (sNat == 1) b (7 + w1) (7 + wf)] with
      | none => rw [hlo] at hdec; nomatch hdec | some cl' =>
      rw [hlo] at hdec
      injection hdec with hp_; injection (Prod.mk.inj hp_).1 with hcl; subst hcl
      obtain ⟨hw1_lt, hm1_v⟩ := getMask_sound hM hm_eq hm1
      obtain ⟨hw2_lt, hm2_v⟩ := getMask_sound hM hm_eq hm2
      obtain ⟨hwf_lt, hmf_v⟩ := getMask_sound hM hm_eq hmf
      obtain ⟨_, _, _, _, _, _, _, _, o1, o2, o3, o4, o5, o6, o7, o8, f1, f2, f3, f4, f5, f6, f7, f8⟩ := optSeq8_false hlo hev
      obtain ⟨pw1, pa, pw2, e1⟩ := litForb_eval_false hX' hval o1 f1
      obtain ⟨_, _, pb_, e2⟩ := litForb_eval_false hX' hval o2 f2
      obtain ⟨_, _, _, e3⟩ := litForb_eval_false hX' hval o3 f3
      obtain ⟨_, _, _, e4⟩ := litForb_eval_false hX' hval o4 f4
      obtain ⟨_, _, pwf, e5⟩ := litForb_eval_false hX' hval o5 f5
      obtain ⟨_, _, _, e6⟩ := litForb_eval_false hX' hval o6 f6
      obtain ⟨_, _, _, e7⟩ := litForb_eval_false hX' hval o7 f7
      obtain ⟨_, _, _, e8⟩ := litForb_eval_false hX' hval o8 f8
      rw [hw_pt hw1_lt pw1, hS_pt ha7 pa, hw_pt hw2_lt pw2] at e1
      rw [hS_pt ha7 pa, hw_pt hw2_lt pw2, hS_pt hb7 pb_] at e2
      rw [hw_pt hw2_lt pw2, hS_pt hb7 pb_, hw_pt hw1_lt pw1] at e3
      rw [hS_pt hb7 pb_, hw_pt hw1_lt pw1, hS_pt ha7 pa] at e4
      rw [hw_pt hw1_lt pw1, hS_pt ha7 pa, hw_pt hwf_lt pwf] at e5
      rw [hS_pt ha7 pa, hw_pt hw2_lt pw2, hw_pt hwf_lt pwf] at e6
      rw [hw_pt hw2_lt pw2, hS_pt hb7 pb_, hw_pt hwf_lt pwf] at e7
      rw [hS_pt hb7 pb_, hw_pt hw1_lt pw1, hw_pt hwf_lt pwf] at e8
      exact n1_convex_quad_vertex_clause hV.hP
        (a := ⟨a, ha7⟩) (b := ⟨b, hb7⟩)
        (T₁ := W₀ ⟨w1, hw1_lt⟩) (T₂ := W₀ ⟨w2, hw2_lt⟩) (Tf := W₀ ⟨wf, hwf_lt⟩)
        (Fin.ne_of_val_ne hab)
        (W₀.injective.ne (Fin.ne_of_val_ne hw12))
        (W₀.injective.ne (Fin.ne_of_val_ne hwf1))
        (W₀.injective.ne (Fin.ne_of_val_ne hwf2))
        (by simp [W₀, specWitnessEmb, hm1_v, s1a]) (by simp [W₀, specWitnessEmb, hm1_v, s1b])
        (by simp [W₀, specWitnessEmb, hm2_v, s2a]) (by simp [W₀, specWitnessEmb, hm2_v, s2b])
        (by rcases hmiss_b with hma | hmb
            · exact Or.inl (by simp [W₀, specWitnessEmb, hmf_v, hma])
            · exact Or.inr (by simp [W₀, specWitnessEmb, hmf_v, hmb]))
        (sNat == 1) ⟨by unfold strictConvexQuadSideBool; simp [e1, e2, e3, e4],
                     by unfold inConvexQuadSideBool; simp [e5, e6, e7, e8]⟩
    rw [if_neg htag14] at hdec
    by_cases htag1517 : (tag == 15 || tag == 17) = true
    · -- Tag 15 (r=0) / Tag 17 (r=2): N1 dart with sameSide
      rw [if_pos htag1517] at hdec
      obtain ⟨a, b, w1, w2, wf, sdNat, ssNat, _, hdec⟩ := matchNats7 hdec
      cases hm1 : getMask ctx w1 with | none => rw [hm1] at hdec; nomatch hdec | some m1 =>
      cases hm2 : getMask ctx w2 with | none => rw [hm1, hm2] at hdec; nomatch hdec | some m2 =>
      cases hmf : getMask ctx wf with | none => rw [hm1, hm2, hmf] at hdec; nomatch hdec | some mf =>
      rw [hm1, hm2, hmf] at hdec; dsimp only at hdec
      obtain ⟨hc, hdec⟩ := ite_none_eq_some hdec
      simp only [Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne, decide_eq_true_eq] at hc
      rcases hc with ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨ha7, hb7⟩, hab⟩, hw12⟩, hwf1⟩, hwf2⟩, s1a⟩, s1b⟩, s2a⟩, s2b⟩, sfa_n⟩
      revert hdec
      generalize hn1_g : notInTriSideLits ctx (sdNat == 1) (if (tag == 15) = true then 7 + w1 else 7 + w2)
          (if (tag == 15) = true then a else b) (if (tag == 15) = true then 7 + w2 else 7 + w1)
          (if (tag == 15) = true then b else a) = o1
      generalize hn2_g : notInTriSideLits ctx (sdNat == 1) (7 + wf) (if (tag == 15) = true then a else b)
          (if (tag == 15) = true then 7 + w2 else 7 + w1) (if (tag == 15) = true then b else a) = o2
      generalize hl3_g : litForb ctx (ssNat == 1) (if (tag == 15) = true then 7 + w1 else 7 + w2) a (7 + wf) = o3
      generalize hl4_g : litForb ctx (ssNat == 1) (if (tag == 15) = true then 7 + w1 else 7 + w2) a
          (if (tag == 15) = true then 7 + w2 else 7 + w1) = o4
      intro hdec
      cases o1 with | none => nomatch hdec | some ls1 =>
      cases o2 with | none => nomatch hdec | some ls2 =>
      cases o3 with | none => nomatch hdec | some l3 =>
      cases o4 with | none => nomatch hdec | some l4 =>
      have hn1 := hn1_g; have hn2 := hn2_g; have hl3 := hl3_g; have hl4 := hl4_g
      injection hdec with hp_; injection (Prod.mk.inj hp_).1 with hcl; subst hcl
      obtain ⟨hw1_lt, hm1_v⟩ := getMask_sound hM hm_eq hm1
      obtain ⟨hw2_lt, hm2_v⟩ := getMask_sound hM hm_eq hm2
      obtain ⟨hwf_lt, hmf_v⟩ := getMask_sound hM hm_eq hmf
      obtain ⟨fls12, fl34⟩ := evalClause_append_false hev
      obtain ⟨fls1, fls2⟩ := evalClause_append_false fls12
      obtain ⟨fl3, r3⟩ := evalClause_cons_false fl34; obtain ⟨fl4, _⟩ := evalClause_cons_false r3
      by_cases ht15 : (tag == 15) = true
      · simp only [ht15, ↓reduceIte] at hn1 hn2 hl3 hl4
        obtain ⟨pw1, pa, pw2, pb_, hs1⟩ := notInTriSideLits_eval_false hX' hval hn1 fls1
        obtain ⟨pwf, _, _, _, hs2⟩ := notInTriSideLits_eval_false hX' hval hn2 fls2
        obtain ⟨_, _, _, e3⟩ := litForb_eval_false hX' hval hl3 fl3
        obtain ⟨_, _, _, e4⟩ := litForb_eval_false hX' hval hl4 fl4
        rw [hw_pt hw1_lt pw1, hS_pt ha7 pa, hw_pt hw2_lt pw2, hS_pt hb7 pb_] at hs1
        rw [hw_pt hwf_lt pwf, hS_pt ha7 pa, hw_pt hw2_lt pw2, hS_pt hb7 pb_] at hs2
        rw [hw_pt hw1_lt pw1, hS_pt ha7 pa, hw_pt hwf_lt pwf] at e3
        rw [hw_pt hw1_lt pw1, hS_pt ha7 pa, hw_pt hw2_lt pw2] at e4
        exact n1_dart_r0_clause hV.hP
          (a := ⟨a, ha7⟩) (b := ⟨b, hb7⟩)
          (T₁ := W₀ ⟨w1, hw1_lt⟩) (T₂ := W₀ ⟨w2, hw2_lt⟩) (Tf := W₀ ⟨wf, hwf_lt⟩)
          (Fin.ne_of_val_ne hab)
          (W₀.injective.ne (Fin.ne_of_val_ne hw12)) (W₀.injective.ne (Fin.ne_of_val_ne hwf1))
          (W₀.injective.ne (Fin.ne_of_val_ne hwf2))
          (by simp [W₀, specWitnessEmb, hm1_v, s1a]) (by simp [W₀, specWitnessEmb, hm1_v, s1b])
          (by simp [W₀, specWitnessEmb, hm2_v, s2a]) (by simp [W₀, specWitnessEmb, hm2_v, s2b])
          (by simp [W₀, specWitnessEmb, hmf_v, sfa_n]) (sdNat == 1)
          ⟨hs1, hs2, by unfold sameSideBool; rw [e3, e4, beq_self_eq_true]⟩
      · simp only [ht15, Bool.false_eq_true, ↓reduceIte] at hn1 hn2 hl3 hl4
        obtain ⟨pw2, pb_, pw1, pa, hs1⟩ := notInTriSideLits_eval_false hX' hval hn1 fls1
        obtain ⟨pwf, _, _, _, hs2⟩ := notInTriSideLits_eval_false hX' hval hn2 fls2
        obtain ⟨_, _, _, e3⟩ := litForb_eval_false hX' hval hl3 fl3
        obtain ⟨_, _, _, e4⟩ := litForb_eval_false hX' hval hl4 fl4
        rw [hw_pt hw2_lt pw2, hS_pt hb7 pb_, hw_pt hw1_lt pw1, hS_pt ha7 pa] at hs1
        rw [hw_pt hwf_lt pwf, hS_pt hb7 pb_, hw_pt hw1_lt pw1, hS_pt ha7 pa] at hs2
        rw [hw_pt hw2_lt pw2, hS_pt ha7 pa, hw_pt hwf_lt pwf] at e3
        rw [hw_pt hw2_lt pw2, hS_pt ha7 pa, hw_pt hw1_lt pw1] at e4
        exact n1_dart_r2_clause hV.hP
          (a := ⟨a, ha7⟩) (b := ⟨b, hb7⟩)
          (T₁ := W₀ ⟨w1, hw1_lt⟩) (T₂ := W₀ ⟨w2, hw2_lt⟩) (Tf := W₀ ⟨wf, hwf_lt⟩)
          (Fin.ne_of_val_ne hab)
          (W₀.injective.ne (Fin.ne_of_val_ne hw12)) (W₀.injective.ne (Fin.ne_of_val_ne hwf1))
          (W₀.injective.ne (Fin.ne_of_val_ne hwf2))
          (by simp [W₀, specWitnessEmb, hm1_v, s1a]) (by simp [W₀, specWitnessEmb, hm1_v, s1b])
          (by simp [W₀, specWitnessEmb, hm2_v, s2a]) (by simp [W₀, specWitnessEmb, hm2_v, s2b])
          (by simp [W₀, specWitnessEmb, hmf_v, sfa_n]) (sdNat == 1)
          ⟨hs1, hs2, by unfold sameSideBool; rw [e3, e4, beq_self_eq_true]⟩
    rw [if_neg htag1517] at hdec
    by_cases htag1618 : (tag == 16 || tag == 18) = true
    · -- Tag 16 (r=1) / Tag 18 (r=3): N1 dart sub-triangle
      rw [if_pos htag1618] at hdec
      obtain ⟨a, b, w1, w2, wf, sdNat, stNat, subIdx, _, hdec⟩ := matchNats8 hdec
      cases hm1 : getMask ctx w1 with | none => rw [hm1] at hdec; nomatch hdec | some m1 =>
      cases hm2 : getMask ctx w2 with | none => rw [hm1, hm2] at hdec; nomatch hdec | some m2 =>
      cases hmf : getMask ctx wf with | none => rw [hm1, hm2, hmf] at hdec; nomatch hdec | some mf =>
      rw [hm1, hm2, hmf] at hdec; dsimp only at hdec
      obtain ⟨hc, hdec⟩ := ite_none_eq_some hdec
      simp only [Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne, decide_eq_true_eq] at hc
      rcases hc with ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨ha7, hb7⟩, hab⟩, hw12⟩, hwf1⟩, hwf2⟩, s1a⟩, s1b⟩, s2a⟩, s2b⟩, sfa_n⟩
      revert hdec
      generalize hn1_g : notInTriSideLits ctx (sdNat == 1) (if (tag == 16) = true then a else b)
          (if (tag == 16) = true then 7 + w2 else 7 + w1) (if (tag == 16) = true then b else a)
          (if (tag == 16) = true then 7 + w1 else 7 + w2) = o1
      generalize hn2_g : (if (subIdx == 0) = true then _ else _) = o2
      intro hdec
      cases o1 with | none => nomatch hdec | some ls1 =>
      cases o2 with | none => nomatch hdec | some ls2 =>
      have hn1 := hn1_g; have hn2 := hn2_g
      injection hdec with hp_; injection (Prod.mk.inj hp_).1 with hcl; subst hcl
      obtain ⟨hw1_lt, hm1_v⟩ := getMask_sound hM hm_eq hm1
      obtain ⟨hw2_lt, hm2_v⟩ := getMask_sound hM hm_eq hm2
      obtain ⟨hwf_lt, hmf_v⟩ := getMask_sound hM hm_eq hmf
      obtain ⟨fls1, fls2⟩ := evalClause_append_false hev
      by_cases ht16 : (tag == 16) = true
      · simp only [ht16, ↓reduceIte] at hn1 hn2
        obtain ⟨pa, pw2, pb_, pw1, hd1⟩ := notInTriSideLits_eval_false hX' hval hn1 fls1
        rw [hS_pt ha7 pa, hw_pt hw2_lt pw2, hS_pt hb7 pb_, hw_pt hw1_lt pw1] at hd1
        by_cases hs0 : (subIdx == 0) = true
        · rw [if_pos hs0] at hn2
          obtain ⟨pwf, _, _, _, hd2⟩ := notInTriSideLits_eval_false hX' hval hn2 fls2
          rw [hw_pt hwf_lt pwf, hS_pt ha7 pa, hw_pt hw2_lt pw2, hS_pt hb7 pb_] at hd2
          exact n1_dart_r1_clause hV.hP
            (a := ⟨a, ha7⟩) (b := ⟨b, hb7⟩)
            (T₁ := W₀ ⟨w1, hw1_lt⟩) (T₂ := W₀ ⟨w2, hw2_lt⟩) (Tf := W₀ ⟨wf, hwf_lt⟩)
            (Fin.ne_of_val_ne hab)
            (W₀.injective.ne (Fin.ne_of_val_ne hw12)) (W₀.injective.ne (Fin.ne_of_val_ne hwf1))
            (W₀.injective.ne (Fin.ne_of_val_ne hwf2))
            (by simp [W₀, specWitnessEmb, hm1_v, s1a]) (by simp [W₀, specWitnessEmb, hm1_v, s1b])
            (by simp [W₀, specWitnessEmb, hm2_v, s2a]) (by simp [W₀, specWitnessEmb, hm2_v, s2b])
            (by simp [W₀, specWitnessEmb, hmf_v, sfa_n]) (sdNat == 1) (stNat == 1) ⟨hd1, Or.inl hd2⟩
        · rw [if_neg hs0] at hn2
          by_cases hs1_b : (subIdx == 1) = true
          · rw [if_pos hs1_b] at hn2
            obtain ⟨pwf, _, _, _, hd2⟩ := notInTriSideLits_eval_false hX' hval hn2 fls2
            rw [hw_pt hwf_lt pwf, hS_pt ha7 pa, hS_pt hb7 pb_, hw_pt hw1_lt pw1] at hd2
            exact n1_dart_r1_clause hV.hP
              (a := ⟨a, ha7⟩) (b := ⟨b, hb7⟩)
              (T₁ := W₀ ⟨w1, hw1_lt⟩) (T₂ := W₀ ⟨w2, hw2_lt⟩) (Tf := W₀ ⟨wf, hwf_lt⟩)
              (Fin.ne_of_val_ne hab)
              (W₀.injective.ne (Fin.ne_of_val_ne hw12)) (W₀.injective.ne (Fin.ne_of_val_ne hwf1))
              (W₀.injective.ne (Fin.ne_of_val_ne hwf2))
              (by simp [W₀, specWitnessEmb, hm1_v, s1a]) (by simp [W₀, specWitnessEmb, hm1_v, s1b])
              (by simp [W₀, specWitnessEmb, hm2_v, s2a]) (by simp [W₀, specWitnessEmb, hm2_v, s2b])
              (by simp [W₀, specWitnessEmb, hmf_v, sfa_n]) (sdNat == 1) (stNat == 1) ⟨hd1, Or.inr hd2⟩
          · rw [if_neg hs1_b] at hn2; nomatch hn2
      · simp only [ht16, Bool.false_eq_true, ↓reduceIte] at hn1 hn2
        obtain ⟨pb_, pw1, pa, pw2, hd1⟩ := notInTriSideLits_eval_false hX' hval hn1 fls1
        rw [hS_pt hb7 pb_, hw_pt hw1_lt pw1, hS_pt ha7 pa, hw_pt hw2_lt pw2] at hd1
        by_cases hs0 : (subIdx == 0) = true
        · rw [if_pos hs0] at hn2
          obtain ⟨pwf, _, _, _, hd2⟩ := notInTriSideLits_eval_false hX' hval hn2 fls2
          rw [hw_pt hwf_lt pwf, hS_pt hb7 pb_, hw_pt hw1_lt pw1, hS_pt ha7 pa] at hd2
          exact n1_dart_r3_clause hV.hP
            (a := ⟨a, ha7⟩) (b := ⟨b, hb7⟩)
            (T₁ := W₀ ⟨w1, hw1_lt⟩) (T₂ := W₀ ⟨w2, hw2_lt⟩) (Tf := W₀ ⟨wf, hwf_lt⟩)
            (Fin.ne_of_val_ne hab)
            (W₀.injective.ne (Fin.ne_of_val_ne hw12)) (W₀.injective.ne (Fin.ne_of_val_ne hwf1))
            (W₀.injective.ne (Fin.ne_of_val_ne hwf2))
            (by simp [W₀, specWitnessEmb, hm1_v, s1a]) (by simp [W₀, specWitnessEmb, hm1_v, s1b])
            (by simp [W₀, specWitnessEmb, hm2_v, s2a]) (by simp [W₀, specWitnessEmb, hm2_v, s2b])
            (by simp [W₀, specWitnessEmb, hmf_v, sfa_n]) (sdNat == 1) (stNat == 1) ⟨hd1, Or.inl hd2⟩
        · rw [if_neg hs0] at hn2
          by_cases hs1_b : (subIdx == 1) = true
          · rw [if_pos hs1_b] at hn2
            obtain ⟨pwf, _, _, _, hd2⟩ := notInTriSideLits_eval_false hX' hval hn2 fls2
            rw [hw_pt hwf_lt pwf, hS_pt hb7 pb_, hS_pt ha7 pa, hw_pt hw2_lt pw2] at hd2
            exact n1_dart_r3_clause hV.hP
              (a := ⟨a, ha7⟩) (b := ⟨b, hb7⟩)
              (T₁ := W₀ ⟨w1, hw1_lt⟩) (T₂ := W₀ ⟨w2, hw2_lt⟩) (Tf := W₀ ⟨wf, hwf_lt⟩)
              (Fin.ne_of_val_ne hab)
              (W₀.injective.ne (Fin.ne_of_val_ne hw12)) (W₀.injective.ne (Fin.ne_of_val_ne hwf1))
              (W₀.injective.ne (Fin.ne_of_val_ne hwf2))
              (by simp [W₀, specWitnessEmb, hm1_v, s1a]) (by simp [W₀, specWitnessEmb, hm1_v, s1b])
              (by simp [W₀, specWitnessEmb, hm2_v, s2a]) (by simp [W₀, specWitnessEmb, hm2_v, s2b])
              (by simp [W₀, specWitnessEmb, hmf_v, sfa_n]) (sdNat == 1) (stNat == 1) ⟨hd1, Or.inr hd2⟩
          · rw [if_neg hs1_b] at hn2; nomatch hn2
    rw [if_neg htag1618] at hdec
    by_cases htag19 : (tag == 19) = true
    · -- Tag 19: (C11) IteratedCut mini-DAG
      rw [if_pos htag19] at hdec
      cases hn : bsReadNat cs1 with
      | none => rw [hn] at hdec; nomatch hdec
      | some pn =>
      rcases pn with ⟨numSteps, cs2⟩; rw [hn] at hdec; dsimp only at hdec
      cases hd : decodeIteratedSteps ctx numSteps .leaf [] cs2 with
      | none => rw [hd] at hdec; nomatch hdec
      | some pd =>
      rcases pd with ⟨et, lits, cs3⟩; rw [hd] at hdec; dsimp only at hdec
      obtain ⟨forbS, forbWIdx, _, hdec⟩ := matchNats2 hdec
      cases hmf : getMask ctx forbWIdx with | none => rw [hmf] at hdec; nomatch hdec | some mf =>
      rw [hmf] at hdec; dsimp only at hdec
      obtain ⟨hc, hdec⟩ := ite_none_eq_some hdec
      simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hc
      rcases hc with ⟨⟨hfs7, hfs_miss⟩, hvis_end⟩
      injection hdec with hp_; injection (Prod.mk.inj hp_).1 with hcl; subst hcl
      obtain ⟨hwf_lt, hmf_v⟩ := getMask_sound hM hm_eq hmf
      have het_all := decodeIteratedSteps_sound hV.hP hM hm_eq hn_pts hval numSteps .leaf et [] lits cs2 cs3 hd hev
        (fun a b ha hb hv => base_hasVisEdge_sound hV.hP hM hm_eq hn_pts ha hb hv)
      have hsees := het_all forbS (7 + forbWIdx) (by omega) (by omega) hvis_end
      rw [pointSeq_S_eq S w W₀ hfs7, pointSeq_w_eq S w W₀ hwf_lt] at hsees
      have h_in := (hV.hP.shatters (W₀ ⟨forbWIdx, hwf_lt⟩) ⟨forbS, hfs7⟩).mp (sees_symm hsees)
      simp [W₀, specWitnessEmb, hmf_v, hfs_miss] at h_in
    · rw [if_neg htag19] at hdec; nomatch hdec
  · rfl

private lemma stepCoreClause_sound {P : Set (ℝ × ℝ)} {S : Fin 7 → ℝ × ℝ} {w : Finset (Fin 7) → ℝ × ℝ}
    {ctx : CertCtx}
    (hV : ValidCanonicalInstance P S w ctx.spec)
    (hM : ValidMasks ctx.spec.masks)
    (hn_pts : ctx.n_pts = 7 + ctx.spec.masks.length)
    (hbccw_eq : ctx.bccw = buildBccw ctx.spec)
    (hm_eq : ctx.maskTrie = buildMaskTrieAux .xH ctx.spec.masks .leaf)
    {val : PIdx → Bool}
    (hval : ∀ {i j k : ℕ} (hij : i < j) (hjk : j < k) (hk : k < ctx.n_pts) {v : PIdx},
      ctx.tripleTrie.get3 (ptKey i) (ptKey j) (ptKey k) = some v →
      val v = orientSign (pointSeq S w (specWitnessEmb hM) ⟨i, by omega⟩)
                         (pointSeq S w (specWitnessEmb hM) ⟨j, by omega⟩)
                         (pointSeq S w (specWitnessEmb hM) ⟨k, by omega⟩))
    {cid cid' : PIdx} {db db' : BinTrie Clause} {bs bs' : ByteStream} {done : Bool}
    (hstep : stepCoreClause ctx cid db bs = some (done, cid', db', bs'))
    (hdb : EvalTrieCNF val db) :
    EvalTrieCNF val db' := by
  unfold stepCoreClause at hstep
  cases hd : decodeOneJust ctx bs with
  | none => simp [hd] at hstep
  | some pd =>
    rcases pd with ⟨clOpt, bs1⟩
    simp only [hd] at hstep
    cases clOpt with
    | none =>
      injection hstep with hp; rcases Prod.mk.inj hp with ⟨_, hp2⟩
      rcases Prod.mk.inj hp2 with ⟨_, hp3⟩; rcases Prod.mk.inj hp3 with ⟨rfl, _⟩
      exact hdb
    | some cl =>
      simp only [withStrictTrie_eq, strictClause_eq] at hstep
      have hdb_eq : db' = db.insert cid cl := by
        cases hs_p : strictPIdx cid.succ <;> simp only [hs_p] at hstep <;>
          injection hstep with hp <;> rcases Prod.mk.inj hp with ⟨_, hp2⟩ <;>
          rcases Prod.mk.inj hp2 with ⟨_, hp3⟩ <;> exact (Prod.mk.inj hp3).1.symm
      subst hdb_eq
      exact evalTrieCNF_insert hdb cid (decodeOneJust_sound hV hM hn_pts hbccw_eq hm_eq hval hd)

private lemma chainStateBlocks_cnf {val : PIdx → Bool}
    {f : PIdx → BinTrie Clause → ByteStream → Option (Bool × PIdx × BinTrie Clause × ByteStream)}
    (hf : ∀ {cid cid' db db' bs bs' done},
      f cid db bs = some (done, cid', db', bs') → EvalTrieCNF val db → EvalTrieCNF val db') :
    ∀ (k : ℕ) {cid cid' : PIdx} {db db' : BinTrie Clause} {bs bs' : ByteStream} {done : Bool},
      chainStateBlocks f k cid db bs = some (done, cid', db', bs') →
      EvalTrieCNF val db → EvalTrieCNF val db'
  | 0, _, _, _, _, _, _, _, h, hdb => by
    injection h with hp; rcases Prod.mk.inj hp with ⟨_, hp2⟩
    rcases Prod.mk.inj hp2 with ⟨_, hp3⟩; rcases Prod.mk.inj hp3 with ⟨rfl, _⟩; exact hdb
  | k + 1, cid, _, db, _, bs, _, _, h, hdb => by
    unfold chainStateBlocks at h
    cases hex : f cid db bs with
    | none => simp [hex] at h
    | some res =>
      rcases res with ⟨d1, cid1, db1, bs1⟩
      simp only [hex] at h
      have hdb1 := hf hex hdb
      cases d1
      · exact chainStateBlocks_cnf hf k h hdb1
      · injection h with hp; rcases Prod.mk.inj hp with ⟨_, hp2⟩
        rcases Prod.mk.inj hp2 with ⟨_, hp3⟩; rcases Prod.mk.inj hp3 with ⟨rfl, _⟩; exact hdb1

private lemma buildCoreTower_sound {P : Set (ℝ × ℝ)} {S : Fin 7 → ℝ × ℝ} {w : Finset (Fin 7) → ℝ × ℝ}
    {ctx : CertCtx}
    (hV : ValidCanonicalInstance P S w ctx.spec)
    (hM : ValidMasks ctx.spec.masks)
    (hn_pts : ctx.n_pts = 7 + ctx.spec.masks.length)
    (hbccw_eq : ctx.bccw = buildBccw ctx.spec)
    (hm_eq : ctx.maskTrie = buildMaskTrieAux .xH ctx.spec.masks .leaf)
    {val : PIdx → Bool}
    (hval : ∀ {i j k : ℕ} (hij : i < j) (hjk : j < k) (hk : k < ctx.n_pts) {v : PIdx},
      ctx.tripleTrie.get3 (ptKey i) (ptKey j) (ptKey k) = some v →
      val v = orientSign (pointSeq S w (specWitnessEmb hM) ⟨i, by omega⟩)
                         (pointSeq S w (specWitnessEmb hM) ⟨j, by omega⟩)
                         (pointSeq S w (specWitnessEmb hM) ⟨k, by omega⟩)) :
    ∀ (lvl : ℕ) {cid cid' : PIdx} {db db' : BinTrie Clause} {bs bs' : ByteStream} {done : Bool},
      buildCoreTower ctx lvl cid db bs = some (done, cid', db', bs') →
      EvalTrieCNF val db → EvalTrieCNF val db'
  | 0, _, _, _, _, _, _, _, h, hdb =>
    chainStateBlocks_cnf (stepCoreClause_sound hV hM hn_pts hbccw_eq hm_eq hval) 16 h hdb
  | lvl + 1, _, _, _, _, _, _, _, h, hdb =>
    chainStateBlocks_cnf (buildCoreTower_sound hV hM hn_pts hbccw_eq hm_eq hval lvl) 16 h hdb

/-- **Master Canonical Certificate Soundness Theorem (`unsat_of_valid_canonical_and_cert`)**:
    For any `ValidCanonicalInstance P S w spec` with `validMasksBool spec.masks = true`,
    `checkCaseCert spec varTree justTree rupTree = true` yields `False`! -/
theorem unsat_of_valid_canonical_and_cert {P : Set (ℝ × ℝ)}
    {S : Fin 7 → ℝ × ℝ} {w : Finset (Fin 7) → ℝ × ℝ} {spec : CaseSpec}
    (hV : ValidCanonicalInstance P S w spec)
    (hMasks : validMasksBool spec.masks = true)
    {varTree justTree rupTree : ChunkTree}
    (hCert : checkCaseCert spec varTree justTree rupTree = true) : False := by
  have hM : ValidMasks spec.masks := validMasks_of_bool hMasks
  unfold checkCaseCert at hCert
  dsimp only at hCert
  cases htt : buildTripleTrieTree (7 + spec.masks.length) varTree with
  | none => rw [htt] at hCert; exact Bool.noConfusion hCert
  | some tripleTrie =>
    rw [htt] at hCert
    dsimp only at hCert
    let ctx : CertCtx := {
      spec := spec
      n_pts := 7 + spec.masks.length
      bccw := buildBccw spec
      ptKeyTrie := .leaf
      maskTrie := buildMaskTrieAux .xH spec.masks .leaf
      tripleTrie := tripleTrie
    }
    change (match buildCoreDBTree ctx justTree with
      | none => false
      | some db => checkTreeRUP db rupTree) = true at hCert
    cases hdb_opt : buildCoreDBTree ctx justTree with
    | none => rw [hdb_opt] at hCert; exact Bool.noConfusion hCert
    | some db =>
      rw [hdb_opt] at hCert
      obtain ⟨val, hval⟩ := buildTripleTrieTree_sound (by have := hM.1; omega)
        (pointSeq S w (specWitnessEmb hM)) htt
      unfold buildCoreDBTree at hdb_opt
      cases htw : buildCoreTower ctx 4 .xH .leaf (ByteStream.ofTree justTree) with
      | none => rw [htw] at hdb_opt; nomatch hdb_opt
      | some res =>
        rcases res with ⟨done, cid', db', bs'⟩
        rw [htw] at hdb_opt
        cases done
        · nomatch hdb_opt
        · injection hdb_opt with hdb_eq; subst hdb_eq
          have hleaf_cnf : EvalTrieCNF val .leaf :=
            fun k _ hg => by rw [BinTrie.get_leaf] at hg; nomatch hg
          have hdb_cnf : EvalTrieCNF val db' :=
            buildCoreTower_sound hV hM rfl rfl rfl hval 4 htw hleaf_cnf
          exact checkTreeRUP_sound hCert hdb_cnf

end VCDim6

end
