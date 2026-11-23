import Mathlib
import RootTask.Defs
import RootTask.CaseBTri

open scoped Classical BigOperators
open Finset

noncomputable section

namespace CaseB

/-! ## Boundary Rays and Closedness -/

def dir1 (W : OpenWedge) : ℝ × ℝ := (-W.u₁.2, W.u₁.1)

def dir2 (W : OpenWedge) : ℝ × ℝ := (W.u₂.2, -W.u₂.1)

def ray1 (W : OpenWedge) (t : ℝ) : ℝ × ℝ :=
  (W.y.1 + t * (dir1 W).1, W.y.2 + t * (dir1 W).2)

def ray2 (W : OpenWedge) (t : ℝ) : ℝ × ℝ :=
  (W.y.1 + t * (dir2 W).1, W.y.2 + t * (dir2 W).2)

def closureMem (W : OpenWedge) (p : ℝ × ℝ) : Prop :=
  0 ≤ W.u₁.1 * (p.1 - W.y.1) + W.u₁.2 * (p.2 - W.y.2) ∧
  0 ≤ W.u₂.1 * (p.1 - W.y.1) + W.u₂.2 * (p.2 - W.y.2)

def bdWedge (W : OpenWedge) : Set (ℝ × ℝ) :=
  {p | ¬ W.MemOpen p ∧ ¬ W.MemExt p}

def Gamma (W : OpenWedge) : Set (ℝ × ℝ) :=
  {p | p ∈ bdWedge W ∧ inOmega p}

lemma wedge_partition (W : OpenWedge) (p : ℝ × ℝ) :
    W.MemOpen p ∨ p ∈ bdWedge W ∨ W.MemExt p := by
  by_cases h1 : W.MemOpen p
  · exact Or.inl h1
  · by_cases h2 : W.MemExt p
    · exact Or.inr (Or.inr h2)
    · exact Or.inr (Or.inl ⟨h1, h2⟩)

lemma bdWedge_iff_closure_eq_zero (W : OpenWedge) (p : ℝ × ℝ) :
    p ∈ bdWedge W ↔ closureMem W p ∧
      (W.u₁.1 * (p.1 - W.y.1) + W.u₁.2 * (p.2 - W.y.2) = 0 ∨
       W.u₂.1 * (p.1 - W.y.1) + W.u₂.2 * (p.2 - W.y.2) = 0) := by
  constructor
  · rintro ⟨hno, hne⟩
    dsimp [OpenWedge.MemOpen, OpenWedge.MemExt] at hno hne
    push Not at hne
    refine ⟨hne, ?_⟩
    by_contra hboth
    push Not at hboth
    exact hno ⟨lt_of_le_of_ne hne.1 hboth.1.symm, lt_of_le_of_ne hne.2 hboth.2.symm⟩
  · rintro ⟨⟨h1, h2⟩, h1z | h2z⟩
    · refine ⟨fun ⟨ho1, _⟩ => by linarith, ?_⟩
      rintro (he1 | he2) <;> linarith
    · refine ⟨fun ⟨_, ho2⟩ => by linarith, ?_⟩
      rintro (he1 | he2) <;> linarith

lemma bdWedge_isClosed (W : OpenWedge) : IsClosed (bdWedge W) := by
  change IsClosed ({p : ℝ × ℝ | W.MemOpen p}ᶜ ∩ {p : ℝ × ℝ | W.MemExt p}ᶜ)
  exact (isOpen_memOpen W).isClosed_compl.inter (isOpen_memExt W).isClosed_compl

lemma dir1_ne_zero (W : OpenWedge) : dir1 W ≠ (0, 0) := by
  intro h
  have h1 : -W.u₁.2 = 0 := congrArg Prod.fst h
  have h2 : W.u₁.1 = 0 := congrArg Prod.snd h
  have hnd := W.h_nondeg
  have h1' : W.u₁.2 = 0 := by linarith
  rw [h1', h2] at hnd
  linarith

lemma dir2_ne_zero (W : OpenWedge) : dir2 W ≠ (0, 0) := by
  intro h
  have h1 : W.u₂.2 = 0 := congrArg Prod.fst h
  have h2 : -W.u₂.1 = 0 := congrArg Prod.snd h
  have hnd := W.h_nondeg
  have h2' : W.u₂.1 = 0 := by linarith
  rw [h1, h2'] at hnd
  linarith

lemma ray1_injective (W : OpenWedge) : Function.Injective (ray1 W) := by
  intro t₁ t₂ heq
  have hne := dir1_ne_zero W
  have hfx : t₁ * (dir1 W).1 = t₂ * (dir1 W).1 := by
    have := congrArg Prod.fst heq; dsimp [ray1] at this; linarith
  have hfy : t₁ * (dir1 W).2 = t₂ * (dir1 W).2 := by
    have := congrArg Prod.snd heq; dsimp [ray1] at this; linarith
  by_cases hx : (dir1 W).1 = 0
  · have hy : (dir1 W).2 ≠ 0 := fun hy => hne (Prod.ext hx hy)
    exact mul_right_cancel₀ hy hfy
  · exact mul_right_cancel₀ hx hfx

lemma ray2_injective (W : OpenWedge) : Function.Injective (ray2 W) := by
  intro t₁ t₂ heq
  have hne := dir2_ne_zero W
  have hfx : t₁ * (dir2 W).1 = t₂ * (dir2 W).1 := by
    have := congrArg Prod.fst heq; dsimp [ray2] at this; linarith
  have hfy : t₁ * (dir2 W).2 = t₂ * (dir2 W).2 := by
    have := congrArg Prod.snd heq; dsimp [ray2] at this; linarith
  by_cases hx : (dir2 W).1 = 0
  · have hy : (dir2 W).2 ≠ 0 := fun hy => hne (Prod.ext hx hy)
    exact mul_right_cancel₀ hy hfy
  · exact mul_right_cancel₀ hx hfx

lemma ray1_isClosedEmbedding (W : OpenWedge) : Topology.IsClosedEmbedding (ray1 W) := by
  have hne := dir1_ne_zero W
  let inv : ℝ × ℝ → ℝ := fun p =>
    if (dir1 W).1 ≠ 0 then (p.1 - W.y.1) / (dir1 W).1 else (p.2 - W.y.2) / (dir1 W).2
  have hcont_ray : Continuous (ray1 W) := by unfold ray1; fun_prop
  have hcont_inv : Continuous inv := by
    unfold inv; split_ifs <;> fun_prop
  have hleft : Function.LeftInverse inv (ray1 W) := by
    intro t
    dsimp [inv, ray1]
    by_cases hx : (dir1 W).1 = 0
    · rw [if_neg (not_not.mpr hx)]
      have hy : (dir1 W).2 ≠ 0 := fun hy => hne (Prod.ext hx hy)
      field_simp [hy]; ring
    · rw [if_pos hx]
      field_simp [hx]; ring
  have hclosed_range : IsClosed (Set.range (ray1 W)) := by
    rw [show Set.range (ray1 W) = {p : ℝ × ℝ | ray1 W (inv p) = p} from by
      ext p; constructor
      · rintro ⟨t, rfl⟩; change ray1 W (inv (ray1 W t)) = ray1 W t; rw [hleft t]
      · intro hp; exact ⟨inv p, hp⟩]
    exact isClosed_eq (hcont_ray.comp hcont_inv) continuous_id
  exact Topology.IsClosedEmbedding.of_continuous_injective_isClosedMap hcont_ray (ray1_injective W)
    (fun s hs => by
      have himg : ray1 W '' s = Set.range (ray1 W) ∩ inv ⁻¹' s := by
        ext p; constructor
        · rintro ⟨t, ht, rfl⟩; exact ⟨⟨t, rfl⟩, by simpa [hleft t] using ht⟩
        · rintro ⟨⟨t, rfl⟩, ht⟩; exact ⟨t, by simpa [hleft t] using ht, rfl⟩
      rw [himg]
      exact hclosed_range.inter (hs.preimage hcont_inv))

lemma ray2_isClosedEmbedding (W : OpenWedge) : Topology.IsClosedEmbedding (ray2 W) := by
  have hne := dir2_ne_zero W
  let inv : ℝ × ℝ → ℝ := fun p =>
    if (dir2 W).1 ≠ 0 then (p.1 - W.y.1) / (dir2 W).1 else (p.2 - W.y.2) / (dir2 W).2
  have hcont_ray : Continuous (ray2 W) := by unfold ray2; fun_prop
  have hcont_inv : Continuous inv := by
    unfold inv; split_ifs <;> fun_prop
  have hleft : Function.LeftInverse inv (ray2 W) := by
    intro t
    dsimp [inv, ray2]
    by_cases hx : (dir2 W).1 = 0
    · rw [if_neg (not_not.mpr hx)]
      have hy : (dir2 W).2 ≠ 0 := fun hy => hne (Prod.ext hx hy)
      field_simp [hy]; ring
    · rw [if_pos hx]
      field_simp [hx]; ring
  have hclosed_range : IsClosed (Set.range (ray2 W)) := by
    rw [show Set.range (ray2 W) = {p : ℝ × ℝ | ray2 W (inv p) = p} from by
      ext p; constructor
      · rintro ⟨t, rfl⟩; change ray2 W (inv (ray2 W t)) = ray2 W t; rw [hleft t]
      · intro hp; exact ⟨inv p, hp⟩]
    exact isClosed_eq (hcont_ray.comp hcont_inv) continuous_id
  exact Topology.IsClosedEmbedding.of_continuous_injective_isClosedMap hcont_ray (ray2_injective W)
    (fun s hs => by
      have himg : ray2 W '' s = Set.range (ray2 W) ∩ inv ⁻¹' s := by
        ext p; constructor
        · rintro ⟨t, ht, rfl⟩; exact ⟨⟨t, rfl⟩, by simpa [hleft t] using ht⟩
        · rintro ⟨⟨t, rfl⟩, ht⟩; exact ⟨t, by simpa [hleft t] using ht, rfl⟩
      rw [himg]
      exact hclosed_range.inter (hs.preimage hcont_inv))

lemma ray1_mem_bdWedge (W : OpenWedge) {t : ℝ} (ht : 0 ≤ t) : ray1 W t ∈ bdWedge W := by
  have hnd := W.h_nondeg
  have hl1 : W.u₁.1 * ((ray1 W t).1 - W.y.1) + W.u₁.2 * ((ray1 W t).2 - W.y.2) = 0 := by
    dsimp [ray1, dir1]; ring
  have hl2 : W.u₂.1 * ((ray1 W t).1 - W.y.1) + W.u₂.2 * ((ray1 W t).2 - W.y.2) =
      t * (W.u₁.1 * W.u₂.2 - W.u₁.2 * W.u₂.1) := by
    dsimp [ray1, dir1]; ring
  have hnn : 0 ≤ t * (W.u₁.1 * W.u₂.2 - W.u₁.2 * W.u₂.1) := mul_nonneg ht (le_of_lt hnd)
  refine ⟨?_, ?_⟩
  · rintro ⟨h1, _⟩; linarith
  · rintro (h1 | h2) <;> linarith

lemma ray2_mem_bdWedge (W : OpenWedge) {t : ℝ} (ht : 0 ≤ t) : ray2 W t ∈ bdWedge W := by
  have hnd := W.h_nondeg
  have hl1 : W.u₁.1 * ((ray2 W t).1 - W.y.1) + W.u₁.2 * ((ray2 W t).2 - W.y.2) =
      t * (W.u₁.1 * W.u₂.2 - W.u₁.2 * W.u₂.1) := by
    dsimp [ray2, dir2]; ring
  have hl2 : W.u₂.1 * ((ray2 W t).1 - W.y.1) + W.u₂.2 * ((ray2 W t).2 - W.y.2) = 0 := by
    dsimp [ray2, dir2]; ring
  have hnn : 0 ≤ t * (W.u₁.1 * W.u₂.2 - W.u₁.2 * W.u₂.1) := mul_nonneg ht (le_of_lt hnd)
  refine ⟨?_, ?_⟩
  · rintro ⟨_, h2⟩; linarith
  · rintro (h1 | h2) <;> linarith

lemma bdWedge_iff_rays (W : OpenWedge) (p : ℝ × ℝ) :
    p ∈ bdWedge W ↔ (∃ t ≥ 0, p = ray1 W t) ∨ (∃ t ≥ 0, p = ray2 W t) := by
  constructor
  · rintro ⟨hno, hne⟩
    dsimp [OpenWedge.MemOpen, OpenWedge.MemExt] at hno hne
    push Not at hne
    have h1_nn : 0 ≤ W.u₁.1 * (p.1 - W.y.1) + W.u₁.2 * (p.2 - W.y.2) := hne.1
    have h2_nn : 0 ≤ W.u₂.1 * (p.1 - W.y.1) + W.u₂.2 * (p.2 - W.y.2) := hne.2
    have hnd := W.h_nondeg
    have hnd_ne : W.u₁.1 * W.u₂.2 - W.u₁.2 * W.u₂.1 ≠ 0 := ne_of_gt hnd
    have h_or : W.u₁.1 * (p.1 - W.y.1) + W.u₁.2 * (p.2 - W.y.2) = 0 ∨
        W.u₂.1 * (p.1 - W.y.1) + W.u₂.2 * (p.2 - W.y.2) = 0 := by
      by_contra hboth
      push Not at hboth
      exact hno ⟨lt_of_le_of_ne h1_nn hboth.1.symm, lt_of_le_of_ne h2_nn hboth.2.symm⟩
    rcases h_or with h1z | h2z
    · left
      let t := (W.u₂.1 * (p.1 - W.y.1) + W.u₂.2 * (p.2 - W.y.2)) /
        (W.u₁.1 * W.u₂.2 - W.u₁.2 * W.u₂.1)
      refine ⟨t, div_nonneg h2_nn (le_of_lt hnd), ?_⟩
      ext
      · dsimp [ray1, dir1, t]
        have hx : (p.1 - W.y.1) * (W.u₁.1 * W.u₂.2 - W.u₁.2 * W.u₂.1) =
            (W.u₂.1 * (p.1 - W.y.1) + W.u₂.2 * (p.2 - W.y.2)) * (-W.u₁.2) := by
          linear_combination W.u₂.2 * h1z
        calc p.1 = W.y.1 + (p.1 - W.y.1) := by ring
          _ = W.y.1 + ((p.1 - W.y.1) * (W.u₁.1 * W.u₂.2 - W.u₁.2 * W.u₂.1)) /
                (W.u₁.1 * W.u₂.2 - W.u₁.2 * W.u₂.1) := by rw [mul_div_cancel_right₀ _ hnd_ne]
          _ = W.y.1 + (W.u₂.1 * (p.1 - W.y.1) + W.u₂.2 * (p.2 - W.y.2)) /
                (W.u₁.1 * W.u₂.2 - W.u₁.2 * W.u₂.1) * -W.u₁.2 := by rw [hx]; ring
      · dsimp [ray1, dir1, t]
        have hy : (p.2 - W.y.2) * (W.u₁.1 * W.u₂.2 - W.u₁.2 * W.u₂.1) =
            (W.u₂.1 * (p.1 - W.y.1) + W.u₂.2 * (p.2 - W.y.2)) * W.u₁.1 := by
          linear_combination -W.u₂.1 * h1z
        calc p.2 = W.y.2 + (p.2 - W.y.2) := by ring
          _ = W.y.2 + ((p.2 - W.y.2) * (W.u₁.1 * W.u₂.2 - W.u₁.2 * W.u₂.1)) /
                (W.u₁.1 * W.u₂.2 - W.u₁.2 * W.u₂.1) := by rw [mul_div_cancel_right₀ _ hnd_ne]
          _ = W.y.2 + (W.u₂.1 * (p.1 - W.y.1) + W.u₂.2 * (p.2 - W.y.2)) /
                (W.u₁.1 * W.u₂.2 - W.u₁.2 * W.u₂.1) * W.u₁.1 := by rw [hy]; ring
    · right
      let t := (W.u₁.1 * (p.1 - W.y.1) + W.u₁.2 * (p.2 - W.y.2)) /
        (W.u₁.1 * W.u₂.2 - W.u₁.2 * W.u₂.1)
      refine ⟨t, div_nonneg h1_nn (le_of_lt hnd), ?_⟩
      ext
      · dsimp [ray2, dir2, t]
        have hx : (p.1 - W.y.1) * (W.u₁.1 * W.u₂.2 - W.u₁.2 * W.u₂.1) =
            (W.u₁.1 * (p.1 - W.y.1) + W.u₁.2 * (p.2 - W.y.2)) * W.u₂.2 := by
          linear_combination -W.u₁.2 * h2z
        calc p.1 = W.y.1 + (p.1 - W.y.1) := by ring
          _ = W.y.1 + ((p.1 - W.y.1) * (W.u₁.1 * W.u₂.2 - W.u₁.2 * W.u₂.1)) /
                (W.u₁.1 * W.u₂.2 - W.u₁.2 * W.u₂.1) := by rw [mul_div_cancel_right₀ _ hnd_ne]
          _ = W.y.1 + (W.u₁.1 * (p.1 - W.y.1) + W.u₁.2 * (p.2 - W.y.2)) /
                (W.u₁.1 * W.u₂.2 - W.u₁.2 * W.u₂.1) * W.u₂.2 := by rw [hx]; ring
      · dsimp [ray2, dir2, t]
        have hy : (p.2 - W.y.2) * (W.u₁.1 * W.u₂.2 - W.u₁.2 * W.u₂.1) =
            (W.u₁.1 * (p.1 - W.y.1) + W.u₁.2 * (p.2 - W.y.2)) * (-W.u₂.1) := by
          linear_combination W.u₁.1 * h2z
        calc p.2 = W.y.2 + (p.2 - W.y.2) := by ring
          _ = W.y.2 + ((p.2 - W.y.2) * (W.u₁.1 * W.u₂.2 - W.u₁.2 * W.u₂.1)) /
                (W.u₁.1 * W.u₂.2 - W.u₁.2 * W.u₂.1) := by rw [mul_div_cancel_right₀ _ hnd_ne]
          _ = W.y.2 + (W.u₁.1 * (p.1 - W.y.1) + W.u₁.2 * (p.2 - W.y.2)) /
                (W.u₁.1 * W.u₂.2 - W.u₁.2 * W.u₂.1) * -W.u₂.1 := by rw [hy]; ring
  · rintro (⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩)
    · exact ray1_mem_bdWedge W ht
    · exact ray2_mem_bdWedge W ht

lemma ray1_eq_ray2 (W : OpenWedge) {t₁ t₂ : ℝ} (heq : ray1 W t₁ = ray2 W t₂) :
    t₁ = 0 ∧ t₂ = 0 := by
  have hnd := ne_of_gt W.h_nondeg
  have hx : t₁ * (-W.u₁.2) = t₂ * W.u₂.2 := by
    have := congrArg Prod.fst heq; dsimp [ray1, ray2, dir1, dir2] at this; linarith
  have hy : t₁ * W.u₁.1 = t₂ * (-W.u₂.1) := by
    have := congrArg Prod.snd heq; dsimp [ray1, ray2, dir1, dir2] at this; linarith
  have h1 : t₁ * (W.u₁.1 * W.u₂.2 - W.u₁.2 * W.u₂.1) = 0 := by
    calc t₁ * (W.u₁.1 * W.u₂.2 - W.u₁.2 * W.u₂.1)
        = (t₁ * W.u₁.1) * W.u₂.2 + (t₁ * (-W.u₁.2)) * W.u₂.1 := by ring
      _ = (t₂ * (-W.u₂.1)) * W.u₂.2 + (t₂ * W.u₂.2) * W.u₂.1 := by rw [hx, hy]
      _ = 0 := by ring
  have h2 : t₂ * (W.u₁.1 * W.u₂.2 - W.u₁.2 * W.u₂.1) = 0 := by
    calc t₂ * (W.u₁.1 * W.u₂.2 - W.u₁.2 * W.u₂.1)
        = W.u₁.1 * (t₂ * W.u₂.2) + W.u₁.2 * (t₂ * (-W.u₂.1)) := by ring
      _ = W.u₁.1 * (t₁ * (-W.u₁.2)) + W.u₁.2 * (t₁ * W.u₁.1) := by rw [← hx, ← hy]
      _ = 0 := by ring
  exact ⟨(mul_eq_zero.mp h1).resolve_right hnd, (mul_eq_zero.mp h2).resolve_right hnd⟩

/-! ## Ray Monotonicity in `Ω` and Continuous Parametrization of `Γ` -/

def rayExit (y d : ℝ × ℝ) : WithTop ℝ :=
  if 0 < d.1 ∧ 0 < d.2 then ↑(max (-y.1 / d.1) (-y.2 / d.2)) else ⊤

lemma rayExit_pos {y d : ℝ × ℝ} (hy1 : y.1 < 0) (_hy2 : y.2 < 0) :
    (0 : WithTop ℝ) < rayExit y d := by
  unfold rayExit
  split_ifs with h
  · exact WithTop.coe_pos.mpr (lt_max_of_lt_left (div_pos (by linarith) h.1))
  · exact WithTop.coe_lt_top 0

lemma ray_inOmega_iff {y d : ℝ × ℝ} (hy1 : y.1 < 0) (hy2 : y.2 < 0) {t : ℝ} (ht : 0 ≤ t) :
    inOmega (y.1 + t * d.1, y.2 + t * d.2) ↔ (t : WithTop ℝ) < rayExit y d := by
  unfold rayExit inOmega
  split_ifs with h
  · rw [WithTop.coe_lt_coe, lt_max_iff]
    dsimp only
    rw [lt_div_iff₀ h.1, lt_div_iff₀ h.2]
    constructor <;> rintro (h' | h') <;> [left; right; left; right] <;> linarith
  · constructor
    · intro _; exact WithTop.coe_lt_top t
    · intro _
      by_cases hd1 : 0 < d.1
      · have hd2 : d.2 ≤ 0 := by
          by_contra h2; push Not at h2; exact h ⟨hd1, h2⟩
        right
        have : t * d.2 ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ht hd2
        linarith
      · left
        have hd1' : d.1 ≤ 0 := not_lt.mp hd1
        have : t * d.1 ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ht hd1'
        linarith

def stretch (T : WithTop ℝ) (s : ℝ) : ℝ :=
  match T with
  | ⊤ => s
  | (t₀ : ℝ) => t₀ * s / (1 + s)

lemma stretch_zero (T : WithTop ℝ) : stretch T 0 = 0 := by
  cases T <;> simp [stretch]

lemma stretch_nonneg {T : WithTop ℝ} (hT : (0 : WithTop ℝ) < T) {s : ℝ} (hs : 0 ≤ s) :
    0 ≤ stretch T s := by
  cases T with
  | top => exact hs
  | coe t₀ =>
    have ht₀ : 0 < t₀ := WithTop.coe_lt_coe.mp hT
    dsimp [stretch]
    exact div_nonneg (mul_nonneg (le_of_lt ht₀) hs) (by linarith)

lemma stretch_lt {T : WithTop ℝ} (hT : (0 : WithTop ℝ) < T) {s : ℝ} (hs : 0 ≤ s) :
    (stretch T s : WithTop ℝ) < T := by
  cases T with
  | top => exact WithTop.coe_lt_top _
  | coe t₀ =>
    have ht₀ : 0 < t₀ := WithTop.coe_lt_coe.mp hT
    rw [WithTop.coe_lt_coe]
    dsimp [stretch]
    rw [div_lt_iff₀ (by linarith)]
    nlinarith

lemma stretch_strictMono {T : WithTop ℝ} (hT : (0 : WithTop ℝ) < T) :
    StrictMonoOn (stretch T) (Set.Ici 0) := by
  intro a ha b hb hab
  cases T with
  | top => exact hab
  | coe t₀ =>
    have ht₀ : 0 < t₀ := WithTop.coe_lt_coe.mp hT
    dsimp [stretch]
    have ha' : 0 < 1 + a := by linarith [Set.mem_Ici.mp ha]
    have hb' : 0 < 1 + b := by linarith [Set.mem_Ici.mp hb]
    rw [div_lt_div_iff₀ ha' hb']
    nlinarith

lemma stretch_surj {T : WithTop ℝ} (hT : (0 : WithTop ℝ) < T) {t : ℝ}
    (ht0 : 0 ≤ t) (htT : (t : WithTop ℝ) < T) :
    ∃ s ≥ 0, stretch T s = t := by
  cases T with
  | top => exact ⟨t, ht0, rfl⟩
  | coe t₀ =>
    have ht₀ : 0 < t₀ := WithTop.coe_lt_coe.mp hT
    have htt₀ : t < t₀ := WithTop.coe_lt_coe.mp htT
    refine ⟨t / (t₀ - t), div_nonneg ht0 (by linarith), ?_⟩
    dsimp [stretch]
    have hne1 : t₀ - t ≠ 0 := by linarith
    have hne2 : 1 + t / (t₀ - t) ≠ 0 := by
      have : 0 ≤ t / (t₀ - t) := div_nonneg ht0 (by linarith)
      linarith
    field_simp [hne1, hne2, ne_of_gt ht₀]
    ring

def gammaParam (W : OpenWedge) (s : ℝ) : ℝ × ℝ :=
  if s ≤ 0 then ray1 W (stretch (rayExit W.y (dir1 W)) (-s))
  else ray2 W (stretch (rayExit W.y (dir2 W)) s)

lemma gammaParam_zero (W : OpenWedge) : gammaParam W 0 = W.y := by
  simp [gammaParam, stretch_zero, ray1]

lemma gammaParam_continuous (W : OpenWedge) : Continuous (gammaParam W) := by
  let f1 : ℝ → ℝ × ℝ := fun s => ray1 W (stretch (rayExit W.y (dir1 W)) (-s))
  let f2 : ℝ → ℝ × ℝ := fun s => ray2 W (stretch (rayExit W.y (dir2 W)) s)
  have hf1 : ContinuousOn f1 (Set.Iic 0) := by
    have hst : ContinuousOn (fun s : ℝ => stretch (rayExit W.y (dir1 W)) (-s)) (Set.Iic 0) := by
      cases hT : rayExit W.y (dir1 W) with
      | top => simp only [stretch]; exact continuous_neg.continuousOn
      | coe t₀ =>
        simp only [stretch]
        refine ContinuousOn.div (continuousOn_const.mul continuous_neg.continuousOn) ?_ ?_
        · exact continuousOn_const.add continuous_neg.continuousOn
        · intro s hs; have : s ≤ 0 := hs; linarith
    exact (by unfold ray1; fun_prop : Continuous (ray1 W)).comp_continuousOn hst
  have hf2 : ContinuousOn f2 (Set.Ici 0) := by
    have hst : ContinuousOn (fun s : ℝ => stretch (rayExit W.y (dir2 W)) s) (Set.Ici 0) := by
      cases hT : rayExit W.y (dir2 W) with
      | top => simp only [stretch]; exact continuousOn_id
      | coe t₀ =>
        simp only [stretch]
        refine ContinuousOn.div (continuousOn_const.mul continuousOn_id) ?_ ?_
        · exact continuousOn_const.add continuousOn_id
        · intro s hs; have : 0 ≤ s := hs; linarith
    exact (by unfold ray2; fun_prop : Continuous (ray2 W)).comp_continuousOn hst
  have heq0 : ∀ s : ℝ, s ∈ Set.Iic (0 : ℝ) ∩ Set.Ici (0 : ℝ) → f1 s = f2 s := by
    intro s hs
    have hs0 : s = 0 := le_antisymm hs.1 hs.2
    subst hs0
    simp [f1, f2, stretch_zero, ray1, ray2]
  have hcont : Continuous (fun s : ℝ => if s ≤ 0 then f1 s else f2 s) := by
    rw [← continuousOn_univ, show (Set.univ : Set ℝ) = Set.Iic 0 ∪ Set.Ici 0 from
      (Set.Iic_union_Ici).symm]
    refine ContinuousOn.union_of_isClosed ?_ ?_ isClosed_Iic isClosed_Ici
    · exact hf1.congr fun s hs => by simp [Set.mem_Iic.mp hs]
    · exact hf2.congr fun s hs => by
        by_cases hs0 : s ≤ 0
        · rw [if_pos hs0]; exact heq0 s ⟨hs0, hs⟩
        · rw [if_neg hs0]
  exact hcont

lemma gammaParam_injective (W : OpenWedge) (hy1 : W.y.1 < 0) (hy2 : W.y.2 < 0) :
    Function.Injective (gammaParam W) := by
  have hT1 := rayExit_pos hy1 hy2 (d := dir1 W)
  have hT2 := rayExit_pos hy1 hy2 (d := dir2 W)
  intro a b hab
  unfold gammaParam at hab
  split_ifs at hab with ha hb hb
  · have h1 := ray1_injective W hab
    have h2 := (stretch_strictMono hT1).injOn (by simp; linarith) (by simp; linarith) h1
    linarith
  · obtain ⟨h1, h2⟩ := ray1_eq_ray2 W hab
    have ha0 : -a = 0 :=
      (stretch_strictMono hT1).injOn (by simp; linarith) (by simp) (by simpa [stretch_zero] using h1)
    have hb0 : b = 0 :=
      (stretch_strictMono hT2).injOn (by simp; linarith) (by simp) (by simpa [stretch_zero] using h2)
    linarith
  · obtain ⟨h1, h2⟩ := ray1_eq_ray2 W hab.symm
    have hb0 : -b = 0 :=
      (stretch_strictMono hT1).injOn (by simp; linarith) (by simp) (by simpa [stretch_zero] using h1)
    have ha0 : a = 0 :=
      (stretch_strictMono hT2).injOn (by simp; linarith) (by simp) (by simpa [stretch_zero] using h2)
    linarith
  · have h1 := ray2_injective W hab
    exact (stretch_strictMono hT2).injOn (by simp; linarith) (by simp; linarith) h1

lemma gammaParam_mem_Gamma (W : OpenWedge) (hy1 : W.y.1 < 0) (hy2 : W.y.2 < 0) (s : ℝ) :
    gammaParam W s ∈ Gamma W := by
  have hT1 := rayExit_pos hy1 hy2 (d := dir1 W)
  have hT2 := rayExit_pos hy1 hy2 (d := dir2 W)
  unfold gammaParam
  split_ifs with hs
  · have hnn : 0 ≤ stretch (rayExit W.y (dir1 W)) (-s) := stretch_nonneg hT1 (by linarith)
    have hlt := stretch_lt hT1 (by linarith : 0 ≤ -s)
    exact ⟨ray1_mem_bdWedge W hnn, (ray_inOmega_iff hy1 hy2 hnn).mpr hlt⟩
  · have hnn : 0 ≤ stretch (rayExit W.y (dir2 W)) s := stretch_nonneg hT2 (by linarith)
    have hlt := stretch_lt hT2 (by linarith : 0 ≤ s)
    exact ⟨ray2_mem_bdWedge W hnn, (ray_inOmega_iff hy1 hy2 hnn).mpr hlt⟩

lemma gammaParam_range (W : OpenWedge) (hy1 : W.y.1 < 0) (hy2 : W.y.2 < 0) :
    Set.range (gammaParam W) = Gamma W := by
  have hT1 := rayExit_pos hy1 hy2 (d := dir1 W)
  have hT2 := rayExit_pos hy1 hy2 (d := dir2 W)
  ext p; constructor
  · rintro ⟨s, rfl⟩; exact gammaParam_mem_Gamma W hy1 hy2 s
  · rintro ⟨hp_bd, hp_om⟩
    rcases (bdWedge_iff_rays W p).mp hp_bd with ⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩
    · have htT : (t : WithTop ℝ) < rayExit W.y (dir1 W) := (ray_inOmega_iff hy1 hy2 ht).mp hp_om
      obtain ⟨s, hs, hst⟩ := stretch_surj hT1 ht htT
      refine ⟨-s, ?_⟩
      simp [gammaParam, hs, hst]
    · have htT : (t : WithTop ℝ) < rayExit W.y (dir2 W) := (ray_inOmega_iff hy1 hy2 ht).mp hp_om
      obtain ⟨s, hs, hst⟩ := stretch_surj hT2 ht htT
      by_cases hs0 : s = 0
      · subst hs0; rw [stretch_zero] at hst; refine ⟨0, ?_⟩; simp [gammaParam, stretch_zero, ← hst, ray1, ray2]
      · refine ⟨s, ?_⟩
        simp [gammaParam, not_le.mpr (lt_of_le_of_ne hs (Ne.symm hs0)), hst]

lemma gammaParam_image_closed_union_isClosed (W : OpenWedge) (hy1 : W.y.1 < 0) (hy2 : W.y.2 < 0)
    {S : Set ℝ} (hS : IsClosed S) :
    IsClosed (gammaParam W '' S ∪ {p ∈ bdWedge W | ¬ inOmega p}) := by
  have hT1 := rayExit_pos hy1 hy2 (d := dir1 W)
  have hT2 := rayExit_pos hy1 hy2 (d := dir2 W)
  let A1 : Set ℝ := {t : ℝ | 0 ≤ t ∧ ((t : WithTop ℝ) < rayExit W.y (dir1 W) →
    ∃ s ≤ 0, stretch (rayExit W.y (dir1 W)) (-s) = t ∧ s ∈ S)}
  let A2 : Set ℝ := {t : ℝ | 0 ≤ t ∧ ((t : WithTop ℝ) < rayExit W.y (dir2 W) →
    ∃ s ≥ 0, stretch (rayExit W.y (dir2 W)) s = t ∧ s ∈ S)}
  have hset : gammaParam W '' S ∪ {p ∈ bdWedge W | ¬ inOmega p} = ray1 W '' A1 ∪ ray2 W '' A2 := by
    ext p; constructor
    · rintro (⟨s, hs, rfl⟩ | ⟨hp_bd, hp_not⟩)
      · unfold gammaParam
        split_ifs with hs0
        · left
          refine ⟨stretch (rayExit W.y (dir1 W)) (-s), ⟨stretch_nonneg hT1 (by linarith),
            fun _ => ⟨s, hs0, rfl, hs⟩⟩, rfl⟩
        · right
          refine ⟨stretch (rayExit W.y (dir2 W)) s, ⟨stretch_nonneg hT2 (by linarith),
            fun _ => ⟨s, by linarith, rfl, hs⟩⟩, rfl⟩
      · rcases (bdWedge_iff_rays W p).mp hp_bd with ⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩
        · left
          refine ⟨t, ⟨ht, fun hlt => False.elim (hp_not ((ray_inOmega_iff hy1 hy2 ht).mpr hlt))⟩, rfl⟩
        · right
          refine ⟨t, ⟨ht, fun hlt => False.elim (hp_not ((ray_inOmega_iff hy1 hy2 ht).mpr hlt))⟩, rfl⟩
    · rintro (⟨t, ⟨ht, hA1⟩, rfl⟩ | ⟨t, ⟨ht, hA2⟩, rfl⟩)
      · by_cases hlt : (t : WithTop ℝ) < rayExit W.y (dir1 W)
        · obtain ⟨s, hs0, hst, hsS⟩ := hA1 hlt
          left; exact ⟨s, hsS, by simp [gammaParam, hs0, hst]⟩
        · right; exact ⟨ray1_mem_bdWedge W ht, fun hom => hlt ((ray_inOmega_iff hy1 hy2 ht).mp hom)⟩
      · by_cases hlt : (t : WithTop ℝ) < rayExit W.y (dir2 W)
        · obtain ⟨s, hs0, hst, hsS⟩ := hA2 hlt
          left; refine ⟨s, hsS, ?_⟩
          by_cases hs_zero : s = 0
          · subst hs_zero; rw [stretch_zero] at hst; simp [gammaParam, stretch_zero, ← hst, ray1, ray2]
          · simp [gammaParam, not_le.mpr (lt_of_le_of_ne hs0 (Ne.symm hs_zero)), hst]
        · right; exact ⟨ray2_mem_bdWedge W ht, fun hom => hlt ((ray_inOmega_iff hy1 hy2 ht).mp hom)⟩
  rw [hset]
  have hA1_closed : IsClosed A1 := by
    rw [← isOpen_compl_iff]
    cases hT : rayExit W.y (dir1 W) with
    | top =>
      have hcomp : A1ᶜ = Set.Iio 0 ∪ (fun t : ℝ => -t) ⁻¹' Sᶜ := by
        ext t; constructor
        · intro ht
          by_cases ht0 : t < 0
          · exact Or.inl ht0
          · right
            have ht_nn : 0 ≤ t := not_lt.mp ht0
            intro hneg
            apply ht
            refine ⟨ht_nn, fun _ => ⟨-t, by linarith, by simp [stretch, hT], hneg⟩⟩
        · rintro (ht0 | hnot) ⟨ht_nn, hmem⟩
          · change t < 0 at ht0; linarith
          · obtain ⟨s, _, hst, hsS⟩ := hmem (by rw [hT]; exact WithTop.coe_lt_top t)
            simp [stretch, hT] at hst
            have hs_eq : s = -t := by linarith
            rw [hs_eq] at hsS
            exact hnot hsS
      rw [hcomp]
      exact isOpen_Iio.union (hS.isOpen_compl.preimage continuous_neg)
    | coe t₀ =>
      have ht₀ : 0 < t₀ := WithTop.coe_lt_coe.mp (by rw [← hT]; exact hT1)
      have hcomp : A1ᶜ = Set.Iio 0 ∪ (Set.Iio t₀ ∩ (fun t : ℝ => -(t / (t₀ - t))) ⁻¹' Sᶜ) := by
        ext t; constructor
        · intro ht
          by_cases ht0 : t < 0
          · exact Or.inl ht0
          · right
            have ht_nn : 0 ≤ t := not_lt.mp ht0
            have htt₀ : t < t₀ := by
              by_contra hge
              apply ht
              refine ⟨ht_nn, fun hlt => False.elim ?_⟩
              rw [hT, WithTop.coe_lt_coe] at hlt
              linarith
            refine ⟨htt₀, fun hmem => ht ⟨ht_nn, fun _ => ⟨-(t / (t₀ - t)), ?_, ?_, hmem⟩⟩⟩
            · have : 0 ≤ t / (t₀ - t) := div_nonneg ht_nn (by linarith)
              linarith
            · dsimp [stretch]; simp [hT]
              have hne1 : t₀ - t ≠ 0 := by linarith
              have hne2 : 1 + t / (t₀ - t) ≠ 0 := by
                have : 0 ≤ t / (t₀ - t) := div_nonneg ht_nn (by linarith)
                linarith
              field_simp [hne1, hne2, ne_of_gt ht₀]; ring
        · rintro (ht0 | ⟨htt₀, hnot⟩) ⟨ht_nn, hmem⟩
          · change t < 0 at ht0; linarith
          · change t < t₀ at htt₀
            obtain ⟨s, hs0, hst, hsS⟩ := hmem (by rw [hT, WithTop.coe_lt_coe]; exact htt₀)
            simp only [stretch, hT] at hst
            have hs_eq : s = -(t / (t₀ - t)) := by
              have h1s : 0 < 1 + (-s) := by linarith
              have hmul := (div_eq_iff (ne_of_gt h1s)).mp hst
              have hne1 : t₀ - t ≠ 0 := by linarith
              have hdiv : -s = t / (t₀ - t) := (eq_div_iff hne1).mpr (by linarith [hmul])
              linarith [hdiv]
            rw [hs_eq] at hsS
            exact hnot hsS
      rw [hcomp]
      refine isOpen_Iio.union ?_
      have hcont : ContinuousOn (fun t : ℝ => -(t / (t₀ - t))) (Set.Iio t₀) := by
        refine ContinuousOn.neg (ContinuousOn.div continuousOn_id (continuousOn_const.sub continuousOn_id) ?_)
        intro t ht; change t < t₀ at ht; linarith
      exact hcont.isOpen_inter_preimage isOpen_Iio hS.isOpen_compl
  have hA2_closed : IsClosed A2 := by
    rw [← isOpen_compl_iff]
    cases hT : rayExit W.y (dir2 W) with
    | top =>
      have hcomp : A2ᶜ = Set.Iio 0 ∪ id ⁻¹' Sᶜ := by
        ext t; constructor
        · intro ht
          by_cases ht0 : t < 0
          · exact Or.inl ht0
          · right
            have ht_nn : 0 ≤ t := not_lt.mp ht0
            intro hmem
            apply ht
            refine ⟨ht_nn, fun _ => ⟨t, ht_nn, by simp [stretch, hT], hmem⟩⟩
        · rintro (ht0 | hnot) ⟨ht_nn, hmem⟩
          · change t < 0 at ht0; linarith
          · obtain ⟨s, _, hst, hsS⟩ := hmem (by rw [hT]; exact WithTop.coe_lt_top t)
            simp [stretch, hT] at hst
            rw [hst] at hsS
            exact hnot hsS
      rw [hcomp]
      exact isOpen_Iio.union hS.isOpen_compl
    | coe t₀ =>
      have ht₀ : 0 < t₀ := WithTop.coe_lt_coe.mp (by rw [← hT]; exact hT2)
      have hcomp : A2ᶜ = Set.Iio 0 ∪ (Set.Iio t₀ ∩ (fun t : ℝ => t / (t₀ - t)) ⁻¹' Sᶜ) := by
        ext t; constructor
        · intro ht
          by_cases ht0 : t < 0
          · exact Or.inl ht0
          · right
            have ht_nn : 0 ≤ t := not_lt.mp ht0
            have htt₀ : t < t₀ := by
              by_contra hge
              apply ht
              refine ⟨ht_nn, fun hlt => False.elim ?_⟩
              rw [hT, WithTop.coe_lt_coe] at hlt
              linarith
            refine ⟨htt₀, fun hmem => ht ⟨ht_nn, fun _ => ⟨t / (t₀ - t), div_nonneg ht_nn (by linarith), ?_, hmem⟩⟩⟩
            dsimp [stretch]; simp [hT]
            have hne1 : t₀ - t ≠ 0 := by linarith
            have hne2 : 1 + t / (t₀ - t) ≠ 0 := by
              have : 0 ≤ t / (t₀ - t) := div_nonneg ht_nn (by linarith)
              linarith
            field_simp [hne1, hne2, ne_of_gt ht₀]; ring
        · rintro (ht0 | ⟨htt₀, hnot⟩) ⟨ht_nn, hmem⟩
          · change t < 0 at ht0; linarith
          · change t < t₀ at htt₀
            obtain ⟨s, hs0, hst, hsS⟩ := hmem (by rw [hT, WithTop.coe_lt_coe]; exact htt₀)
            simp only [stretch, hT] at hst
            have hs_eq : s = t / (t₀ - t) := by
              have h1s : 0 < 1 + s := by linarith
              have hmul := (div_eq_iff (ne_of_gt h1s)).mp hst
              have hne1 : t₀ - t ≠ 0 := by linarith
              exact (eq_div_iff hne1).mpr (by linarith [hmul])
            rw [hs_eq] at hsS
            exact hnot hsS
      rw [hcomp]
      refine isOpen_Iio.union ?_
      have hcont : ContinuousOn (fun t : ℝ => t / (t₀ - t)) (Set.Iio t₀) := by
        refine ContinuousOn.div continuousOn_id (continuousOn_const.sub continuousOn_id) ?_
        intro t ht; change t < t₀ at ht; linarith
      exact hcont.isOpen_inter_preimage isOpen_Iio hS.isOpen_compl
  exact ((ray1_isClosedEmbedding W).isClosedMap A1 hA1_closed).union
        ((ray2_isClosedEmbedding W).isClosedMap A2 hA2_closed)

/-! ## Connected Components and Arc-Splitting Face Bound -/

def Comps (U : Set (ℝ × ℝ)) : Set (Set (ℝ × ℝ)) :=
  {C | ∃ x ∈ U, C = connectedComponentIn U x}

lemma comps_omega_card : (Comps {p : ℝ × ℝ | inOmega p}).encard = 1 := by
  obtain ⟨⟨p₀, hp₀⟩, hpre⟩ := isConnected_omega
  have heq : Comps {p : ℝ × ℝ | inOmega p} = {{p : ℝ × ℝ | inOmega p}} := by
    ext C; constructor
    · rintro ⟨x, hx, rfl⟩
      exact hpre.connectedComponentIn hx
    · intro hC
      rw [Set.mem_singleton_iff.mp hC]
      exact ⟨p₀, hp₀, (hpre.connectedComponentIn hp₀).symm⟩
  rw [heq, Set.encard_singleton]

private lemma union_balls_preconnected
    {α : Set (ℝ × ℝ)} (hα_conn : IsPreconnected α)
    (r : ℝ × ℝ → ℝ) (B : (ℝ × ℝ) → Set (ℝ × ℝ))
    (hr_pos : ∀ z ∈ α, 0 < r z)
    (_hB_ne : ∀ z ∈ α, (B z).Nonempty)
    (hB_conn : ∀ z ∈ α, IsPreconnected (B z))
    (hB_ov : ∀ z ∈ α, ∀ z' ∈ α, z' ∈ Metric.ball z (r z) → (B z ∩ B z').Nonempty) :
    IsPreconnected (⋃ z ∈ α, B z) := by
  intro S T hS hT hsub hS_ne hT_ne
  by_contra hnot_inter
  rw [Set.not_nonempty_iff_eq_empty] at hnot_inter
  have hB_choice : ∀ z ∈ α, B z ⊆ S ∨ B z ⊆ T := by
    intro z hz
    have hBz_sub : B z ⊆ S ∪ T := (Set.subset_biUnion_of_mem (u := fun z => B z) hz).trans hsub
    by_cases hBS : B z ⊆ S
    · exact Or.inl hBS
    · right
      by_contra hBT
      obtain ⟨pT, hpT_B, hpT_S⟩ := Set.not_subset.mp hBS
      have hpT_T : pT ∈ T := (hBz_sub hpT_B).resolve_left hpT_S
      obtain ⟨pS, hpS_B, hpS_T⟩ := Set.not_subset.mp hBT
      have hpS_S : pS ∈ S := (hBz_sub hpS_B).resolve_right hpS_T
      obtain ⟨w, hwB, hwS, hwT⟩ := hB_conn z hz S T hS hT hBz_sub ⟨pS, hpS_B, hpS_S⟩ ⟨pT, hpT_B, hpT_T⟩
      have hwU : w ∈ ⋃ z' ∈ α, B z' := Set.mem_biUnion hz hwB
      exact (Set.eq_empty_iff_forall_notMem.mp hnot_inter w) ⟨hwU, hwS, hwT⟩
  let αS : Set (ℝ × ℝ) := {z ∈ α | B z ⊆ S}
  let αT : Set (ℝ × ℝ) := {z ∈ α | B z ⊆ T}
  let OS : Set (ℝ × ℝ) := ⋃ z ∈ αS, Metric.ball z (r z)
  let OT : Set (ℝ × ℝ) := ⋃ z ∈ αT, Metric.ball z (r z)
  have hOS : IsOpen OS := isOpen_biUnion fun z _ => Metric.isOpen_ball
  have hOT : IsOpen OT := isOpen_biUnion fun z _ => Metric.isOpen_ball
  have hα_sub : α ⊆ OS ∪ OT := by
    intro z hz
    rcases hB_choice z hz with hBS | hBT
    · left; exact Set.mem_biUnion ⟨hz, hBS⟩ (Metric.mem_ball_self (hr_pos z hz))
    · right; exact Set.mem_biUnion ⟨hz, hBT⟩ (Metric.mem_ball_self (hr_pos z hz))
  have hα_S_ne : (α ∩ OS).Nonempty := by
    obtain ⟨w, hwU, hwS⟩ := hS_ne
    rw [Set.mem_iUnion₂] at hwU
    rcases hwU with ⟨z, hz, hwB⟩
    rcases hB_choice z hz with hBS | hBT
    · exact ⟨z, hz, Set.mem_biUnion ⟨hz, hBS⟩ (Metric.mem_ball_self (hr_pos z hz))⟩
    · exact False.elim ((Set.eq_empty_iff_forall_notMem.mp hnot_inter w)
        ⟨Set.mem_biUnion hz hwB, hwS, hBT hwB⟩)
  have hα_T_ne : (α ∩ OT).Nonempty := by
    obtain ⟨w, hwU, hwT⟩ := hT_ne
    rw [Set.mem_iUnion₂] at hwU
    rcases hwU with ⟨z, hz, hwB⟩
    rcases hB_choice z hz with hBS | hBT
    · exact False.elim ((Set.eq_empty_iff_forall_notMem.mp hnot_inter w)
        ⟨Set.mem_biUnion hz hwB, hBS hwB, hwT⟩)
    · exact ⟨z, hz, Set.mem_biUnion ⟨hz, hBT⟩ (Metric.mem_ball_self (hr_pos z hz))⟩
  obtain ⟨w, hw, hwS, hwT⟩ := hα_conn OS OT hOS hOT hα_sub hα_S_ne hα_T_ne
  rw [Set.mem_iUnion₂] at hwS hwT
  rcases hwS with ⟨zS, ⟨hzS, hBS⟩, hwbS⟩
  rcases hwT with ⟨zT, ⟨hzT, hBT⟩, hwbT⟩
  obtain ⟨pS, hpS1, hpS2⟩ := hB_ov zS hzS w hw hwbS
  obtain ⟨pT, hpT1, hpT2⟩ := hB_ov zT hzT w hw hwbT
  rcases hB_choice w hw with hwS' | hwT'
  · exact (Set.eq_empty_iff_forall_notMem.mp hnot_inter pT)
      ⟨Set.mem_biUnion hzT hpT1, hwS' hpT2, hBT hpT1⟩
  · exact (Set.eq_empty_iff_forall_notMem.mp hnot_inter pS)
      ⟨Set.mem_biUnion hzS hpS1, hBS hpS1, hwT' hpS2⟩

lemma comps_remove_arc
    {U α : Set (ℝ × ℝ)} (_hU : IsOpen U) (hα_sub : α ⊆ U)
    (hα_ne : α.Nonempty) (hα_conn : IsPreconnected α) (hUα_open : IsOpen (U \ α))
    (r : ℝ × ℝ → ℝ) (BL BR : (ℝ × ℝ) → Set (ℝ × ℝ))
    (hr_pos : ∀ z ∈ α, 0 < r z)
    (hball_sub : ∀ z ∈ α, Metric.ball z (r z) ⊆ U)
    (hball_split : ∀ z ∈ α, Metric.ball z (r z) \ α = BL z ∪ BR z)
    (hBL_ne : ∀ z ∈ α, (BL z).Nonempty)
    (hBL_conn : ∀ z ∈ α, IsPreconnected (BL z))
    (hBR_ne : ∀ z ∈ α, (BR z).Nonempty)
    (hBR_conn : ∀ z ∈ α, IsPreconnected (BR z))
    (hBL_ov : ∀ z ∈ α, ∀ z' ∈ α, z' ∈ Metric.ball z (r z) → (BL z ∩ BL z').Nonempty)
    (hBR_ov : ∀ z ∈ α, ∀ z' ∈ α, z' ∈ Metric.ball z (r z) → (BR z ∩ BR z').Nonempty) :
    (Comps (U \ α)).encard ≤ (Comps U).encard + 1 := by
  obtain ⟨z₀, hz₀⟩ := hα_ne
  let F : Set (ℝ × ℝ) := connectedComponentIn U z₀
  have hF_mem : F ∈ Comps U := ⟨z₀, hα_sub hz₀, rfl⟩
  have hF_conn : IsPreconnected F := isPreconnected_connectedComponentIn
  have hα_sub_F : α ⊆ F := hα_conn.subset_connectedComponentIn hz₀ hα_sub
  let UL : Set (ℝ × ℝ) := ⋃ z ∈ α, BL z
  let UR : Set (ℝ × ℝ) := ⋃ z ∈ α, BR z
  have hBL_sub : ∀ z ∈ α, BL z ⊆ U \ α := by
    intro z hz p hp
    have hmem : p ∈ Metric.ball z (r z) \ α := by rw [hball_split z hz]; exact Or.inl hp
    exact ⟨hball_sub z hz hmem.1, hmem.2⟩
  have hBR_sub : ∀ z ∈ α, BR z ⊆ U \ α := by
    intro z hz p hp
    have hmem : p ∈ Metric.ball z (r z) \ α := by rw [hball_split z hz]; exact Or.inr hp
    exact ⟨hball_sub z hz hmem.1, hmem.2⟩
  have hUL_sub : UL ⊆ U \ α := Set.iUnion₂_subset hBL_sub
  have hUR_sub : UR ⊆ U \ α := Set.iUnion₂_subset hBR_sub
  have hUL_conn : IsPreconnected UL :=
    union_balls_preconnected hα_conn r BL hr_pos hBL_ne hBL_conn hBL_ov
  have hUR_conn : IsPreconnected UR :=
    union_balls_preconnected hα_conn r BR hr_pos hBR_ne hBR_conn hBR_ov
  obtain ⟨uL, huL⟩ := hBL_ne z₀ hz₀
  obtain ⟨uR, huR⟩ := hBR_ne z₀ hz₀
  have huL_mem : uL ∈ UL := Set.mem_biUnion hz₀ huL
  have huR_mem : uR ∈ UR := Set.mem_biUnion hz₀ huR
  let CL : Set (ℝ × ℝ) := connectedComponentIn (U \ α) uL
  let CR : Set (ℝ × ℝ) := connectedComponentIn (U \ α) uR
  have hsub : Comps (U \ α) ⊆ insert CL (insert CR (Comps U \ {F})) := by
    have comp_eq_of_mem : ∀ {S : Set (ℝ × ℝ)} {a b p : ℝ × ℝ},
        p ∈ connectedComponentIn S a → p ∈ connectedComponentIn S b →
        connectedComponentIn S a = connectedComponentIn S b := fun hpa hpb =>
      (connectedComponentIn_eq hpa).trans (connectedComponentIn_eq hpb).symm
    rintro C ⟨x, hx, rfl⟩
    by_cases hxF : x ∈ F
    · have hmeet : (connectedComponentIn (U \ α) x ∩ (UL ∪ UR)).Nonempty := by
        by_contra hno
        rw [Set.not_nonempty_iff_eq_empty] at hno
        let A : Set (ℝ × ℝ) := connectedComponentIn (U \ α) x
        let B : Set (ℝ × ℝ) :=
          (⋃ y ∈ (U \ α) \ A, connectedComponentIn (U \ α) y) ∪
          (⋃ z ∈ α, Metric.ball z (r z))
        have hA_open : IsOpen A := hUα_open.connectedComponentIn
        have hB_open : IsOpen B :=
          (isOpen_biUnion fun _ _ => hUα_open.connectedComponentIn).union
            (isOpen_biUnion fun _ _ => Metric.isOpen_ball)
        have hF_sub : F ⊆ A ∪ B := by
          intro p hpF
          by_cases hpα : p ∈ α
          · right; right; exact Set.mem_biUnion hpα (Metric.mem_ball_self (hr_pos p hpα))
          · have hpU : p ∈ U \ α := ⟨connectedComponentIn_subset U z₀ hpF, hpα⟩
            by_cases hpA : p ∈ A
            · left; exact hpA
            · right; left
              exact Set.mem_biUnion ⟨hpU, hpA⟩ (mem_connectedComponentIn hpU)
        have hF_disj : F ∩ (A ∩ B) = ∅ := by
          rw [Set.eq_empty_iff_forall_notMem]
          rintro p ⟨_, hpA, hpB1 | hpB2⟩
          · rw [Set.mem_iUnion₂] at hpB1
            rcases hpB1 with ⟨y, ⟨hy, hyA⟩, hpy⟩
            have heq : A = connectedComponentIn (U \ α) y := comp_eq_of_mem hpA hpy
            rw [heq] at hyA
            exact hyA (mem_connectedComponentIn hy)
          · rw [Set.mem_iUnion₂] at hpB2
            rcases hpB2 with ⟨z, hz, hpb⟩
            have hp_not : p ∉ α := (connectedComponentIn_subset (U \ α) x hpA).2
            have hp_split : p ∈ BL z ∪ BR z := by
              rw [← hball_split z hz]; exact ⟨hpb, hp_not⟩
            have hp_U : p ∈ UL ∪ UR := by
              rcases hp_split with h1 | h2
              · left; exact Set.mem_biUnion hz h1
              · right; exact Set.mem_biUnion hz h2
            exact (Set.eq_empty_iff_forall_notMem.mp hno p) ⟨hpA, hp_U⟩
        obtain ⟨w, hwF, hwA, hwB⟩ := hF_conn A B hA_open hB_open hF_sub
          ⟨x, hxF, mem_connectedComponentIn hx⟩
          ⟨z₀, hα_sub_F hz₀, Or.inr (Set.mem_biUnion hz₀ (Metric.mem_ball_self (hr_pos z₀ hz₀)))⟩
        exact (Set.eq_empty_iff_forall_notMem.mp hF_disj w) ⟨hwF, hwA, hwB⟩
      obtain ⟨w, hwC, hwL | hwR⟩ := hmeet
      · left
        have hw_mem : w ∈ U \ α := hUL_sub hwL
        have h1 : connectedComponentIn (U \ α) x = connectedComponentIn (U \ α) w :=
          comp_eq_of_mem hwC (mem_connectedComponentIn hw_mem)
        have h2 : connectedComponentIn (U \ α) w = CL := by
          have hsub1 : UL ⊆ connectedComponentIn (U \ α) uL :=
            hUL_conn.subset_connectedComponentIn huL_mem hUL_sub
          exact comp_eq_of_mem (mem_connectedComponentIn hw_mem) (hsub1 hwL)
        exact h1.trans h2
      · right; left
        have hw_mem : w ∈ U \ α := hUR_sub hwR
        have h1 : connectedComponentIn (U \ α) x = connectedComponentIn (U \ α) w :=
          comp_eq_of_mem hwC (mem_connectedComponentIn hw_mem)
        have h2 : connectedComponentIn (U \ α) w = CR := by
          have hsub1 : UR ⊆ connectedComponentIn (U \ α) uR :=
            hUR_conn.subset_connectedComponentIn huR_mem hUR_sub
          exact comp_eq_of_mem (mem_connectedComponentIn hw_mem) (hsub1 hwR)
        exact h1.trans h2
    · right; right
      let F' := connectedComponentIn U x
      have hxU : x ∈ U := hx.1
      have hF'_mem : F' ∈ Comps U := ⟨x, hxU, rfl⟩
      have hF'_ne : F' ≠ F := by
        intro heq; apply hxF; rw [← heq]; exact mem_connectedComponentIn hxU
      have hF'_disj : Disjoint F' F := by
        rw [Set.disjoint_left]
        intro p hp1 hp2
        exact hF'_ne (comp_eq_of_mem hp1 hp2)
      have hF'_sub : F' ⊆ U \ α := by
        intro p hp
        refine ⟨connectedComponentIn_subset U x hp, fun hpα => ?_⟩
        exact Set.disjoint_left.mp hF'_disj hp (hα_sub_F hpα)
      have hC_eq : connectedComponentIn (U \ α) x = F' := by
        apply Set.Subset.antisymm
        · exact connectedComponentIn_mono x Set.sdiff_subset
        · exact isPreconnected_connectedComponentIn.subset_connectedComponentIn
            (mem_connectedComponentIn hxU) hF'_sub
      rw [hC_eq]
      exact ⟨hF'_mem, hF'_ne⟩
  calc (Comps (U \ α)).encard
      ≤ (insert CL (insert CR (Comps U \ {F}))).encard := Set.encard_le_encard hsub
    _ ≤ (insert CR (Comps U \ {F})).encard + 1 := Set.encard_insert_le _ _
    _ ≤ ((Comps U \ {F}).encard + 1) + 1 := add_le_add (Set.encard_insert_le _ _) le_rfl
    _ = (Comps U).encard + 1 := by
        rw [add_assoc, add_comm 1 1, ← add_assoc, Set.encard_sdiff_singleton_add_one hF_mem]

/-! ## Segment Decomposition and Arrangement Face Count -/

def seg : (xs : List ℝ) → Fin (xs.length + 1) → Set ℝ
  | [], _ => Set.univ
  | a :: _, ⟨0, _⟩ => Set.Iio a
  | a :: tl, ⟨k + 1, hk⟩ => seg tl ⟨k, by simp at hk; omega⟩ ∩ Set.Ioi a

lemma seg_isOpen : ∀ (xs : List ℝ) (i : Fin (xs.length + 1)), IsOpen (seg xs i)
  | [], _ => isOpen_univ
  | _ :: _, ⟨0, _⟩ => isOpen_Iio
  | _ :: tl, ⟨k + 1, hk⟩ => (seg_isOpen tl ⟨k, by simp at hk; omega⟩).inter isOpen_Ioi

lemma seg_convex : ∀ (xs : List ℝ) (i : Fin (xs.length + 1)), Convex ℝ (seg xs i)
  | [], _ => convex_univ
  | _ :: _, ⟨0, _⟩ => convex_Iio _
  | a :: tl, ⟨k + 1, hk⟩ => (seg_convex tl ⟨k, by simp at hk; omega⟩).inter (convex_Ioi a)

lemma seg_isPreconnected (xs : List ℝ) (i : Fin (xs.length + 1)) : IsPreconnected (seg xs i) :=
  (seg_convex xs i).isPreconnected

lemma seg_nonempty : ∀ (xs : List ℝ), xs.SortedLT → ∀ (i : Fin (xs.length + 1)), (seg xs i).Nonempty
  | [], _, _ => ⟨0, trivial⟩
  | a :: _, _, ⟨0, _⟩ => ⟨a - 1, by simp [seg]⟩
  | a :: [], _, ⟨1, _⟩ => ⟨a + 1, by simp [seg]⟩
  | a :: b :: tl', hsort, ⟨1, _⟩ => by
    have hab : a < b := hsort (Fin.mk_lt_mk.mpr (Nat.zero_lt_one) :
      (⟨0, by simp⟩ : Fin (a :: b :: tl').length) < ⟨1, by simp⟩)
    exact ⟨(a + b) / 2, by simp [seg]; constructor <;> linarith⟩
  | a :: b :: tl', hsort, ⟨k + 2, hk⟩ => by
    have hab : a < b := hsort (Fin.mk_lt_mk.mpr (Nat.zero_lt_one) :
      (⟨0, by simp⟩ : Fin (a :: b :: tl').length) < ⟨1, by simp⟩)
    have htl : (b :: tl').SortedLT := fun i j hij => hsort (Fin.succ_lt_succ_iff.mpr hij)
    obtain ⟨w, hw⟩ := seg_nonempty (b :: tl') htl ⟨k + 1, by dsimp [List.length] at hk ⊢; omega⟩
    have hwb : b < w := hw.2
    exact ⟨w, hw, hab.trans hwb⟩

lemma seg_disjoint_list : ∀ (xs : List ℝ), xs.SortedLT →
    ∀ (i : Fin (xs.length + 1)), seg xs i ⊆ {s : ℝ | s ∉ xs}
  | [], _, _, _, _, hmem => by simp at hmem
  | a :: tl, hsort, ⟨0, _⟩, s, hs, hmem => by
    change s < a at hs
    rcases List.mem_cons.mp hmem with rfl | htl
    · exact lt_irrefl _ hs
    · obtain ⟨j, hj⟩ := List.mem_iff_get.mp htl
      have has : a < s := by
        rw [← hj]
        exact hsort (Fin.mk_lt_mk.mpr (Nat.zero_lt_succ j.val) :
          (⟨0, by simp⟩ : Fin (a :: tl).length) < ⟨j.val + 1, by simp⟩)
      linarith
  | a :: tl, hsort, ⟨k + 1, hk⟩, s, hs, hmem => by
    have htl_sort : tl.SortedLT := fun i j hij => hsort (Fin.succ_lt_succ_iff.mpr hij)
    rcases List.mem_cons.mp hmem with rfl | htl
    · exact lt_irrefl s (Set.mem_Ioi.mp hs.2)
    · exact seg_disjoint_list tl htl_sort ⟨k, by dsimp [List.length] at hk ⊢; omega⟩ hs.1 htl

lemma compl_list_subset_iUnion_seg : ∀ (xs : List ℝ),
    {s : ℝ | s ∉ xs} ⊆ ⋃ i : Fin (xs.length + 1), seg xs i
  | [], s, _ => Set.mem_iUnion.mpr ⟨0, trivial⟩
  | a :: tl, s, hs => by
    have hne : s ≠ a := fun h => hs (h ▸ List.mem_cons_self)
    have htl : s ∉ tl := fun h => hs (List.mem_cons_of_mem _ h)
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact Set.mem_iUnion.mpr ⟨0, hlt⟩
    · have hmem := compl_list_subset_iUnion_seg tl htl
      rw [Set.mem_iUnion] at hmem
      obtain ⟨k, hk⟩ := hmem
      exact Set.mem_iUnion.mpr ⟨k.succ, hk, hgt⟩

lemma closure_seg_subset : ∀ (xs : List ℝ) (i : Fin (xs.length + 1)),
    closure (seg xs i) ⊆ seg xs i ∪ {s : ℝ | s ∈ xs}
  | [], _, s, _ => Or.inl trivial
  | a :: _, ⟨0, _⟩, s, hs => by
    have hs' : s ≤ a := by simpa [seg] using hs
    rcases lt_or_eq_of_le hs' with h | rfl
    · exact Or.inl h
    · exact Or.inr List.mem_cons_self
  | a :: tl, ⟨k + 1, hk⟩, s, hs => by
    have h1 : s ∈ closure (seg tl ⟨k, by simp at hk; omega⟩) :=
      closure_mono Set.inter_subset_left hs
    have h2 : a ≤ s := by
      have := closure_mono Set.inter_subset_right hs
      simpa using this
    rcases lt_or_eq_of_le h2 with ha_lt | rfl
    · rcases closure_seg_subset tl ⟨k, by simp at hk; omega⟩ h1 with hseg | htl
      · exact Or.inl ⟨hseg, ha_lt⟩
      · exact Or.inr (List.mem_cons_of_mem _ htl)
    · exact Or.inr List.mem_cons_self

/-! ## Pairwise Intersection Bounds -/

lemma inter_card_le_four {W : Fin 5 → OpenWedge} (hGP : GeneralPosition W)
    {i j : Fin 5} (hij : i ≠ j) :
    (bdWedge (W i) ∩ bdWedge (W j)).Finite ∧ (bdWedge (W i) ∩ bdWedge (W j)).ncard ≤ 4 := by
  have huniq : ∀ (bi bj : Bool), ∃ p₀ : ℝ × ℝ,
      lineAt W (i, bi) p₀ = 0 ∧ lineAt W (j, bj) p₀ = 0 ∧
      (∀ p : ℝ × ℝ, lineAt W (i, bi) p = 0 → lineAt W (j, bj) p = 0 → p = p₀) := by
    intro bi bj
    have hne : (i, bi) ≠ (j, bj) := fun h => hij (congrArg Prod.fst h)
    have hdet := hGP.no_parallel (i, bi) (j, bj) hne
    let a1 := (normal W (i, bi)).1; let a2 := (normal W (i, bi)).2
    let b1 := (normal W (j, bj)).1; let b2 := (normal W (j, bj)).2
    let ca := a1 * (W i).y.1 + a2 * (W i).y.2
    let cb := b1 * (W j).y.1 + b2 * (W j).y.2
    let det := a1 * b2 - a2 * b1
    have hdet' : det ≠ 0 := hdet
    refine ⟨((b2 * ca - a2 * cb) / det, (-b1 * ca + a1 * cb) / det), ?_, ?_, fun p hp1 hp2 => ?_⟩
    · dsimp [lineAt]
      change a1 * ((b2 * ca - a2 * cb) / det - (W i).y.1) +
             a2 * ((-b1 * ca + a1 * cb) / det - (W i).y.2) = 0
      field_simp [hdet']; dsimp [det, ca, cb]; ring
    · dsimp [lineAt]
      change b1 * ((b2 * ca - a2 * cb) / det - (W j).y.1) +
             b2 * ((-b1 * ca + a1 * cb) / det - (W j).y.2) = 0
      field_simp [hdet']; dsimp [det, ca, cb]; ring
    · dsimp [lineAt] at hp1 hp2
      have h1 : det * p.1 = b2 * ca - a2 * cb := by
        change (a1 * b2 - a2 * b1) * p.1 = b2 * (a1 * (W i).y.1 + a2 * (W i).y.2) -
          a2 * (b1 * (W j).y.1 + b2 * (W j).y.2)
        linear_combination b2 * hp1 - a2 * hp2
      have h2 : det * p.2 = -b1 * ca + a1 * cb := by
        change (a1 * b2 - a2 * b1) * p.2 = -b1 * (a1 * (W i).y.1 + a2 * (W i).y.2) +
          a1 * (b1 * (W j).y.1 + b2 * (W j).y.2)
        linear_combination -b1 * hp1 + a1 * hp2
      ext
      · exact (eq_div_iff hdet).mpr (by rw [mul_comm]; exact h1)
      · exact (eq_div_iff hdet).mpr (by rw [mul_comm]; exact h2)
  let pt (bi bj : Bool) : ℝ × ℝ := (huniq bi bj).choose
  have hpt1 : ∀ bi bj, lineAt W (i, bi) (pt bi bj) = 0 := fun bi bj => (huniq bi bj).choose_spec.1
  have hpt2 : ∀ bi bj, lineAt W (j, bj) (pt bi bj) = 0 := fun bi bj => (huniq bi bj).choose_spec.2.1
  have hpt : ∀ bi bj p, lineAt W (i, bi) p = 0 → lineAt W (j, bj) p = 0 → p = pt bi bj :=
    fun bi bj => (huniq bi bj).choose_spec.2.2
  let S4 : Finset (ℝ × ℝ) := {pt true true, pt true false, pt false true, pt false false}
  have hsub : bdWedge (W i) ∩ bdWedge (W j) ⊆ (S4 : Set (ℝ × ℝ)) := by
    rintro p ⟨hi, hj⟩
    obtain ⟨_, hi_eq⟩ := (bdWedge_iff_closure_eq_zero (W i) p).mp hi
    obtain ⟨_, hj_eq⟩ := (bdWedge_iff_closure_eq_zero (W j) p).mp hj
    rcases hi_eq with hi1 | hi2 <;> rcases hj_eq with hj1 | hj2
    · have := hpt true true p (by simpa [lineAt, normal] using hi1) (by simpa [lineAt, normal] using hj1)
      simp [S4, this]
    · have := hpt true false p (by simpa [lineAt, normal] using hi1) (by simpa [lineAt, normal] using hj2)
      simp [S4, this]
    · have := hpt false true p (by simpa [lineAt, normal] using hi2) (by simpa [lineAt, normal] using hj1)
      simp [S4, this]
    · have := hpt false false p (by simpa [lineAt, normal] using hi2) (by simpa [lineAt, normal] using hj2)
      simp [S4, this]
  refine ⟨S4.finite_toSet.subset hsub, ?_⟩
  calc (bdWedge (W i) ∩ bdWedge (W j)).ncard
      ≤ (S4 : Set (ℝ × ℝ)).ncard := Set.ncard_le_ncard hsub S4.finite_toSet
    _ = S4.card := Set.ncard_coe_finset S4
    _ ≤ 4 := by
        dsimp [S4]
        exact (Finset.card_insert_le _ _).trans (Nat.succ_le_succ
          ((Finset.card_insert_le _ _).trans (Nat.succ_le_succ
            ((Finset.card_insert_le _ _).trans (Nat.succ_le_succ (by simp))))))

lemma gamma_inter_finite {W : Fin 5 → OpenWedge} (hGP : GeneralPosition W)
    {i j : Fin 5} (hij : i ≠ j) :
    (Gamma (W i) ∩ Gamma (W j)).Finite :=
  (inter_card_le_four hGP hij).1.subset fun _ ⟨⟨hi, _⟩, ⟨hj, _⟩⟩ => ⟨hi, hj⟩

lemma quad_four_inter_rays {W : Fin 5 → OpenWedge} (hGP : GeneralPosition W)
    {i j : Fin 5} (hij : i ≠ j)
    (h4 : ¬ (Gamma (W i) ∩ Gamma (W j)).ncard ≤ 3) :
    ∀ bi bj : Bool, ∃ ti > 0, ∃ tj > 0,
      (if bi then ray1 (W i) ti else ray2 (W i) ti) =
      (if bj then ray1 (W j) tj else ray2 (W j) tj) ∧
      (if bi then ray1 (W i) ti else ray2 (W i) ti) ∈ Gamma (W i) ∩ Gamma (W j) := by
  have huniq : ∀ (bi bj : Bool), ∃ p₀ : ℝ × ℝ,
      lineAt W (i, bi) p₀ = 0 ∧ lineAt W (j, bj) p₀ = 0 ∧
      (∀ p : ℝ × ℝ, lineAt W (i, bi) p = 0 → lineAt W (j, bj) p = 0 → p = p₀) := by
    intro bi bj
    have hne : (i, bi) ≠ (j, bj) := fun h => hij (congrArg Prod.fst h)
    have hdet := hGP.no_parallel (i, bi) (j, bj) hne
    let a1 := (normal W (i, bi)).1; let a2 := (normal W (i, bi)).2
    let b1 := (normal W (j, bj)).1; let b2 := (normal W (j, bj)).2
    let ca := a1 * (W i).y.1 + a2 * (W i).y.2
    let cb := b1 * (W j).y.1 + b2 * (W j).y.2
    let det := a1 * b2 - a2 * b1
    have hdet' : det ≠ 0 := hdet
    refine ⟨((b2 * ca - a2 * cb) / det, (-b1 * ca + a1 * cb) / det), ?_, ?_, fun p hp1 hp2 => ?_⟩
    · dsimp [lineAt]
      change a1 * ((b2 * ca - a2 * cb) / det - (W i).y.1) +
             a2 * ((-b1 * ca + a1 * cb) / det - (W i).y.2) = 0
      field_simp [hdet']; dsimp [det, ca, cb]; ring
    · dsimp [lineAt]
      change b1 * ((b2 * ca - a2 * cb) / det - (W j).y.1) +
             b2 * ((-b1 * ca + a1 * cb) / det - (W j).y.2) = 0
      field_simp [hdet']; dsimp [det, ca, cb]; ring
    · dsimp [lineAt] at hp1 hp2
      have h1 : det * p.1 = b2 * ca - a2 * cb := by
        change (a1 * b2 - a2 * b1) * p.1 = b2 * (a1 * (W i).y.1 + a2 * (W i).y.2) -
          a2 * (b1 * (W j).y.1 + b2 * (W j).y.2)
        linear_combination b2 * hp1 - a2 * hp2
      have h2 : det * p.2 = -b1 * ca + a1 * cb := by
        change (a1 * b2 - a2 * b1) * p.2 = -b1 * (a1 * (W i).y.1 + a2 * (W i).y.2) +
          a1 * (b1 * (W j).y.1 + b2 * (W j).y.2)
        linear_combination -b1 * hp1 + a1 * hp2
      ext
      · exact (eq_div_iff hdet).mpr (by rw [mul_comm]; exact h1)
      · exact (eq_div_iff hdet).mpr (by rw [mul_comm]; exact h2)
  let pt (bi bj : Bool) : ℝ × ℝ := (huniq bi bj).choose
  have hpt1 : ∀ bi bj, lineAt W (i, bi) (pt bi bj) = 0 := fun bi bj => (huniq bi bj).choose_spec.1
  have hpt2 : ∀ bi bj, lineAt W (j, bj) (pt bi bj) = 0 := fun bi bj => (huniq bi bj).choose_spec.2.1
  have hpt : ∀ bi bj p, lineAt W (i, bi) p = 0 → lineAt W (j, bj) p = 0 → p = pt bi bj :=
    fun bi bj => (huniq bi bj).choose_spec.2.2
  let S4 : Finset (ℝ × ℝ) := {pt true true, pt true false, pt false true, pt false false}
  have hsub : Gamma (W i) ∩ Gamma (W j) ⊆ (S4 : Set (ℝ × ℝ)) := by
    rintro p ⟨⟨hi, _⟩, ⟨hj, _⟩⟩
    obtain ⟨_, hi_eq⟩ := (bdWedge_iff_closure_eq_zero (W i) p).mp hi
    obtain ⟨_, hj_eq⟩ := (bdWedge_iff_closure_eq_zero (W j) p).mp hj
    rcases hi_eq with hi1 | hi2 <;> rcases hj_eq with hj1 | hj2
    · have := hpt true true p (by simpa [lineAt, normal] using hi1) (by simpa [lineAt, normal] using hj1)
      simp [S4, this]
    · have := hpt true false p (by simpa [lineAt, normal] using hi1) (by simpa [lineAt, normal] using hj2)
      simp [S4, this]
    · have := hpt false true p (by simpa [lineAt, normal] using hi2) (by simpa [lineAt, normal] using hj1)
      simp [S4, this]
    · have := hpt false false p (by simpa [lineAt, normal] using hi2) (by simpa [lineAt, normal] using hj2)
      simp [S4, this]
  have hmem_all : ∀ bi bj : Bool, pt bi bj ∈ Gamma (W i) ∩ Gamma (W j) := by
    intro bi bj
    by_contra hnot
    let S3 : Finset (ℝ × ℝ) := S4.erase (pt bi bj)
    have hsub3 : Gamma (W i) ∩ Gamma (W j) ⊆ (S3 : Set (ℝ × ℝ)) := by
      intro p hp
      have hpS4 : p ∈ S4 := hsub hp
      exact Finset.mem_coe.mpr (Finset.mem_erase.mpr ⟨fun heq => hnot (heq ▸ hp), hpS4⟩)
    have hpt_mem : pt bi bj ∈ S4 := by cases bi <;> cases bj <;> simp [S4]
    have hcard4 : S4.card ≤ 4 := by
      dsimp [S4]
      exact (Finset.card_insert_le _ _).trans (Nat.succ_le_succ
        ((Finset.card_insert_le _ _).trans (Nat.succ_le_succ
          ((Finset.card_insert_le _ _).trans (Nat.succ_le_succ (by simp))))))
    have hcard3 : S3.card ≤ 3 := by
      have hcard_eq := Finset.card_erase_add_one hpt_mem
      change S3.card + 1 = S4.card at hcard_eq
      omega
    have hle3 : (Gamma (W i) ∩ Gamma (W j)).ncard ≤ 3 := by
      calc (Gamma (W i) ∩ Gamma (W j)).ncard
          ≤ (S3 : Set (ℝ × ℝ)).ncard := Set.ncard_le_ncard hsub3 S3.finite_toSet
        _ = S3.card := Set.ncard_coe_finset S3
        _ ≤ 3 := hcard3
    exact h4 hle3
  intro bi bj
  have hp := hmem_all bi bj
  obtain ⟨⟨hi_bd, hi_om⟩, ⟨hj_bd, hj_om⟩⟩ := hp
  have hi_neq : pt bi bj ≠ (W i).y := by
    intro heq
    have hji : j ≠ i := hij.symm
    obtain ⟨_, hj_eq⟩ := (bdWedge_iff_closure_eq_zero (W j) (pt bi bj)).mp hj_bd
    rw [heq] at hj_eq
    rcases hj_eq with h1 | h2
    · exact gp_apex_not_on_line hGP hji true (by simpa [lineAt, normal] using h1)
    · exact gp_apex_not_on_line hGP hji false (by simpa [lineAt, normal] using h2)
  have hj_neq : pt bi bj ≠ (W j).y := by
    intro heq
    obtain ⟨_, hi_eq⟩ := (bdWedge_iff_closure_eq_zero (W i) (pt bi bj)).mp hi_bd
    rw [heq] at hi_eq
    rcases hi_eq with h1 | h2
    · exact gp_apex_not_on_line hGP hij true (by simpa [lineAt, normal] using h1)
    · exact gp_apex_not_on_line hGP hij false (by simpa [lineAt, normal] using h2)
  have hi_ray : ∃ ti > 0, pt bi bj = if bi then ray1 (W i) ti else ray2 (W i) ti := by
    have hnd := (W i).h_nondeg
    rcases (bdWedge_iff_rays (W i) (pt bi bj)).mp hi_bd with ⟨t, ht, hpt_eq⟩ | ⟨t, ht, hpt_eq⟩
    · have ht_pos : 0 < t := lt_of_le_of_ne ht fun ht0 => by
        apply hi_neq; rw [hpt_eq, ← ht0]; simp [ray1]
      cases bi with
      | true => exact ⟨t, ht_pos, hpt_eq⟩
      | false =>
        have hfalse := hpt1 false bj
        rw [hpt_eq] at hfalse
        have hval : lineAt W (i, false) (ray1 (W i) t) =
            t * ((W i).u₁.1 * (W i).u₂.2 - (W i).u₁.2 * (W i).u₂.1) := by
          dsimp [lineAt, normal, ray1, dir1]; ring
        rw [hval] at hfalse
        have hmul : 0 < t * ((W i).u₁.1 * (W i).u₂.2 - (W i).u₁.2 * (W i).u₂.1) := mul_pos ht_pos hnd
        linarith
    · have ht_pos : 0 < t := lt_of_le_of_ne ht fun ht0 => by
        apply hi_neq; rw [hpt_eq, ← ht0]; simp [ray2]
      cases bi with
      | true =>
        have htrue := hpt1 true bj
        rw [hpt_eq] at htrue
        have hval : lineAt W (i, true) (ray2 (W i) t) =
            t * ((W i).u₁.1 * (W i).u₂.2 - (W i).u₁.2 * (W i).u₂.1) := by
          dsimp [lineAt, normal, ray2, dir2]; ring
        rw [hval] at htrue
        have hmul : 0 < t * ((W i).u₁.1 * (W i).u₂.2 - (W i).u₁.2 * (W i).u₂.1) := mul_pos ht_pos hnd
        linarith
      | false => exact ⟨t, ht_pos, hpt_eq⟩
  have hj_ray : ∃ tj > 0, pt bi bj = if bj then ray1 (W j) tj else ray2 (W j) tj := by
    have hnd := (W j).h_nondeg
    rcases (bdWedge_iff_rays (W j) (pt bi bj)).mp hj_bd with ⟨t, ht, hpt_eq⟩ | ⟨t, ht, hpt_eq⟩
    · have ht_pos : 0 < t := lt_of_le_of_ne ht fun ht0 => by
        apply hj_neq; rw [hpt_eq, ← ht0]; simp [ray1]
      cases bj with
      | true => exact ⟨t, ht_pos, hpt_eq⟩
      | false =>
        have hfalse := hpt2 bi false
        rw [hpt_eq] at hfalse
        have hval : lineAt W (j, false) (ray1 (W j) t) =
            t * ((W j).u₁.1 * (W j).u₂.2 - (W j).u₁.2 * (W j).u₂.1) := by
          dsimp [lineAt, normal, ray1, dir1]; ring
        rw [hval] at hfalse
        have hmul : 0 < t * ((W j).u₁.1 * (W j).u₂.2 - (W j).u₁.2 * (W j).u₂.1) := mul_pos ht_pos hnd
        linarith
    · have ht_pos : 0 < t := lt_of_le_of_ne ht fun ht0 => by
        apply hj_neq; rw [hpt_eq, ← ht0]; simp [ray2]
      cases bj with
      | true =>
        have htrue := hpt2 bi true
        rw [hpt_eq] at htrue
        have hval : lineAt W (j, true) (ray2 (W j) t) =
            t * ((W j).u₁.1 * (W j).u₂.2 - (W j).u₁.2 * (W j).u₂.1) := by
          dsimp [lineAt, normal, ray2, dir2]; ring
        rw [hval] at htrue
        have hmul : 0 < t * ((W j).u₁.1 * (W j).u₂.2 - (W j).u₁.2 * (W j).u₂.1) := mul_pos ht_pos hnd
        linarith
      | false => exact ⟨t, ht_pos, hpt_eq⟩
  obtain ⟨ti, hti, heqi⟩ := hi_ray
  obtain ⟨tj, htj, heqj⟩ := hj_ray
  exact ⟨ti, hti, tj, htj, heqi.symm.trans heqj, heqi ▸ hmem_all bi bj⟩

private lemma closureMem_coords (W : OpenWedge) (p : ℝ × ℝ) (hp : closureMem W p) :
    ∃ c1 c2 : ℝ, 0 ≤ c1 ∧ 0 ≤ c2 ∧
      p.1 = W.y.1 + c1 * (dir1 W).1 + c2 * (dir2 W).1 ∧
      p.2 = W.y.2 + c1 * (dir1 W).2 + c2 * (dir2 W).2 := by
  have hnd := W.h_nondeg
  have hnd_ne : W.u₁.1 * W.u₂.2 - W.u₁.2 * W.u₂.1 ≠ 0 := ne_of_gt hnd
  let Δ := W.u₁.1 * W.u₂.2 - W.u₁.2 * W.u₂.1
  have hΔ : Δ ≠ 0 := hnd_ne
  let c1 := (W.u₂.1 * (p.1 - W.y.1) + W.u₂.2 * (p.2 - W.y.2)) / Δ
  let c2 := (W.u₁.1 * (p.1 - W.y.1) + W.u₁.2 * (p.2 - W.y.2)) / Δ
  refine ⟨c1, c2, div_nonneg hp.2 (le_of_lt hnd), div_nonneg hp.1 (le_of_lt hnd), ?_, ?_⟩
  · dsimp [c1, c2, dir1, dir2]; field_simp [hΔ]; dsimp [Δ]; ring
  · dsimp [c1, c2, dir1, dir2]; field_simp [hΔ]; dsimp [Δ]; ring

private lemma quad_four_ray_slopes (Wi Wj : OpenWedge)
    (hrays : ∀ bi bj : Bool, ∃ ti > 0, ∃ tj > 0,
      (if bi then ray1 Wi ti else ray2 Wi ti) =
      (if bj then ray1 Wj tj else ray2 Wj tj) ∧
      (if bi then ray1 Wi ti else ray2 Wi ti) ∈ Gamma Wi ∩ Gamma Wj) :
    let a1 := Wj.u₁.1 * (Wi.y.1 - Wj.y.1) + Wj.u₁.2 * (Wi.y.2 - Wj.y.2)
    let a2 := Wj.u₂.1 * (Wi.y.1 - Wj.y.1) + Wj.u₂.2 * (Wi.y.2 - Wj.y.2)
    let s11 := Wj.u₁.1 * (dir1 Wi).1 + Wj.u₁.2 * (dir1 Wi).2
    let s12 := Wj.u₂.1 * (dir1 Wi).1 + Wj.u₂.2 * (dir1 Wi).2
    let s21 := Wj.u₁.1 * (dir2 Wi).1 + Wj.u₁.2 * (dir2 Wi).2
    let s22 := Wj.u₂.1 * (dir2 Wi).1 + Wj.u₂.2 * (dir2 Wi).2
    ((a1 < 0 ∧ 0 < a2 ∧ 0 < s11 ∧ s12 < 0 ∧ 0 < s21 ∧ s22 < 0) ∨
     (a2 < 0 ∧ 0 < a1 ∧ s11 < 0 ∧ 0 < s12 ∧ s21 < 0 ∧ 0 < s22)) := by
  intro a1 a2 s11 s12 s21 s22
  obtain ⟨t11, ht11, tj11, htj11, heq11, hmem11⟩ := hrays true true
  obtain ⟨t12, ht12, tj12, htj12, heq12, hmem12⟩ := hrays true false
  obtain ⟨t21, ht21, tj21, htj21, heq21, hmem21⟩ := hrays false true
  obtain ⟨t22, ht22, tj22, htj22, heq22, hmem22⟩ := hrays false false
  simp only [ite_true, ite_false, Bool.false_eq_true] at heq11 heq12 heq21 heq22 hmem11 hmem12 hmem21 hmem22
  have hndj := Wj.h_nondeg
  have e_l1_r1 : ∀ t, Wj.u₁.1 * ((ray1 Wi t).1 - Wj.y.1) + Wj.u₁.2 * ((ray1 Wi t).2 - Wj.y.2) = a1 + t * s11 := by
    intro t; dsimp [a1, s11, ray1]; ring
  have e_l2_r1 : ∀ t, Wj.u₂.1 * ((ray1 Wi t).1 - Wj.y.1) + Wj.u₂.2 * ((ray1 Wi t).2 - Wj.y.2) = a2 + t * s12 := by
    intro t; dsimp [a2, s12, ray1]; ring
  have e_l1_r2 : ∀ t, Wj.u₁.1 * ((ray2 Wi t).1 - Wj.y.1) + Wj.u₁.2 * ((ray2 Wi t).2 - Wj.y.2) = a1 + t * s21 := by
    intro t; dsimp [a1, s21, ray2]; ring
  have e_l2_r2 : ∀ t, Wj.u₂.1 * ((ray2 Wi t).1 - Wj.y.1) + Wj.u₂.2 * ((ray2 Wi t).2 - Wj.y.2) = a2 + t * s22 := by
    intro t; dsimp [a2, s22, ray2]; ring
  have z11 : a1 + t11 * s11 = 0 := by rw [← e_l1_r1, heq11]; dsimp [ray1, dir1]; ring
  have p11 : 0 < a2 + t11 * s12 := by
    rw [← e_l2_r1, heq11]
    have : Wj.u₂.1 * ((ray1 Wj tj11).1 - Wj.y.1) + Wj.u₂.2 * ((ray1 Wj tj11).2 - Wj.y.2) =
        tj11 * (Wj.u₁.1 * Wj.u₂.2 - Wj.u₁.2 * Wj.u₂.1) := by dsimp [ray1, dir1]; ring
    rw [this]; exact mul_pos htj11 hndj
  have z12 : a2 + t12 * s12 = 0 := by rw [← e_l2_r1, heq12]; dsimp [ray2, dir2]; ring
  have p12 : 0 < a1 + t12 * s11 := by
    rw [← e_l1_r1, heq12]
    have : Wj.u₁.1 * ((ray2 Wj tj12).1 - Wj.y.1) + Wj.u₁.2 * ((ray2 Wj tj12).2 - Wj.y.2) =
        tj12 * (Wj.u₁.1 * Wj.u₂.2 - Wj.u₁.2 * Wj.u₂.1) := by dsimp [ray2, dir2]; ring
    rw [this]; exact mul_pos htj12 hndj
  have z21 : a1 + t21 * s21 = 0 := by rw [← e_l1_r2, heq21]; dsimp [ray1, dir1]; ring
  have p21 : 0 < a2 + t21 * s22 := by
    rw [← e_l2_r2, heq21]
    have : Wj.u₂.1 * ((ray1 Wj tj21).1 - Wj.y.1) + Wj.u₂.2 * ((ray1 Wj tj21).2 - Wj.y.2) =
        tj21 * (Wj.u₁.1 * Wj.u₂.2 - Wj.u₁.2 * Wj.u₂.1) := by dsimp [ray1, dir1]; ring
    rw [this]; exact mul_pos htj21 hndj
  have z22 : a2 + t22 * s22 = 0 := by rw [← e_l2_r2, heq22]; dsimp [ray2, dir2]; ring
  have p22 : 0 < a1 + t22 * s21 := by
    rw [← e_l1_r2, heq22]
    have : Wj.u₁.1 * ((ray2 Wj tj22).1 - Wj.y.1) + Wj.u₁.2 * ((ray2 Wj tj22).2 - Wj.y.2) =
        tj22 * (Wj.u₁.1 * Wj.u₂.2 - Wj.u₁.2 * Wj.u₂.1) := by dsimp [ray2, dir2]; ring
    rw [this]; exact mul_pos htj22 hndj
  have hs11_ne : s11 ≠ 0 := by
    intro h0; rw [h0, mul_zero, add_zero] at z11 p12; linarith
  have hs12_ne : s12 ≠ 0 := by
    intro h0; rw [h0, mul_zero, add_zero] at z12 p11; linarith
  have hs21_ne : s21 ≠ 0 := by
    intro h0; rw [h0, mul_zero, add_zero] at z21 p22; linarith
  have hs22_ne : s22 ≠ 0 := by
    intro h0; rw [h0, mul_zero, add_zero] at z22 p21; linarith
  rcases lt_or_gt_of_ne hs11_ne with hs11 | hs11
  · right
    have ha1 : 0 < a1 := by
      have : 0 < -(t11 * s11) := neg_pos.mpr (mul_neg_of_pos_of_neg ht11 hs11)
      linarith
    have hs21 : s21 < 0 := by
      by_contra hge
      have : 0 ≤ t21 * s21 := mul_nonneg (le_of_lt ht21) (not_lt.mp hge)
      linarith
    have hlt_t : t12 < t11 := by
      have hsub : 0 < (t12 - t11) * s11 := by linarith
      by_contra hge
      have : (t12 - t11) * s11 ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by linarith) (le_of_lt hs11)
      linarith
    have hs12 : 0 < s12 := by
      have hsub : 0 < (t11 - t12) * s12 := by linarith
      by_contra hle
      have : (t11 - t12) * s12 ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by linarith) (not_lt.mp hle)
      linarith
    have ha2 : a2 < 0 := by
      have : 0 < t12 * s12 := mul_pos ht12 hs12
      linarith
    have hs22 : 0 < s22 := by
      by_contra hle
      have : t22 * s22 ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (le_of_lt ht22) (not_lt.mp hle)
      linarith
    exact ⟨ha2, ha1, hs11, hs12, hs21, hs22⟩
  · left
    have ha1 : a1 < 0 := by
      have : 0 < t11 * s11 := mul_pos ht11 hs11
      linarith
    have hs21 : 0 < s21 := by
      by_contra hle
      have : t21 * s21 ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (le_of_lt ht21) (not_lt.mp hle)
      linarith
    have hlt_t : t11 < t12 := by
      have hsub : 0 < (t12 - t11) * s11 := by linarith
      by_contra hle
      have : (t12 - t11) * s11 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) (le_of_lt hs11)
      linarith
    have hs12 : s12 < 0 := by
      have hsub : 0 < (t11 - t12) * s12 := by linarith
      by_contra hge
      have : (t11 - t12) * s12 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) (not_lt.mp hge)
      linarith
    have ha2 : 0 < a2 := by
      have : t12 * s12 < 0 := mul_neg_of_pos_of_neg ht12 hs12
      linarith
    have hs22 : s22 < 0 := by
      by_contra hge
      have : 0 ≤ t22 * s22 := mul_nonneg (le_of_lt ht22) (not_lt.mp hge)
      linarith
    exact ⟨ha1, ha2, hs11, hs12, hs21, hs22⟩

lemma quad_bounded {W : Fin 5 → OpenWedge} (hGP : GeneralPosition W)
    {i j : Fin 5} (hij : i ≠ j)
    (h4 : ¬ (Gamma (W i) ∩ Gamma (W j)).ncard ≤ 3) :
    ∃ M : ℝ, ∀ p : ℝ × ℝ, closureMem (W i) p → closureMem (W j) p →
      |p.1| ≤ M ∧ |p.2| ≤ M := by
  have hrays := quad_four_inter_rays hGP hij h4
  have hslopes := quad_four_ray_slopes (W i) (W j) hrays
  let a1 := (W j).u₁.1 * ((W i).y.1 - (W j).y.1) + (W j).u₁.2 * ((W i).y.2 - (W j).y.2)
  let a2 := (W j).u₂.1 * ((W i).y.1 - (W j).y.1) + (W j).u₂.2 * ((W i).y.2 - (W j).y.2)
  let s11 := (W j).u₁.1 * (dir1 (W i)).1 + (W j).u₁.2 * (dir1 (W i)).2
  let s12 := (W j).u₂.1 * (dir1 (W i)).1 + (W j).u₂.2 * (dir1 (W i)).2
  let s21 := (W j).u₁.1 * (dir2 (W i)).1 + (W j).u₁.2 * (dir2 (W i)).2
  let s22 := (W j).u₂.1 * (dir2 (W i)).1 + (W j).u₂.2 * (dir2 (W i)).2
  have hlam_bound : ∃ B : ℝ, ∀ p, closureMem (W i) p → closureMem (W j) p →
      ∃ c1 c2 : ℝ, 0 ≤ c1 ∧ c1 ≤ B ∧ 0 ≤ c2 ∧ c2 ≤ B ∧
      p.1 = (W i).y.1 + c1 * (dir1 (W i)).1 + c2 * (dir2 (W i)).1 ∧
      p.2 = (W i).y.2 + c1 * (dir1 (W i)).2 + c2 * (dir2 (W i)).2 := by
    rcases hslopes with ⟨_, ha2, _, hs12, _, hs22⟩ | ⟨_, ha1, hs11, _, hs21, _⟩
    · refine ⟨max (a2 / (-s12)) (a2 / (-s22)), fun p hpi hpj => ?_⟩
      obtain ⟨c1, c2, hc1, hc2, hp1, hp2⟩ := closureMem_coords (W i) p hpi
      have hL2 : (W j).u₂.1 * (p.1 - (W j).y.1) + (W j).u₂.2 * (p.2 - (W j).y.2) =
          a2 + c1 * s12 + c2 * s22 := by
        rw [hp1, hp2]; dsimp [a2, s12, s22]; ring
      have hge0 : 0 ≤ a2 + c1 * s12 + c2 * s22 := hL2 ▸ hpj.2
      have hb1 : c1 ≤ a2 / (-s12) := by
        rw [le_div_iff₀ (by linarith)]
        have : c2 * s22 ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hc2 (le_of_lt hs22)
        linarith
      have hb2 : c2 ≤ a2 / (-s22) := by
        rw [le_div_iff₀ (by linarith)]
        have : c1 * s12 ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hc1 (le_of_lt hs12)
        linarith
      exact ⟨c1, c2, hc1, hb1.trans (le_max_left _ _), hc2, hb2.trans (le_max_right _ _), hp1, hp2⟩
    · refine ⟨max (a1 / (-s11)) (a1 / (-s21)), fun p hpi hpj => ?_⟩
      obtain ⟨c1, c2, hc1, hc2, hp1, hp2⟩ := closureMem_coords (W i) p hpi
      have hL1 : (W j).u₁.1 * (p.1 - (W j).y.1) + (W j).u₁.2 * (p.2 - (W j).y.2) =
          a1 + c1 * s11 + c2 * s21 := by
        rw [hp1, hp2]; dsimp [a1, s11, s21]; ring
      have hge0 : 0 ≤ a1 + c1 * s11 + c2 * s21 := hL1 ▸ hpj.1
      have hb1 : c1 ≤ a1 / (-s11) := by
        rw [le_div_iff₀ (by linarith)]
        have : c2 * s21 ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hc2 (le_of_lt hs21)
        linarith
      have hb2 : c2 ≤ a1 / (-s21) := by
        rw [le_div_iff₀ (by linarith)]
        have : c1 * s11 ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hc1 (le_of_lt hs11)
        linarith
      exact ⟨c1, c2, hc1, hb1.trans (le_max_left _ _), hc2, hb2.trans (le_max_right _ _), hp1, hp2⟩
  obtain ⟨B, hB⟩ := hlam_bound
  let B' := max B 0
  refine ⟨|(W i).y.1| + |(W i).y.2| + B' * (|(dir1 (W i)).1| + |(dir1 (W i)).2| +
    |(dir2 (W i)).1| + |(dir2 (W i)).2|), fun p hpi hpj => ?_⟩
  obtain ⟨c1, c2, hc1, hc1B, hc2, hc2B, hp1, hp2⟩ := hB p hpi hpj
  have hB1 : c1 ≤ B' := hc1B.trans (le_max_left _ _)
  have hB2 : c2 ≤ B' := hc2B.trans (le_max_left _ _)
  constructor
  · rw [hp1]
    have t1 : |(W i).y.1 + c1 * (dir1 (W i)).1 + c2 * (dir2 (W i)).1| ≤
        |(W i).y.1| + |c1 * (dir1 (W i)).1| + |c2 * (dir2 (W i)).1| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    rw [abs_mul, abs_mul, abs_of_nonneg hc1, abs_of_nonneg hc2] at t1
    have m1 : c1 * |(dir1 (W i)).1| ≤ B' * |(dir1 (W i)).1| := mul_le_mul_of_nonneg_right hB1 (abs_nonneg _)
    have m2 : c2 * |(dir2 (W i)).1| ≤ B' * |(dir2 (W i)).1| := mul_le_mul_of_nonneg_right hB2 (abs_nonneg _)
    nlinarith [abs_nonneg (W i).y.2, abs_nonneg (dir1 (W i)).2, abs_nonneg (dir2 (W i)).2, le_max_right B 0]
  · rw [hp2]
    have t2 : |(W i).y.2 + c1 * (dir1 (W i)).2 + c2 * (dir2 (W i)).2| ≤
        |(W i).y.2| + |c1 * (dir1 (W i)).2| + |c2 * (dir2 (W i)).2| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    rw [abs_mul, abs_mul, abs_of_nonneg hc1, abs_of_nonneg hc2] at t2
    have m1 : c1 * |(dir1 (W i)).2| ≤ B' * |(dir1 (W i)).2| := mul_le_mul_of_nonneg_right hB1 (abs_nonneg _)
    have m2 : c2 * |(dir2 (W i)).2| ≤ B' * |(dir2 (W i)).2| := mul_le_mul_of_nonneg_right hB2 (abs_nonneg _)
    nlinarith [abs_nonneg (W i).y.1, abs_nonneg (dir1 (W i)).1, abs_nonneg (dir2 (W i)).1, le_max_right B 0]

private lemma quad_bd_in_closure_inOmega (Wi Wj : OpenWedge)
    (hyi : Wi.y.1 < 0 ∧ Wi.y.2 < 0)
    (hrays : ∀ bi bj : Bool, ∃ ti > 0, ∃ tj > 0,
      (if bi then ray1 Wi ti else ray2 Wi ti) =
      (if bj then ray1 Wj tj else ray2 Wj tj) ∧
      (if bi then ray1 Wi ti else ray2 Wi ti) ∈ Gamma Wi ∩ Gamma Wj)
    {p : ℝ × ℝ} (hp_bd : p ∈ bdWedge Wi) (hp_cl : closureMem Wj p) :
    inOmega p := by
  have hslopes := quad_four_ray_slopes Wi Wj hrays
  obtain ⟨t11, ht11, _, _, heq11, hmem11⟩ := hrays true true
  obtain ⟨t12, ht12, _, _, heq12, hmem12⟩ := hrays true false
  obtain ⟨t21, ht21, _, _, heq21, hmem21⟩ := hrays false true
  obtain ⟨t22, ht22, _, _, heq22, hmem22⟩ := hrays false false
  simp only [ite_true, ite_false, Bool.false_eq_true] at heq11 heq12 heq21 heq22 hmem11 hmem12 hmem21 hmem22
  have h11_om : (t11 : WithTop ℝ) < rayExit Wi.y (dir1 Wi) :=
    (ray_inOmega_iff hyi.1 hyi.2 (le_of_lt ht11)).mp hmem11.1.2
  have h12_om : (t12 : WithTop ℝ) < rayExit Wi.y (dir1 Wi) :=
    (ray_inOmega_iff hyi.1 hyi.2 (le_of_lt ht12)).mp hmem12.1.2
  have h21_om : (t21 : WithTop ℝ) < rayExit Wi.y (dir2 Wi) :=
    (ray_inOmega_iff hyi.1 hyi.2 (le_of_lt ht21)).mp hmem21.1.2
  have h22_om : (t22 : WithTop ℝ) < rayExit Wi.y (dir2 Wi) :=
    (ray_inOmega_iff hyi.1 hyi.2 (le_of_lt ht22)).mp hmem22.1.2
  rcases (bdWedge_iff_rays Wi p).mp hp_bd with ⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩
  · have hlt_T : (t : WithTop ℝ) < rayExit Wi.y (dir1 Wi) := by
      have z11 : Wj.u₁.1 * ((ray1 Wi t11).1 - Wj.y.1) + Wj.u₁.2 * ((ray1 Wi t11).2 - Wj.y.2) = 0 := by
        rw [heq11]; dsimp [ray1, dir1]; ring
      have z12 : Wj.u₂.1 * ((ray1 Wi t12).1 - Wj.y.1) + Wj.u₂.2 * ((ray1 Wi t12).2 - Wj.y.2) = 0 := by
        rw [heq12]; dsimp [ray2, dir2]; ring
      have ht_le : t ≤ max t11 t12 := by
        rcases hslopes with ⟨ha1, ha2, hs11, hs12, _, _⟩ | ⟨ha2, ha1, hs11, hs12, _, _⟩
        · have hL2 : 0 ≤ (Wj.u₂.1 * (Wi.y.1 - Wj.y.1) + Wj.u₂.2 * (Wi.y.2 - Wj.y.2)) +
              t * (Wj.u₂.1 * (dir1 Wi).1 + Wj.u₂.2 * (dir1 Wi).2) := by
            dsimp [ray1] at hp_cl; linarith [hp_cl.2]
          have hz2 : (Wj.u₂.1 * (Wi.y.1 - Wj.y.1) + Wj.u₂.2 * (Wi.y.2 - Wj.y.2)) +
              t12 * (Wj.u₂.1 * (dir1 Wi).1 + Wj.u₂.2 * (dir1 Wi).2) = 0 := by
            dsimp [ray1] at z12; linarith [z12]
          have hle12 : t ≤ t12 := by nlinarith
          exact hle12.trans (le_max_right _ _)
        · have hL1 : 0 ≤ (Wj.u₁.1 * (Wi.y.1 - Wj.y.1) + Wj.u₁.2 * (Wi.y.2 - Wj.y.2)) +
              t * (Wj.u₁.1 * (dir1 Wi).1 + Wj.u₁.2 * (dir1 Wi).2) := by
            dsimp [ray1] at hp_cl; linarith [hp_cl.1]
          have hz1 : (Wj.u₁.1 * (Wi.y.1 - Wj.y.1) + Wj.u₁.2 * (Wi.y.2 - Wj.y.2)) +
              t11 * (Wj.u₁.1 * (dir1 Wi).1 + Wj.u₁.2 * (dir1 Wi).2) = 0 := by
            dsimp [ray1] at z11; linarith [z11]
          have hle11 : t ≤ t11 := by nlinarith
          exact hle11.trans (le_max_left _ _)
      exact lt_of_le_of_lt (WithTop.coe_le_coe.mpr ht_le) (max_lt h11_om h12_om)
    exact (ray_inOmega_iff hyi.1 hyi.2 ht).mpr hlt_T
  · have hlt_T : (t : WithTop ℝ) < rayExit Wi.y (dir2 Wi) := by
      have z21 : Wj.u₁.1 * ((ray2 Wi t21).1 - Wj.y.1) + Wj.u₁.2 * ((ray2 Wi t21).2 - Wj.y.2) = 0 := by
        rw [heq21]; dsimp [ray1, dir1]; ring
      have z22 : Wj.u₂.1 * ((ray2 Wi t22).1 - Wj.y.1) + Wj.u₂.2 * ((ray2 Wi t22).2 - Wj.y.2) = 0 := by
        rw [heq22]; dsimp [ray2, dir2]; ring
      have ht_le : t ≤ max t21 t22 := by
        rcases hslopes with ⟨ha1, ha2, _, _, hs21, hs22⟩ | ⟨ha2, ha1, _, _, hs21, hs22⟩
        · have hL2 : 0 ≤ (Wj.u₂.1 * (Wi.y.1 - Wj.y.1) + Wj.u₂.2 * (Wi.y.2 - Wj.y.2)) +
              t * (Wj.u₂.1 * (dir2 Wi).1 + Wj.u₂.2 * (dir2 Wi).2) := by
            dsimp [ray2] at hp_cl; linarith [hp_cl.2]
          have hz2 : (Wj.u₂.1 * (Wi.y.1 - Wj.y.1) + Wj.u₂.2 * (Wi.y.2 - Wj.y.2)) +
              t22 * (Wj.u₂.1 * (dir2 Wi).1 + Wj.u₂.2 * (dir2 Wi).2) = 0 := by
            dsimp [ray2] at z22; linarith [z22]
          have hle22 : t ≤ t22 := by nlinarith
          exact hle22.trans (le_max_right _ _)
        · have hL1 : 0 ≤ (Wj.u₁.1 * (Wi.y.1 - Wj.y.1) + Wj.u₁.2 * (Wi.y.2 - Wj.y.2)) +
              t * (Wj.u₁.1 * (dir2 Wi).1 + Wj.u₁.2 * (dir2 Wi).2) := by
            dsimp [ray2] at hp_cl; linarith [hp_cl.1]
          have hz1 : (Wj.u₁.1 * (Wi.y.1 - Wj.y.1) + Wj.u₁.2 * (Wi.y.2 - Wj.y.2)) +
              t21 * (Wj.u₁.1 * (dir2 Wi).1 + Wj.u₁.2 * (dir2 Wi).2) = 0 := by
            dsimp [ray2] at z21; linarith [z21]
          have hle21 : t ≤ t21 := by nlinarith
          exact hle21.trans (le_max_left _ _)
      exact lt_of_le_of_lt (WithTop.coe_le_coe.mpr ht_le) (max_lt h21_om h22_om)
    exact (ray_inOmega_iff hyi.1 hyi.2 ht).mpr hlt_T

lemma inter_card_le_three_of_origin {W : Fin 5 → OpenWedge} (hGP : GeneralPosition W)
    (h_apex : ∀ k : Fin 5, (W k).y.1 < 0 ∧ (W k).y.2 < 0)
    {i j : Fin 5} (hij : i ≠ j)
    (hi0 : (W i).MemOpen (0, 0)) (hj0 : (W j).MemOpen (0, 0)) :
    (Gamma (W i) ∩ Gamma (W j)).ncard ≤ 3 := by
  by_contra h4
  obtain ⟨M, hM⟩ := quad_bounded hGP hij h4
  have hrays := quad_four_inter_rays hGP hij h4
  have hrays_sym : ∀ bj bi : Bool, ∃ tj > 0, ∃ ti > 0,
      (if bj then ray1 (W j) tj else ray2 (W j) tj) =
      (if bi then ray1 (W i) ti else ray2 (W i) ti) ∧
      (if bj then ray1 (W j) tj else ray2 (W j) tj) ∈ Gamma (W j) ∩ Gamma (W i) := by
    intro bj bi
    obtain ⟨ti, hti, tj, htj, heq, hmem⟩ := hrays bi bj
    exact ⟨tj, htj, ti, hti, heq.symm, heq ▸ hmem.symm⟩
  let u : Fin 4 → ℝ × ℝ := ![ (W i).u₁, (W i).u₂, (W j).u₁, (W j).u₂ ]
  let y : Fin 4 → ℝ × ℝ := ![ (W i).y, (W i).y, (W j).y, (W j).y ]
  let v : Fin 4 → ℝ := fun m => (u m).1 * (0 - (y m).1) + (u m).2 * (0 - (y m).2)
  let sl : Fin 4 → ℝ := fun m => (u m).1 + (u m).2
  have hv_pos : ∀ m : Fin 4, 0 < v m := by
    intro m; fin_cases m
    · exact hi0.1
    · exact hi0.2
    · exact hj0.1
    · exact hj0.2
  let T : ℝ := max M 0 + 1
  have hT_pos : 0 < T := by positivity
  have hT_out : ¬ (closureMem (W i) (T, T) ∧ closureMem (W j) (T, T)) := by
    intro ⟨hci, hcj⟩
    have h1 := (hM (T, T) hci hcj).1
    have h2 : T ≤ |T| := le_abs_self T
    linarith [le_max_left M 0]
  have hneg_ex : ∃ m : Fin 4, sl m < 0 := by
    by_contra hnone
    push Not at hnone
    apply hT_out
    have hlin : ∀ m : Fin 4, 0 ≤ (u m).1 * (T - (y m).1) + (u m).2 * (T - (y m).2) := by
      intro m
      have e : (u m).1 * (T - (y m).1) + (u m).2 * (T - (y m).2) = v m + T * sl m := by
        dsimp [v, sl]; ring
      rw [e]; nlinarith [hv_pos m, hnone m]
    exact ⟨⟨hlin 0, hlin 1⟩, ⟨hlin 2, hlin 3⟩⟩
  let negSet : Finset (Fin 4) := Finset.univ.filter (fun m : Fin 4 => sl m < 0)
  have hneg_ne : negSet.Nonempty := by
    obtain ⟨m, hm⟩ := hneg_ex
    exact ⟨m, Finset.mem_filter.mpr ⟨Finset.mem_univ m, hm⟩⟩
  let tExit : Fin 4 → ℝ := fun m => -v m / sl m
  let tstar : ℝ := negSet.inf' hneg_ne tExit
  obtain ⟨mstar, hmstar_mem, hmstar_eq⟩ := Finset.exists_mem_eq_inf' hneg_ne tExit
  have hmstar_sl : sl mstar < 0 := (Finset.mem_filter.mp hmstar_mem).2
  have htstar_pos : 0 < tstar := by
    dsimp [tstar]; rw [hmstar_eq]; exact div_pos_of_neg_of_neg (by linarith [hv_pos mstar]) hmstar_sl
  have hcl_tstar : closureMem (W i) (tstar, tstar) ∧ closureMem (W j) (tstar, tstar) := by
    have hlin : ∀ m : Fin 4, 0 ≤ (u m).1 * (tstar - (y m).1) + (u m).2 * (tstar - (y m).2) := by
      intro m
      have e : (u m).1 * (tstar - (y m).1) + (u m).2 * (tstar - (y m).2) = v m + tstar * sl m := by
        dsimp [v, sl]; ring
      rw [e]
      by_cases hm : sl m < 0
      · have hmem : m ∈ negSet := Finset.mem_filter.mpr ⟨Finset.mem_univ m, hm⟩
        have hle : tstar ≤ -v m / sl m := Finset.inf'_le tExit hmem
        have hmul : -v m ≤ tstar * sl m := by
          rw [le_div_iff_of_neg hm] at hle; linarith
        linarith
      · have hm' : 0 ≤ sl m := not_lt.mp hm
        nlinarith [hv_pos m]
    exact ⟨⟨hlin 0, hlin 1⟩, ⟨hlin 2, hlin 3⟩⟩
  have hzero_mstar : (u mstar).1 * (tstar - (y mstar).1) + (u mstar).2 * (tstar - (y mstar).2) = 0 := by
    have e : (u mstar).1 * (tstar - (y mstar).1) + (u mstar).2 * (tstar - (y mstar).2) =
        v mstar + tstar * sl mstar := by dsimp [v, sl]; ring
    rw [e, show tstar = tExit mstar from hmstar_eq]
    dsimp [tExit]; field_simp [ne_of_lt hmstar_sl]; ring
  have hom : inOmega (tstar, tstar) := by
    fin_cases mstar
    · have hbd : (tstar, tstar) ∈ bdWedge (W i) :=
        (bdWedge_iff_closure_eq_zero (W i) (tstar, tstar)).mpr ⟨hcl_tstar.1, Or.inl hzero_mstar⟩
      exact quad_bd_in_closure_inOmega (W i) (W j) (h_apex i) hrays hbd hcl_tstar.2
    · have hbd : (tstar, tstar) ∈ bdWedge (W i) :=
        (bdWedge_iff_closure_eq_zero (W i) (tstar, tstar)).mpr ⟨hcl_tstar.1, Or.inr hzero_mstar⟩
      exact quad_bd_in_closure_inOmega (W i) (W j) (h_apex i) hrays hbd hcl_tstar.2
    · have hbd : (tstar, tstar) ∈ bdWedge (W j) :=
        (bdWedge_iff_closure_eq_zero (W j) (tstar, tstar)).mpr ⟨hcl_tstar.2, Or.inl hzero_mstar⟩
      exact quad_bd_in_closure_inOmega (W j) (W i) (h_apex j) hrays_sym hbd hcl_tstar.1
    · have hbd : (tstar, tstar) ∈ bdWedge (W j) :=
        (bdWedge_iff_closure_eq_zero (W j) (tstar, tstar)).mpr ⟨hcl_tstar.2, Or.inr hzero_mstar⟩
      exact quad_bd_in_closure_inOmega (W j) (W i) (h_apex j) hrays_sym hbd hcl_tstar.1
  rcases hom with h1 | h2 <;> linarith

lemma inter_card_le_three_of_Lgt {W : Fin 5 → OpenWedge} (hGP : GeneralPosition W)
    (pa pb : ℝ × ℝ)
    (h_apex : ∀ k : Fin 5, (W k).y.1 < 0 ∧ (W k).y.2 < 0)
    (hxa : 0 < pa.1) (hya : pa.2 < 0) (hxb : pb.1 < 0) (hyb : 0 < pb.2)
    (hC : pa.1 * pb.2 - pa.2 * pb.1 < 0)
    (ha : ∀ k : Fin 5, (W k).MemOpen pa) (hb : ∀ k : Fin 5, (W k).MemOpen pb)
    {i j : Fin 5} (hij : i ≠ j)
    (hi_gt : isLgt (W i) pa pb) (hj_gt : isLgt (W j) pa pb) :
    (Gamma (W i) ∩ Gamma (W j)).ncard ≤ 3 := by
  by_contra h4
  obtain ⟨M, hM⟩ := quad_bounded hGP hij h4
  have hA : 0 < pb.2 - pa.2 := by linarith
  have hB : 0 < pa.1 - pb.1 := by linarith
  let R : ℝ := max M 0 + |pa.1 * pb.2 - pa.2 * pb.1| / (pb.2 - pa.2 + (pa.1 - pb.1)) + 1
  have hR_pos : 0 < R := by positivity
  have hAB_pos : 0 < (pb.2 - pa.2) + (pa.1 - pb.1) := by linarith
  have hsub : (pb.2 - pa.2) * (-R) + (pa.1 - pb.1) * (-R) ≤ pa.1 * pb.2 - pa.2 * pb.1 := by
    have h1 : |pa.1 * pb.2 - pa.2 * pb.1| < R * ((pb.2 - pa.2) + (pa.1 - pb.1)) := by
      have : |pa.1 * pb.2 - pa.2 * pb.1| / ((pb.2 - pa.2) + (pa.1 - pb.1)) < R := by
        dsimp [R]; linarith [le_max_right M 0]
      rwa [div_lt_iff₀ hAB_pos] at this
    have h2 : -(pa.1 * pb.2 - pa.2 * pb.1) ≤ |pa.1 * pb.2 - pa.2 * pb.1| := neg_le_abs _
    linarith
  have hi_mem := caseB_Lgt_contains_sublevel (W i) pa pb (-R, -R) (h_apex i).1 (h_apex i).2
    hxa hya hxb hyb hC (ha i) (hb i) hi_gt (by linarith) (by linarith) hsub
  have hj_mem := caseB_Lgt_contains_sublevel (W j) pa pb (-R, -R) (h_apex j).1 (h_apex j).2
    hxa hya hxb hyb hC (ha j) (hb j) hj_gt (by linarith) (by linarith) hsub
  have hbd := (hM (-R, -R) ⟨le_of_lt hi_mem.1, le_of_lt hi_mem.2⟩
    ⟨le_of_lt hj_mem.1, le_of_lt hj_mem.2⟩).1
  have hR_le : R ≤ |-R| := by rw [abs_neg, abs_of_pos hR_pos]
  dsimp [R] at hbd hR_le
  linarith [le_max_left M 0, div_nonneg (abs_nonneg (pa.1 * pb.2 - pa.2 * pb.1)) (le_of_lt hAB_pos)]

private lemma ray_meets_convex_bd_at_most_once (y d : ℝ × ℝ) (Wj : OpenWedge)
    (hy_mem : Wj.MemOpen y) :
    Set.Subsingleton {t : ℝ | 0 ≤ t ∧ (y.1 + t * d.1, y.2 + t * d.2) ∈ bdWedge Wj} := by
  intro t₁ ht₁ t₂ ht₂
  by_contra hne
  wlog hlt : t₁ < t₂ generalizing t₁ t₂
  · exact this ht₂ ht₁ (Ne.symm hne) (lt_of_le_of_ne (not_lt.mp hlt) (Ne.symm hne))
  have ht1_pos : 0 < t₁ := by
    refine lt_of_le_of_ne ht₁.1 ?_
    rintro rfl
    have hy0 : (y.1 + 0 * d.1, y.2 + 0 * d.2) = y := by ext <;> simp
    dsimp only [Set.mem_setOf_eq] at ht₁
    rw [hy0] at ht₁
    exact ht₁.2.1 hy_mem
  have ht2_pos : 0 < t₂ := ht1_pos.trans hlt
  let θ : ℝ := t₁ / t₂
  have hθ0 : 0 < θ := div_pos ht1_pos ht2_pos
  have hθ1 : 0 < 1 - θ := by
    dsimp [θ]; rw [sub_pos, div_lt_one ht2_pos]; exact hlt
  have hcl2 := (bdWedge_iff_closure_eq_zero Wj _).mp ht₂.2 |>.1
  have e1 : Wj.u₁.1 * ((y.1 + t₁ * d.1) - Wj.y.1) + Wj.u₁.2 * ((y.2 + t₁ * d.2) - Wj.y.2) =
      (1 - θ) * (Wj.u₁.1 * (y.1 - Wj.y.1) + Wj.u₁.2 * (y.2 - Wj.y.2)) +
      θ * (Wj.u₁.1 * ((y.1 + t₂ * d.1) - Wj.y.1) + Wj.u₁.2 * ((y.2 + t₂ * d.2) - Wj.y.2)) := by
    dsimp [θ]; field_simp [ne_of_gt ht2_pos]; ring
  have e2 : Wj.u₂.1 * ((y.1 + t₁ * d.1) - Wj.y.1) + Wj.u₂.2 * ((y.2 + t₁ * d.2) - Wj.y.2) =
      (1 - θ) * (Wj.u₂.1 * (y.1 - Wj.y.1) + Wj.u₂.2 * (y.2 - Wj.y.2)) +
      θ * (Wj.u₂.1 * ((y.1 + t₂ * d.1) - Wj.y.1) + Wj.u₂.2 * ((y.2 + t₂ * d.2) - Wj.y.2)) := by
    dsimp [θ]; field_simp [ne_of_gt ht2_pos]; ring
  have ho1 : 0 < Wj.u₁.1 * ((y.1 + t₁ * d.1) - Wj.y.1) + Wj.u₁.2 * ((y.2 + t₁ * d.2) - Wj.y.2) := by
    rw [e1]; nlinarith [hy_mem.1, hcl2.1]
  have ho2 : 0 < Wj.u₂.1 * ((y.1 + t₁ * d.1) - Wj.y.1) + Wj.u₂.2 * ((y.2 + t₁ * d.2) - Wj.y.2) := by
    rw [e2]; nlinarith [hy_mem.2, hcl2.2]
  exact ht₁.2.1 ⟨ho1, ho2⟩

lemma inter_card_le_two_of_Llt_Lgt (W : Fin 5 → OpenWedge) (pa pb : ℝ × ℝ)
    (h_apex : ∀ k : Fin 5, (W k).y.1 < 0 ∧ (W k).y.2 < 0)
    (hxa : 0 < pa.1) (hya : pa.2 < 0) (hxb : pb.1 < 0) (hyb : 0 < pb.2)
    (hC : pa.1 * pb.2 - pa.2 * pb.1 < 0)
    (ha : ∀ k : Fin 5, (W k).MemOpen pa) (hb : ∀ k : Fin 5, (W k).MemOpen pb)
    {i j : Fin 5} (hlt : isLlt (W i) pa pb) (hgt : isLgt (W j) pa pb) :
    (Gamma (W i) ∩ Gamma (W j)).ncard ≤ 2 := by
  have hyi_in_j := caseB_Llt_in_Lgt (W i) (W j) pa pb (h_apex i).1 (h_apex i).2
    (h_apex j).1 (h_apex j).2 hxa hya hxb hyb hC (ha j) (hb j) hlt hgt
  let S1 := {t : ℝ | 0 ≤ t ∧ ray1 (W i) t ∈ bdWedge (W j)}
  let S2 := {t : ℝ | 0 ≤ t ∧ ray2 (W i) t ∈ bdWedge (W j)}
  have hS1 : S1.Subsingleton := ray_meets_convex_bd_at_most_once (W i).y (dir1 (W i)) (W j) hyi_in_j
  have hS2 : S2.Subsingleton := ray_meets_convex_bd_at_most_once (W i).y (dir2 (W i)) (W j) hyi_in_j
  have hsub : Gamma (W i) ∩ Gamma (W j) ⊆ ray1 (W i) '' S1 ∪ ray2 (W i) '' S2 := by
    rintro p ⟨⟨hi_bd, _⟩, ⟨hj_bd, _⟩⟩
    rcases (bdWedge_iff_rays (W i) p).mp hi_bd with ⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩
    · left; exact ⟨t, ⟨ht, hj_bd⟩, rfl⟩
    · right; exact ⟨t, ⟨ht, hj_bd⟩, rfl⟩
  have hfin1 : (ray1 (W i) '' S1).Finite := (hS1.finite).image _
  have hfin2 : (ray2 (W i) '' S2).Finite := (hS2.finite).image _
  have hc1 : (ray1 (W i) '' S1).ncard ≤ 1 := by
    rw [Set.ncard_le_one_iff hfin1]
    intro a b ha hb
    rcases ha with ⟨ta, hta, rfl⟩; rcases hb with ⟨tb, htb, rfl⟩
    rw [hS1 hta htb]
  have hc2 : (ray2 (W i) '' S2).ncard ≤ 1 := by
    rw [Set.ncard_le_one_iff hfin2]
    intro a b ha hb
    rcases ha with ⟨ta, hta, rfl⟩; rcases hb with ⟨tb, htb, rfl⟩
    rw [hS2 hta htb]
  calc (Gamma (W i) ∩ Gamma (W j)).ncard
      ≤ (ray1 (W i) '' S1 ∪ ray2 (W i) '' S2).ncard := Set.ncard_le_ncard hsub (hfin1.union hfin2)
    _ ≤ (ray1 (W i) '' S1).ncard + (ray2 (W i) '' S2).ncard := Set.ncard_union_le _ _
    _ ≤ 1 + 1 := add_le_add hc1 hc2

/-! ## Removing a Wedge Curve & Global Face Count Bound -/

lemma seg_pairwise_disjoint : ∀ (xs : List ℝ) {i j : Fin (xs.length + 1)},
    i ≠ j → Disjoint (seg xs i) (seg xs j)
  | [], i, j, hij => False.elim (hij ((Fin.eq_zero i).trans (Fin.eq_zero j).symm))
  | _ :: _, ⟨0, _⟩, ⟨0, _⟩, hij => False.elim (hij rfl)
  | _ :: _, ⟨0, _⟩, ⟨_ + 1, _⟩, _ => by
    rw [Set.disjoint_left]
    intro s hs1 hs2
    have h1 : s < _ := hs1
    have h2 : _ < s := hs2.2
    linarith
  | _ :: _, ⟨_ + 1, _⟩, ⟨0, _⟩, _ => by
    rw [Set.disjoint_left]
    intro s hs1 hs2
    have h1 : _ < s := hs1.2
    have h2 : s < _ := hs2
    linarith
  | _ :: tl, ⟨k₁ + 1, hk₁⟩, ⟨k₂ + 1, hk₂⟩, hij => by
    have hk_ne : (⟨k₁, by dsimp [List.length] at hk₁ ⊢; omega⟩ : Fin (tl.length + 1)) ≠
        ⟨k₂, by dsimp [List.length] at hk₂ ⊢; omega⟩ := by
      intro h; apply hij; have hv := congrArg Fin.val h; exact Fin.ext (by dsimp at hv ⊢; omega)
    rw [Set.disjoint_left]
    intro s hs1 hs2
    exact Set.disjoint_left.mp (seg_pairwise_disjoint tl hk_ne) hs1.1 hs2.1

private lemma halfspace_lt_convex (u y : ℝ × ℝ) :
    Convex ℝ {p : ℝ × ℝ | u.1 * (p.1 - y.1) + u.2 * (p.2 - y.2) < 0} := by
  intro x hx z hz a b ha hb hab
  have hlin : u.1 * ((a • x + b • z).1 - y.1) + u.2 * ((a • x + b • z).2 - y.2) =
      a * (u.1 * (x.1 - y.1) + u.2 * (x.2 - y.2)) +
      b * (u.1 * (z.1 - y.1) + u.2 * (z.2 - y.2)) := by
    simp only [Prod.smul_fst, Prod.smul_snd, Prod.fst_add, Prod.snd_add, smul_eq_mul]
    calc u.1 * (a * x.1 + b * z.1 - y.1) + u.2 * (a * x.2 + b * z.2 - y.2)
        = a * (u.1 * (x.1 - y.1) + u.2 * (x.2 - y.2)) +
          b * (u.1 * (z.1 - y.1) + u.2 * (z.2 - y.2)) +
          ((a + b) - 1) * (u.1 * y.1 + u.2 * y.2) := by ring
      _ = a * (u.1 * (x.1 - y.1) + u.2 * (x.2 - y.2)) +
          b * (u.1 * (z.1 - y.1) + u.2 * (z.2 - y.2)) := by rw [hab]; ring
  rw [Set.mem_setOf_eq, hlin]
  rcases lt_or_eq_of_le ha with ha_pos | rfl
  · have h1 := mul_neg_of_pos_of_neg ha_pos hx
    have h2 := mul_nonpos_of_nonneg_of_nonpos hb (le_of_lt hz)
    linarith
  · have hb1 : b = 1 := by linarith
    rw [hb1]; simp; exact hz

private lemma biUnion_ncard_le_sum {ι α : Type*} (S : Finset ι) (f : ι → Set α)
    (hf : ∀ i ∈ S, (f i).Finite) :
    (⋃ i ∈ S, f i).ncard ≤ ∑ i ∈ S, (f i).ncard := by
  induction S using Finset.induction with
  | empty => simp
  | @insert i S' hiS ih =>
    have hf' : ∀ j ∈ S', (f j).Finite := fun j hj => hf j (Finset.mem_insert_of_mem hj)
    have h_un_fin : (⋃ j ∈ S', f j).Finite := S'.finite_toSet.biUnion hf'
    have h_eq : (⋃ j ∈ insert i S', f j) = f i ∪ (⋃ j ∈ S', f j) := by
      ext x; simp [Finset.mem_insert]
    rw [h_eq, Finset.sum_insert hiS]
    exact (Set.ncard_union_le _ _).trans (add_le_add le_rfl (ih hf'))

private lemma ball_shift_mem {z d : ℝ × ℝ} {δ : ℝ} (hδ : 0 < δ) :
    ∃ ε > 0, (z.1 + ε * d.1, z.2 + ε * d.2) ∈ Metric.ball z δ := by
  let B := |d.1| + |d.2| + 1
  have hB : 0 < B := by positivity
  refine ⟨δ / (2 * B), by positivity, ?_⟩
  rw [Metric.mem_ball, Prod.dist_eq]
  have he : 0 < δ / (2 * B) := by positivity
  have h1 : dist (z.1 + (δ / (2 * B)) * d.1) z.1 < δ := by
    rw [Real.dist_eq, show z.1 + (δ / (2 * B)) * d.1 - z.1 = (δ / (2 * B)) * d.1 by ring,
      abs_mul, abs_of_pos he]
    have hle : |d.1| < B := by dsimp [B]; linarith [abs_nonneg d.2]
    calc (δ / (2 * B)) * |d.1| ≤ (δ / (2 * B)) * B :=
          mul_le_mul_of_nonneg_left (le_of_lt hle) (le_of_lt he)
      _ = δ / 2 := by field_simp [ne_of_gt hB]
      _ < δ := by linarith
  have h2 : dist (z.2 + (δ / (2 * B)) * d.2) z.2 < δ := by
    rw [Real.dist_eq, show z.2 + (δ / (2 * B)) * d.2 - z.2 = (δ / (2 * B)) * d.2 by ring,
      abs_mul, abs_of_pos he]
    have hle : |d.2| < B := by dsimp [B]; linarith [abs_nonneg d.1]
    calc (δ / (2 * B)) * |d.2| ≤ (δ / (2 * B)) * B :=
          mul_le_mul_of_nonneg_left (le_of_lt hle) (le_of_lt he)
      _ = δ / 2 := by field_simp [ne_of_gt hB]
      _ < δ := by linarith
  exact max_lt h1 h2

private lemma bdWedge_ball_memOpen_ne (Wk : OpenWedge) {z : ℝ × ℝ} (hz : z ∈ bdWedge Wk)
    {δ : ℝ} (hδ : 0 < δ) :
    (Metric.ball z δ ∩ {p | Wk.MemOpen p}).Nonempty := by
  let d : ℝ × ℝ := ((dir1 Wk).1 + (dir2 Wk).1, (dir1 Wk).2 + (dir2 Wk).2)
  obtain ⟨ε, hε, hball⟩ := ball_shift_mem (z := z) (d := d) hδ
  have hcl := (bdWedge_iff_closure_eq_zero Wk z).mp hz |>.1
  have hnd := Wk.h_nondeg
  have ho1 : 0 < Wk.u₁.1 * ((z.1 + ε * d.1) - Wk.y.1) +
      Wk.u₁.2 * ((z.2 + ε * d.2) - Wk.y.2) := by
    have e : Wk.u₁.1 * ((z.1 + ε * d.1) - Wk.y.1) + Wk.u₁.2 * ((z.2 + ε * d.2) - Wk.y.2) =
        (Wk.u₁.1 * (z.1 - Wk.y.1) + Wk.u₁.2 * (z.2 - Wk.y.2)) +
        ε * (Wk.u₁.1 * Wk.u₂.2 - Wk.u₁.2 * Wk.u₂.1) := by
      dsimp [d, dir1, dir2]; ring
    rw [e]; nlinarith [hcl.1]
  have ho2 : 0 < Wk.u₂.1 * ((z.1 + ε * d.1) - Wk.y.1) +
      Wk.u₂.2 * ((z.2 + ε * d.2) - Wk.y.2) := by
    have e : Wk.u₂.1 * ((z.1 + ε * d.1) - Wk.y.1) + Wk.u₂.2 * ((z.2 + ε * d.2) - Wk.y.2) =
        (Wk.u₂.1 * (z.1 - Wk.y.1) + Wk.u₂.2 * (z.2 - Wk.y.2)) +
        ε * (Wk.u₁.1 * Wk.u₂.2 - Wk.u₁.2 * Wk.u₂.1) := by
      dsimp [d, dir1, dir2]; ring
    rw [e]; nlinarith [hcl.2]
  exact ⟨(z.1 + ε * d.1, z.2 + ε * d.2), hball, ho1, ho2⟩

private lemma bdWedge_ball_memExt_ne (Wk : OpenWedge) {z : ℝ × ℝ} (hz : z ∈ bdWedge Wk)
    {δ : ℝ} (hδ : 0 < δ) :
    (Metric.ball z δ ∩ {p | Wk.MemExt p}).Nonempty := by
  have hnd := Wk.h_nondeg
  rcases (bdWedge_iff_closure_eq_zero Wk z).mp hz |>.2 with hz1 | hz2
  · let d : ℝ × ℝ := (-(dir2 Wk).1, -(dir2 Wk).2)
    obtain ⟨ε, hε, hball⟩ := ball_shift_mem (z := z) (d := d) hδ
    have hext : Wk.u₁.1 * ((z.1 + ε * d.1) - Wk.y.1) +
        Wk.u₁.2 * ((z.2 + ε * d.2) - Wk.y.2) < 0 := by
      have e : Wk.u₁.1 * ((z.1 + ε * d.1) - Wk.y.1) + Wk.u₁.2 * ((z.2 + ε * d.2) - Wk.y.2) =
          (Wk.u₁.1 * (z.1 - Wk.y.1) + Wk.u₁.2 * (z.2 - Wk.y.2)) -
          ε * (Wk.u₁.1 * Wk.u₂.2 - Wk.u₁.2 * Wk.u₂.1) := by
        dsimp [d, dir2]; ring
      rw [e, hz1]; nlinarith
    exact ⟨(z.1 + ε * d.1, z.2 + ε * d.2), hball, Or.inl hext⟩
  · let d : ℝ × ℝ := (-(dir1 Wk).1, -(dir1 Wk).2)
    obtain ⟨ε, hε, hball⟩ := ball_shift_mem (z := z) (d := d) hδ
    have hext : Wk.u₂.1 * ((z.1 + ε * d.1) - Wk.y.1) +
        Wk.u₂.2 * ((z.2 + ε * d.2) - Wk.y.2) < 0 := by
      have e : Wk.u₂.1 * ((z.1 + ε * d.1) - Wk.y.1) + Wk.u₂.2 * ((z.2 + ε * d.2) - Wk.y.2) =
          (Wk.u₂.1 * (z.1 - Wk.y.1) + Wk.u₂.2 * (z.2 - Wk.y.2)) -
          ε * (Wk.u₁.1 * Wk.u₂.2 - Wk.u₁.2 * Wk.u₂.1) := by
        dsimp [d, dir1]; ring
      rw [e, hz2]; nlinarith
    exact ⟨(z.1 + ε * d.1, z.2 + ε * d.2), hball, Or.inr hext⟩

private lemma remove_seg_arc_comps
    (Wk : OpenWedge) (hyk : Wk.y.1 < 0 ∧ Wk.y.2 < 0)
    (U : Set (ℝ × ℝ)) (hU_open : IsOpen U) (hU_om : U ⊆ {p : ℝ × ℝ | inOmega p})
    (xs : List ℝ) (hxs_sorted : xs.SortedLT)
    (_hxs_disj : ∀ s ∈ xs, gammaParam Wk s ∉ U)
    (i : Fin (xs.length + 1))
    (hi_sub : gammaParam Wk '' seg xs i ⊆ U)
    (hUi_open : IsOpen (U \ (gammaParam Wk '' seg xs i))) :
    (Comps (U \ (gammaParam Wk '' seg xs i))).encard ≤ (Comps U).encard + 1 := by
  let α : Set (ℝ × ℝ) := gammaParam Wk '' seg xs i
  have hα_ne : α.Nonempty := (seg_nonempty xs hxs_sorted i).image _
  have hα_conn : IsPreconnected α :=
    (seg_isPreconnected xs i).image (gammaParam Wk) (gammaParam_continuous Wk).continuousOn
  let K_other : Set (ℝ × ℝ) := gammaParam Wk '' (seg xs i)ᶜ ∪ {p ∈ bdWedge Wk | ¬ inOmega p}
  have hK_closed : IsClosed K_other :=
    gammaParam_image_closed_union_isClosed Wk hyk.1 hyk.2 (seg_isOpen xs i).isClosed_compl
  let V : (ℝ × ℝ) → Set (ℝ × ℝ) := fun z =>
    if z = Wk.y then U ∩ K_otherᶜ
    else if Wk.u₁.1 * (z.1 - Wk.y.1) + Wk.u₁.2 * (z.2 - Wk.y.2) = 0 then
      U ∩ K_otherᶜ ∩ {p | 0 < Wk.u₂.1 * (p.1 - Wk.y.1) + Wk.u₂.2 * (p.2 - Wk.y.2)}
    else
      U ∩ K_otherᶜ ∩ {p | 0 < Wk.u₁.1 * (p.1 - Wk.y.1) + Wk.u₁.2 * (p.2 - Wk.y.2)}
  have hV_open : ∀ z, IsOpen (V z) := by
    intro z; dsimp [V]
    split_ifs
    · exact hU_open.inter hK_closed.isOpen_compl
    · refine (hU_open.inter hK_closed.isOpen_compl).inter (isOpen_lt continuous_const ?_)
      fun_prop
    · refine (hU_open.inter hK_closed.isOpen_compl).inter (isOpen_lt continuous_const ?_)
      fun_prop
  have hz_mem_V : ∀ z ∈ α, z ∈ V z := by
    rintro z ⟨s, hs, rfl⟩
    have hzU : gammaParam Wk s ∈ U := hi_sub ⟨s, hs, rfl⟩
    have hzG : gammaParam Wk s ∈ Gamma Wk := gammaParam_mem_Gamma Wk hyk.1 hyk.2 s
    have hzK : gammaParam Wk s ∉ K_other := by
      rintro (⟨s', hs', heq⟩ | ⟨_, hnom⟩)
      · rw [gammaParam_injective Wk hyk.1 hyk.2 heq] at hs'
        exact hs' hs
      · exact hnom hzG.2
    dsimp [V]
    split_ifs with hzy hz1
    · exact ⟨hzU, hzK⟩
    · refine ⟨⟨hzU, hzK⟩, ?_⟩
      have hcl := (bdWedge_iff_closure_eq_zero Wk _).mp hzG.1 |>.1
      refine lt_of_le_of_ne hcl.2 fun hz2 => hzy ?_
      have hnd := ne_of_gt Wk.h_nondeg
      have e1 : (gammaParam Wk s).1 - Wk.y.1 = 0 := by
        have hmul : ((gammaParam Wk s).1 - Wk.y.1) * (Wk.u₁.1 * Wk.u₂.2 - Wk.u₁.2 * Wk.u₂.1) = 0 := by
          linear_combination Wk.u₂.2 * hz1 - Wk.u₁.2 * hz2.symm
        exact (mul_eq_zero.mp hmul).resolve_right hnd
      have e2 : (gammaParam Wk s).2 - Wk.y.2 = 0 := by
        have hmul : ((gammaParam Wk s).2 - Wk.y.2) * (Wk.u₁.1 * Wk.u₂.2 - Wk.u₁.2 * Wk.u₂.1) = 0 := by
          linear_combination -Wk.u₂.1 * hz1 + Wk.u₁.1 * hz2.symm
        exact (mul_eq_zero.mp hmul).resolve_right hnd
      ext <;> linarith
    · refine ⟨⟨hzU, hzK⟩, ?_⟩
      have hcl := (bdWedge_iff_closure_eq_zero Wk _).mp hzG.1 |>.1
      exact lt_of_le_of_ne hcl.1 (Ne.symm hz1)
  let r : (ℝ × ℝ) → ℝ := fun z =>
    if hz : z ∈ α then (Metric.isOpen_iff.mp (hV_open z) z (hz_mem_V z hz)).choose else 1
  have hr_pos : ∀ z ∈ α, 0 < r z := fun z hz => by
    dsimp [r]; rw [dif_pos hz]
    exact (Metric.isOpen_iff.mp (hV_open z) z (hz_mem_V z hz)).choose_spec.1
  have hball_V : ∀ z ∈ α, Metric.ball z (r z) ⊆ V z := fun z hz => by
    dsimp [r]; rw [dif_pos hz]
    exact (Metric.isOpen_iff.mp (hV_open z) z (hz_mem_V z hz)).choose_spec.2
  have hV_sub_UK : ∀ z, V z ⊆ U ∩ K_otherᶜ := by
    intro z; dsimp [V]; split_ifs <;> [exact Set.Subset.rfl; exact Set.inter_subset_left; exact Set.inter_subset_left]
  have hball_sub : ∀ z ∈ α, Metric.ball z (r z) ⊆ U := fun z hz =>
    (hball_V z hz).trans ((hV_sub_UK z).trans Set.inter_subset_left)
  let BL : (ℝ × ℝ) → Set (ℝ × ℝ) := fun z => Metric.ball z (r z) ∩ {p | Wk.MemOpen p}
  let BR : (ℝ × ℝ) → Set (ℝ × ℝ) := fun z => Metric.ball z (r z) ∩ {p | Wk.MemExt p}
  have hball_split : ∀ z ∈ α, Metric.ball z (r z) \ α = BL z ∪ BR z := by
    intro z hz
    ext p; constructor
    · rintro ⟨hp_ball, hp_nα⟩
      have hpUK := hV_sub_UK z (hball_V z hz hp_ball)
      have hp_om : inOmega p := hU_om hpUK.1
      have hp_nbd : p ∉ bdWedge Wk := by
        intro hp_bd
        have hp_G : p ∈ Gamma Wk := ⟨hp_bd, hp_om⟩
        rw [← gammaParam_range Wk hyk.1 hyk.2] at hp_G
        obtain ⟨s', rfl⟩ := hp_G
        by_cases hs' : s' ∈ seg xs i
        · exact hp_nα ⟨s', hs', rfl⟩
        · exact hpUK.2 (Or.inl ⟨s', hs', rfl⟩)
      dsimp [bdWedge] at hp_nbd
      push Not at hp_nbd
      by_cases ho : Wk.MemOpen p
      · left; exact ⟨hp_ball, ho⟩
      · right; exact ⟨hp_ball, hp_nbd ho⟩
    · rintro (⟨hp_ball, ho⟩ | ⟨hp_ball, he⟩)
      · refine ⟨hp_ball, fun hpα => ?_⟩
        obtain ⟨s', _, rfl⟩ := hpα
        exact (gammaParam_mem_Gamma Wk hyk.1 hyk.2 s').1.1 ho
      · refine ⟨hp_ball, fun hpα => ?_⟩
        obtain ⟨s', _, rfl⟩ := hpα
        exact (gammaParam_mem_Gamma Wk hyk.1 hyk.2 s').1.2 he
  have hBL_ne : ∀ z ∈ α, (BL z).Nonempty := fun z hz => by
    obtain ⟨s, _, rfl⟩ := hz
    exact bdWedge_ball_memOpen_ne Wk (gammaParam_mem_Gamma Wk hyk.1 hyk.2 s).1 (hr_pos _ ⟨s, ‹_›, rfl⟩)
  have hBL_conn : ∀ z ∈ α, IsPreconnected (BL z) := fun z _ =>
    ((convex_ball z (r z)).inter (memOpen_convex Wk)).isPreconnected
  have hBR_ne : ∀ z ∈ α, (BR z).Nonempty := fun z hz => by
    obtain ⟨s, _, rfl⟩ := hz
    exact bdWedge_ball_memExt_ne Wk (gammaParam_mem_Gamma Wk hyk.1 hyk.2 s).1 (hr_pos _ ⟨s, ‹_›, rfl⟩)
  have hBR_conn : ∀ z ∈ α, IsPreconnected (BR z) := by
    intro z hz
    dsimp [BR]
    by_cases hzy : z = Wk.y
    · let S1 : Set (ℝ × ℝ) := Metric.ball z (r z) ∩
        {p | Wk.u₁.1 * (p.1 - Wk.y.1) + Wk.u₁.2 * (p.2 - Wk.y.2) < 0}
      let S2 : Set (ℝ × ℝ) := Metric.ball z (r z) ∩
        {p | Wk.u₂.1 * (p.1 - Wk.y.1) + Wk.u₂.2 * (p.2 - Wk.y.2) < 0}
      have heq : Metric.ball z (r z) ∩ {p | Wk.MemExt p} = S1 ∪ S2 := by
        ext p; simp [S1, S2, OpenWedge.MemExt, and_or_left]
      rw [heq]
      have hc1 : IsPreconnected S1 :=
        ((convex_ball z (r z)).inter (halfspace_lt_convex Wk.u₁ Wk.y)).isPreconnected
      have hc2 : IsPreconnected S2 :=
        ((convex_ball z (r z)).inter (halfspace_lt_convex Wk.u₂ Wk.y)).isPreconnected
      let d_neg : ℝ × ℝ := (-(dir1 Wk).1 - (dir2 Wk).1, -(dir1 Wk).2 - (dir2 Wk).2)
      obtain ⟨ε, hε, hball⟩ := ball_shift_mem (z := z) (d := d_neg) (hr_pos z hz)
      have hnd := Wk.h_nondeg
      have ho1 : Wk.u₁.1 * ((z.1 + ε * d_neg.1) - Wk.y.1) +
          Wk.u₁.2 * ((z.2 + ε * d_neg.2) - Wk.y.2) < 0 := by
        rw [hzy]
        have e : Wk.u₁.1 * ((Wk.y.1 + ε * d_neg.1) - Wk.y.1) +
            Wk.u₁.2 * ((Wk.y.2 + ε * d_neg.2) - Wk.y.2) =
            -ε * (Wk.u₁.1 * Wk.u₂.2 - Wk.u₁.2 * Wk.u₂.1) := by
          dsimp [d_neg, dir1, dir2]; ring
        rw [e]; nlinarith
      have ho2 : Wk.u₂.1 * ((z.1 + ε * d_neg.1) - Wk.y.1) +
          Wk.u₂.2 * ((z.2 + ε * d_neg.2) - Wk.y.2) < 0 := by
        rw [hzy]
        have e : Wk.u₂.1 * ((Wk.y.1 + ε * d_neg.1) - Wk.y.1) +
            Wk.u₂.2 * ((Wk.y.2 + ε * d_neg.2) - Wk.y.2) =
            -ε * (Wk.u₁.1 * Wk.u₂.2 - Wk.u₁.2 * Wk.u₂.1) := by
          dsimp [d_neg, dir1, dir2]; ring
        rw [e]; nlinarith
      exact hc1.union' ⟨(z.1 + ε * d_neg.1, z.2 + ε * d_neg.2), ⟨hball, ho1⟩, ⟨hball, ho2⟩⟩ hc2
    · by_cases hz1 : Wk.u₁.1 * (z.1 - Wk.y.1) + Wk.u₁.2 * (z.2 - Wk.y.2) = 0
      · have hsubV : Metric.ball z (r z) ⊆ {p | 0 < Wk.u₂.1 * (p.1 - Wk.y.1) + Wk.u₂.2 * (p.2 - Wk.y.2)} := by
          intro p hp
          have hpV := hball_V z hz hp
          dsimp [V] at hpV
          rw [if_neg hzy, if_pos hz1] at hpV
          exact hpV.2
        have heq : Metric.ball z (r z) ∩ {p | Wk.MemExt p} =
            Metric.ball z (r z) ∩ {p | Wk.u₁.1 * (p.1 - Wk.y.1) + Wk.u₁.2 * (p.2 - Wk.y.2) < 0} := by
          ext p; constructor
          · rintro ⟨hp, hp1 | hp2⟩
            · exact ⟨hp, hp1⟩
            · exfalso; have hp_pos : 0 < Wk.u₂.1 * (p.1 - Wk.y.1) + Wk.u₂.2 * (p.2 - Wk.y.2) := hsubV hp
              linarith
          · rintro ⟨hp, hp1⟩; exact ⟨hp, Or.inl hp1⟩
        rw [heq]
        exact ((convex_ball z (r z)).inter (halfspace_lt_convex Wk.u₁ Wk.y)).isPreconnected
      · have hsubV : Metric.ball z (r z) ⊆ {p | 0 < Wk.u₁.1 * (p.1 - Wk.y.1) + Wk.u₁.2 * (p.2 - Wk.y.2)} := by
          intro p hp
          have hpV := hball_V z hz hp
          dsimp [V] at hpV
          rw [if_neg hzy, if_neg hz1] at hpV
          exact hpV.2
        have heq : Metric.ball z (r z) ∩ {p | Wk.MemExt p} =
            Metric.ball z (r z) ∩ {p | Wk.u₂.1 * (p.1 - Wk.y.1) + Wk.u₂.2 * (p.2 - Wk.y.2) < 0} := by
          ext p; constructor
          · rintro ⟨hp, hp1 | hp2⟩
            · exfalso; have hp_pos : 0 < Wk.u₁.1 * (p.1 - Wk.y.1) + Wk.u₁.2 * (p.2 - Wk.y.2) := hsubV hp
              linarith
            · exact ⟨hp, hp2⟩
          · rintro ⟨hp, hp2⟩; exact ⟨hp, Or.inr hp2⟩
        rw [heq]
        exact ((convex_ball z (r z)).inter (halfspace_lt_convex Wk.u₂ Wk.y)).isPreconnected
  have h_ball_inter : ∀ z ∈ α, ∀ z' ∈ α, z' ∈ Metric.ball z (r z) →
      ∃ δ > 0, Metric.ball z' δ ⊆ Metric.ball z (r z) ∩ Metric.ball z' (r z') := by
    intro z _ z' hz' hz'b
    let δ := min (r z - dist z' z) (r z')
    have hδ : 0 < δ := lt_min (sub_pos.mpr (Metric.mem_ball.mp hz'b)) (hr_pos z' hz')
    refine ⟨δ, hδ, fun p hp => ⟨?_, ?_⟩⟩
    · rw [Metric.mem_ball] at hp ⊢
      have hd1 : dist p z' < r z - dist z' z := lt_of_lt_of_le hp (min_le_left _ _)
      linarith [dist_triangle p z' z]
    · exact Metric.mem_ball.mpr (lt_of_lt_of_le (Metric.mem_ball.mp hp) (min_le_right _ _))
  have hBL_ov : ∀ z ∈ α, ∀ z' ∈ α, z' ∈ Metric.ball z (r z) → (BL z ∩ BL z').Nonempty := by
    intro z hz z' hz' hz'b
    obtain ⟨δ, hδ, hsub_ball⟩ := h_ball_inter z hz z' hz' hz'b
    obtain ⟨s', _, rfl⟩ := hz'
    obtain ⟨p, hp_ball, hp_om⟩ :=
      bdWedge_ball_memOpen_ne Wk (gammaParam_mem_Gamma Wk hyk.1 hyk.2 s').1 hδ
    exact ⟨p, ⟨(hsub_ball hp_ball).1, hp_om⟩, ⟨(hsub_ball hp_ball).2, hp_om⟩⟩
  have hBR_ov : ∀ z ∈ α, ∀ z' ∈ α, z' ∈ Metric.ball z (r z) → (BR z ∩ BR z').Nonempty := by
    intro z hz z' hz' hz'b
    obtain ⟨δ, hδ, hsub_ball⟩ := h_ball_inter z hz z' hz' hz'b
    obtain ⟨s', _, rfl⟩ := hz'
    obtain ⟨p, hp_ball, hp_ext⟩ :=
      bdWedge_ball_memExt_ne Wk (gammaParam_mem_Gamma Wk hyk.1 hyk.2 s').1 hδ
    exact ⟨p, ⟨(hsub_ball hp_ball).1, hp_ext⟩, ⟨(hsub_ball hp_ball).2, hp_ext⟩⟩
  exact comps_remove_arc hU_open hi_sub hα_ne hα_conn hUi_open r BL BR
    hr_pos hball_sub hball_split hBL_ne hBL_conn hBR_ne hBR_conn hBL_ov hBR_ov

lemma add_wedge_comps_bound {W : Fin 5 → OpenWedge} (hGP : GeneralPosition W)
    (h_apex : ∀ m : Fin 5, (W m).y.1 < 0 ∧ (W m).y.2 < 0)
    (S : Finset (Fin 5)) (k : Fin 5) (hkS : k ∉ S) :
    (Comps ({p : ℝ × ℝ | inOmega p} \ ⋃ j ∈ insert k S, Gamma (W j))).encard ≤
    (Comps ({p : ℝ × ℝ | inOmega p} \ ⋃ j ∈ S, Gamma (W j))).encard +
      1 + ∑ j ∈ S, ((Gamma (W k) ∩ Gamma (W j)).ncard : ℕ∞) := by
  let U₀ : Set (ℝ × ℝ) := {p : ℝ × ℝ | inOmega p} \ ⋃ j ∈ S, Gamma (W j)
  have hU₀_eq : U₀ = {p : ℝ × ℝ | inOmega p} \ ⋃ j ∈ S, bdWedge (W j) := by
    ext p; constructor
    · rintro ⟨hp_om, hp_not⟩
      refine ⟨hp_om, fun hbd => hp_not ?_⟩
      rw [Set.mem_iUnion₂] at hbd ⊢
      rcases hbd with ⟨j, hj, hpj⟩
      exact ⟨j, hj, hpj, hp_om⟩
    · rintro ⟨hp_om, hp_not⟩
      refine ⟨hp_om, fun hG => hp_not ?_⟩
      rw [Set.mem_iUnion₂] at hG ⊢
      rcases hG with ⟨j, hj, hpj, _⟩
      exact ⟨j, hj, hpj⟩
  have hU₀_open : IsOpen U₀ := by
    rw [hU₀_eq]
    exact isOpen_omega.sdiff (S.finite_toSet.isClosed_biUnion fun j _ => bdWedge_isClosed (W j))
  let P_set : Set (ℝ × ℝ) := ⋃ j ∈ S, (Gamma (W k) ∩ Gamma (W j))
  have hP_fin : P_set.Finite :=
    S.finite_toSet.biUnion fun j hj => gamma_inter_finite hGP (ne_of_mem_of_not_mem hj hkS).symm
  let P_param : Set ℝ := (gammaParam (W k)) ⁻¹' P_set
  have hP_param_fin : P_param.Finite :=
    hP_fin.preimage (gammaParam_injective (W k) (h_apex k).1 (h_apex k).2).injOn
  let xs : List ℝ := hP_param_fin.toFinset.sort (· ≤ ·)
  have hxs_sorted : xs.SortedLT := Finset.sortedLT_sort _
  have hxs_iff : ∀ s : ℝ, s ∈ xs ↔ gammaParam (W k) s ∈ P_set := fun s => by
    simp [xs, P_param]
  let α : Fin (xs.length + 1) → Set (ℝ × ℝ) := fun i => gammaParam (W k) '' seg xs i
  let U_step : ℕ → Set (ℝ × ℝ) := fun m =>
    U₀ \ ⋃ (i : Fin (xs.length + 1)) (_ : i.val < m), α i
  have hU_step_om : ∀ m, U_step m ⊆ {p : ℝ × ℝ | inOmega p} := fun m _ hp => hp.1.1
  have hU_step_open : ∀ m, IsOpen (U_step m) := by
    intro m
    let I : Finset (Fin (xs.length + 1)) := Finset.univ.filter (fun i => i.val < m)
    let S_cl : Set ℝ := ⋃ i ∈ (I : Set (Fin (xs.length + 1))), closure (seg xs i)
    have hS_cl : IsClosed S_cl :=
      I.finite_toSet.isClosed_biUnion fun _ _ => isClosed_closure
    let K_cl : Set (ℝ × ℝ) :=
      gammaParam (W k) '' S_cl ∪ {p ∈ bdWedge (W k) | ¬ inOmega p}
    have hK_cl : IsClosed K_cl :=
      gammaParam_image_closed_union_isClosed (W k) (h_apex k).1 (h_apex k).2 hS_cl
    have hEq : U_step m = U₀ \ K_cl := by
      ext p; constructor
      · rintro ⟨hpU₀, hp_not⟩
        refine ⟨hpU₀, ?_⟩
        rintro (⟨s, hs, rfl⟩ | ⟨_, hnom⟩)
        · rw [Set.mem_iUnion₂] at hs
          rcases hs with ⟨i, hiI, hsi⟩
          rcases closure_seg_subset xs i hsi with hseg | hmem_xs
          · exact hp_not (Set.mem_iUnion₂.mpr ⟨i, (Finset.mem_filter.mp (Finset.mem_coe.mp hiI)).2,
              ⟨s, hseg, rfl⟩⟩)
          · have hP := (hxs_iff s).mp hmem_xs
            rw [Set.mem_iUnion₂] at hP
            rcases hP with ⟨j, hjS, _, hjG⟩
            exact hpU₀.2 (Set.mem_iUnion₂.mpr ⟨j, hjS, hjG⟩)
        · exact hnom hpU₀.1
      · rintro ⟨hpU₀, hp_not⟩
        refine ⟨hpU₀, fun hmem => hp_not ?_⟩
        rw [Set.mem_iUnion₂] at hmem
        rcases hmem with ⟨i, him, ⟨s, hsi, rfl⟩⟩
        left
        refine ⟨s, Set.mem_iUnion₂.mpr ⟨i, ?_, subset_closure hsi⟩, rfl⟩
        exact Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ i, him⟩)
    rw [hEq]
    exact hU₀_open.sdiff hK_cl
  have hxs_disj : ∀ m (s : ℝ), s ∈ xs → gammaParam (W k) s ∉ U_step m := by
    intro m s hs hp
    have hP := (hxs_iff s).mp hs
    rw [Set.mem_iUnion₂] at hP
    rcases hP with ⟨j, hjS, _, hjG⟩
    exact hp.1.2 (Set.mem_iUnion₂.mpr ⟨j, hjS, hjG⟩)
  have h_step : ∀ m : ℕ, m ≤ xs.length + 1 →
      (Comps (U_step m)).encard ≤ (Comps U₀).encard + (m : ℕ∞) := by
    intro m
    induction m with
    | zero =>
      intro _
      have heq : U_step 0 = U₀ := by ext p; simp [U_step]
      rw [heq]; simp
    | succ m ih =>
      intro hm
      have hm' : m < xs.length + 1 := hm
      let i : Fin (xs.length + 1) := ⟨m, hm'⟩
      have h_split : U_step (m + 1) = U_step m \ α i := by
        ext p; constructor
        · rintro ⟨hpU₀, hp_not⟩
          refine ⟨⟨hpU₀, fun h => hp_not ?_⟩, fun h => hp_not ?_⟩
          · rw [Set.mem_iUnion₂] at h ⊢
            rcases h with ⟨j, hj, hpj⟩
            exact ⟨j, Nat.lt_succ_of_lt hj, hpj⟩
          · exact Set.mem_iUnion₂.mpr ⟨i, Nat.lt_succ_self m, h⟩
        · rintro ⟨⟨hpU₀, hp_not⟩, hp_ni⟩
          refine ⟨hpU₀, fun h => ?_⟩
          rw [Set.mem_iUnion₂] at h
          rcases h with ⟨j, hj, hpj⟩
          rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj' | hj'
          · exact hp_not (Set.mem_iUnion₂.mpr ⟨j, hj', hpj⟩)
          · have hji : j = i := Fin.ext hj'
            rw [hji] at hpj
            exact hp_ni hpj
      have hi_sub : α i ⊆ U_step m := by
        rintro p ⟨s, hs, rfl⟩
        refine ⟨⟨(gammaParam_mem_Gamma (W k) (h_apex k).1 (h_apex k).2 s).2, fun hU => ?_⟩,
            fun hprev => ?_⟩
        · rw [Set.mem_iUnion₂] at hU
          rcases hU with ⟨j, hjS, hjG⟩
          have hP : gammaParam (W k) s ∈ P_set :=
            Set.mem_iUnion₂.mpr ⟨j, hjS, gammaParam_mem_Gamma (W k) (h_apex k).1 (h_apex k).2 s, hjG⟩
          exact seg_disjoint_list xs hxs_sorted i hs ((hxs_iff s).mpr hP)
        · rw [Set.mem_iUnion₂] at hprev
          rcases hprev with ⟨j, hj, ⟨s', hs', heq⟩⟩
          have hij : j ≠ i := fun h => by rw [h] at hj; exact Nat.lt_irrefl m hj
          have hs_eq : s' = s := gammaParam_injective (W k) (h_apex k).1 (h_apex k).2 heq
          rw [hs_eq] at hs'
          exact Set.disjoint_left.mp (seg_pairwise_disjoint xs hij) hs' hs
      have h_inc : (Comps (U_step (m + 1))).encard ≤ (Comps (U_step m)).encard + 1 := by
        rw [h_split]
        exact remove_seg_arc_comps (W k) (h_apex k) (U_step m) (hU_step_open m) (hU_step_om m)
          xs hxs_sorted (fun s hs => hxs_disj m s hs) i hi_sub (h_split ▸ hU_step_open (m + 1))
      calc (Comps (U_step (m + 1))).encard
          ≤ (Comps (U_step m)).encard + 1 := h_inc
        _ ≤ ((Comps U₀).encard + (m : ℕ∞)) + 1 := add_le_add (ih (Nat.le_of_lt hm')) le_rfl
        _ = (Comps U₀).encard + ((m + 1 : ℕ) : ℕ∞) := by
            rw [Nat.cast_add, Nat.cast_one, add_assoc]
  have h_final_eq : {p : ℝ × ℝ | inOmega p} \ ⋃ j ∈ insert k S, Gamma (W j) =
      U_step (xs.length + 1) := by
    ext p; constructor
    · rintro ⟨hp_om, hp_not⟩
      refine ⟨⟨hp_om, fun h => hp_not ?_⟩, fun h => hp_not ?_⟩
      · rw [Set.mem_iUnion₂] at h ⊢
        rcases h with ⟨j, hj, hpj⟩
        exact ⟨j, Finset.mem_insert_of_mem hj, hpj⟩
      · rw [Set.mem_iUnion₂] at h
        rcases h with ⟨i, _, ⟨s, _, rfl⟩⟩
        exact Set.mem_iUnion₂.mpr ⟨k, Finset.mem_insert_self k S,
          gammaParam_mem_Gamma (W k) (h_apex k).1 (h_apex k).2 s⟩
    · rintro ⟨⟨hp_om, hp_notS⟩, hp_not_seg⟩
      refine ⟨hp_om, fun h => ?_⟩
      rw [Set.mem_iUnion₂] at h
      rcases h with ⟨j, hj, hpj⟩
      rcases Finset.mem_insert.mp hj with hjk | hjS
      · rw [hjk] at hpj
        rw [← gammaParam_range (W k) (h_apex k).1 (h_apex k).2] at hpj
        obtain ⟨s, rfl⟩ := hpj
        have hs_nxs : s ∉ xs := by
          intro hmem
          have hP := (hxs_iff s).mp hmem
          rw [Set.mem_iUnion₂] at hP
          rcases hP with ⟨j', hj', _, hjG⟩
          exact hp_notS (Set.mem_iUnion₂.mpr ⟨j', hj', hjG⟩)
        have hmem_seg := compl_list_subset_iUnion_seg xs hs_nxs
        rw [Set.mem_iUnion] at hmem_seg
        obtain ⟨i, hsi⟩ := hmem_seg
        exact hp_not_seg (Set.mem_iUnion₂.mpr ⟨i, i.isLt, ⟨s, hsi, rfl⟩⟩)
      · exact hp_notS (Set.mem_iUnion₂.mpr ⟨j, hjS, hpj⟩)
  have h_len_bound : xs.length ≤ ∑ j ∈ S, (Gamma (W k) ∩ Gamma (W j)).ncard := by
    have h1 : xs.length = hP_param_fin.toFinset.card := Finset.length_sort (· ≤ ·)
    have h2 : (hP_param_fin.toFinset.card : ℕ) = P_param.ncard :=
      (Set.ncard_eq_toFinset_card P_param hP_param_fin).symm
    have h3 : P_param.ncard ≤ P_set.ncard := by
      have himg : gammaParam (W k) '' P_param ⊆ P_set := Set.image_preimage_subset _ _
      rw [← Set.ncard_image_of_injective P_param (gammaParam_injective (W k) (h_apex k).1 (h_apex k).2)]
      exact Set.ncard_le_ncard himg hP_fin
    have h4 : P_set.ncard ≤ ∑ j ∈ S, (Gamma (W k) ∩ Gamma (W j)).ncard :=
      biUnion_ncard_le_sum S (fun j => Gamma (W k) ∩ Gamma (W j))
        fun j hj => gamma_inter_finite hGP (ne_of_mem_of_not_mem hj hkS).symm
    omega
  rw [h_final_eq]
  have h_fin := h_step (xs.length + 1) le_rfl
  have h_enat : ((xs.length + 1 : ℕ) : ℕ∞) ≤
      1 + ∑ j ∈ S, ((Gamma (W k) ∩ Gamma (W j)).ncard : ℕ∞) := by
    have h_sum_coe : (∑ j ∈ S, ((Gamma (W k) ∩ Gamma (W j)).ncard : ℕ∞)) =
        ((∑ j ∈ S, (Gamma (W k) ∩ Gamma (W j)).ncard : ℕ) : ℕ∞) := by
      push_cast; rfl
    rw [h_sum_coe, add_comm (1 : ℕ∞)]
    calc ((xs.length + 1 : ℕ) : ℕ∞)
        ≤ (((∑ j ∈ S, (Gamma (W k) ∩ Gamma (W j)).ncard) + 1 : ℕ) : ℕ∞) :=
          Nat.cast_le.mpr (by omega)
      _ = ((∑ j ∈ S, (Gamma (W k) ∩ Gamma (W j)).ncard : ℕ) : ℕ∞) + 1 := by
          push_cast; rfl
  calc (Comps (U_step (xs.length + 1))).encard
      ≤ (Comps U₀).encard + ((xs.length + 1 : ℕ) : ℕ∞) := h_fin
    _ ≤ (Comps U₀).encard + (1 + ∑ j ∈ S, ((Gamma (W k) ∩ Gamma (W j)).ncard : ℕ∞)) :=
        add_le_add le_rfl h_enat
    _ = (Comps U₀).encard + 1 + ∑ j ∈ S, ((Gamma (W k) ∩ Gamma (W j)).ncard : ℕ∞) := by
        rw [add_assoc]

lemma arr_comps_bound {W : Fin 5 → OpenWedge} (hGP : GeneralPosition W)
    (h_apex : ∀ m : Fin 5, (W m).y.1 < 0 ∧ (W m).y.2 < 0)
    (S : Finset (Fin 5)) :
    (Comps ({p : ℝ × ℝ | inOmega p} \ ⋃ j ∈ S, Gamma (W j))).encard ≤
    1 + (S.card : ℕ∞) +
      ∑ i ∈ S, ∑ j ∈ S with i < j, ((Gamma (W i) ∩ Gamma (W j)).ncard : ℕ∞) := by
  induction S using Finset.induction with
  | empty =>
    simp only [Finset.notMem_empty, Set.iUnion_of_empty, Set.iUnion_empty, Set.sdiff_empty,
      Finset.card_empty, CharP.cast_eq_zero, add_zero, Finset.sum_empty]
    exact comps_omega_card.le
  | @insert k S' hkS ih =>
    have h_add := add_wedge_comps_bound hGP h_apex S' k hkS
    have h_sum_eq : ∑ i ∈ insert k S', ∑ j ∈ insert k S' with i < j,
          ((Gamma (W i) ∩ Gamma (W j)).ncard : ℕ∞) =
        (∑ i ∈ S', ∑ j ∈ S' with i < j, ((Gamma (W i) ∩ Gamma (W j)).ncard : ℕ∞)) +
          ∑ j ∈ S', ((Gamma (W k) ∩ Gamma (W j)).ncard : ℕ∞) := by
      have h_in : ∀ i ∈ S', (∑ j ∈ (insert k S').filter (i < ·), ((Gamma (W i) ∩ Gamma (W j)).ncard : ℕ∞)) =
          (∑ j ∈ S'.filter (i < ·), ((Gamma (W i) ∩ Gamma (W j)).ncard : ℕ∞)) +
          (if i < k then ((Gamma (W i) ∩ Gamma (W k)).ncard : ℕ∞) else 0) := by
        intro i _
        rw [Finset.filter_insert]
        split_ifs with hik
        · rw [Finset.sum_insert (fun h => hkS (Finset.mem_filter.mp h).1), add_comm]
        · rw [add_zero]
      rw [Finset.sum_insert hkS]
      have h_k : (∑ j ∈ (insert k S').filter (k < ·), ((Gamma (W k) ∩ Gamma (W j)).ncard : ℕ∞)) =
          ∑ j ∈ S', if k < j then ((Gamma (W k) ∩ Gamma (W j)).ncard : ℕ∞) else 0 := by
        rw [Finset.filter_insert, if_neg (lt_irrefl k), Finset.sum_filter]
      have h_S : (∑ i ∈ S', ∑ j ∈ (insert k S').filter (i < ·), ((Gamma (W i) ∩ Gamma (W j)).ncard : ℕ∞)) =
          (∑ i ∈ S', ∑ j ∈ S'.filter (i < ·), ((Gamma (W i) ∩ Gamma (W j)).ncard : ℕ∞)) +
          ∑ i ∈ S', if i < k then ((Gamma (W i) ∩ Gamma (W k)).ncard : ℕ∞) else 0 := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl h_in
      rw [h_k, h_S]
      have h_pair : (∑ j ∈ S', if k < j then ((Gamma (W k) ∩ Gamma (W j)).ncard : ℕ∞) else 0) +
          (∑ i ∈ S', if i < k then ((Gamma (W i) ∩ Gamma (W k)).ncard : ℕ∞) else 0) =
          ∑ j ∈ S', ((Gamma (W k) ∩ Gamma (W j)).ncard : ℕ∞) := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun j hj => ?_
        have hne : j ≠ k := ne_of_mem_of_not_mem hj hkS
        rcases lt_or_gt_of_ne hne with hjk | hkj
        · rw [if_neg (not_lt.mpr (le_of_lt hjk)), if_pos hjk, zero_add, Set.inter_comm]
        · rw [if_pos hkj, if_neg (not_lt.mpr (le_of_lt hkj)), add_zero]
      rw [← add_assoc, add_comm (∑ j ∈ S', if k < j then _ else _), add_assoc, h_pair]
    calc (Comps ({p : ℝ × ℝ | inOmega p} \ ⋃ j ∈ insert k S', Gamma (W j))).encard
        ≤ (Comps ({p : ℝ × ℝ | inOmega p} \ ⋃ j ∈ S', Gamma (W j))).encard +
            1 + ∑ j ∈ S', ((Gamma (W k) ∩ Gamma (W j)).ncard : ℕ∞) := h_add
      _ ≤ (1 + (S'.card : ℕ∞) +
            ∑ i ∈ S', ∑ j ∈ S' with i < j, ((Gamma (W i) ∩ Gamma (W j)).ncard : ℕ∞)) +
            1 + ∑ j ∈ S', ((Gamma (W k) ∩ Gamma (W j)).ncard : ℕ∞) :=
          add_le_add (add_le_add ih le_rfl) le_rfl
      _ = 1 + ((insert k S').card : ℕ∞) +
            ∑ i ∈ insert k S', ∑ j ∈ insert k S' with i < j,
              ((Gamma (W i) ∩ Gamma (W j)).ncard : ℕ∞) := by
          rw [Finset.card_insert_of_notMem hkS, Nat.cast_add, Nat.cast_one, h_sum_eq]
          simp only [add_assoc, add_left_comm]

lemma comp_ne_of_sep_wedge {W : Fin 5 → OpenWedge} {S : Finset (Fin 5)}
    {j : Fin 5} (hj : j ∈ S) {p₁ p₂ : ℝ × ℝ}
    (hp₁ : p₁ ∈ {p : ℝ × ℝ | inOmega p} \ ⋃ i ∈ S, Gamma (W i))
    (hp₂ : p₂ ∈ {p : ℝ × ℝ | inOmega p} \ ⋃ i ∈ S, Gamma (W i))
    (hsep : ((W j).MemOpen p₁ ∧ (W j).MemExt p₂) ∨ ((W j).MemExt p₁ ∧ (W j).MemOpen p₂)) :
    connectedComponentIn ({p : ℝ × ℝ | inOmega p} \ ⋃ i ∈ S, Gamma (W i)) p₁ ≠
    connectedComponentIn ({p : ℝ × ℝ | inOmega p} \ ⋃ i ∈ S, Gamma (W i)) p₂ := by
  let U := {p : ℝ × ℝ | inOmega p} \ ⋃ i ∈ S, Gamma (W i)
  intro heq
  have hp₂_in : p₂ ∈ connectedComponentIn U p₁ := by
    rw [heq]; exact mem_connectedComponentIn hp₂
  have hp₁_in : p₁ ∈ connectedComponentIn U p₁ := mem_connectedComponentIn hp₁
  have hsub : connectedComponentIn U p₁ ⊆
      {p | (W j).MemOpen p} ∪ {p | (W j).MemExt p} := by
    intro p hp
    have hpU : p ∈ U := connectedComponentIn_subset U p₁ hp
    have hp_nbd : p ∉ bdWedge (W j) := fun hbd =>
      hpU.2 (Set.mem_iUnion₂.mpr ⟨j, hj, hbd, hpU.1⟩)
    dsimp [bdWedge] at hp_nbd
    push Not at hp_nbd
    by_cases ho : (W j).MemOpen p
    · left; exact ho
    · right; exact hp_nbd ho
  have hdisj : Disjoint {p | (W j).MemOpen p} {p | (W j).MemExt p} := by
    rw [Set.disjoint_left]
    exact fun p ho he => memOpen_memExt_disjoint (W j) p ⟨ho, he⟩
  rcases isPreconnected_connectedComponentIn.subset_or_subset
      (isOpen_memOpen (W j)) (isOpen_memExt (W j)) hdisj hsub with hO | hE
  · rcases hsep with ⟨_, he₂⟩ | ⟨he₁, _⟩
    · exact memOpen_memExt_disjoint (W j) p₂ ⟨hO hp₂_in, he₂⟩
    · exact memOpen_memExt_disjoint (W j) p₁ ⟨hO hp₁_in, he₁⟩
  · rcases hsep with ⟨ho₁, _⟩ | ⟨_, ho₂⟩
    · exact memOpen_memExt_disjoint (W j) p₁ ⟨ho₁, hE hp₁_in⟩
    · exact memOpen_memExt_disjoint (W j) p₂ ⟨ho₂, hE hp₂_in⟩

lemma card_le_comps_of_inj {W : Fin 5 → OpenWedge} {S : Finset (Fin 5)}
    {α : Type*} [Fintype α] (pt : α → ℝ × ℝ)
    (h_mem : ∀ a : α, pt a ∈ {p : ℝ × ℝ | inOmega p} \ ⋃ i ∈ S, Gamma (W i))
    (h_inj : ∀ a b : α, a ≠ b →
      connectedComponentIn ({p : ℝ × ℝ | inOmega p} \ ⋃ i ∈ S, Gamma (W i)) (pt a) ≠
      connectedComponentIn ({p : ℝ × ℝ | inOmega p} \ ⋃ i ∈ S, Gamma (W i)) (pt b)) :
    (Fintype.card α : ℕ∞) ≤
      (Comps ({p : ℝ × ℝ | inOmega p} \ ⋃ i ∈ S, Gamma (W i))).encard := by
  let U := {p : ℝ × ℝ | inOmega p} \ ⋃ i ∈ S, Gamma (W i)
  let f : α → Set (ℝ × ℝ) := fun a => connectedComponentIn U (pt a)
  have hf_inj : Function.Injective f := fun a b hab => by
    by_contra hne; exact h_inj a b hne hab
  have hf_sub : Set.range f ⊆ Comps U := by
    rintro _ ⟨a, rfl⟩
    exact ⟨pt a, h_mem a, rfl⟩
  calc (Fintype.card α : ℕ∞)
      = (Set.univ : Set α).encard := by rw [Set.encard_univ, ENat.card_eq_coe_fintype_card]
    _ = (f '' Set.univ).encard := (hf_inj.injOn.encard_image).symm
    _ = (Set.range f).encard := by rw [Set.image_univ]
    _ ≤ (Comps U).encard := Set.encard_le_encard hf_sub

end CaseB
end
