import Mathlib
import RootTask.Defs
import RootTask.Sec9Perturb

open scoped Classical BigOperators
open Finset

noncomputable section

namespace Sec9

/-- From `leaf83_v_hull_slopes_strictly_decreasing.proved.lean`, adapted without `valid`. -/
lemma hull_slopes_and_contiguity
    (u1 v1 u2 v2 u3 v3 s2 s t : ℝ)
    (hu12 : u1 < u2) (hu23 : u2 < u3)
    (hsup1 : v1 - s2 * u1 < v2 - s2 * u2)
    (hsup3 : v3 - s2 * u3 < v2 - s2 * u2) :
    (v3 - v2) / (u3 - u2) < s2 ∧
    s2 < (v2 - v1) / (u2 - u1) ∧
    (0 < v1 - s * u1 - t → 0 < v3 - s * u3 - t → 0 < v2 - s * u2 - t) := by
  exact ⟨(div_lt_iff₀ (by linarith)).mpr (by linarith),
         (lt_div_iff₀ (by linarith)).mpr (by linarith),
         fun A B => by nlinarith⟩

/-- Upper-hull vertex predicate on the 10 dual points `Fin 5 × Bool`. -/
def isUpperHullVertex (f : Fin 5 → VFunc) (q : Fin 5 × Bool) : Prop :=
  ∃ s : ℝ, ∀ w : Fin 5 × Bool, w ≠ q →
    (dualPt f w).2 - s * (dualPt f w).1 < (dualPt f q).2 - s * (dualPt f q).1

def H_top (f : Fin 5 → VFunc) : Finset (Fin 5 × Bool) :=
  Finset.univ.filter (isUpperHullVertex f)

def R_int (f : Fin 5 → VFunc) : Finset (Fin 5 × Bool) :=
  Finset.univ \ H_top f

lemma u_min_mem_H_top (f : Fin 5 → VFunc)
    (hf_inj : Function.Injective (fun k : Fin 5 × Bool => (dualPt f k).1)) :
    ∃ p_min : Fin 5 × Bool, p_min ∈ H_top f ∧
      ∀ w : Fin 5 × Bool, (dualPt f p_min).1 ≤ (dualPt f w).1 := by
  obtain ⟨p_min, _, hp_min⟩ := Finset.exists_min_image Finset.univ (fun k => (dualPt f k).1)
    ⟨(0, false), Finset.mem_univ _⟩
  refine ⟨p_min, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, fun w => hp_min w (Finset.mem_univ w)⟩
  let others := Finset.univ.erase p_min
  have hoth_ne : others.Nonempty := by
    have hcard : 1 < (Finset.univ : Finset (Fin 5 × Bool)).card := by decide
    exact Finset.card_pos.mp (by rw [Finset.card_erase_of_mem (Finset.mem_univ _)]; omega)
  let slope (w : Fin 5 × Bool) : ℝ :=
    ((dualPt f w).2 - (dualPt f p_min).2) / ((dualPt f w).1 - (dualPt f p_min).1)
  let s : ℝ := others.sup' hoth_ne slope + 1
  refine ⟨s, fun w hne => ?_⟩
  have hw_mem : w ∈ others := Finset.mem_erase.mpr ⟨hne, Finset.mem_univ w⟩
  have hle_u : (dualPt f p_min).1 ≤ (dualPt f w).1 := hp_min w (Finset.mem_univ w)
  have hlt_u : (dualPt f p_min).1 < (dualPt f w).1 :=
    lt_of_le_of_ne hle_u (fun heq => hne (hf_inj heq.symm))
  have hsup : slope w ≤ others.sup' hoth_ne slope := Finset.le_sup' slope hw_mem
  have hsl : slope w < s := by dsimp [s]; linarith
  have hdu : 0 < (dualPt f w).1 - (dualPt f p_min).1 := sub_pos.mpr hlt_u
  have hmul : (dualPt f w).2 - (dualPt f p_min).2 < s * ((dualPt f w).1 - (dualPt f p_min).1) :=
    (div_lt_iff₀ hdu).mp hsl
  linarith

lemma u_max_mem_H_top (f : Fin 5 → VFunc)
    (hf_inj : Function.Injective (fun k : Fin 5 × Bool => (dualPt f k).1)) :
    ∃ p_max : Fin 5 × Bool, p_max ∈ H_top f ∧
      ∀ w : Fin 5 × Bool, (dualPt f w).1 ≤ (dualPt f p_max).1 := by
  obtain ⟨p_max, _, hp_max⟩ := Finset.exists_max_image Finset.univ (fun k => (dualPt f k).1)
    ⟨(0, false), Finset.mem_univ _⟩
  refine ⟨p_max, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, fun w => hp_max w (Finset.mem_univ w)⟩
  let others := Finset.univ.erase p_max
  have hoth_ne : others.Nonempty := by
    have hcard : 1 < (Finset.univ : Finset (Fin 5 × Bool)).card := by decide
    exact Finset.card_pos.mp (by rw [Finset.card_erase_of_mem (Finset.mem_univ _)]; omega)
  let slope (w : Fin 5 × Bool) : ℝ :=
    ((dualPt f p_max).2 - (dualPt f w).2) / ((dualPt f p_max).1 - (dualPt f w).1)
  let s : ℝ := others.inf' hoth_ne slope - 1
  refine ⟨s, fun w hne => ?_⟩
  have hw_mem : w ∈ others := Finset.mem_erase.mpr ⟨hne, Finset.mem_univ w⟩
  have hle_u : (dualPt f w).1 ≤ (dualPt f p_max).1 := hp_max w (Finset.mem_univ w)
  have hlt_u : (dualPt f w).1 < (dualPt f p_max).1 :=
    lt_of_le_of_ne hle_u (fun heq => hne (hf_inj heq))
  have hinf : others.inf' hoth_ne slope ≤ slope w := Finset.inf'_le slope hw_mem
  have hsl : s < slope w := by dsimp [s]; linarith
  have hdu : 0 < (dualPt f p_max).1 - (dualPt f w).1 := sub_pos.mpr hlt_u
  have hmul : s * ((dualPt f p_max).1 - (dualPt f w).1) < (dualPt f p_max).2 - (dualPt f w).2 :=
    (lt_div_iff₀ hdu).mp hsl
  linarith

/-- Package of ordered upper-hull data and structural theorems for a generic `f : Fin 5 → VFunc`. -/
structure HullData (f : Fin 5 → VFunc) where
  h : ℕ
  hh_ge : 5 ≤ h
  hh_le : h ≤ 10
  q : Fin h → Fin 5 × Bool
  hq_mem : ∀ r, q r ∈ H_top f
  hq_inj : Function.Injective q
  hq_surj : ∀ p ∈ H_top f, ∃ r, q r = p
  hq_mono : StrictMono (fun r => (dualPt f (q r)).1)
  hq_min : ∀ w : Fin 5 × Bool, (dualPt f (q ⟨0, by omega⟩)).1 ≤ (dualPt f w).1
  hq_max : ∀ w : Fin 5 × Bool, (dualPt f w).1 ≤ (dualPt f (q ⟨h - 1, by omega⟩)).1
  μ : Fin (h - 1) → ℝ
  hμ_def : ∀ r : Fin (h - 1),
    μ r = ((dualPt f (q ⟨r.val + 1, by omega⟩)).2 - (dualPt f (q ⟨r.val, by omega⟩)).2) /
          ((dualPt f (q ⟨r.val + 1, by omega⟩)).1 - (dualPt f (q ⟨r.val, by omega⟩)).1)
  hμ_anti : StrictAnti μ
  h_subenv : ∀ p ∈ R_int f, ∃ r : Fin (h - 1),
    (dualPt f (q ⟨r.val, by omega⟩)).1 < (dualPt f p).1 ∧
    (dualPt f p).1 < (dualPt f (q ⟨r.val + 1, by omega⟩)).1 ∧
    (dualPt f p).2 < (dualPt f (q ⟨r.val, by omega⟩)).2 +
      μ r * ((dualPt f p).1 - (dualPt f (q ⟨r.val, by omega⟩)).1)
  h_contiguity : ∀ (s t : ℝ) (r₁ r r₂ : Fin h), r₁ < r → r < r₂ →
    s * (dualPt f (q r₁)).1 + t < (dualPt f (q r₁)).2 →
    s * (dualPt f (q r₂)).1 + t < (dualPt f (q r₂)).2 →
    s * (dualPt f (q r)).1 + t < (dualPt f (q r)).2
  h_lift : ∀ (s t : ℝ) (p : Fin 5 × Bool) (r : Fin (h - 1)),
    p ∈ R_int f →
    (dualPt f (q ⟨r.val, by omega⟩)).1 < (dualPt f p).1 →
    (dualPt f p).1 < (dualPt f (q ⟨r.val + 1, by omega⟩)).1 →
    s * (dualPt f p).1 + t < (dualPt f p).2 →
    s * (dualPt f (q ⟨r.val, by omega⟩)).1 + t < (dualPt f (q ⟨r.val, by omega⟩)).2 ∨
    s * (dualPt f (q ⟨r.val + 1, by omega⟩)).1 + t < (dualPt f (q ⟨r.val + 1, by omega⟩)).2
  h_R_inj : ∀ p₁ ∈ R_int f, ∀ p₂ ∈ R_int f, p₁.1 = p₂.1 → p₁ = p₂
  h_colors_H : ∀ i : Fin 5, ∃ b : Bool, (i, b) ∈ H_top f

def HullData.n {f : Fin 5 → VFunc} (H : HullData f) : ℕ :=
  1 + (Finset.univ.filter (fun r : Fin (H.h - 1) =>
    (H.q ⟨r.val, by have := H.hh_ge; omega⟩).1 ≠
    (H.q ⟨r.val + 1, by have := H.hh_ge; omega⟩).1)).card

def F_top (f : Fin 5 → VFunc) (x : ℝ) : ℝ :=
  Finset.univ.sup' ⟨0, Finset.mem_univ _⟩ (fun i : Fin 5 => (f i).eval x)

lemma F_top_eq_dual_sup (f : Fin 5 → VFunc) (x : ℝ) :
    F_top f x = Finset.univ.sup' ⟨(0, false), Finset.mem_univ _⟩
      (fun w : Fin 5 × Bool => (dualPt f w).1 * x + (dualPt f w).2) := by
  apply le_antisymm
  · rw [F_top, Finset.sup'_le_iff]
    intro i _
    unfold VFunc.eval
    apply max_le
    · exact Finset.le_sup' (fun w : Fin 5 × Bool => (dualPt f w).1 * x + (dualPt f w).2)
        (Finset.mem_univ (i, false))
    · exact Finset.le_sup' (fun w : Fin 5 × Bool => (dualPt f w).1 * x + (dualPt f w).2)
        (Finset.mem_univ (i, true))
  · rw [Finset.sup'_le_iff]
    rintro ⟨i, b⟩ _
    have hi : (f i).eval x ≤ F_top f x :=
      Finset.le_sup' (fun j : Fin 5 => (f j).eval x) (Finset.mem_univ i)
    refine le_trans ?_ hi
    cases b <;> simp only [dualPt, VFunc.eval]
    · exact le_max_left _ _
    · exact le_max_right _ _

/-- Construct `HullData f` and prove all Lemma 9.5 (`v-hull-structure`) properties. -/
theorem build_hullData (f : Fin 5 → VFunc)
    (hf_inj : Function.Injective (fun k : Fin 5 × Bool => (dualPt f k).1))
    (hf_noncol : ∀ p q r : Fin 5 × Bool, p ≠ q → q ≠ r → p ≠ r →
      ((dualPt f q).1 - (dualPt f p).1) * ((dualPt f r).2 - (dualPt f p).2) -
      ((dualPt f q).2 - (dualPt f p).2) * ((dualPt f r).1 - (dualPt f p).1) ≠ 0)
    (hf_dual : ∀ S : Finset (Fin 5), ∃ s t : ℝ, DualRealizes f S s t) :
    Nonempty (HullData f) := by
  let h : ℕ := (H_top f).card
  obtain ⟨p_min, hp_min_mem, hp_min⟩ := u_min_mem_H_top f hf_inj
  obtain ⟨p_max, hp_max_mem, hp_max⟩ := u_max_mem_H_top f hf_inj
  have hmin_ne_max : p_min ≠ p_max := by
    intro heq
    have h10 : ∀ w : Fin 5 × Bool, (dualPt f w).1 = (dualPt f p_min).1 := by
      intro w; exact le_antisymm (by rw [heq]; exact hp_max w) (hp_min w)
    have h01 : ((0 : Fin 5), false) = ((0 : Fin 5), true) :=
      hf_inj (show (dualPt f ((0 : Fin 5), false)).1 = (dualPt f ((0 : Fin 5), true)).1 by
        rw [h10 ((0 : Fin 5), false), h10 ((0 : Fin 5), true)])
    exact Bool.false_ne_true (congrArg Prod.snd h01)
  have hh_ge2 : 2 ≤ h := by
    have hsub : ({p_min, p_max} : Finset (Fin 5 × Bool)) ⊆ H_top f := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> assumption
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_pair hmin_ne_max] at hcard
    exact hcard
  have hh_le : h ≤ 10 := by
    calc h = (H_top f).card := rfl
      _ ≤ (Finset.univ : Finset (Fin 5 × Bool)).card := Finset.card_le_univ _
      _ = 10 := by decide
  let uSet : Finset ℝ := (H_top f).image (fun k => (dualPt f k).1)
  have huSet_card : uSet.card = h :=
    Finset.card_image_of_injective (H_top f) (fun a b hab => hf_inj hab)
  let uEmb : Fin h ↪o ℝ := uSet.orderEmbOfFin huSet_card
  have h_ex_q : ∀ r : Fin h, ∃ p ∈ H_top f, (dualPt f p).1 = uEmb r := by
    intro r
    have hr := Finset.orderEmbOfFin_mem uSet huSet_card r
    rcases Finset.mem_image.mp hr with ⟨p, hp, hpu⟩
    exact ⟨p, hp, hpu⟩
  choose q hq_mem hq_u using h_ex_q
  have hq_mono : StrictMono (fun r => (dualPt f (q r)).1) := by
    intro r₁ r₂ hr
    dsimp only
    rw [hq_u r₁, hq_u r₂]
    exact uEmb.strictMono hr
  have hq_inj : Function.Injective q := by
    intro r₁ r₂ heq
    by_contra hne
    rcases lt_trichotomy r₁ r₂ with hlt | rfl | hgt
    · exact ne_of_lt (hq_mono hlt) (congrArg (fun k => (dualPt f k).1) heq)
    · exact hne rfl
    · exact ne_of_lt (hq_mono hgt) (congrArg (fun k => (dualPt f k).1) heq.symm)
  have hq_surj : ∀ p ∈ H_top f, ∃ r, q r = p := by
    intro p hp
    have hu : (dualPt f p).1 ∈ uSet := Finset.mem_image_of_mem _ hp
    have hrange : (dualPt f p).1 ∈ Set.range uEmb := by
      simpa [uEmb, Finset.range_orderEmbOfFin] using hu
    rcases hrange with ⟨r, hr⟩
    refine ⟨r, hf_inj ?_⟩
    dsimp only
    rw [hq_u r, hr]
  have hq_min_eq : q ⟨0, by omega⟩ = p_min := by
    obtain ⟨r0, hr0⟩ := hq_surj p_min hp_min_mem
    have hle : (⟨0, by omega⟩ : Fin h) ≤ r0 := Nat.zero_le r0.val
    rcases eq_or_lt_of_le hle with h0 | hlt
    · rw [h0, hr0]
    · exfalso
      have h1 := hq_mono hlt
      dsimp only at h1
      have h2 := hp_min (q ⟨0, by omega⟩)
      rw [hr0] at h1
      linarith
  have hq_max_eq : q ⟨h - 1, by omega⟩ = p_max := by
    obtain ⟨rm, hrm⟩ := hq_surj p_max hp_max_mem
    have hle : rm ≤ (⟨h - 1, by omega⟩ : Fin h) := by
      change rm.val ≤ h - 1; omega
    rcases eq_or_lt_of_le hle with hm | hlt
    · rw [← hm, hrm]
    · exfalso
      have h1 := hq_mono hlt
      dsimp only at h1
      have h2 := hp_max (q ⟨h - 1, by omega⟩)
      rw [hrm] at h1
      linarith
  have hq_min : ∀ w : Fin 5 × Bool, (dualPt f (q ⟨0, by omega⟩)).1 ≤ (dualPt f w).1 := by
    rw [hq_min_eq]; exact hp_min
  have hq_max : ∀ w : Fin 5 × Bool, (dualPt f w).1 ≤ (dualPt f (q ⟨h - 1, by omega⟩)).1 := by
    rw [hq_max_eq]; exact hp_max
  let μ : Fin (h - 1) → ℝ := fun r =>
    ((dualPt f (q ⟨r.val + 1, by omega⟩)).2 - (dualPt f (q ⟨r.val, by omega⟩)).2) /
    ((dualPt f (q ⟨r.val + 1, by omega⟩)).1 - (dualPt f (q ⟨r.val, by omega⟩)).1)
  have hμ_def : ∀ r : Fin (h - 1),
      μ r = ((dualPt f (q ⟨r.val + 1, by omega⟩)).2 - (dualPt f (q ⟨r.val, by omega⟩)).2) /
            ((dualPt f (q ⟨r.val + 1, by omega⟩)).1 - (dualPt f (q ⟨r.val, by omega⟩)).1) := fun _ => rfl
  have hμ_step : ∀ r : ℕ, (hr : r + 2 < h) →
      μ ⟨r + 1, by omega⟩ < μ ⟨r, by omega⟩ := by
    intro r hr
    have hmem : q ⟨r + 1, by omega⟩ ∈ H_top f := hq_mem _
    obtain ⟨s₂, hs₂⟩ := (Finset.mem_filter.mp hmem).2
    have hu12 : (dualPt f (q ⟨r, by omega⟩)).1 < (dualPt f (q ⟨r + 1, by omega⟩)).1 :=
      hq_mono (by change r < r + 1; omega)
    have hu23 : (dualPt f (q ⟨r + 1, by omega⟩)).1 < (dualPt f (q ⟨r + 2, by omega⟩)).1 :=
      hq_mono (by change r + 1 < r + 2; omega)
    have hne1 : q ⟨r, by omega⟩ ≠ q ⟨r + 1, by omega⟩ :=
      fun heq => by have := hq_inj heq; simp [Fin.ext_iff] at this
    have hne3 : q ⟨r + 2, by omega⟩ ≠ q ⟨r + 1, by omega⟩ :=
      fun heq => by have := hq_inj heq; simp [Fin.ext_iff] at this
    have h12 := hull_slopes_and_contiguity
      (dualPt f (q ⟨r, by omega⟩)).1 (dualPt f (q ⟨r, by omega⟩)).2
      (dualPt f (q ⟨r + 1, by omega⟩)).1 (dualPt f (q ⟨r + 1, by omega⟩)).2
      (dualPt f (q ⟨r + 2, by omega⟩)).1 (dualPt f (q ⟨r + 2, by omega⟩)).2
      s₂ 0 0 hu12 hu23 (hs₂ _ hne1) (hs₂ _ hne3)
    dsimp [μ]
    exact lt_trans h12.1 h12.2.1
  have hμ_anti : StrictAnti μ := by
    intro r₁ r₂ hr
    have hr2_lt := r₂.isLt
    have hstep : ∀ d : ℕ, ∀ (a : ℕ) (had : a + d < h - 1), d ≥ 1 →
        μ ⟨a + d, had⟩ < μ ⟨a, by omega⟩ := by
      intro d
      induction d with
      | zero => intro _ _ hd; omega
      | succ d ih =>
        intro a had _
        by_cases hd0 : d = 0
        · subst hd0; simpa using hμ_step a (by omega)
        · have h1 : μ ⟨a + d + 1, by omega⟩ < μ ⟨a + d, by omega⟩ :=
            hμ_step (a + d) (by omega)
          have h2 : μ ⟨a + d, by omega⟩ < μ ⟨a, by omega⟩ := ih a (by omega) (by omega)
          have heq_idx : (⟨a + (d + 1), had⟩ : Fin (h - 1)) = ⟨a + d + 1, by omega⟩ := by
            ext; dsimp; omega
          rw [heq_idx]; exact lt_trans h1 h2
    obtain ⟨d, hd⟩ : ∃ d, r₂.val = r₁.val + d ∧ d ≥ 1 :=
      ⟨r₂.val - r₁.val, by omega, by change r₁.val < r₂.val at hr; omega⟩
    have hres := hstep d r₁.val (by omega) hd.2
    have hr2_eq : (⟨r₁.val + d, by omega⟩ : Fin (h - 1)) = r₂ := by
      ext; exact hd.1.symm
    have hr1_eq : (⟨r₁.val, by omega⟩ : Fin (h - 1)) = r₁ := rfl
    have hr2_lt' : r₁.val + d < h - 1 := by omega
    rw [show (⟨r₁.val + d, hr2_lt'⟩ : Fin (h - 1)) = r₂ from hr2_eq, hr1_eq] at hres
    exact hres
  -- Helper slope bounds for `r₁ < r` and `r < r₂`
  have h_dv_ge : ∀ (a b : Fin h), a < b →
      μ ⟨b.val - 1, by omega⟩ * ((dualPt f (q b)).1 - (dualPt f (q a)).1) ≤
      (dualPt f (q b)).2 - (dualPt f (q a)).2 := by
    intro a b hab
    have ha_lt := a.isLt; have hb_lt := b.isLt
    have h_ind : ∀ d : ℕ, ∀ (a0 : ℕ) (ha0 : a0 + d < h) (hd : 1 ≤ d),
        μ ⟨a0 + d - 1, by omega⟩ *
          ((dualPt f (q ⟨a0 + d, ha0⟩)).1 - (dualPt f (q ⟨a0, by omega⟩)).1) ≤
        (dualPt f (q ⟨a0 + d, ha0⟩)).2 - (dualPt f (q ⟨a0, by omega⟩)).2 := by
      intro d
      induction d with
      | zero => intro _ _ hd; omega
      | succ d ih =>
        intro a0 ha0 _
        by_cases hd0 : d = 0
        · subst hd0
          have hdu : 0 < (dualPt f (q ⟨a0 + 1, ha0⟩)).1 - (dualPt f (q ⟨a0, by omega⟩)).1 :=
            sub_pos.mpr (hq_mono (by change a0 < a0 + 1; omega))
          have hm : μ ⟨a0, by omega⟩ =
              ((dualPt f (q ⟨a0 + 1, ha0⟩)).2 - (dualPt f (q ⟨a0, by omega⟩)).2) /
              ((dualPt f (q ⟨a0 + 1, ha0⟩)).1 - (dualPt f (q ⟨a0, by omega⟩)).1) := rfl
          have hmul := (div_eq_iff (ne_of_gt hdu)).mp hm.symm
          have hid : (⟨a0 + 1 - 1, by omega⟩ : Fin (h - 1)) = ⟨a0, by omega⟩ := by ext; simp
          rw [hid]; linarith
        · have ih' := ih a0 (by omega) (by omega)
          have h_last : μ ⟨a0 + d, by omega⟩ *
              ((dualPt f (q ⟨a0 + d + 1, ha0⟩)).1 - (dualPt f (q ⟨a0 + d, by omega⟩)).1) =
              (dualPt f (q ⟨a0 + d + 1, ha0⟩)).2 - (dualPt f (q ⟨a0 + d, by omega⟩)).2 := by
            have hdu : 0 < (dualPt f (q ⟨a0 + d + 1, ha0⟩)).1 - (dualPt f (q ⟨a0 + d, by omega⟩)).1 :=
              sub_pos.mpr (hq_mono (by change a0 + d < a0 + d + 1; omega))
            have hm : μ ⟨a0 + d, by omega⟩ =
                ((dualPt f (q ⟨a0 + d + 1, ha0⟩)).2 - (dualPt f (q ⟨a0 + d, by omega⟩)).2) /
                ((dualPt f (q ⟨a0 + d + 1, ha0⟩)).1 - (dualPt f (q ⟨a0 + d, by omega⟩)).1) := rfl
            exact ((div_eq_iff (ne_of_gt hdu)).mp hm.symm).symm
          have hanti : μ ⟨a0 + d, by omega⟩ ≤ μ ⟨a0 + d - 1, by omega⟩ :=
            le_of_lt (hμ_anti (by change a0 + d - 1 < a0 + d; omega))
          have hdu1 : 0 ≤ (dualPt f (q ⟨a0 + d, by omega⟩)).1 - (dualPt f (q ⟨a0, by omega⟩)).1 :=
            sub_nonneg.mpr (le_of_lt (hq_mono (by change a0 < a0 + d; omega)))
          have h1 : μ ⟨a0 + d, by omega⟩ *
              ((dualPt f (q ⟨a0 + d, by omega⟩)).1 - (dualPt f (q ⟨a0, by omega⟩)).1) ≤
              μ ⟨a0 + d - 1, by omega⟩ *
              ((dualPt f (q ⟨a0 + d, by omega⟩)).1 - (dualPt f (q ⟨a0, by omega⟩)).1) :=
            mul_le_mul_of_nonneg_right hanti hdu1
          have hid : (⟨a0 + (d + 1) - 1, by omega⟩ : Fin (h - 1)) = ⟨a0 + d, by omega⟩ := by
            ext; simp
          have hqeq : (⟨a0 + (d + 1), ha0⟩ : Fin h) = ⟨a0 + d + 1, ha0⟩ := by ext; dsimp; omega
          rw [hid, hqeq]
          linarith
    have hres := h_ind (b.val - a.val) a.val (by change a.val < b.val at hab; omega)
      (by change a.val < b.val at hab; omega)
    have hb_eq : (⟨a.val + (b.val - a.val), by omega⟩ : Fin h) = b := by
      ext; dsimp; change a.val < b.val at hab; omega
    have ha_eq : (⟨a.val, by omega⟩ : Fin h) = a := rfl
    have hidx : (⟨a.val + (b.val - a.val) - 1, by omega⟩ : Fin (h - 1)) = ⟨b.val - 1, by omega⟩ := by
      ext; dsimp; change a.val < b.val at hab; omega
    rw [hb_eq, ha_eq, hidx] at hres
    exact hres
  have h_dv_le : ∀ (a b : Fin h) (hab : a < b),
      (dualPt f (q b)).2 - (dualPt f (q a)).2 ≤
      μ ⟨a.val, have := b.isLt; have : a.val < b.val := hab; by omega⟩ *
        ((dualPt f (q b)).1 - (dualPt f (q a)).1) := by
    intro a b hab
    have ha_lt := a.isLt; have hb_lt := b.isLt
    have h_ind : ∀ d : ℕ, ∀ (a0 : ℕ) (ha0 : a0 + d < h) (hd : 1 ≤ d),
        (dualPt f (q ⟨a0 + d, ha0⟩)).2 - (dualPt f (q ⟨a0, by omega⟩)).2 ≤
        μ ⟨a0, by omega⟩ *
          ((dualPt f (q ⟨a0 + d, ha0⟩)).1 - (dualPt f (q ⟨a0, by omega⟩)).1) := by
      intro d
      induction d with
      | zero => intro _ _ hd; omega
      | succ d ih =>
        intro a0 ha0 _
        by_cases hd0 : d = 0
        · subst hd0
          have hdu : 0 < (dualPt f (q ⟨a0 + 1, ha0⟩)).1 - (dualPt f (q ⟨a0, by omega⟩)).1 :=
            sub_pos.mpr (hq_mono (by change a0 < a0 + 1; omega))
          have hm : μ ⟨a0, by omega⟩ =
              ((dualPt f (q ⟨a0 + 1, ha0⟩)).2 - (dualPt f (q ⟨a0, by omega⟩)).2) /
              ((dualPt f (q ⟨a0 + 1, ha0⟩)).1 - (dualPt f (q ⟨a0, by omega⟩)).1) := rfl
          have hmul := (div_eq_iff (ne_of_gt hdu)).mp hm.symm
          linarith
        · have ih' := ih a0 (by omega) (by omega)
          have h_last : μ ⟨a0 + d, by omega⟩ *
              ((dualPt f (q ⟨a0 + d + 1, ha0⟩)).1 - (dualPt f (q ⟨a0 + d, by omega⟩)).1) =
              (dualPt f (q ⟨a0 + d + 1, ha0⟩)).2 - (dualPt f (q ⟨a0 + d, by omega⟩)).2 := by
            have hdu : 0 < (dualPt f (q ⟨a0 + d + 1, ha0⟩)).1 - (dualPt f (q ⟨a0 + d, by omega⟩)).1 :=
              sub_pos.mpr (hq_mono (by change a0 + d < a0 + d + 1; omega))
            have hm : μ ⟨a0 + d, by omega⟩ =
                ((dualPt f (q ⟨a0 + d + 1, ha0⟩)).2 - (dualPt f (q ⟨a0 + d, by omega⟩)).2) /
                ((dualPt f (q ⟨a0 + d + 1, ha0⟩)).1 - (dualPt f (q ⟨a0 + d, by omega⟩)).1) := rfl
            exact ((div_eq_iff (ne_of_gt hdu)).mp hm.symm).symm
          have hanti : μ ⟨a0 + d, by omega⟩ ≤ μ ⟨a0, by omega⟩ :=
            le_of_lt (hμ_anti (by change a0 < a0 + d; omega))
          have hdu2 : 0 ≤ (dualPt f (q ⟨a0 + d + 1, ha0⟩)).1 - (dualPt f (q ⟨a0 + d, by omega⟩)).1 :=
            sub_nonneg.mpr (le_of_lt (hq_mono (by change a0 + d < a0 + d + 1; omega)))
          have h1 : μ ⟨a0 + d, by omega⟩ *
              ((dualPt f (q ⟨a0 + d + 1, ha0⟩)).1 - (dualPt f (q ⟨a0 + d, by omega⟩)).1) ≤
              μ ⟨a0, by omega⟩ *
              ((dualPt f (q ⟨a0 + d + 1, ha0⟩)).1 - (dualPt f (q ⟨a0 + d, by omega⟩)).1) :=
            mul_le_mul_of_nonneg_right hanti hdu2
          have hqeq : (⟨a0 + (d + 1), ha0⟩ : Fin h) = ⟨a0 + d + 1, ha0⟩ := by ext; dsimp; omega
          rw [hqeq]
          linarith
    have hres := h_ind (b.val - a.val) a.val (by change a.val < b.val at hab; omega)
      (by change a.val < b.val at hab; omega)
    have hb_eq : (⟨a.val + (b.val - a.val), by omega⟩ : Fin h) = b := by
      ext; dsimp; change a.val < b.val at hab; omega
    have ha_eq : (⟨a.val, by omega⟩ : Fin h) = a := rfl
    rw [hb_eq, ha_eq] at hres
    exact hres
  have h_contiguity : ∀ (s t : ℝ) (r₁ r r₂ : Fin h), r₁ < r → r < r₂ →
      s * (dualPt f (q r₁)).1 + t < (dualPt f (q r₁)).2 →
      s * (dualPt f (q r₂)).1 + t < (dualPt f (q r₂)).2 →
      s * (dualPt f (q r)).1 + t < (dualPt f (q r)).2 := by
    intro s t r₁ r r₂ hr1 hr2 h1 h2
    have hu1 : (dualPt f (q r₁)).1 < (dualPt f (q r)).1 := hq_mono hr1
    have hu2 : (dualPt f (q r)).1 < (dualPt f (q r₂)).1 := hq_mono hr2
    have hge := h_dv_ge r₁ r hr1
    have hle := h_dv_le r r₂ hr2
    have hr_lt : (⟨r.val, by omega⟩ : Fin (h - 1)) < ⟨r.val - 1, by omega⟩ → False := by
      intro hlt; change r.val < r.val - 1 at hlt; omega
    have hmu : μ ⟨r.val, by omega⟩ < μ ⟨r.val - 1, by omega⟩ :=
      hμ_anti (by change r.val - 1 < r.val; change r₁.val < r.val at hr1; omega)
    have h12_pos : 0 < (dualPt f (q r)).1 - (dualPt f (q r₁)).1 := sub_pos.mpr hu1
    have h23_pos : 0 < (dualPt f (q r₂)).1 - (dualPt f (q r)).1 := sub_pos.mpr hu2
    have hslope1 : μ ⟨r.val - 1, by omega⟩ ≤
        ((dualPt f (q r)).2 - (dualPt f (q r₁)).2) / ((dualPt f (q r)).1 - (dualPt f (q r₁)).1) :=
      (le_div_iff₀ h12_pos).mpr hge
    have hslope2 : ((dualPt f (q r₂)).2 - (dualPt f (q r)).2) / ((dualPt f (q r₂)).1 - (dualPt f (q r)).1) ≤
        μ ⟨r.val, by omega⟩ :=
      (div_le_iff₀ h23_pos).mpr hle
    have hslope_lt : ((dualPt f (q r₂)).2 - (dualPt f (q r)).2) / ((dualPt f (q r₂)).1 - (dualPt f (q r)).1) <
        ((dualPt f (q r)).2 - (dualPt f (q r₁)).2) / ((dualPt f (q r)).1 - (dualPt f (q r₁)).1) :=
      lt_of_le_of_lt hslope2 (lt_of_lt_of_le hmu hslope1)
    have hcross : ((dualPt f (q r₂)).2 - (dualPt f (q r)).2) * ((dualPt f (q r)).1 - (dualPt f (q r₁)).1) <
        ((dualPt f (q r)).2 - (dualPt f (q r₁)).2) * ((dualPt f (q r₂)).1 - (dualPt f (q r)).1) :=
      (div_lt_div_iff₀ h23_pos h12_pos).mp hslope_lt
    nlinarith
  -- Sub-envelope inequality `v-hull-structure(iii)`
  have h_subenv : ∀ p ∈ R_int f, ∃ r : Fin (h - 1),
      (dualPt f (q ⟨r.val, by omega⟩)).1 < (dualPt f p).1 ∧
      (dualPt f p).1 < (dualPt f (q ⟨r.val + 1, by omega⟩)).1 ∧
      (dualPt f p).2 < (dualPt f (q ⟨r.val, by omega⟩)).2 +
        μ r * ((dualPt f p).1 - (dualPt f (q ⟨r.val, by omega⟩)).1) := by
    intro p hp
    have hp_not_H : p ∉ H_top f := (Finset.mem_sdiff.mp hp).2
    have hp_ne_0 : p ≠ q ⟨0, by omega⟩ := fun h => hp_not_H (h ▸ hq_mem _)
    have hp_ne_last : p ≠ q ⟨h - 1, by omega⟩ := fun h => hp_not_H (h ▸ hq_mem _)
    have hu_gt0 : (dualPt f (q ⟨0, by omega⟩)).1 < (dualPt f p).1 :=
      lt_of_le_of_ne (hq_min p) (fun heq => hp_ne_0 (hf_inj heq.symm))
    have hu_lt_last : (dualPt f p).1 < (dualPt f (q ⟨h - 1, by omega⟩)).1 :=
      lt_of_le_of_ne (hq_max p) (fun heq => hp_ne_last (hf_inj heq))
    let S_lt : Finset (Fin h) := Finset.univ.filter (fun j => (dualPt f (q j)).1 < (dualPt f p).1)
    have hS_ne : S_lt.Nonempty := ⟨⟨0, by omega⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hu_gt0⟩⟩
    let r0 : Fin h := S_lt.max' hS_ne
    have hr0_lt : (dualPt f (q r0)).1 < (dualPt f p).1 :=
      (Finset.mem_filter.mp (Finset.max'_mem S_lt hS_ne)).2
    have hr0_isLt := r0.isLt
    have hr0_not_last : r0.val < h - 1 := by
      by_contra hge
      have h_eq : r0 = ⟨h - 1, by omega⟩ := by ext; dsimp; omega
      rw [h_eq] at hr0_lt
      linarith
    let r : Fin (h - 1) := ⟨r0.val, hr0_not_last⟩
    have hr1_not_in : (⟨r.val + 1, by omega⟩ : Fin h) ∉ S_lt := by
      intro hmem
      have hle := Finset.le_max' S_lt ⟨r.val + 1, by omega⟩ hmem
      change r.val + 1 ≤ r0.val at hle
      dsimp [r] at hle
      omega
    have hu_le_r1 : (dualPt f p).1 ≤ (dualPt f (q ⟨r.val + 1, by omega⟩)).1 := by
      by_contra hlt
      exact hr1_not_in (Finset.mem_filter.mpr ⟨Finset.mem_univ _, not_le.mp hlt⟩)
    have hp_ne_r1 : p ≠ q ⟨r.val + 1, by omega⟩ := fun h => hp_not_H (h ▸ hq_mem _)
    have hu_lt_r1 : (dualPt f p).1 < (dualPt f (q ⟨r.val + 1, by omega⟩)).1 :=
      lt_of_le_of_ne hu_le_r1 (fun heq => hp_ne_r1 (hf_inj heq))
    refine ⟨r, hr0_lt, hu_lt_r1, ?_⟩
    by_contra hge
    replace hge : (dualPt f (q ⟨r.val, by omega⟩)).2 +
        μ r * ((dualPt f p).1 - (dualPt f (q ⟨r.val, by omega⟩)).1) ≤ (dualPt f p).2 :=
      not_lt.mp hge
    have hgt : (dualPt f (q ⟨r.val, by omega⟩)).2 +
        μ r * ((dualPt f p).1 - (dualPt f (q ⟨r.val, by omega⟩)).1) < (dualPt f p).2 := by
      refine lt_of_le_of_ne hge (fun heq => ?_)
      have hp_ne_r : p ≠ q ⟨r.val, by omega⟩ := fun h => hp_not_H (h ▸ hq_mem _)
      have hr_ne_r1 : q ⟨r.val, by omega⟩ ≠ q ⟨r.val + 1, by omega⟩ :=
        fun h => by have := hq_inj h; simp [Fin.ext_iff] at this
      have hdet := hf_noncol (q ⟨r.val, by omega⟩) p (q ⟨r.val + 1, by omega⟩)
        hp_ne_r.symm hp_ne_r1 hr_ne_r1
      apply hdet
      have hdu_r : 0 < (dualPt f (q ⟨r.val + 1, by omega⟩)).1 - (dualPt f (q ⟨r.val, by omega⟩)).1 :=
        sub_pos.mpr (hq_mono (by change r.val < r.val + 1; omega))
      have hm_mul : μ r * ((dualPt f (q ⟨r.val + 1, by omega⟩)).1 - (dualPt f (q ⟨r.val, by omega⟩)).1) =
          (dualPt f (q ⟨r.val + 1, by omega⟩)).2 - (dualPt f (q ⟨r.val, by omega⟩)).2 := by
        rw [hμ_def r]
        field_simp [ne_of_gt hdu_r]
      have hsub1 : (dualPt f p).2 - (dualPt f (q ⟨r.val, by omega⟩)).2 =
          μ r * ((dualPt f p).1 - (dualPt f (q ⟨r.val, by omega⟩)).1) := by linarith
      calc ((dualPt f p).1 - (dualPt f (q ⟨r.val, by omega⟩)).1) *
              ((dualPt f (q ⟨r.val + 1, by omega⟩)).2 - (dualPt f (q ⟨r.val, by omega⟩)).2) -
           ((dualPt f p).2 - (dualPt f (q ⟨r.val, by omega⟩)).2) *
              ((dualPt f (q ⟨r.val + 1, by omega⟩)).1 - (dualPt f (q ⟨r.val, by omega⟩)).1)
          = ((dualPt f p).1 - (dualPt f (q ⟨r.val, by omega⟩)).1) *
              (μ r * ((dualPt f (q ⟨r.val + 1, by omega⟩)).1 - (dualPt f (q ⟨r.val, by omega⟩)).1)) -
            (μ r * ((dualPt f p).1 - (dualPt f (q ⟨r.val, by omega⟩)).1)) *
              ((dualPt f (q ⟨r.val + 1, by omega⟩)).1 - (dualPt f (q ⟨r.val, by omega⟩)).1) := by
              rw [hm_mul, hsub1]
        _ = 0 := by ring
    let g (w : Fin 5 × Bool) : ℝ := (dualPt f w).2 - μ r * (dualPt f w).1
    have hg_step : ∀ j : Fin (h - 1),
        g (q ⟨j.val + 1, by omega⟩) - g (q ⟨j.val, by omega⟩) =
        (μ j - μ r) * ((dualPt f (q ⟨j.val + 1, by omega⟩)).1 - (dualPt f (q ⟨j.val, by omega⟩)).1) := by
      intro j
      have hdu : 0 < (dualPt f (q ⟨j.val + 1, by omega⟩)).1 - (dualPt f (q ⟨j.val, by omega⟩)).1 :=
        sub_pos.mpr (hq_mono (by change j.val < j.val + 1; omega))
      have hm_mul : μ j * ((dualPt f (q ⟨j.val + 1, by omega⟩)).1 - (dualPt f (q ⟨j.val, by omega⟩)).1) =
          (dualPt f (q ⟨j.val + 1, by omega⟩)).2 - (dualPt f (q ⟨j.val, by omega⟩)).2 := by
        rw [hμ_def j]; field_simp [ne_of_gt hdu]
      dsimp [g]
      linarith
    have hg_hull : ∀ j : Fin h, g (q j) ≤ g (q ⟨r.val, by omega⟩) := by
      intro j
      have hj_lt := j.isLt
      have h_left : ∀ d : ℕ, ∀ (k : ℕ) (hk : k + d = r.val),
          g (q ⟨k, by omega⟩) ≤ g (q ⟨r.val, by omega⟩) := by
        intro d
        induction d with
        | zero =>
          intro k hk
          have hkeq : (⟨k, by omega⟩ : Fin h) = ⟨r.val, by omega⟩ := by ext; dsimp; omega
          rw [hkeq]
        | succ d ih =>
          intro k hk
          have hk1 : k + 1 + d = r.val := by omega
          have ih' := ih (k + 1) hk1
          have hs := hg_step ⟨k, by omega⟩
          have hanti : μ r < μ ⟨k, by omega⟩ := hμ_anti (by change k < r.val; omega)
          have hdu : 0 < (dualPt f (q ⟨k + 1, by omega⟩)).1 - (dualPt f (q ⟨k, by omega⟩)).1 :=
            sub_pos.mpr (hq_mono (by change k < k + 1; omega))
          have hle : g (q ⟨k, by omega⟩) ≤ g (q ⟨k + 1, by omega⟩) := by nlinarith
          exact le_trans hle ih'
      have h_right : ∀ d : ℕ, (hd : r.val + d < h) →
          g (q ⟨r.val + d, hd⟩) ≤ g (q ⟨r.val, by omega⟩) := by
        intro d
        induction d with
        | zero => intro _; exact le_rfl
        | succ d ih =>
          intro hd
          have ih' := ih (by omega)
          have hs := hg_step ⟨r.val + d, by omega⟩
          have hanti : μ ⟨r.val + d, by omega⟩ ≤ μ r := by
            by_cases hd0 : d = 0
            · subst hd0; exact le_rfl
            · exact le_of_lt (hμ_anti (by change r.val < r.val + d; omega))
          have hdu : 0 < (dualPt f (q ⟨r.val + d + 1, hd⟩)).1 - (dualPt f (q ⟨r.val + d, by omega⟩)).1 :=
            sub_pos.mpr (hq_mono (by change r.val + d < r.val + d + 1; omega))
          have hle : g (q ⟨r.val + d + 1, hd⟩) ≤ g (q ⟨r.val + d, by omega⟩) := by nlinarith
          have hqeq : (⟨r.val + (d + 1), hd⟩ : Fin h) = ⟨r.val + d + 1, hd⟩ := by ext; dsimp; omega
          rw [hqeq]; exact le_trans hle ih'
      rcases le_total j.val r.val with hjr | hrj
      · exact h_left (r.val - j.val) j.val (by omega)
      · have hres := h_right (j.val - r.val) (by omega)
        have hjeq : (⟨r.val + (j.val - r.val), by omega⟩ : Fin h) = j := by ext; dsimp; omega
        rw [hjeq] at hres
        exact hres
    have hg_lt_p : g (q ⟨r.val, by omega⟩) < g p := by dsimp [g]; linarith
    let M1 : ℝ := Finset.univ.sup' ⟨p, Finset.mem_univ p⟩ g
    let A_max : Finset (Fin 5 × Bool) := Finset.univ.filter (fun w => g w = M1)
    have hp_le_M1 : g p ≤ M1 := Finset.le_sup' g (Finset.mem_univ p)
    have hA_disj : ∀ w ∈ A_max, w ∉ H_top f := by
      intro w hw hwH
      obtain ⟨j, rfl⟩ := hq_surj w hwH
      have hw_eq : g (q j) = M1 := (Finset.mem_filter.mp hw).2
      have := hg_hull j
      linarith
    have hA_ne : A_max.Nonempty := by
      obtain ⟨w1, _, hw1⟩ := Finset.exists_max_image Finset.univ g ⟨p, Finset.mem_univ p⟩
      refine ⟨w1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_antisymm (Finset.le_sup' g (Finset.mem_univ w1)) ?_⟩⟩
      rw [Finset.sup'_le_iff]
      intro w _
      exact hw1 w (Finset.mem_univ w)
    obtain ⟨w0, hw0_mem, hw0_min⟩ := Finset.exists_min_image A_max (fun w => (dualPt f w).1) hA_ne
    have hw0_eq : g w0 = M1 := (Finset.mem_filter.mp hw0_mem).2
    let nonMax := Finset.univ \ A_max
    have hnonMax_ne : nonMax.Nonempty :=
      ⟨q ⟨0, by omega⟩, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun h => hA_disj _ h (hq_mem _)⟩⟩
    let η : ℝ := nonMax.inf' hnonMax_ne (fun w => M1 - g w)
    have hη_pos : 0 < η := by
      rw [Finset.lt_inf'_iff]
      intro w hw
      have hw' := Finset.mem_sdiff.mp hw
      have hle : g w ≤ M1 := Finset.le_sup' g (Finset.mem_univ w)
      have hne : g w ≠ M1 := fun heq => hw'.2 (Finset.mem_filter.mpr ⟨Finset.mem_univ w, heq⟩)
      exact sub_pos.mpr (lt_of_le_of_ne hle hne)
    let D0 : ℝ := 1 + Finset.univ.sup' ⟨w0, Finset.mem_univ w0⟩ (fun w => |(dualPt f w).1 - (dualPt f w0).1|)
    have hD0_ge : 1 ≤ D0 := by
      have h0 : 0 ≤ |(dualPt f w0).1 - (dualPt f w0).1| := abs_nonneg _
      have hle : |(dualPt f w0).1 - (dualPt f w0).1| ≤
          Finset.univ.sup' ⟨w0, Finset.mem_univ w0⟩ (fun w => |(dualPt f w).1 - (dualPt f w0).1|) :=
        Finset.le_sup' (fun w => |(dualPt f w).1 - (dualPt f w0).1|) (Finset.mem_univ w0)
      dsimp [D0]; linarith
    let s_star : ℝ := μ r + η / (2 * D0)
    have hw0_H : w0 ∈ H_top f := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨s_star, fun w hne => ?_⟩⟩
      have hdiff : ((dualPt f w0).2 - s_star * (dualPt f w0).1) -
          ((dualPt f w).2 - s_star * (dualPt f w).1) =
          (g w0 - g w) + (η / (2 * D0)) * ((dualPt f w).1 - (dualPt f w0).1) := by
        dsimp [g, s_star]; ring
      by_cases hwA : w ∈ A_max
      · have hw_eq : g w = M1 := (Finset.mem_filter.mp hwA).2
        have hlt_u : (dualPt f w0).1 < (dualPt f w).1 :=
          lt_of_le_of_ne (hw0_min w hwA) (fun heq => hne (hf_inj heq.symm))
        have hpos_term : 0 < (η / (2 * D0)) * ((dualPt f w).1 - (dualPt f w0).1) :=
          mul_pos (div_pos hη_pos (by linarith)) (sub_pos.mpr hlt_u)
        linarith
      · have hw_non : w ∈ nonMax := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hwA⟩
        have hη_le : η ≤ M1 - g w := Finset.inf'_le (fun z => M1 - g z) hw_non
        have h_abs : |(dualPt f w).1 - (dualPt f w0).1| < D0 := by
          have hle : |(dualPt f w).1 - (dualPt f w0).1| ≤
              Finset.univ.sup' ⟨w0, Finset.mem_univ w0⟩ (fun z => |(dualPt f z).1 - (dualPt f w0).1|) :=
            Finset.le_sup' (fun z => |(dualPt f z).1 - (dualPt f w0).1|) (Finset.mem_univ w)
          dsimp [D0]; linarith
        have h_bound : -(η / 2) < (η / (2 * D0)) * ((dualPt f w).1 - (dualPt f w0).1) := by
          have hD0_pos : 0 < D0 := by linarith
          have h1 : (η / (2 * D0)) * (-D0) < (η / (2 * D0)) * ((dualPt f w).1 - (dualPt f w0).1) :=
            mul_lt_mul_of_pos_left (abs_lt.mp h_abs).1 (div_pos hη_pos (by linarith))
          have eq1 : (η / (2 * D0)) * (-D0) = -(η / 2) := by
            field_simp [ne_of_gt hD0_pos]
          linarith
        linarith
    exact hA_disj w0 hw0_mem hw0_H
  -- Interior witness lift
  have h_lift : ∀ (s t : ℝ) (p : Fin 5 × Bool) (r : Fin (h - 1)),
      p ∈ R_int f →
      (dualPt f (q ⟨r.val, by omega⟩)).1 < (dualPt f p).1 →
      (dualPt f p).1 < (dualPt f (q ⟨r.val + 1, by omega⟩)).1 →
      s * (dualPt f p).1 + t < (dualPt f p).2 →
      s * (dualPt f (q ⟨r.val, by omega⟩)).1 + t < (dualPt f (q ⟨r.val, by omega⟩)).2 ∨
      s * (dualPt f (q ⟨r.val + 1, by omega⟩)).1 + t < (dualPt f (q ⟨r.val + 1, by omega⟩)).2 := by
    intro s t p r hp hu1 hu2 hUp
    obtain ⟨r', hr'1, hr'2, hr'v⟩ := h_subenv p hp
    have hr_eq : r' = r := by
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have h_le : r'.val + 1 ≤ r.val := hlt
        have hmono : (dualPt f (q ⟨r'.val + 1, by omega⟩)).1 ≤ (dualPt f (q ⟨r.val, by omega⟩)).1 := by
          by_cases heq : r'.val + 1 = r.val
          · have : (⟨r'.val + 1, by omega⟩ : Fin h) = ⟨r.val, by omega⟩ := by ext; exact heq
            rw [this]
          · exact le_of_lt (hq_mono (by change r'.val + 1 < r.val; omega))
        linarith
      · have h_le : r.val + 1 ≤ r'.val := hgt
        have hmono : (dualPt f (q ⟨r.val + 1, by omega⟩)).1 ≤ (dualPt f (q ⟨r'.val, by omega⟩)).1 := by
          by_cases heq : r.val + 1 = r'.val
          · have : (⟨r.val + 1, by omega⟩ : Fin h) = ⟨r'.val, by omega⟩ := by ext; exact heq
            rw [this]
          · exact le_of_lt (hq_mono (by change r.val + 1 < r'.val; omega))
        linarith
    subst hr_eq
    have hdu : 0 < (dualPt f (q ⟨r'.val + 1, by omega⟩)).1 - (dualPt f (q ⟨r'.val, by omega⟩)).1 :=
      sub_pos.mpr (hq_mono (by change r'.val < r'.val + 1; omega))
    have hm_mul : μ r' * ((dualPt f (q ⟨r'.val + 1, by omega⟩)).1 - (dualPt f (q ⟨r'.val, by omega⟩)).1) =
        (dualPt f (q ⟨r'.val + 1, by omega⟩)).2 - (dualPt f (q ⟨r'.val, by omega⟩)).2 := by
      rw [hμ_def r']; field_simp [ne_of_gt hdu]
    by_contra hboth
    push Not at hboth
    have hle1 : (dualPt f (q ⟨r'.val, by omega⟩)).2 ≤ s * (dualPt f (q ⟨r'.val, by omega⟩)).1 + t := hboth.1
    have hle2 : (dualPt f (q ⟨r'.val + 1, by omega⟩)).2 ≤ s * (dualPt f (q ⟨r'.val + 1, by omega⟩)).1 + t := hboth.2
    have h1 : 0 < ((dualPt f p).2 - s * (dualPt f p).1 - t) *
        ((dualPt f (q ⟨r'.val + 1, by omega⟩)).1 - (dualPt f (q ⟨r'.val, by omega⟩)).1) :=
      mul_pos (by linarith) hdu
    nlinarith
  -- Every color `i : Fin 5` has at least one point in `H_top f`
  have h_colors_H : ∀ i : Fin 5, ∃ b : Bool, (i, b) ∈ H_top f := by
    intro i
    obtain ⟨s, t, _, hS⟩ := hf_dual {i}
    obtain ⟨b0, hb0⟩ := (hS i).mp (Finset.mem_singleton_self i)
    by_cases hH : (i, b0) ∈ H_top f
    · exact ⟨b0, hH⟩
    · have hpR : (i, b0) ∈ R_int f := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hH⟩
      obtain ⟨r, hu1, hu2, _⟩ := h_subenv (i, b0) hpR
      rcases h_lift s t (i, b0) r hpR hu1 hu2 hb0 with hqL | hqR
      · have hiL : (q ⟨r.val, by omega⟩).1 ∈ ({i} : Finset (Fin 5)) :=
          (hS (q ⟨r.val, by omega⟩).1).mpr ⟨(q ⟨r.val, by omega⟩).2, by simpa using hqL⟩
        rw [Finset.mem_singleton] at hiL
        refine ⟨(q ⟨r.val, by omega⟩).2, ?_⟩
        rw [← hiL]
        exact hq_mem _
      · have hiR : (q ⟨r.val + 1, by omega⟩).1 ∈ ({i} : Finset (Fin 5)) :=
          (hS (q ⟨r.val + 1, by omega⟩).1).mpr ⟨(q ⟨r.val + 1, by omega⟩).2, by simpa using hqR⟩
        rw [Finset.mem_singleton] at hiR
        refine ⟨(q ⟨r.val + 1, by omega⟩).2, ?_⟩
        rw [← hiR]
        exact hq_mem _
  have hh_ge : 5 ≤ h := by
    have hsub : (Finset.univ : Finset (Fin 5)) ⊆ (H_top f).image Prod.fst := by
      intro i _
      obtain ⟨b, hb⟩ := h_colors_H i
      exact Finset.mem_image.mpr ⟨(i, b), hb, rfl⟩
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.card_image_le (f := Prod.fst) (s := H_top f)
    simp only [Finset.card_fin] at h1
    exact le_trans h1 h2
  have h_R_inj : ∀ p₁ ∈ R_int f, ∀ p₂ ∈ R_int f, p₁.1 = p₂.1 → p₁ = p₂ := by
    rintro ⟨i₁, b₁⟩ hp1 ⟨i₂, b₂⟩ hp2 heq
    dsimp at heq; subst heq
    obtain ⟨bH, hbH⟩ := h_colors_H i₁
    have hb1_not : (i₁, b₁) ∉ H_top f := (Finset.mem_sdiff.mp hp1).2
    have hb2_not : (i₁, b₂) ∉ H_top f := (Finset.mem_sdiff.mp hp2).2
    cases b₁ <;> cases b₂ <;> cases bH <;> first | rfl | exact False.elim (hb1_not hbH) | exact False.elim (hb2_not hbH)
  exact ⟨⟨h, hh_ge, hh_le, q, hq_mem, hq_inj, hq_surj, hq_mono, hq_min, hq_max,
    μ, hμ_def, hμ_anti, h_subenv, h_contiguity, h_lift, h_R_inj, h_colors_H⟩⟩

/-- Strict upper-hull evaluation structure for `F_top f x`:
    interior points `R_int f` never achieve `F_top f x`, and on `H_top f`, ties between two
    distinct hull points occur only at `-μ r` where ONLY `q r` and `q (r+1)` achieve `F_top f x`. -/
lemma F_top_strict_int {f : Fin 5 → VFunc} (H : HullData f) (x : ℝ)
    (p : Fin 5 × Bool) (hp : p ∈ R_int f) :
    (dualPt f p).1 * x + (dualPt f p).2 < F_top f x := by
  obtain ⟨r, hu1, hu2, hv⟩ := H.h_subenv p hp
  have hdu : 0 < (dualPt f (H.q ⟨r.val + 1, by have := H.hh_ge; omega⟩)).1 -
      (dualPt f (H.q ⟨r.val, by have := H.hh_ge; omega⟩)).1 :=
    sub_pos.mpr (H.hq_mono (by change r.val < r.val + 1; omega))
  have hm_mul : H.μ r * ((dualPt f (H.q ⟨r.val + 1, by have := H.hh_ge; omega⟩)).1 -
      (dualPt f (H.q ⟨r.val, by have := H.hh_ge; omega⟩)).1) =
      (dualPt f (H.q ⟨r.val + 1, by have := H.hh_ge; omega⟩)).2 -
      (dualPt f (H.q ⟨r.val, by have := H.hh_ge; omega⟩)).2 := by
    rw [H.hμ_def r]; field_simp [ne_of_gt hdu]
  have hmax : (dualPt f p).1 * x + (dualPt f p).2 <
      max ((dualPt f (H.q ⟨r.val, by have := H.hh_ge; omega⟩)).1 * x +
           (dualPt f (H.q ⟨r.val, by have := H.hh_ge; omega⟩)).2)
          ((dualPt f (H.q ⟨r.val + 1, by have := H.hh_ge; omega⟩)).1 * x +
           (dualPt f (H.q ⟨r.val + 1, by have := H.hh_ge; omega⟩)).2) := by
    have hlt1 : (dualPt f p).1 * x + (dualPt f p).2 <
        (dualPt f p).1 * x + (dualPt f (H.q ⟨r.val, by have := H.hh_ge; omega⟩)).2 +
        H.μ r * ((dualPt f p).1 - (dualPt f (H.q ⟨r.val, by have := H.hh_ge; omega⟩)).1) := by
      linarith
    rcases le_total
      ((dualPt f (H.q ⟨r.val, by have := H.hh_ge; omega⟩)).1 * x +
       (dualPt f (H.q ⟨r.val, by have := H.hh_ge; omega⟩)).2)
      ((dualPt f (H.q ⟨r.val + 1, by have := H.hh_ge; omega⟩)).1 * x +
       (dualPt f (H.q ⟨r.val + 1, by have := H.hh_ge; omega⟩)).2) with hle | hle
    · rw [max_eq_right hle]; nlinarith
    · rw [max_eq_left hle]; nlinarith
  rw [F_top_eq_dual_sup]
  refine lt_of_lt_of_le hmax (max_le ?_ ?_)
  · exact Finset.le_sup' (fun w : Fin 5 × Bool => (dualPt f w).1 * x + (dualPt f w).2) (Finset.mem_univ _)
  · exact Finset.le_sup' (fun w : Fin 5 × Bool => (dualPt f w).1 * x + (dualPt f w).2) (Finset.mem_univ _)

/-- Exact characterization of all top-two crossings `x` where `∃ i < j, (f i).eval x = (f j).eval x = F_top f x`. -/
theorem top_crossings_eq_block_boundaries {f : Fin 5 → VFunc} (H : HullData f) :
    ∀ x : ℝ,
      (∃ i j : Fin 5, i < j ∧ (f i).eval x = (f j).eval x ∧ (f i).eval x = F_top f x) ↔
      (∃ r : Fin (H.h - 1),
        (H.q ⟨r.val, by have := H.hh_ge; omega⟩).1 ≠
        (H.q ⟨r.val + 1, by have := H.hh_ge; omega⟩).1 ∧
        x = -H.μ r) := by
  have hh5 := H.hh_ge
  let val (w : Fin 5 × Bool) (x : ℝ) : ℝ := (dualPt f w).1 * x + (dualPt f w).2
  have hstep : ∀ (x : ℝ) (r : Fin (H.h - 1)),
      val (H.q ⟨r.val + 1, by omega⟩) x - val (H.q ⟨r.val, by omega⟩) x =
      (x + H.μ r) * ((dualPt f (H.q ⟨r.val + 1, by omega⟩)).1 -
                     (dualPt f (H.q ⟨r.val, by omega⟩)).1) := by
    intro x r
    have hdu : 0 < (dualPt f (H.q ⟨r.val + 1, by omega⟩)).1 -
        (dualPt f (H.q ⟨r.val, by omega⟩)).1 :=
      sub_pos.mpr (H.hq_mono (by change r.val < r.val + 1; omega))
    have hm_mul : H.μ r * ((dualPt f (H.q ⟨r.val + 1, by omega⟩)).1 -
        (dualPt f (H.q ⟨r.val, by omega⟩)).1) =
        (dualPt f (H.q ⟨r.val + 1, by omega⟩)).2 -
        (dualPt f (H.q ⟨r.val, by omega⟩)).2 := by
      rw [H.hμ_def r]; field_simp [ne_of_gt hdu]
    dsimp [val]; linarith
  intro x
  constructor
  · rintro ⟨i, j, hij, heq, htop⟩
    have eval_branch : ∀ c : Fin 5, ∃ b : Bool, (f c).eval x = val (c, b) x := by
      intro c; unfold VFunc.eval; rcases le_total ((f c).a * x + (f c).b) ((f c).c * x + (f c).d) with h | h
      · rw [max_eq_right h]; exact ⟨true, rfl⟩
      · rw [max_eq_left h]; exact ⟨false, rfl⟩
    obtain ⟨bi, hbi⟩ := eval_branch i
    obtain ⟨bj, hbj⟩ := eval_branch j
    have hi_H : (i, bi) ∈ H_top f := by
      by_contra hnot
      have hlt := F_top_strict_int H x (i, bi) (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hnot⟩)
      change val (i, bi) x < F_top f x at hlt
      linarith
    have hj_H : (j, bj) ∈ H_top f := by
      by_contra hnot
      have hlt := F_top_strict_int H x (j, bj) (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hnot⟩)
      change val (j, bj) x < F_top f x at hlt
      linarith
    obtain ⟨ri, hri⟩ := H.hq_surj (i, bi) hi_H
    obtain ⟨rj, hrj⟩ := H.hq_surj (j, bj) hj_H
    have hri_ne_rj : ri ≠ rj := by
      intro h; subst h; rw [hri] at hrj; exact (ne_of_lt hij) (congrArg Prod.fst hrj)
    have hval_le : ∀ w : Fin 5 × Bool, val w x ≤ F_top f x := by
      intro w; rw [F_top_eq_dual_sup]; exact Finset.le_sup' (fun z => val z x) (Finset.mem_univ w)
    -- Without loss of generality assume `ri < rj` by checking both cases
    have h_ordered : ∀ a b : Fin H.h, a < b → (H.q a).1 ≠ (H.q b).1 →
        val (H.q a) x = F_top f x → val (H.q b) x = F_top f x →
        ∃ r : Fin (H.h - 1),
          (H.q ⟨r.val, by omega⟩).1 ≠ (H.q ⟨r.val + 1, by omega⟩).1 ∧ x = -H.μ r := by
      intro a b hab hcol_ab ha_top hb_top
      have h_b_eq : b.val = a.val + 1 := by
        by_contra hne
        have hlt1 : a.val + 1 < b.val := by change a.val < b.val at hab; omega
        let m : Fin H.h := ⟨a.val + 1, by omega⟩
        have hs1 := hstep x ⟨a.val, by omega⟩
        have hs2 := hstep x ⟨a.val + 1, by omega⟩
        -- Since `a < m < b` and `q a, q b` both reach `F_top f x`, check signs of `x + μ k`
        -- Actually for ANY `k < b`, `val (q k) x ≤ val (q b) x`, wait: if `x + μ a < 0`, then for all `k ≥ a`, `x + μ k < 0`!
        have hdu_a : 0 < (dualPt f (H.q m)).1 - (dualPt f (H.q a)).1 :=
          sub_pos.mpr (H.hq_mono (by change a.val < a.val + 1; omega))
        rcases lt_trichotomy x (-H.μ ⟨a.val, by omega⟩) with hlt | heq_x | hgt
        · -- `x < -μ a`, so `x < -μ k` for all `k ≥ a`, making `val (q b) x < val (q a) x`!
          have hdec : ∀ d : ℕ, (hd : a.val + d + 1 < H.h) →
              val (H.q ⟨a.val + d + 1, hd⟩) x < val (H.q a) x := by
            intro d
            induction d with
            | zero =>
              intro hd
              have hs := hstep x ⟨a.val, by omega⟩
              have hlt0 : x + H.μ ⟨a.val, by omega⟩ < 0 := by linarith
              have hmul : (x + H.μ ⟨a.val, by omega⟩) *
                  ((dualPt f (H.q ⟨a.val + 1, hd⟩)).1 - (dualPt f (H.q ⟨a.val, by omega⟩)).1) < 0 :=
                mul_neg_of_neg_of_pos hlt0 hdu_a
              have ha0 : (⟨a.val, by omega⟩ : Fin H.h) = a := rfl
              rw [ha0] at hs; linarith
            | succ d ih =>
              intro hd
              have ih' := ih (by omega)
              have hs := hstep x ⟨a.val + d + 1, by omega⟩
              have hanti : H.μ ⟨a.val + d + 1, by omega⟩ < H.μ ⟨a.val, by omega⟩ :=
                H.hμ_anti (by change a.val < a.val + d + 1; omega)
              have hlt0 : x + H.μ ⟨a.val + d + 1, by omega⟩ < 0 := by linarith
              have hdu' : 0 < (dualPt f (H.q ⟨a.val + d + 2, hd⟩)).1 -
                  (dualPt f (H.q ⟨a.val + d + 1, by omega⟩)).1 :=
                sub_pos.mpr (H.hq_mono (by change a.val + d + 1 < a.val + d + 2; omega))
              have hmul : (x + H.μ ⟨a.val + d + 1, by omega⟩) *
                  ((dualPt f (H.q ⟨a.val + d + 2, hd⟩)).1 -
                   (dualPt f (H.q ⟨a.val + d + 1, by omega⟩)).1) < 0 :=
                mul_neg_of_neg_of_pos hlt0 hdu'
              have hqeq : (⟨a.val + (d + 1) + 1, hd⟩ : Fin H.h) = ⟨a.val + d + 2, hd⟩ := by ext; dsimp; omega
              rw [hqeq]; linarith
          have ha_lt := a.isLt; have hb_lt_h := b.isLt
          have hb_lt := hdec (b.val - a.val - 1) (by omega)
          have hbeq : (⟨a.val + (b.val - a.val - 1) + 1, by omega⟩ : Fin H.h) = b := by ext; dsimp; omega
          rw [hbeq] at hb_lt
          linarith
        · -- `x = -μ a`, then for `k ≥ a + 1`, `μ k < μ a`, so `x + μ k < 0`, strictly decreasing from `m`!
          have hdec : ∀ d : ℕ, (hd : a.val + 1 + d + 1 < H.h) →
              val (H.q ⟨a.val + 1 + d + 1, hd⟩) x < val (H.q m) x := by
            intro d
            induction d with
            | zero =>
              intro hd
              have hs := hstep x ⟨a.val + 1, by omega⟩
              have hanti : H.μ ⟨a.val + 1, by omega⟩ < H.μ ⟨a.val, by omega⟩ :=
                H.hμ_anti (by change a.val < a.val + 1; omega)
              have hlt0 : x + H.μ ⟨a.val + 1, by omega⟩ < 0 := by linarith
              have hdu' : 0 < (dualPt f (H.q ⟨a.val + 2, hd⟩)).1 - (dualPt f (H.q m)).1 :=
                sub_pos.mpr (H.hq_mono (by change a.val + 1 < a.val + 2; omega))
              have hmul : (x + H.μ ⟨a.val + 1, by omega⟩) *
                  ((dualPt f (H.q ⟨a.val + 2, hd⟩)).1 - (dualPt f (H.q m)).1) < 0 :=
                mul_neg_of_neg_of_pos hlt0 hdu'
              have hm0 : (⟨a.val + 1, by omega⟩ : Fin H.h) = m := rfl
              rw [hm0] at hs; linarith
            | succ d ih =>
              intro hd
              have ih' := ih (by omega)
              have hs := hstep x ⟨a.val + 1 + d + 1, by omega⟩
              have hanti : H.μ ⟨a.val + 1 + d + 1, by omega⟩ < H.μ ⟨a.val, by omega⟩ :=
                H.hμ_anti (by change a.val < a.val + 1 + d + 1; omega)
              have hlt0 : x + H.μ ⟨a.val + 1 + d + 1, by omega⟩ < 0 := by linarith
              have hdu' : 0 < (dualPt f (H.q ⟨a.val + 1 + d + 2, hd⟩)).1 -
                  (dualPt f (H.q ⟨a.val + 1 + d + 1, by omega⟩)).1 :=
                sub_pos.mpr (H.hq_mono (by change a.val + 1 + d + 1 < a.val + 1 + d + 2; omega))
              have hmul : (x + H.μ ⟨a.val + 1 + d + 1, by omega⟩) *
                  ((dualPt f (H.q ⟨a.val + 1 + d + 2, hd⟩)).1 -
                   (dualPt f (H.q ⟨a.val + 1 + d + 1, by omega⟩)).1) < 0 :=
                mul_neg_of_neg_of_pos hlt0 hdu'
              have hqeq : (⟨a.val + 1 + (d + 1) + 1, hd⟩ : Fin H.h) = ⟨a.val + 1 + d + 2, hd⟩ := by ext; dsimp; omega
              rw [hqeq]; linarith
          have ha_lt := a.isLt; have hb_lt_h := b.isLt
          have hb_lt := hdec (b.val - a.val - 2) (by omega)
          have hbeq : (⟨a.val + 1 + (b.val - a.val - 2) + 1, by omega⟩ : Fin H.h) = b := by ext; dsimp; omega
          rw [hbeq] at hb_lt
          have hm_le := hval_le (H.q m)
          linarith
        · -- `x > -μ a`, so `val (q a) x < val (q m) x ≤ F_top f x`!
          have hs := hstep x ⟨a.val, by omega⟩
          have hgt0 : 0 < x + H.μ ⟨a.val, by omega⟩ := by linarith
          have hmul : 0 < (x + H.μ ⟨a.val, by omega⟩) *
              ((dualPt f (H.q m)).1 - (dualPt f (H.q a)).1) :=
            mul_pos hgt0 hdu_a
          have ha0 : (⟨a.val, by omega⟩ : Fin H.h) = a := rfl
          have hm0 : (⟨a.val + 1, by omega⟩ : Fin H.h) = m := rfl
          rw [ha0, hm0] at hs
          have hm_le := hval_le (H.q m)
          linarith
      let r : Fin (H.h - 1) := ⟨a.val, by omega⟩
      have hb_eq' : (⟨r.val + 1, by omega⟩ : Fin H.h) = b := by ext; exact h_b_eq.symm
      have ha_eq' : (⟨r.val, by omega⟩ : Fin H.h) = a := rfl
      have hdu : 0 < (dualPt f (H.q b)).1 - (dualPt f (H.q a)).1 := sub_pos.mpr (H.hq_mono hab)
      have hs := hstep x r
      rw [ha_eq', hb_eq'] at hs
      have hzero : (x + H.μ r) * ((dualPt f (H.q b)).1 - (dualPt f (H.q a)).1) = 0 := by linarith
      rcases mul_eq_zero.mp hzero with hx_eq | hdu_zero
      · refine ⟨r, ?_, by linarith⟩
        rw [ha_eq', hb_eq']
        exact hcol_ab
      · linarith
    rcases lt_or_gt_of_ne hri_ne_rj with hlt | hgt
    · exact h_ordered ri rj hlt (by rw [hri, hrj]; exact ne_of_lt hij)
        (by rw [hri]; linarith) (by rw [hrj]; linarith)
    · exact h_ordered rj ri hgt (by rw [hri, hrj]; exact ne_of_gt hij)
        (by rw [hrj]; linarith) (by rw [hri]; linarith)
  · rintro ⟨r, hcol, rfl⟩
    have hs := hstep (-H.μ r) r
    have hEq : val (H.q ⟨r.val + 1, by omega⟩) (-H.μ r) = val (H.q ⟨r.val, by omega⟩) (-H.μ r) := by
      linarith
    have h_ge_left : ∀ j : Fin H.h, j.val ≤ r.val →
        val (H.q j) (-H.μ r) ≤ val (H.q ⟨r.val, by omega⟩) (-H.μ r) := by
      intro j hj
      have hr_lt := r.isLt
      have h_ind : ∀ d : ℕ, ∀ (k : ℕ) (hk : k + d = r.val),
          val (H.q ⟨k, by omega⟩) (-H.μ r) ≤ val (H.q ⟨r.val, by omega⟩) (-H.μ r) := by
        intro d
        induction d with
        | zero =>
          intro k hk
          have hkeq : (⟨k, by omega⟩ : Fin H.h) = ⟨r.val, by omega⟩ := by ext; dsimp; omega
          rw [hkeq]
        | succ d ih =>
          intro k hk
          have ih' := ih (k + 1) (by omega)
          have hs' := hstep (-H.μ r) ⟨k, by omega⟩
          have hanti : H.μ r < H.μ ⟨k, by omega⟩ := H.hμ_anti (by change k < r.val; omega)
          have hdu' : 0 < (dualPt f (H.q ⟨k + 1, by omega⟩)).1 - (dualPt f (H.q ⟨k, by omega⟩)).1 :=
            sub_pos.mpr (H.hq_mono (by change k < k + 1; omega))
          have hle : val (H.q ⟨k, by omega⟩) (-H.μ r) ≤ val (H.q ⟨k + 1, by omega⟩) (-H.μ r) := by
            nlinarith
          exact le_trans hle ih'
      exact h_ind (r.val - j.val) j.val (by omega)
    have h_ge_right : ∀ j : Fin H.h, r.val + 1 ≤ j.val →
        val (H.q j) (-H.μ r) ≤ val (H.q ⟨r.val + 1, by omega⟩) (-H.μ r) := by
      intro j hj
      have hj_lt := j.isLt
      have h_ind : ∀ d : ℕ, (hd : r.val + 1 + d < H.h) →
          val (H.q ⟨r.val + 1 + d, hd⟩) (-H.μ r) ≤ val (H.q ⟨r.val + 1, by omega⟩) (-H.μ r) := by
        intro d
        induction d with
        | zero => intro _; exact le_rfl
        | succ d ih =>
          intro hd
          have ih' := ih (by omega)
          have hs' := hstep (-H.μ r) ⟨r.val + 1 + d, by omega⟩
          have hanti : H.μ ⟨r.val + 1 + d, by omega⟩ < H.μ r :=
            H.hμ_anti (by change r.val < r.val + 1 + d; omega)
          have hdu' : 0 < (dualPt f (H.q ⟨r.val + 1 + d + 1, hd⟩)).1 -
              (dualPt f (H.q ⟨r.val + 1 + d, by omega⟩)).1 :=
            sub_pos.mpr (H.hq_mono (by change r.val + 1 + d < r.val + 1 + d + 1; omega))
          have hle : val (H.q ⟨r.val + 1 + d + 1, hd⟩) (-H.μ r) ≤
              val (H.q ⟨r.val + 1 + d, by omega⟩) (-H.μ r) := by nlinarith
          have hqeq : (⟨r.val + 1 + (d + 1), hd⟩ : Fin H.h) = ⟨r.val + 1 + d + 1, hd⟩ := by ext; dsimp; omega
          rw [hqeq]; exact le_trans hle ih'
      have hres := h_ind (j.val - (r.val + 1)) (by omega)
      have hjeq : (⟨r.val + 1 + (j.val - (r.val + 1)), by omega⟩ : Fin H.h) = j := by ext; dsimp; omega
      rw [hjeq] at hres
      exact hres
    have h_top_val : val (H.q ⟨r.val, by omega⟩) (-H.μ r) = F_top f (-H.μ r) := by
      obtain ⟨w0, _, hw0_max⟩ := Finset.exists_max_image Finset.univ
        (fun w : Fin 5 × Bool => val w (-H.μ r)) ⟨(0, false), Finset.mem_univ _⟩
      have hF_eq : F_top f (-H.μ r) = val w0 (-H.μ r) := by
        rw [F_top_eq_dual_sup]
        apply le_antisymm
        · rw [Finset.sup'_le_iff]; intro w _; exact hw0_max w (Finset.mem_univ w)
        · exact Finset.le_sup' (fun w => val w (-H.μ r)) (Finset.mem_univ w0)
      have hw0_H : w0 ∈ H_top f := by
        by_contra hnot
        have hlt := F_top_strict_int H (-H.μ r) w0 (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hnot⟩)
        change val w0 (-H.μ r) < F_top f (-H.μ r) at hlt
        linarith
      obtain ⟨j0, rfl⟩ := H.hq_surj w0 hw0_H
      have h_le_top : val (H.q ⟨r.val, by omega⟩) (-H.μ r) ≤ F_top f (-H.μ r) := by
        rw [F_top_eq_dual_sup]; exact Finset.le_sup' (fun w => val w (-H.μ r)) (Finset.mem_univ _)
      have h_top_le : F_top f (-H.μ r) ≤ val (H.q ⟨r.val, by omega⟩) (-H.μ r) := by
        rw [hF_eq]
        rcases le_or_gt j0.val r.val with hj | hj
        · exact h_ge_left j0 hj
        · rw [← hEq]; exact h_ge_right j0 hj
      exact le_antisymm h_le_top h_top_le
    have h_eval_ge : ∀ w : Fin 5 × Bool, val w (-H.μ r) ≤ (f w.1).eval (-H.μ r) := by
      rintro ⟨c, b⟩; cases b <;> simp only [val, dualPt_false, dualPt_true, VFunc.eval]
      · exact le_max_left _ _
      · exact le_max_right _ _
    have h_eval_le : ∀ c : Fin 5, (f c).eval (-H.μ r) ≤ F_top f (-H.μ r) := by
      intro c; exact Finset.le_sup' (fun k : Fin 5 => (f k).eval (-H.μ r)) (Finset.mem_univ c)
    let c1 := (H.q ⟨r.val, by omega⟩).1
    let c2 := (H.q ⟨r.val + 1, by omega⟩).1
    have hc1 : (f c1).eval (-H.μ r) = F_top f (-H.μ r) :=
      le_antisymm (h_eval_le c1) (h_top_val ▸ h_eval_ge (H.q ⟨r.val, by omega⟩))
    have hc2 : (f c2).eval (-H.μ r) = F_top f (-H.μ r) :=
      le_antisymm (h_eval_le c2) ((hEq ▸ h_top_val) ▸ h_eval_ge (H.q ⟨r.val + 1, by omega⟩))
    rcases lt_or_gt_of_ne hcol with hlt | hgt
    · exact ⟨c1, c2, hlt, by linarith, hc1⟩
    · exact ⟨c2, c1, hgt, by linarith, hc2⟩

end Sec9

end
