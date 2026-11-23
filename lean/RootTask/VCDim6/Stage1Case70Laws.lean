import Mathlib
import RootTask.VCDim6.Stage1Case70Chains

open scoped BigOperators
open Finset
open PolygonCore ChirotopeSoundness CertifiedAndHalfPlaneSoundness

noncomputable section

namespace VCDim6

/-!
# Section 3.1 Master Propagation Laws (`Lemmas 3.4, 3.5, 3.6, 3.7`)

Formalizes the complete geometric propagation suite for Stage 1 Case `(7, 0)` on `CCWConvexSeven`:
1. **`firesW0_capacity_le_two`** (Theorem 2.3(4) on `W₀`)
2. **`law_05_star_sign` & `adj_equal_sign_excl`** (Lemma 3.4(a)–(b))
3. **`alt_witness_dichotomy`** (Lemma 3.5: Branch 1 chain firing vs. Branch 2 tangential escape)
4. **`master_law_I`** (Lemma 3.6: double-miss propagation on `w_{¬{p, q}}`)
5. **`master_law_II`** (Lemma 3.7: triple-miss second-chain forcing on `w_ι`)
-/

/-- Alternating 4-element seen subset `V_ι = {ι + 1, ι + 3, ι + 5, ι + 6}` missing `M_ι = {ι, ι + 2, ι + 4}`. -/
def V_alt (ι : Fin 7) : Finset (Fin 7) :=
  {ι + 1, ι + 3, ι + 5, ι + 6}

/-- Alternating 3-element missed independent set `M_ι = {ι, ι + 2, ι + 4}`. -/
def M_alt (ι : Fin 7) : Finset (Fin 7) :=
  {ι, ι + 2, ι + 4}

/-- 5-element witness subset missing `{p, q}`. -/
def T_miss2 (p q : Fin 7) : Finset (Fin 7) :=
  (Finset.univ.erase p).erase q

/-- Membership in `W₀ \ {w_★}` (`5 ≤ |Tv| ≤ 6` or `Tv = V_alt ι`). -/
def IsW0Set (Tv : Finset (Fin 7)) : Prop :=
  (5 ≤ Tv.card ∧ Tv.card ≤ 6) ∨ ∃ ι : Fin 7, Tv = V_alt ι

/-- `p ← {a, b}`: some witness `Tv` in `W₀ \ {w_★}` fires Lemma 4.4 with `w_★` on `p` across `{a, b}`. -/
def FiresW0 (P : Set (ℝ × ℝ)) (S : Fin 7 → ℝ × ℝ) (w : Finset (Fin 7) → ℝ × ℝ)
    (p a b : Fin 7) : Prop :=
  ∃ (Tv : Finset (Fin 7)) (g c : Fin 7),
    IsW0Set Tv ∧ ({g, c} : Finset (Fin 7)) = {a, b} ∧ FiresOrdered P S w Tv g p c

/-- Endpoints `(a, b)` of the three hull chains cut by `M_alt ι`:
    `0 ↦ (ι, ι + 2)`, `1 ↦ (ι + 2, ι + 4)`, `2 ↦ (ι + 4, ι)`. -/
def chainEndpoints (ι : Fin 7) (tag : Fin 3) : Fin 7 × Fin 7 :=
  match tag.val with
  | 0 => (ι, ι + 2)
  | 1 => (ι + 2, ι + 4)
  | _ => (ι + 4, ι)

/-- Third missed vertex `M_alt ι \ {a, b}` opposite chain `tag`. -/
def chainOppositeMissed (ι : Fin 7) (tag : Fin 3) : Fin 7 :=
  match tag.val with
  | 0 => ι + 4
  | 1 => ι
  | _ => ι + 2

/-- Branch 1 of Lemma 3.5: `w (V_alt ι)` fires chain `tag ∈ {0, 1, 2}` with sign `s`. -/
def IotaFiresChain (P : Set (ℝ × ℝ)) (S : Fin 7 → ℝ × ℝ) (w : Finset (Fin 7) → ℝ × ℝ)
    (ι : Fin 7) (tag : Fin 3) (s : Bool) : Prop :=
  let a := (chainEndpoints ι tag).1
  let b := (chainEndpoints ι tag).2
  orientSign (w (V_alt ι)) (w Finset.univ) (S a) = s ∧
  orientSign (w (V_alt ι)) (w Finset.univ) (S b) = s ∧
  ∀ p : Fin 7, 0 < (p - a).val → (p - a).val < (b - a).val →
    FiresW0 P S w p a b ∧
    intrinsicPol S w p = s ∧
    orientSign (w (V_alt ι)) (w Finset.univ) (S p) = s

/-- Branch 2 of Lemma 3.5: tangential escape of `w (V_alt ι)` along `tag_adj ∈ {0, 1, 2}` with sign `s`. -/
def IotaEscapes (_P : Set (ℝ × ℝ)) (S : Fin 7 → ℝ × ℝ) (w : Finset (Fin 7) → ℝ × ℝ)
    (ι : Fin 7) (tag_adj : Fin 3) (s : Bool) : Prop :=
  let a := (chainEndpoints ι tag_adj).1
  let b := (chainEndpoints ι tag_adj).2
  let m := if s then a else b
  orientSign (w (V_alt ι)) (w Finset.univ) (S m) = !s ∧
  (∀ v : Fin 7, v ≠ m → orientSign (w (V_alt ι)) (w Finset.univ) (S v) = s) ∧
  (∀ u : Fin 7, (u - a).val < (b - a).val →
    orientSign (S u) (S (u + 1)) (w (V_alt ι)) = false ∧
    orientSign (S u) (S (u + 1)) (w Finset.univ) = false)

/-! ### Pure `Fin 7` / `Fin 3` Combinatorial Identities (`decide +revert` over small finite domains) -/

private lemma bool_ne_not {b : Bool} (h : b = !b) : False :=
  (Bool.eq_not_self b).mp h

private lemma valt_ne_univ (ι : Fin 7) : V_alt ι ≠ Finset.univ := by
  intro h; have : ι ∈ V_alt ι := h ▸ Finset.mem_univ ι; revert ι this; decide

private lemma tmiss2_isW0 {p q : Fin 7} (hpq : p ≠ q) : IsW0Set (T_miss2 p q) := by
  left
  have hc : (T_miss2 p q).card = 5 := by revert p q hpq; decide
  omega

private lemma tmiss2_ne_univ (p q : Fin 7) : T_miss2 p q ≠ Finset.univ := by
  intro h; have : p ∈ T_miss2 p q := h ▸ Finset.mem_univ p; revert p q this; decide

private lemma valt_adj_mem (ι k : Fin 7) :
    k ∈ V_alt ι → k - 1 ∉ V_alt ι → k + 1 ∉ V_alt ι → k + 2 ∈ V_alt ι := by
  decide +revert

private lemma pair_eq_or (g c a b : Fin 7) :
    ({g, c} : Finset (Fin 7)) = {a, b} → a ≠ b → (g = a ∧ c = b) ∨ (g = b ∧ c = a) := by
  decide +revert

private lemma card_ge5_adj_mem (Tv : Finset (Fin 7)) (k : Fin 7)
    (hc : 5 ≤ Tv.card) (hm1 : k - 1 ∉ Tv) (hp1 : k + 1 ∉ Tv) : k + 2 ∈ Tv := by
  by_contra hp2
  have hsub : Tv ⊆ (((Finset.univ.erase (k - 1)).erase (k + 1)).erase (k + 2)) := by
    intro x hx
    simp only [Finset.mem_erase, Finset.mem_univ, and_true]
    refine ⟨fun e => hp2 (e ▸ hx), fun e => hp1 (e ▸ hx), fun e => hm1 (e ▸ hx)⟩
  have hcard4 : ∀ k₀ : Fin 7,
      (((Finset.univ.erase (k₀ - 1)).erase (k₀ + 1)).erase (k₀ + 2)).card = 4 := by decide
  have hle := Finset.card_le_card hsub
  have hc4 := hcard4 k
  omega

private lemma valt_missed_props (ι : Fin 7) (tag : Fin 3) :
    let a := (chainEndpoints ι tag).1
    let b := (chainEndpoints ι tag).2
    let m := chainOppositeMissed ι tag
    a ∉ V_alt ι ∧ a - 1 ∈ V_alt ι ∧ a + 1 ∈ V_alt ι ∧
    b ∉ V_alt ι ∧ b - 1 ∈ V_alt ι ∧ b + 1 ∈ V_alt ι ∧
    m ∉ V_alt ι ∧ m - 1 ∈ V_alt ι ∧ m + 1 ∈ V_alt ι ∧
    2 ≤ (b - a).val ∧ (b - a).val ≤ 3 ∧
    (∀ p : Fin 7, 0 < (p - a).val → (p - a).val < (b - a).val → p ∈ V_alt ι) ∧
    (∀ x : Fin 7, x ∈ V_alt ι ∨ (x - a).val ≤ (b - a).val ∨ x = m) ∧
    m ≠ a ∧ m ≠ b ∧ (m - a).val > (b - a).val := by
  decide +revert

private lemma iota_partition_edge (ι u : Fin 7) :
    ∃ tag : Fin 3, (u - (chainEndpoints ι tag).1).val <
      ((chainEndpoints ι tag).2 - (chainEndpoints ι tag).1).val := by
  decide +revert

private lemma iota_next_chains_far (ι : Fin 7) (tag_bad : Fin 3) :
    let ab := (chainEndpoints ι tag_bad).1
    let bb := (chainEndpoints ι tag_bad).2
    let a1 := (chainEndpoints ι (tag_bad + 1)).1
    let b1 := (chainEndpoints ι (tag_bad + 1)).2
    let a2 := (chainEndpoints ι (tag_bad + 2)).1
    let b2 := (chainEndpoints ι (tag_bad + 2)).2
    a1 = bb ∧ b1 = a2 ∧ b2 = ab ∧
    a1 + 1 ∈ V_alt ι ∧ a2 + 1 ∈ V_alt ι ∧
    0 < ((a1 + 1) - a1).val ∧ ((a1 + 1) - a1).val < (b1 - a1).val ∧
    0 < ((a2 + 1) - a2).val ∧ ((a2 + 1) - a2).val < (b2 - a2).val ∧
    (∀ t ∈ ({tag_bad + 1, tag_bad + 2} : Finset (Fin 3)),
      let a := (chainEndpoints ι t).1
      let b := (chainEndpoints ι t).2
      a ≠ a + 1 ∧ b - 1 ≠ b ∧ a ≠ b ∧
      (bb - ab).val ≤ (a - ab).val ∧ (a - ab).val + ((a + 1) - a).val ≤ 7 ∧
      (bb - ab).val ≤ ((b - 1) - ab).val ∧ ((b - 1) - ab).val + (b - (b - 1)).val ≤ 7 ∧
      (bb - ab).val ≤ (a - ab).val ∧ (a - ab).val + (b - a).val ≤ 7) ∧
    ((a1 + 1) ≠ b1 ∧ (bb - ab).val ≤ ((a1 + 1) - ab).val ∧
      ((a1 + 1) - ab).val + (b1 - (a1 + 1)).val ≤ 7) ∧
    (a2 ≠ (a2 + 1) ∧ (bb - ab).val ≤ (a2 - ab).val ∧
      (a2 - ab).val + ((a2 + 1) - a2).val ≤ 7) ∧
    chainOppositeMissed ι (tag_bad + 2) = bb ∧
    chainOppositeMissed ι (tag_bad + 1) = ab := by
  decide +revert

private lemma iota_two_bad_share (ι : Fin 7) (t1 t2 : Fin 3) :
    t1 ≠ t2 →
      let a1 := (chainEndpoints ι t1).1
      let b1 := (chainEndpoints ι t1).2
      let a2 := (chainEndpoints ι t2).1
      let b2 := (chainEndpoints ι t2).2
      (b1 = a2 ∧ 0 < (b1 - a1).val ∧ (b1 - a1).val < (b2 - a1).val) ∨
      (b2 = a1 ∧ 0 < (b2 - a2).val ∧ (b2 - a2).val < (b1 - a2).val) := by
  decide +revert

private lemma iota_adj_escape_geom (ι : Fin 7) (tag_star : Fin 3) (s : Bool) :
    let as_ := (chainEndpoints ι tag_star).1
    let bs_ := (chainEndpoints ι tag_star).2
    let m := chainOppositeMissed ι tag_star
    let g := if s then as_ else bs_
    let tag_adj := if s then tag_star - 1 else tag_star + 1
    let aa := (chainEndpoints ι tag_adj).1
    let ba := (chainEndpoints ι tag_adj).2
    let u_adj := if s then g - 1 else g + 1
    tag_adj ≠ tag_star ∧
    ((s = false → aa = g ∧ ba = m) ∧ (s = true → aa = m ∧ ba = g)) ∧
    u_adj ∈ V_alt ι ∧ u_adj ≠ m ∧
    (u_adj - aa).val < (ba - aa).val := by
  decide +revert

private lemma fin7_ne_succ' (x : Fin 7) : x ≠ x + 1 := by decide +revert

private lemma fin3_ne_succ_or_add2 (t tb : Fin 3) :
    t ≠ tb → t = tb + 1 ∨ t = tb + 2 := by
  decide +revert

private lemma fin3_add1_ne_add2 (ts : Fin 3) : ts + 1 ≠ ts + 2 := by decide +revert
private lemma fin3_add1_ne_self (t : Fin 3) : t + 1 ≠ t := by decide +revert
private lemma fin3_add2_ne_self (t : Fin 3) : t + 2 ≠ t := by decide +revert
private lemma fin3_add1_ne_add2' (t : Fin 3) : t + 1 ≠ t + 2 := by decide +revert
private lemma fin3_add2_ne_add1' (t : Fin 3) : t + 2 ≠ t + 1 := by decide +revert

private lemma malt_valt_props (ι : Fin 7) :
    (∀ y : Fin 7, y ∈ M_alt ι → y ∈ V_alt ι → False) ∧
    (∀ y : Fin 7, y ∈ M_alt ι ∨ y ∈ V_alt ι) ∧
    (∀ t : Fin 3, (chainEndpoints ι t).1 ∈ M_alt ι ∧ (chainEndpoints ι t).2 ∈ M_alt ι) := by
  decide +revert

private lemma fin3_add_overlap (ts tb : Fin 3) :
    ts + 1 = tb + 1 ∨ ts + 1 = tb + 2 ∨ ts + 2 = tb + 1 ∨ ts + 2 = tb + 2 := by
  decide +revert

private lemma iota_other_chains_outside (ι : Fin 7) (tag_star : Fin 3) :
    let as_ := (chainEndpoints ι tag_star).1
    let bs_ := (chainEndpoints ι tag_star).2
    ∀ t ∈ ({tag_star + 1, tag_star + 2} : Finset (Fin 3)),
      ∀ x : Fin 7, (x - (chainEndpoints ι t).1).val ≤
        ((chainEndpoints ι t).2 - (chainEndpoints ι t).1).val →
      x = as_ ∨ (bs_ - as_).val ≤ (x - as_).val := by
  decide +revert

private lemma iota_unique_edge_tag (ι : Fin 7) (t1 t2 : Fin 3) (u : Fin 7) :
    (u - (chainEndpoints ι t1).1).val < ((chainEndpoints ι t1).2 - (chainEndpoints ι t1).1).val →
    (u - (chainEndpoints ι t2).1).val < ((chainEndpoints ι t2).2 - (chainEndpoints ι t2).1).val →
    t1 = t2 := by
  decide +revert

private lemma iota_chain_step_props (ι : Fin 7) (tag : Fin 3) :
    let a := (chainEndpoints ι tag).1
    let b := (chainEndpoints ι tag).2
    a ≠ b ∧
    ((b - 1) - a).val < (b - a).val ∧
    ((b - 1) - a).val + 1 = (b - a).val := by
  decide +revert

private lemma iota_law2_quad_sep (ι : Fin 7) (tag1 : Fin 3) (p1 p2 : Fin 7) :
    let a1 := (chainEndpoints ι (tag1 + 1)).1
    let b1 := (chainEndpoints ι (tag1 + 1)).2
    let a2 := (chainEndpoints ι (tag1 + 2)).1
    let b2 := (chainEndpoints ι (tag1 + 2)).2
    0 < (p1 - a1).val → (p1 - a1).val < (b1 - a1).val →
    0 < (p2 - a2).val → (p2 - a2).val < (b2 - a2).val →
    0 < (p1 - a1).val ∧ (p1 - a1).val < (b1 - a1).val ∧ (b1 - a1).val < (p2 - a1).val ∧
    a1 ∈ M_alt ι ∧ b1 ∈ M_alt ι := by
  decide +revert

set_option synthInstance.maxHeartbeats 200000 in
private lemma miss2_short_long_props (p q : Fin 7) :
    2 ≤ (q - p).val → (q - p).val ≤ 3 →
      4 ≤ (p - q).val ∧ (p - q).val ≤ 5 ∧
      (q + 1 ≠ q + 2 ∧ q + 1 ≠ q + 3 ∧ q + 2 ≠ q + 3) ∧
      (0 < ((q + 1) - q).val ∧ ((q + 1) - q).val < (p - q).val) ∧
      (0 < ((q + 2) - q).val ∧ ((q + 2) - q).val < (p - q).val) ∧
      (0 < ((q + 3) - q).val ∧ ((q + 3) - q).val < (p - q).val) ∧
      (p ≠ p + 1 ∧ q - 1 ≠ q ∧ p ≠ q ∧
       (p - q).val ≤ (p - q).val ∧ (p - q).val + ((p + 1) - p).val ≤ 7 ∧
       (p - q).val ≤ ((q - 1) - q).val ∧ ((q - 1) - q).val + (q - (q - 1)).val ≤ 7 ∧
       (p - q).val + (q - p).val ≤ 7) ∧
      (q ≠ q + 1 ∧ p - 1 ≠ p ∧ q ≠ p ∧
       (q - p).val ≤ (q - p).val ∧ (q - p).val + ((q + 1) - q).val ≤ 7 ∧
       (q - p).val ≤ ((p - 1) - p).val ∧ ((p - 1) - p).val + (p - (p - 1)).val ≤ 7 ∧
       (q - p).val + (p - q).val ≤ 7) ∧
      (∀ r1 r2 : Fin 7,
        0 < (r1 - p).val → (r1 - p).val < (q - p).val →
        0 < (r2 - q).val → (r2 - q).val < (p - q).val →
        (q - p).val < (r2 - p).val) := by
  fin_cases p <;> fin_cases q <;> decide

set_option synthInstance.maxHeartbeats 200000 in
private lemma chain_len25_tri_props (a b : Fin 7) :
    2 ≤ (b - a).val → (b - a).val ≤ 5 →
      a ≠ b ∧
      (((b - a).val = 2 ∧ a + 1 + 1 = b ∧ ((a + 1) - a).val ≤ (b - a).val) ∨
       ((b - a).val = 3 ∧ a + 1 + 1 + 1 = b ∧ a ≠ a + 1 + 1 ∧
         ((a + 1) - a).val ≤ (b - a).val ∧ ((a + 1 + 1) - a).val ≤ (b - a).val) ∨
       ((b - a).val = 4 ∧ a + 1 + 1 + 1 + 1 = b ∧ a ≠ a + 1 + 1 ∧ a ≠ a + 1 + 1 + 1 ∧
         ((a + 1) - a).val ≤ (b - a).val ∧ ((a + 1 + 1) - a).val ≤ (b - a).val ∧
         ((a + 1 + 1 + 1) - a).val ≤ (b - a).val) ∨
       ((b - a).val = 5 ∧ a + 1 + 1 + 1 + 1 + 1 = b ∧
         a ≠ a + 1 + 1 ∧ a ≠ a + 1 + 1 + 1 ∧ a ≠ a + 1 + 1 + 1 + 1 ∧
         ((a + 1) - a).val ≤ (b - a).val ∧ ((a + 1 + 1) - a).val ≤ (b - a).val ∧
         ((a + 1 + 1 + 1) - a).val ≤ (b - a).val ∧ ((a + 1 + 1 + 1 + 1) - a).val ≤ (b - a).val)) := by
  fin_cases a <;> fin_cases b <;> decide

private lemma nonadj_miss2_props (p q : Fin 7) :
    2 ≤ (q - p).val → (q - p).val ≤ 5 →
      p ≠ q ∧ p ∉ T_miss2 p q ∧ q ∉ T_miss2 p q ∧
      p - 1 ∈ T_miss2 p q ∧ p + 1 ∈ T_miss2 p q ∧
      q - 1 ∈ T_miss2 p q ∧ q + 1 ∈ T_miss2 p q ∧
      (∀ r : Fin 7, r ≠ p → r ≠ q → r ∈ T_miss2 p q) ∧
      (∀ u : Fin 7, (u - p).val < (q - p).val ∨ (u - q).val < (p - q).val) ∧
      ((q - p).val + (p - q).val = 7) ∧
      (((q - p).val ≤ 3 ∧ 4 ≤ (p - q).val) ∨ ((p - q).val ≤ 3 ∧ 4 ≤ (q - p).val)) := by
  decide +revert

/-! ### Basic `FiresW0` Properties, Theorem 2.3(4), and Lemma 3.4(a)–(b) -/

open scoped Classical

theorem firesW0_symm {P : Set (ℝ × ℝ)} {S : Fin 7 → ℝ × ℝ} {w : Finset (Fin 7) → ℝ × ℝ}
    {p a b : Fin 7} (hf : FiresW0 P S w p a b) : FiresW0 P S w p b a := by
  rcases hf with ⟨Tv, g, c, hW, hpair, hfo⟩
  exact ⟨Tv, g, c, hW, hpair.trans (Finset.pair_comm a b), hfo⟩

theorem firesW0_ne {P : Set (ℝ × ℝ)} {S : Fin 7 → ℝ × ℝ} {w : Finset (Fin 7) → ℝ × ℝ}
    {p a b : Fin 7} (hf : FiresW0 P S w p a b) : p ≠ a ∧ p ≠ b ∧ a ≠ b := by
  rcases hf with ⟨Tv, g, c, _, hpair, hfo⟩
  have hgp : p ≠ g := fun h => hfo.ha_not_v (h ▸ hfo.hp_v)
  have hcp : p ≠ c := fun h => hfo.hc_not_v (h ▸ hfo.hp_v)
  have hgc : g ≠ c := by
    intro h; have hc := hfo.h_cross_ac; rw [h] at hc
    have h0 : ∀ z, orient2D (S c) (S c) z = 0 := fun z => by unfold orient2D; ring
    simp [oppSideBool, orientSign, h0] at hc
  have ha_mem : a ∈ ({g, c} : Finset (Fin 7)) := by rw [hpair]; simp
  have hb_mem : b ∈ ({g, c} : Finset (Fin 7)) := by rw [hpair]; simp
  have hg_mem : g ∈ ({a, b} : Finset (Fin 7)) := by rw [← hpair]; simp
  have hc_mem : c ∈ ({a, b} : Finset (Fin 7)) := by rw [← hpair]; simp
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha_mem hb_mem hg_mem hc_mem
  refine ⟨?_, ?_, ?_⟩
  · rcases ha_mem with rfl | rfl <;> assumption
  · rcases hb_mem with rfl | rfl <;> assumption
  · intro hab; subst hab
    simp only [ or_self] at hg_mem hc_mem
    exact hgc (hg_mem.trans hc_mem.symm)

/-- **Theorem 2.3(4) (`firesW0_capacity_le_two`)**:
    At most two distinct targets `p₀, p₁, p₂` can fire across the same chord `{a, b}`. -/
theorem firesW0_capacity_le_two {P : Set (ℝ × ℝ)} {S : Fin 7 → ℝ × ℝ} {w : Finset (Fin 7) → ℝ × ℝ}
    (hP : ShatteredSimplePolygon P S w)
    {a b p₀ p₁ p₂ : Fin 7}
    (hp01 : p₀ ≠ p₁) (hp02 : p₀ ≠ p₂) (hp12 : p₁ ≠ p₂)
    (hf0 : FiresW0 P S w p₀ a b) (hf1 : FiresW0 P S w p₁ a b) (hf2 : FiresW0 P S w p₂ a b) :
    False := by
  have n0 := firesW0_ne hf0; have n1 := firesW0_ne hf1; have n2 := firesW0_ne hf2
  rcases hf0 with ⟨_, _, _, _, hp0, hfo0⟩
  rcases hf1 with ⟨_, _, _, _, hp1, hfo1⟩
  rcases hf2 with ⟨_, _, _, _, hp2, hfo2⟩
  obtain ⟨H₀, ht0⟩ := fires_half_plane_test hP hfo0 hp0
  obtain ⟨H₁, ht1⟩ := fires_half_plane_test hP hfo1 hp1
  obtain ⟨H₂, ht2⟩ := fires_half_plane_test hP hfo2 hp2
  exact chord_capacity_le_two hP hp01 hp02 hp12
    (by simp [n0.1, n0.2.1]) (by simp [n1.1, n1.2.1]) (by simp [n2.1, n2.2.1]) ht0 ht1 ht2

/-- **Lemma 3.4(a) (`law_05_star_sign`)**:
    If `m ← {a, b}` and `Ty` sees `{a, b}` while missing `m`, then
    `orientSign (w Ty) (w Finset.univ) (S m) = !(intrinsicPol S w m)`. -/
theorem law_05_star_sign {P : Set (ℝ × ℝ)} {S : Fin 7 → ℝ × ℝ} {w : Finset (Fin 7) → ℝ × ℝ}
    (hP : ShatteredSimplePolygon P S w)
    {m a b : Fin 7} {Ty : Finset (Fin 7)}
    (hf : FiresW0 P S w m a b) (hab_Ty : {a, b} ⊆ Ty) (hm_not : m ∉ Ty) :
    orientSign (w Ty) (w Finset.univ) (S m) = !(intrinsicPol S w m) := by
  rcases hf with ⟨_, g, c, _, hpair, hfo⟩
  exact ((fires_intrinsic_pol_and_signs hP hfo).2.2.2 (hpair.symm ▸ hab_Ty) hm_not).2

/-- **Lemma 3.4(b) (`adj_equal_sign_excl`)**:
    For any `k : Fin 7` with `intrinsicPol S w k = intrinsicPol S w (k + 1)`, we cannot
    simultaneously have `k ← {k - 1, k + 1}` and `(k + 1) ← {k, k + 2}`. -/
theorem adj_equal_sign_excl {P : Set (ℝ × ℝ)} {S : Fin 7 → ℝ × ℝ} {w : Finset (Fin 7) → ℝ × ℝ}
    (hP : ShatteredSimplePolygon P S w) {k : Fin 7}
    (heq_pol : intrinsicPol S w k = intrinsicPol S w (k + 1))
    (hfk : FiresW0 P S w k (k - 1) (k + 1))
    (hfk1 : FiresW0 P S w (k + 1) k (k + 2)) : False := by
  rcases hfk with ⟨Tv, g, c, hW0, hpair, hfo⟩
  have hk_in : k ∈ Tv := hfo.hp_v
  have hm1_mem : k - 1 ∈ ({g, c} : Finset (Fin 7)) := by rw [hpair]; simp
  have hp1_mem : k + 1 ∈ ({g, c} : Finset (Fin 7)) := by rw [hpair]; simp
  have hm1_out : k - 1 ∉ Tv := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm1_mem
    rcases hm1_mem with rfl | rfl; exact hfo.ha_not_v; exact hfo.hc_not_v
  have hp1_out : k + 1 ∉ Tv := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp1_mem
    rcases hp1_mem with rfl | rfl; exact hfo.ha_not_v; exact hfo.hc_not_v
  have hp2_in : k + 2 ∈ Tv := by
    rcases hW0 with ⟨hc5, _⟩ | ⟨ι, rfl⟩
    · exact card_ge5_adj_mem Tv k hc5 hm1_out hp1_out
    · exact valt_adj_mem ι k hk_in hm1_out hp1_out
  have hkk2_sub : ({k, k + 2} : Finset (Fin 7)) ⊆ Tv := by
    intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> assumption
  have h_not := law_05_star_sign hP hfk1 hkk2_sub hp1_out
  have h_pos_k : orientSign (w Tv) (w Finset.univ) (S k) = intrinsicPol S w k :=
    (fires_intrinsic_pol_and_signs hP hfo).1
  have h_pos_k1 : orientSign (w Tv) (w Finset.univ) (S (k + 1)) = intrinsicPol S w k := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp1_mem
    rcases hp1_mem with rfl | rfl
    · exact hfo.h_vqa.trans h_pos_k
    · exact hfo.h_vqc.trans h_pos_k
  rw [h_pos_k1, ← heq_pol] at h_not
  exact bool_ne_not h_not

/-- CCW sign consequences of `FiresW0 P S w p a b` when `(a, p, b)` is in strict CCW order on `Fin 7`. -/
theorem firesW0_ccw_signs {P : Set (ℝ × ℝ)} {S : Fin 7 → ℝ × ℝ} {w : Finset (Fin 7) → ℝ × ℝ}
    (hP : ShatteredSimplePolygon P S w) (hccw : CCWConvexSeven S)
    (hA : PolygonCore.interiorPoints S = ∅) (hH : PolygonCore.certifiedSet P S w = ∅)
    {p a b : Fin 7} (hf : FiresW0 P S w p a b)
    (hp1 : 0 < (p - a).val) (hp2 : (p - a).val < (b - a).val) :
    (if intrinsicPol S w p then orientSign (S a) (S p) (w Finset.univ) = true
     else orientSign (S p) (S b) (w Finset.univ) = true) ∧
    (∀ {Ty : Finset (Fin 7)}, {a, b} ⊆ Ty → p ∉ Ty →
      if intrinsicPol S w p then orientSign (S p) (S b) (w Ty) = true
      else orientSign (S a) (S p) (w Ty) = true) := by
  have ⟨hpa, hpb, hab⟩ := firesW0_ne hf
  rcases hf with ⟨Tv, g, c, _, hpair, hfo⟩
  obtain ⟨_, hgpc, hc9_x, _⟩ := fires_intrinsic_pol_and_signs hP hfo
  have hpD : p ∈ PolygonCore.hullVertices S \ PolygonCore.certifiedSet P S w := by
    rw [hH]
    have hB : PolygonCore.hullVertices S = Finset.univ := by
      ext x; simp only [Finset.mem_univ, iff_true]
      by_contra hx
      have hxA : x ∈ PolygonCore.interiorPoints S := Finset.mem_sdiff.mpr ⟨Finset.mem_univ x, hx⟩
      rw [hA] at hxA; exact Finset.notMem_empty x hxA
    simp [hB]
  have hapb_t : orientSign (S a) (S p) (S b) = true := hccw a p b hp1 hp2
  have hbpa_f : orientSign (S b) (S p) (S a) = false := by
    have := orient2D_pos_of_ccw hccw hp1 hp2
    have hid : orient2D (S b) (S p) (S a) = -orient2D (S a) (S p) (S b) := by unfold orient2D; ring
    exact (orientSign_eq_false_iff _ _ _).mpr (le_of_lt (by linarith))
  have hgc_or := pair_eq_or g c a b hpair hab
  cases hσ : intrinsicPol S w p
  · simp only [Bool.false_eq_true, ↓reduceIte]
    have hgb : g = b ∧ c = a := by
      rcases hgc_or with ⟨hg, hc⟩ | ⟨hg, hc⟩
      · rw [hg, hc, hapb_t, hσ] at hgpc; exact False.elim (Bool.noConfusion hgpc)
      · exact ⟨hg, hc⟩
    rcases hgb with ⟨hg, hc⟩; subst hg hc
    refine ⟨?_, fun {Ty} hab_Ty hp_Ty => ?_⟩
    · have h1 := hc9_x (Finset.subset_univ _) (Finset.mem_univ p)
      rw [hσ] at h1
      have h2 : orientSign (S g) (S p) (w Finset.univ) = false := by
        rw [orientSign_cycle2 (S p) (w Finset.univ) (S g), h1]
      rw [orientSign_swap12 (orient_S_S_w_ne hP hpb.symm Finset.univ), h2]; rfl
    · have hba_Ty : ({g, c} : Finset (Fin 7)) ⊆ Ty := Finset.pair_comm c g ▸ hab_Ty
      have h1 := fires_unmarked_c_sign hP (by decide : 3 ≤ 7) hfo hpD hba_Ty hp_Ty
      rw [hσ] at h1
      rw [orientSign_swap12 (orient_S_S_w_ne hP hpa Ty), h1]; rfl
  · simp only [↓reduceIte]
    have hga : g = a ∧ c = b := by
      rcases hgc_or with ⟨hg, hc⟩ | ⟨hg, hc⟩
      · exact ⟨hg, hc⟩
      · rw [hg, hc, hbpa_f, hσ] at hgpc; exact False.elim (Bool.noConfusion hgpc)
    rcases hga with ⟨hg, hc⟩; subst hg hc
    refine ⟨?_, fun {Ty} hab_Ty hp_Ty => ?_⟩
    · have h1 := hc9_x (Finset.subset_univ _) (Finset.mem_univ p)
      rw [hσ] at h1
      rw [orientSign_cycle2 (S p) (w Finset.univ) (S g), h1]
    · have h1 := fires_unmarked_c_sign hP (by decide : 3 ≤ 7) hfo hpD hab_Ty hp_Ty
      rwa [hσ] at h1

/-! ### Chain-Goodness & Uncut Chain Helpers -/

lemma hull_edge_orient_nonneg {S : Fin 7 → ℝ × ℝ} (hccw : CCWConvexSeven S)
    (u z : Fin 7) : 0 ≤ orient2D (S u) (S (u + 1)) (S z) := by
  by_cases hzu : z = u
  · subst hzu; exact le_of_eq (by unfold orient2D; ring)
  · by_cases hzu1 : z = u + 1
    · subst hzu1; exact le_of_eq (by unfold orient2D; ring)
    · exact le_of_lt (strictConvexCCWPoly_of_ccwConvexSeven hccw u z hzu hzu1)

lemma unmarked_c_witness_of_firesW0 {P : Set (ℝ × ℝ)} {S : Fin 7 → ℝ × ℝ} {w : Finset (Fin 7) → ℝ × ℝ}
    (hP : ShatteredSimplePolygon P S w)
    (hA : PolygonCore.interiorPoints S = ∅) (hH : PolygonCore.certifiedSet P S w = ∅)
    {p a b : Fin 7} {Ty : Finset (Fin 7)}
    (hf : FiresW0 P S w p a b) (hab_Ty : {a, b} ⊆ Ty) (hp_not : p ∉ Ty) :
    ∃ c ∈ Ty, c ≠ p ∧ orientSign (S p) (S c) (w Ty) = intrinsicPol S w p := by
  rcases hf with ⟨_, g, c, _, hpair, hfo⟩
  have hpD : p ∈ PolygonCore.hullVertices S \ PolygonCore.certifiedSet P S w := by
    rw [hH]
    have hB : PolygonCore.hullVertices S = Finset.univ := by
      ext x; simp only [Finset.mem_univ, iff_true]
      by_contra hx
      have hxA : x ∈ PolygonCore.interiorPoints S := Finset.mem_sdiff.mpr ⟨Finset.mem_univ x, hx⟩
      rw [hA] at hxA; exact Finset.notMem_empty x hxA
    simp [hB]
  have hgc_Ty : {g, c} ⊆ Ty := hpair.symm ▸ hab_Ty
  have hc_Ty : c ∈ Ty := hgc_Ty (by simp)
  have hcp : c ≠ p := fun e => hp_not (e ▸ hc_Ty)
  exact ⟨c, hc_Ty, hcp, fires_unmarked_c_sign hP (by decide : 3 ≤ 7) hfo hpD hgc_Ty hp_not⟩

lemma vc_extremum_orient_and_ne {P : Set (ℝ × ℝ)} {S : Fin 7 → ℝ × ℝ} {w : Finset (Fin 7) → ℝ × ℝ}
    (_hP : ShatteredSimplePolygon P S w)
    {Tv : Finset (Fin 7)} (vc : VisibleContour (m := 4) S (w Tv)) (s : Bool) :
    let t_ext : Fin 7 := if s then vc.i_min else vc.i_max
    (∀ z : Fin 7, z ≠ t_ext → orientSign (w Tv) (S t_ext) (S z) = s) ∧
    (∀ m c : Fin 7, c ≠ m → orientSign (S m) (S c) (w Tv) = !s → t_ext ≠ m) := by
  intro t_ext
  have hor : ∀ z : Fin 7, z ≠ t_ext → orientSign (w Tv) (S t_ext) (S z) = s := by
    intro z hz
    cases hs : s
    · have hzt : z ≠ vc.i_max := by dsimp [t_ext] at hz; rwa [hs] at hz
      have hlt : vc.slope z < vc.slope vc.i_max :=
        lt_of_le_of_ne (vc.h_extrema z).2 (fun h => hzt (vc.h_slope_inj h))
      have hpos : 0 < orient2D (w Tv) (S z) (S vc.i_max) := (vc.h_orient z vc.i_max).mpr hlt
      have hneg : orient2D (w Tv) (S vc.i_max) (S z) < 0 := by rw [orient2D_swap23]; linarith
      dsimp [t_ext]; rw [hs]
      exact (orientSign_eq_false_iff _ _ _).mpr (le_of_lt hneg)
    · have hzt : z ≠ vc.i_min := by dsimp [t_ext] at hz; rwa [hs] at hz
      have hlt : vc.slope vc.i_min < vc.slope z :=
        lt_of_le_of_ne (vc.h_extrema z).1 (fun h => hzt (vc.h_slope_inj h.symm))
      have hpos : 0 < orient2D (w Tv) (S vc.i_min) (S z) := (vc.h_orient vc.i_min z).mpr hlt
      dsimp [t_ext]; rw [hs]
      exact (orientSign_eq_true_iff _ _ _).mpr hpos
  refine ⟨hor, fun m c hcm hmc heq => ?_⟩
  have h1 : orientSign (w Tv) (S t_ext) (S c) = s := hor c (heq ▸ hcm)
  rw [heq, orientSign_cycle2 (S m) (S c) (w Tv), hmc] at h1
  exact bool_ne_not h1.symm

private lemma not_chord_face_of_uncut_all_true {P : Set (ℝ × ℝ)} {S : Fin 7 → ℝ × ℝ}
    {w : Finset (Fin 7) → ℝ × ℝ} (hP : ShatteredSimplePolygon P S w)
    {Tv : Finset (Fin 7)} (hTv : Tv ≠ Finset.univ)
    {a b : Fin 7} {s₁ : Bool}
    (hlo : 2 ≤ (b - a).val) (hhi : (b - a).val ≤ 5)
    (hall_t : ∀ u : Fin 7, orientSign (S u) (S (u + 1)) (w Tv) = true)
    (huncut : ∀ x : Fin 7, (x - a).val ≤ (b - a).val → orientSign (w Tv) (w Finset.univ) (S x) = s₁) :
    orientSign (S a) (S b) (w Tv) = true := by
  by_contra hnf
  obtain ⟨hab_ne, hcases⟩ := chain_len25_tri_props a b hlo hhi
  have hab_neg : orient2D (S a) (S b) (w Tv) < 0 :=
    (orientSign_eq_false_iff_of_ne_zero (orient_S_S_w_ne hP hab_ne Tv)).mp (Bool.eq_false_iff.mpr hnf)
  have hba_pos : 0 < orient2D (S b) (S a) (w Tv) := by rw [orient2D_swap12]; linarith
  have ht : ∀ u : Fin 7, 0 < orient2D (S u) (S (u + 1)) (w Tv) := fun u =>
    (orientSign_eq_true_iff _ _ _).mp (hall_t u)
  have hs0 := huncut a (by simp)
  have hsb := huncut b le_rfl
  rcases hcases with ⟨_, he2, hle1⟩ | ⟨_, he3, hne2, hle1, hle2⟩ |
    ⟨_, he4, hne2, hne3, hle1, hle2, hle3⟩ |
    ⟨_, he5, hne2, hne3, hne4, hle1, hle2, hle3, hle4⟩
  · have t1 := ht (a + 1); rw [he2] at t1
    exact not_in_tri_of_same_line_side hP hTv hs0 (huncut (a + 1) hle1) hsb ⟨ht a, t1, hba_pos⟩
  · have t2 := ht (a + 1 + 1); rw [he3] at t2
    by_cases hd2 : 0 < orient2D (S a) (S (a + 1 + 1)) (w Tv)
    · exact not_in_tri_of_same_line_side hP hTv hs0 (huncut (a + 1 + 1) hle2) hsb ⟨hd2, t2, hba_pos⟩
    · have hd2' : 0 < orient2D (S (a + 1 + 1)) (S a) (w Tv) := by
        rw [orient2D_swap12]; linarith [lt_of_le_of_ne (not_lt.mp hd2) (orient_S_S_w_ne hP hne2 Tv)]
      exact not_in_tri_of_same_line_side hP hTv hs0 (huncut (a + 1) hle1) (huncut (a + 1 + 1) hle2)
        ⟨ht a, ht (a + 1), hd2'⟩
  · have t3 := ht (a + 1 + 1 + 1); rw [he4] at t3
    by_cases hd2 : 0 < orient2D (S a) (S (a + 1 + 1)) (w Tv)
    · by_cases hd3 : 0 < orient2D (S a) (S (a + 1 + 1 + 1)) (w Tv)
      · exact not_in_tri_of_same_line_side hP hTv hs0 (huncut (a + 1 + 1 + 1) hle3) hsb
          ⟨hd3, t3, hba_pos⟩
      · have hd3' : 0 < orient2D (S (a + 1 + 1 + 1)) (S a) (w Tv) := by
          rw [orient2D_swap12]; linarith [lt_of_le_of_ne (not_lt.mp hd3) (orient_S_S_w_ne hP hne3 Tv)]
        exact not_in_tri_of_same_line_side hP hTv hs0 (huncut (a + 1 + 1) hle2)
          (huncut (a + 1 + 1 + 1) hle3) ⟨hd2, ht (a + 1 + 1), hd3'⟩
    · have hd2' : 0 < orient2D (S (a + 1 + 1)) (S a) (w Tv) := by
        rw [orient2D_swap12]; linarith [lt_of_le_of_ne (not_lt.mp hd2) (orient_S_S_w_ne hP hne2 Tv)]
      exact not_in_tri_of_same_line_side hP hTv hs0 (huncut (a + 1) hle1) (huncut (a + 1 + 1) hle2)
        ⟨ht a, ht (a + 1), hd2'⟩
  · have t4 := ht (a + 1 + 1 + 1 + 1); rw [he5] at t4
    by_cases hd2 : 0 < orient2D (S a) (S (a + 1 + 1)) (w Tv)
    · by_cases hd3 : 0 < orient2D (S a) (S (a + 1 + 1 + 1)) (w Tv)
      · by_cases hd4 : 0 < orient2D (S a) (S (a + 1 + 1 + 1 + 1)) (w Tv)
        · exact not_in_tri_of_same_line_side hP hTv hs0 (huncut (a + 1 + 1 + 1 + 1) hle4) hsb
            ⟨hd4, t4, hba_pos⟩
        · have hd4' : 0 < orient2D (S (a + 1 + 1 + 1 + 1)) (S a) (w Tv) := by
            rw [orient2D_swap12]; linarith [lt_of_le_of_ne (not_lt.mp hd4) (orient_S_S_w_ne hP hne4 Tv)]
          exact not_in_tri_of_same_line_side hP hTv hs0 (huncut (a + 1 + 1 + 1) hle3)
            (huncut (a + 1 + 1 + 1 + 1) hle4) ⟨hd3, ht (a + 1 + 1 + 1), hd4'⟩
      · have hd3' : 0 < orient2D (S (a + 1 + 1 + 1)) (S a) (w Tv) := by
          rw [orient2D_swap12]; linarith [lt_of_le_of_ne (not_lt.mp hd3) (orient_S_S_w_ne hP hne3 Tv)]
        exact not_in_tri_of_same_line_side hP hTv hs0 (huncut (a + 1 + 1) hle2)
          (huncut (a + 1 + 1 + 1) hle3) ⟨hd2, ht (a + 1 + 1), hd3'⟩
    · have hd2' : 0 < orient2D (S (a + 1 + 1)) (S a) (w Tv) := by
        rw [orient2D_swap12]; linarith [lt_of_le_of_ne (not_lt.mp hd2) (orient_S_S_w_ne hP hne2 Tv)]
      exact not_in_tri_of_same_line_side hP hTv hs0 (huncut (a + 1) hle1) (huncut (a + 1 + 1) hle2)
        ⟨ht a, ht (a + 1), hd2'⟩

private lemma iota_chains_structure {P : Set (ℝ × ℝ)} {S : Fin 7 → ℝ × ℝ} {w : Finset (Fin 7) → ℝ × ℝ}
    (hP : ShatteredSimplePolygon P S w) (hccw : CCWConvexSeven S)
    (hA : PolygonCore.interiorPoints S = ∅) (hH : PolygonCore.certifiedSet P S w = ∅)
    (ι : Fin 7) :
    ((∀ u : Fin 7, orientSign (S u) (S (u + 1)) (w (V_alt ι)) = true) ∧
      (∀ t1 t2 : Fin 3, t1 ≠ t2 →
        ChainGood S (w (V_alt ι)) (chainEndpoints ι t1).1 (chainEndpoints ι t1).2 ∨
        ChainGood S (w (V_alt ι)) (chainEndpoints ι t2).1 (chainEndpoints ι t2).2)) ∨
    (∃ (vc : VisibleContour (m := 4) S (w (V_alt ι))) (tag_bad : Fin 3),
      let ab := (chainEndpoints ι tag_bad).1
      let bb := (chainEndpoints ι tag_bad).2
      (vc.i_min - ab).val = (vc.i_max - ab).val + vc.d_near ∧
      (vc.i_max - ab).val < (bb - ab).val ∧
      (vc.i_min - ab).val ≤ (bb - ab).val ∧
      (∀ u : Fin 7, orientSign (S u) (S (u + 1)) (w (V_alt ι)) = false ↔
        (vc.i_max - ab).val ≤ (u - ab).val ∧ (u - ab).val < (vc.i_min - ab).val) ∧
      (∀ c d : Fin 7, c ≠ d → (bb - ab).val ≤ (c - ab).val →
        (c - ab).val + (d - c).val ≤ 7 →
        orientSign (S c) (S d) (w (V_alt ι)) = true) ∧
      ChainGood S (w (V_alt ι)) (chainEndpoints ι (tag_bad + 1)).1 (chainEndpoints ι (tag_bad + 1)).2 ∧
      ChainGood S (w (V_alt ι)) (chainEndpoints ι (tag_bad + 2)).1 (chainEndpoints ι (tag_bad + 2)).2) := by
  by_cases hall_t : ∀ u : Fin 7, orientSign (S u) (S (u + 1)) (w (V_alt ι)) = true
  · left
    refine ⟨hall_t, fun t1 t2 h12 => ?_⟩
    by_contra hneither; push Not at hneither
    have hf1 : orientSign (S (chainEndpoints ι t1).1) (S (chainEndpoints ι t1).2) (w (V_alt ι)) = false := by
      cases h : orientSign (S (chainEndpoints ι t1).1) (S (chainEndpoints ι t1).2) (w (V_alt ι))
      · rfl
      · have hb1 : orientSign (S ((chainEndpoints ι t1).2 - 1)) (S (chainEndpoints ι t1).2) (w (V_alt ι)) = true := by
          have h0 := hall_t ((chainEndpoints ι t1).2 - 1); rwa [sub_add_cancel] at h0
        exact False.elim (hneither.1 ⟨hall_t _, hb1, h⟩)
    have hf2 : orientSign (S (chainEndpoints ι t2).1) (S (chainEndpoints ι t2).2) (w (V_alt ι)) = false := by
      cases h : orientSign (S (chainEndpoints ι t2).1) (S (chainEndpoints ι t2).2) (w (V_alt ι))
      · rfl
      · have hb2 : orientSign (S ((chainEndpoints ι t2).2 - 1)) (S (chainEndpoints ι t2).2) (w (V_alt ι)) = true := by
          have h0 := hall_t ((chainEndpoints ι t2).2 - 1); rwa [sub_add_cancel] at h0
        exact False.elim (hneither.2 ⟨hall_t _, hb2, h⟩)
    rcases iota_two_bad_share ι t1 t2 h12 with ⟨heq, c1, c2⟩ | ⟨heq, c1, c2⟩
    · have mp := valt_missed_props ι t1
      have hf2' : orientSign (S (chainEndpoints ι t1).2) (S (chainEndpoints ι t2).2) (w (V_alt ι)) = false := by
        rwa [← heq] at hf2
      exact c4_chord_wedge_excl hP hccw hA hH mp.2.2.2.1 mp.2.2.2.2.1 mp.2.2.2.2.2.1 c1 c2 ⟨hf1, hf2'⟩
    · have mp := valt_missed_props ι t2
      have hf1' : orientSign (S (chainEndpoints ι t2).2) (S (chainEndpoints ι t1).2) (w (V_alt ι)) = false := by
        rwa [← heq] at hf1
      exact c4_chord_wedge_excl hP hccw hA hH mp.2.2.2.1 mp.2.2.2.2.1 mp.2.2.2.2.2.1 c1 c2 ⟨hf2, hf1'⟩
  · right
    push Not at hall_t
    rcases hall_t with ⟨u₀, hu₀⟩
    have hf0 : orientSign (S u₀) (S (u₀ + 1)) (w (V_alt ι)) = false :=
      Bool.eq_false_iff.mpr hu₀
    obtain ⟨vc⟩ := exists_vc_of_facing_edge hP hccw hf0
    obtain ⟨tag_bad, hmax_in⟩ := iota_partition_edge ι vc.i_max
    let ab := (chainEndpoints ι tag_bad).1
    let bb := (chainEndpoints ι tag_bad).2
    have mp := valt_missed_props ι tag_bad
    have hno_b : ∀ k : ℕ, 0 < k → k < vc.d_near → finShift vc.i_max k ≠ bb := by
      intro k hk0 hk_lt heq_b
      have hf_prev : orientSign (S (bb - 1)) (S bb) (w (V_alt ι)) = false := by
        have h1 : finShift vc.i_max (k - 1) = bb - 1 := by
          have := finShift_pred (by decide : 2 ≤ 7) vc.i_max (k - 1)
          rw [Nat.sub_add_cancel hk0, heq_b] at this
          exact this.symm
        have hneg := (vc.h_near_face (k - 1) (by omega)).1
        rw [← finShift_succ (by decide : 2 ≤ 7), h1, sub_add_cancel] at hneg
        exact (orientSign_eq_false_iff _ _ _).mpr (le_of_lt hneg)
      have hf_next : orientSign (S bb) (S (bb + 1)) (w (V_alt ι)) = false := by
        have hneg := (vc.h_near_face k hk_lt).1
        rw [← finShift_succ (by decide : 2 ≤ 7), heq_b] at hneg
        exact (orientSign_eq_false_iff _ _ _).mpr (le_of_lt hneg)
      exact c4_missed_neighbors hP hccw hA hH mp.2.2.2.1 mp.2.2.2.2.1 mp.2.2.2.2.2.1 ⟨hf_prev, hf_next⟩
    obtain ⟨heq_d, hmin_le, hface_iff, hfar_chords⟩ := vc_confined_to_chain hP vc hmax_in hno_b
    have hnf := iota_next_chains_far ι tag_bad
    have hg1 : ChainGood S (w (V_alt ι)) (chainEndpoints ι (tag_bad + 1)).1 (chainEndpoints ι (tag_bad + 1)).2 := by
      have ht := hnf.2.2.2.2.2.2.2.2.2.1 (tag_bad + 1) (by simp)
      exact ⟨hfar_chords _ _ ht.1 ht.2.2.2.1 ht.2.2.2.2.1,
        hfar_chords _ _ ht.2.1 ht.2.2.2.2.2.1 ht.2.2.2.2.2.2.1,
        hfar_chords _ _ ht.2.2.1 ht.2.2.2.2.2.2.2.1 ht.2.2.2.2.2.2.2.2⟩
    have hg2 : ChainGood S (w (V_alt ι)) (chainEndpoints ι (tag_bad + 2)).1 (chainEndpoints ι (tag_bad + 2)).2 := by
      have ht := hnf.2.2.2.2.2.2.2.2.2.1 (tag_bad + 2) (by simp)
      exact ⟨hfar_chords _ _ ht.1 ht.2.2.2.1 ht.2.2.2.2.1,
        hfar_chords _ _ ht.2.1 ht.2.2.2.2.2.1 ht.2.2.2.2.2.2.1,
        hfar_chords _ _ ht.2.2.1 ht.2.2.2.2.2.2.2.1 ht.2.2.2.2.2.2.2.2⟩
    exact ⟨vc, tag_bad, heq_d, hmax_in, hmin_le, hface_iff, hfar_chords, hg1, hg2⟩

private lemma uncut_chain_good_iota {P : Set (ℝ × ℝ)} {S : Fin 7 → ℝ × ℝ} {w : Finset (Fin 7) → ℝ × ℝ}
    (hP : ShatteredSimplePolygon P S w) (hccw : CCWConvexSeven S)
    (hA : PolygonCore.interiorPoints S = ∅) (hH : PolygonCore.certifiedSet P S w = ∅)
    {ι : Fin 7} {tag : Fin 3} {s : Bool}
    (huncut : ∀ x : Fin 7, (x - (chainEndpoints ι tag).1).val ≤
      ((chainEndpoints ι tag).2 - (chainEndpoints ι tag).1).val →
      orientSign (w (V_alt ι)) (w Finset.univ) (S x) = s)
    (hz : ∃ z : Fin 7, orientSign (w (V_alt ι)) (w Finset.univ) (S z) = !s) :
    ChainGood S (w (V_alt ι)) (chainEndpoints ι tag).1 (chainEndpoints ι tag).2 := by
  have hTv : V_alt ι ≠ Finset.univ := valt_ne_univ ι
  have mp := valt_missed_props ι tag
  rcases iota_chains_structure hP hccw hA hH ι with ⟨hall_t, _⟩ |
    ⟨vc, tag_bad, _, hmax, hmin, _, _, hg1, hg2⟩
  · have hb_edge : orientSign (S ((chainEndpoints ι tag).2 - 1)) (S (chainEndpoints ι tag).2) (w (V_alt ι)) = true := by
      have h0 := hall_t ((chainEndpoints ι tag).2 - 1); rwa [sub_add_cancel] at h0
    exact ⟨hall_t _, hb_edge,
      not_chord_face_of_uncut_all_true hP hTv
        mp.2.2.2.2.2.2.2.2.2.1 (le_trans mp.2.2.2.2.2.2.2.2.2.2.1 (by decide)) hall_t huncut⟩
  · by_cases h_eq : tag = tag_bad
    · exfalso
      subst h_eq
      rcases hz with ⟨z, hz_s⟩
      have hmax_s := huncut vc.i_max (le_of_lt hmax)
      have hmin_s := huncut vc.i_min hmin
      have hz_s' := vc_all_side_of_tangents hP hTv vc hmax_s hmin_s z
      rw [hz_s'] at hz_s
      exact bool_ne_not hz_s
    · rcases fin3_ne_succ_or_add2 tag tag_bad h_eq with rfl | rfl
      · exact hg1
      · exact hg2

private lemma fire_iota_chain_of_good {P : Set (ℝ × ℝ)} {S : Fin 7 → ℝ × ℝ} {w : Finset (Fin 7) → ℝ × ℝ}
    (hP : ShatteredSimplePolygon P S w) (hccw : CCWConvexSeven S)
    {ι : Fin 7} {tag : Fin 3} {s : Bool}
    (hgood : ChainGood S (w (V_alt ι)) (chainEndpoints ι tag).1 (chainEndpoints ι tag).2)
    (huncut : ∀ x : Fin 7, (x - (chainEndpoints ι tag).1).val ≤
      ((chainEndpoints ι tag).2 - (chainEndpoints ι tag).1).val →
      orientSign (w (V_alt ι)) (w Finset.univ) (S x) = s)
    (hiv : (∃ s₂ ∈ V_alt ι, orientSign (w (V_alt ι)) (w Finset.univ) (S s₂) = !s) ∨
      (∃ ie ∈ V_alt ι, orientSign (w (V_alt ι)) (w Finset.univ) (S ie) = s ∧
        orientSign (w (V_alt ι)) (S ie)
          (S (if s then (chainEndpoints ι tag).1 else (chainEndpoints ι tag).2)) = s)) :
    IotaFiresChain P S w ι tag s := by
  let a := (chainEndpoints ι tag).1
  let b := (chainEndpoints ι tag).2
  have mp := valt_missed_props ι tag
  have ha0 : (a - a).val ≤ (b - a).val := by rw [sub_self]; exact Nat.zero_le _
  refine ⟨huncut a ha0, huncut b le_rfl, fun p hp1 hp2 => ?_⟩
  have hp_in : p ∈ V_alt ι := mp.2.2.2.2.2.2.2.2.2.2.2.1 p hp1 hp2
  have hs_p : orientSign (w (V_alt ι)) (w Finset.univ) (S p) = s := huncut p (le_of_lt hp2)
  have hfo := chainGood_firesOrdered hP hccw hgood mp.1 mp.2.2.2.1 hp_in hp1 hp2
    (huncut a ha0) hs_p (huncut b le_rfl) hiv
  have hpol : intrinsicPol S w p = s :=
    (fires_intrinsic_pol_and_signs hP hfo).1.symm.trans hs_p
  have hpair : ({if s then a else b, if s then b else a} : Finset (Fin 7)) = {a, b} := by
    cases s <;> [exact Finset.pair_comm b a; rfl]
  exact ⟨⟨V_alt ι, _, _, Or.inr ⟨ι, rfl⟩, hpair, hfo⟩, hpol, hs_p⟩

/-- **Lemma 3.5 (`alt_witness_dichotomy`)**:
    Every `w (V_alt ι)` (`ι : Fin 7`) satisfies either Branch 1 (`IotaFiresChain`) or
    Branch 2 (`IotaEscapes`). -/
theorem alt_witness_dichotomy {P : Set (ℝ × ℝ)} {S : Fin 7 → ℝ × ℝ} {w : Finset (Fin 7) → ℝ × ℝ}
    (hP : ShatteredSimplePolygon P S w) (hccw : CCWConvexSeven S)
    (hA : PolygonCore.interiorPoints S = ∅) (hH : PolygonCore.certifiedSet P S w = ∅)
    (ι : Fin 7) :
    (∃ (tag : Fin 3) (s : Bool), IotaFiresChain P S w ι tag s) ∨
    (∃ (tag_adj : Fin 3) (s : Bool), IotaEscapes P S w ι tag_adj s) := by
  let Tv := V_alt ι
  have hTv : Tv ≠ Finset.univ := valt_ne_univ ι
  by_cases hall_same : ∃ s : Bool, ∀ z : Fin 7, orientSign (w Tv) (w Finset.univ) (S z) = s
  · left
    rcases hall_same with ⟨s, hall⟩
    obtain ⟨i₀, hf0⟩ := exists_facing_edge_of_all_same_side hP hTv hall
    rcases iota_chains_structure hP hccw hA hH ι with ⟨ht_all, _⟩ |
      ⟨vc, tag_bad, _, _, _, _, hfar, hg1, hg2⟩
    · rw [ht_all i₀] at hf0; exact Bool.noConfusion hf0
    · have hnf := iota_next_chains_far ι tag_bad
      cases s
      · refine ⟨tag_bad + 1, false, fire_iota_chain_of_good hP hccw hg1 (fun x _ => hall x) (Or.inr ?_)⟩
        let a2 := (chainEndpoints ι (tag_bad + 2)).1
        refine ⟨a2 + 1, hnf.2.2.2.2.1, hall _, ?_⟩
        simp only [Bool.false_eq_true, ↓reduceIte]
        rw [hnf.2.1]
        have hf_a2 := hfar a2 (a2 + 1) hnf.2.2.2.2.2.2.2.2.2.2.2.1.1
          hnf.2.2.2.2.2.2.2.2.2.2.2.1.2.1 hnf.2.2.2.2.2.2.2.2.2.2.2.1.2.2
        have h1 : orientSign (w (V_alt ι)) (S a2) (S (a2 + 1)) = true := by
          rw [orientSign_cycle2 (S a2) (S (a2 + 1)) (w (V_alt ι)), hf_a2]
        rw [orientSign_swap23 (orient_w_S_S_ne hP Tv hnf.2.2.2.2.2.2.2.2.2.2.2.1.1), h1]; rfl
      · refine ⟨tag_bad + 2, true, fire_iota_chain_of_good hP hccw hg2 (fun x _ => hall x) (Or.inr ?_)⟩
        let a1 := (chainEndpoints ι (tag_bad + 1)).1
        let b1 := (chainEndpoints ι (tag_bad + 1)).2
        refine ⟨a1 + 1, hnf.2.2.2.1, hall _, ?_⟩
        simp only [↓reduceIte]
        rw [← hnf.2.1]
        have hf_a1 := hfar (a1 + 1) b1 hnf.2.2.2.2.2.2.2.2.2.2.1.1
          hnf.2.2.2.2.2.2.2.2.2.2.1.2.1 hnf.2.2.2.2.2.2.2.2.2.2.1.2.2
        rw [orientSign_cycle2 (S (a1 + 1)) (S b1) (w (V_alt ι)), hf_a1]
  · push Not at hall_same
    obtain ⟨tag_star, s, ha_s, hb_s⟩ : ∃ (tag_star : Fin 3) (s : Bool),
        orientSign (w Tv) (w Finset.univ) (S (chainEndpoints ι tag_star).1) = s ∧
        orientSign (w Tv) (w Finset.univ) (S (chainEndpoints ι tag_star).2) = s := by
      cases h0 : orientSign (w Tv) (w Finset.univ) (S ι) <;>
        cases h2 : orientSign (w Tv) (w Finset.univ) (S (ι + 2)) <;>
        cases h4 : orientSign (w Tv) (w Finset.univ) (S (ι + 4))
      · exact ⟨0, false, h0, h2⟩
      · exact ⟨0, false, h0, h2⟩
      · exact ⟨2, false, h4, h0⟩
      · exact ⟨1, true, h2, h4⟩
      · exact ⟨1, false, h2, h4⟩
      · exact ⟨2, true, h4, h0⟩
      · exact ⟨0, true, h0, h2⟩
      · exact ⟨0, true, h0, h2⟩
    let as_ := (chainEndpoints ι tag_star).1
    let bs_ := (chainEndpoints ι tag_star).2
    have mp := valt_missed_props ι tag_star
    obtain ⟨z_opp, hz_opp⟩ : ∃ z : Fin 7, orientSign (w Tv) (w Finset.univ) (S z) = !s := by
      obtain ⟨z, hz⟩ := hall_same s
      exact ⟨z, by cases h : orientSign (w Tv) (w Finset.univ) (S z) <;> cases hs_b : s <;>
        first | rfl | exact False.elim (hz (hs_b ▸ h))⟩
    by_cases h_in_opp : ∃ p : Fin 7, 0 < (p - as_).val ∧ (p - as_).val < (bs_ - as_).val ∧
        orientSign (w Tv) (w Finset.univ) (S p) = !s
    · left
      rcases h_in_opp with ⟨p₀, hp1, hp2, hp_opp⟩
      have hp0_in : p₀ ∈ Tv := mp.2.2.2.2.2.2.2.2.2.2.2.1 p₀ hp1 hp2
      have h_out_s : ∀ z : Fin 7, (bs_ - as_).val ≤ (z - as_).val →
          orientSign (w Tv) (w Finset.univ) (S z) = s := by
        intro z hz_ge
        by_cases hza : z = as_
        · rwa [hza]
        · by_cases hzb : z = bs_
          · rwa [hzb]
          · by_contra hne
            have hz_ns : orientSign (w Tv) (w Finset.univ) (S z) = !s := by
              cases h : orientSign (w Tv) (w Finset.univ) (S z) <;> cases hs_b : s <;>
                first | rfl | exact False.elim (hne (hs_b ▸ h))
            have hlt_zb : (bs_ - as_).val < (z - as_).val :=
              lt_of_le_of_ne hz_ge (fun hv => hzb (sub_left_injective (Fin.ext hv)).symm)
            exact quad_line_sep_false hP hccw hTv hp1 hp2 hlt_zb ha_s hb_s hp_opp hz_ns
      have h_other_good : ChainGood S (w Tv) (chainEndpoints ι (tag_star + 1)).1 (chainEndpoints ι (tag_star + 1)).2 ∨
          ChainGood S (w Tv) (chainEndpoints ι (tag_star + 2)).1 (chainEndpoints ι (tag_star + 2)).2 := by
        rcases iota_chains_structure hP hccw hA hH ι with ⟨_, htwo⟩ | ⟨_, tb, _, _, _, _, _, g1, g2⟩
        · exact htwo (tag_star + 1) (tag_star + 2) (fin3_add1_ne_add2 tag_star)
        · rcases fin3_add_overlap tag_star tb with e | e | e | e <;>
            [left; left; right; right] <;> rwa [e]
      have h_sub_out := iota_other_chains_outside ι tag_star
      rcases h_other_good with hg1 | hg2
      · refine ⟨tag_star + 1, s, fire_iota_chain_of_good hP hccw hg1 ?_ (Or.inl ⟨p₀, hp0_in, hp_opp⟩)⟩
        intro x hx
        rcases h_sub_out (tag_star + 1) (by simp) x hx with rfl | hge
        · exact ha_s
        · exact h_out_s x hge
      · refine ⟨tag_star + 2, s, fire_iota_chain_of_good hP hccw hg2 ?_ (Or.inl ⟨p₀, hp0_in, hp_opp⟩)⟩
        intro x hx
        rcases h_sub_out (tag_star + 2) (by simp) x hx with rfl | hge
        · exact ha_s
        · exact h_out_s x hge
    · push Not at h_in_opp
      have huncut_star : ∀ x : Fin 7, (x - as_).val ≤ (bs_ - as_).val →
          orientSign (w Tv) (w Finset.univ) (S x) = s := by
        intro x hx
        by_cases hxa : x = as_
        · rwa [hxa]
        · by_cases hxb : x = bs_
          · rwa [hxb]
          · have h1 : 0 < (x - as_).val :=
              Nat.pos_of_ne_zero (fun hz => hxa (sub_eq_zero.mp (Fin.ext hz)))
            have h2 : (x - as_).val < (bs_ - as_).val :=
              lt_of_le_of_ne hx (fun hv => hxb (sub_left_injective (Fin.ext hv)))
            cases hsx : orientSign (w Tv) (w Finset.univ) (S x) <;> cases s <;>
              first | rfl | exact False.elim (h_in_opp x h1 h2 hsx)
      have hgood_star := uncut_chain_good_iota hP hccw hA hH huncut_star ⟨z_opp, hz_opp⟩
      by_cases h_seen_opp : ∃ s₂ ∈ Tv, orientSign (w Tv) (w Finset.univ) (S s₂) = !s
      · exact Or.inl ⟨tag_star, s, fire_iota_chain_of_good hP hccw hgood_star huncut_star (Or.inl h_seen_opp)⟩
      · push Not at h_seen_opp
        let m := chainOppositeMissed ι tag_star
        have hall_but_m : ∀ v : Fin 7, v ≠ m → orientSign (w Tv) (w Finset.univ) (S v) = s := by
          intro v hvm
          rcases mp.2.2.2.2.2.2.2.2.2.2.2.2.1 v with hv_in | hv_ch | rfl
          · cases h : orientSign (w Tv) (w Finset.univ) (S v) <;> cases hs_b : s <;>
              first | rfl | exact False.elim (h_seen_opp v hv_in (hs_b ▸ h))
          · exact huncut_star v hv_ch
          · exact False.elim (hvm rfl)
        have hm_opp : orientSign (w Tv) (w Finset.univ) (S m) = !s := by
          by_cases hzm : z_opp = m
          · rwa [← hzm]
          · rw [hall_but_m z_opp hzm] at hz_opp
            exact False.elim (bool_ne_not hz_opp)
        let g := if s then as_ else bs_
        let tag_adj := if s then tag_star - 1 else tag_star + 1
        let aa := (chainEndpoints ι tag_adj).1
        let ba := (chainEndpoints ι tag_adj).2
        let u_adj := if s then g - 1 else g + 1
        have hadj := iota_adj_escape_geom ι tag_star s
        by_cases h_fire_u : orientSign (w Tv) (S u_adj) (S g) = s
        · exact Or.inl ⟨tag_star, s, fire_iota_chain_of_good hP hccw hgood_star huncut_star
            (Or.inr ⟨u_adj, hadj.2.2.1, hall_but_m u_adj hadj.2.2.2.1, h_fire_u⟩)⟩
        · right
          refine ⟨tag_adj, s, ?_⟩
          have hm_eq : (if s then aa else ba) = m := by
            cases hs_b : s
            · exact (hadj.2.1.1 hs_b).2
            · exact (hadj.2.1.2 hs_b).1
          have hcstep := iota_chain_step_props ι tag_adj
          have hab_ne : aa ≠ ba := hcstep.1
          have hba_pos : 0 < (ba - aa).val := by
            have := (valt_missed_props ι tag_adj).2.2.2.2.2.2.2.2.2.1; omega
          have hedge_face : ∃ u_e : Fin 7, (u_e - aa).val < (ba - aa).val ∧
              orientSign (S u_e) (S (u_e + 1)) (w Tv) = false := by
            cases hs_b : s
            · have hu_t : orientSign (w Tv) (S (g + 1)) (S g) = true := by
                dsimp [u_adj] at h_fire_u; rw [hs_b] at h_fire_u
                exact Bool.eq_true_of_not_eq_false h_fire_u
              have hgf : orientSign (S g) (S (g + 1)) (w Tv) = false := by
                have h1 : orientSign (S (g + 1)) (S g) (w Tv) = true := by
                  rw [← orientSign_cycle2 (S (g + 1)) (S g) (w Tv), hu_t]
                rw [orientSign_swap12 (orient_S_S_w_ne hP (fin7_ne_succ' g).symm Tv), h1]; rfl
              have haa_g : aa = g := (hadj.2.1.1 hs_b).1
              exact ⟨aa, by rw [sub_self]; exact hba_pos, haa_g ▸ hgf⟩
            · have hu_f : orientSign (w Tv) (S (g - 1)) (S g) = false := by
                dsimp [u_adj] at h_fire_u; rw [hs_b] at h_fire_u
                exact Bool.eq_false_iff.mpr h_fire_u
              have hgf : orientSign (S (g - 1)) (S g) (w Tv) = false := by
                rw [← orientSign_cycle2 (S (g - 1)) (S g) (w Tv), hu_f]
              have hba_g : ba = g := (hadj.2.1.2 hs_b).2
              refine ⟨ba - 1, hcstep.2.1, ?_⟩
              rw [sub_add_cancel, hba_g]; exact hgf
          rcases hedge_face with ⟨u_e, hue_in, hue_f⟩
          rcases iota_chains_structure hP hccw hA hH ι with ⟨ht_all, _⟩ |
            ⟨vc, tag_bad, _, hmax_in, hmin_le, hface_iff, _, _, _⟩
          · rw [ht_all u_e] at hue_f; exact Bool.noConfusion hue_f
          · have hue_tb_lt : (u_e - (chainEndpoints ι tag_bad).1).val <
                ((chainEndpoints ι tag_bad).2 - (chainEndpoints ι tag_bad).1).val :=
              lt_of_lt_of_le ((hface_iff u_e).mp hue_f).2 hmin_le
            have htb_eq : tag_bad = tag_adj :=
              iota_unique_edge_tag ι tag_bad tag_adj u_e hue_tb_lt hue_in
            subst htb_eq
            have hor_m : (vc.i_max : Fin 7) = m ∨ (vc.i_min : Fin 7) = m := by
              by_contra hnot; push Not at hnot
              have hm_s := vc_all_side_of_tangents hP hTv vc
                (hall_but_m vc.i_max hnot.1) (hall_but_m vc.i_min hnot.2) m
              rw [hm_s] at hm_opp
              exact bool_ne_not hm_opp
            have hexact_ends : (vc.i_max : Fin 7) = aa ∧ (vc.i_min : Fin 7) = ba := by
              cases hs_b : s
              · have haa_g : aa = g := (hadj.2.1.1 hs_b).1
                have hba_m : ba = m := (hadj.2.1.1 hs_b).2
                have hu_t : orientSign (w Tv) (S (g + 1)) (S g) = true := by
                  dsimp [u_adj] at h_fire_u; rw [hs_b] at h_fire_u
                  exact Bool.eq_true_of_not_eq_false h_fire_u
                have hgf : orientSign (S aa) (S (aa + 1)) (w Tv) = false := by
                  have h1 : orientSign (S (g + 1)) (S g) (w Tv) = true := by
                    rw [← orientSign_cycle2 (S (g + 1)) (S g) (w Tv), hu_t]
                  rw [haa_g, orientSign_swap12 (orient_S_S_w_ne hP (fin7_ne_succ' g).symm Tv), h1]; rfl
                have hle0 : ((vc.i_max : Fin 7) - aa).val ≤ (aa - aa).val := ((hface_iff aa).mp hgf).1
                simp only [sub_self, Fin.val_zero, Nat.le_zero] at hle0
                have himax_aa : (vc.i_max : Fin 7) = aa := sub_eq_zero.mp (Fin.ext hle0)
                have himax_ne_m : (vc.i_max : Fin 7) ≠ m := by rw [himax_aa, ← hba_m]; exact hab_ne
                have himin_ba : (vc.i_min : Fin 7) = ba :=
                  (hor_m.resolve_left himax_ne_m).trans hba_m.symm
                exact ⟨himax_aa, himin_ba⟩
              · have haa_m : aa = m := (hadj.2.1.2 hs_b).1
                have hba_g : ba = g := (hadj.2.1.2 hs_b).2
                have hu_f : orientSign (w Tv) (S (g - 1)) (S g) = false := by
                  dsimp [u_adj] at h_fire_u; rw [hs_b] at h_fire_u
                  exact Bool.eq_false_iff.mpr h_fire_u
                have hgf : orientSign (S (ba - 1)) (S ((ba - 1) + 1)) (w Tv) = false := by
                  rw [sub_add_cancel, hba_g, ← orientSign_cycle2 (S (g - 1)) (S g) (w Tv), hu_f]
                have hlt_min : ((ba - 1) - aa).val < ((vc.i_min : Fin 7) - aa).val :=
                  ((hface_iff (ba - 1)).mp hgf).2
                have hmin_le' : ((vc.i_min : Fin 7) - aa).val ≤ (ba - aa).val := hmin_le
                have hge_min : (ba - aa).val ≤ ((vc.i_min : Fin 7) - aa).val :=
                  hcstep.2.2 ▸ Nat.succ_le_of_lt hlt_min
                have hmin_val : ((vc.i_min : Fin 7) - aa).val = (ba - aa).val :=
                  Nat.le_antisymm hmin_le' hge_min
                have himin_ba : (vc.i_min : Fin 7) = ba := sub_left_injective (Fin.ext hmin_val)
                have himin_ne_m : (vc.i_min : Fin 7) ≠ m := by rw [himin_ba, ← haa_m]; exact hab_ne.symm
                have himax_aa : (vc.i_max : Fin 7) = aa :=
                  (hor_m.resolve_right himin_ne_m).trans haa_m.symm
                exact ⟨himax_aa, himin_ba⟩
            have hf_v_all : ∀ u : Fin 7, (u - aa).val < (ba - aa).val →
                orientSign (S u) (S (u + 1)) (w Tv) = false := by
              intro u hu
              apply (hface_iff u).mpr
              change ((vc.i_max : Fin 7) - aa).val ≤ (u - aa).val ∧
                (u - aa).val < ((vc.i_min : Fin 7) - aa).val
              rw [hexact_ends.1, hexact_ends.2, sub_self]
              exact ⟨Nat.zero_le _, hu⟩
            have hchord_f : orientSign (S aa) (S ba) (w Tv) = false :=
              facing_arc_chord_false hP hccw hba_pos hf_v_all
            have hvba_pos : 0 < orient2D (w Tv) (S ba) (S aa) := by
              have hneg := (orientSign_eq_false_iff_of_ne_zero (orient_S_S_w_ne hP hab_ne Tv)).mp hchord_f
              have hid : orient2D (w Tv) (S ba) (S aa) = -orient2D (S aa) (S ba) (w Tv) := by
                unfold orient2D; ring
              linarith
            have haa_sign : orientSign (w Tv) (w Finset.univ) (S aa) = false := by
              cases hs_b : s
              · have haa_g : aa = g := (hadj.2.1.1 hs_b).1
                have hba_m : ba = m := (hadj.2.1.1 hs_b).2
                have hne : aa ≠ m := hba_m ▸ hab_ne
                rw [hall_but_m aa hne, hs_b]
              · have haa_m : aa = m := (hadj.2.1.2 hs_b).1
                rw [haa_m, hm_opp, hs_b]; rfl
            have hba_sign : orientSign (w Tv) (w Finset.univ) (S ba) = true := by
              cases hs_b : s
              · have hba_m : ba = m := (hadj.2.1.1 hs_b).2
                rw [hba_m, hm_opp, hs_b]; rfl
              · have haa_m : aa = m := (hadj.2.1.2 hs_b).1
                have hne : ba ≠ m := haa_m ▸ hab_ne.symm
                rw [hall_but_m ba hne, hs_b]
            have hda_neg : orient2D (w Tv) (w Finset.univ) (S aa) < 0 :=
              (orientSign_eq_false_iff_of_ne_zero (orient_w_w_S_ne hP hTv aa)).mp haa_sign
            have hdb_pos : 0 < orient2D (w Tv) (w Finset.univ) (S ba) :=
              (orientSign_eq_true_iff _ _ _).mp hba_sign
            have hwba_pos : 0 < orient2D (w Finset.univ) (S ba) (S aa) := by
              have hid : orient2D (w Finset.univ) (S ba) (S aa) =
                  orient2D (w Tv) (S ba) (S aa) + orient2D (w Tv) (w Finset.univ) (S ba) -
                  orient2D (w Tv) (w Finset.univ) (S aa) := by
                unfold orient2D; ring
              linarith
            dsimp only [IotaEscapes]
            refine ⟨by rw [hm_eq]; exact hm_opp, fun v hv => hall_but_m v (hm_eq ▸ hv), fun u hu => ?_⟩
            have hfv := hf_v_all u hu
            have huv_neg : orient2D (S u) (S (u + 1)) (w Tv) < 0 :=
              (orientSign_eq_false_iff_of_ne_zero (orient_S_S_w_ne hP (fin7_ne_succ' u) Tv)).mp hfv
            have hua_nn := hull_edge_orient_nonneg hccw u aa
            have hub_nn := hull_edge_orient_nonneg hccw u ba
            have hcramer : orient2D (w Tv) (S ba) (S aa) * orient2D (S u) (S (u + 1)) (w Finset.univ) =
                orient2D (w Finset.univ) (S ba) (S aa) * orient2D (S u) (S (u + 1)) (w Tv) +
                orient2D (w Tv) (w Finset.univ) (S aa) * orient2D (S u) (S (u + 1)) (S ba) -
                orient2D (w Tv) (w Finset.univ) (S ba) * orient2D (S u) (S (u + 1)) (S aa) := by
              unfold orient2D; ring
            have huw_neg : orient2D (S u) (S (u + 1)) (w Finset.univ) < 0 := by nlinarith
            exact ⟨hfv, (orientSign_eq_false_iff _ _ _).mpr (le_of_lt huw_neg)⟩

/-! ### Master Law I (`Lemma 3.6`) and Master Law II (`Lemma 3.7`) -/

private lemma miss2_chains_structure {P : Set (ℝ × ℝ)} {S : Fin 7 → ℝ × ℝ} {w : Finset (Fin 7) → ℝ × ℝ}
    (hP : ShatteredSimplePolygon P S w) (hccw : CCWConvexSeven S)
    (hA : PolygonCore.interiorPoints S = ∅) (hH : PolygonCore.certifiedSet P S w = ∅)
    {p q : Fin 7} (hlo : 2 ≤ (q - p).val) (hhi : (q - p).val ≤ 3) :
    let Tv := T_miss2 p q
    (∀ u : Fin 7, orientSign (S u) (S (u + 1)) (w Tv) = true) ∨
    (∃ vc : VisibleContour (m := 4) S (w Tv),
      (((vc.i_max - p).val < (q - p).val ∧ (vc.i_min - p).val ≤ (q - p).val ∧
        ChainGood S (w Tv) q p) ∨
       ((vc.i_max - q).val < (p - q).val ∧ (vc.i_min - q).val ≤ (p - q).val ∧
        ChainGood S (w Tv) p q))) := by
  intro Tv
  have mp := nonadj_miss2_props p q hlo (le_trans hhi (by decide))
  have sp := miss2_short_long_props p q hlo hhi
  by_cases hall_t : ∀ u : Fin 7, orientSign (S u) (S (u + 1)) (w Tv) = true
  · exact Or.inl hall_t
  · right
    push Not at hall_t
    rcases hall_t with ⟨u₀, hu₀⟩
    obtain ⟨vc⟩ := exists_vc_of_facing_edge hP hccw (Bool.eq_false_iff.mpr hu₀)
    refine ⟨vc, ?_⟩
    rcases mp.2.2.2.2.2.2.2.2.1 vc.i_max with hmax_pq | hmax_qp
    · left
      have hno_q : ∀ k : ℕ, 0 < k → k < vc.d_near → finShift vc.i_max k ≠ q := by
        intro k hk0 hk_lt heq_q
        have hf_prev : orientSign (S (q - 1)) (S q) (w Tv) = false := by
          have h1 : finShift vc.i_max (k - 1) = q - 1 := by
            have := finShift_pred (by decide : 2 ≤ 7) vc.i_max (k - 1)
            rw [Nat.sub_add_cancel hk0, heq_q] at this; exact this.symm
          have hneg := (vc.h_near_face (k - 1) (by omega)).1
          rw [← finShift_succ (by decide : 2 ≤ 7), h1, sub_add_cancel] at hneg
          exact (orientSign_eq_false_iff _ _ _).mpr (le_of_lt hneg)
        have hf_next : orientSign (S q) (S (q + 1)) (w Tv) = false := by
          have hneg := (vc.h_near_face k hk_lt).1
          rw [← finShift_succ (by decide : 2 ≤ 7), heq_q] at hneg
          exact (orientSign_eq_false_iff _ _ _).mpr (le_of_lt hneg)
        exact c4_missed_neighbors hP hccw hA hH mp.2.2.1 mp.2.2.2.2.2.1 mp.2.2.2.2.2.2.1 ⟨hf_prev, hf_next⟩
      obtain ⟨_, hmin_le, _, hfar⟩ := vc_confined_to_chain hP vc hmax_pq hno_q
      have g_qp := sp.2.2.2.2.2.2.2.1
      exact ⟨hmax_pq, hmin_le,
        hfar q (q + 1) g_qp.1 g_qp.2.2.2.1 g_qp.2.2.2.2.1,
        hfar (p - 1) p g_qp.2.1 g_qp.2.2.2.2.2.1 g_qp.2.2.2.2.2.2.1,
        hfar q p g_qp.2.2.1 g_qp.2.2.2.1 g_qp.2.2.2.2.2.2.2⟩
    · right
      have hno_p : ∀ k : ℕ, 0 < k → k < vc.d_near → finShift vc.i_max k ≠ p := by
        intro k hk0 hk_lt heq_p
        have hf_prev : orientSign (S (p - 1)) (S p) (w Tv) = false := by
          have h1 : finShift vc.i_max (k - 1) = p - 1 := by
            have := finShift_pred (by decide : 2 ≤ 7) vc.i_max (k - 1)
            rw [Nat.sub_add_cancel hk0, heq_p] at this; exact this.symm
          have hneg := (vc.h_near_face (k - 1) (by omega)).1
          rw [← finShift_succ (by decide : 2 ≤ 7), h1, sub_add_cancel] at hneg
          exact (orientSign_eq_false_iff _ _ _).mpr (le_of_lt hneg)
        have hf_next : orientSign (S p) (S (p + 1)) (w Tv) = false := by
          have hneg := (vc.h_near_face k hk_lt).1
          rw [← finShift_succ (by decide : 2 ≤ 7), heq_p] at hneg
          exact (orientSign_eq_false_iff _ _ _).mpr (le_of_lt hneg)
        exact c4_missed_neighbors hP hccw hA hH mp.2.1 mp.2.2.2.1 mp.2.2.2.2.1 ⟨hf_prev, hf_next⟩
      obtain ⟨_, hmin_le, _, hfar⟩ := vc_confined_to_chain hP vc hmax_qp hno_p
      have g_pq := sp.2.2.2.2.2.2.1
      exact ⟨hmax_qp, hmin_le,
        hfar p (p + 1) g_pq.1 g_pq.2.2.2.1 g_pq.2.2.2.2.1,
        hfar (q - 1) q g_pq.2.1 g_pq.2.2.2.2.2.1 g_pq.2.2.2.2.2.2.1,
        hfar p q g_pq.2.2.1 g_pq.2.2.2.1 g_pq.2.2.2.2.2.2.2⟩

/-- **Lemma 3.6 (`master_law_I` — Double-Miss Propagation)**:
    Let `p, q : Fin 7` satisfy `2 ≤ (q - p).val ∧ (q - p).val ≤ 3` (so `[p .. q]` is the shorter
    hull chain between non-adjacent `p` and `q`). If `p ← {a_p, b_p}` and `q ← {a_q, b_q}` with
    `q ∉ {a_p, b_p}`, `p ∉ {a_q, b_q}`, and `intrinsicPol S w p = s`, `intrinsicPol S w q = s`,
    then every inner vertex `r` of `[p .. q]` (`0 < (r - p).val < (q - p).val`) satisfies
    `FiresW0 P S w r p q ∧ intrinsicPol S w r = !s`. -/
theorem master_law_I {P : Set (ℝ × ℝ)} {S : Fin 7 → ℝ × ℝ} {w : Finset (Fin 7) → ℝ × ℝ}
    (hP : ShatteredSimplePolygon P S w) (hccw : CCWConvexSeven S)
    (hA : PolygonCore.interiorPoints S = ∅) (hH : PolygonCore.certifiedSet P S w = ∅)
    {p q a_p b_p a_q b_q : Fin 7} {s : Bool}
    (hqp_lo : 2 ≤ (q - p).val) (hqp_hi : (q - p).val ≤ 3)
    (hfp : FiresW0 P S w p a_p b_p) (hfq : FiresW0 P S w q a_q b_q)
    (hq_not_abp : q ∉ ({a_p, b_p} : Finset (Fin 7)))
    (hp_not_abq : p ∉ ({a_q, b_q} : Finset (Fin 7)))
    (hpol_p : intrinsicPol S w p = s) (hpol_q : intrinsicPol S w q = s) :
    ∀ r : Fin 7, 0 < (r - p).val → (r - p).val < (q - p).val →
      FiresW0 P S w r p q ∧ intrinsicPol S w r = !s := by
  let Tv := T_miss2 p q
  have mp := nonadj_miss2_props p q hqp_lo (le_trans hqp_hi (by decide))
  have sp := miss2_short_long_props p q hqp_lo hqp_hi
  have hpq : p ≠ q := mp.1
  have hTv : Tv ≠ Finset.univ := tmiss2_ne_univ p q
  have hW0 : IsW0Set Tv := tmiss2_isW0 hpq
  have nep := firesW0_ne hfp
  have neq := firesW0_ne hfq
  have ha_p_Tv : a_p ∈ Tv :=
    mp.2.2.2.2.2.2.2.1 a_p nep.1.symm (fun e => hq_not_abp (by rw [e]; simp))
  have hb_p_Tv : b_p ∈ Tv :=
    mp.2.2.2.2.2.2.2.1 b_p nep.2.1.symm (fun e => hq_not_abp (by rw [e]; simp))
  have habp_Tv : ({a_p, b_p} : Finset (Fin 7)) ⊆ Tv := by
    intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> assumption
  have ha_q_Tv : a_q ∈ Tv :=
    mp.2.2.2.2.2.2.2.1 a_q (fun e => hp_not_abq (by rw [e]; simp)) neq.1.symm
  have hb_q_Tv : b_q ∈ Tv :=
    mp.2.2.2.2.2.2.2.1 b_q (fun e => hp_not_abq (by rw [e]; simp)) neq.2.1.symm
  have habq_Tv : ({a_q, b_q} : Finset (Fin 7)) ⊆ Tv := by
    intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> assumption
  have hp_ns : orientSign (w Tv) (w Finset.univ) (S p) = !s := by
    rw [← hpol_p]; exact law_05_star_sign hP hfp habp_Tv mp.2.1
  have hq_ns : orientSign (w Tv) (w Finset.univ) (S q) = !s := by
    rw [← hpol_q]; exact law_05_star_sign hP hfq habq_Tv mp.2.2.1
  -- Helper: firing `[p .. q]` on side `!s` proves the goal
  have fire_pq : ChainGood S (w Tv) p q →
      (∀ x : Fin 7, (x - p).val ≤ (q - p).val → orientSign (w Tv) (w Finset.univ) (S x) = !s) →
      ((∃ s₂ ∈ Tv, orientSign (w Tv) (w Finset.univ) (S s₂) = !(!s)) ∨
       (∃ ie ∈ Tv, orientSign (w Tv) (w Finset.univ) (S ie) = !s ∧
         orientSign (w Tv) (S ie) (S (if !s then p else q)) = !s)) →
      ∀ r : Fin 7, 0 < (r - p).val → (r - p).val < (q - p).val →
        FiresW0 P S w r p q ∧ intrinsicPol S w r = !s := by
    intro hgood huncut hiv r hr1 hr2
    have hrp : r ≠ p := fun e => by subst e; simp at hr1
    have hrq : r ≠ q := fun e => by subst e; omega
    have hr_Tv : r ∈ Tv := mp.2.2.2.2.2.2.2.1 r hrp hrq
    have hs_r := huncut r (le_of_lt hr2)
    have hfo := chainGood_firesOrdered hP hccw hgood mp.2.1 mp.2.2.1 hr_Tv hr1 hr2
      hp_ns hs_r hq_ns hiv
    have hpol_r : intrinsicPol S w r = !s :=
      (fires_intrinsic_pol_and_signs hP hfo).1.symm.trans hs_r
    have hpair : ({if !s then p else q, if !s then q else p} : Finset (Fin 7)) = {p, q} := by
      cases s <;> [rfl; exact Finset.pair_comm q p]
    exact ⟨⟨Tv, _, _, hW0, hpair, hfo⟩, hpol_r⟩
  -- Helper: `[q .. p]` cannot fire (`q + 1, q + 2, q + 3` violate `firesW0_capacity_le_two`)
  have no_fire_qp : ChainGood S (w Tv) q p →
      (∀ x : Fin 7, (x - q).val ≤ (p - q).val → orientSign (w Tv) (w Finset.univ) (S x) = !s) →
      ((∃ s₂ ∈ Tv, orientSign (w Tv) (w Finset.univ) (S s₂) = !(!s)) ∨
       (∃ ie ∈ Tv, orientSign (w Tv) (w Finset.univ) (S ie) = !s ∧
         orientSign (w Tv) (S ie) (S (if !s then q else p)) = !s)) → False := by
    intro hgood huncut hiv
    have mk_r : ∀ r : Fin 7, 0 < (r - q).val → (r - q).val < (p - q).val → FiresW0 P S w r q p := by
      intro r hr1 hr2
      have hrq : r ≠ q := fun e => by subst e; simp at hr1
      have hrp : r ≠ p := fun e => by subst e; omega
      have hr_Tv : r ∈ Tv := mp.2.2.2.2.2.2.2.1 r hrp hrq
      have hfo := chainGood_firesOrdered hP hccw hgood mp.2.2.1 mp.2.1 hr_Tv hr1 hr2
        hq_ns (huncut r (le_of_lt hr2)) hp_ns hiv
      have hpair : ({if !s then q else p, if !s then p else q} : Finset (Fin 7)) = {q, p} := by
        cases s <;> [rfl; exact Finset.pair_comm p q]
      exact ⟨Tv, _, _, hW0, hpair, hfo⟩
    exact firesW0_capacity_le_two hP sp.2.2.1.1 sp.2.2.1.2.1 sp.2.2.1.2.2
      (mk_r (q + 1) sp.2.2.2.1.1 sp.2.2.2.1.2)
      (mk_r (q + 2) sp.2.2.2.2.1.1 sp.2.2.2.2.1.2)
      (mk_r (q + 3) sp.2.2.2.2.2.1.1 sp.2.2.2.2.2.1.2)
  by_cases hz_opp : ∃ z : Fin 7, orientSign (w Tv) (w Finset.univ) (S z) = s
  · rcases hz_opp with ⟨z₀, hz₀⟩
    have hz_in : z₀ ∈ Tv := by
      refine mp.2.2.2.2.2.2.2.1 z₀ (fun e => ?_) (fun e => ?_)
      · rw [e, hp_ns] at hz₀; exact bool_ne_not hz₀.symm
      · rw [e, hq_ns] at hz₀; exact bool_ne_not hz₀.symm
    have hz_nns : orientSign (w Tv) (w Finset.univ) (S z₀) = !(!s) := by
      rw [Bool.not_not]; exact hz₀
    by_cases h_pq_opp : ∃ r₁ : Fin 7, 0 < (r₁ - p).val ∧ (r₁ - p).val < (q - p).val ∧
        orientSign (w Tv) (w Finset.univ) (S r₁) = s
    · exfalso
      rcases h_pq_opp with ⟨r₁, hr1a, hr1b, hr1s⟩
      have huncut_qp : ∀ x : Fin 7, (x - q).val ≤ (p - q).val →
          orientSign (w Tv) (w Finset.univ) (S x) = !s := by
        intro x hx
        by_cases hxq : x = q
        · rwa [hxq]
        · by_cases hxp : x = p
          · rwa [hxp]
          · by_contra hne
            have hx_s : orientSign (w Tv) (w Finset.univ) (S x) = s := by
              cases h : orientSign (w Tv) (w Finset.univ) (S x) <;> cases hs_b : s <;>
                first | rfl | exact False.elim (hne (hs_b ▸ h))
            have hx1 : 0 < (x - q).val :=
              Nat.pos_of_ne_zero (fun hz => hxq (sub_eq_zero.mp (Fin.ext hz)))
            have hx2 : (x - q).val < (p - q).val :=
              lt_of_le_of_ne hx (fun hv => hxp (sub_left_injective (Fin.ext hv)))
            have hlt_xp := sp.2.2.2.2.2.2.2.2 r₁ x hr1a hr1b hx1 hx2
            have hr1_nns : orientSign (w Tv) (w Finset.univ) (S r₁) = !(!s) := by
              rw [Bool.not_not]; exact hr1s
            have hx_nns : orientSign (w Tv) (w Finset.univ) (S x) = !(!s) := by
              rw [Bool.not_not]; exact hx_s
            exact quad_line_sep_false hP hccw hTv hr1a hr1b hlt_xp hp_ns hq_ns hr1_nns hx_nns
      have hgood_qp : ChainGood S (w Tv) q p := by
        rcases miss2_chains_structure hP hccw hA hH hqp_lo hqp_hi with hall_t | ⟨vc, h_pq | h_qp⟩
        · have hp_edge : orientSign (S (p - 1)) (S p) (w Tv) = true := by
            have h0 := hall_t (p - 1); rwa [sub_add_cancel] at h0
          exact ⟨hall_t _, hp_edge,
            not_chord_face_of_uncut_all_true hP hTv
              (le_trans (by decide : 2 ≤ 4) sp.1) sp.2.1 hall_t huncut_qp⟩
        · exact h_pq.2.2
        · exfalso
          have h1 := huncut_qp vc.i_max (le_of_lt h_qp.1)
          have h2 := huncut_qp vc.i_min h_qp.2.1
          have hz_ns := vc_all_side_of_tangents hP hTv vc h1 h2 z₀
          rw [hz_ns] at hz₀
          exact bool_ne_not hz₀.symm
      exact no_fire_qp hgood_qp huncut_qp (Or.inl ⟨z₀, hz_in, hz_nns⟩)
    · push Not at h_pq_opp
      have huncut_pq : ∀ x : Fin 7, (x - p).val ≤ (q - p).val →
          orientSign (w Tv) (w Finset.univ) (S x) = !s := by
        intro x hx
        by_cases hxp : x = p
        · rwa [hxp]
        · by_cases hxq : x = q
          · rwa [hxq]
          · have hx1 : 0 < (x - p).val :=
              Nat.pos_of_ne_zero (fun hz => hxp (sub_eq_zero.mp (Fin.ext hz)))
            have hx2 : (x - p).val < (q - p).val :=
              lt_of_le_of_ne hx (fun hv => hxq (sub_left_injective (Fin.ext hv)))
            cases hsx : orientSign (w Tv) (w Finset.univ) (S x) <;> cases hs_b : s <;>
              first | rfl | exact False.elim (h_pq_opp x hx1 hx2 (hs_b ▸ hsx))
      have hgood_pq : ChainGood S (w Tv) p q := by
        rcases miss2_chains_structure hP hccw hA hH hqp_lo hqp_hi with hall_t | ⟨vc, h_pq | h_qp⟩
        · have hq_edge : orientSign (S (q - 1)) (S q) (w Tv) = true := by
            have h0 := hall_t (q - 1); rwa [sub_add_cancel] at h0
          exact ⟨hall_t _, hq_edge,
            not_chord_face_of_uncut_all_true hP hTv
              hqp_lo (le_trans hqp_hi (by decide)) hall_t huncut_pq⟩
        · exfalso
          have h1 := huncut_pq vc.i_max (le_of_lt h_pq.1)
          have h2 := huncut_pq vc.i_min h_pq.2.1
          have hz_ns := vc_all_side_of_tangents hP hTv vc h1 h2 z₀
          rw [hz_ns] at hz₀
          exact bool_ne_not hz₀.symm
        · exact h_qp.2.2
      exact fire_pq hgood_pq huncut_pq (Or.inl ⟨z₀, hz_in, hz_nns⟩)
  · push Not at hz_opp
    have hall_ns : ∀ z : Fin 7, orientSign (w Tv) (w Finset.univ) (S z) = !s := fun z => by
      cases h : orientSign (w Tv) (w Finset.univ) (S z) <;> cases hs_b : s <;>
        first | rfl | exact False.elim (hz_opp z (hs_b ▸ h))
    obtain ⟨i₀, hf0⟩ := exists_facing_edge_of_all_same_side hP hTv hall_ns
    rcases miss2_chains_structure hP hccw hA hH hqp_lo hqp_hi with hall_t | ⟨vc, h_pq | h_qp⟩
    · rw [hall_t i₀] at hf0; exact False.elim (Bool.noConfusion hf0)
    · exfalso
      obtain ⟨cp, _, hcp_ne, hcp_s⟩ := unmarked_c_witness_of_firesW0 hP hA hH hfp habp_Tv mp.2.1
      obtain ⟨cq, _, hcq_ne, hcq_s⟩ := unmarked_c_witness_of_firesW0 hP hA hH hfq habq_Tv mp.2.2.1
      have ⟨hor, hne_ext⟩ := vc_extremum_orient_and_ne hP vc (!s)
      let t_ext : Fin 7 := if !s then vc.i_min else vc.i_max
      have hcp_s' : orientSign (S p) (S cp) (w Tv) = !(!s) := by
        rw [Bool.not_not, ← hpol_p]; exact hcp_s
      have hcq_s' : orientSign (S q) (S cq) (w Tv) = !(!s) := by
        rw [Bool.not_not, ← hpol_q]; exact hcq_s
      have ht_ne_p : t_ext ≠ p := hne_ext p cp hcp_ne hcp_s'
      have ht_ne_q : t_ext ≠ q := hne_ext q cq hcq_ne hcq_s'
      have ht_Tv : t_ext ∈ Tv := mp.2.2.2.2.2.2.2.1 t_ext ht_ne_p ht_ne_q
      have ht_ne_targ : (if !s then q else p) ≠ t_ext := by
        cases s <;> [exact ht_ne_q.symm; exact ht_ne_p.symm]
      exact no_fire_qp h_pq.2.2 (fun x _ => hall_ns x)
        (Or.inr ⟨t_ext, ht_Tv, hall_ns t_ext, hor _ ht_ne_targ⟩)
    · obtain ⟨cp, _, hcp_ne, hcp_s⟩ := unmarked_c_witness_of_firesW0 hP hA hH hfp habp_Tv mp.2.1
      obtain ⟨cq, _, hcq_ne, hcq_s⟩ := unmarked_c_witness_of_firesW0 hP hA hH hfq habq_Tv mp.2.2.1
      have ⟨hor, hne_ext⟩ := vc_extremum_orient_and_ne hP vc (!s)
      let t_ext : Fin 7 := if !s then vc.i_min else vc.i_max
      have hcp_s' : orientSign (S p) (S cp) (w Tv) = !(!s) := by
        rw [Bool.not_not, ← hpol_p]; exact hcp_s
      have hcq_s' : orientSign (S q) (S cq) (w Tv) = !(!s) := by
        rw [Bool.not_not, ← hpol_q]; exact hcq_s
      have ht_ne_p : t_ext ≠ p := hne_ext p cp hcp_ne hcp_s'
      have ht_ne_q : t_ext ≠ q := hne_ext q cq hcq_ne hcq_s'
      have ht_Tv : t_ext ∈ Tv := mp.2.2.2.2.2.2.2.1 t_ext ht_ne_p ht_ne_q
      have ht_ne_targ : (if !s then p else q) ≠ t_ext := by
        cases s <;> [exact ht_ne_p.symm; exact ht_ne_q.symm]
      exact fire_pq h_qp.2.2 (fun x _ => hall_ns x)
        (Or.inr ⟨t_ext, ht_Tv, hall_ns t_ext, hor _ ht_ne_targ⟩)

/-- **Lemma 3.7 (`master_law_II` — Triple-Miss Second-Chain Forcing)**:
    If `w (V_alt ι)` fires chain `tag₁` with sign `s`, and the opposite missed vertex
    `m₃ = chainOppositeMissed ι tag₁` satisfies `FiresW0 P S w m₃ a₃ b₃` with
    `{a₃, b₃} ⊆ V_alt ι` and `intrinsicPol S w m₃ = !s`, then `w (V_alt ι)` also fires
    a second chain `tag₂ ≠ tag₁` with sign `s`. -/
theorem master_law_II {P : Set (ℝ × ℝ)} {S : Fin 7 → ℝ × ℝ} {w : Finset (Fin 7) → ℝ × ℝ}
    (hP : ShatteredSimplePolygon P S w) (hccw : CCWConvexSeven S)
    (hA : PolygonCore.interiorPoints S = ∅) (hH : PolygonCore.certifiedSet P S w = ∅)
    {ι : Fin 7} {tag₁ : Fin 3} {s : Bool} {a₃ b₃ : Fin 7}
    (hf1 : IotaFiresChain P S w ι tag₁ s)
    (hfm3 : FiresW0 P S w (chainOppositeMissed ι tag₁) a₃ b₃)
    (hab3 : ({a₃, b₃} : Finset (Fin 7)) ⊆ V_alt ι)
    (hpol3 : intrinsicPol S w (chainOppositeMissed ι tag₁) = !s) :
    ∃ tag₂ : Fin 3, tag₂ ≠ tag₁ ∧ IotaFiresChain P S w ι tag₂ s := by
  let Tv := V_alt ι
  have hTv : Tv ≠ Finset.univ := valt_ne_univ ι
  let m₁ := (chainEndpoints ι tag₁).1
  let m₂ := (chainEndpoints ι tag₁).2
  let m₃ := chainOppositeMissed ι tag₁
  have mp1 := valt_missed_props ι tag₁
  have mv := malt_valt_props ι
  have hm1_s : orientSign (w Tv) (w Finset.univ) (S m₁) = s := hf1.1
  have hm2_s : orientSign (w Tv) (w Finset.univ) (S m₂) = s := hf1.2.1
  have hm3_s : orientSign (w Tv) (w Finset.univ) (S m₃) = s := by
    have h := law_05_star_sign hP hfm3 hab3 mp1.2.2.2.2.2.2.1
    rw [hpol3, Bool.not_not] at h; exact h
  have hM_s : ∀ x ∈ M_alt ι, orientSign (w Tv) (w Finset.univ) (S x) = s := by
    intro x hx
    rcases mp1.2.2.2.2.2.2.2.2.2.2.2.2.1 x with hx_in | hx_ch | rfl
    · exact False.elim (mv.1 x hx hx_in)
    · by_cases hxm1 : x = m₁
      · rwa [hxm1]
      · by_cases hxm2 : x = m₂
        · rwa [hxm2]
        · have hx1 : 0 < (x - m₁).val :=
            Nat.pos_of_ne_zero (fun hz => hxm1 (sub_eq_zero.mp (Fin.ext hz)))
          have hx2 : (x - m₁).val < (m₂ - m₁).val :=
            lt_of_le_of_ne hx_ch (fun hv => hxm2 (sub_left_injective (Fin.ext hv)))
          exact (hf1.2.2 x hx1 hx2).2.2
    · exact hm3_s
  by_cases hz_opp : ∃ z : Fin 7, orientSign (w Tv) (w Finset.univ) (S z) = !s
  · rcases hz_opp with ⟨z₀, hz₀⟩
    have hz_in : z₀ ∈ Tv := by
      rcases mv.2.1 z₀ with hM | hV
      · rw [hM_s z₀ hM] at hz₀; exact False.elim (bool_ne_not hz₀)
      · exact hV
    have h_end_M := mv.2.2
    by_cases h_c1_opp : ∃ p₁ : Fin 7,
        0 < (p₁ - (chainEndpoints ι (tag₁ + 1)).1).val ∧
        (p₁ - (chainEndpoints ι (tag₁ + 1)).1).val <
          ((chainEndpoints ι (tag₁ + 1)).2 - (chainEndpoints ι (tag₁ + 1)).1).val ∧
        orientSign (w Tv) (w Finset.univ) (S p₁) = !s
    · rcases h_c1_opp with ⟨p₁, hp1a, hp1b, hp1_opp⟩
      have huncut_2 : ∀ x : Fin 7, (x - (chainEndpoints ι (tag₁ + 2)).1).val ≤
          ((chainEndpoints ι (tag₁ + 2)).2 - (chainEndpoints ι (tag₁ + 2)).1).val →
          orientSign (w Tv) (w Finset.univ) (S x) = s := by
        intro x hx
        let a2 := (chainEndpoints ι (tag₁ + 2)).1
        let b2 := (chainEndpoints ι (tag₁ + 2)).2
        by_cases hxa : x = a2
        · rw [hxa]; exact hM_s a2 (h_end_M (tag₁ + 2)).1
        · by_cases hxb : x = b2
          · rw [hxb]; exact hM_s b2 (h_end_M (tag₁ + 2)).2
          · by_contra hne
            have hx_opp : orientSign (w Tv) (w Finset.univ) (S x) = !s := by
              cases h : orientSign (w Tv) (w Finset.univ) (S x) <;> cases hs_b : s <;>
                first | rfl | exact False.elim (hne (hs_b ▸ h))
            have hx1 : 0 < (x - a2).val :=
              Nat.pos_of_ne_zero (fun hz => hxa (sub_eq_zero.mp (Fin.ext hz)))
            have hx2 : (x - a2).val < (b2 - a2).val :=
              lt_of_le_of_ne hx (fun hv => hxb (sub_left_injective (Fin.ext hv)))
            have hq := iota_law2_quad_sep ι tag₁ p₁ x hp1a hp1b hx1 hx2
            exact quad_line_sep_false hP hccw hTv hq.1 hq.2.1 hq.2.2.1
              (hM_s _ hq.2.2.2.1) (hM_s _ hq.2.2.2.2) hp1_opp hx_opp
      have hg2 := uncut_chain_good_iota hP hccw hA hH huncut_2 ⟨z₀, hz₀⟩
      exact ⟨tag₁ + 2, fin3_add2_ne_self tag₁,
        fire_iota_chain_of_good hP hccw hg2 huncut_2 (Or.inl ⟨z₀, hz_in, hz₀⟩)⟩
    · push Not at h_c1_opp
      have huncut_1 : ∀ x : Fin 7, (x - (chainEndpoints ι (tag₁ + 1)).1).val ≤
          ((chainEndpoints ι (tag₁ + 1)).2 - (chainEndpoints ι (tag₁ + 1)).1).val →
          orientSign (w Tv) (w Finset.univ) (S x) = s := by
        intro x hx
        let a1 := (chainEndpoints ι (tag₁ + 1)).1
        let b1 := (chainEndpoints ι (tag₁ + 1)).2
        by_cases hxa : x = a1
        · rw [hxa]; exact hM_s a1 (h_end_M (tag₁ + 1)).1
        · by_cases hxb : x = b1
          · rw [hxb]; exact hM_s b1 (h_end_M (tag₁ + 1)).2
          · have hx1 : 0 < (x - a1).val :=
              Nat.pos_of_ne_zero (fun hz => hxa (sub_eq_zero.mp (Fin.ext hz)))
            have hx2 : (x - a1).val < (b1 - a1).val :=
              lt_of_le_of_ne hx (fun hv => hxb (sub_left_injective (Fin.ext hv)))
            cases hsx : orientSign (w Tv) (w Finset.univ) (S x) <;> cases hs_b : s <;>
              first | rfl | exact False.elim (h_c1_opp x hx1 hx2 (hs_b ▸ hsx))
      have hg1 := uncut_chain_good_iota hP hccw hA hH huncut_1 ⟨z₀, hz₀⟩
      exact ⟨tag₁ + 1, fin3_add1_ne_self tag₁,
        fire_iota_chain_of_good hP hccw hg1 huncut_1 (Or.inl ⟨z₀, hz_in, hz₀⟩)⟩
  · push Not at hz_opp
    have hall : ∀ z : Fin 7, orientSign (w Tv) (w Finset.univ) (S z) = s := fun z => by
      cases h : orientSign (w Tv) (w Finset.univ) (S z) <;> cases hs_b : s <;>
        first | rfl | exact False.elim (hz_opp z (hs_b ▸ h))
    obtain ⟨i₀, hf0⟩ := exists_facing_edge_of_all_same_side hP hTv hall
    rcases iota_chains_structure hP hccw hA hH ι with ⟨ht_all, _⟩ |
      ⟨vc, tag_bad, heq_d, hmax_in, hmin_le, _, hfar, hg1, hg2⟩
    · rw [ht_all i₀] at hf0; exact False.elim (Bool.noConfusion hf0)
    · have hnf := iota_next_chains_far ι tag_bad
      obtain ⟨c₃, _, hc3_ne, hc3_s⟩ :=
        unmarked_c_witness_of_firesW0 hP hA hH hfm3 hab3 mp1.2.2.2.2.2.2.1
      let ab := (chainEndpoints ι tag_bad).1
      let bb := (chainEndpoints ι tag_bad).2
      have mp_bad := valt_missed_props ι tag_bad
      obtain rfl | rfl : s = false ∨ s = true := by cases s <;> simp
      · have ⟨hor, hne_ext⟩ := vc_extremum_orient_and_ne hP vc false
        have ht_ne_m3 : vc.i_max ≠ m₃ := hne_ext m₃ c₃ hc3_ne (hpol3 ▸ hc3_s)
        have hf_tb1 : IotaFiresChain P S w ι (tag_bad + 1) false := by
          refine fire_iota_chain_of_good hP hccw hg1 (fun x _ => hall x) (Or.inr ?_)
          let a2 := (chainEndpoints ι (tag_bad + 2)).1
          refine ⟨a2 + 1, hnf.2.2.2.2.1, hall _, ?_⟩
          simp only [Bool.false_eq_true, ↓reduceIte]
          rw [hnf.2.1]
          have hf_a2 := hfar a2 (a2 + 1) hnf.2.2.2.2.2.2.2.2.2.2.2.1.1
            hnf.2.2.2.2.2.2.2.2.2.2.2.1.2.1 hnf.2.2.2.2.2.2.2.2.2.2.2.1.2.2
          have h1 : orientSign (w (V_alt ι)) (S a2) (S (a2 + 1)) = true := by
            rw [orientSign_cycle2 (S a2) (S (a2 + 1)) (w (V_alt ι)), hf_a2]
          rw [orientSign_swap23 (orient_w_S_S_ne hP Tv hnf.2.2.2.2.2.2.2.2.2.2.2.1.1), h1]; rfl
        by_cases heq1 : tag_bad + 1 = tag₁
        · subst heq1
          have hm3_ab : m₃ = ab := hnf.2.2.2.2.2.2.2.2.2.2.2.2.2
          have himax_ne_ab : (vc.i_max : Fin 7) ≠ ab := hm3_ab ▸ ht_ne_m3
          have himax_pos : 0 < ((vc.i_max : Fin 7) - ab).val :=
            Nat.pos_of_ne_zero (fun hz => himax_ne_ab (sub_eq_zero.mp (Fin.ext hz)))
          have himax_Tv : (vc.i_max : Fin 7) ∈ Tv :=
            mp_bad.2.2.2.2.2.2.2.2.2.2.2.1 vc.i_max himax_pos hmax_in
          have hb2_eq : (chainEndpoints ι (tag_bad + 2)).2 = ab := hnf.2.2.1
          have hne_targ : (if false then (chainEndpoints ι (tag_bad + 2)).1
              else (chainEndpoints ι (tag_bad + 2)).2) ≠ vc.i_max := by
            simp only [Bool.false_eq_true, ↓reduceIte, hb2_eq]
            exact himax_ne_ab.symm
          exact ⟨tag_bad + 2, fin3_add2_ne_add1' tag_bad,
            fire_iota_chain_of_good hP hccw hg2 (fun x _ => hall x)
              (Or.inr ⟨vc.i_max, himax_Tv, hall vc.i_max, hor _ hne_targ⟩)⟩
        · exact ⟨tag_bad + 1, heq1, hf_tb1⟩
      · have ⟨hor, hne_ext⟩ := vc_extremum_orient_and_ne hP vc true
        have ht_ne_m3 : vc.i_min ≠ m₃ := hne_ext m₃ c₃ hc3_ne (hpol3 ▸ hc3_s)
        have hf_tb2 : IotaFiresChain P S w ι (tag_bad + 2) true := by
          refine fire_iota_chain_of_good hP hccw hg2 (fun x _ => hall x) (Or.inr ?_)
          let a1 := (chainEndpoints ι (tag_bad + 1)).1
          let b1 := (chainEndpoints ι (tag_bad + 1)).2
          refine ⟨a1 + 1, hnf.2.2.2.1, hall _, ?_⟩
          simp only [↓reduceIte]
          rw [← hnf.2.1]
          have hf_a1 := hfar (a1 + 1) b1 hnf.2.2.2.2.2.2.2.2.2.2.1.1
            hnf.2.2.2.2.2.2.2.2.2.2.1.2.1 hnf.2.2.2.2.2.2.2.2.2.2.1.2.2
          rw [orientSign_cycle2 (S (a1 + 1)) (S b1) (w (V_alt ι)), hf_a1]
        by_cases heq2 : tag_bad + 2 = tag₁
        · subst heq2
          have hm3_bb : m₃ = bb := hnf.2.2.2.2.2.2.2.2.2.2.2.2.1
          have himin_ne_bb : (vc.i_min : Fin 7) ≠ bb := hm3_bb ▸ ht_ne_m3
          have hd_pos := vc.hd_pos
          have heq_d' : ((vc.i_min : Fin 7) - ab).val = ((vc.i_max : Fin 7) - ab).val + vc.d_near :=
            heq_d
          have himin_pos : 0 < ((vc.i_min : Fin 7) - ab).val := by omega
          have himin_lt : ((vc.i_min : Fin 7) - ab).val < (bb - ab).val :=
            lt_of_le_of_ne hmin_le (fun hv => himin_ne_bb (sub_left_injective (Fin.ext hv)))
          have himin_Tv : (vc.i_min : Fin 7) ∈ Tv :=
            mp_bad.2.2.2.2.2.2.2.2.2.2.2.1 vc.i_min himin_pos himin_lt
          have ha1_eq : (chainEndpoints ι (tag_bad + 1)).1 = bb := hnf.1
          have hne_targ : (if true then (chainEndpoints ι (tag_bad + 1)).1
              else (chainEndpoints ι (tag_bad + 1)).2) ≠ vc.i_min := by
            simp only [↓reduceIte, ha1_eq]
            exact himin_ne_bb.symm
          exact ⟨tag_bad + 1, fin3_add1_ne_add2' tag_bad,
            fire_iota_chain_of_good hP hccw hg1 (fun x _ => hall x)
              (Or.inr ⟨vc.i_min, himin_Tv, hall vc.i_min, hor _ hne_targ⟩)⟩
        · exact ⟨tag_bad + 2, heq2, hf_tb2⟩

end VCDim6

end
