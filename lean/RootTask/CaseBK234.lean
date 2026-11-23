import RootTask.CaseBFace

open scoped BigOperators

noncomputable section

namespace CaseB

/-! ## Finite `Fin 5` Sum Bounds via `decide` -/

lemma fin5_k23_sum_le_30 :
    ∀ b : Fin 5 → Bool,
      ((Finset.univ.filter (fun i : Fin 5 => b i = true)).card = 2 ∨
       (Finset.univ.filter (fun i : Fin 5 => b i = true)).card = 3) →
      6 + ∑ i : Fin 5, ∑ j ∈ Finset.univ.filter (i < ·),
        (if b i = b j then (3 : ℕ) else 2) ≤ 30 := by
  decide

lemma fin5_k4_sum_max32 (i₀ : Fin 5) :
    6 + ∑ i : Fin 5, ∑ j ∈ Finset.univ.filter (i < ·),
      (if i = i₀ ∨ j = i₀ then (2 : ℕ) else 3) = 32 := by
  revert i₀; decide

lemma fin5_k4_sum_drop1 (i₀ j₁ : Fin 5) (hne : j₁ ≠ i₀) :
    6 + ∑ i : Fin 5, ∑ j ∈ Finset.univ.filter (i < ·),
      (if (i = i₀ ∧ j = j₁) ∨ (i = j₁ ∧ j = i₀) then (1 : ℕ)
       else if i = i₀ ∨ j = i₀ then 2 else 3) = 31 := by
  revert i₀ j₁ hne; decide

open scoped Classical

/-! ## Case B (`k ∈ {2, 3}`) Elimination -/

theorem caseB_k2_k3_elim {W : Fin 5 → OpenWedge} (hGP : GeneralPosition W)
    (pa pb : ℝ × ℝ)
    (h_apex : ∀ k : Fin 5, (W k).y.1 < 0 ∧ (W k).y.2 < 0)
    (hxa : 0 < pa.1) (hya : pa.2 < 0) (hxb : pb.1 < 0) (hyb : 0 < pb.2)
    (hC : pa.1 * pb.2 - pa.2 * pb.1 < 0)
    (ha : ∀ k : Fin 5, (W k).MemOpen pa) (hb : ∀ k : Fin 5, (W k).MemOpen pb)
    (h_masks : ∀ m : Fin 5 → Bool, ∃ p : ℝ × ℝ, inOmega p ∧ RealizesWedgeMask W m p)
    (hk23 : (Finset.univ.filter (fun i : Fin 5 => isLgt (W i) pa pb)).card = 2 ∨
            (Finset.univ.filter (fun i : Fin 5 => isLgt (W i) pa pb)).card = 3) :
    False := by
  let b : Fin 5 → Bool := fun i => decide (isLgt (W i) pa pb)
  have hb_filter : Finset.univ.filter (fun i : Fin 5 => b i = true) =
      Finset.univ.filter (fun i : Fin 5 => isLgt (W i) pa pb) := by
    ext i; simp [b]
  have hb_card : (Finset.univ.filter (fun i : Fin 5 => b i = true)).card = 2 ∨
      (Finset.univ.filter (fun i : Fin 5 => b i = true)).card = 3 := by
    rwa [hb_filter]
  have h_gt : ∀ i : Fin 5, b i = true → isLgt (W i) pa pb := fun i hi => by
    simpa [b] using hi
  have h_lt : ∀ i : Fin 5, b i = false → isLlt (W i) pa pb := fun i hi => by
    have hngt : ¬ isLgt (W i) pa pb := by simpa [b] using hi
    exact (caseB_dichotomy (W i) pa pb (h_apex i).1 (h_apex i).2
      hxa hya hxb hyb hC (ha i) (hb i)).resolve_right hngt
  have h_origin : ∀ i : Fin 5, b i = false → (W i).MemOpen (0, 0) := fun i hi =>
    case_b_origin_in_wedge (W i) pa pb (h_apex i).1 (h_apex i).2
      hxa hya hxb hyb hC (ha i) (hb i) (h_lt i hi)
  let U : Set (ℝ × ℝ) := {p : ℝ × ℝ | inOmega p} \ ⋃ j ∈ (Finset.univ : Finset (Fin 5)), Gamma (W j)
  have h_pair_bound : ∀ i j : Fin 5, i < j →
      (Gamma (W i) ∩ Gamma (W j)).ncard ≤ if b i = b j then 3 else 2 := by
    intro i j hij
    cases hbi : b i <;> cases hbj : b j
    · simp only [if_true]
      exact inter_card_le_three_of_origin hGP h_apex (ne_of_lt hij)
        (h_origin i hbi) (h_origin j hbj)
    · simp only [Bool.false_eq_true, if_false]
      exact inter_card_le_two_of_Llt_Lgt W pa pb h_apex hxa hya hxb hyb hC ha hb
        (h_lt i hbi) (h_gt j hbj)
    · simp only [Bool.true_eq_false, if_false]
      rw [Set.inter_comm]
      exact inter_card_le_two_of_Llt_Lgt W pa pb h_apex hxa hya hxb hyb hC ha hb
        (h_lt j hbj) (h_gt i hbi)
    · simp only [if_true]
      exact inter_card_le_three_of_Lgt hGP pa pb h_apex hxa hya hxb hyb hC ha hb
        (ne_of_lt hij) (h_gt i hbi) (h_gt j hbj)
  have h_upper : (Comps U).encard ≤ 30 := by
    have hbound := arr_comps_bound hGP h_apex Finset.univ
    have h_sum_nat : ∑ i : Fin 5, ∑ j ∈ (Finset.univ : Finset (Fin 5)).filter (i < ·),
          (Gamma (W i) ∩ Gamma (W j)).ncard ≤
        ∑ i : Fin 5, ∑ j ∈ Finset.univ.filter (i < ·),
          (if b i = b j then (3 : ℕ) else 2) := by
      refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j hj => ?_
      exact h_pair_bound i j (Finset.mem_filter.mp hj).2
    have h_sum_le : ∑ i : Fin 5, ∑ j ∈ (Finset.univ : Finset (Fin 5)).filter (i < ·),
          ((Gamma (W i) ∩ Gamma (W j)).ncard : ℕ∞) ≤
        ((∑ i : Fin 5, ∑ j ∈ Finset.univ.filter (i < ·),
          (if b i = b j then (3 : ℕ) else 2) : ℕ) : ℕ∞) := by
      calc ∑ i : Fin 5, ∑ j ∈ (Finset.univ : Finset (Fin 5)).filter (i < ·),
            ((Gamma (W i) ∩ Gamma (W j)).ncard : ℕ∞)
          = ((∑ i : Fin 5, ∑ j ∈ (Finset.univ : Finset (Fin 5)).filter (i < ·),
              (Gamma (W i) ∩ Gamma (W j)).ncard : ℕ) : ℕ∞) := by
            simp only [Nat.cast_sum]
        _ ≤ ((∑ i : Fin 5, ∑ j ∈ Finset.univ.filter (i < ·),
              (if b i = b j then (3 : ℕ) else 2) : ℕ) : ℕ∞) :=
            Nat.cast_le.mpr h_sum_nat
    have h30 := fin5_k23_sum_le_30 b hb_card
    calc (Comps U).encard
        ≤ 1 + ((Finset.univ : Finset (Fin 5)).card : ℕ∞) +
            ∑ i : Fin 5, ∑ j ∈ (Finset.univ : Finset (Fin 5)).filter (i < ·),
              ((Gamma (W i) ∩ Gamma (W j)).ncard : ℕ∞) := hbound
      _ ≤ (6 : ℕ∞) + ((∑ i : Fin 5, ∑ j ∈ Finset.univ.filter (i < ·),
            (if b i = b j then (3 : ℕ) else 2) : ℕ) : ℕ∞) := by
          refine add_le_add ?_ h_sum_le
          exact le_of_eq (by rw [Finset.card_fin]; norm_num)
      _ = ((6 + ∑ i : Fin 5, ∑ j ∈ Finset.univ.filter (i < ·),
            (if b i = b j then (3 : ℕ) else 2) : ℕ) : ℕ∞) := by push_cast; rfl
      _ ≤ 30 := Nat.cast_le.mpr h30
  have h_real_U : ∀ m : Fin 5 → Bool, ∃ p ∈ U, RealizesWedgeMask W m p := by
    intro m
    obtain ⟨p, hp_om, hp_real⟩ := h_masks m
    refine ⟨p, ⟨hp_om, fun hU => ?_⟩, hp_real⟩
    rw [Set.mem_iUnion₂] at hU
    rcases hU with ⟨j, _, hjG⟩
    cases hmj : m j
    · have hext : (W j).MemExt p := by simpa [hmj] using hp_real j
      exact hjG.1.2 hext
    · have hop : (W j).MemOpen p := by simpa [hmj] using hp_real j
      exact hjG.1.1 hop
  let pt : (Fin 5 → Bool) → ℝ × ℝ := fun m => (h_real_U m).choose
  have hpt_U : ∀ m, pt m ∈ U := fun m => (h_real_U m).choose_spec.1
  have hpt_inj : ∀ m₁ m₂ : Fin 5 → Bool, m₁ ≠ m₂ →
      connectedComponentIn U (pt m₁) ≠ connectedComponentIn U (pt m₂) := by
    intro m₁ m₂ hne
    have hj_ex : ∃ j : Fin 5, m₁ j ≠ m₂ j := by
      by_contra hnone; push Not at hnone; exact hne (funext hnone)
    obtain ⟨j, hj⟩ := hj_ex
    have hr1 := (h_real_U m₁).choose_spec.2 j
    have hr2 := (h_real_U m₂).choose_spec.2 j
    have hsep : ((W j).MemOpen (pt m₁) ∧ (W j).MemExt (pt m₂)) ∨
        ((W j).MemExt (pt m₁) ∧ (W j).MemOpen (pt m₂)) := by
      cases h1 : m₁ j <;> cases h2 : m₂ j
      · exact False.elim (hj (h1.trans h2.symm))
      · exact Or.inr ⟨by simpa [pt, h1] using hr1, by simpa [pt, h2] using hr2⟩
      · exact Or.inl ⟨by simpa [pt, h1] using hr1, by simpa [pt, h2] using hr2⟩
      · exact False.elim (hj (h1.trans h2.symm))
    exact comp_ne_of_sep_wedge (Finset.mem_univ j) (hpt_U m₁) (hpt_U m₂) hsep
  have h_lower : (32 : ℕ∞) ≤ (Comps U).encard := by
    have hcard32 : 32 ≤ Fintype.card (Fin 5 → Bool) := by
      rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
      norm_num
    exact (Nat.cast_le.mpr hcard32).trans (card_le_comps_of_inj pt hpt_U hpt_inj)
  exact absurd (h_lower.trans h_upper) (by decide)

/-! ## Case B (`k = 4`) Elimination -/

lemma caseB_k4_barrier_in_union
    (W1 W2 : Set (ℝ × ℝ)) (Xb Yb X : ℝ)
    (hXb : Xb < 0) (_hYb : 0 < Yb) (hX : X < 0)
    (h0 : (0, 0) ∈ W1) (hpb1 : (Xb, Yb) ∈ W1) (_hpb2 : (Xb, Yb) ∈ W2)
    (hconv1 : Convex ℝ W1)
    (hray2 : ∀ t : ℝ, 0 ≤ t → (Xb - t, Yb) ∈ W2) :
    (X, if X ≤ Xb then Yb else (Yb / Xb) * X) ∈ W1 ∪ W2 := by
  by_cases hle : X ≤ Xb
  · rw [if_pos hle]; right
    have h := hray2 (Xb - X) (by linarith)
    simpa [sub_sub_cancel] using h
  · rw [if_neg hle]; left
    have hXgt : Xb < X := lt_of_not_ge hle
    let t : ℝ := X / Xb
    have ht_pos : 0 < t := div_pos_of_neg_of_neg hX hXb
    have ht_lt : t < 1 := (div_lt_one_of_neg hXb).mpr hXgt
    have h1mt : 0 ≤ 1 - t := sub_nonneg.mpr (le_of_lt ht_lt)
    have hseg := hconv1 hpb1 h0 (le_of_lt ht_pos) h1mt (by ring)
    have hpt : t • (Xb, Yb) + (1 - t) • (0, 0) = (X, (Yb / Xb) * X) := by
      ext
      · simp only [t, Prod.smul_fst, Prod.fst_add, smul_eq_mul]
        rw [div_mul_cancel₀ _ (ne_of_lt hXb)]; ring
      · simp only [t, Prod.smul_snd, Prod.snd_add, smul_eq_mul]; ring
    rwa [← hpt]

private lemma k4_ray_dirs {W : Fin 5 → OpenWedge} (pa pb : ℝ × ℝ)
    (h_apex : ∀ k : Fin 5, (W k).y.1 < 0 ∧ (W k).y.2 < 0)
    (hxa : 0 < pa.1) (hya : pa.2 < 0) (hxb : pb.1 < 0) (hyb : 0 < pb.2)
    (hC : pa.1 * pb.2 - pa.2 * pb.1 < 0)
    (ha : ∀ k : Fin 5, (W k).MemOpen pa) (hb : ∀ k : Fin 5, (W k).MemOpen pb)
    (i₀ j₁ : Fin 5) (hj₁ : j₁ ≠ i₀)
    (hi₀_lt : isLlt (W i₀) pa pb) (hi₀_origin : (W i₀).MemOpen (0, 0))
    (h_other_gt : ∀ j : Fin 5, j ≠ i₀ → isLgt (W j) pa pb)
    (h_ncard_eq2 : ∀ j : Fin 5, j ≠ i₀ → (Gamma (W i₀) ∩ Gamma (W j)).ncard = 2)
    (hLgt_normals : ∀ j : Fin 5, j ≠ i₀ →
      (W j).u₁.1 < 0 ∧ (W j).u₁.2 < 0 ∧ (W j).u₂.1 < 0 ∧ (W j).u₂.2 < 0) :
    (∀ j : Fin 5, j ≠ i₀ →
      ((W j).u₁.1 * (dir1 (W i₀)).1 + (W j).u₁.2 * (dir1 (W i₀)).2 < 0 ∨
       (W j).u₂.1 * (dir1 (W i₀)).1 + (W j).u₂.2 * (dir1 (W i₀)).2 < 0)) ∧
    (∀ j : Fin 5, j ≠ i₀ →
      ((W j).u₁.1 * (dir2 (W i₀)).1 + (W j).u₁.2 * (dir2 (W i₀)).2 < 0 ∨
       (W j).u₂.1 * (dir2 (W i₀)).1 + (W j).u₂.2 * (dir2 (W i₀)).2 < 0)) ∧
    0 < (dir1 (W i₀)).2 ∧ 0 < (dir2 (W i₀)).1 := by
  have h_ray_meets : ∀ j : Fin 5, j ≠ i₀ →
      (∃ t > 0, ray1 (W i₀) t ∈ bdWedge (W j)) ∧
      (∃ t > 0, ray2 (W i₀) t ∈ bdWedge (W j)) := by
    intro j hj
    have hyi_in_j := caseB_Llt_in_Lgt (W i₀) (W j) pa pb (h_apex i₀).1 (h_apex i₀).2
      (h_apex j).1 (h_apex j).2 hxa hya hxb hyb hC (ha j) (hb j) hi₀_lt (h_other_gt j hj)
    let S1 := {t : ℝ | 0 ≤ t ∧ ray1 (W i₀) t ∈ bdWedge (W j)}
    let S2 := {t : ℝ | 0 ≤ t ∧ ray2 (W i₀) t ∈ bdWedge (W j)}
    have hS1_sub : S1.Subsingleton := by
      intro t₁ ht₁ t₂ ht₂
      by_contra hne
      wlog hlt : t₁ < t₂ generalizing t₁ t₂
      · exact this ht₂ ht₁ (Ne.symm hne) (lt_of_le_of_ne (not_lt.mp hlt) (Ne.symm hne))
      have ht1_pos : 0 < t₁ := lt_of_le_of_ne ht₁.1 (by
        rintro rfl
        have hpt0 : ray1 (W i₀) 0 = (W i₀).y := by ext <;> simp [ray1]
        rcases ht₁ with ⟨_, hbd1⟩
        rw [hpt0] at hbd1
        exact hbd1.1 hyi_in_j)
      have ht2_pos : 0 < t₂ := ht1_pos.trans hlt
      let θ : ℝ := t₁ / t₂
      have hθ0 : 0 < θ := div_pos ht1_pos ht2_pos
      have hθ1 : 0 < 1 - θ := by dsimp [θ]; rw [sub_pos, div_lt_one ht2_pos]; exact hlt
      have hcl2 := (bdWedge_iff_closure_eq_zero (W j) _).mp ht₂.2 |>.1
      have e1 : (W j).u₁.1 * ((ray1 (W i₀) t₁).1 - (W j).y.1) +
          (W j).u₁.2 * ((ray1 (W i₀) t₁).2 - (W j).y.2) =
          (1 - θ) * ((W j).u₁.1 * ((W i₀).y.1 - (W j).y.1) + (W j).u₁.2 * ((W i₀).y.2 - (W j).y.2)) +
          θ * ((W j).u₁.1 * ((ray1 (W i₀) t₂).1 - (W j).y.1) +
            (W j).u₁.2 * ((ray1 (W i₀) t₂).2 - (W j).y.2)) := by
        dsimp [θ, ray1]; field_simp [ne_of_gt ht2_pos]; ring
      have e2 : (W j).u₂.1 * ((ray1 (W i₀) t₁).1 - (W j).y.1) +
          (W j).u₂.2 * ((ray1 (W i₀) t₁).2 - (W j).y.2) =
          (1 - θ) * ((W j).u₂.1 * ((W i₀).y.1 - (W j).y.1) + (W j).u₂.2 * ((W i₀).y.2 - (W j).y.2)) +
          θ * ((W j).u₂.1 * ((ray1 (W i₀) t₂).1 - (W j).y.1) +
            (W j).u₂.2 * ((ray1 (W i₀) t₂).2 - (W j).y.2)) := by
        dsimp [θ, ray1]; field_simp [ne_of_gt ht2_pos]; ring
      exact ht₁.2.1 ⟨by rw [e1]; nlinarith [hyi_in_j.1, hcl2.1],
        by rw [e2]; nlinarith [hyi_in_j.2, hcl2.2]⟩
    have hS2_sub : S2.Subsingleton := by
      intro t₁ ht₁ t₂ ht₂
      by_contra hne
      wlog hlt : t₁ < t₂ generalizing t₁ t₂
      · exact this ht₂ ht₁ (Ne.symm hne) (lt_of_le_of_ne (not_lt.mp hlt) (Ne.symm hne))
      have ht1_pos : 0 < t₁ := lt_of_le_of_ne ht₁.1 (by
        rintro rfl
        have hpt0 : ray2 (W i₀) 0 = (W i₀).y := by ext <;> simp [ray2]
        rcases ht₁ with ⟨_, hbd1⟩
        rw [hpt0] at hbd1
        exact hbd1.1 hyi_in_j)
      have ht2_pos : 0 < t₂ := ht1_pos.trans hlt
      let θ : ℝ := t₁ / t₂
      have hθ0 : 0 < θ := div_pos ht1_pos ht2_pos
      have hθ1 : 0 < 1 - θ := by dsimp [θ]; rw [sub_pos, div_lt_one ht2_pos]; exact hlt
      have hcl2 := (bdWedge_iff_closure_eq_zero (W j) _).mp ht₂.2 |>.1
      have e1 : (W j).u₁.1 * ((ray2 (W i₀) t₁).1 - (W j).y.1) +
          (W j).u₁.2 * ((ray2 (W i₀) t₁).2 - (W j).y.2) =
          (1 - θ) * ((W j).u₁.1 * ((W i₀).y.1 - (W j).y.1) + (W j).u₁.2 * ((W i₀).y.2 - (W j).y.2)) +
          θ * ((W j).u₁.1 * ((ray2 (W i₀) t₂).1 - (W j).y.1) +
            (W j).u₁.2 * ((ray2 (W i₀) t₂).2 - (W j).y.2)) := by
        dsimp [θ, ray2]; field_simp [ne_of_gt ht2_pos]; ring
      have e2 : (W j).u₂.1 * ((ray2 (W i₀) t₁).1 - (W j).y.1) +
          (W j).u₂.2 * ((ray2 (W i₀) t₁).2 - (W j).y.2) =
          (1 - θ) * ((W j).u₂.1 * ((W i₀).y.1 - (W j).y.1) + (W j).u₂.2 * ((W i₀).y.2 - (W j).y.2)) +
          θ * ((W j).u₂.1 * ((ray2 (W i₀) t₂).1 - (W j).y.1) +
            (W j).u₂.2 * ((ray2 (W i₀) t₂).2 - (W j).y.2)) := by
        dsimp [θ, ray2]; field_simp [ne_of_gt ht2_pos]; ring
      exact ht₁.2.1 ⟨by rw [e1]; nlinarith [hyi_in_j.1, hcl2.1],
        by rw [e2]; nlinarith [hyi_in_j.2, hcl2.2]⟩
    have hsub : Gamma (W i₀) ∩ Gamma (W j) ⊆ ray1 (W i₀) '' S1 ∪ ray2 (W i₀) '' S2 := by
      rintro p ⟨⟨hi_bd, _⟩, ⟨hj_bd, _⟩⟩
      rcases (bdWedge_iff_rays (W i₀) p).mp hi_bd with ⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩
      · left; exact ⟨t, ⟨ht, hj_bd⟩, rfl⟩
      · right; exact ⟨t, ⟨ht, hj_bd⟩, rfl⟩
    have hfin1 : (ray1 (W i₀) '' S1).Finite := hS1_sub.finite.image _
    have hfin2 : (ray2 (W i₀) '' S2).Finite := hS2_sub.finite.image _
    have hncard := h_ncard_eq2 j hj
    have hne1 : S1.Nonempty := by
      by_contra hemp
      rw [Set.not_nonempty_iff_eq_empty] at hemp
      have hc2 : (ray2 (W i₀) '' S2).ncard ≤ 1 := by
        rw [Set.ncard_le_one_iff hfin2]
        rintro _ _ ⟨ta, hta, rfl⟩ ⟨tb, htb, rfl⟩
        rw [hS2_sub hta htb]
      have hsub' : Gamma (W i₀) ∩ Gamma (W j) ⊆ ray2 (W i₀) '' S2 := by
        simpa [hemp] using hsub
      have hle : (Gamma (W i₀) ∩ Gamma (W j)).ncard ≤ 1 :=
        (Set.ncard_le_ncard hsub' hfin2).trans hc2
      omega
    have hne2 : S2.Nonempty := by
      by_contra hemp
      rw [Set.not_nonempty_iff_eq_empty] at hemp
      have hc1 : (ray1 (W i₀) '' S1).ncard ≤ 1 := by
        rw [Set.ncard_le_one_iff hfin1]
        rintro _ _ ⟨ta, hta, rfl⟩ ⟨tb, htb, rfl⟩
        rw [hS1_sub hta htb]
      have hsub' : Gamma (W i₀) ∩ Gamma (W j) ⊆ ray1 (W i₀) '' S1 := by
        simpa [hemp] using hsub
      have hle : (Gamma (W i₀) ∩ Gamma (W j)).ncard ≤ 1 :=
        (Set.ncard_le_ncard hsub' hfin1).trans hc1
      omega
    obtain ⟨t1, ht1⟩ := hne1
    obtain ⟨t2, ht2⟩ := hne2
    have ht1_pos : 0 < t1 := lt_of_le_of_ne ht1.1 (by
      rintro rfl
      have hpt0 : ray1 (W i₀) 0 = (W i₀).y := by ext <;> simp [ray1]
      rcases ht1 with ⟨_, hbd1⟩
      rw [hpt0] at hbd1
      exact hbd1.1 hyi_in_j)
    have ht2_pos : 0 < t2 := lt_of_le_of_ne ht2.1 (by
      rintro rfl
      have hpt0 : ray2 (W i₀) 0 = (W i₀).y := by ext <;> simp [ray2]
      rcases ht2 with ⟨_, hbd2⟩
      rw [hpt0] at hbd2
      exact hbd2.1 hyi_in_j)
    exact ⟨⟨t1, ht1_pos, ht1.2⟩, ⟨t2, ht2_pos, ht2.2⟩⟩
  have hd1_neg : ∀ j : Fin 5, j ≠ i₀ →
      ((W j).u₁.1 * (dir1 (W i₀)).1 + (W j).u₁.2 * (dir1 (W i₀)).2 < 0 ∨
       (W j).u₂.1 * (dir1 (W i₀)).1 + (W j).u₂.2 * (dir1 (W i₀)).2 < 0) := by
    intro j hj
    obtain ⟨t, ht, hbd⟩ := (h_ray_meets j hj).1
    have hyi_in_j := caseB_Llt_in_Lgt (W i₀) (W j) pa pb (h_apex i₀).1 (h_apex i₀).2
      (h_apex j).1 (h_apex j).2 hxa hya hxb hyb hC (ha j) (hb j) hi₀_lt (h_other_gt j hj)
    rcases (bdWedge_iff_closure_eq_zero (W j) _).mp hbd |>.2 with hz1 | hz2
    · left
      have e : (W j).u₁.1 * ((ray1 (W i₀) t).1 - (W j).y.1) +
          (W j).u₁.2 * ((ray1 (W i₀) t).2 - (W j).y.2) =
          ((W j).u₁.1 * ((W i₀).y.1 - (W j).y.1) + (W j).u₁.2 * ((W i₀).y.2 - (W j).y.2)) +
          t * ((W j).u₁.1 * (dir1 (W i₀)).1 + (W j).u₁.2 * (dir1 (W i₀)).2) := by
        dsimp [ray1]; ring
      rw [e] at hz1; nlinarith [hyi_in_j.1]
    · right
      have e : (W j).u₂.1 * ((ray1 (W i₀) t).1 - (W j).y.1) +
          (W j).u₂.2 * ((ray1 (W i₀) t).2 - (W j).y.2) =
          ((W j).u₂.1 * ((W i₀).y.1 - (W j).y.1) + (W j).u₂.2 * ((W i₀).y.2 - (W j).y.2)) +
          t * ((W j).u₂.1 * (dir1 (W i₀)).1 + (W j).u₂.2 * (dir1 (W i₀)).2) := by
        dsimp [ray1]; ring
      rw [e] at hz2; nlinarith [hyi_in_j.2]
  have hd2_neg : ∀ j : Fin 5, j ≠ i₀ →
      ((W j).u₁.1 * (dir2 (W i₀)).1 + (W j).u₁.2 * (dir2 (W i₀)).2 < 0 ∨
       (W j).u₂.1 * (dir2 (W i₀)).1 + (W j).u₂.2 * (dir2 (W i₀)).2 < 0) := by
    intro j hj
    obtain ⟨t, ht, hbd⟩ := (h_ray_meets j hj).2
    have hyi_in_j := caseB_Llt_in_Lgt (W i₀) (W j) pa pb (h_apex i₀).1 (h_apex i₀).2
      (h_apex j).1 (h_apex j).2 hxa hya hxb hyb hC (ha j) (hb j) hi₀_lt (h_other_gt j hj)
    rcases (bdWedge_iff_closure_eq_zero (W j) _).mp hbd |>.2 with hz1 | hz2
    · left
      have e : (W j).u₁.1 * ((ray2 (W i₀) t).1 - (W j).y.1) +
          (W j).u₁.2 * ((ray2 (W i₀) t).2 - (W j).y.2) =
          ((W j).u₁.1 * ((W i₀).y.1 - (W j).y.1) + (W j).u₁.2 * ((W i₀).y.2 - (W j).y.2)) +
          t * ((W j).u₁.1 * (dir2 (W i₀)).1 + (W j).u₁.2 * (dir2 (W i₀)).2) := by
        dsimp [ray2]; ring
      rw [e] at hz1; nlinarith [hyi_in_j.1]
    · right
      have e : (W j).u₂.1 * ((ray2 (W i₀) t).1 - (W j).y.1) +
          (W j).u₂.2 * ((ray2 (W i₀) t).2 - (W j).y.2) =
          ((W j).u₂.1 * ((W i₀).y.1 - (W j).y.1) + (W j).u₂.2 * ((W i₀).y.2 - (W j).y.2)) +
          t * ((W j).u₂.1 * (dir2 (W i₀)).1 + (W j).u₂.2 * (dir2 (W i₀)).2) := by
        dsimp [ray2]; ring
      rw [e] at hz2; nlinarith [hyi_in_j.2]
  have hd1_y_pos : 0 < (dir1 (W i₀)).2 := by
    have hnot_q3 : 0 < (dir1 (W i₀)).1 ∨ 0 < (dir1 (W i₀)).2 := by
      by_contra hle; push Not at hle
      obtain ⟨hu11, hu12, hu21, hu22⟩ := hLgt_normals j₁ hj₁
      rcases hd1_neg j₁ hj₁ with h1 | h2 <;> nlinarith [hle.1, hle.2]
    by_contra hle; have h2 : (dir1 (W i₀)).2 ≤ 0 := not_lt.mp hle
    have h1 : 0 < (dir1 (W i₀)).1 := hnot_q3.resolve_right hle
    have hdet : (dir1 (W i₀)).1 * (-(W i₀).y.2) - (dir1 (W i₀)).2 * (-(W i₀).y.1) =
        -((W i₀).u₁.1 * (0 - (W i₀).y.1) + (W i₀).u₁.2 * (0 - (W i₀).y.2)) := by
      dsimp [dir1]; ring
    have hneg : (dir1 (W i₀)).1 * (-(W i₀).y.2) - (dir1 (W i₀)).2 * (-(W i₀).y.1) < 0 := by
      rw [hdet]; linarith [hi₀_origin.1]
    nlinarith [(h_apex i₀).1, (h_apex i₀).2]
  have hd2_x_pos : 0 < (dir2 (W i₀)).1 := by
    have hnot_q3 : 0 < (dir2 (W i₀)).1 ∨ 0 < (dir2 (W i₀)).2 := by
      by_contra hle; push Not at hle
      obtain ⟨hu11, hu12, hu21, hu22⟩ := hLgt_normals j₁ hj₁
      rcases hd2_neg j₁ hj₁ with h1 | h2 <;> nlinarith [hle.1, hle.2]
    by_contra hle; have h1 : (dir2 (W i₀)).1 ≤ 0 := not_lt.mp hle
    have h2 : 0 < (dir2 (W i₀)).2 := hnot_q3.resolve_left hle
    have hdet : (dir2 (W i₀)).1 * (-(W i₀).y.2) - (dir2 (W i₀)).2 * (-(W i₀).y.1) =
        (W i₀).u₂.1 * (0 - (W i₀).y.1) + (W i₀).u₂.2 * (0 - (W i₀).y.2) := by
      dsimp [dir2]; ring
    have hpos : 0 < (dir2 (W i₀)).1 * (-(W i₀).y.2) - (dir2 (W i₀)).2 * (-(W i₀).y.1) := by
      rw [hdet]; exact hi₀_origin.2
    nlinarith [(h_apex i₀).1, (h_apex i₀).2]
  exact ⟨hd1_neg, hd2_neg, hd1_y_pos, hd2_x_pos⟩

private lemma k4_exists_p_hi {W : Fin 5 → OpenWedge} (pb : ℝ × ℝ)
    (hxb : pb.1 < 0) (i₀ j₁ : Fin 5) (hj₁ : j₁ ≠ i₀)
    (hLgt_normals : ∀ j : Fin 5, j ≠ i₀ →
      (W j).u₁.1 < 0 ∧ (W j).u₁.2 < 0 ∧ (W j).u₂.1 < 0 ∧ (W j).u₂.2 < 0)
    (hd1_neg : ∀ j : Fin 5, j ≠ i₀ →
      ((W j).u₁.1 * (dir1 (W i₀)).1 + (W j).u₁.2 * (dir1 (W i₀)).2 < 0 ∨
       (W j).u₂.1 * (dir1 (W i₀)).1 + (W j).u₂.2 * (dir1 (W i₀)).2 < 0))
    (hd1_y_pos : 0 < (dir1 (W i₀)).2) :
    ∃ p_hi : ℝ × ℝ, p_hi ∈ ({p : ℝ × ℝ | inOmega p} \ ⋃ j ∈ (Finset.univ : Finset (Fin 5)), Gamma (W j)) ∧
      (∀ m : Fin 5, (W m).MemExt p_hi) ∧ p_hi.1 < 0 ∧
      (if p_hi.1 ≤ pb.1 then pb.2 else (pb.2 / pb.1) * p_hi.1) < p_hi.2 := by
  by_cases hd1x : 0 < (dir1 (W i₀)).1
  · let X := pb.1 - 1
    have hX_neg : X < 0 := by linarith
    have h_Y_ex : ∀ j : Fin 5, ∃ Yj : ℝ, ∀ Y : ℝ, Yj < Y → (W j).MemExt (X, Y) := by
      intro j
      by_cases hj : j = i₀
      · subst hj
        have hu12 : (W j).u₁.2 < 0 := by dsimp [dir1] at hd1x; linarith
        refine ⟨(W j).y.2 + ((W j).u₁.1 * (X - (W j).y.1)) / (-(W j).u₁.2), fun Y hY => ?_⟩
        left
        have hmul : ((W j).u₁.1 * (X - (W j).y.1)) < (Y - (W j).y.2) * (-(W j).u₁.2) := by
          have hY' : ((W j).u₁.1 * (X - (W j).y.1)) / (-(W j).u₁.2) < Y - (W j).y.2 := by linarith
          rw [div_lt_iff₀ (by linarith)] at hY'
          nlinarith
        linarith
      · obtain ⟨_, hu12, _, _⟩ := hLgt_normals j hj
        refine ⟨(W j).y.2 + ((W j).u₁.1 * (X - (W j).y.1)) / (-(W j).u₁.2), fun Y hY => ?_⟩
        left
        have hmul : ((W j).u₁.1 * (X - (W j).y.1)) < (Y - (W j).y.2) * (-(W j).u₁.2) := by
          have hY' : ((W j).u₁.1 * (X - (W j).y.1)) / (-(W j).u₁.2) < Y - (W j).y.2 := by linarith
          rw [div_lt_iff₀ (by linarith)] at hY'
          nlinarith
        linarith
    let Y := max pb.2 ((Finset.univ : Finset (Fin 5)).sup' Finset.univ_nonempty
      (fun j => (h_Y_ex j).choose)) + 1
    refine ⟨(X, Y), ⟨Or.inl hX_neg, ?_⟩, ?_, hX_neg, ?_⟩
    · intro hU
      rw [Set.mem_iUnion₂] at hU
      rcases hU with ⟨j, _, hjG⟩
      have hY_gt : (h_Y_ex j).choose < Y := by
        have hle := Finset.le_sup' (fun j => (h_Y_ex j).choose) (Finset.mem_univ j)
        have hmr := le_max_right pb.2 ((Finset.univ : Finset (Fin 5)).sup' Finset.univ_nonempty
          (fun j => (h_Y_ex j).choose))
        linarith
      exact hjG.1.2 ((h_Y_ex j).choose_spec Y hY_gt)
    · intro j
      have hY_gt : (h_Y_ex j).choose < Y := by
        have hle := Finset.le_sup' (fun j => (h_Y_ex j).choose) (Finset.mem_univ j)
        have hmr := le_max_right pb.2 ((Finset.univ : Finset (Fin 5)).sup' Finset.univ_nonempty
          (fun j => (h_Y_ex j).choose))
        linarith
      exact (h_Y_ex j).choose_spec Y hY_gt
    · rw [if_pos (by dsimp [X]; linarith)]
      have hml := le_max_left pb.2 ((Finset.univ : Finset (Fin 5)).sup' Finset.univ_nonempty
        (fun j => (h_Y_ex j).choose))
      linarith
  · have hd1x' : (dir1 (W i₀)).1 ≤ 0 := not_lt.mp hd1x
    let S_gt : Finset (Fin 5) := Finset.univ.erase i₀
    have hS_ne : S_gt.Nonempty := ⟨j₁, Finset.mem_erase.mpr ⟨hj₁, Finset.mem_univ _⟩⟩
    have hu_ex : ∀ j ∈ S_gt, ∃ u : ℝ × ℝ, (u = (W j).u₁ ∨ u = (W j).u₂) ∧
        u.1 < 0 ∧ u.1 * (dir1 (W i₀)).1 + u.2 * (dir1 (W i₀)).2 < 0 := by
      intro j hj
      have hne := Finset.ne_of_mem_erase hj
      obtain ⟨hu11, _, hu21, _⟩ := hLgt_normals j hne
      rcases hd1_neg j hne with h1 | h2
      · exact ⟨(W j).u₁, Or.inl rfl, hu11, h1⟩
      · exact ⟨(W j).u₂, Or.inr rfl, hu21, h2⟩
    let bound : Fin 5 → ℝ := fun j =>
      if hj : j ∈ S_gt then
        let u := (hu_ex j hj).choose
        (-(u.1 * (dir1 (W i₀)).1 + u.2 * (dir1 (W i₀)).2)) / (-u.1)
      else 1
    have hbound_pos : ∀ j ∈ S_gt, 0 < bound j := by
      intro j hj
      dsimp [bound]; rw [dif_pos hj]
      have hs := (hu_ex j hj).choose_spec
      exact div_pos (by linarith [hs.2.2]) (by linarith [hs.2.1])
    let η : ℝ := (S_gt.inf' hS_ne bound) / 2
    have hη_pos : 0 < η := by
      obtain ⟨j, hj, heq⟩ := Finset.exists_mem_eq_inf' hS_ne bound
      dsimp [η]; rw [heq]; linarith [hbound_pos j hj]
    let dtilde : ℝ × ℝ := ((dir1 (W i₀)).1 - η, (dir1 (W i₀)).2)
    have hdtilde_x : dtilde.1 < 0 := by dsimp [dtilde]; linarith
    have hdtilde_i0 : (W i₀).u₁.1 * dtilde.1 + (W i₀).u₁.2 * dtilde.2 < 0 := by
      have e : (W i₀).u₁.1 * dtilde.1 + (W i₀).u₁.2 * dtilde.2 = -η * (dir1 (W i₀)).2 := by
        dsimp [dtilde, dir1]; ring
      rw [e]; exact mul_neg_of_neg_of_pos (by linarith) hd1_y_pos
    have hdtilde_j : ∀ (j : Fin 5) (hj : j ∈ S_gt),
        (hu_ex j hj).choose.1 * dtilde.1 + (hu_ex j hj).choose.2 * dtilde.2 < 0 := by
      intro j hj
      have hs := (hu_ex j hj).choose_spec
      have hle : S_gt.inf' hS_ne bound ≤ bound j := Finset.inf'_le bound hj
      have hη_lt : η < bound j := by dsimp [η]; linarith [hbound_pos j hj]
      dsimp [bound] at hη_lt; rw [dif_pos hj] at hη_lt
      rw [lt_div_iff₀ (by linarith [hs.2.1])] at hη_lt
      have e : (hu_ex j hj).choose.1 * dtilde.1 + (hu_ex j hj).choose.2 * dtilde.2 =
          ((hu_ex j hj).choose.1 * (dir1 (W i₀)).1 + (hu_ex j hj).choose.2 * (dir1 (W i₀)).2) -
          η * (hu_ex j hj).choose.1 := by dsimp [dtilde]; ring
      rw [e]; linarith
    let R_j : Fin 5 → ℝ := fun j =>
      if hj : j ∈ S_gt then
        let u := (hu_ex j hj).choose
        (u.1 * ((W i₀).y.1 - (W j).y.1) + u.2 * ((W i₀).y.2 - (W j).y.2)) /
          (-(u.1 * dtilde.1 + u.2 * dtilde.2))
      else 0
    let R : ℝ := max (max ((pb.1 - (W i₀).y.1) / dtilde.1) ((pb.2 - (W i₀).y.2) / dtilde.2))
      (max (S_gt.sup' hS_ne R_j) 0) + 1
    have hR_pos : 0 < R := by
      have h1 := le_max_right (S_gt.sup' hS_ne R_j) 0
      have h2 := le_max_right
        (max ((pb.1 - (W i₀).y.1) / dtilde.1) ((pb.2 - (W i₀).y.2) / dtilde.2))
        (max (S_gt.sup' hS_ne R_j) 0)
      linarith
    let p_hi : ℝ × ℝ := ((W i₀).y.1 + R * dtilde.1, (W i₀).y.2 + R * dtilde.2)
    have hp_hi_x_le : p_hi.1 ≤ pb.1 := by
      have h1 : (pb.1 - (W i₀).y.1) / dtilde.1 < R := by
        have ha1 := le_max_left ((pb.1 - (W i₀).y.1) / dtilde.1) ((pb.2 - (W i₀).y.2) / dtilde.2)
        have ha2 := le_max_left
          (max ((pb.1 - (W i₀).y.1) / dtilde.1) ((pb.2 - (W i₀).y.2) / dtilde.2))
          (max (S_gt.sup' hS_ne R_j) 0)
        linarith
      rw [div_lt_iff_of_neg hdtilde_x] at h1
      dsimp [p_hi]; linarith
    have hp_hi_x_neg : p_hi.1 < 0 := lt_of_le_of_lt hp_hi_x_le hxb
    have hp_hi_y_gt : pb.2 < p_hi.2 := by
      have h1 : (pb.2 - (W i₀).y.2) / dtilde.2 < R := by
        have ha1 := le_max_right ((pb.1 - (W i₀).y.1) / dtilde.1) ((pb.2 - (W i₀).y.2) / dtilde.2)
        have ha2 := le_max_left
          (max ((pb.1 - (W i₀).y.1) / dtilde.1) ((pb.2 - (W i₀).y.2) / dtilde.2))
          (max (S_gt.sup' hS_ne R_j) 0)
        linarith
      have hdy : 0 < dtilde.2 := hd1_y_pos
      rw [div_lt_iff₀ hdy] at h1
      dsimp [p_hi]; linarith
    have hp_hi_ext : ∀ j : Fin 5, (W j).MemExt p_hi := by
      intro j
      by_cases hj : j = i₀
      · subst hj; left
        have e : (W j).u₁.1 * (p_hi.1 - (W j).y.1) + (W j).u₁.2 * (p_hi.2 - (W j).y.2) =
            R * ((W j).u₁.1 * dtilde.1 + (W j).u₁.2 * dtilde.2) := by dsimp [p_hi]; ring
        rw [e]; exact mul_neg_of_pos_of_neg hR_pos hdtilde_i0
      · have hjS : j ∈ S_gt := Finset.mem_erase.mpr ⟨hj, Finset.mem_univ _⟩
        have hlt_R : R_j j < R := by
          have hle1 := Finset.le_sup' R_j hjS
          have hle2 := le_max_left (S_gt.sup' hS_ne R_j) 0
          have hle3 := le_max_right
            (max ((pb.1 - (W i₀).y.1) / dtilde.1) ((pb.2 - (W i₀).y.2) / dtilde.2))
            (max (S_gt.sup' hS_ne R_j) 0)
          linarith
        dsimp [R_j] at hlt_R; rw [dif_pos hjS] at hlt_R
        have hneg := hdtilde_j j hjS
        rw [div_lt_iff₀ (by linarith)] at hlt_R
        have hlin : (hu_ex j hjS).choose.1 * (p_hi.1 - (W j).y.1) +
            (hu_ex j hjS).choose.2 * (p_hi.2 - (W j).y.2) < 0 := by
          have e : (hu_ex j hjS).choose.1 * (p_hi.1 - (W j).y.1) +
              (hu_ex j hjS).choose.2 * (p_hi.2 - (W j).y.2) =
              ((hu_ex j hjS).choose.1 * ((W i₀).y.1 - (W j).y.1) +
                (hu_ex j hjS).choose.2 * ((W i₀).y.2 - (W j).y.2)) +
              R * ((hu_ex j hjS).choose.1 * dtilde.1 + (hu_ex j hjS).choose.2 * dtilde.2) := by
            dsimp [p_hi]; ring
          rw [e]; linarith
        rcases (hu_ex j hjS).choose_spec.1 with hu1 | hu2
        · left; rwa [← hu1]
        · right; rwa [← hu2]
    refine ⟨p_hi, ⟨Or.inl hp_hi_x_neg, ?_⟩, hp_hi_ext, hp_hi_x_neg, ?_⟩
    · intro hU; rw [Set.mem_iUnion₂] at hU
      rcases hU with ⟨j, _, hjG⟩; exact hjG.1.2 (hp_hi_ext j)
    · rw [if_pos hp_hi_x_le]; exact hp_hi_y_gt

private lemma k4_exists_p_lo {W : Fin 5 → OpenWedge}
    (h_apex : ∀ k : Fin 5, (W k).y.1 < 0 ∧ (W k).y.2 < 0)
    (i₀ j₁ : Fin 5) (hj₁ : j₁ ≠ i₀)
    (hLgt_normals : ∀ j : Fin 5, j ≠ i₀ →
      (W j).u₁.1 < 0 ∧ (W j).u₁.2 < 0 ∧ (W j).u₂.1 < 0 ∧ (W j).u₂.2 < 0)
    (hd2_neg : ∀ j : Fin 5, j ≠ i₀ →
      ((W j).u₁.1 * (dir2 (W i₀)).1 + (W j).u₁.2 * (dir2 (W i₀)).2 < 0 ∨
       (W j).u₂.1 * (dir2 (W i₀)).1 + (W j).u₂.2 * (dir2 (W i₀)).2 < 0))
    (hd2_x_pos : 0 < (dir2 (W i₀)).1) :
    ∃ p_lo : ℝ × ℝ, p_lo ∈ ({p : ℝ × ℝ | inOmega p} \ ⋃ j ∈ (Finset.univ : Finset (Fin 5)), Gamma (W j)) ∧
      (∀ m : Fin 5, (W m).MemExt p_lo) ∧ p_lo.2 < 0 := by
  by_cases hd2y : 0 < (dir2 (W i₀)).2
  · let Y : ℝ := -1
    have h_X_ex : ∀ j : Fin 5, ∃ Xj : ℝ, ∀ X : ℝ, Xj < X → (W j).MemExt (X, Y) := by
      intro j
      by_cases hj : j = i₀
      · subst hj
        have hu21 : (W j).u₂.1 < 0 := by dsimp [dir2] at hd2y; linarith
        refine ⟨(W j).y.1 + ((W j).u₂.2 * (Y - (W j).y.2)) / (-(W j).u₂.1), fun X hX => ?_⟩
        right
        have hmul : ((W j).u₂.2 * (Y - (W j).y.2)) < (X - (W j).y.1) * (-(W j).u₂.1) := by
          have hX' : ((W j).u₂.2 * (Y - (W j).y.2)) / (-(W j).u₂.1) < X - (W j).y.1 := by linarith
          rw [div_lt_iff₀ (by linarith)] at hX'; nlinarith
        linarith
      · obtain ⟨hu11, _, _, _⟩ := hLgt_normals j hj
        refine ⟨(W j).y.1 + ((W j).u₁.2 * (Y - (W j).y.2)) / (-(W j).u₁.1), fun X hX => ?_⟩
        left
        have hmul : ((W j).u₁.2 * (Y - (W j).y.2)) < (X - (W j).y.1) * (-(W j).u₁.1) := by
          have hX' : ((W j).u₁.2 * (Y - (W j).y.2)) / (-(W j).u₁.1) < X - (W j).y.1 := by linarith
          rw [div_lt_iff₀ (by linarith)] at hX'; nlinarith
        linarith
    let X := (Finset.univ : Finset (Fin 5)).sup' Finset.univ_nonempty (fun j => (h_X_ex j).choose) + 1
    refine ⟨(X, Y), ⟨Or.inr (by norm_num [Y]), ?_⟩, ?_, by norm_num [Y]⟩
    · intro hU; rw [Set.mem_iUnion₂] at hU
      rcases hU with ⟨j, _, hjG⟩
      have hX_gt : (h_X_ex j).choose < X := by
        have hle := Finset.le_sup' (fun j => (h_X_ex j).choose) (Finset.mem_univ j)
        linarith
      exact hjG.1.2 ((h_X_ex j).choose_spec X hX_gt)
    · intro j
      have hX_gt : (h_X_ex j).choose < X := by
        have hle := Finset.le_sup' (fun j => (h_X_ex j).choose) (Finset.mem_univ j)
        linarith
      exact (h_X_ex j).choose_spec X hX_gt
  · have hd2y' : (dir2 (W i₀)).2 ≤ 0 := not_lt.mp hd2y
    let S_gt : Finset (Fin 5) := Finset.univ.erase i₀
    have hS_ne : S_gt.Nonempty := ⟨j₁, Finset.mem_erase.mpr ⟨hj₁, Finset.mem_univ _⟩⟩
    have hu_ex : ∀ j ∈ S_gt, ∃ u : ℝ × ℝ, (u = (W j).u₁ ∨ u = (W j).u₂) ∧
        u.2 < 0 ∧ u.1 * (dir2 (W i₀)).1 + u.2 * (dir2 (W i₀)).2 < 0 := by
      intro j hj
      have hne := Finset.ne_of_mem_erase hj
      obtain ⟨_, hu12, _, hu22⟩ := hLgt_normals j hne
      rcases hd2_neg j hne with h1 | h2
      · exact ⟨(W j).u₁, Or.inl rfl, hu12, h1⟩
      · exact ⟨(W j).u₂, Or.inr rfl, hu22, h2⟩
    let bound : Fin 5 → ℝ := fun j =>
      if hj : j ∈ S_gt then
        let u := (hu_ex j hj).choose
        (-(u.1 * (dir2 (W i₀)).1 + u.2 * (dir2 (W i₀)).2)) / (-u.2)
      else 1
    have hbound_pos : ∀ j ∈ S_gt, 0 < bound j := by
      intro j hj
      dsimp [bound]; rw [dif_pos hj]
      have hs := (hu_ex j hj).choose_spec
      exact div_pos (by linarith [hs.2.2]) (by linarith [hs.2.1])
    let η : ℝ := (S_gt.inf' hS_ne bound) / 2
    have hη_pos : 0 < η := by
      obtain ⟨j, hj, heq⟩ := Finset.exists_mem_eq_inf' hS_ne bound
      dsimp [η]; rw [heq]; linarith [hbound_pos j hj]
    let dtilde : ℝ × ℝ := ((dir2 (W i₀)).1, (dir2 (W i₀)).2 - η)
    have hdtilde_y : dtilde.2 < 0 := by dsimp [dtilde]; linarith
    have hdtilde_i0 : (W i₀).u₂.1 * dtilde.1 + (W i₀).u₂.2 * dtilde.2 < 0 := by
      have e : (W i₀).u₂.1 * dtilde.1 + (W i₀).u₂.2 * dtilde.2 = -η * (dir2 (W i₀)).1 := by
        dsimp [dtilde, dir2]; ring
      rw [e]; exact mul_neg_of_neg_of_pos (by linarith) hd2_x_pos
    have hdtilde_j : ∀ (j : Fin 5) (hj : j ∈ S_gt),
        (hu_ex j hj).choose.1 * dtilde.1 + (hu_ex j hj).choose.2 * dtilde.2 < 0 := by
      intro j hj
      have hs := (hu_ex j hj).choose_spec
      have hle : S_gt.inf' hS_ne bound ≤ bound j := Finset.inf'_le bound hj
      have hη_lt : η < bound j := by dsimp [η]; linarith [hbound_pos j hj]
      dsimp [bound] at hη_lt; rw [dif_pos hj] at hη_lt
      rw [lt_div_iff₀ (by linarith [hs.2.1])] at hη_lt
      have e : (hu_ex j hj).choose.1 * dtilde.1 + (hu_ex j hj).choose.2 * dtilde.2 =
          ((hu_ex j hj).choose.1 * (dir2 (W i₀)).1 + (hu_ex j hj).choose.2 * (dir2 (W i₀)).2) -
          η * (hu_ex j hj).choose.2 := by dsimp [dtilde]; ring
      rw [e]; linarith
    let R_j : Fin 5 → ℝ := fun j =>
      if hj : j ∈ S_gt then
        let u := (hu_ex j hj).choose
        (u.1 * ((W i₀).y.1 - (W j).y.1) + u.2 * ((W i₀).y.2 - (W j).y.2)) /
          (-(u.1 * dtilde.1 + u.2 * dtilde.2))
      else 0
    let R : ℝ := max (S_gt.sup' hS_ne R_j) 0 + 1
    have hR_pos : 0 < R := by
      have hmr := le_max_right (S_gt.sup' hS_ne R_j) 0
      linarith
    let p_lo : ℝ × ℝ := ((W i₀).y.1 + R * dtilde.1, (W i₀).y.2 + R * dtilde.2)
    have hp_lo_y_neg : p_lo.2 < 0 := by
      dsimp [p_lo]
      nlinarith [(h_apex i₀).2, hR_pos, hdtilde_y]
    have hp_lo_ext : ∀ j : Fin 5, (W j).MemExt p_lo := by
      intro j
      by_cases hj : j = i₀
      · subst hj; right
        have e : (W j).u₂.1 * (p_lo.1 - (W j).y.1) + (W j).u₂.2 * (p_lo.2 - (W j).y.2) =
            R * ((W j).u₂.1 * dtilde.1 + (W j).u₂.2 * dtilde.2) := by dsimp [p_lo]; ring
        rw [e]; exact mul_neg_of_pos_of_neg hR_pos hdtilde_i0
      · have hjS : j ∈ S_gt := Finset.mem_erase.mpr ⟨hj, Finset.mem_univ _⟩
        have hlt_R : R_j j < R := by
          have hle1 := Finset.le_sup' R_j hjS
          have hle2 := le_max_left (S_gt.sup' hS_ne R_j) 0
          linarith
        dsimp [R_j] at hlt_R; rw [dif_pos hjS] at hlt_R
        have hneg := hdtilde_j j hjS
        rw [div_lt_iff₀ (by linarith)] at hlt_R
        have hlin : (hu_ex j hjS).choose.1 * (p_lo.1 - (W j).y.1) +
            (hu_ex j hjS).choose.2 * (p_lo.2 - (W j).y.2) < 0 := by
          have e : (hu_ex j hjS).choose.1 * (p_lo.1 - (W j).y.1) +
              (hu_ex j hjS).choose.2 * (p_lo.2 - (W j).y.2) =
              ((hu_ex j hjS).choose.1 * ((W i₀).y.1 - (W j).y.1) +
                (hu_ex j hjS).choose.2 * ((W i₀).y.2 - (W j).y.2)) +
              R * ((hu_ex j hjS).choose.1 * dtilde.1 + (hu_ex j hjS).choose.2 * dtilde.2) := by
            dsimp [p_lo]; ring
          rw [e]; linarith
        rcases (hu_ex j hjS).choose_spec.1 with hu1 | hu2
        · left; rwa [← hu1]
        · right; rwa [← hu2]
    refine ⟨p_lo, ⟨Or.inr hp_lo_y_neg, ?_⟩, hp_lo_ext, hp_lo_y_neg⟩
    intro hU; rw [Set.mem_iUnion₂] at hU
    rcases hU with ⟨j, _, hjG⟩; exact hjG.1.2 (hp_lo_ext j)

theorem caseB_k4_elim {W : Fin 5 → OpenWedge} (hGP : GeneralPosition W)
    (pa pb : ℝ × ℝ)
    (h_apex : ∀ k : Fin 5, (W k).y.1 < 0 ∧ (W k).y.2 < 0)
    (hxa : 0 < pa.1) (hya : pa.2 < 0) (hxb : pb.1 < 0) (hyb : 0 < pb.2)
    (hC : pa.1 * pb.2 - pa.2 * pb.1 < 0)
    (ha : ∀ k : Fin 5, (W k).MemOpen pa) (hb : ∀ k : Fin 5, (W k).MemOpen pb)
    (h_masks : ∀ m : Fin 5 → Bool, ∃ p : ℝ × ℝ, inOmega p ∧ RealizesWedgeMask W m p)
    (hk4 : (Finset.univ.filter (fun i : Fin 5 => isLgt (W i) pa pb)).card = 4) :
    False := by
  let Lgt : Finset (Fin 5) := Finset.univ.filter (fun i : Fin 5 => isLgt (W i) pa pb)
  have hcomp_card : (Finset.univ \ Lgt).card = 1 := by
    have h := Finset.card_sdiff_add_card_inter (Finset.univ : Finset (Fin 5)) Lgt
    rw [Finset.univ_inter, Finset.card_univ, Fintype.card_fin] at h
    have hLgt : Lgt.card = 4 := hk4
    omega
  obtain ⟨i₀, hi₀_eq⟩ := Finset.card_eq_one.mp hcomp_card
  have hi₀_lt : isLlt (W i₀) pa pb := by
    have hmem : i₀ ∈ Finset.univ \ Lgt := hi₀_eq ▸ Finset.mem_singleton_self i₀
    have hngt : ¬ isLgt (W i₀) pa pb := fun hgt =>
      (Finset.mem_sdiff.mp hmem).2 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hgt⟩)
    exact (caseB_dichotomy (W i₀) pa pb (h_apex i₀).1 (h_apex i₀).2
      hxa hya hxb hyb hC (ha i₀) (hb i₀)).resolve_right hngt
  have hi₀_origin : (W i₀).MemOpen (0, 0) :=
    case_b_origin_in_wedge (W i₀) pa pb (h_apex i₀).1 (h_apex i₀).2
      hxa hya hxb hyb hC (ha i₀) (hb i₀) hi₀_lt
  have h_other_gt : ∀ j : Fin 5, j ≠ i₀ → isLgt (W j) pa pb := by
    intro j hj
    by_contra hngt
    have hmem : j ∈ Finset.univ \ Lgt := Finset.mem_sdiff.mpr
      ⟨Finset.mem_univ _, fun h => hngt (Finset.mem_filter.mp h).2⟩
    rw [hi₀_eq] at hmem
    exact hj (Finset.mem_singleton.mp hmem)
  let U : Set (ℝ × ℝ) := {p : ℝ × ℝ | inOmega p} \ ⋃ j ∈ (Finset.univ : Finset (Fin 5)), Gamma (W j)
  have h_real_U : ∀ m : Fin 5 → Bool, ∃ p ∈ U, RealizesWedgeMask W m p := by
    intro m
    obtain ⟨p, hp_om, hp_real⟩ := h_masks m
    refine ⟨p, ⟨hp_om, fun hU => ?_⟩, hp_real⟩
    rw [Set.mem_iUnion₂] at hU
    rcases hU with ⟨j, _, hjG⟩
    cases hmj : m j
    · exact hjG.1.2 (by simpa [hmj] using hp_real j)
    · exact hjG.1.1 (by simpa [hmj] using hp_real j)
  have h_lower32 : (32 : ℕ∞) ≤ (Comps U).encard := by
    let pt32 : (Fin 5 → Bool) → ℝ × ℝ := fun m => (h_real_U m).choose
    have hpt_U : ∀ m, pt32 m ∈ U := fun m => (h_real_U m).choose_spec.1
    have hpt_inj : ∀ m₁ m₂ : Fin 5 → Bool, m₁ ≠ m₂ →
        connectedComponentIn U (pt32 m₁) ≠ connectedComponentIn U (pt32 m₂) := by
      intro m₁ m₂ hne
      have hj_ex : ∃ j : Fin 5, m₁ j ≠ m₂ j := by
        by_contra hnone; push Not at hnone; exact hne (funext hnone)
      obtain ⟨j, hj⟩ := hj_ex
      have hr1 := (h_real_U m₁).choose_spec.2 j
      have hr2 := (h_real_U m₂).choose_spec.2 j
      have hsep : ((W j).MemOpen (pt32 m₁) ∧ (W j).MemExt (pt32 m₂)) ∨
          ((W j).MemExt (pt32 m₁) ∧ (W j).MemOpen (pt32 m₂)) := by
        cases h1 : m₁ j <;> cases h2 : m₂ j
        · exact False.elim (hj (h1.trans h2.symm))
        · exact Or.inr ⟨by simpa [pt32, h1] using hr1, by simpa [pt32, h2] using hr2⟩
        · exact Or.inl ⟨by simpa [pt32, h1] using hr1, by simpa [pt32, h2] using hr2⟩
        · exact False.elim (hj (h1.trans h2.symm))
      exact comp_ne_of_sep_wedge (Finset.mem_univ j) (hpt_U m₁) (hpt_U m₂) hsep
    have hcard32 : 32 ≤ Fintype.card (Fin 5 → Bool) := by
      rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
      norm_num
    exact (Nat.cast_le.mpr hcard32).trans (card_le_comps_of_inj pt32 hpt_U hpt_inj)
  have h_upper32 : (Comps U).encard ≤ 32 := by
    have hbound := arr_comps_bound hGP h_apex Finset.univ
    have h_sum_nat : ∑ i : Fin 5, ∑ j ∈ (Finset.univ : Finset (Fin 5)).filter (i < ·),
          (Gamma (W i) ∩ Gamma (W j)).ncard ≤
        ∑ i : Fin 5, ∑ j ∈ Finset.univ.filter (i < ·),
          (if i = i₀ ∨ j = i₀ then (2 : ℕ) else 3) := by
      refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j hj => ?_
      have hij : i < j := (Finset.mem_filter.mp hj).2
      split_ifs with h0
      · rcases h0 with rfl | rfl
        · exact inter_card_le_two_of_Llt_Lgt W pa pb h_apex hxa hya hxb hyb hC ha hb
            hi₀_lt (h_other_gt j (ne_of_gt hij))
        · rw [Set.inter_comm]
          exact inter_card_le_two_of_Llt_Lgt W pa pb h_apex hxa hya hxb hyb hC ha hb
            hi₀_lt (h_other_gt i (ne_of_lt hij))
      · push Not at h0
        exact inter_card_le_three_of_Lgt hGP pa pb h_apex hxa hya hxb hyb hC ha hb
          (ne_of_lt hij) (h_other_gt i h0.1) (h_other_gt j h0.2)
    have h_sum_le : ∑ i : Fin 5, ∑ j ∈ (Finset.univ : Finset (Fin 5)).filter (i < ·),
          ((Gamma (W i) ∩ Gamma (W j)).ncard : ℕ∞) ≤
        ((∑ i : Fin 5, ∑ j ∈ Finset.univ.filter (i < ·),
          (if i = i₀ ∨ j = i₀ then (2 : ℕ) else 3) : ℕ) : ℕ∞) := by
      calc ∑ i : Fin 5, ∑ j ∈ (Finset.univ : Finset (Fin 5)).filter (i < ·),
            ((Gamma (W i) ∩ Gamma (W j)).ncard : ℕ∞)
          = ((∑ i : Fin 5, ∑ j ∈ (Finset.univ : Finset (Fin 5)).filter (i < ·),
              (Gamma (W i) ∩ Gamma (W j)).ncard : ℕ) : ℕ∞) := by
            simp only [Nat.cast_sum]
        _ ≤ ((∑ i : Fin 5, ∑ j ∈ Finset.univ.filter (i < ·),
              (if i = i₀ ∨ j = i₀ then (2 : ℕ) else 3) : ℕ) : ℕ∞) :=
            Nat.cast_le.mpr h_sum_nat
    have h32 := fin5_k4_sum_max32 i₀
    calc (Comps U).encard
        ≤ 1 + ((Finset.univ : Finset (Fin 5)).card : ℕ∞) +
            ∑ i : Fin 5, ∑ j ∈ (Finset.univ : Finset (Fin 5)).filter (i < ·),
              ((Gamma (W i) ∩ Gamma (W j)).ncard : ℕ∞) := hbound
      _ ≤ (6 : ℕ∞) + ((∑ i : Fin 5, ∑ j ∈ Finset.univ.filter (i < ·),
            (if i = i₀ ∨ j = i₀ then (2 : ℕ) else 3) : ℕ) : ℕ∞) := by
          refine add_le_add ?_ h_sum_le
          exact le_of_eq (by rw [Finset.card_fin]; norm_num)
      _ = ((6 + ∑ i : Fin 5, ∑ j ∈ Finset.univ.filter (i < ·),
            (if i = i₀ ∨ j = i₀ then (2 : ℕ) else 3) : ℕ) : ℕ∞) := by push_cast; rfl
      _ = 32 := by rw [h32]; norm_num
  have h_ncard_eq2 : ∀ j : Fin 5, j ≠ i₀ → (Gamma (W i₀) ∩ Gamma (W j)).ncard = 2 := by
    intro j₁ hj₁
    have hle2 : (Gamma (W i₀) ∩ Gamma (W j₁)).ncard ≤ 2 :=
      inter_card_le_two_of_Llt_Lgt W pa pb h_apex hxa hya hxb hyb hC ha hb hi₀_lt (h_other_gt j₁ hj₁)
    by_contra hne2
    have hle1 : (Gamma (W i₀) ∩ Gamma (W j₁)).ncard ≤ 1 := by omega
    have hbound := arr_comps_bound hGP h_apex Finset.univ
    have h_sum_nat : ∑ i : Fin 5, ∑ j ∈ (Finset.univ : Finset (Fin 5)).filter (i < ·),
          (Gamma (W i) ∩ Gamma (W j)).ncard ≤
        ∑ i : Fin 5, ∑ j ∈ Finset.univ.filter (i < ·),
          (if (i = i₀ ∧ j = j₁) ∨ (i = j₁ ∧ j = i₀) then (1 : ℕ)
           else if i = i₀ ∨ j = i₀ then 2 else 3) := by
      refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j hj => ?_
      have hij : i < j := (Finset.mem_filter.mp hj).2
      split_ifs with hp h0
      · rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact hle1
        · rw [Set.inter_comm]; exact hle1
      · rcases h0 with rfl | rfl
        · exact inter_card_le_two_of_Llt_Lgt W pa pb h_apex hxa hya hxb hyb hC ha hb
            hi₀_lt (h_other_gt j (ne_of_gt hij))
        · rw [Set.inter_comm]
          exact inter_card_le_two_of_Llt_Lgt W pa pb h_apex hxa hya hxb hyb hC ha hb
            hi₀_lt (h_other_gt i (ne_of_lt hij))
      · push Not at h0
        exact inter_card_le_three_of_Lgt hGP pa pb h_apex hxa hya hxb hyb hC ha hb
          (ne_of_lt hij) (h_other_gt i h0.1) (h_other_gt j h0.2)
    have h_sum_le : ∑ i : Fin 5, ∑ j ∈ (Finset.univ : Finset (Fin 5)).filter (i < ·),
          ((Gamma (W i) ∩ Gamma (W j)).ncard : ℕ∞) ≤
        ((∑ i : Fin 5, ∑ j ∈ Finset.univ.filter (i < ·),
          (if (i = i₀ ∧ j = j₁) ∨ (i = j₁ ∧ j = i₀) then (1 : ℕ)
           else if i = i₀ ∨ j = i₀ then 2 else 3) : ℕ) : ℕ∞) := by
      calc ∑ i : Fin 5, ∑ j ∈ (Finset.univ : Finset (Fin 5)).filter (i < ·),
            ((Gamma (W i) ∩ Gamma (W j)).ncard : ℕ∞)
          = ((∑ i : Fin 5, ∑ j ∈ (Finset.univ : Finset (Fin 5)).filter (i < ·),
              (Gamma (W i) ∩ Gamma (W j)).ncard : ℕ) : ℕ∞) := by
            simp only [Nat.cast_sum]
        _ ≤ ((∑ i : Fin 5, ∑ j ∈ Finset.univ.filter (i < ·),
              (if (i = i₀ ∧ j = j₁) ∨ (i = j₁ ∧ j = i₀) then (1 : ℕ)
               else if i = i₀ ∨ j = i₀ then 2 else 3) : ℕ) : ℕ∞) :=
            Nat.cast_le.mpr h_sum_nat
    have h31 := fin5_k4_sum_drop1 i₀ j₁ hj₁
    have h_upper31 : (Comps U).encard ≤ 31 := by
      calc (Comps U).encard
          ≤ 1 + ((Finset.univ : Finset (Fin 5)).card : ℕ∞) +
              ∑ i : Fin 5, ∑ j ∈ (Finset.univ : Finset (Fin 5)).filter (i < ·),
                ((Gamma (W i) ∩ Gamma (W j)).ncard : ℕ∞) := hbound
        _ ≤ (6 : ℕ∞) + ((∑ i : Fin 5, ∑ j ∈ Finset.univ.filter (i < ·),
              (if (i = i₀ ∧ j = j₁) ∨ (i = j₁ ∧ j = i₀) then (1 : ℕ)
               else if i = i₀ ∨ j = i₀ then 2 else 3) : ℕ) : ℕ∞) := by
            refine add_le_add ?_ h_sum_le
            exact le_of_eq (by rw [Finset.card_fin]; norm_num)
        _ = ((6 + ∑ i : Fin 5, ∑ j ∈ Finset.univ.filter (i < ·),
              (if (i = i₀ ∧ j = j₁) ∨ (i = j₁ ∧ j = i₀) then (1 : ℕ)
               else if i = i₀ ∨ j = i₀ then 2 else 3) : ℕ) : ℕ∞) := by push_cast; rfl
        _ = 31 := by rw [h31]; norm_num
    exact absurd (h_lower32.trans h_upper31) (by decide)
  let j₁ : Fin 5 := if i₀ = 0 then 1 else 0
  have hj₁ : j₁ ≠ i₀ := by
    dsimp [j₁]; split_ifs with h
    · simp [h]
    · exact Ne.symm h
  have hLgt_normals : ∀ j : Fin 5, j ≠ i₀ →
      (W j).u₁.1 < 0 ∧ (W j).u₁.2 < 0 ∧ (W j).u₂.1 < 0 ∧ (W j).u₂.2 < 0 := fun j hj =>
    caseB_Lgt_normals_neg (W j) pa pb (h_apex j).1 (h_apex j).2 hxa hya hxb hyb hC
      (ha j) (hb j) (h_other_gt j hj)
  obtain ⟨hd1_neg, hd2_neg, hd1_y_pos, hd2_x_pos⟩ :=
    k4_ray_dirs pa pb h_apex hxa hya hxb hyb hC ha hb i₀ j₁ hj₁ hi₀_lt hi₀_origin
      h_other_gt h_ncard_eq2 hLgt_normals
  -- Construct barrier curve `g` and disjoint open sets `U_above`, `U_below`
  let g : ℝ → ℝ := fun X => if X ≤ pb.1 then pb.2 else (pb.2 / pb.1) * X
  have hg_cont : Continuous g := by
    rw [← continuousOn_univ, show (Set.univ : Set ℝ) = Set.Iic pb.1 ∪ Set.Ici pb.1 from
      (Set.Iic_union_Ici).symm]
    refine ContinuousOn.union_of_isClosed ?_ ?_ isClosed_Iic isClosed_Ici
    · exact (continuousOn_const (c := pb.2)).congr fun X hX => by simp [g, Set.mem_Iic.mp hX]
    · refine ((continuousOn_const (c := pb.2 / pb.1)).mul continuousOn_id).congr fun X hX => ?_
      by_cases hle : X ≤ pb.1
      · have hXeq : X = pb.1 := le_antisymm hle (Set.mem_Ici.mp hX)
        subst hXeq; simp [g, div_mul_cancel₀ _ (ne_of_lt hxb)]
      · simp [g, hle]
  have hg_in_union : ∀ X < 0, (W i₀).MemOpen (X, g X) ∨ (W j₁).MemOpen (X, g X) := by
    intro X hX
    have hray_j1 : ∀ t : ℝ, 0 ≤ t → (W j₁).MemOpen (pb.1 - t, pb.2) := by
      intro t ht
      obtain ⟨hu11, _, hu21, _⟩ := hLgt_normals j₁ hj₁
      obtain ⟨hb1, hb2⟩ := hb j₁
      constructor
      · have : (W j₁).u₁.1 * ((pb.1 - t) - (W j₁).y.1) + (W j₁).u₁.2 * (pb.2 - (W j₁).y.2) =
            ((W j₁).u₁.1 * (pb.1 - (W j₁).y.1) + (W j₁).u₁.2 * (pb.2 - (W j₁).y.2)) +
            t * (-(W j₁).u₁.1) := by ring
        rw [this]; nlinarith
      · have : (W j₁).u₂.1 * ((pb.1 - t) - (W j₁).y.1) + (W j₁).u₂.2 * (pb.2 - (W j₁).y.2) =
            ((W j₁).u₂.1 * (pb.1 - (W j₁).y.1) + (W j₁).u₂.2 * (pb.2 - (W j₁).y.2)) +
            t * (-(W j₁).u₂.1) := by ring
        rw [this]; nlinarith
    exact caseB_k4_barrier_in_union {p | (W i₀).MemOpen p} {p | (W j₁).MemOpen p}
      pb.1 pb.2 X hxb hyb hX hi₀_origin (hb i₀) (hb j₁) (memOpen_convex (W i₀)) hray_j1
  let U_above : Set (ℝ × ℝ) := {p : ℝ × ℝ | p.1 < 0 ∧ g p.1 < p.2}
  let U_below : Set (ℝ × ℝ) := {p : ℝ × ℝ | p.2 < 0} ∪ {p : ℝ × ℝ | p.1 < 0 ∧ p.2 < g p.1}
  have hUa_open : IsOpen U_above :=
    (isOpen_lt continuous_fst continuous_const).inter
      (isOpen_lt (hg_cont.comp continuous_fst) continuous_snd)
  have hUb_open : IsOpen U_below :=
    (isOpen_lt continuous_snd continuous_const).union
      ((isOpen_lt continuous_fst continuous_const).inter
        (isOpen_lt continuous_snd (hg_cont.comp continuous_fst)))
  have hUab_disj : Disjoint U_above U_below := by
    rw [Set.disjoint_left]
    rintro p ⟨hp1, hp2⟩ (hp_neg | ⟨_, hp_lt⟩)
    · have : 0 < g p.1 := by
        dsimp [g]; split_ifs
        · exact hyb
        · exact mul_pos_of_neg_of_neg (div_neg_of_pos_of_neg hyb hxb) hp1
      change p.2 < 0 at hp_neg
      linarith
    · linarith
  obtain ⟨p_hi, hp_hi_U, hp_hi_ext, hp_hi_x, hp_hi_y⟩ :=
    k4_exists_p_hi pb hxb i₀ j₁ hj₁ hLgt_normals hd1_neg hd1_y_pos
  have hp_hi_above : p_hi ∈ U_above := ⟨hp_hi_x, hp_hi_y⟩
  obtain ⟨p_lo, hp_lo_U, hp_lo_ext, hp_lo_y⟩ :=
    k4_exists_p_lo h_apex i₀ j₁ hj₁ hLgt_normals hd2_neg hd2_x_pos
  have hp_lo_below : p_lo ∈ U_below := Or.inl hp_lo_y
  have hcomp_hi_lo_ne : connectedComponentIn U p_hi ≠ connectedComponentIn U p_lo := by
    intro heq
    have hp_lo_in : p_lo ∈ connectedComponentIn U p_hi := by
      rw [heq]; exact mem_connectedComponentIn hp_lo_U
    have hp_hi_in : p_hi ∈ connectedComponentIn U p_hi := mem_connectedComponentIn hp_hi_U
    have hsub : connectedComponentIn U p_hi ⊆ U_above ∪ U_below := by
      intro q hq
      have hqU : q ∈ U := connectedComponentIn_subset U p_hi hq
      have hq_ext : ∀ j : Fin 5, (W j).MemExt q := by
        intro j
        by_contra hnot
        have hq_nbd : q ∉ bdWedge (W j) := fun hbd =>
          hqU.2 (Set.mem_iUnion₂.mpr ⟨j, Finset.mem_univ j, hbd, hqU.1⟩)
        dsimp [bdWedge] at hq_nbd; push Not at hq_nbd
        have hq_open : (W j).MemOpen q := by
          by_contra hno; exact hnot (hq_nbd hno)
        exact comp_ne_of_sep_wedge (Finset.mem_univ j) hqU hp_hi_U
          (Or.inl ⟨hq_open, hp_hi_ext j⟩) (connectedComponentIn_eq hq).symm
      by_cases hqy : q.2 < 0
      · exact Or.inr (Or.inl hqy)
      · have hqx : q.1 < 0 := hqU.1.resolve_right hqy
        have hq_ne_g : q.2 ≠ g q.1 := by
          intro hqeq
          have hmem_un := hg_in_union q.1 hqx
          have hpt_eq : (q.1, g q.1) = q := Prod.ext rfl hqeq.symm
          rw [hpt_eq] at hmem_un
          rcases hmem_un with ho1 | ho2
          · exact memOpen_memExt_disjoint (W i₀) q ⟨ho1, hq_ext i₀⟩
          · exact memOpen_memExt_disjoint (W j₁) q ⟨ho2, hq_ext j₁⟩
        rcases lt_or_gt_of_ne hq_ne_g with hlt | hgt
        · exact Or.inr (Or.inr ⟨hqx, hlt⟩)
        · exact Or.inl ⟨hqx, hgt⟩
    rcases isPreconnected_connectedComponentIn.subset_or_subset
        hUa_open hUb_open hUab_disj hsub with hA | hB
    · exact Set.disjoint_left.mp hUab_disj (hA hp_lo_in) hp_lo_below
    · exact Set.disjoint_left.mp hUab_disj hp_hi_above (hB hp_hi_in)
  -- Inject `Option (Option {m : Fin 5 → Bool // m ≠ fun _ => false})` (size 33) into `Comps U`
  let m0 : Fin 5 → Bool := fun _ => false
  let pt33 : Option (Option {m : Fin 5 → Bool // m ≠ m0}) → ℝ × ℝ
    | none => p_hi
    | some none => p_lo
    | some (some m) => (h_real_U m.1).choose
  have hpt33_U : ∀ x, pt33 x ∈ U := by
    rintro (_ | _ | m)
    · exact hp_hi_U
    · exact hp_lo_U
    · exact (h_real_U m.1).choose_spec.1
  have hpt33_inj : ∀ x₁ x₂, x₁ ≠ x₂ →
      connectedComponentIn U (pt33 x₁) ≠ connectedComponentIn U (pt33 x₂) := by
    intro x₁ x₂ hne
    have sep_m0 : ∀ {q : ℝ × ℝ} {m : {m : Fin 5 → Bool // m ≠ m0}},
        q ∈ U → (∀ j : Fin 5, (W j).MemExt q) →
        connectedComponentIn U q ≠ connectedComponentIn U (h_real_U m.1).choose := by
      intro q m hqU hq_ext
      have hj_ex : ∃ j : Fin 5, m.1 j = true := by
        by_contra hnone; push Not at hnone
        apply m.2; funext j
        cases hmj : m.1 j
        · rfl
        · exact False.elim (hnone j hmj)
      obtain ⟨j, hj⟩ := hj_ex
      have hopen : (W j).MemOpen (h_real_U m.1).choose := by
        simpa [hj] using (h_real_U m.1).choose_spec.2 j
      exact comp_ne_of_sep_wedge (Finset.mem_univ j) hqU (h_real_U m.1).choose_spec.1
        (Or.inr ⟨hq_ext j, hopen⟩)
    rcases x₁ with _ | _ | m₁ <;> rcases x₂ with _ | _ | m₂
    · exact False.elim (hne rfl)
    · exact hcomp_hi_lo_ne
    · exact sep_m0 hp_hi_U hp_hi_ext
    · exact hcomp_hi_lo_ne.symm
    · exact False.elim (hne rfl)
    · exact sep_m0 hp_lo_U hp_lo_ext
    · exact (sep_m0 hp_hi_U hp_hi_ext).symm
    · exact (sep_m0 hp_lo_U hp_lo_ext).symm
    · have hm_ne : m₁.1 ≠ m₂.1 := fun h =>
        hne (congrArg (Option.some ∘ Option.some) (Subtype.ext h))
      have hj_ex : ∃ j : Fin 5, m₁.1 j ≠ m₂.1 j := by
        by_contra hnone; push Not at hnone; exact hm_ne (funext hnone)
      obtain ⟨j, hj⟩ := hj_ex
      have hr1 := (h_real_U m₁.1).choose_spec.2 j
      have hr2 := (h_real_U m₂.1).choose_spec.2 j
      have hsep : ((W j).MemOpen (pt33 (some (some m₁))) ∧ (W j).MemExt (pt33 (some (some m₂)))) ∨
          ((W j).MemExt (pt33 (some (some m₁))) ∧ (W j).MemOpen (pt33 (some (some m₂)))) := by
        cases h1 : m₁.1 j <;> cases h2 : m₂.1 j
        · exact False.elim (hj (h1.trans h2.symm))
        · exact Or.inr ⟨by simpa [pt33, h1] using hr1, by simpa [pt33, h2] using hr2⟩
        · exact Or.inl ⟨by simpa [pt33, h1] using hr1, by simpa [pt33, h2] using hr2⟩
        · exact False.elim (hj (h1.trans h2.symm))
      exact comp_ne_of_sep_wedge (Finset.mem_univ j)
        (hpt33_U (some (some m₁))) (hpt33_U (some (some m₂))) hsep
  have h_lower33 : (33 : ℕ∞) ≤ (Comps U).encard := by
    have hcard_sub : Fintype.card {m : Fin 5 → Bool // m ≠ m0} = 31 := by
      have h := Fintype.card_subtype_compl (fun m : Fin 5 → Bool => m = m0)
      rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] at h
      have h1 : Fintype.card {m : Fin 5 → Bool // m = m0} = 1 := by
        rw [Fintype.card_eq_one_iff]
        exact ⟨⟨m0, rfl⟩, fun ⟨m, hm⟩ => Subtype.ext hm⟩
      have h2 : Fintype.card {m : Fin 5 → Bool // m ≠ m0} =
          Fintype.card {m : Fin 5 → Bool // ¬(fun m => m = m0) m} :=
        Fintype.card_congr (Equiv.refl _)
      rw [h2, h, h1]
      norm_num
    have hcard33 : 33 ≤ Fintype.card (Option (Option {m : Fin 5 → Bool // m ≠ m0})) := by
      simp only [Fintype.card_option, hcard_sub]
      omega
    exact (Nat.cast_le.mpr hcard33).trans (card_le_comps_of_inj pt33 hpt33_U hpt33_inj)
  exact absurd (h_lower33.trans h_upper32) (by decide)

end CaseB
end
