import RootTask.CaseBFace

open scoped BigOperators Classical

noncomputable section

namespace CaseB

/-! ## Interval Witnesses Adjacent to Sorted Crossings -/

lemma exists_left_mem_seg : ∀ (xs : List ℝ), xs.SortedLT →
    ∀ (k : Fin xs.length) (δ : ℝ), 0 < δ →
      ∃ s ∈ seg xs k.castSucc, xs.get k - δ < s ∧ s < xs.get k
  | [], _, k, _, _ => Fin.elim0 k
  | a :: _, _, ⟨0, _⟩, δ, hδ =>
    ⟨a - δ / 2, by change a - δ / 2 < a; linarith, by simp; linarith⟩
  | a :: tl, hsort, ⟨k + 1, hk⟩, δ, hδ => by
    have hk' : k < tl.length := Nat.lt_of_succ_lt_succ hk
    have htl_sort : tl.SortedLT := fun i j hij => hsort (Fin.succ_lt_succ_iff.mpr hij)
    have ha_lt : a < tl.get ⟨k, hk'⟩ :=
      hsort (Fin.mk_lt_mk.mpr (Nat.zero_lt_succ k) :
        (⟨0, by simp⟩ : Fin (a :: tl).length) < ⟨k + 1, hk⟩)
    let δ' : ℝ := min δ ((tl.get ⟨k, hk'⟩ - a) / 2)
    have hδ' : 0 < δ' := lt_min hδ (by linarith)
    obtain ⟨s, hs, hlo, hhi⟩ := exists_left_mem_seg tl htl_sort ⟨k, hk'⟩ δ' hδ'
    have hlo' : tl.get ⟨k, hk'⟩ - δ < s :=
      lt_of_le_of_lt (sub_le_sub_left (min_le_left _ _) _) hlo
    have h_a_s : a < s := by
      have h1 : tl.get ⟨k, hk'⟩ - (tl.get ⟨k, hk'⟩ - a) / 2 ≤ tl.get ⟨k, hk'⟩ - δ' :=
        sub_le_sub_left (min_le_right _ _) _
      linarith
    exact ⟨s, ⟨hs, h_a_s⟩, by simpa using hlo', by simpa using hhi⟩

lemma exists_right_mem_seg : ∀ (xs : List ℝ), xs.SortedLT →
    ∀ (k : Fin xs.length) (δ : ℝ), 0 < δ →
      ∃ s ∈ seg xs k.succ, xs.get k < s ∧ s < xs.get k + δ
  | [], _, k, _, _ => Fin.elim0 k
  | a :: [], _, ⟨0, _⟩, δ, hδ =>
    ⟨a + δ / 2, by change True ∧ a < a + δ / 2; exact ⟨trivial, by linarith⟩,
      by simp; linarith⟩
  | a :: b :: _, hsort, ⟨0, _⟩, δ, hδ => by
    have hab : a < b := hsort (Fin.mk_lt_mk.mpr Nat.zero_lt_one :
      (⟨0, by simp⟩ : Fin (a :: b :: _).length) < ⟨1, by simp⟩)
    let ε : ℝ := min (δ / 2) ((b - a) / 2)
    have hε : 0 < ε := lt_min (by linarith) (by linarith)
    refine ⟨a + ε, ?_, ?_, ?_⟩
    · change a + ε < b ∧ a < a + ε
      exact ⟨by linarith [min_le_right (δ / 2) ((b - a) / 2)], by linarith⟩
    · simp; linarith
    · simp; linarith [min_le_left (δ / 2) ((b - a) / 2)]
  | a :: tl, hsort, ⟨k + 1, hk⟩, δ, hδ => by
    have hk' : k < tl.length := Nat.lt_of_succ_lt_succ hk
    have htl_sort : tl.SortedLT := fun i j hij => hsort (Fin.succ_lt_succ_iff.mpr hij)
    have ha_lt : a < tl.get ⟨k, hk'⟩ :=
      hsort (Fin.mk_lt_mk.mpr (Nat.zero_lt_succ k) :
        (⟨0, by simp⟩ : Fin (a :: tl).length) < ⟨k + 1, hk⟩)
    obtain ⟨s, hs, hlo, hhi⟩ := exists_right_mem_seg tl htl_sort ⟨k, hk'⟩ δ hδ
    exact ⟨s, ⟨hs, ha_lt.trans hlo⟩, by simpa using hlo, by simpa using hhi⟩

/-! ## Combinatorial 8-Mask Bound Along `Γ_{i₀}` -/

lemma eight_mask_bound_of_coord {α : Type*} [Fintype α] [DecidableEq α]
    (hcard4 : Fintype.card α = 4)
    (m : ℕ) (w : Fin (m + 1) → (α → Bool)) (coord : Fin m → α)
    (h_step : ∀ (k : Fin m) (a : α), a ≠ coord k → w k.castSucc a = w k.succ a)
    (h_le2 : ∀ a : α, (Finset.univ.filter (fun k : Fin m => coord k = a)).card ≤ 2) :
    (Finset.univ.image w).card ≤ 8 := by
  have hm_sum : m = ∑ a : α, (Finset.univ.filter (fun k : Fin m => coord k = a)).card := by
    have hfib := Finset.card_eq_sum_card_fiberwise
      (f := coord) (s := (Finset.univ : Finset (Fin m))) (t := (Finset.univ : Finset α))
      (fun k _ => Finset.mem_univ (coord k))
    simpa only [Finset.card_univ, Fintype.card_fin] using hfib
  have hm_le8 : m ≤ 8 := by
    calc m = ∑ a : α, (Finset.univ.filter (fun k : Fin m => coord k = a)).card := hm_sum
      _ ≤ ∑ _a : α, 2 := Finset.sum_le_sum fun a _ => h_le2 a
      _ = 8 := by simp [hcard4]
  rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ (Nat.lt_succ_of_le hm_le8)) with hm7 | rfl
  · calc (Finset.univ.image w).card
        ≤ (Finset.univ : Finset (Fin (m + 1))).card := Finset.card_image_le
      _ = m + 1 := Finset.card_fin (m + 1)
      _ ≤ 8 := by omega
  · by_cases h_eq : ∃ k : Fin 8, w k.castSucc (coord k) = w k.succ (coord k)
    · obtain ⟨k, hk⟩ := h_eq
      have hwk : w k.castSucc = w k.succ := by
        funext a
        by_cases ha : a = coord k
        · rw [ha, hk]
        · exact h_step k a ha
      have himg : Finset.univ.image w = (Finset.univ.erase k.succ).image w := by
        ext v; simp only [Finset.mem_image, Finset.mem_univ, Finset.mem_erase, true_and, and_true]
        constructor
        · rintro ⟨t, rfl⟩
          by_cases ht : t = k.succ
          · exact ⟨k.castSucc, by simp [Fin.ext_iff], by rw [ht]; exact hwk⟩
          · exact ⟨t, ht, rfl⟩
        · rintro ⟨t, _, rfl⟩; exact ⟨t, rfl⟩
      rw [himg]
      calc ((Finset.univ.erase k.succ).image w).card
          ≤ (Finset.univ.erase k.succ).card := Finset.card_image_le
        _ = 8 := by rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_fin]
    · push Not at h_eq
      have h_eq2 : ∀ a : α, (Finset.univ.filter (fun k : Fin 8 => coord k = a)).card = 2 := by
        intro a
        by_contra hne
        have hlt : (Finset.univ.filter (fun k : Fin 8 => coord k = a)).card < 2 :=
          lt_of_le_of_ne (h_le2 a) hne
        have hsum_lt : ∑ x : α, (Finset.univ.filter (fun k : Fin 8 => coord k = x)).card <
            ∑ _x : α, 2 :=
          Finset.sum_lt_sum (fun x _ => h_le2 x) ⟨a, Finset.mem_univ a, hlt⟩
        simp only [Finset.sum_const, Finset.card_univ, hcard4, smul_eq_mul, mul_two] at hsum_lt
        omega
      have h_parity : ∀ (t : ℕ) (ht : t ≤ 8) (a : α),
          w ⟨t, Nat.lt_succ_of_le ht⟩ a =
            if (Finset.univ.filter (fun k : Fin 8 => k.val < t ∧ coord k = a)).card % 2 = 0
            then w 0 a else !(w 0 a) := by
        intro t
        induction t with
        | zero =>
          intro ht a
          have heq0 : (Finset.univ.filter (fun k : Fin 8 => k.val < 0 ∧ coord k = a)) = ∅ := by
            ext k; simp
          rw [heq0]; simp
        | succ t ih =>
          intro ht a
          let k : Fin 8 := ⟨t, ht⟩
          have ih' := ih (Nat.le_of_lt ht) a
          have h_filter : Finset.univ.filter (fun j : Fin 8 => j.val < t + 1 ∧ coord j = a) =
              if coord k = a then
                insert k (Finset.univ.filter (fun j : Fin 8 => j.val < t ∧ coord j = a))
              else
                Finset.univ.filter (fun j : Fin 8 => j.val < t ∧ coord j = a) := by
            ext j
            split_ifs with hck <;> simp only [Finset.mem_filter, Finset.mem_univ, true_and,
              Finset.mem_insert]
            · constructor
              · rintro ⟨hj, hcj⟩
                rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj' | hj'
                · right; exact ⟨hj', hcj⟩
                · left; exact Fin.ext hj'
              · rintro (rfl | ⟨hj, hcj⟩)
                · exact ⟨Nat.lt_succ_self t, hck⟩
                · exact ⟨Nat.lt_succ_of_lt hj, hcj⟩
            · constructor
              · rintro ⟨hj, hcj⟩
                refine ⟨(Nat.lt_succ_iff_lt_or_eq.mp hj).resolve_right fun hj' => ?_, hcj⟩
                apply hck
                have hjk : j = k := Fin.ext hj'
                rw [← hjk]; exact hcj
              · rintro ⟨hj, hcj⟩; exact ⟨Nat.lt_succ_of_lt hj, hcj⟩
          by_cases hck : coord k = a
          · have hk_not : k ∉ Finset.univ.filter (fun j : Fin 8 => j.val < t ∧ coord j = a) := by
              simp [k]
            rw [h_filter, if_pos hck, Finset.card_insert_of_notMem hk_not]
            have hflip : w k.succ a = !(w k.castSucc a) := by
              have hne := h_eq k
              rw [hck] at hne
              cases h1 : w k.castSucc a <;> cases h2 : w k.succ a <;> simp_all
            have hcast : k.castSucc = ⟨t, Nat.lt_succ_of_le (Nat.le_of_lt ht)⟩ := rfl
            have hsucc : k.succ = ⟨t + 1, Nat.lt_succ_of_le ht⟩ := rfl
            rw [← hsucc, hflip, hcast, ih']
            split_ifs <;> first | omega | simp
          · rw [h_filter, if_neg hck]
            have hsame : w k.succ a = w k.castSucc a := (h_step k a (Ne.symm hck)).symm
            have hcast : k.castSucc = ⟨t, Nat.lt_succ_of_le (Nat.le_of_lt ht)⟩ := rfl
            have hsucc : k.succ = ⟨t + 1, Nat.lt_succ_of_le ht⟩ := rfl
            rw [← hsucc, hsame, hcast, ih']
      have hw8 : w (Fin.last 8) = w 0 := by
        funext a
        have hp := h_parity 8 le_rfl a
        have hf : Finset.univ.filter (fun k : Fin 8 => k.val < 8 ∧ coord k = a) =
            Finset.univ.filter (fun k : Fin 8 => coord k = a) := by
          ext k; simp
        rw [hf, h_eq2 a] at hp
        simpa [Fin.last] using hp
      have himg : Finset.univ.image w = (Finset.univ.erase (Fin.last 8)).image w := by
        ext v; simp only [Finset.mem_image, Finset.mem_univ, Finset.mem_erase, true_and, and_true]
        constructor
        · rintro ⟨t, rfl⟩
          by_cases ht : t = Fin.last 8
          · exact ⟨0, by simp [Fin.ext_iff], by rw [ht]; exact hw8.symm⟩
          · exact ⟨t, ht, rfl⟩
        · rintro ⟨t, _, rfl⟩; exact ⟨t, rfl⟩
      rw [himg]
      calc ((Finset.univ.erase (Fin.last 8)).image w).card
          ≤ (Finset.univ.erase (Fin.last 8)).card := Finset.card_image_le
        _ = 8 := by rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_fin]

/-! ## Case B (`k = 1`) Elimination -/

theorem caseB_k1_elim {W : Fin 5 → OpenWedge} (hGP : GeneralPosition W)
    (pa pb : ℝ × ℝ)
    (h_apex : ∀ k : Fin 5, (W k).y.1 < 0 ∧ (W k).y.2 < 0)
    (hxa : 0 < pa.1) (hya : pa.2 < 0) (hxb : pb.1 < 0) (hyb : 0 < pb.2)
    (hC : pa.1 * pb.2 - pa.2 * pb.1 < 0)
    (ha : ∀ k : Fin 5, (W k).MemOpen pa) (hb : ∀ k : Fin 5, (W k).MemOpen pb)
    (h_masks : ∀ m : Fin 5 → Bool, ∃ p : ℝ × ℝ, inOmega p ∧ RealizesWedgeMask W m p)
    (hk1 : (Finset.univ.filter (fun i : Fin 5 => isLgt (W i) pa pb)).card = 1) :
    False := by
  obtain ⟨i₀, hi₀_eq⟩ := Finset.card_eq_one.mp hk1
  have hi₀_gt : isLgt (W i₀) pa pb := by
    have hmem : i₀ ∈ Finset.univ.filter (fun i : Fin 5 => isLgt (W i) pa pb) := by
      rw [hi₀_eq]; exact Finset.mem_singleton_self i₀
    exact (Finset.mem_filter.mp hmem).2
  let S : Finset (Fin 5) := Finset.univ.erase i₀
  have hi₀_nS : i₀ ∉ S := Finset.notMem_erase i₀ _
  have hS_card : S.card = 4 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_fin]
  have hS_lt : ∀ j ∈ S, isLlt (W j) pa pb := by
    intro j hj
    have hne : j ≠ i₀ := Finset.ne_of_mem_erase hj
    have hngt : ¬ isLgt (W j) pa pb := by
      intro hgt
      have hmem : j ∈ ({i₀} : Finset (Fin 5)) := by
        rw [← hi₀_eq]; exact Finset.mem_filter.mpr ⟨Finset.mem_univ j, hgt⟩
      exact hne (Finset.mem_singleton.mp hmem)
    exact (caseB_dichotomy (W j) pa pb (h_apex j).1 (h_apex j).2
      hxa hya hxb hyb hC (ha j) (hb j)).resolve_right hngt
  have hS_origin : ∀ j ∈ S, (W j).MemOpen (0, 0) := fun j hj =>
    case_b_origin_in_wedge (W j) pa pb (h_apex j).1 (h_apex j).2
      hxa hya hxb hyb hC (ha j) (hb j) (hS_lt j hj)
  let U : Set (ℝ × ℝ) := {p : ℝ × ℝ | inOmega p} \ ⋃ j ∈ S, Gamma (W j)
  have h_comps_upper : (Comps U).encard ≤ 23 := by
    have hbound := arr_comps_bound hGP h_apex S
    have hpair_le : ∀ i ∈ S, ∀ j ∈ S, i < j →
        ((Gamma (W i) ∩ Gamma (W j)).ncard : ℕ∞) ≤ 3 := fun i hi j hj hij =>
      Nat.cast_le.mpr (inter_card_le_three_of_origin hGP h_apex (ne_of_lt hij)
        (hS_origin i hi) (hS_origin j hj))
    have h_sum_le : ∑ i ∈ S, ∑ j ∈ S with i < j, ((Gamma (W i) ∩ Gamma (W j)).ncard : ℕ∞) ≤
        ∑ i ∈ S, ∑ _j ∈ S with i < _j, (3 : ℕ∞) :=
      Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj =>
        hpair_le i hi j (Finset.mem_filter.mp hj).1 (Finset.mem_filter.mp hj).2
    have h_pairs6 : (∑ i ∈ S, (S.filter (i < ·)).card) = 6 := by
      dsimp [S]; fin_cases i₀ <;> decide
    have h_sum_eq18 : ∑ i ∈ S, ∑ _j ∈ S with i < _j, (3 : ℕ∞) = 18 := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      have h_cast : (∑ i ∈ S, ((S.filter (i < ·)).card : ℕ∞) * 3) =
          ((∑ i ∈ S, (S.filter (i < ·)).card : ℕ) : ℕ∞) * 3 := by
        rw [← Finset.sum_mul]; push_cast; rfl
      rw [h_cast, h_pairs6]
      norm_num
    calc (Comps U).encard
        ≤ 1 + (S.card : ℕ∞) +
            ∑ i ∈ S, ∑ j ∈ S with i < j, ((Gamma (W i) ∩ Gamma (W j)).ncard : ℕ∞) := hbound
      _ ≤ 1 + 4 + 18 := add_le_add (by rw [hS_card]; exact le_rfl) (h_sum_le.trans h_sum_eq18.le)
      _ = 23 := by norm_num
  let P_set : Set (ℝ × ℝ) := ⋃ j ∈ S, (Gamma (W i₀) ∩ Gamma (W j))
  have hP_fin : P_set.Finite :=
    S.finite_toSet.biUnion fun j hj => gamma_inter_finite hGP (Finset.ne_of_mem_erase hj).symm
  let P_param : Set ℝ := (gammaParam (W i₀)) ⁻¹' P_set
  have hP_param_fin : P_param.Finite :=
    hP_fin.preimage (gammaParam_injective (W i₀) (h_apex i₀).1 (h_apex i₀).2).injOn
  let xs : List ℝ := hP_param_fin.toFinset.sort (· ≤ ·)
  have hxs_sorted : xs.SortedLT := Finset.sortedLT_sort _
  have hxs_iff : ∀ s : ℝ, s ∈ xs ↔ gammaParam (W i₀) s ∈ P_set := fun s => by
    simp [xs, P_param]
  have hseg_sub : ∀ idx : Fin (xs.length + 1), gammaParam (W i₀) '' seg xs idx ⊆ U := by
    rintro idx p ⟨s, hs, rfl⟩
    refine ⟨(gammaParam_mem_Gamma (W i₀) (h_apex i₀).1 (h_apex i₀).2 s).2, fun hU => ?_⟩
    rw [Set.mem_iUnion₂] at hU
    rcases hU with ⟨j, hjS, hjG⟩
    have hP : gammaParam (W i₀) s ∈ P_set :=
      Set.mem_iUnion₂.mpr ⟨j, hjS, gammaParam_mem_Gamma (W i₀) (h_apex i₀).1 (h_apex i₀).2 s, hjG⟩
    exact seg_disjoint_list xs hxs_sorted idx hs ((hxs_iff s).mpr hP)
  have hseg_const : ∀ (idx : Fin (xs.length + 1)) (j : S) {s₁ s₂ : ℝ},
      s₁ ∈ seg xs idx → s₂ ∈ seg xs idx →
      ((W j.1).MemOpen (gammaParam (W i₀) s₁) ↔ (W j.1).MemOpen (gammaParam (W i₀) s₂)) := by
    intro idx j s₁ s₂ hs₁ hs₂
    have hconn : IsPreconnected (gammaParam (W i₀) '' seg xs idx) :=
      (seg_isPreconnected xs idx).image _ (gammaParam_continuous (W i₀)).continuousOn
    have hsub : gammaParam (W i₀) '' seg xs idx ⊆
        {p | (W j.1).MemOpen p} ∪ {p | (W j.1).MemExt p} := by
      rintro p hp
      have hpU := hseg_sub idx hp
      have hp_nbd : p ∉ bdWedge (W j.1) := fun hbd =>
        hpU.2 (Set.mem_iUnion₂.mpr ⟨j.1, j.2, hbd, hpU.1⟩)
      dsimp [bdWedge] at hp_nbd; push Not at hp_nbd
      by_cases ho : (W j.1).MemOpen p
      · left; exact ho
      · right; exact hp_nbd ho
    have hdisj : Disjoint {p | (W j.1).MemOpen p} {p | (W j.1).MemExt p} := by
      rw [Set.disjoint_left]; exact fun p ho he => memOpen_memExt_disjoint (W j.1) p ⟨ho, he⟩
    rcases hconn.subset_or_subset (isOpen_memOpen (W j.1)) (isOpen_memExt (W j.1)) hdisj hsub
        with hO | hE
    · exact iff_of_true (hO ⟨s₁, hs₁, rfl⟩) (hO ⟨s₂, hs₂, rfl⟩)
    · have hf1 : ¬ (W j.1).MemOpen (gammaParam (W i₀) s₁) := fun ho =>
        memOpen_memExt_disjoint (W j.1) _ ⟨ho, hE ⟨s₁, hs₁, rfl⟩⟩
      have hf2 : ¬ (W j.1).MemOpen (gammaParam (W i₀) s₂) := fun ho =>
        memOpen_memExt_disjoint (W j.1) _ ⟨ho, hE ⟨s₂, hs₂, rfl⟩⟩
      exact iff_of_false hf1 hf2
  let sRep (idx : Fin (xs.length + 1)) : ℝ := (seg_nonempty xs hxs_sorted idx).choose
  have hsRep_mem : ∀ idx, sRep idx ∈ seg xs idx := fun idx =>
    (seg_nonempty xs hxs_sorted idx).choose_spec
  let w (idx : Fin (xs.length + 1)) (j : S) : Bool :=
    decide ((W j.1).MemOpen (gammaParam (W i₀) (sRep idx)))
  have hw_eval : ∀ (idx : Fin (xs.length + 1)) {s : ℝ} (hs : s ∈ seg xs idx) (j : S),
      ((W j.1).MemOpen (gammaParam (W i₀) s) ↔ w idx j = true) := by
    intro idx s hs j
    rw [hseg_const idx j hs (hsRep_mem idx)]
    simp [w]
  have h_coord_ex : ∀ k : Fin xs.length, ∃ j : S,
      gammaParam (W i₀) (xs.get k) ∈ Gamma (W i₀) ∩ Gamma (W j.1) := by
    intro k
    have hk_mem : xs.get k ∈ xs := List.get_mem xs k
    have hP := (hxs_iff (xs.get k)).mp hk_mem
    rw [Set.mem_iUnion₂] at hP
    rcases hP with ⟨j, hjS, hmem⟩
    exact ⟨⟨j, hjS⟩, hmem⟩
  let coord (k : Fin xs.length) : S := (h_coord_ex k).choose
  have h_coord_spec : ∀ k : Fin xs.length,
      gammaParam (W i₀) (xs.get k) ∈ Gamma (W i₀) ∩ Gamma (W (coord k).1) := fun k =>
    (h_coord_ex k).choose_spec
  have h_step : ∀ (k : Fin xs.length) (j : S), j ≠ coord k →
      w k.castSucc j = w k.succ j := by
    intro k j hjne
    let p_k := gammaParam (W i₀) (xs.get k)
    have hmem_k := h_coord_spec k
    have hp_nbd : p_k ∉ bdWedge (W j.1) := by
      intro hbd
      obtain ⟨bi, hbi⟩ : ∃ b : Bool, lineAt W (i₀, b) p_k = 0 := by
        rcases (bdWedge_iff_closure_eq_zero (W i₀) p_k).mp hmem_k.1.1 |>.2 with h1 | h2
        · exact ⟨true, by simpa [lineAt, normal] using h1⟩
        · exact ⟨false, by simpa [lineAt, normal] using h2⟩
      obtain ⟨bc, hbc⟩ : ∃ b : Bool, lineAt W ((coord k).1, b) p_k = 0 := by
        rcases (bdWedge_iff_closure_eq_zero (W (coord k).1) p_k).mp hmem_k.2.1 |>.2 with h1 | h2
        · exact ⟨true, by simpa [lineAt, normal] using h1⟩
        · exact ⟨false, by simpa [lineAt, normal] using h2⟩
      obtain ⟨bj, hbj⟩ : ∃ b : Bool, lineAt W (j.1, b) p_k = 0 := by
        rcases (bdWedge_iff_closure_eq_zero (W j.1) p_k).mp hbd |>.2 with h1 | h2
        · exact ⟨true, by simpa [lineAt, normal] using h1⟩
        · exact ⟨false, by simpa [lineAt, normal] using h2⟩
      have hne1 : (i₀, bi) ≠ ((coord k).1, bc) := fun h =>
        Finset.ne_of_mem_erase (coord k).2 (congrArg Prod.fst h).symm
      have hne2 : (i₀, bi) ≠ (j.1, bj) := fun h =>
        Finset.ne_of_mem_erase j.2 (congrArg Prod.fst h).symm
      have hne3 : ((coord k).1, bc) ≠ (j.1, bj) := fun h =>
        hjne (Subtype.ext (congrArg Prod.fst h).symm)
      exact hGP.no_three_concurrent _ _ _ hne1 hne2 hne3 p_k ⟨hbi, hbc, hbj⟩
    dsimp [bdWedge] at hp_nbd; push Not at hp_nbd
    have hp_oe : (W j.1).MemOpen p_k ∨ (W j.1).MemExt p_k := by
      by_cases ho : (W j.1).MemOpen p_k
      · exact Or.inl ho
      · exact Or.inr (hp_nbd ho)
    rcases hp_oe with ho | he
    · have hopen_pre : IsOpen ((gammaParam (W i₀)) ⁻¹' {p | (W j.1).MemOpen p}) :=
        (isOpen_memOpen (W j.1)).preimage (gammaParam_continuous (W i₀))
      obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hopen_pre (xs.get k) ho
      obtain ⟨sL, hsL, hL1, hL2⟩ := exists_left_mem_seg xs hxs_sorted k δ hδ
      obtain ⟨sR, hsR, hR1, hR2⟩ := exists_right_mem_seg xs hxs_sorted k δ hδ
      have hL_open : (W j.1).MemOpen (gammaParam (W i₀) sL) :=
        hball (Metric.mem_ball.mpr (abs_lt.mpr ⟨by linarith, by linarith⟩))
      have hR_open : (W j.1).MemOpen (gammaParam (W i₀) sR) :=
        hball (Metric.mem_ball.mpr (abs_lt.mpr ⟨by linarith, by linarith⟩))
      rw [hw_eval k.castSucc hsL j] at hL_open
      rw [hw_eval k.succ hsR j] at hR_open
      rw [hL_open, hR_open]
    · have hopen_pre : IsOpen ((gammaParam (W i₀)) ⁻¹' {p | (W j.1).MemExt p}) :=
        (isOpen_memExt (W j.1)).preimage (gammaParam_continuous (W i₀))
      obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hopen_pre (xs.get k) he
      obtain ⟨sL, hsL, hL1, hL2⟩ := exists_left_mem_seg xs hxs_sorted k δ hδ
      obtain ⟨sR, hsR, hR1, hR2⟩ := exists_right_mem_seg xs hxs_sorted k δ hδ
      have hL_ext : (W j.1).MemExt (gammaParam (W i₀) sL) :=
        hball (Metric.mem_ball.mpr (abs_lt.mpr ⟨by linarith, by linarith⟩))
      have hR_ext : (W j.1).MemExt (gammaParam (W i₀) sR) :=
        hball (Metric.mem_ball.mpr (abs_lt.mpr ⟨by linarith, by linarith⟩))
      have hL_no : ¬ (W j.1).MemOpen (gammaParam (W i₀) sL) := fun ho =>
        memOpen_memExt_disjoint (W j.1) _ ⟨ho, hL_ext⟩
      have hR_no : ¬ (W j.1).MemOpen (gammaParam (W i₀) sR) := fun ho =>
        memOpen_memExt_disjoint (W j.1) _ ⟨ho, hR_ext⟩
      rw [hw_eval k.castSucc hsL j] at hL_no
      rw [hw_eval k.succ hsR j] at hR_no
      cases h1 : w k.castSucc j <;> cases h2 : w k.succ j <;> simp_all
  have h_le2 : ∀ j : S, (Finset.univ.filter (fun k : Fin xs.length => coord k = j)).card ≤ 2 := by
    intro j
    let T : Finset (Fin xs.length) := Finset.univ.filter (fun k => coord k = j)
    let f : Fin xs.length → ℝ × ℝ := fun k => gammaParam (W i₀) (xs.get k)
    have hf_inj : Function.Injective f := fun k₁ k₂ heq => by
      have h1 := gammaParam_injective (W i₀) (h_apex i₀).1 (h_apex i₀).2 heq
      have h2 := hxs_sorted.strictMono_get.injective h1
      exact h2
    have hsub : f '' (T : Set (Fin xs.length)) ⊆ Gamma (W i₀) ∩ Gamma (W j.1) := by
      rintro _ ⟨k, hk, rfl⟩
      have hck : coord k = j := (Finset.mem_filter.mp hk).2
      rw [← hck]
      exact h_coord_spec k
    have hj_lt : isLlt (W j.1) pa pb := hS_lt j.1 j.2
    have h2 : (Gamma (W i₀) ∩ Gamma (W j.1)).ncard ≤ 2 := by
      rw [Set.inter_comm]
      exact inter_card_le_two_of_Llt_Lgt W pa pb h_apex hxa hya hxb hyb hC ha hb hj_lt hi₀_gt
    calc T.card = (T : Set (Fin xs.length)).ncard := (Set.ncard_coe_finset T).symm
      _ = (f '' (T : Set (Fin xs.length))).ncard := (Set.ncard_image_of_injective _ hf_inj).symm
      _ ≤ (Gamma (W i₀) ∩ Gamma (W j.1)).ncard :=
          Set.ncard_le_ncard hsub (gamma_inter_finite hGP (Finset.ne_of_mem_erase j.2).symm)
      _ ≤ 2 := h2
  have hS_fintype_card : Fintype.card S = 4 := by
    rw [Fintype.card_coe]; exact hS_card
  let M_Gamma : Finset (S → Bool) := Finset.univ.image w
  have hM_card : M_Gamma.card ≤ 8 :=
    eight_mask_bound_of_coord hS_fintype_card xs.length w coord h_step h_le2
  let M_miss : Finset (S → Bool) := Finset.univ \ M_Gamma
  have hS_bool_card : Fintype.card (S → Bool) = 16 := by
    rw [Fintype.card_fun, Fintype.card_bool, hS_fintype_card]; norm_num
  have hM_miss_card : M_Gamma.card + M_miss.card = 16 := by
    have h := Finset.card_sdiff_add_card_inter (Finset.univ : Finset (S → Bool)) M_Gamma
    rw [Finset.univ_inter] at h
    rw [Finset.card_univ, hS_bool_card] at h
    dsimp [M_miss]; omega
  -- Witness injection from `M_Gamma ⊕ M_miss ⊕ M_miss` into `Comps U`
  let extendMask (m' : S → Bool) (b₀ : Bool) : Fin 5 → Bool := fun i =>
    if h : i ∈ S then m' ⟨i, h⟩ else b₀
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
  let pt : M_Gamma ⊕ M_miss ⊕ M_miss → ℝ × ℝ := fun x =>
    match x with
    | Sum.inl ⟨m', hm'⟩ =>
      let idx := (Finset.mem_image.mp hm').choose
      gammaParam (W i₀) (sRep idx)
    | Sum.inr (Sum.inl ⟨m', _⟩) => (h_real_U (extendMask m' true)).choose
    | Sum.inr (Sum.inr ⟨m', _⟩) => (h_real_U (extendMask m' false)).choose
  have hpt_U : ∀ x, pt x ∈ U := by
    rintro (⟨m', hm'⟩ | ⟨m', _⟩ | ⟨m', _⟩)
    · exact hseg_sub _ ⟨_, hsRep_mem _, rfl⟩
    · exact (h_real_U (extendMask m' true)).choose_spec.1
    · exact (h_real_U (extendMask m' false)).choose_spec.1
  let maskOf (x : M_Gamma ⊕ M_miss ⊕ M_miss) : S → Bool :=
    match x with
    | Sum.inl ⟨m', _⟩ => m'
    | Sum.inr (Sum.inl ⟨m', _⟩) => m'
    | Sum.inr (Sum.inr ⟨m', _⟩) => m'
  have hpt_mask : ∀ x (j : S), ((W j.1).MemOpen (pt x) ↔ maskOf x j = true) := by
    rintro (⟨m', hm'⟩ | ⟨m', _⟩ | ⟨m', _⟩) j
    · dsimp [pt, maskOf]
      have hspec := (Finset.mem_image.mp hm').choose_spec
      have hw := hw_eval (Finset.mem_image.mp hm').choose (hsRep_mem _) j
      rw [hw, hspec.2]
    · dsimp [pt, maskOf]
      have hreal := (h_real_U (extendMask m' true)).choose_spec.2
      constructor
      · intro ho
        by_contra hnf
        have hfalse : extendMask m' true j.1 = false := by
          simp [extendMask, j.2, Bool.eq_false_iff.mpr hnf]
        have hext : (W j.1).MemExt (h_real_U (extendMask m' true)).choose := by
          simpa [hfalse] using hreal j.1
        exact memOpen_memExt_disjoint (W j.1) _ ⟨ho, hext⟩
      · intro ht
        have htrue : extendMask m' true j.1 = true := by simp [extendMask, j.2, ht]
        simpa [htrue] using hreal j.1
    · dsimp [pt, maskOf]
      have hreal := (h_real_U (extendMask m' false)).choose_spec.2
      constructor
      · intro ho
        by_contra hnf
        have hfalse : extendMask m' false j.1 = false := by
          simp [extendMask, j.2, Bool.eq_false_iff.mpr hnf]
        have hext : (W j.1).MemExt (h_real_U (extendMask m' false)).choose := by
          simpa [hfalse] using hreal j.1
        exact memOpen_memExt_disjoint (W j.1) _ ⟨ho, hext⟩
      · intro ht
        have htrue : extendMask m' false j.1 = true := by simp [extendMask, j.2, ht]
        simpa [htrue] using hreal j.1
  have hpt_ext : ∀ x (j : S), maskOf x j = false → (W j.1).MemExt (pt x) := by
    intro x j hmf
    have hpU := hpt_U x
    have hnbd : pt x ∉ bdWedge (W j.1) := fun hbd =>
      hpU.2 (Set.mem_iUnion₂.mpr ⟨j.1, j.2, hbd, hpU.1⟩)
    dsimp [bdWedge] at hnbd; push Not at hnbd
    apply hnbd
    intro ho
    rw [hpt_mask x j] at ho
    rw [hmf] at ho; exact Bool.false_ne_true ho
  have hpt_inj : ∀ x₁ x₂, x₁ ≠ x₂ →
      connectedComponentIn U (pt x₁) ≠ connectedComponentIn U (pt x₂) := by
    intro x₁ x₂ hne
    by_cases hm_eq : maskOf x₁ = maskOf x₂
    · have hm_not : maskOf x₁ ∉ M_Gamma := by
        rcases x₁ with ⟨m₁, hm₁⟩ | ⟨m₁, hm₁⟩ | ⟨m₁, hm₁⟩ <;>
        rcases x₂ with ⟨m₂, hm₂⟩ | ⟨m₂, hm₂⟩ | ⟨m₂, hm₂⟩ <;>
        dsimp [maskOf] at hm_eq
        · exact False.elim (hne (congrArg Sum.inl (Subtype.ext hm_eq)))
        · exfalso; rw [← hm_eq] at hm₂; exact (Finset.mem_sdiff.mp hm₂).2 hm₁
        · exfalso; rw [← hm_eq] at hm₂; exact (Finset.mem_sdiff.mp hm₂).2 hm₁
        · exfalso; rw [hm_eq] at hm₁; exact (Finset.mem_sdiff.mp hm₁).2 hm₂
        · exact False.elim (hne (congrArg (Sum.inr ∘ Sum.inl) (Subtype.ext hm_eq)))
        · exact (Finset.mem_sdiff.mp hm₁).2
        · exfalso; rw [hm_eq] at hm₁; exact (Finset.mem_sdiff.mp hm₁).2 hm₂
        · exact (Finset.mem_sdiff.mp hm₁).2
        · exact False.elim (hne (congrArg (Sum.inr ∘ Sum.inr) (Subtype.ext hm_eq)))
      have h_i0_sep : ((W i₀).MemOpen (pt x₁) ∧ (W i₀).MemExt (pt x₂)) ∨
          ((W i₀).MemExt (pt x₁) ∧ (W i₀).MemOpen (pt x₂)) := by
        rcases x₁ with ⟨m₁, hm₁⟩ | ⟨m₁, hm₁⟩ | ⟨m₁, hm₁⟩ <;>
        rcases x₂ with ⟨m₂, hm₂⟩ | ⟨m₂, hm₂⟩ | ⟨m₂, hm₂⟩ <;>
        dsimp [maskOf] at hm_eq hm_not
        · exact False.elim (hm_not hm₁)
        · exact False.elim (hm_not hm₁)
        · exact False.elim (hm_not hm₁)
        · exact False.elim (hm_not (hm_eq ▸ hm₂))
        · exact False.elim (hne (congrArg (Sum.inr ∘ Sum.inl) (Subtype.ext hm_eq)))
        · left
          have h1 : (W i₀).MemOpen (pt (Sum.inr (Sum.inl ⟨m₁, hm₁⟩))) := by
            have hr := (h_real_U (extendMask m₁ true)).choose_spec.2 i₀
            have hext : extendMask m₁ true i₀ = true := by simp [extendMask, hi₀_nS]
            simpa [pt, hext] using hr
          have h2 : (W i₀).MemExt (pt (Sum.inr (Sum.inr ⟨m₂, hm₂⟩))) := by
            have hr := (h_real_U (extendMask m₂ false)).choose_spec.2 i₀
            have hext : extendMask m₂ false i₀ = false := by simp [extendMask, hi₀_nS]
            simpa [pt, hext] using hr
          exact ⟨h1, h2⟩
        · exact False.elim (hm_not (hm_eq ▸ hm₂))
        · right
          have h1 : (W i₀).MemExt (pt (Sum.inr (Sum.inr ⟨m₁, hm₁⟩))) := by
            have hr := (h_real_U (extendMask m₁ false)).choose_spec.2 i₀
            have hext : extendMask m₁ false i₀ = false := by simp [extendMask, hi₀_nS]
            simpa [pt, hext] using hr
          have h2 : (W i₀).MemOpen (pt (Sum.inr (Sum.inl ⟨m₂, hm₂⟩))) := by
            have hr := (h_real_U (extendMask m₂ true)).choose_spec.2 i₀
            have hext : extendMask m₂ true i₀ = true := by simp [extendMask, hi₀_nS]
            simpa [pt, hext] using hr
          exact ⟨h1, h2⟩
        · exact False.elim (hne (congrArg (Sum.inr ∘ Sum.inr) (Subtype.ext hm_eq)))
      intro hcomp_eq
      have hmeet_bd : (connectedComponentIn U (pt x₁) ∩ bdWedge (W i₀)).Nonempty := by
        by_contra hno
        rw [Set.not_nonempty_iff_eq_empty] at hno
        have hsub : connectedComponentIn U (pt x₁) ⊆
            {p | (W i₀).MemOpen p} ∪ {p | (W i₀).MemExt p} := by
          intro p hp
          have hp_nbd : p ∉ bdWedge (W i₀) := fun hbd =>
            (Set.eq_empty_iff_forall_notMem.mp hno p) ⟨hp, hbd⟩
          dsimp [bdWedge] at hp_nbd; push Not at hp_nbd
          by_cases ho : (W i₀).MemOpen p
          · exact Or.inl ho
          · exact Or.inr (hp_nbd ho)
        have hdisj : Disjoint {p | (W i₀).MemOpen p} {p | (W i₀).MemExt p} := by
          rw [Set.disjoint_left]; exact fun p ho he => memOpen_memExt_disjoint (W i₀) p ⟨ho, he⟩
        have hp1 := mem_connectedComponentIn (hpt_U x₁)
        have hp2 : pt x₂ ∈ connectedComponentIn U (pt x₁) := by
          rw [hcomp_eq]; exact mem_connectedComponentIn (hpt_U x₂)
        rcases isPreconnected_connectedComponentIn.subset_or_subset
            (isOpen_memOpen (W i₀)) (isOpen_memExt (W i₀)) hdisj hsub with hO | hE
        · rcases h_i0_sep with ⟨_, he2⟩ | ⟨he1, _⟩
          · exact memOpen_memExt_disjoint (W i₀) _ ⟨hO hp2, he2⟩
          · exact memOpen_memExt_disjoint (W i₀) _ ⟨hO hp1, he1⟩
        · rcases h_i0_sep with ⟨ho1, _⟩ | ⟨_, ho2⟩
          · exact memOpen_memExt_disjoint (W i₀) _ ⟨ho1, hE hp1⟩
          · exact memOpen_memExt_disjoint (W i₀) _ ⟨ho2, hE hp2⟩
      obtain ⟨q, hq_comp, hq_bd⟩ := hmeet_bd
      have hqU : q ∈ U := connectedComponentIn_subset U (pt x₁) hq_comp
      have hqG : q ∈ Gamma (W i₀) := ⟨hq_bd, hqU.1⟩
      rw [← gammaParam_range (W i₀) (h_apex i₀).1 (h_apex i₀).2] at hqG
      obtain ⟨s, rfl⟩ := hqG
      have hs_nxs : s ∉ xs := by
        intro hmem
        have hP := (hxs_iff s).mp hmem
        rw [Set.mem_iUnion₂] at hP
        rcases hP with ⟨j, hjS, _, hjG⟩
        exact hqU.2 (Set.mem_iUnion₂.mpr ⟨j, hjS, hjG⟩)
      have hmem_seg := compl_list_subset_iUnion_seg xs hs_nxs
      rw [Set.mem_iUnion] at hmem_seg
      obtain ⟨idx, hs_idx⟩ := hmem_seg
      have hq_mask : w idx = maskOf x₁ := by
        funext j
        have h_same : ((W j.1).MemOpen (gammaParam (W i₀) s) ↔ (W j.1).MemOpen (pt x₁)) := by
          by_contra hdiff
          have hsep : ((W j.1).MemOpen (gammaParam (W i₀) s) ∧ (W j.1).MemExt (pt x₁)) ∨
              ((W j.1).MemExt (gammaParam (W i₀) s) ∧ (W j.1).MemOpen (pt x₁)) := by
            have hq_nbd : gammaParam (W i₀) s ∉ bdWedge (W j.1) := fun hbd =>
              hqU.2 (Set.mem_iUnion₂.mpr ⟨j.1, j.2, hbd, hqU.1⟩)
            have h1_nbd : pt x₁ ∉ bdWedge (W j.1) := fun hbd =>
              (hpt_U x₁).2 (Set.mem_iUnion₂.mpr ⟨j.1, j.2, hbd, (hpt_U x₁).1⟩)
            dsimp [bdWedge] at hq_nbd h1_nbd; push Not at hq_nbd h1_nbd
            by_cases hq_o : (W j.1).MemOpen (gammaParam (W i₀) s)
            · have h1_no : ¬ (W j.1).MemOpen (pt x₁) := fun h => hdiff (iff_of_true hq_o h)
              exact Or.inl ⟨hq_o, h1_nbd h1_no⟩
            · have h1_o : (W j.1).MemOpen (pt x₁) := by
                by_contra h; exact hdiff (iff_of_false hq_o h)
              exact Or.inr ⟨hq_nbd hq_o, h1_o⟩
          have hne_comp := comp_ne_of_sep_wedge j.2 hqU (hpt_U x₁) hsep
          exact hne_comp (connectedComponentIn_eq hq_comp).symm
        have h1 := hw_eval idx hs_idx j
        have h2 := hpt_mask x₁ j
        have hiff : w idx j = true ↔ maskOf x₁ j = true := h1.symm.trans (h_same.trans h2)
        exact Bool.eq_iff_iff.mpr hiff
      exact hm_not (Finset.mem_image.mpr ⟨idx, Finset.mem_univ idx, hq_mask⟩)
    · have hj_ex : ∃ j : S, maskOf x₁ j ≠ maskOf x₂ j := by
        by_contra hnone; push Not at hnone; exact hm_eq (funext hnone)
      obtain ⟨j, hj⟩ := hj_ex
      have hsep : ((W j.1).MemOpen (pt x₁) ∧ (W j.1).MemExt (pt x₂)) ∨
          ((W j.1).MemExt (pt x₁) ∧ (W j.1).MemOpen (pt x₂)) := by
        cases h1 : maskOf x₁ j <;> cases h2 : maskOf x₂ j
        · exact False.elim (hj (h1.trans h2.symm))
        · exact Or.inr ⟨hpt_ext x₁ j h1, (hpt_mask x₂ j).mpr h2⟩
        · exact Or.inl ⟨(hpt_mask x₁ j).mpr h1, hpt_ext x₂ j h2⟩
        · exact False.elim (hj (h1.trans h2.symm))
      exact comp_ne_of_sep_wedge j.2 (hpt_U x₁) (hpt_U x₂) hsep
  have h_comps_lower : (24 : ℕ∞) ≤ (Comps U).encard := by
    have hcard_sum : 24 ≤ Fintype.card (M_Gamma ⊕ M_miss ⊕ M_miss) := by
      simp only [Fintype.card_sum, Fintype.card_coe]
      omega
    exact (Nat.cast_le.mpr hcard_sum).trans (card_le_comps_of_inj pt hpt_U hpt_inj)
  have h_contra : (24 : ℕ∞) ≤ 23 := h_comps_lower.trans h_comps_upper
  exact absurd h_contra (by decide)

end CaseB
end
