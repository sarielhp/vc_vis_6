import Mathlib
import RootTask.PolygonDefs
import RootTask.PolygonEnclosureCore
import RootTask.Sec5HalfPlane
import RootTask.NewEnclosureLemmas
import RootTask.ChirotopeSoundness

open scoped Classical BigOperators
open Finset

/-!
# Certified Pocket Soundness `(C6)`, Half-Plane Chirotope Clauses `(C9)`, and Verified RUP Checker

Extends `RootTask.ChirotopeSoundness` (`upper_8.tex` Section 8, Theorem 8.1) with:
1. **`SoundRUPChecker`**: A total, computable Propositional Resolution / Reverse Unit Propagation
   (RUP) certificate verifier in pure Lean 4 (`Clause := List Int`, `CNF := List Clause`,
   `evalLit (v : Nat → Bool) (l : Int) : Bool`) with soundness theorem `checkCert_sound`
   (`checkCert cnf cert = true → ∀ v, evalCNF v cnf = false`), proved constructively without
   `native_decide`.
2. **Clause `(C6)` (Certified Pocket Chirotope Soundness)**:
   - Pocket triangle containment `inOpenTriBool (S h) (w Tw) (S l) (S r) = true` when `{l, r} ⊆ Tw`
     plus wedge separation on `W({l, r})`;
   - Hull-neighbor triangle containment `inOpenTriBool (S h) (w Tw) (S hm) (S hp) = true` when
     `{hm, hp} ⊆ Tw` plus wedge separation on `W({hm, hp})`;
   - `z_h` separation across `z_h h` in `orientSign` / `sameSideBool` / `oppSideBool` form;
   - `side-corners` propagation in `orientSign` / `oppSideBool` / `inOpenTriBool` form for both
     hull pairs `u, v ∈ B \ {h}` and general pairs `u, v ∈ S \ {h}`.
3. **Clause `(C9)` (Half-Plane Lemma Pure Chirotope Orientation Clauses)**:
   - Pure `orientSign` formulation of the normalized Half-Plane configuration on `(v, q, p, a, c)`
     with `σ := orientSign v q p`;
   - Proofs of `orientSign v a x = !σ` (`Claim 4.4(a)`), `orientSign v p x = !σ` (`Claim 4.4(b)`),
     `orientSign p x a = σ` (`Claim 4.4(c)` when `x` sees `p`), and pure chirotope slope separation
     `orientSign p x y = σ` (`Claim 4.5`) for every `x` seeing `{a, c, p}` and every `y` seeing
     `{a, c}` and missing `p`.
-/

/-! ## 1. Verified Propositional Resolution / RUP Certificate Checker (`SoundRUPChecker`) -/

namespace SoundRUPChecker

/-- A propositional clause in DIMACS convention: a list of signed integer literals
    (`l > 0` represents `v l.natAbs`, `l < 0` represents `!(v l.natAbs)`). -/
abbrev Clause := List Int

/-- A CNF formula is a conjunction (list) of clauses. -/
abbrev CNF := List Clause

/-- Evaluates a signed integer literal `l` under Boolean valuation `v : Nat → Bool`.
    Literal `0` evaluates to `false` (neutral element for disjunction). -/
def evalLit (v : Nat → Bool) (l : Int) : Bool :=
  if 0 < l then v l.natAbs
  else if l < 0 then !(v l.natAbs)
  else false

/-- Evaluates a clause as the disjunction of its literals. -/
def evalClause (v : Nat → Bool) (c : Clause) : Bool :=
  c.any (evalLit v)

/-- Evaluates a CNF formula as the conjunction of its clauses. -/
def evalCNF (v : Nat → Bool) (cnf : CNF) : Bool :=
  cnf.all (evalClause v)

/-- Scans a clause `cl` against a list `fLits` of known-falsified literals:
    - `some none`: conflict (every literal of `cl` belongs to `fLits`);
    - `some (some u)`: unit clause with unique non-falsified literal `u`;
    - `none`: two or more distinct literals of `cl` lie outside `fLits`. -/
def scanClause (fLits : List Int) : Option Int → Clause → Option (Option Int)
  | cand, [] => some cand
  | cand, l :: ls =>
    if fLits.contains l then
      scanClause fLits cand ls
    else
      match cand with
      | none => scanClause fLits (some l) ls
      | some u => if l == u then scanClause fLits (some u) ls else none

/-- Reverse Unit Propagation (RUP) along a sequence of 0-based clause hint indices:
    assumes all literals in `fLits` are falsified and propagates unit literals until conflict. -/
def rupPropagate (cnf : CNF) (fLits : List Int) : List Nat → Bool
  | [] => false
  | idx :: rest =>
    match cnf[idx]? with
    | none => false
    | some cl =>
      match scanClause fLits none cl with
      | some none => true
      | some (some u) => (u != 0) && rupPropagate cnf ((-u) :: fLits) rest
      | none => false

/-- Binary propositional resolution of `c₁` and `c₂` on pivot literal `piv`. -/
def resolveClauses (c₁ c₂ : Clause) (piv : Int) : Clause :=
  (c₁.filter (· != piv)) ++ (c₂.filter (· != -piv))

/-- Proof steps supported by the verified RUP / Resolution certificate checker. -/
inductive CertStep : Type
  | rup (cl : Clause) (hints : List Nat)
  | res (i j : Nat) (piv : Int)
  | del (idx : Nat)
  deriving DecidableEq, Repr

/-- A refutation certificate is a finite sequence of RUP, resolution, and deletion steps. -/
abbrev Cert := List CertStep

/-- Total functional RUP / Resolution refutation verifier. -/
def checkCert (cnf : CNF) : Cert → Bool
  | [] => cnf.any List.isEmpty
  | CertStep.rup cl hints :: rest =>
    rupPropagate cnf cl hints && (cl.isEmpty || checkCert (cnf ++ [cl]) rest)
  | CertStep.res i j piv :: rest =>
    match cnf[i]?, cnf[j]? with
    | some c₁, some c₂ =>
      (piv != 0) &&
        let r := resolveClauses c₁ c₂ piv
        r.isEmpty || checkCert (cnf ++ [r]) rest
    | _, _ => false
  | CertStep.del idx :: rest =>
    checkCert (cnf.eraseIdx idx) rest

lemma evalLit_neg {l : Int} (hl : l ≠ 0) (v : Nat → Bool) :
    evalLit v (-l) = !(evalLit v l) := by
  unfold evalLit
  rcases (by omega : 0 < l ∨ l < 0) with hpos | hneg
  · rw [if_neg (by omega : ¬ (0 < -l)), if_pos (by omega : -l < 0),
        if_pos hpos, Int.natAbs_neg]
  · rw [if_pos (by omega : 0 < -l), if_neg (by omega : ¬ (0 < l)),
        if_pos hneg, Int.natAbs_neg, Bool.not_not]

lemma scanClause_spec (fLits : List Int) :
    ∀ (cand res : Option Int) (cl : Clause),
      scanClause fLits cand cl = some res →
      match res with
      | none => cand = none ∧ ∀ l ∈ cl, fLits.contains l = true
      | some u => (cand = none ∨ cand = some u) ∧ ∀ l ∈ cl, fLits.contains l = true ∨ l = u
  | cand, res, [], h => by
    injection h with hEq
    subst hEq
    cases cand with
    | none => exact ⟨rfl, fun _ hm => by simp at hm⟩
    | some u => exact ⟨Or.inr rfl, fun _ hm => by simp at hm⟩
  | cand, res, l :: ls, h => by
    cases hmem : fLits.contains l
    · cases cand with
      | none =>
        simp only [scanClause, hmem, Bool.false_eq_true, ↓reduceIte] at h
        have ih := scanClause_spec fLits (some l) res ls h
        cases res with
        | none => nomatch ih.1
        | some u =>
          have hlu : l = u := by
            rcases ih.1 with hno | heq
            · nomatch hno
            · exact Option.some.inj heq
          refine ⟨Or.inl rfl, fun x hx => ?_⟩
          rcases List.mem_cons.mp hx with rfl | hxs
          · exact Or.inr hlu
          · exact ih.2 x hxs
      | some u₀ =>
        cases heq_b : (l == u₀)
        · simp only [scanClause, hmem, heq_b, Bool.false_eq_true, ↓reduceIte] at h
          nomatch h
        · simp only [scanClause, hmem, heq_b, Bool.false_eq_true, ↓reduceIte] at h
          have hlu₀ : l = u₀ := beq_iff_eq.mp heq_b
          have ih := scanClause_spec fLits (some u₀) res ls h
          cases res with
          | none => nomatch ih.1
          | some u =>
            have hu₀u : u₀ = u := by
              rcases ih.1 with hno | heq
              · nomatch hno
              · exact Option.some.inj heq
            refine ⟨Or.inr (congrArg some hu₀u), fun x hx => ?_⟩
            rcases List.mem_cons.mp hx with rfl | hxs
            · exact Or.inr (hlu₀.trans hu₀u)
            · exact ih.2 x hxs
    · simp only [scanClause, hmem, ↓reduceIte] at h
      have ih := scanClause_spec fLits cand res ls h
      cases res with
      | none =>
        refine ⟨ih.1, fun x hx => ?_⟩
        rcases List.mem_cons.mp hx with rfl | hxs
        · exact hmem
        · exact ih.2 x hxs
      | some u =>
        refine ⟨ih.1, fun x hx => ?_⟩
        rcases List.mem_cons.mp hx with rfl | hxs
        · exact Or.inl hmem
        · exact ih.2 x hxs

lemma rupPropagate_false_of_all_false {cnf : CNF} {v : Nat → Bool}
    (hcnf : evalCNF v cnf = true) :
    ∀ (hints : List Nat) (fLits : List Int),
      rupPropagate cnf fLits hints = true →
      (∀ x ∈ fLits, evalLit v x = false) → False
  | [], _, hrup, _ => Bool.noConfusion hrup
  | idx :: rest, fLits, hrup, hf => by
    cases hget : cnf[idx]? with
    | none => simp only [rupPropagate, hget] at hrup; exact Bool.noConfusion hrup
    | some cl =>
      simp only [rupPropagate, hget] at hrup
      have hcl_mem : cl ∈ cnf := List.mem_of_getElem? hget
      have hcl_true : evalClause v cl = true := (List.all_eq_true.mp hcnf) cl hcl_mem
      cases hscan : scanClause fLits none cl with
      | none => simp only [hscan] at hrup; exact Bool.noConfusion hrup
      | some res =>
        simp only [hscan] at hrup
        have hspec := scanClause_spec fLits none res cl hscan
        cases res with
        | none =>
          obtain ⟨l, hl_mem, hl_true⟩ := List.any_eq_true.mp hcl_true
          have hl_in : l ∈ fLits := by simpa using hspec.2 l hl_mem
          rw [hf l hl_in] at hl_true
          exact Bool.noConfusion hl_true
        | some u =>
          simp only [Bool.and_eq_true, bne_iff_ne] at hrup
          obtain ⟨hu_ne, hrup_rest⟩ := hrup
          obtain ⟨l, hl_mem, hl_true⟩ := List.any_eq_true.mp hcl_true
          have hu_true : evalLit v u = true := by
            rcases hspec.2 l hl_mem with hl_f | rfl
            · have hfl : l ∈ fLits := by simpa using hl_f
              rw [hf l hfl] at hl_true
              exact False.elim (Bool.noConfusion hl_true)
            · exact hl_true
          have hnu_false : evalLit v (-u) = false := by
            rw [evalLit_neg hu_ne v, hu_true]; rfl
          exact rupPropagate_false_of_all_false hcnf rest ((-u) :: fLits) hrup_rest
            (fun x hx => by
              rcases List.mem_cons.mp hx with rfl | hxs
              · exact hnu_false
              · exact hf x hxs)

lemma rupPropagate_sound {cnf : CNF} {cl : Clause} {hints : List Nat} {v : Nat → Bool}
    (hrup : rupPropagate cnf cl hints = true) (hcnf : evalCNF v cnf = true) :
    evalClause v cl = true := by
  cases hcl : evalClause v cl
  · exfalso
    have hall_false : ∀ x ∈ cl, evalLit v x = false := by
      intro x hx
      cases hlit : evalLit v x
      · rfl
      · have hany : evalClause v cl = true := List.any_eq_true.mpr ⟨x, hx, hlit⟩
        rw [hcl] at hany
        exact False.elim (Bool.noConfusion hany)
    exact rupPropagate_false_of_all_false hcnf hints cl hrup hall_false
  · rfl

lemma resolveClauses_sound {c₁ c₂ : Clause} {piv : Int} {v : Nat → Bool}
    (hpiv : piv ≠ 0) (hc₁ : evalClause v c₁ = true) (hc₂ : evalClause v c₂ = true) :
    evalClause v (resolveClauses c₁ c₂ piv) = true := by
  unfold evalClause resolveClauses
  rw [List.any_eq_true]
  cases hp : evalLit v piv
  · obtain ⟨l, hl_mem, hl_true⟩ := List.any_eq_true.mp hc₁
    have hne : l ≠ piv := by
      intro heq; subst heq; rw [hp] at hl_true; exact Bool.noConfusion hl_true
    exact ⟨l, List.mem_append_left _ (List.mem_filter.mpr ⟨hl_mem, bne_iff_ne.mpr hne⟩), hl_true⟩
  · obtain ⟨l, hl_mem, hl_true⟩ := List.any_eq_true.mp hc₂
    have hnp : evalLit v (-piv) = false := by rw [evalLit_neg hpiv v, hp]; rfl
    have hne : l ≠ -piv := by
      intro heq; subst heq; rw [hnp] at hl_true; exact Bool.noConfusion hl_true
    exact ⟨l, List.mem_append_right _ (List.mem_filter.mpr ⟨hl_mem, bne_iff_ne.mpr hne⟩), hl_true⟩

/-- **Main Soundness Theorem for `SoundRUPChecker`**:
    If `checkCert cnf cert = true`, then `cnf` is unsatisfiable (`∀ v, evalCNF v cnf = false`). -/
theorem checkCert_sound (cnf : CNF) (cert : Cert) :
    checkCert cnf cert = true → ∀ v : Nat → Bool, evalCNF v cnf = false := by
  intro hcert v
  induction cert generalizing cnf with
  | nil =>
    unfold checkCert at hcert
    obtain ⟨cl, hcl_mem, hcl_emp⟩ := List.any_eq_true.mp hcert
    have hemp : cl = [] := List.isEmpty_iff.mp hcl_emp
    subst hemp
    cases hcnf : evalCNF v cnf
    · rfl
    · have hfalse : evalClause v [] = true := (List.all_eq_true.mp hcnf) [] hcl_mem
      exact False.elim (Bool.noConfusion hfalse)
  | cons step rest ih =>
    cases hcnf : evalCNF v cnf
    · rfl
    · exfalso
      cases step with
      | rup cl hints =>
        unfold checkCert at hcert
        simp only [Bool.and_eq_true, Bool.or_eq_true] at hcert
        obtain ⟨hrup, hemp_or_rest⟩ := hcert
        have hcl_true : evalClause v cl = true := rupPropagate_sound hrup hcnf
        rcases hemp_or_rest with hemp | hrest
        · rw [List.isEmpty_iff.mp hemp] at hcl_true
          exact Bool.noConfusion hcl_true
        · have happ : evalCNF v (cnf ++ [cl]) = true := by
            unfold evalCNF at hcnf ⊢
            rw [List.all_append, Bool.and_eq_true]
            exact ⟨hcnf, by simp [hcl_true]⟩
          have hfalse := ih (cnf ++ [cl]) hrest
          rw [happ] at hfalse
          exact Bool.noConfusion hfalse
      | res i j piv =>
        unfold checkCert at hcert
        cases hi : cnf[i]? with
        | none => rw [hi] at hcert; exact Bool.noConfusion hcert
        | some c₁ =>
          rw [hi] at hcert
          cases hj : cnf[j]? with
          | none => rw [hj] at hcert; exact Bool.noConfusion hcert
          | some c₂ =>
            rw [hj] at hcert
            simp only [Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne] at hcert
            obtain ⟨hpiv, hemp_or_rest⟩ := hcert
            have hc₁ : evalClause v c₁ = true :=
              (List.all_eq_true.mp hcnf) c₁ (List.mem_of_getElem? hi)
            have hc₂ : evalClause v c₂ = true :=
              (List.all_eq_true.mp hcnf) c₂ (List.mem_of_getElem? hj)
            have hr_true : evalClause v (resolveClauses c₁ c₂ piv) = true :=
              resolveClauses_sound hpiv hc₁ hc₂
            rcases hemp_or_rest with hemp | hrest
            · rw [List.isEmpty_iff.mp hemp] at hr_true
              exact Bool.noConfusion hr_true
            · have happ : evalCNF v (cnf ++ [resolveClauses c₁ c₂ piv]) = true := by
                unfold evalCNF at hcnf ⊢
                rw [List.all_append, Bool.and_eq_true]
                exact ⟨hcnf, by simp [hr_true]⟩
              have hfalse := ih (cnf ++ [resolveClauses c₁ c₂ piv]) hrest
              rw [happ] at hfalse
              exact Bool.noConfusion hfalse
      | del idx =>
        unfold checkCert at hcert
        have herase : evalCNF v (cnf.eraseIdx idx) = true := by
          unfold evalCNF at hcnf ⊢
          rw [List.all_eq_true] at hcnf ⊢
          intro cl hmem
          exact hcnf cl (List.mem_of_mem_eraseIdx hmem)
        have hfalse := ih (cnf.eraseIdx idx) hcert
        rw [herase] at hfalse
        exact Bool.noConfusion hfalse

/-- Pure kernel (`decide`, zero `native_decide`) test refutation on the 4-clause 2-variable formula. -/
theorem example_unsat_by_decide :
    ∀ v : Nat → Bool, evalCNF v [[1, 2], [1, -2], [-1, 2], [-1, -2]] = false :=
  checkCert_sound [[1, 2], [1, -2], [-1, 2], [-1, -2]]
    [CertStep.rup [1] [0, 1], CertStep.rup [] [4, 2, 3]]
    (by decide)

end SoundRUPChecker


/-! ## 2. Clause `(C6)` (Certified Pocket Chirotope Soundness) -/

noncomputable section

namespace CertifiedAndHalfPlaneSoundness

open PolygonCore Sec5HP NewEnclosure ChirotopeSoundness

/-- Helper converting `InOpenTri (w Tw) (S a) (S b) (S h)` to `inOpenTriBool (S h) (w Tw) (S a) (S b) = true`
    under general position when `a, b, h` are pairwise distinct. -/
lemma inOpenTriBool_S_w_S_S {n : ℕ} {P : Set (ℝ × ℝ)}
    {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ}
    (hP : ShatteredSimplePolygon P S w)
    {h a b : Fin n} (hha : h ≠ a) (hhb : h ≠ b) (hab : a ≠ b)
    (Tw : Finset (Fin n)) :
    inOpenTriBool (S h) (w Tw) (S a) (S b) = true ↔ InOpenTri (w Tw) (S a) (S b) (S h) :=
  inOpenTriBool_iff_inOpenTri
    (orient_w_S_S_ne hP Tw hha.symm)
    (orient_S_S_S_ne hP hab hhb.symm hha.symm)
    (orient_S_w_S_ne hP hhb.symm Tw)

/-- **Clause `(C6)` Part 1 (`certified_pocket_lr_C6`, Outer Pocket Containment & Wedge Separation)**:
    Whenever `(certifiedSet P S w).Nonempty`, `certified_structure` yields distinct adjacent non-certified
    hull vertices `l, r ∈ D = hullVertices S \ certifiedSet P S w` such that:
    1. Every `h ∈ certifiedSet P S w` satisfies `inOpenTriBool (S h) (w Tw) (S l) (S r) = true`
       whenever `{l, r} ⊆ Tw`;
    2. Wedge separation holds on `W({l, r})` for every `h ∈ certifiedSet P S w`;
    3. `|A| + |H| ≤ 5` and `H` is the contiguous block `[k_f .. k_g]` along `N_q`. -/
theorem certified_pocket_lr_C6 {n : ℕ} {P : Set (ℝ × ℝ)}
    {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ}
    (hP : ShatteredSimplePolygon P S w) (hn : 3 ≤ n)
    (cb : CyclicSubsetBoundary S (hullVertices S))
    (vc : VisibleContour (S ∘ cb.p_idx) (w Finset.univ))
    (hH : (certifiedSet P S w).Nonempty) :
    ∃ (k_f k_g : ℕ) (l r : Fin n),
      0 < k_f ∧ k_f ≤ k_g ∧ k_g < vc.d_near ∧
      l = cb.p_idx (finShift vc.i_max (k_f - 1)) ∧
      r = cb.p_idx (finShift vc.i_max (k_g + 1)) ∧
      l ∈ hullVertices S \ certifiedSet P S w ∧
      r ∈ hullVertices S \ certifiedSet P S w ∧
      l ≠ r ∧
      (∀ k : ℕ, k < cb.m + 3 →
        (k_f ≤ k ∧ k ≤ k_g ↔ cb.p_idx (finShift vc.i_max k) ∈ certifiedSet P S w)) ∧
      (∀ h ∈ certifiedSet P S w, ∀ Tw : Finset (Fin n), {l, r} ⊆ Tw →
        inOpenTriBool (S h) (w Tw) (S l) (S r) = true) ∧
      (∀ h ∈ certifiedSet P S w, ∀ {T₁ T₂ Tm : Finset (Fin n)}, T₁ ≠ T₂ →
        {l, r} ⊆ T₁ → h ∈ T₁ → {l, r} ⊆ T₂ → h ∈ T₂ → {l, r} ⊆ Tm → h ∉ Tm →
        ∀ s : Bool,
          ¬ (orientSign (S h) (w T₁) (w T₂) = s ∧
             orientSign (S h) (w T₁) (w Tm) = s ∧
             orientSign (S h) (w Tm) (w T₂) = s)) ∧
      (interiorPoints S).card + (certifiedSet P S w).card ≤ 5 := by
  obtain ⟨k_f, k_g, l, r, hkf0, hkfg, hkg_lt, hl_eq, hr_eq, hlD, hrD, hlr, hblock, hpart_ii, h5⟩ :=
    certified_structure hP hn cb vc hH
  have hl_notH : l ∉ certifiedSet P S w := (Finset.mem_sdiff.mp hlD).2
  have hr_notH : r ∉ certifiedSet P S w := (Finset.mem_sdiff.mp hrD).2
  have h_tri_bool : ∀ h ∈ certifiedSet P S w, ∀ Tw : Finset (Fin n), {l, r} ⊆ Tw →
      inOpenTriBool (S h) (w Tw) (S l) (S r) = true := by
    intro h hh Tw hsub
    have hhl : h ≠ l := fun e => hl_notH (e ▸ hh)
    have hhr : h ≠ r := fun e => hr_notH (e ▸ hh)
    have hl_in : l ∈ Tw := hsub (by simp)
    have hr_in : r ∈ Tw := hsub (by simp)
    exact (inOpenTriBool_S_w_S_S hP hhl hhr hlr Tw).mpr
      (hpart_ii h hh Tw ((hP.shatters Tw l).mpr hl_in) ((hP.shatters Tw r).mpr hr_in))
  refine ⟨k_f, k_g, l, r, hkf0, hkfg, hkg_lt, hl_eq, hr_eq, hlD, hrD, hlr, hblock,
    h_tri_bool, ?_, h5⟩
  intro h hh T₁ T₂ Tm hT12 hlr1 hh1 hlr2 hh2 hlrm hhm s
  have hhl : h ≠ l := fun e => hl_notH (e ▸ hh)
  have hhr : h ≠ r := fun e => hr_notH (e ▸ hh)
  exact wedge_sep_clause_C5 hP hhl hhr hlr hT12
    (hlr1 (by simp)) (hlr1 (by simp)) hh1
    (hlr2 (by simp)) (hlr2 (by simp)) hh2
    (hlrm (by simp)) (hlrm (by simp)) hhm
    (h_tri_bool h hh T₁ hlr1) (h_tri_bool h hh T₂ hlr2) s

/-- Unconditional existential wrapper for `certified_pocket_lr_C6` constructing `cb` and `vc` automatically. -/
theorem exists_certified_pocket_lr_C6 {n : ℕ} {P : Set (ℝ × ℝ)}
    {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ}
    (hP : ShatteredSimplePolygon P S w) (hn : 3 ≤ n)
    (hH : (certifiedSet P S w).Nonempty) :
    ∃ l r : Fin n,
      l ∈ hullVertices S \ certifiedSet P S w ∧
      r ∈ hullVertices S \ certifiedSet P S w ∧
      l ≠ r ∧
      ∀ h ∈ certifiedSet P S w, ∀ Tw : Finset (Fin n), {l, r} ⊆ Tw →
        inOpenTriBool (S h) (w Tw) (S l) (S r) = true := by
  have hB3 : 3 ≤ (hullVertices S).card := hullVertices_card_ge_three hn hP
  obtain ⟨cb⟩ := exists_cyclicSubsetBoundary hP (Finset.Subset.refl _) hB3
  rcases hH with ⟨h₀, hh₀⟩
  obtain ⟨vc⟩ := exists_q_visibleContour hP hn cb (Finset.mem_filter.mp hh₀).2
  obtain ⟨_, _, l, r, _, _, _, _, _, hlD, hrD, hlr, _, htri, _, _⟩ :=
    certified_pocket_lr_C6 hP hn cb vc ⟨h₀, hh₀⟩
  exact ⟨l, r, hlD, hrD, hlr, htri⟩

/-- **Clause `(C6)` Part 2 (`certified_neighbor_tri_C6`, Hull-Neighbor Containment & Wedge Separation)**:
    For every `h ∈ certifiedSet P S w` and its CCW predecessor/successor `hm, hp` on `hullVertices S`,
    every witness `w Tw` with `{hm, hp} ⊆ Tw` satisfies
    `inOpenTriBool (S h) (w Tw) (S hm) (S hp) = true`, and wedge separation holds on `W({hm, hp})`. -/
theorem certified_neighbor_tri_C6 {n : ℕ} {P : Set (ℝ × ℝ)}
    {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ}
    (hP : ShatteredSimplePolygon P S w) (hn : 3 ≤ n)
    {h hm hp : Fin n} (hh : h ∈ certifiedSet P S w)
    (h_pred : IsCCWHullEdge ((hullVertices S).image S) (S hm) (S h))
    (h_succ : IsCCWHullEdge ((hullVertices S).image S) (S h) (S hp)) :
    hm ≠ h ∧ hp ≠ h ∧ hm ≠ hp ∧
    (∀ Tw : Finset (Fin n), {hm, hp} ⊆ Tw →
      inOpenTriBool (S h) (w Tw) (S hm) (S hp) = true) ∧
    (∀ {T₁ T₂ Tm : Finset (Fin n)}, T₁ ≠ T₂ →
      {hm, hp} ⊆ T₁ → h ∈ T₁ → {hm, hp} ⊆ T₂ → h ∈ T₂ → {hm, hp} ⊆ Tm → h ∉ Tm →
      ∀ s : Bool,
        ¬ (orientSign (S h) (w T₁) (w T₂) = s ∧
           orientSign (S h) (w T₁) (w Tm) = s ∧
           orientSign (S h) (w Tm) (w T₂) = s)) := by
  have hcert : IsCertified P S w h := (Finset.mem_filter.mp hh).2
  obtain ⟨b, c, _, _, hbh, hch, hbc, hbh_edge, hhc_edge, hall⟩ :=
    certified_neighbors_and_front hP hn hcert
  have hhm_eq : b = hm := (hP.s_inj (isCCWHullEdge_pred_unique h_pred hbh_edge)).symm
  have hhp_eq : c = hp := (hP.s_inj (isCCWHullEdge_succ_unique h_succ hhc_edge)).symm
  rw [hhm_eq] at hbh hbc hall
  rw [hhp_eq] at hch hbc hall
  have h_tri_bool : ∀ Tw : Finset (Fin n), {hm, hp} ⊆ Tw →
      inOpenTriBool (S h) (w Tw) (S hm) (S hp) = true := by
    intro Tw hsub
    have hb_in : hm ∈ Tw := hsub (by simp)
    have hc_in : hp ∈ Tw := hsub (by simp)
    exact (inOpenTriBool_S_w_S_S hP hbh.symm hch.symm hbc Tw).mpr
      (hall Tw ((hP.shatters Tw hm).mpr hb_in) ((hP.shatters Tw hp).mpr hc_in)).1
  refine ⟨hbh, hch, hbc, h_tri_bool, ?_⟩
  intro T₁ T₂ Tm hT12 h1 hh1 h2 hh2 hmsub hhm s
  exact wedge_sep_clause_C5 hP hbh.symm hch.symm hbc hT12
    (h1 (by simp)) (h1 (by simp)) hh1
    (h2 (by simp)) (h2 (by simp)) hh2
    (hmsub (by simp)) (hmsub (by simp)) hhm
    (h_tri_bool T₁ h1) (h_tri_bool T₂ h2) s

/-- Indexed `CyclicSubsetBoundary` version of `certified_neighbor_tri_C6`:
    for `cb.p_idx i_h = h ∈ certifiedSet P S w`, `hm = cb.p_idx (i_h - 1)` and `hp = cb.p_idx (i_h + 1)`
    satisfy `inOpenTriBool (S h) (w Tw) (S hm) (S hp) = true` whenever `{hm, hp} ⊆ Tw`. -/
theorem certified_neighbor_tri_indexed_C6 {n : ℕ} {P : Set (ℝ × ℝ)}
    {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ}
    (hP : ShatteredSimplePolygon P S w) (hn : 3 ≤ n)
    (cb : CyclicSubsetBoundary S (hullVertices S))
    (i_h : Fin (cb.m + 3))
    (hh : cb.p_idx i_h ∈ certifiedSet P S w)
    {Tw : Finset (Fin n)} (hsub : {cb.p_idx (i_h - 1), cb.p_idx (i_h + 1)} ⊆ Tw) :
    inOpenTriBool (S (cb.p_idx i_h)) (w Tw) (S (cb.p_idx (i_h - 1))) (S (cb.p_idx (i_h + 1))) = true := by
  let p := S ∘ cb.p_idx
  have hp_inj : Function.Injective p := hP.s_inj.comp cb.hp_idx_inj
  have himg_eq : Finset.univ.image p = (hullVertices S).image S := by
    calc Finset.univ.image (S ∘ cb.p_idx)
        = (Finset.univ.image cb.p_idx).image S := Finset.image_image.symm
      _ = (hullVertices S).image S := by rw [cb.hp_idx_img]
  have h_pred : IsCCWHullEdge ((hullVertices S).image S) (S (cb.p_idx (i_h - 1))) (S (cb.p_idx i_h)) := by
    rw [← himg_eq]
    exact (isCCWHullEdge_iff_succ cb.hstrict hp_inj).mpr
      ⟨i_h - 1, rfl, congrArg p (sub_add_cancel i_h 1)⟩
  have h_succ : IsCCWHullEdge ((hullVertices S).image S) (S (cb.p_idx i_h)) (S (cb.p_idx (i_h + 1))) := by
    rw [← himg_eq]
    exact (isCCWHullEdge_iff_succ cb.hstrict hp_inj).mpr ⟨i_h, rfl, rfl⟩
  exact (certified_neighbor_tri_C6 hP hn hh h_pred h_succ).2.2.2.1 Tw hsub

/-- **Clause `(C6)` Part 3 (`certified_zh_separation_C6`, `z_h` Separation across `z_h h`)**:
    For every `h ∈ certifiedSet P S w`, `h = cb.p_idx (finShift vc.i_max kh)` is an inner vertex
    (`0 < kh < vc.d_near`) of `N_q`, and in pure `orientSign` / `oppSideBool` form:
    1. Every predecessor `k₁ < kh` on `N_q` (including `l` and all predecessors in `H`) satisfies
       `orientSign (zWitness w h) (S h) (S (cb.p_idx (finShift vc.i_max k₁))) = true`;
    2. Every successor `kh < k₂ ≤ vc.d_near` on `N_q` (including `r` and all successors in `H`) satisfies
       `orientSign (zWitness w h) (S h) (S (cb.p_idx (finShift vc.i_max k₂))) = false`;
    3. Every predecessor `k₁ < kh` and successor `kh < k₂ ≤ vc.d_near` lie on opposite sides of `z_h h`:
       `oppSideBool (zWitness w h) (S h) (S (cb.p_idx (finShift vc.i_max k₁))) (S (cb.p_idx (finShift vc.i_max k₂))) = true`;
    4. `z_h h` splits the entire hull boundary `∂ conv B \ {h}` into two contiguous `orientSign` arcs. -/
theorem certified_zh_separation_C6 {n : ℕ} {P : Set (ℝ × ℝ)}
    {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ}
    (hP : ShatteredSimplePolygon P S w) (hn : 3 ≤ n)
    (cb : CyclicSubsetBoundary S (hullVertices S))
    (vc : VisibleContour (S ∘ cb.p_idx) (w Finset.univ))
    {h : Fin n} (hh : h ∈ certifiedSet P S w) :
    ∃ kh : ℕ, 0 < kh ∧ kh < vc.d_near ∧ cb.p_idx (finShift vc.i_max kh) = h ∧
      (∀ k₁ : ℕ, k₁ < kh →
        orientSign (zWitness w h) (S h) (S (cb.p_idx (finShift vc.i_max k₁))) = true) ∧
      (∀ k₂ : ℕ, kh < k₂ → k₂ ≤ vc.d_near →
        orientSign (zWitness w h) (S h) (S (cb.p_idx (finShift vc.i_max k₂))) = false) ∧
      (∀ k₁ k₂ : ℕ, k₁ < kh → kh < k₂ → k₂ ≤ vc.d_near →
        oppSideBool (zWitness w h) (S h)
          (S (cb.p_idx (finShift vc.i_max k₁)))
          (S (cb.p_idx (finShift vc.i_max k₂))) = true) ∧
      (∃ k_split : ℕ, 1 ≤ k_split ∧ k_split < cb.m + 2 ∧
        (∀ k : ℕ, 1 ≤ k → k ≤ k_split →
          orientSign (zWitness w h) (S h)
            (S (cb.p_idx (finShift (finShift vc.i_max kh) k))) = false) ∧
        (∀ k : ℕ, k_split < k → k < cb.m + 3 →
          orientSign (zWitness w h) (S h)
            (S (cb.p_idx (finShift (finShift vc.i_max kh) k))) = true)) := by
  have hcert : IsCertified P S w h := (Finset.mem_filter.mp hh).2
  obtain ⟨kh, hkh0, hkh_lt, hkh_eq, hleft, hright, k_split, hs1, hs2, hneg_arc, hpos_arc⟩ :=
    separation hP hn cb vc hcert
  have hleft_sign : ∀ k₁ : ℕ, k₁ < kh →
      orientSign (zWitness w h) (S h) (S (cb.p_idx (finShift vc.i_max k₁))) = true :=
    fun k₁ hk₁ => (orientSign_eq_true_iff _ _ _).mpr (hleft k₁ hk₁)
  have hright_sign : ∀ k₂ : ℕ, kh < k₂ → k₂ ≤ vc.d_near →
      orientSign (zWitness w h) (S h) (S (cb.p_idx (finShift vc.i_max k₂))) = false :=
    fun k₂ hk₂ hk₂_le => (orientSign_eq_false_iff _ _ _).mpr (le_of_lt (hright k₂ hk₂ hk₂_le))
  refine ⟨kh, hkh0, hkh_lt, hkh_eq, hleft_sign, hright_sign, ?_, k_split, hs1, hs2, ?_, ?_⟩
  · intro k₁ k₂ hk₁ hk₂ hk₂_le
    unfold oppSideBool
    rw [hleft_sign k₁ hk₁, hright_sign k₂ hk₂ hk₂_le]
    rfl
  · intro k ha hb
    exact (orientSign_eq_false_iff _ _ _).mpr (le_of_lt (hneg_arc k ha hb))
  · intro k ha hb
    exact (orientSign_eq_true_iff _ _ _).mpr (hpos_arc k ha hb)

/-- **Clause `(C6)` Part 4a (`certified_side_corners_hull_C6`, Hull `side-corners` in `orientSign` Form)**:
    For `h ∈ certifiedSet P S w` and hull vertices `u, v ∈ hullVertices S` (`u ≠ h`, `v ≠ h`),
    if `oppSideBool (zWitness w h) (S h) (S u) (S v) = true` (equivalently
    `orientSign (zWitness w h) (S h) (S u) != orientSign (zWitness w h) (S h) (S v)`),
    then `inOpenTriBool (S h) (w Tw) (S u) (S v) = true` for every witness `w Tw` with `{u, v} ⊆ Tw`. -/
theorem certified_side_corners_hull_C6 {n : ℕ} {P : Set (ℝ × ℝ)}
    {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ}
    (hP : ShatteredSimplePolygon P S w) (hn : 3 ≤ n)
    {h u v : Fin n} (hh : h ∈ certifiedSet P S w)
    (huB : u ∈ hullVertices S) (hvB : v ∈ hullVertices S)
    (huh : u ≠ h) (hvh : v ≠ h)
    (hopp : oppSideBool (zWitness w h) (S h) (S u) (S v) = true)
    {Tw : Finset (Fin n)} (hsub : {u, v} ⊆ Tw) :
    inOpenTriBool (S h) (w Tw) (S u) (S v) = true := by
  have huv : u ≠ v := by
    intro heq; subst heq
    unfold oppSideBool at hopp
    simp at hopp
  have hm : orient2D (zWitness w h) (S h) (S u) * orient2D (zWitness w h) (S h) (S v) < 0 :=
    (oppSideBool_iff_mul_neg
      (orient_w_S_S_ne hP (Finset.univ.erase h) huh.symm)
      (orient_w_S_S_ne hP (Finset.univ.erase h) hvh.symm)).mp hopp
  have hcert : IsCertified P S w h := (Finset.mem_filter.mp hh).2
  have hu_in : u ∈ Tw := hsub (by simp)
  have hv_in : v ∈ Tw := hsub (by simp)
  have htri : InOpenTri (w Tw) (S u) (S v) (S h) :=
    side_corners hP hn hcert huB hvB huh hvh hm Tw
      ((hP.shatters Tw u).mpr hu_in) ((hP.shatters Tw v).mpr hv_in)
  exact (inOpenTriBool_S_w_S_S hP huh.symm hvh.symm huv Tw).mpr htri

/-- Explicit `s : Bool` sign-literal form of `certified_side_corners_hull_C6`. -/
theorem certified_side_corners_hull_orientSign_C6 {n : ℕ} {P : Set (ℝ × ℝ)}
    {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ}
    (hP : ShatteredSimplePolygon P S w) (hn : 3 ≤ n)
    {h u v : Fin n} (hh : h ∈ certifiedSet P S w)
    (huB : u ∈ hullVertices S) (hvB : v ∈ hullVertices S)
    (huh : u ≠ h) (hvh : v ≠ h) {s : Bool}
    (hsu : orientSign (zWitness w h) (S h) (S u) = s)
    (hsv : orientSign (zWitness w h) (S h) (S v) = !s)
    {Tw : Finset (Fin n)} (hsub : {u, v} ⊆ Tw) :
    inOpenTriBool (S h) (w Tw) (S u) (S v) = true := by
  apply certified_side_corners_hull_C6 hP hn hh huB hvB huh hvh _ hsub
  unfold oppSideBool
  rw [hsu, hsv]
  cases s <;> rfl

/-- **Clause `(C6)` Part 4b (`certified_side_corners_cone_C6`, General `S \ {h}` Propagation via Cone Lemma)**:
    For any `h, u, v : Fin n` (`u ≠ h`, `v ≠ h`, `u ≠ v`), if `S h ∈ int tri(z_h, S u, S v)` in Boolean form
    (`inOpenTriBool (S h) (zWitness w h) (S u) (S v) = true`, covering `u` or `v` in `A = interiorPoints S`),
    then `u, v` lie on opposite sides of `z_h h` (`oppSideBool (zWitness w h) (S h) (S u) (S v) = true`)
    and `inOpenTriBool (S h) (w Tw) (S u) (S v) = true` for every witness `w Tw` with `{u, v} ⊆ Tw`. -/
theorem certified_side_corners_cone_C6 {n : ℕ} {P : Set (ℝ × ℝ)}
    {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ}
    (hP : ShatteredSimplePolygon P S w)
    {h u v : Fin n} (huh : u ≠ h) (hvh : v ≠ h) (huv : u ≠ v)
    (htri_zh : inOpenTriBool (S h) (zWitness w h) (S u) (S v) = true) :
    oppSideBool (zWitness w h) (S h) (S u) (S v) = true ∧
    ∀ Tw : Finset (Fin n), {u, v} ⊆ Tw →
      inOpenTriBool (S h) (w Tw) (S u) (S v) = true := by
  have ho_zh : InOpenTri (zWitness w h) (S u) (S v) (S h) :=
    (inOpenTriBool_S_w_S_S hP huh.symm hvh.symm huv (Finset.univ.erase h)).mp htri_zh
  have hopp : oppSideBool (zWitness w h) (S h) (S u) (S v) = true := by
    rcases ho_zh with ⟨μ₁, μ₂, μ₃, _, hμ2, hμ3, hsum, hh1, hh2⟩
    have hμ1_eq : μ₁ = 1 - μ₂ - μ₃ := by linarith
    have hid_u : orient2D (zWitness w h) (S h) (S u) =
        -μ₃ * orient2D (zWitness w h) (S u) (S v) := by
      unfold orient2D; rw [hh1, hh2, hμ1_eq]; ring
    have hid_v : orient2D (zWitness w h) (S h) (S v) =
        μ₂ * orient2D (zWitness w h) (S u) (S v) := by
      unfold orient2D; rw [hh1, hh2, hμ1_eq]; ring
    have hd_ne : orient2D (zWitness w h) (S u) (S v) ≠ 0 :=
      orient_w_S_S_ne hP (Finset.univ.erase h) huv
    have hmul : orient2D (zWitness w h) (S h) (S u) * orient2D (zWitness w h) (S h) (S v) < 0 := by
      rw [hid_u, hid_v]
      have hsq : 0 < orient2D (zWitness w h) (S u) (S v) * orient2D (zWitness w h) (S u) (S v) :=
        mul_self_pos.mpr hd_ne
      nlinarith [mul_pos hμ2 hμ3]
    exact (oppSideBool_iff_mul_neg
      (orient_w_S_S_ne hP (Finset.univ.erase h) huh.symm)
      (orient_w_S_S_ne hP (Finset.univ.erase h) hvh.symm)).mpr hmul
  refine ⟨hopp, fun Tw hsub => ?_⟩
  by_cases heq : Tw = Finset.univ.erase h
  · rw [zWitness] at htri_zh; rwa [heq]
  · have hzh_u : Sees P (zWitness w h) (S u) :=
      (hP.shatters (Finset.univ.erase h) u).mpr (Finset.mem_erase.mpr ⟨huh, Finset.mem_univ _⟩)
    have hzh_v : Sees P (zWitness w h) (S v) :=
      (hP.shatters (Finset.univ.erase h) v).mpr (Finset.mem_erase.mpr ⟨hvh, Finset.mem_univ _⟩)
    have hzh_nh : ¬ Sees P (zWitness w h) (S h) :=
      fun hs => (Finset.mem_erase.mp ((hP.shatters (Finset.univ.erase h) h).mp hs)).1 rfl
    have hu_in : u ∈ Tw := hsub (by simp)
    have hv_in : v ∈ Tw := hsub (by simp)
    have hxU : w Tw ∈ UCone (S h) (S u) (S v) :=
      cone hP.toEnclosureDomain hzh_u hzh_v hzh_nh ho_zh
        ((hP.shatters Tw u).mpr hu_in)
        ((hP.shatters Tw v).mpr hv_in)
        (orient_S_S_w_ne hP huh.symm Tw)
        (orient_S_S_w_ne hP hvh.symm Tw)
        (orient_w_S_w_ne hP (Ne.symm heq) h)
    exact (inOpenTriBool_S_w_S_S hP huh.symm hvh.symm huv Tw).mpr
      ((mem_uCone_iff_inOpenTri (S h) (S u) (S v) (w Tw)).mp hxU)


/-! ## 3. Clause `(C9)` (Half-Plane Lemma Pure Chirotope Orientation Clauses) -/

/-- Exact 2D Cramer linear-functional determinant identity rooted at `p`:
    for any linear functional `L(z) = n₁ z₁ + n₂ z₂ + c` and points `v, p, z₁, z₂ ∈ ℝ²`,
    `orient2D p z₁ z₂ * (L v - L p) = orient2D v p z₁ * (L z₂ - L p) - orient2D v p z₂ * (L z₁ - L p)`. -/
lemma orient2D_linear_functional_cramer (n₁ n₂ c : ℝ) (v p z₁ z₂ : ℝ × ℝ) :
    let L : ℝ × ℝ → ℝ := fun u => n₁ * u.1 + n₂ * u.2 + c
    orient2D p z₁ z₂ * (L v - L p) =
      orient2D v p z₁ * (L z₂ - L p) - orient2D v p z₂ * (L z₁ - L p) := by
  dsimp only
  unfold orient2D
  ring

/-- Helper converting `0 < orient2D a b c * orient2D u v z` with `orientSign u v z = σ`
    (for non-collinear `(u, v, z)`) into `orientSign a b c = σ`. -/
private lemma orientSign_eq_of_mul_pos {a b c u v z : ℝ × ℝ} {σ : Bool}
    (huvz : orient2D u v z ≠ 0)
    (hσ : orientSign u v z = σ)
    (hmul : 0 < orient2D a b c * orient2D u v z) :
    orientSign a b c = σ := by
  cases σ
  · have hn : orient2D u v z < 0 := (orientSign_eq_false_iff_of_ne_zero huvz).mp hσ
    have ha : orient2D a b c < 0 := by nlinarith
    exact (orientSign_eq_false_iff a b c).mpr (le_of_lt ha)
  · have hp : 0 < orient2D u v z := (orientSign_eq_true_iff u v z).mp hσ
    have ha : 0 < orient2D a b c := by nlinarith
    exact (orientSign_eq_true_iff a b c).mpr ha

/-- Pure chirotope & visibility-bitmask hypotheses of the normalized Half-Plane Lemma
    (`upper_8.tex` Lemma 4.1 / Section 8 `(C9)`, matching `gen_chiro_v2.cpp` lines 467–488)
    on `(v = w Tv, q = w Tq, p = S ip, a = S ia, c = S ic)` with `σ := orientSign v q p`. -/
structure HalfPlaneChirotopeConfig {n : ℕ} (P : Set (ℝ × ℝ))
    (S : Fin n → ℝ × ℝ) (w : Finset (Fin n) → ℝ × ℝ)
    (Tv Tq : Finset (Fin n)) (ia ip ic : Fin n) : Prop where
  /-- `(i)` `v` sees `p` and misses `a, c`; `q` sees `a, p, c`. -/
  hp_v : ip ∈ Tv
  ha_not_v : ia ∉ Tv
  hc_not_v : ic ∉ Tv
  ha_q : ia ∈ Tq
  hp_q : ip ∈ Tq
  hc_q : ic ∈ Tq
  /-- `(ii)` `a, p, c` lie on the `σ`-side of `vq` with `θ(a) < θ(p) < θ(c)`. -/
  h_vqa : orientSign (w Tv) (w Tq) (S ia) = orientSign (w Tv) (w Tq) (S ip)
  h_vqc : orientSign (w Tv) (w Tq) (S ic) = orientSign (w Tv) (w Tq) (S ip)
  h_vap : orientSign (w Tv) (S ia) (S ip) = orientSign (w Tv) (w Tq) (S ip)
  h_vpc : orientSign (w Tv) (S ip) (S ic) = orientSign (w Tv) (w Tq) (S ip)
  /-- `(iii)` `v` and `p` lie on opposite sides of `ac` (together with `h_vap`, `h_vpc` this gives `SegmentsCross v p a c`). -/
  h_cross_ac : oppSideBool (S ia) (S ic) (w Tv) (S ip) = true
  /-- `(iv)` Either `v` sees `q`, or `v` and `q` both see two points on opposite sides of `vq`
      (forcing `v` to see `q`), or some `e ∈ Tv ∩ Tq` lies on the `σ`-side of `vq` with `θ(e) < θ(a)`. -/
  h_cond_iv :
    Sees P (w Tv) (w Tq) ∨
    (∃ s₁ s₂ : Fin n, s₁ ∈ Tv ∧ s₁ ∈ Tq ∧ s₂ ∈ Tv ∧ s₂ ∈ Tq ∧
      oppSideBool (w Tv) (w Tq) (S s₁) (S s₂) = true) ∨
    (∃ ie : Fin n, ie ∈ Tv ∧ ie ∈ Tq ∧
      orientSign (w Tv) (w Tq) (S ie) = orientSign (w Tv) (w Tq) (S ip) ∧
      orientSign (w Tv) (S ie) (S ia) = orientSign (w Tv) (w Tq) (S ip))

/-- Convenience constructor building `HalfPlaneChirotopeConfig` from `segsCrossBool (w Tv) (S ip) (S ia) (S ic) = true`. -/
lemma HalfPlaneChirotopeConfig.of_segsCrossBool {n : ℕ} {P : Set (ℝ × ℝ)}
    {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ}
    {Tv Tq : Finset (Fin n)} {ia ip ic : Fin n}
    (hp_v : ip ∈ Tv) (ha_not_v : ia ∉ Tv) (hc_not_v : ic ∉ Tv)
    (ha_q : ia ∈ Tq) (hp_q : ip ∈ Tq) (hc_q : ic ∈ Tq)
    (h_vqa : orientSign (w Tv) (w Tq) (S ia) = orientSign (w Tv) (w Tq) (S ip))
    (h_vqc : orientSign (w Tv) (w Tq) (S ic) = orientSign (w Tv) (w Tq) (S ip))
    (h_vap : orientSign (w Tv) (S ia) (S ip) = orientSign (w Tv) (w Tq) (S ip))
    (h_vpc : orientSign (w Tv) (S ip) (S ic) = orientSign (w Tv) (w Tq) (S ip))
    (h_cross : segsCrossBool (w Tv) (S ip) (S ia) (S ic) = true)
    (h_cond_iv :
      Sees P (w Tv) (w Tq) ∨
      (∃ s₁ s₂ : Fin n, s₁ ∈ Tv ∧ s₁ ∈ Tq ∧ s₂ ∈ Tv ∧ s₂ ∈ Tq ∧
        oppSideBool (w Tv) (w Tq) (S s₁) (S s₂) = true) ∨
      (∃ ie : Fin n, ie ∈ Tv ∧ ie ∈ Tq ∧
        orientSign (w Tv) (w Tq) (S ie) = orientSign (w Tv) (w Tq) (S ip) ∧
        orientSign (w Tv) (S ie) (S ia) = orientSign (w Tv) (w Tq) (S ip))) :
    HalfPlaneChirotopeConfig P S w Tv Tq ia ip ic where
  hp_v := hp_v
  ha_not_v := ha_not_v
  hc_not_v := hc_not_v
  ha_q := ha_q
  hp_q := hp_q
  hc_q := hc_q
  h_vqa := h_vqa
  h_vqc := h_vqc
  h_vap := h_vap
  h_vpc := h_vpc
  h_cross_ac := by
    unfold segsCrossBool at h_cross
    simp only [Bool.and_eq_true] at h_cross
    exact h_cross.2
  h_cond_iv := h_cond_iv

/-- **Clause `(C9)` Master Soundness Theorem (`half_plane_chirotope_clauses_C9`)**:
    Under `HalfPlaneChirotopeConfig P S w Tv Tq ia ip ic` on `ShatteredSimplePolygon P S w`,
    putting `v := w Tv`, `q := w Tq`, `p := S ip`, `a := S ia`, `c := S ic`, and
    `σ := orientSign v q p`:
    1. **`Claim 4.4(a)`**: Every witness `x = w Tx` seeing `{a, c}` (`{ia, ic} ⊆ Tx`) satisfies
       `orientSign v a x = !σ` (and `sameSideBool v a x q = true`);
    2. **`Claim 4.4(b)`**: Every witness `x = w Tx` seeing `{a, c}` (`{ia, ic} ⊆ Tx`) satisfies
       `orientSign v p x = !σ` (and `sameSideBool v p x q = true`);
    3. **`Claim 4.4(c)`**: Every witness `x = w Tx` seeing `{a, c, p}` (`{ia, ic} ⊆ Tx`, `ip ∈ Tx`,
       including both `Tx ≠ Tq` and `Tx = Tq`) satisfies `orientSign p x a = σ`
       (and when `Tx ≠ Tq`, `sameSideBool p a x q = true`);
    4. **`Claim 4.5` Slope Separation in Pure `orientSign` Form**: For every witness `x = w Tx`
       seeing `{a, c, p}` (`{ia, ic} ⊆ Tx`, `ip ∈ Tx`) and every witness `y = w Ty` seeing `{a, c}`
       and missing `p` (`{ia, ic} ⊆ Ty`, `ip ∉ Ty`), `orientSign p x y = σ`. -/
theorem half_plane_chirotope_clauses_C9 {n : ℕ} {P : Set (ℝ × ℝ)}
    {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ}
    (hP : ShatteredSimplePolygon P S w)
    {Tv Tq : Finset (Fin n)} {ia ip ic : Fin n}
    (hcfg : HalfPlaneChirotopeConfig P S w Tv Tq ia ip ic) :
    let σ := orientSign (w Tv) (w Tq) (S ip)
    (∀ {Tx : Finset (Fin n)}, {ia, ic} ⊆ Tx →
      orientSign (w Tv) (S ia) (w Tx) = !σ ∧
      sameSideBool (w Tv) (S ia) (w Tx) (w Tq) = true) ∧
    (∀ {Tx : Finset (Fin n)}, {ia, ic} ⊆ Tx →
      orientSign (w Tv) (S ip) (w Tx) = !σ ∧
      sameSideBool (w Tv) (S ip) (w Tx) (w Tq) = true) ∧
    (∀ {Tx : Finset (Fin n)}, {ia, ic} ⊆ Tx → ip ∈ Tx →
      orientSign (S ip) (w Tx) (S ia) = σ ∧
      (Tx ≠ Tq → sameSideBool (S ip) (S ia) (w Tx) (w Tq) = true)) ∧
    (∀ {Tx Ty : Finset (Fin n)}, {ia, ic} ⊆ Tx → ip ∈ Tx → {ia, ic} ⊆ Ty → ip ∉ Ty →
      orientSign (S ip) (w Tx) (w Ty) = σ) := by
  intro σ
  have hTvq : Tv ≠ Tq := fun heq => hcfg.ha_not_v (heq ▸ hcfg.ha_q)
  have hap : ia ≠ ip := fun heq => hcfg.ha_not_v (heq ▸ hcfg.hp_v)
  have hcp : ic ≠ ip := fun heq => hcfg.hc_not_v (heq ▸ hcfg.hp_v)
  have hac : ia ≠ ic := by
    intro heq
    have hc := hcfg.h_cross_ac
    rw [heq] at hc
    have h0 : ∀ z, orient2D (S ic) (S ic) z = 0 := fun z => by unfold orient2D; ring
    simp [oppSideBool, orientSign, h0] at hc
  have hvqp_ne : orient2D (w Tv) (w Tq) (S ip) ≠ 0 := orient_w_w_S_ne hP hTvq ip
  have hvqa_ne : orient2D (w Tv) (w Tq) (S ia) ≠ 0 := orient_w_w_S_ne hP hTvq ia
  have hvqc_ne : orient2D (w Tv) (w Tq) (S ic) ≠ 0 := orient_w_w_S_ne hP hTvq ic
  have hvap_ne : orient2D (w Tv) (S ia) (S ip) ≠ 0 := orient_w_S_S_ne hP Tv hap
  have hvpc_ne : orient2D (w Tv) (S ip) (S ic) ≠ 0 := orient_w_S_S_ne hP Tv hcp.symm
  have hsame_ap : SameSideOfLine (w Tv) (w Tq) (S ia) (S ip) :=
    mul_pos_of_orientSign_eq hvqa_ne hvqp_ne hcfg.h_vqa rfl
  have hsame_cp : SameSideOfLine (w Tv) (w Tq) (S ic) (S ip) :=
    mul_pos_of_orientSign_eq hvqc_ne hvqp_ne hcfg.h_vqc rfl
  have htheta_ap : 0 < orient2D (w Tv) (S ia) (S ip) * orient2D (w Tv) (w Tq) (S ip) :=
    mul_pos_of_orientSign_eq hvap_ne hvqp_ne hcfg.h_vap rfl
  have htheta_pc : 0 < orient2D (w Tv) (S ip) (S ic) * orient2D (w Tv) (w Tq) (S ip) :=
    mul_pos_of_orientSign_eq hvpc_ne hvqp_ne hcfg.h_vpc rfl
  have hcross : Sec5HP.SegmentsCross (w Tv) (S ip) (S ia) (S ic) := by
    refine ⟨?_, ?_⟩
    · have hvpa_opp : orientSign (w Tv) (S ip) (S ia) = !σ := by
        rw [ChirotopeSoundness.orientSign_swap23 hvap_ne, hcfg.h_vap]
      exact mul_neg_of_orientSign_opp
        (orient_w_S_S_ne hP Tv hap.symm) hvpc_ne hvpa_opp
        (by rw [Bool.not_not]; exact hcfg.h_vpc)
    · exact (oppSideBool_iff_mul_neg
        (orient_S_S_w_ne hP hac Tv)
        (orient_S_S_S_ne hP hac hcp hap)).mp hcfg.h_cross_ac
  have hiv : Sees P (w Tv) (w Tq) ∨
      ∃ ie : Fin n, Sees P (w Tv) (S ie) ∧ Sees P (w Tq) (S ie) ∧
        SameSideOfLine (w Tv) (w Tq) (S ie) (S ia) ∧
        0 < orient2D (w Tv) (S ie) (S ia) * orient2D (w Tv) (w Tq) (S ip) := by
    rcases hcfg.h_cond_iv with hvq | ⟨s₁, s₂, hs1v, hs1q, hs2v, hs2q, hopp⟩ | ⟨ie, hev, heq_in, hvqe, hvea⟩
    · exact Or.inl hvq
    · exact Or.inl (vis_chord_sees_of_oppSide hP hTvq hs1v hs1q hs2v hs2q hopp)
    · right
      have hea : ie ≠ ia := fun h => hcfg.ha_not_v (h ▸ hev)
      refine ⟨ie, (hP.shatters Tv ie).mpr hev, (hP.shatters Tq ie).mpr heq_in, ?_, ?_⟩
      · exact mul_pos_of_orientSign_eq (orient_w_w_S_ne hP hTvq ie) hvqa_ne hvqe hcfg.h_vqa
      · exact mul_pos_of_orientSign_eq (orient_w_S_S_ne hP Tv hea) hvqp_ne hvea rfl
  obtain ⟨H, hH_test, hH_bdry, hH_v, _, hH_a, _, hH_pos⟩ :=
    half_plane_lemma_orient hP Tv Tq ia ip ic
      ((hP.shatters Tv ip).mpr hcfg.hp_v)
      (fun hs => hcfg.ha_not_v ((hP.shatters Tv ia).mp hs))
      (fun hs => hcfg.hc_not_v ((hP.shatters Tv ic).mp hs))
      ((hP.shatters Tq ia).mpr hcfg.ha_q)
      ((hP.shatters Tq ip).mpr hcfg.hp_q)
      ((hP.shatters Tq ic).mpr hcfg.hc_q)
      hsame_ap hsame_cp htheta_ap htheta_pc hcross hiv
  have hvaq_sign : orientSign (w Tv) (S ia) (w Tq) = !σ := by
    rw [ChirotopeSoundness.orientSign_swap23 hvqa_ne, hcfg.h_vqa]
  have hvpq_sign : orientSign (w Tv) (S ip) (w Tq) = !σ := by
    rw [ChirotopeSoundness.orientSign_swap23 hvqp_ne]
  have hvpa_sign : orientSign (w Tv) (S ip) (S ia) = !σ := by
    rw [ChirotopeSoundness.orientSign_swap23 hvap_ne, hcfg.h_vap]
  -- Helper proving `orientSign (S ip) (w Tx) z = σ` via `orient2D_linear_functional_cramer`
  have hcramer_sign : ∀ {Tx : Finset (Fin n)} {z : ℝ × ℝ},
      {ia, ic} ⊆ Tx → ip ∈ Tx →
      orient2D (S ip) (w Tx) z ≠ 0 →
      orient2D (w Tv) (S ip) z ≠ 0 →
      orientSign (w Tv) (S ip) z = !σ →
      H.MemNeg z →
      orientSign (S ip) (w Tx) z = σ := by
    intro Tx z hTx_ac hTx_p hpxz_ne hvpz_ne hvpz_sign hz_neg
    have hx_mem : w Tx ∈ WitnessSet {ia, ic} ∅ w :=
      ⟨Tx, hTx_ac, Finset.disjoint_empty_right Tx, rfl⟩
    have hx_pos : H.MemPos (w Tx) :=
      (hH_test (w Tx) hx_mem).2.mp ((hP.shatters Tx ip).mpr hTx_p)
    have hTx_ne_Tv : Tv ≠ Tx := fun heq => hcfg.ha_not_v (heq ▸ hTx_ac (by simp))
    have hvpx_ne : orient2D (w Tv) (S ip) (w Tx) ≠ 0 := orient_w_S_w_ne hP hTx_ne_Tv ip
    have hvpx_mul : 0 < orient2D (w Tv) (S ip) (w Tx) * orient2D (w Tv) (S ip) (w Tq) :=
      (hH_pos (w Tx) hx_mem).1
    have hvpx_sign : orientSign (w Tv) (S ip) (w Tx) = !σ :=
      orientSign_eq_of_mul_pos (orient_w_S_w_ne hP hTvq ip) hvpq_sign hvpx_mul
    have hid := orient2D_linear_functional_cramer H.n.1 H.n.2 H.c (w Tv) (S ip) (w Tx) z
    dsimp only at hid
    rw [hH_bdry, sub_zero, sub_zero, sub_zero] at hid
    have hLv : 0 < H.n.1 * (w Tv).1 + H.n.2 * (w Tv).2 + H.c := hH_v
    have hLx : 0 < H.n.1 * (w Tx).1 + H.n.2 * (w Tx).2 + H.c := hx_pos
    have hLz : H.n.1 * z.1 + H.n.2 * z.2 + H.c < 0 := hz_neg
    cases hσ_cases : σ
    · rw [hσ_cases] at hvpx_sign hvpz_sign
      have hvpx_gt : 0 < orient2D (w Tv) (S ip) (w Tx) :=
        (orientSign_eq_true_iff _ _ _).mp hvpx_sign
      have hvpz_gt : 0 < orient2D (w Tv) (S ip) z :=
        (orientSign_eq_true_iff _ _ _).mp hvpz_sign
      have hprod_neg : orient2D (S ip) (w Tx) z * (H.n.1 * (w Tv).1 + H.n.2 * (w Tv).2 + H.c) < 0 := by
        nlinarith
      have hneg : orient2D (S ip) (w Tx) z < 0 := by nlinarith
      exact (orientSign_eq_false_iff _ _ _).mpr (le_of_lt hneg)
    · rw [hσ_cases] at hvpx_sign hvpz_sign
      have hvpx_lt : orient2D (w Tv) (S ip) (w Tx) < 0 :=
        (orientSign_eq_false_iff_of_ne_zero hvpx_ne).mp hvpx_sign
      have hvpz_lt : orient2D (w Tv) (S ip) z < 0 :=
        (orientSign_eq_false_iff_of_ne_zero hvpz_ne).mp hvpz_sign
      have hprod_pos : 0 < orient2D (S ip) (w Tx) z * (H.n.1 * (w Tv).1 + H.n.2 * (w Tv).2 + H.c) := by
        nlinarith
      have hpos : 0 < orient2D (S ip) (w Tx) z := by nlinarith
      exact (orientSign_eq_true_iff _ _ _).mpr hpos
  have hpart_a : ∀ {Tx : Finset (Fin n)}, {ia, ic} ⊆ Tx →
      orientSign (w Tv) (S ia) (w Tx) = !σ ∧
      sameSideBool (w Tv) (S ia) (w Tx) (w Tq) = true := by
    intro Tx hTx
    have hx_mem : w Tx ∈ WitnessSet {ia, ic} ∅ w :=
      ⟨Tx, hTx, Finset.disjoint_empty_right Tx, rfl⟩
    have hmul := (hH_pos (w Tx) hx_mem).2
    have hsgn : orientSign (w Tv) (S ia) (w Tx) = !σ :=
      orientSign_eq_of_mul_pos
        (orient_w_S_w_ne hP hTvq ia) hvaq_sign hmul
    refine ⟨hsgn, ?_⟩
    unfold sameSideBool
    rw [hsgn, hvaq_sign, beq_self_eq_true]
  have hpart_b : ∀ {Tx : Finset (Fin n)}, {ia, ic} ⊆ Tx →
      orientSign (w Tv) (S ip) (w Tx) = !σ ∧
      sameSideBool (w Tv) (S ip) (w Tx) (w Tq) = true := by
    intro Tx hTx
    have hx_mem : w Tx ∈ WitnessSet {ia, ic} ∅ w :=
      ⟨Tx, hTx, Finset.disjoint_empty_right Tx, rfl⟩
    have hmul := (hH_pos (w Tx) hx_mem).1
    have hsgn : orientSign (w Tv) (S ip) (w Tx) = !σ :=
      orientSign_eq_of_mul_pos
        (orient_w_S_w_ne hP hTvq ip) hvpq_sign hmul
    refine ⟨hsgn, ?_⟩
    unfold sameSideBool
    rw [hsgn, hvpq_sign, beq_self_eq_true]
  have hpart_c : ∀ {Tx : Finset (Fin n)}, {ia, ic} ⊆ Tx → ip ∈ Tx →
      orientSign (S ip) (w Tx) (S ia) = σ ∧
      (Tx ≠ Tq → sameSideBool (S ip) (S ia) (w Tx) (w Tq) = true) := by
    intro Tx hTx hTx_p
    have hsgn : orientSign (S ip) (w Tx) (S ia) = σ :=
      hcramer_sign hTx hTx_p
        (orient_S_w_S_ne hP hap.symm Tx)
        (orient_w_S_S_ne hP Tv hap.symm)
        hvpa_sign hH_a
    have hTq_ac : {ia, ic} ⊆ Tq := by
      intro u hu
      simp only [Finset.mem_insert, Finset.mem_singleton] at hu
      rcases hu with rfl | rfl
      · exact hcfg.ha_q
      · exact hcfg.hc_q
    have hsgn_q : orientSign (S ip) (w Tq) (S ia) = σ :=
      hcramer_sign hTq_ac hcfg.hp_q
        (orient_S_w_S_ne hP hap.symm Tq)
        (orient_w_S_S_ne hP Tv hap.symm)
        hvpa_sign hH_a
    refine ⟨hsgn, fun _ => ?_⟩
    unfold sameSideBool
    rw [ChirotopeSoundness.orientSign_swap23 (orient_S_w_S_ne hP hap.symm Tx),
        ChirotopeSoundness.orientSign_swap23 (orient_S_w_S_ne hP hap.symm Tq),
        hsgn, hsgn_q, beq_self_eq_true]
  have hpart_slope : ∀ {Tx Ty : Finset (Fin n)}, {ia, ic} ⊆ Tx → ip ∈ Tx → {ia, ic} ⊆ Ty → ip ∉ Ty →
      orientSign (S ip) (w Tx) (w Ty) = σ := by
    intro Tx Ty hTx hTx_p hTy hTy_np
    have hTx_ne_Ty : Tx ≠ Ty := fun heq => hTy_np (heq ▸ hTx_p)
    have hTy_ne_Tv : Tv ≠ Ty := fun heq => hcfg.ha_not_v (heq ▸ hTy (by simp))
    have hy_mem : w Ty ∈ WitnessSet {ia, ic} ∅ w :=
      ⟨Ty, hTy, Finset.disjoint_empty_right Ty, rfl⟩
    have hy_not_sees_p : ¬ Sees P (w Ty) (S ip) :=
      fun hs => hTy_np ((hP.shatters Ty ip).mp hs)
    have hy_neg : H.MemNeg (w Ty) := by
      rcases (hH_test (w Ty) hy_mem).1 with hpos | hneg
      · exact False.elim (hy_not_sees_p ((hH_test (w Ty) hy_mem).2.mpr hpos))
      · exact hneg
    exact hcramer_sign hTx hTx_p
      (orient_S_w_w_ne hP ip hTx_ne_Ty)
      (orient_w_S_w_ne hP hTy_ne_Tv ip)
      (hpart_b hTy).1 hy_neg
  exact ⟨hpart_a, hpart_b, hpart_c, hpart_slope⟩


/-! ## 4. Unified Chirotope `(C1)`–`(C11)` + `SoundRUPChecker` End-to-End Bridge -/

/-- Extended Theorem 8.1 Soundness Bundle combining `SoundChirotopeBundle` with
    Clause `(C6)` (certified pocket geometry) and Clause `(C9)` (Half-Plane chirotope clauses). -/
structure ExtendedSoundChirotopeBundle {n k : ℕ} (P : Set (ℝ × ℝ))
    (S : Fin n → ℝ × ℝ) (w : Finset (Fin n) → ℝ × ℝ)
    (W₀ : Fin k ↪ Finset (Fin n)) : Prop where
  base : SoundChirotopeBundle P S w W₀
  /-- `(C6)` Outer pocket containment on `W({l, r})` whenever `H ≠ ∅` (`3 ≤ n`). -/
  c6_pocket_lr : 3 ≤ n → (certifiedSet P S w).Nonempty →
    ∃ l r : Fin n,
      l ∈ hullVertices S \ certifiedSet P S w ∧
      r ∈ hullVertices S \ certifiedSet P S w ∧
      l ≠ r ∧
      ∀ h ∈ certifiedSet P S w, ∀ Tw : Finset (Fin n), {l, r} ⊆ Tw →
        inOpenTriBool (S h) (w Tw) (S l) (S r) = true
  /-- `(C6)` Hull-neighbor containment on `W({hm, hp})` (`3 ≤ n`). -/
  c6_neighbor_tri : 3 ≤ n → ∀ {h hm hp : Fin n},
    h ∈ certifiedSet P S w →
    IsCCWHullEdge ((hullVertices S).image S) (S hm) (S h) →
    IsCCWHullEdge ((hullVertices S).image S) (S h) (S hp) →
    ∀ Tw : Finset (Fin n), {hm, hp} ⊆ Tw →
      inOpenTriBool (S h) (w Tw) (S hm) (S hp) = true
  /-- `(C6)` Hull `side-corners` propagation in `orientSign` / `oppSideBool` form (`3 ≤ n`). -/
  c6_side_corners : 3 ≤ n → ∀ {h u v : Fin n} {Tw : Finset (Fin n)},
    h ∈ certifiedSet P S w → u ∈ hullVertices S → v ∈ hullVertices S →
    u ≠ h → v ≠ h →
    oppSideBool (zWitness w h) (S h) (S u) (S v) = true →
    {u, v} ⊆ Tw →
    inOpenTriBool (S h) (w Tw) (S u) (S v) = true
  /-- `(C9)` Pure chirotope Half-Plane orientation & slope-separation clauses. -/
  c9_half_plane : ∀ {Tv Tq : Finset (Fin n)} {ia ip ic : Fin n},
    HalfPlaneChirotopeConfig P S w Tv Tq ia ip ic →
    let σ := orientSign (w Tv) (w Tq) (S ip)
    (∀ {Tx : Finset (Fin n)}, {ia, ic} ⊆ Tx → orientSign (w Tv) (S ia) (w Tx) = !σ) ∧
    (∀ {Tx : Finset (Fin n)}, {ia, ic} ⊆ Tx → orientSign (w Tv) (S ip) (w Tx) = !σ) ∧
    (∀ {Tx : Finset (Fin n)}, {ia, ic} ⊆ Tx → ip ∈ Tx → orientSign (S ip) (w Tx) (S ia) = σ) ∧
    (∀ {Tx Ty : Finset (Fin n)}, {ia, ic} ⊆ Tx → ip ∈ Tx → {ia, ic} ⊆ Ty → ip ∉ Ty →
      orientSign (S ip) (w Tx) (w Ty) = σ)

/-- Every `ShatteredSimplePolygon P S w` satisfies `ExtendedSoundChirotopeBundle P S w W₀`. -/
theorem extended_sound_chirotope_reduction {n k : ℕ} {P : Set (ℝ × ℝ)}
    {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ}
    (hP : ShatteredSimplePolygon P S w) (W₀ : Fin k ↪ Finset (Fin n)) :
    ExtendedSoundChirotopeBundle P S w W₀ where
  base := sound_chirotope_reduction hP W₀
  c6_pocket_lr hn hH := exists_certified_pocket_lr_C6 hP hn hH
  c6_neighbor_tri hn := fun hh hpred hsucc => (certified_neighbor_tri_C6 hP hn hh hpred hsucc).2.2.2.1
  c6_side_corners hn := fun hh huB hvB huh hvh hopp hsub =>
    certified_side_corners_hull_C6 hP hn hh huB hvB huh hvh hopp hsub
  c9_half_plane hcfg := by
    obtain ⟨ha, hb, hc, hs⟩ := half_plane_chirotope_clauses_C9 hP hcfg
    exact ⟨fun h => (ha h).1, fun h => (hb h).1, fun h1 h2 => (hc h1 h2).1, hs⟩

/-- **End-to-End Chirotope + RUP Refutation Bridge**:
    If a Boolean valuation `v : Nat → Bool` (extracted from `orientSign` on `ShatteredSimplePolygon P S w`)
    satisfies `evalCNF v cnf = true` and `SoundRUPChecker.checkCert cnf cert = true`, then `False`. -/
theorem refutation_of_sound_cnf_and_rup {v : Nat → Bool}
    {cnf : SoundRUPChecker.CNF} {cert : SoundRUPChecker.Cert}
    (hsound : SoundRUPChecker.evalCNF v cnf = true)
    (hcert : SoundRUPChecker.checkCert cnf cert = true) :
    False := by
  have hfalse := SoundRUPChecker.checkCert_sound cnf cert hcert v
  rw [hsound] at hfalse
  exact Bool.noConfusion hfalse

end CertifiedAndHalfPlaneSoundness

end
