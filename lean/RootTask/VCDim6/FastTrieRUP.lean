/-!
# Fast Pure-Kernel Binary-Trie RUP Refutation Checker (`FastTrieRUP`)

Provides an $O(\log N)$-per-lookup Reverse Unit Propagation (RUP) verifier designed specifically for
Lean 4's pure kernel reducer (`decide` / `Eq.refl true`, zero `native_decide`, zero `Lean.trustCompiler`):
1. `PIdx`: positive binary index (`xH | xO p | xI p`) enabling pure constructor-pattern-match trie
   indexing without `List` scans or `Int` arithmetic.
2. `BinTrie α`: radix-2 trie with `get`, `insert`, and `erase` in $O(\log K)$ constructor steps.
3. `Lit := Bool × PIdx`: signed literal (`(true, v)` = positive, `(false, v)` = negative),
   with `BinTrie Bool` falsified-literal maps supporting immediate complementary-literal conflict detection.
4. Compact ASCII nibble-varint decoder (`'a'..'p'` continuation nibbles, `'A'..'P'` terminal nibbles)
   so multi-thousand-step RUP certificates parse and elaborate as a single `String` AST node with zero
   typeclass synthesis overhead.
-/

namespace VCDim6.FastTrieRUP

noncomputable section

/-- Positive binary key (`1 = xH`, `2p = xO p`, `2p + 1 = xI p`). -/
inductive PIdx : Type
  | xH : PIdx
  | xO : PIdx → PIdx
  | xI : PIdx → PIdx
  deriving DecidableEq

def mkXO : PIdx → PIdx
  | .xH => .xO .xH
  | .xO r => .xO (.xO r)
  | .xI r => .xO (.xI r)

def mkXI : PIdx → PIdx
  | .xH => .xI .xH
  | .xO r => .xI (.xO r)
  | .xI r => .xI (.xI r)

@[simp] theorem mkXO_eq (p : PIdx) : mkXO p = .xO p := by cases p <;> rfl
@[simp] theorem mkXI_eq (p : PIdx) : mkXI p = .xI p := by cases p <;> rfl

def strictPIdx (k : PIdx) : PIdx :=
  @PIdx.rec (fun _ => PIdx) .xH (fun _ ih => mkXO ih) (fun _ ih => mkXI ih) k

@[simp] theorem strictPIdx_eq (p : PIdx) : strictPIdx p = p := by
  induction p with
  | xH => rfl
  | xO p ih => change mkXO (strictPIdx p) = .xO p; rw [ih, mkXO_eq]
  | xI p ih => change mkXI (strictPIdx p) = .xI p; rw [ih, mkXI_eq]

/-- Successor on `PIdx` (`p + 1`, spine-strict, direct `.rec` without `.brecOn`). -/
def PIdx.succ (k : PIdx) : PIdx :=
  @PIdx.rec (fun _ => PIdx) (.xO .xH) (fun p _ => .xI p) (fun _ ih => mkXO ih) k

/-- Binary radix tree indexed by `PIdx`. -/
inductive BinTrie (α : Type) : Type
  | leaf : BinTrie α
  | node : Option α → BinTrie α → BinTrie α → BinTrie α

def mkNodeL {α : Type} (v : Option α) (l r : BinTrie α) : BinTrie α :=
  match l with
  | .leaf => .node v .leaf r
  | .node lv ll lr => .node v (.node lv ll lr) r

def mkNodeR {α : Type} (v : Option α) (l r : BinTrie α) : BinTrie α :=
  match r with
  | .leaf => .node v l .leaf
  | .node rv rl rr => .node v l (.node rv rl rr)

@[simp] theorem mkNodeL_eq {α : Type} (v : Option α) (l r : BinTrie α) :
    mkNodeL v l r = .node v l r := by cases l <;> rfl

@[simp] theorem mkNodeR_eq {α : Type} (v : Option α) (l r : BinTrie α) :
    mkNodeR v l r = .node v l r := by cases r <;> rfl

def withStrictTrie {α β : Type} (t : BinTrie α) (k : BinTrie α → β) : β :=
  match t with
  | .leaf => k .leaf
  | .node v l r => k (.node v l r)

@[simp] theorem withStrictTrie_eq {α β : Type} (t : BinTrie α) (k : BinTrie α → β) :
    withStrictTrie t k = k t := by cases t <;> rfl

/-- $O(\log k)$ trie lookup via direct `PIdx.rec` (zero `.brecOn` / `PProd` shadow allocation!). -/
def trieGet {α : Type} (k : PIdx) : BinTrie α → Option α :=
  @PIdx.rec (fun _ => BinTrie α → Option α)
    (fun t => match t with | .leaf => none | .node v _ _ => v)
    (fun _ ih t => match t with | .leaf => none | .node _ l _ => ih l)
    (fun _ ih t => match t with | .leaf => none | .node _ _ r => ih r)
    k

@[inline] def BinTrie.get {α : Type} (t : BinTrie α) (k : PIdx) : Option α :=
  trieGet k t

/-- $O(\log k)$ spine-strict trie insertion via direct `PIdx.rec` (zero `.brecOn`). -/
def trieInsert {α : Type} (x : α) (k : PIdx) : BinTrie α → BinTrie α :=
  @PIdx.rec (fun _ => BinTrie α → BinTrie α)
    (fun t => match t with | .leaf => .node (some x) .leaf .leaf | .node _ l r => .node (some x) l r)
    (fun _ ih t => match t with | .leaf => mkNodeL none (ih .leaf) .leaf | .node v l r => mkNodeL v (ih l) r)
    (fun _ ih t => match t with | .leaf => mkNodeR none .leaf (ih .leaf) | .node v l r => mkNodeR v l (ih r))
    k

@[inline] def BinTrie.insert {α : Type} (t : BinTrie α) (k : PIdx) (x : α) : BinTrie α :=
  trieInsert x k t

/-- $O(\log k)$ spine-strict trie key deletion via direct `PIdx.rec` (zero `.brecOn`). -/
def trieErase {α : Type} (k : PIdx) : BinTrie α → BinTrie α :=
  @PIdx.rec (fun _ => BinTrie α → BinTrie α)
    (fun t => match t with | .leaf => .leaf | .node _ l r => .node none l r)
    (fun _ ih t => match t with | .leaf => .leaf | .node v l r => mkNodeL v (ih l) r)
    (fun _ ih t => match t with | .leaf => .leaf | .node v l r => mkNodeR v l (ih r))
    k

@[inline] def BinTrie.erase {α : Type} (t : BinTrie α) (k : PIdx) : BinTrie α :=
  trieErase k t

@[simp] theorem trieGet_xH {α : Type} (t : BinTrie α) :
    trieGet .xH t = (match t with | .leaf => none | .node v _ _ => v) := rfl
@[simp] theorem trieGet_xO {α : Type} (p : PIdx) (t : BinTrie α) :
    trieGet (.xO p) t = (match t with | .leaf => none | .node _ l _ => trieGet p l) := rfl
@[simp] theorem trieGet_xI {α : Type} (p : PIdx) (t : BinTrie α) :
    trieGet (.xI p) t = (match t with | .leaf => none | .node _ _ r => trieGet p r) := rfl

@[simp] theorem trieInsert_xH {α : Type} (x : α) (t : BinTrie α) :
    trieInsert x .xH t = (match t with | .leaf => .node (some x) .leaf .leaf | .node _ l r => .node (some x) l r) := rfl
@[simp] theorem trieInsert_xO {α : Type} (x : α) (p : PIdx) (t : BinTrie α) :
    trieInsert x (.xO p) t = (match t with | .leaf => mkNodeL none (trieInsert x p .leaf) .leaf | .node v l r => mkNodeL v (trieInsert x p l) r) := rfl
@[simp] theorem trieInsert_xI {α : Type} (x : α) (p : PIdx) (t : BinTrie α) :
    trieInsert x (.xI p) t = (match t with | .leaf => mkNodeR none .leaf (trieInsert x p .leaf) | .node v l r => mkNodeR v l (trieInsert x p r)) := rfl

@[simp] theorem trieErase_xH {α : Type} (t : BinTrie α) :
    trieErase .xH t = (match t with | .leaf => .leaf | .node _ l r => .node none l r) := rfl
@[simp] theorem trieErase_xO {α : Type} (p : PIdx) (t : BinTrie α) :
    trieErase (.xO p) t = (match t with | .leaf => .leaf | .node v l r => mkNodeL v (trieErase p l) r) := rfl
@[simp] theorem trieErase_xI {α : Type} (p : PIdx) (t : BinTrie α) :
    trieErase (.xI p) t = (match t with | .leaf => .leaf | .node v l r => mkNodeR v l (trieErase p r)) := rfl

@[simp] theorem trieGet_leaf {α : Type} (k : PIdx) : trieGet k (.leaf : BinTrie α) = none := by
  cases k <;> rfl

theorem BinTrie.get_leaf {α : Type} (k : PIdx) : (BinTrie.leaf : BinTrie α).get k = none :=
  trieGet_leaf k

theorem BinTrie.get_insert_self {α : Type} (t : BinTrie α) (k : PIdx) (x : α) :
    (t.insert k x).get k = some x := by
  induction k generalizing t with
  | xH => cases t <;> rfl
  | xO p ih =>
    cases t with
    | leaf => simpa [BinTrie.insert, BinTrie.get] using ih .leaf
    | node v l r => simpa [BinTrie.insert, BinTrie.get] using ih l
  | xI p ih =>
    cases t with
    | leaf => simpa [BinTrie.insert, BinTrie.get] using ih .leaf
    | node v l r => simpa [BinTrie.insert, BinTrie.get] using ih r

theorem BinTrie.get_insert_ne {α : Type} (t : BinTrie α) {k₁ k₂ : PIdx} (x : α) (hne : k₁ ≠ k₂) :
    (t.insert k₁ x).get k₂ = t.get k₂ := by
  induction k₁ generalizing t k₂ with
  | xH =>
    cases k₂ with
    | xH => exact False.elim (hne rfl)
    | xO p₂ => cases t <;> simp [BinTrie.insert, BinTrie.get]
    | xI p₂ => cases t <;> simp [BinTrie.insert, BinTrie.get]
  | xO p₁ ih =>
    cases k₂ with
    | xH => cases t <;> simp [BinTrie.insert, BinTrie.get]
    | xO p₂ =>
      have hp : p₁ ≠ p₂ := fun e => hne (congrArg PIdx.xO e)
      cases t with
      | leaf => simpa [BinTrie.insert, BinTrie.get] using ih .leaf hp
      | node v l r => simpa [BinTrie.insert, BinTrie.get] using ih l hp
    | xI p₂ => cases t <;> simp [BinTrie.insert, BinTrie.get]
  | xI p₁ ih =>
    cases k₂ with
    | xH => cases t <;> simp [BinTrie.insert, BinTrie.get]
    | xO p₂ => cases t <;> simp [BinTrie.insert, BinTrie.get]
    | xI p₂ =>
      have hp : p₁ ≠ p₂ := fun e => hne (congrArg PIdx.xI e)
      cases t with
      | leaf => simpa [BinTrie.insert, BinTrie.get] using ih .leaf hp
      | node v l r => simpa [BinTrie.insert, BinTrie.get] using ih r hp

theorem BinTrie.erase_leaf {α : Type} (k : PIdx) : (BinTrie.leaf : BinTrie α).erase k = .leaf := by
  cases k <;> rfl

theorem BinTrie.get_erase_of_some {α : Type} (t : BinTrie α) (k₁ k₂ : PIdx) {x : α}
    (h : (t.erase k₁).get k₂ = some x) : t.get k₂ = some x := by
  induction k₁ generalizing t k₂ with
  | xH =>
    cases t with
    | leaf => rw [BinTrie.erase_leaf, BinTrie.get_leaf] at h; nomatch h
    | node v l r =>
      cases k₂ with
      | xH => cases h
      | xO p₂ => exact h
      | xI p₂ => exact h
  | xO p₁ ih =>
    cases t with
    | leaf => rw [BinTrie.erase_leaf, BinTrie.get_leaf] at h; nomatch h
    | node v l r =>
      simp only [BinTrie.erase, trieErase_xO, mkNodeL_eq] at h
      cases k₂ with
      | xH => exact h
      | xO p₂ => exact ih l p₂ h
      | xI p₂ => exact h
  | xI p₁ ih =>
    cases t with
    | leaf => rw [BinTrie.erase_leaf, BinTrie.get_leaf] at h; nomatch h
    | node v l r =>
      simp only [BinTrie.erase, trieErase_xI, mkNodeR_eq] at h
      cases k₂ with
      | xH => exact h
      | xO p₂ => exact h
      | xI p₂ => exact ih r p₂ h

/-- Fast structural equality on `PIdx` via direct `PIdx.rec` (zero `.brecOn`). -/
def PIdx.beq (p : PIdx) : PIdx → Bool :=
  @PIdx.rec (fun _ => PIdx → Bool)
    (fun q => match q with | .xH => true | _ => false)
    (fun _ ih q => match q with | .xO q' => ih q' | _ => false)
    (fun _ ih q => match q with | .xI q' => ih q' | _ => false)
    p

theorem PIdx.beq_iff_eq (p q : PIdx) : PIdx.beq p q = true ↔ p = q := by
  induction p generalizing q with
  | xH =>
    cases q with
    | xH => exact ⟨fun _ => rfl, fun _ => rfl⟩
    | xO _ => exact ⟨fun h => Bool.noConfusion h, fun h => nomatch h⟩
    | xI _ => exact ⟨fun h => Bool.noConfusion h, fun h => nomatch h⟩
  | xO p ih =>
    cases q with
    | xH => exact ⟨fun h => Bool.noConfusion h, fun h => nomatch h⟩
    | xO q => exact (ih q).trans ⟨congrArg PIdx.xO, PIdx.xO.inj⟩
    | xI _ => exact ⟨fun h => Bool.noConfusion h, fun h => nomatch h⟩
  | xI p ih =>
    cases q with
    | xH => exact ⟨fun h => Bool.noConfusion h, fun h => nomatch h⟩
    | xO _ => exact ⟨fun h => Bool.noConfusion h, fun h => nomatch h⟩
    | xI q => exact (ih q).trans ⟨congrArg PIdx.xI, PIdx.xI.inj⟩

def boolBeq : Bool → Bool → Bool
  | true, true => true
  | false, false => true
  | _, _ => false

theorem boolBeq_iff_eq (a b : Bool) : boolBeq a b = true ↔ a = b := by
  cases a <;> cases b <;> simp [boolBeq]

/-- Propositional literal: `(true, v)` asserts `val v = true`, `(false, v)` asserts `val v = false`. -/
abbrev Lit := Bool × PIdx

/-- Fast `Decidable`-free equality check on `Lit`. -/
def litEq (a b : Lit) : Bool :=
  match boolBeq a.1 b.1 with
  | true => PIdx.beq a.2 b.2
  | false => false

theorem litEq_iff_eq (a b : Lit) : litEq a b = true ↔ a = b := by
  rcases a with ⟨a1, a2⟩
  rcases b with ⟨b1, b2⟩
  unfold litEq
  cases hb : boolBeq a1 b1
  · simp only [Bool.false_eq_true, false_iff, Prod.mk.injEq, not_and]
    intro heq
    have := (boolBeq_iff_eq a1 b1).mpr heq
    rw [hb] at this
    exact Bool.noConfusion this
  · simp only [PIdx.beq_iff_eq, Prod.mk.injEq]
    have ha1b1 : a1 = b1 := (boolBeq_iff_eq a1 b1).mp hb
    exact ⟨fun h2 => ⟨ha1b1, h2⟩, fun ⟨_, h2⟩ => h2⟩

/-- Propositional clause: disjunction of literals. -/
abbrev Clause := List Lit

/-- Evaluates a literal under Boolean valuation `val : PIdx → Bool`. -/
def evalLit (val : PIdx → Bool) (l : Lit) : Bool :=
  boolBeq (val l.2) l.1

/-- Evaluates a clause as the disjunction of its literals. -/
def evalClause (val : PIdx → Bool) (cl : Clause) : Bool :=
  cl.any (evalLit val)

/-- Mathematical satisfaction predicate for a `BinTrie Clause` database. -/
def EvalTrieCNF (val : PIdx → Bool) (db : BinTrie Clause) : Prop :=
  ∀ k cl, db.get k = some cl → evalClause val cl = true

theorem evalLit_neg (val : PIdx → Bool) (l : Lit) :
    evalLit val (!l.1, l.2) = !(evalLit val l) := by
  unfold evalLit
  cases val l.2 <;> cases l.1 <;> rfl

/-- Invariant for a falsified-literal map `fmap : BinTrie Bool`:
    if `fmap.get p = some b`, then literal `(b, p)` evaluates to `false` under `val`. -/
def FMapSound (val : PIdx → Bool) (fmap : BinTrie Bool) : Prop :=
  ∀ p b, fmap.get p = some b → evalLit val (b, p) = false

/-- Checks if `l` is recorded as falsified in `fmap` (pure constructor match, zero `Decidable`). -/
def isFalsified (fmap : BinTrie Bool) (l : Lit) : Bool :=
  match fmap.get l.2 with
  | some b => boolBeq b l.1
  | none => false

theorem evalLit_false_of_isFalsified {val : PIdx → Bool} {fmap : BinTrie Bool}
    (hs : FMapSound val fmap) {l : Lit} (hf : isFalsified fmap l = true) :
    evalLit val l = false := by
  unfold isFalsified at hf
  cases hget : fmap.get l.2 with
  | none => rw [hget] at hf; exact Bool.noConfusion hf
  | some b =>
    rw [hget, boolBeq_iff_eq] at hf
    subst hf
    exact hs l.2 l.1 hget

/-- Spine-strict literal record: forces `l.1` and `l.2` to constructor form so no thunks persist. -/
def withStrictLit {β : Type} (l : Lit) (k : Lit → β) : β :=
  match l.1 with
  | true =>
    match strictPIdx l.2 with
    | .xH => k (true, .xH)
    | .xO p => k (true, .xO p)
    | .xI p => k (true, .xI p)
  | false =>
    match strictPIdx l.2 with
    | .xH => k (false, .xH)
    | .xO p => k (false, .xO p)
    | .xI p => k (false, .xI p)

@[simp] theorem withStrictLit_eq {β : Type} (l : Lit) (k : Lit → β) :
    withStrictLit l k = k l := by
  rcases l with ⟨b, p⟩
  unfold withStrictLit
  rw [strictPIdx_eq]
  cases b <;> cases p <;> rfl

/-- Spine-strict `Clause` normalizer via direct `List.rec`: forces every `Lit` and cons cell. -/
def strictClause (cl : Clause) : Clause :=
  @List.rec Lit (fun _ => Clause)
    []
    (fun l _ ih =>
      withStrictLit l (fun l' =>
        match ih with
        | [] => [l']
        | hd :: tl => l' :: hd :: tl))
    cl

@[simp] theorem strictClause_eq (cl : Clause) : strictClause cl = cl := by
  induction cl with
  | nil => rfl
  | cons l ls ih =>
    change withStrictLit l (fun l' => match strictClause ls with | [] => [l'] | hd :: tl => l' :: hd :: tl) = l :: ls
    rw [withStrictLit_eq, ih]
    cases ls <;> rfl

/-- Spine-strict batch erasure on `BinTrie Clause` via direct `List.rec`. -/
def strictEraseList (db : BinTrie Clause) (dels : List PIdx) : BinTrie Clause :=
  @List.rec PIdx (fun _ => BinTrie Clause → BinTrie Clause)
    (fun cur => cur)
    (fun d _ ih cur => withStrictTrie (cur.erase d) ih)
    dels db

@[simp] theorem strictEraseList_eq (db : BinTrie Clause) (dels : List PIdx) :
    strictEraseList db dels = dels.foldl BinTrie.erase db := by
  induction dels generalizing db with
  | nil => rfl
  | cons d ds ih =>
    change withStrictTrie (db.erase d) (fun cur => strictEraseList cur ds) = _
    rw [withStrictTrie_eq, ih]
    rfl

/-- Records literal `l` as falsified in `fmap` (pure constructor match, spine-strict, zero `Decidable`).
    Returns `none` if the opposite literal `(!l.1, l.2)` was already falsified (immediate conflict!). -/
def addFalseLit (fmap : BinTrie Bool) (l : Lit) : Option (BinTrie Bool) :=
  match fmap.get l.2 with
  | none => withStrictTrie (fmap.insert l.2 l.1) some
  | some b =>
    match boolBeq b l.1 with
    | true => some fmap
    | false => none

theorem addFalseLit_none_false {val : PIdx → Bool} {fmap : BinTrie Bool}
    (hs : FMapSound val fmap) {l : Lit} (hl : evalLit val l = false)
    (hnone : addFalseLit fmap l = none) : False := by
  unfold addFalseLit at hnone
  cases hget : fmap.get l.2 with
  | none => simp only [hget, withStrictTrie_eq] at hnone; nomatch hnone
  | some b =>
    simp only [hget] at hnone
    cases hb : boolBeq b l.1
    · have hb_not : b = !l.1 := by
        rcases l with ⟨l1, l2⟩
        dsimp at hb ⊢
        cases b <;> cases l1 <;> first | rfl | exact False.elim (Bool.noConfusion hb)
      have h1 : evalLit val (!l.1, l.2) = false := hb_not ▸ hs l.2 b hget
      rw [evalLit_neg, hl] at h1
      exact Bool.noConfusion h1
    · simp only [hb] at hnone; nomatch hnone

theorem addFalseLit_some_sound {val : PIdx → Bool} {fmap fmap' : BinTrie Bool}
    (hs : FMapSound val fmap) {l : Lit} (hl : evalLit val l = false)
    (hsome : addFalseLit fmap l = some fmap') : FMapSound val fmap' := by
  unfold addFalseLit at hsome
  cases hget : fmap.get l.2 with
  | none =>
    simp only [hget, withStrictTrie_eq] at hsome
    injection hsome with heq
    subst heq
    intro p b hp
    by_cases hpk : l.2 = p
    · subst hpk
      rw [BinTrie.get_insert_self] at hp
      injection hp with hbl
      subst hbl
      exact hl
    · rw [BinTrie.get_insert_ne _ _ hpk] at hp
      exact hs p b hp
  | some b₀ =>
    simp only [hget] at hsome
    cases hb : boolBeq b₀ l.1
    · simp only [hb] at hsome; nomatch hsome
    · simp only [hb] at hsome
      injection hsome with heq
      subst heq
      exact hs

/-- Initializes `fmap` by assuming all literals in `cl` are falsified (direct `List.rec`, zero `.brecOn`).
    Returns `none` if `cl` is tautological (`l` and `!l` both in `cl`). -/
def initFalseLits (fmap : BinTrie Bool) (cl : Clause) : Option (BinTrie Bool) :=
  @List.rec Lit (fun _ => BinTrie Bool → Option (BinTrie Bool))
    (fun cur => some cur)
    (fun l _ ih cur =>
      match addFalseLit cur l with
      | none => none
      | some fmap' => ih fmap')
    cl fmap

theorem initFalseLits_cons (fmap : BinTrie Bool) (l : Lit) (ls : Clause) :
    initFalseLits fmap (l :: ls) =
      (match addFalseLit fmap l with | none => none | some fmap' => initFalseLits fmap' ls) := rfl

theorem initFalseLits_spec {val : PIdx → Bool} :
    ∀ (fmap : BinTrie Bool) (cl : Clause),
      FMapSound val fmap →
      evalClause val cl = false →
      ∃ fmap', initFalseLits fmap cl = some fmap' ∧ FMapSound val fmap'
  | fmap, [], hs, _ => ⟨fmap, rfl, hs⟩
  | fmap, l :: ls, hs, hcl => by
    have hl_false : evalLit val l = false := by
      cases hv : evalLit val l
      · rfl
      · have : evalClause val (l :: ls) = true := List.any_eq_true.mpr ⟨l, List.mem_cons_self, hv⟩
        rw [hcl] at this; exact Bool.noConfusion this
    have hls_false : evalClause val ls = false := by
      cases hv : evalClause val ls
      · rfl
      · obtain ⟨x, hx, hxt⟩ := List.any_eq_true.mp hv
        have : evalClause val (l :: ls) = true :=
          List.any_eq_true.mpr ⟨x, List.mem_cons_of_mem l hx, hxt⟩
        rw [hcl] at this; exact Bool.noConfusion this
    cases hadd : addFalseLit fmap l with
    | none => exact False.elim (addFalseLit_none_false hs hl_false hadd)
    | some fmap₁ =>
      rw [initFalseLits_cons, hadd]
      exact initFalseLits_spec fmap₁ ls (addFalseLit_some_sound hs hl_false hadd) hls_false

/-- Scans a hint clause `cl` against `fmap` via direct `List.rec` (zero `.brecOn`):
    - `some none`: all literals of `cl` are falsified in `fmap` (conflict!);
    - `some (some u)`: unique non-falsified literal `u` (unit propagation!);
    - `none`: non-unit clause (proof error). -/
def scanClause (fmap : BinTrie Bool) (cand : Option Lit) (cl : Clause) : Option (Option Lit) :=
  @List.rec Lit (fun _ => Option Lit → Option (Option Lit))
    (fun c => some c)
    (fun l _ ih c =>
      match isFalsified fmap l with
      | true => ih c
      | false =>
        match c with
        | none => ih (some l)
        | some u =>
          match litEq l u with
          | true => ih (some u)
          | false => none)
    cl cand

theorem scanClause_cons (fmap : BinTrie Bool) (cand : Option Lit) (l : Lit) (ls : Clause) :
    scanClause fmap cand (l :: ls) =
      (match isFalsified fmap l with
       | true => scanClause fmap cand ls
       | false =>
         match cand with
         | none => scanClause fmap (some l) ls
         | some u => match litEq l u with | true => scanClause fmap (some u) ls | false => none) := rfl

theorem scanClause_spec (fmap : BinTrie Bool) :
    ∀ (cand res : Option Lit) (cl : Clause),
      scanClause fmap cand cl = some res →
      match res with
      | none => cand = none ∧ ∀ l ∈ cl, isFalsified fmap l = true
      | some u => (cand = none ∨ cand = some u) ∧ ∀ l ∈ cl, isFalsified fmap l = true ∨ l = u
  | cand, res, [], h => by
    injection h with heq; subst heq
    cases cand with
    | none => exact ⟨rfl, fun _ hm => nomatch hm⟩
    | some u => exact ⟨Or.inr rfl, fun _ hm => nomatch hm⟩
  | cand, res, l :: ls, h => by
    rw [scanClause_cons] at h
    cases hf : isFalsified fmap l
    · cases cand with
      | none =>
        simp only [hf] at h
        have ih := scanClause_spec fmap (some l) res ls h
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
        cases heq_b : litEq l u₀
        · simp only [hf, heq_b] at h
          nomatch h
        · simp only [hf, heq_b] at h
          have hlu₀ : l = u₀ := (litEq_iff_eq l u₀).mp heq_b
          have ih := scanClause_spec fmap (some u₀) res ls h
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
    · simp only [hf] at h
      have ih := scanClause_spec fmap cand res ls h
      cases res with
      | none =>
        refine ⟨ih.1, fun x hx => ?_⟩
        rcases List.mem_cons.mp hx with rfl | hxs
        · exact hf
        · exact ih.2 x hxs
      | some u =>
        refine ⟨ih.1, fun x hx => ?_⟩
        rcases List.mem_cons.mp hx with rfl | hxs
        · exact Or.inl hf
        · exact ih.2 x hxs

/-- Propagates along hint IDs `hints` in `db` via direct `List.rec` (zero `.brecOn`). -/
def rupPropagate (db : BinTrie Clause) (fmap : BinTrie Bool) (hints : List PIdx) : Bool :=
  @List.rec PIdx (fun _ => BinTrie Bool → Bool)
    (fun _ => false)
    (fun hid _ ih cur =>
      match db.get hid with
      | none => false
      | some hcl =>
        match scanClause cur none hcl with
        | none => false
        | some none => true
        | some (some u) =>
          match addFalseLit cur (!u.1, u.2) with
          | none => true
          | some fmap' => ih fmap')
    hints fmap

theorem rupPropagate_cons (db : BinTrie Clause) (fmap : BinTrie Bool) (hid : PIdx) (rest : List PIdx) :
    rupPropagate db fmap (hid :: rest) =
      (match db.get hid with
       | none => false
       | some hcl =>
         match scanClause fmap none hcl with
         | none => false
         | some none => true
         | some (some u) =>
           match addFalseLit fmap (!u.1, u.2) with
           | none => true
           | some fmap' => rupPropagate db fmap' rest) := rfl

theorem rupPropagate_false {val : PIdx → Bool} {db : BinTrie Clause}
    (hdb : EvalTrieCNF val db) :
    ∀ (hints : List PIdx) (fmap : BinTrie Bool),
      FMapSound val fmap → rupPropagate db fmap hints = true → False
  | [], _, _, hrup => Bool.noConfusion hrup
  | hid :: rest, fmap, hs, hrup => by
    rw [rupPropagate_cons] at hrup
    cases hget : db.get hid with
    | none => simp only [hget] at hrup; exact Bool.noConfusion hrup
    | some hcl =>
      simp only [hget] at hrup
      have hcl_true : evalClause val hcl = true := hdb hid hcl hget
      cases hscan : scanClause fmap none hcl with
      | none => simp only [hscan] at hrup; exact Bool.noConfusion hrup
      | some res =>
        simp only [hscan] at hrup
        have hspec := scanClause_spec fmap none res hcl hscan
        obtain ⟨x, hx_mem, hx_true⟩ := List.any_eq_true.mp hcl_true
        cases res with
        | none =>
          have hxf := evalLit_false_of_isFalsified hs (hspec.2 x hx_mem)
          rw [hxf] at hx_true
          exact Bool.noConfusion hx_true
        | some u =>
          have hu_true : evalLit val u = true := by
            rcases hspec.2 x hx_mem with hxf | rfl
            · rw [evalLit_false_of_isFalsified hs hxf] at hx_true
              exact False.elim (Bool.noConfusion hx_true)
            · exact hx_true
          have hnu_false : evalLit val (!u.1, u.2) = false := by
            rw [evalLit_neg, hu_true]; rfl
          cases hadd : addFalseLit fmap (!u.1, u.2) with
          | none => exact addFalseLit_none_false hs hnu_false hadd
          | some fmap' =>
            simp only [hadd] at hrup
            exact rupPropagate_false hdb rest fmap'
              (addFalseLit_some_sound hs hnu_false hadd) hrup

/-- A single RUP step with explicit destination ID `id` and optional dead-clause deletions `dels`. -/
structure RupStep where
  id : PIdx
  cl : Clause
  hints : List PIdx
  dels : List PIdx

/-- Verifies a sequence of RUP steps starting from `db`, succeeding upon deriving the empty clause `[]`. -/
def checkSteps (db : BinTrie Clause) : List RupStep → Bool
  | [] => false
  | step :: rest =>
    let ok :=
      match initFalseLits .leaf step.cl with
      | none => true
      | some fmap => rupPropagate db fmap step.hints
    ok && (step.cl.isEmpty ||
      let db₁ := step.dels.foldl BinTrie.erase db
      checkSteps (db₁.insert step.id step.cl) rest)

theorem evalTrieCNF_foldl_erase {val : PIdx → Bool} :
    ∀ (dels : List PIdx) (db : BinTrie Clause),
      EvalTrieCNF val db → EvalTrieCNF val (dels.foldl BinTrie.erase db)
  | [], _, hdb => hdb
  | d :: ds, db, hdb =>
    evalTrieCNF_foldl_erase ds (db.erase d) (fun k cl h =>
      hdb k cl (BinTrie.get_erase_of_some db d k h))

theorem evalTrieCNF_insert {val : PIdx → Bool} {db : BinTrie Clause}
    (hdb : EvalTrieCNF val db) (id : PIdx) {cl : Clause} (hcl : evalClause val cl = true) :
    EvalTrieCNF val (db.insert id cl) := by
  intro k c hget
  by_cases hik : id = k
  · subst hik
    rw [BinTrie.get_insert_self] at hget
    injection hget with heq; subst heq
    exact hcl
  · rw [BinTrie.get_insert_ne _ _ hik] at hget
    exact hdb k c hget

/-- **Main Soundness Theorem (`checkSteps_sound`)**:
    If `checkSteps db steps = true`, no Boolean valuation `val : PIdx → Bool` satisfies `db`. -/
theorem checkSteps_sound {db : BinTrie Clause} {steps : List RupStep}
    (hcheck : checkSteps db steps = true) {val : PIdx → Bool}
    (hdb : EvalTrieCNF val db) : False := by
  induction steps generalizing db with
  | nil => exact Bool.noConfusion hcheck
  | cons step rest ih =>
    unfold checkSteps at hcheck
    simp only [Bool.and_eq_true, Bool.or_eq_true] at hcheck
    obtain ⟨hok, hemp_or_rest⟩ := hcheck
    have hcl_true : evalClause val step.cl = true := by
      cases hcl : evalClause val step.cl
      · exfalso
        have hleaf : FMapSound val .leaf := fun p _ h => by rw [BinTrie.get_leaf] at h; nomatch h
        obtain ⟨fmap, hinit, hfs⟩ := initFalseLits_spec .leaf step.cl hleaf hcl
        rw [hinit] at hok
        exact rupPropagate_false hdb step.hints fmap hfs hok
      · rfl
    rcases hemp_or_rest with hemp | hrest
    · rw [List.isEmpty_iff.mp hemp] at hcl_true
      exact Bool.noConfusion hcl_true
    · exact ih hrest (evalTrieCNF_insert (evalTrieCNF_foldl_erase step.dels db hdb) step.id hcl_true)

/-! ## Compact ASCII Nibble-Varint Stream Decoder -/

/-- Converts a `Nat` (`n ≥ 1`, using `max n 1`) to `PIdx` by binary bits.
    Actually even faster: we decode `PIdx` directly from bit-chars without `Nat` division! -/
def decodePIdxBits : List Char → Option (PIdx × List Char)
  | 'H' :: rest => some (.xH, rest)
  | 'O' :: cs =>
    match decodePIdxBits cs with
    | some (p, rest) => some (.xO p, rest)
    | none => none
  | 'I' :: cs =>
    match decodePIdxBits cs with
    | some (p, rest) => some (.xI p, rest)
    | none => none
  | _ => none

/-- Decodes a nibble character directly by pattern matching (zero `UInt32.toNat` overhead). -/
def decodeNibbleChar : Char → Option (Bool × Nat)
  | 'A' => some (true, 0)  | 'B' => some (true, 1)  | 'C' => some (true, 2)  | 'D' => some (true, 3)
  | 'E' => some (true, 4)  | 'F' => some (true, 5)  | 'G' => some (true, 6)  | 'H' => some (true, 7)
  | 'I' => some (true, 8)  | 'J' => some (true, 9)  | 'K' => some (true, 10) | 'L' => some (true, 11)
  | 'M' => some (true, 12) | 'N' => some (true, 13) | 'O' => some (true, 14) | 'P' => some (true, 15)
  | 'a' => some (false, 0) | 'b' => some (false, 1) | 'c' => some (false, 2) | 'd' => some (false, 3)
  | 'e' => some (false, 4) | 'f' => some (false, 5) | 'g' => some (false, 6) | 'h' => some (false, 7)
  | 'i' => some (false, 8) | 'j' => some (false, 9) | 'k' => some (false, 10)| 'l' => some (false, 11)
  | 'm' => some (false, 12)| 'n' => some (false, 13)| 'o' => some (false, 14)| 'p' => some (false, 15)
  | _ => none

/-- Decodes a `Nat` encoded in big-endian nibble varint (`'a'..'p'` = continuation `0..15`,
    `'A'..'P'` = terminal `0..15`). -/
def decodeNatAux (acc : Nat) : List Char → Option (Nat × List Char)
  | c :: rest =>
    match decodeNibbleChar c with
    | some (true, nib) => some (acc * 16 + nib, rest)
    | some (false, nib) => decodeNatAux (acc * 16 + nib) rest
    | none => none
  | [] => none

def decodeNat (cs : List Char) : Option (Nat × List Char) :=
  decodeNatAux 0 cs

/-- Decodes `k` signed literals (`'+'`/`'-'` followed by `PIdx` bitstring `'O'/'I'* 'H'`). -/
def decodeLits : Nat → Clause → List Char → Option (Clause × List Char)
  | 0, acc, cs => some (acc.reverse, cs)
  | k + 1, acc, '+' :: cs =>
    match decodePIdxBits cs with
    | some (p, rest) => decodeLits k ((true, p) :: acc) rest
    | none => none
  | k + 1, acc, '-' :: cs =>
    match decodePIdxBits cs with
    | some (p, rest) => decodeLits k ((false, p) :: acc) rest
    | none => none
  | _ + 1, _, _ => none

/-- Decodes `k` `PIdx` keys. -/
def decodePIdxs : Nat → List PIdx → List Char → Option (List PIdx × List Char)
  | 0, acc, cs => some (acc.reverse, cs)
  | k + 1, acc, cs =>
    match decodePIdxBits cs with
    | some (p, rest) => decodePIdxs k (p :: acc) rest
    | none => none

/-- Decodes a list of `RupStep`s from a compact ASCII stream:
    each step is `<id:PIdx> <nLits:Nat> <lits...> <nHints:Nat> <hints...> <nDels:Nat> <dels...>`. -/
def decodeRupStepsAux : Nat → List RupStep → List Char → List RupStep
  | 0, acc, _ => acc.reverse
  | n + 1, acc, cs =>
    match decodePIdxBits cs with
    | none => acc.reverse
    | some (id, cs₁) =>
      match decodeNat cs₁ with
      | none => acc.reverse
      | some (nLits, cs₂) =>
        match decodeLits nLits [] cs₂ with
        | none => acc.reverse
        | some (cl, cs₃) =>
          match decodeNat cs₃ with
          | none => acc.reverse
          | some (nHints, cs₄) =>
            match decodePIdxs nHints [] cs₄ with
            | none => acc.reverse
            | some (hints, cs₅) =>
              match decodeNat cs₅ with
              | none => acc.reverse
              | some (nDels, cs₆) =>
                match decodePIdxs nDels [] cs₆ with
                | none => acc.reverse
                | some (dels, cs₇) =>
                  decodeRupStepsAux n ({ id, cl, hints, dels } :: acc) cs₇

def decodeRupSteps (s : String) : List RupStep :=
  match decodeNat s.toList with
  | none => []
  | some (nSteps, rest) => decodeRupStepsAux nSteps [] rest

/-- End-to-end string-encoded RUP check: decodes `rupStr` and runs `checkSteps db`. -/
def checkEncodedRUP (db : BinTrie Clause) (rupStr : String) : Bool :=
  checkSteps db (decodeRupSteps rupStr)

theorem checkEncodedRUP_sound {db : BinTrie Clause} {rupStr : String}
    (hcheck : checkEncodedRUP db rupStr = true) {val : PIdx → Bool}
    (hdb : EvalTrieCNF val db) : False :=
  checkSteps_sound hcheck hdb

/-! ## Ultra-Fast GMP `ChunkTree` Byte-Stream Decoder & Bounded-Depth RUP Executor -/

/-- Balanced binary tree of 256-bit `Nat` leaves (each leaf packs up to 32 bytes in little-endian base 256).
    Eliminates Lean 4.31 `String`/`ByteArray` $O(N^2)$ `Array.push` unfolding and bounds recursion depth to $O(\log N)$. -/
inductive ChunkTree : Type
  | empty : ChunkTree
  | leaf : Nat → ChunkTree
  | node : ChunkTree → ChunkTree → ChunkTree

/-- Direct `List.rec` reverse-append (`zero .brecOn`, unlike `List.reverseAux`). -/
def fastRev {α : Type} (xs : List α) : List α :=
  @List.rec α (fun _ => List α → List α) (fun acc => acc) (fun x _ ih acc => ih (x :: acc)) xs []

theorem fastRev_eq_reverse {α : Type} (xs : List α) : fastRev xs = xs.reverse := by
  have haux : ∀ (ys acc : List α),
      @List.rec α (fun _ => List α → List α) (fun a => a) (fun x _ ih a => ih (x :: a)) ys acc =
      List.reverseAux ys acc := by
    intro ys
    induction ys with
    | nil => intro acc; rfl
    | cons y ys ih => intro acc; exact ih (y :: acc)
  exact haux xs []

/-- Forces `x : Nat` to WHNF in Lean's C++ kernel via `Nat.casesOn`, binding a fresh `nat_lit`
    with zero `Nat.div`/`Nat.mod`/`HMod` AST history! -/
def withStrictNat {α : Type} (x : Nat) (f : Nat → α) : α :=
  match x with
  | 0 => f 0
  | .succ p => f (Nat.add p 1)

def unpackRevAux (k : Nat) : Nat → List Nat → List Nat :=
  @Nat.rec (fun _ => Nat → List Nat → List Nat)
    (fun _ acc => acc)
    (fun _ ih x acc =>
      withStrictNat (Nat.mod x 256) (fun b =>
        withStrictNat (Nat.div x 256) (fun q =>
          ih q (b :: acc))))
    k

def u32 (x : Nat) : List Nat :=
  fastRev (unpackRevAux 32 x [])

def pullLeftmost (t : ChunkTree) : List ChunkTree → Option (Nat × List ChunkTree) :=
  @ChunkTree.rec (fun _ => List ChunkTree → Option (Nat × List ChunkTree))
    (fun _ => none)
    (fun x stack => some (x, stack))
    (fun _ r ihl _ stack => ihl (r :: stack))
    t

def popChunkStack (st : List ChunkTree) : Option (Nat × List ChunkTree) :=
  @List.rec ChunkTree (fun _ => Option (Nat × List ChunkTree))
    none
    (fun t ts ih =>
      match pullLeftmost t ts with
      | some res => some res
      | none => ih)
    st

/-- Amortized $O(1)$ byte cursor with `cur.length ≤ 32` and `stack.length ≤ 16`. -/
abbrev ByteStream := List Nat × List ChunkTree

def ByteStream.ofTree (t : ChunkTree) : ByteStream :=
  ([], [t])

def ByteStream.next : ByteStream → Option (Nat × ByteStream)
  | (b :: bs, stack) => some (b, (bs, stack))
  | ([], stack) =>
    match popChunkStack stack with
    | none => none
    | some (chunk, stack') =>
      match u32 chunk with
      | [] => none
      | b :: bs => some (b, (bs, stack'))

/-- Big-endian base-128 varint reader (`< 128` terminal, `≥ 128` continuation `b - 128`, direct `Nat.rec`). -/
def bsReadNatAux (fuel : Nat) : Nat → ByteStream → Option (Nat × ByteStream) :=
  @Nat.rec (fun _ => Nat → ByteStream → Option (Nat × ByteStream))
    (fun _ _ => none)
    (fun _ ih acc bs =>
      match bs.next with
      | none => none
      | some (b, bs') =>
        match Nat.ble 128 b with
        | false =>
          withStrictNat (Nat.add (Nat.mul acc 128) b) (fun v => some (v, bs'))
        | true =>
          withStrictNat (Nat.add (Nat.mul acc 128) (Nat.sub b 128)) (fun acc' =>
            ih acc' bs'))
    fuel

def bsReadNat (bs : ByteStream) : Option (Nat × ByteStream) :=
  bsReadNatAux 5 0 bs

def bsReadNats (k : Nat) : List Nat → ByteStream → Option (List Nat × ByteStream) :=
  @Nat.rec (fun _ => List Nat → ByteStream → Option (List Nat × ByteStream))
    (fun acc bs => some (fastRev acc, bs))
    (fun _ ih acc bs =>
      match bsReadNat bs with
      | none => none
      | some (n, bs') => ih (n :: acc) bs')
    k

/-- Fast binary-tree `Nat.ble` 3-bit wrapper (`8 * t + lo` for `0 ≤ lo < 8`, zero `dite`/`Decidable`!). -/
def wrapLow3 (lo : Nat) (t : PIdx) : PIdx :=
  match Nat.ble 4 lo with
  | false =>
    match Nat.ble 2 lo with
    | false =>
      match Nat.ble 1 lo with
      | false => .xO (.xO (.xO t))
      | true  => .xI (.xO (.xO t))
    | true =>
      match Nat.ble 3 lo with
      | false => .xO (.xI (.xO t))
      | true  => .xI (.xI (.xO t))
  | true =>
    match Nat.ble 6 lo with
    | false =>
      match Nat.ble 5 lo with
      | false => .xO (.xO (.xI t))
      | true  => .xI (.xO (.xI t))
    | true =>
      match Nat.ble 7 lo with
      | false => .xO (.xI (.xI t))
      | true  => .xI (.xI (.xI t))

/-- Fast binary-tree `Nat.ble` top-3-bit `PIdx` lookup (`1..7`, zero `dite`/`Decidable`!). -/
def pidxTop3 (b : Nat) : PIdx :=
  match Nat.ble 4 b with
  | false =>
    match Nat.ble 2 b with
    | false => .xH
    | true =>
      match Nat.ble 3 b with
      | false => .xO .xH
      | true  => .xI .xH
  | true =>
    match Nat.ble 6 b with
    | false =>
      match Nat.ble 5 b with
      | false => .xO (.xO .xH)
      | true  => .xI (.xO .xH)
    | true =>
      match Nat.ble 7 b with
      | false => .xO (.xI .xH)
      | true  => .xI (.xI .xH)

/-- Fast `Decidable`-free conversion of `1 ≤ b < 64` to `PIdx`. -/
def pidxTop6 (b : Nat) : PIdx :=
  match Nat.ble 8 b with
  | false => pidxTop3 b
  | true => wrapLow3 (b % 8) (pidxTop3 (b / 8))

/-- Fast `Decidable`-free 6-bit wrapper (`64 * tail + lo` for `0 ≤ lo < 64`). -/
def wrapLow6 (lo : Nat) (tail : PIdx) : PIdx :=
  wrapLow3 (lo % 8) (wrapLow3 (lo / 8) tail)

/-- Little-endian base-64 `PIdx` reader via direct `Nat.rec` (zero `.brecOn`). -/
def bsReadPIdxAux (fuel : Nat) : ByteStream → Option (PIdx × ByteStream) :=
  @Nat.rec (fun _ => ByteStream → Option (PIdx × ByteStream))
    (fun _ => none)
    (fun _ ih bs =>
      match bs.next with
      | none => none
      | some (b, bs') =>
        match Nat.ble 1 b with
        | false => none
        | true =>
          match Nat.ble 64 b with
          | false => some (pidxTop6 b, bs')
          | true =>
            match Nat.ble 128 b with
            | false =>
              match ih bs' with
              | none => none
              | some (tail, bs'') => some (wrapLow6 (b - 64) tail, bs'')
            | true => none)
    fuel

def bsReadPIdx (bs : ByteStream) : Option (PIdx × ByteStream) :=
  bsReadPIdxAux 4 bs

def bsReadPIdxs (k : Nat) : List PIdx → ByteStream → Option (List PIdx × ByteStream) :=
  @Nat.rec (fun _ => List PIdx → ByteStream → Option (List PIdx × ByteStream))
    (fun acc bs => some (fastRev acc, bs))
    (fun _ ih acc bs =>
      match bsReadPIdx bs with
      | none => none
      | some (p, bs') => ih (p :: acc) bs')
    k

/-- Reads a signed literal: bit 7 (`≥ 128`) is polarity, bits `0..6` are the first `PIdx` byte. -/
def bsReadLit (bs : ByteStream) : Option (Lit × ByteStream) :=
  match bs.next with
  | none => none
  | some (raw, bs') =>
    let pol := Nat.ble 128 raw
    let b := match pol with | true => raw - 128 | false => raw
    match Nat.ble 1 b with
    | false => none
    | true =>
      match Nat.ble 64 b with
      | false => some ((pol, pidxTop6 b), bs')
      | true =>
        match Nat.ble 128 b with
        | false =>
          match bsReadPIdxAux 3 bs' with
          | none => none
          | some (tail, bs'') => some ((pol, wrapLow6 (b - 64) tail), bs'')
        | true => none

def bsReadLits (k : Nat) : Clause → ByteStream → Option (Clause × ByteStream) :=
  @Nat.rec (fun _ => Clause → ByteStream → Option (Clause × ByteStream))
    (fun acc bs => some (fastRev acc, bs))
    (fun _ ih acc bs =>
      match bsReadLit bs with
      | none => none
      | some (l, bs') => ih (l :: acc) bs')
    k

/-- Reads and executes a single RUP step directly from `bs` without materializing `List RupStep`.
    Returns `some (true, db, bs')` as soon as the empty clause `[]` is derived! -/
def execOneRupStep (db : BinTrie Clause) (bs : ByteStream) :
    Option (Bool × BinTrie Clause × ByteStream) :=
  match bsReadPIdx bs with
  | none => none
  | some (id, bs1) =>
    match bsReadNat bs1 with
    | none => none
    | some (nLits, bs2) =>
      match bsReadLits nLits [] bs2 with
      | none => none
      | some (cl, bs3) =>
        match bsReadNat bs3 with
        | none => none
        | some (nHints, bs4) =>
          match bsReadPIdxs nHints [] bs4 with
          | none => none
          | some (hints, bs5) =>
            match bsReadNat bs5 with
            | none => none
            | some (nDels, bs6) =>
              match bsReadPIdxs nDels [] bs6 with
              | none => none
              | some (dels, bs7) =>
                let ok :=
                  match initFalseLits .leaf cl with
                  | none => true
                  | some fmap => rupPropagate db fmap hints
                match ok with
                | false => none
                | true =>
                  match cl.isEmpty with
                  | true => some (true, db, bs7)
                  | false =>
                    let cl' := strictClause cl
                    let db₁ := strictEraseList db dels
                    withStrictTrie (db₁.insert (strictPIdx id) cl') (fun db₂ =>
                      some (false, db₂, bs7))

theorem execOneRupStep_sound {db db' : BinTrie Clause} {bs bs' : ByteStream} {done : Bool}
    (hexec : execOneRupStep db bs = some (done, db', bs'))
    {val : PIdx → Bool} (hdb : EvalTrieCNF val db) :
    (done = true → False) ∧ (done = false → EvalTrieCNF val db') := by
  unfold execOneRupStep at hexec
  cases h1 : bsReadPIdx bs with
  | none => simp only [h1] at hexec; nomatch hexec
  | some p1 =>
    rcases p1 with ⟨id, bs1⟩
    simp only [h1] at hexec
    cases h2 : bsReadNat bs1 with
    | none => simp only [h2] at hexec; nomatch hexec
    | some p2 =>
      rcases p2 with ⟨nLits, bs2⟩
      simp only [h2] at hexec
      cases h3 : bsReadLits nLits [] bs2 with
      | none => simp only [h3] at hexec; nomatch hexec
      | some p3 =>
        rcases p3 with ⟨cl, bs3⟩
        simp only [h3] at hexec
        cases h4 : bsReadNat bs3 with
        | none => simp only [h4] at hexec; nomatch hexec
        | some p4 =>
          rcases p4 with ⟨nHints, bs4⟩
          simp only [h4] at hexec
          cases h5 : bsReadPIdxs nHints [] bs4 with
          | none => simp only [h5] at hexec; nomatch hexec
          | some p5 =>
            rcases p5 with ⟨hints, bs5⟩
            simp only [h5] at hexec
            cases h6 : bsReadNat bs5 with
            | none => simp only [h6] at hexec; nomatch hexec
            | some p6 =>
              rcases p6 with ⟨nDels, bs6⟩
              simp only [h6] at hexec
              cases h7 : bsReadPIdxs nDels [] bs6 with
              | none => simp only [h7] at hexec; nomatch hexec
              | some p7 =>
                rcases p7 with ⟨dels, bs7⟩
                simp only [h7, withStrictTrie_eq, strictEraseList_eq, strictClause_eq, strictPIdx_eq] at hexec
                let ok :=
                  match initFalseLits .leaf cl with
                  | none => true
                  | some fmap => rupPropagate db fmap hints
                change (match ok with
                  | false => none
                  | true =>
                    match cl.isEmpty with
                    | true => some (true, db, bs7)
                    | false => some (false, (dels.foldl BinTrie.erase db).insert id cl, bs7)) =
                  some (done, db', bs') at hexec
                cases hok : ok
                · simp only [hok] at hexec; nomatch hexec
                · simp only [hok] at hexec
                  have hcl_true : evalClause val cl = true := by
                    cases hcl : evalClause val cl
                    · exfalso
                      have hleaf : FMapSound val .leaf := fun p _ h => by rw [BinTrie.get_leaf] at h; nomatch h
                      obtain ⟨fmap, hinit, hfs⟩ := initFalseLits_spec .leaf cl hleaf hcl
                      change (match initFalseLits .leaf cl with
                        | none => true
                        | some fmap => rupPropagate db fmap hints) = true at hok
                      rw [hinit] at hok
                      exact rupPropagate_false hdb hints fmap hfs hok
                    · rfl
                  cases hemp : cl.isEmpty
                  · simp only [hemp] at hexec
                    injection hexec with hpair
                    injection hpair with hdone hp2
                    injection hp2 with hdb_eq _
                    subst hdone hdb_eq
                    exact ⟨fun h => Bool.noConfusion h,
                      fun _ => evalTrieCNF_insert (evalTrieCNF_foldl_erase dels db hdb) id hcl_true⟩
                  · simp only [hemp] at hexec
                    injection hexec with hpair
                    injection hpair with hdone _
                    subst hdone
                    rw [List.isEmpty_iff.mp hemp] at hcl_true
                    exact ⟨fun _ => Bool.noConfusion hcl_true, fun h => Bool.noConfusion h⟩

/-- Executes up to `k` RUP steps via direct `Nat.rec` (zero `.brecOn`). -/
def execRupBatch (k : Nat) : BinTrie Clause → ByteStream →
    Option (Bool × BinTrie Clause × ByteStream) :=
  @Nat.rec (fun _ => BinTrie Clause → ByteStream → Option (Bool × BinTrie Clause × ByteStream))
    (fun db bs => some (false, db, bs))
    (fun _ ih db bs =>
      match execOneRupStep db bs with
      | none => none
      | some (true, db', bs') => some (true, db', bs')
      | some (false, db', bs') => ih db' bs')
    k

theorem execRupBatch_sound :
    ∀ (k : Nat) {db db' : BinTrie Clause} {bs bs' : ByteStream} {done : Bool},
      execRupBatch k db bs = some (done, db', bs') →
      ∀ {val : PIdx → Bool}, EvalTrieCNF val db →
        (done = true → False) ∧ (done = false → EvalTrieCNF val db')
  | 0, db, db', bs, bs', done, h, _, hdb => by
    injection h with hp
    injection hp with hd hp2
    injection hp2 with hdb' _
    subst hd hdb'
    exact ⟨fun hc => Bool.noConfusion hc, fun _ => hdb⟩
  | k + 1, db, db', bs, bs', done, h, val, hdb => by
    change (match execOneRupStep db bs with
      | none => none
      | some (true, db', bs') => some (true, db', bs')
      | some (false, db', bs') => execRupBatch k db' bs') = some (done, db', bs') at h
    cases hex : execOneRupStep db bs with
    | none => simp only [hex] at h; nomatch h
    | some res =>
      rcases res with ⟨d1, db1, bs1⟩
      simp only [hex] at h
      have hs1 := execOneRupStep_sound hex hdb
      cases d1
      · exact execRupBatch_sound k h (hs1.2 rfl)
      · injection h with hp
        injection hp with hd _
        subst hd
        exact ⟨fun _ => hs1.1 rfl, fun hc => Bool.noConfusion hc⟩

/-- Chains `k` calls to a block step `f` via direct `Nat.rec` (zero `.brecOn`). -/
def chainRupBlocks (f : BinTrie Clause → ByteStream → Option (Bool × BinTrie Clause × ByteStream))
    (k : Nat) : BinTrie Clause → ByteStream → Option (Bool × BinTrie Clause × ByteStream) :=
  @Nat.rec (fun _ => BinTrie Clause → ByteStream → Option (Bool × BinTrie Clause × ByteStream))
    (fun db bs => some (false, db, bs))
    (fun _ ih db bs =>
      match f db bs with
      | none => none
      | some (true, db', bs') => some (true, db', bs')
      | some (false, db', bs') => ih db' bs')
    k

theorem chainRupBlocks_sound
    {f : BinTrie Clause → ByteStream → Option (Bool × BinTrie Clause × ByteStream)}
    (hf : ∀ {db db' bs bs' done}, f db bs = some (done, db', bs') →
      ∀ {val}, EvalTrieCNF val db → (done = true → False) ∧ (done = false → EvalTrieCNF val db')) :
    ∀ (k : Nat) {db db' : BinTrie Clause} {bs bs' : ByteStream} {done : Bool},
      chainRupBlocks f k db bs = some (done, db', bs') →
      ∀ {val : PIdx → Bool}, EvalTrieCNF val db →
        (done = true → False) ∧ (done = false → EvalTrieCNF val db')
  | 0, _, _, _, _, _, h, _, hdb => by
    injection h with hp
    injection hp with hd hp2
    injection hp2 with hdb' _
    subst hd hdb'
    exact ⟨fun hc => Bool.noConfusion hc, fun _ => hdb⟩
  | k + 1, db, _, bs, _, _, h, _, hdb => by
    change (match f db bs with
      | none => none
      | some (true, db', bs') => some (true, db', bs')
      | some (false, db', bs') => chainRupBlocks f k db' bs') = _ at h
    cases hex : f db bs with
    | none => simp only [hex] at h; nomatch h
    | some res =>
      rcases res with ⟨d1, db1, bs1⟩
      simp only [hex] at h
      have hs1 := hf hex hdb
      cases d1
      · exact chainRupBlocks_sound hf k h (hs1.2 rfl)
      · injection h with hp
        injection hp with hd _
        subst hd
        exact ⟨fun _ => hs1.1 rfl, fun hc => Bool.noConfusion hc⟩

/-- Hierarchical 16-ary RUP tower via direct `Nat.rec` (zero `.brecOn`). -/
def execRupTower (lvl : Nat) : BinTrie Clause → ByteStream →
    Option (Bool × BinTrie Clause × ByteStream) :=
  @Nat.rec (fun _ => BinTrie Clause → ByteStream → Option (Bool × BinTrie Clause × ByteStream))
    (execRupBatch 16)
    (fun _ ih => chainRupBlocks ih 16)
    lvl

theorem execRupTower_sound :
    ∀ (lvl : Nat) {db db' : BinTrie Clause} {bs bs' : ByteStream} {done : Bool},
      execRupTower lvl db bs = some (done, db', bs') →
      ∀ {val : PIdx → Bool}, EvalTrieCNF val db →
        (done = true → False) ∧ (done = false → EvalTrieCNF val db')
  | 0, _, _, _, _, _, h, _, hdb => execRupBatch_sound 16 h hdb
  | lvl + 1, _, _, _, _, _, h, _, hdb => by
    change chainRupBlocks (execRupTower lvl) 16 _ _ = _ at h
    exact chainRupBlocks_sound (execRupTower_sound lvl) 16 h hdb

/-- Verifies a `ChunkTree`-encoded RUP proof of up to `16^5 = 1,048,576` steps with stack depth `≤ 80`. -/
def checkTreeRUP (db : BinTrie Clause) (rupTree : ChunkTree) : Bool :=
  match execRupTower 4 db (ByteStream.ofTree rupTree) with
  | some (true, _, _) => true
  | _ => false

theorem checkTreeRUP_sound {db : BinTrie Clause} {rupTree : ChunkTree}
    (hcheck : checkTreeRUP db rupTree = true) {val : PIdx → Bool}
    (hdb : EvalTrieCNF val db) : False := by
  unfold checkTreeRUP at hcheck
  cases hex : execRupTower 4 db (ByteStream.ofTree rupTree) with
  | none => rw [hex] at hcheck; exact Bool.noConfusion hcheck
  | some res =>
    rcases res with ⟨done, db', bs'⟩
    rw [hex] at hcheck
    cases done
    · exact Bool.noConfusion hcheck
    · exact (execRupTower_sound 4 hex hdb).1 rfl

end

end VCDim6.FastTrieRUP
