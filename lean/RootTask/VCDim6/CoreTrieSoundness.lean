import Mathlib
import RootTask.PolygonDefs
import RootTask.PolygonEnclosureCore
import RootTask.NewEnclosureLemmas
import RootTask.ChirotopeSoundness
import RootTask.VCDim6.CaseCertFormat

open scoped Classical BigOperators
open Finset
open PolygonCore NewEnclosure ChirotopeSoundness VCDim6.FastTrieRUP

noncomputable section

namespace VCDim6

/-!
# Soundness of `TripleTrie`, `maskTrie`, Literal Encodings, and `IteratedCut` Mini-DAGs

Proves the data-structure and mini-DAG soundness lemmas underlying `checkCaseCert`:
1. `PIdx.toPosNat` & injectivity of `ptKey` up to `511` (and lower bound `≥ 512` above `511`).
2. `ValidMasks` (`validMasksBool`), `maskToFinset`, `specWitnessEmb`, and `getMask_sound`.
3. `buildTripleTrieTree_sound`: constructs the exact chirotope Boolean valuation `val : PIdx → Bool`
   matching `orientSign` on `pointSeq S w W₀`, together with `litSign_sound`, `litForb_false_iff`,
   `inTriPairLits_sound`, and `notInTriSideLits_false_iff`.
4. `decodeIteratedSteps_sound`: proves soundness of `(E1)` two-sided path and `(E2)` triangle
   enclosure mini-DAGs (`Tag 19`) directly from `hP.two_path_enclosure` and `hP.triangle_enclosure`.
-/

/-! ## 1. `PIdx.toPosNat` and Exact `ptKey` Arithmetic -/

namespace FastTrieRUP

/-- Positive natural number value of a `PIdx` (`xH ↦ 1`, `xO p ↦ 2p`, `xI p ↦ 2p + 1`). -/
def PIdx.toPosNat : PIdx → ℕ
  | .xH => 1
  | .xO p => 2 * p.toPosNat
  | .xI p => 2 * p.toPosNat + 1

theorem PIdx.toPosNat_pos (p : PIdx) : 1 ≤ p.toPosNat := by
  induction p with
  | xH => decide
  | xO p ih => dsimp [PIdx.toPosNat]; omega
  | xI p ih => dsimp [PIdx.toPosNat]; omega

theorem PIdx.toPosNat_succ (p : PIdx) : p.succ.toPosNat = p.toPosNat + 1 := by
  induction p with
  | xH => rfl
  | xO p _ => rfl
  | xI p ih =>
    change (mkXO p.succ).toPosNat = 2 * p.toPosNat + 1 + 1
    rw [mkXO_eq]
    dsimp [PIdx.toPosNat]
    omega

theorem PIdx.toPosNat_inj : Function.Injective PIdx.toPosNat := by
  intro p₁
  induction p₁ with
  | xH =>
    intro p₂ h
    cases p₂ with
    | xH => rfl
    | xO q => dsimp [PIdx.toPosNat] at h; have := q.toPosNat_pos; omega
    | xI q => dsimp [PIdx.toPosNat] at h; have := q.toPosNat_pos; omega
  | xO p₁ ih =>
    intro p₂ h
    cases p₂ with
    | xH => dsimp [PIdx.toPosNat] at h; have := p₁.toPosNat_pos; omega
    | xO q => dsimp [PIdx.toPosNat] at h; exact congrArg PIdx.xO (ih (by omega))
    | xI q => dsimp [PIdx.toPosNat] at h; omega
  | xI p₁ ih =>
    intro p₂ h
    cases p₂ with
    | xH => dsimp [PIdx.toPosNat] at h; have := p₁.toPosNat_pos; omega
    | xO q => dsimp [PIdx.toPosNat] at h; omega
    | xI q => dsimp [PIdx.toPosNat] at h; exact congrArg PIdx.xI (ih (by omega))

end FastTrieRUP

theorem wrapLow3_toPosNat (lo : ℕ) (hlo : lo < 8) (t : PIdx) :
    (wrapLow3 lo t).toPosNat = 8 * t.toPosNat + lo := by
  have hc : lo = 0 ∨ lo = 1 ∨ lo = 2 ∨ lo = 3 ∨ lo = 4 ∨ lo = 5 ∨ lo = 6 ∨ lo = 7 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    (dsimp [wrapLow3, PIdx.toPosNat]; omega)

theorem wrapLow3_toPosNat_ge (lo : ℕ) (t : PIdx) :
    8 * t.toPosNat ≤ (wrapLow3 lo t).toPosNat := by
  unfold wrapLow3
  cases Nat.ble 4 lo <;> cases Nat.ble 2 lo <;> cases Nat.ble 1 lo <;>
    cases Nat.ble 3 lo <;> cases Nat.ble 6 lo <;> cases Nat.ble 5 lo <;>
    cases Nat.ble 7 lo <;> (dsimp [PIdx.toPosNat]; omega)

theorem pidxTop3_toPosNat (b : ℕ) (hb1 : 1 ≤ b) (hb8 : b < 8) :
    (pidxTop3 b).toPosNat = b := by
  have hc : b = 1 ∨ b = 2 ∨ b = 3 ∨ b = 4 ∨ b = 5 ∨ b = 6 ∨ b = 7 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

private lemma nat_ble_false_lt {a b : ℕ} (h : Nat.ble a b = false) : b < a := by
  by_contra hge
  have hle : a ≤ b := Nat.le_of_not_lt hge
  have ht : Nat.ble a b = true := Nat.ble_eq.mpr hle
  rw [h] at ht; exact Bool.noConfusion ht

private lemma nat_ble_true_le {a b : ℕ} (h : Nat.ble a b = true) : a ≤ b :=
  Nat.ble_eq.mp h

theorem pidxTop6_toPosNat (b : ℕ) (hb1 : 1 ≤ b) (hb64 : b < 64) :
    (pidxTop6 b).toPosNat = b := by
  unfold pidxTop6
  cases h8 : Nat.ble 8 b
  · exact pidxTop3_toPosNat b hb1 (nat_ble_false_lt h8)
  · have hge8 := nat_ble_true_le h8
    rw [wrapLow3_toPosNat (b % 8) (by omega), pidxTop3_toPosNat (b / 8) (by omega) (by omega)]
    omega

theorem pidxTop6_toPosNat_ge8 {b : ℕ} (hb : 8 ≤ b) : 8 ≤ (pidxTop6 b).toPosNat := by
  unfold pidxTop6
  have ht : Nat.ble 8 b = true := Nat.ble_eq.mpr hb
  rw [ht]
  dsimp only
  have hpos := PIdx.toPosNat_pos (pidxTop3 (b / 8))
  have hge := wrapLow3_toPosNat_ge (b % 8) (pidxTop3 (b / 8))
  omega

theorem wrapLow6_toPosNat (lo : ℕ) (hlo : lo < 64) (t : PIdx) :
    (wrapLow6 lo t).toPosNat = 64 * t.toPosNat + lo := by
  unfold wrapLow6
  rw [wrapLow3_toPosNat (lo % 8) (by omega), wrapLow3_toPosNat (lo / 8) (by omega)]
  omega

theorem wrapLow6_toPosNat_ge (lo : ℕ) (t : PIdx) :
    64 * t.toPosNat ≤ (wrapLow6 lo t).toPosNat := by
  unfold wrapLow6
  have h1 := wrapLow3_toPosNat_ge (lo / 8) t
  have h2 := wrapLow3_toPosNat_ge (lo % 8) (wrapLow3 (lo / 8) t)
  omega

theorem ptKey_toPosNat {u : ℕ} (hu : u < 511) : (ptKey u).toPosNat = u + 1 := by
  unfold ptKey
  dsimp only
  cases h64 : Nat.ble 64 (u + 1)
  · exact pidxTop6_toPosNat (u + 1) (by omega) (nat_ble_false_lt h64)
  · have hge := nat_ble_true_le h64
    rw [wrapLow6_toPosNat ((u + 1) % 64) (by omega),
        pidxTop6_toPosNat ((u + 1) / 64) (by omega) (by omega)]
    omega

theorem ptKey_toPosNat_ge512 {u : ℕ} (hu : 511 ≤ u) : 512 ≤ (ptKey u).toPosNat := by
  unfold ptKey
  dsimp only
  have ht : Nat.ble 64 (u + 1) = true := Nat.ble_eq.mpr (by omega)
  rw [ht]
  dsimp only
  have h8 : 8 ≤ (pidxTop6 ((u + 1) / 64)).toPosNat := pidxTop6_toPosNat_ge8 (by omega)
  have h64 := wrapLow6_toPosNat_ge ((u + 1) % 64) (pidxTop6 ((u + 1) / 64))
  omega

theorem ptKey_inj_lt511 {u v : ℕ} (hu : u < 511) (hv : v < 511) (h : ptKey u = ptKey v) :
    u = v := by
  have := congrArg PIdx.toPosNat h
  rw [ptKey_toPosNat hu, ptKey_toPosNat hv] at this
  omega

/-! ## 2. `ValidMasks`, `maskToFinset`, and `getMask_sound` -/

/-- Decidable check that `masks` has length `≤ 200`, entries `< 128`, and no duplicates. -/
def validMasksAux : List ℕ → Bool
  | [] => true
  | m :: ms => Nat.ble (m + 1) 128 && !(ms.contains m) && validMasksAux ms

def validMasksBool (masks : List ℕ) : Bool :=
  Nat.ble masks.length 200 && validMasksAux masks

/-- Propositional counterpart of `validMasksBool`. -/
def ValidMasks (masks : List ℕ) : Prop :=
  masks.length ≤ 200 ∧ (∀ m ∈ masks, m < 128) ∧ masks.Nodup

private lemma validMasksAux_sound :
    ∀ masks : List ℕ, validMasksAux masks = true → (∀ m ∈ masks, m < 128) ∧ masks.Nodup
  | [], _ => by simp
  | m :: ms, h => by
    unfold validMasksAux at h
    cases hm_lt : Nat.ble (m + 1) 128
    · rw [hm_lt] at h; nomatch h
    · cases hcon : ms.contains m
      · rw [hm_lt, hcon] at h
        have hm128 : m < 128 := by have := nat_ble_true_le hm_lt; omega
        have hm_not : m ∉ ms := by
          intro hmem
          have hc : ms.contains m = true := List.contains_iff_mem.mpr hmem
          rw [hcon] at hc; exact Bool.noConfusion hc
        obtain ⟨hall, hnd⟩ := validMasksAux_sound ms h
        refine ⟨fun x hx => ?_, List.nodup_cons.mpr ⟨hm_not, hnd⟩⟩
        rcases List.mem_cons.mp hx with rfl | hms
        · exact hm128
        · exact hall x hms
      · rw [hm_lt, hcon] at h; nomatch h

theorem validMasks_of_bool {masks : List ℕ} (h : validMasksBool masks = true) :
    ValidMasks masks := by
  unfold validMasksBool at h
  simp only [Bool.and_eq_true] at h
  exact ⟨nat_ble_true_le h.1, (validMasksAux_sound masks h.2).1, (validMasksAux_sound masks h.2).2⟩

/-- 7-bit mask decoded as a `Finset (Fin 7)`. -/
def maskToFinset (m : ℕ) : Finset (Fin 7) :=
  Finset.univ.filter (fun s => seesBit m s.val = true)

@[simp] theorem mem_maskToFinset_iff (m : ℕ) (s : Fin 7) :
    s ∈ maskToFinset m ↔ seesBit m s.val = true := by
  simp [maskToFinset]

theorem pow2Small_eq {s : ℕ} (hs : s < 7) : pow2Small s = 2 ^ s := by
  have hc : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 ∨ s = 6 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem seesBit_iff_mod {m s : ℕ} (hs : s < 7) :
    seesBit m s = true ↔ (m / 2 ^ s) % 2 = 1 := by
  unfold seesBit
  rw [pow2Small_eq hs, Nat.beq_eq]

private lemma mod2_eq_of_iff {x y : ℕ} (h : x % 2 = 1 ↔ y % 2 = 1) : x % 2 = y % 2 := by
  omega

private lemma nat_eq_of_mod_div {x y : ℕ} (hm : x % 2 = y % 2) (hd : x / 2 = y / 2) : x = y := by
  omega

theorem maskToFinset_inj {m₁ m₂ : ℕ} (h1 : m₁ < 128) (h2 : m₂ < 128)
    (heq : maskToFinset m₁ = maskToFinset m₂) : m₁ = m₂ := by
  have hbit : ∀ (s : ℕ) (hs : s < 7), (m₁ / 2 ^ s) % 2 = 1 ↔ (m₂ / 2 ^ s) % 2 = 1 := by
    intro s hs
    have hmem := Finset.ext_iff.mp heq ⟨s, hs⟩
    simpa [mem_maskToFinset_iff, seesBit_iff_mod hs] using hmem
  have e0 : m₁ % 2 = m₂ % 2 := mod2_eq_of_iff (by simpa using hbit 0 (by decide))
  have e1 : (m₁ / 2) % 2 = (m₂ / 2) % 2 := mod2_eq_of_iff (hbit 1 (by decide))
  have e2 : (m₁ / 4) % 2 = (m₂ / 4) % 2 := mod2_eq_of_iff (hbit 2 (by decide))
  have e3 : (m₁ / 8) % 2 = (m₂ / 8) % 2 := mod2_eq_of_iff (hbit 3 (by decide))
  have e4 : (m₁ / 16) % 2 = (m₂ / 16) % 2 := mod2_eq_of_iff (hbit 4 (by decide))
  have e5 : (m₁ / 32) % 2 = (m₂ / 32) % 2 := mod2_eq_of_iff (hbit 5 (by decide))
  have e6 : (m₁ / 64) % 2 = (m₂ / 64) % 2 := mod2_eq_of_iff (hbit 6 (by decide))
  have d6 : m₁ / 64 = m₂ / 64 := by omega
  have d5 : m₁ / 32 = m₂ / 32 := nat_eq_of_mod_div e5 (by rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul]; exact d6)
  have d4 : m₁ / 16 = m₂ / 16 := nat_eq_of_mod_div e4 (by rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul]; exact d5)
  have d3 : m₁ / 8 = m₂ / 8 := nat_eq_of_mod_div e3 (by rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul]; exact d4)
  have d2 : m₁ / 4 = m₂ / 4 := nat_eq_of_mod_div e2 (by rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul]; exact d3)
  have d1 : m₁ / 2 = m₂ / 2 := nat_eq_of_mod_div e1 (by rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul]; exact d2)
  exact nat_eq_of_mod_div e0 d1

/-- Embedding `Fin masks.length ↪ Finset (Fin 7)` induced by `ValidMasks masks`. -/
def specWitnessEmb {masks : List ℕ} (hM : ValidMasks masks) :
    Fin masks.length ↪ Finset (Fin 7) where
  toFun j := maskToFinset (masks[j.val]'j.isLt)
  inj' i j hij := by
    have hi_lt : masks[i.val]'i.isLt < 128 := hM.2.1 _ (List.getElem_mem _)
    have hj_lt : masks[j.val]'j.isLt < 128 := hM.2.1 _ (List.getElem_mem _)
    have hm_eq := maskToFinset_inj hi_lt hj_lt hij
    exact Fin.ext ((List.Nodup.getElem_inj_iff hM.2.2).mp hm_eq)

private lemma seesBit_zh_fin : ∀ (h s : Fin 7),
    (seesBit (127 - pow2Small h.val) s.val = true) ↔ s ≠ h := by
  decide

/-- `zm = 127 - 2^h` (`h < 7`) decodes to `Finset.univ.erase ⟨h, hh⟩`, so `w (maskToFinset zm) = zWitness w h`. -/
theorem maskToFinset_zh_eq_erase {h : ℕ} (hh : h < 7) :
    maskToFinset (127 - pow2Small h) = Finset.univ.erase ⟨h, hh⟩ := by
  ext s
  simp only [mem_maskToFinset_iff, Finset.mem_erase, Finset.mem_univ, and_true]
  exact seesBit_zh_fin ⟨h, hh⟩ s

private lemma buildMaskTrieAux_sound (full : List ℕ) (hlen : full.length ≤ 200) :
    ∀ (rem : List ℕ) (off : ℕ) (cur : PIdx) (acc : BinTrie ℕ)
      (hoff : off + rem.length = full.length),
      (∀ idx (hidx : idx < rem.length), rem[idx] = full[off + idx]'(by omega)) →
      cur.toPosNat = off + 1 →
      (∀ k v, acc.get k = some v → ∃ idx : ℕ, ∃ h : idx < off,
        k = ptKey idx ∧ full[idx]'(by omega) = v) →
      ∀ k v, (buildMaskTrieAux cur rem acc).get k = some v →
        ∃ idx : ℕ, ∃ h : idx < full.length, k = ptKey idx ∧ full[idx]'h = v
  | [], off, _, acc, hoff, _, _, hacc, k, v, hget => by
    obtain ⟨idx, hidx, hk, hv⟩ := hacc k v hget
    exact ⟨idx, by omega, hk, hv⟩
  | m :: ms, off, cur, acc, hoff, hrem, hcur, hacc, k, v, hget => by
    unfold buildMaskTrieAux at hget
    refine buildMaskTrieAux_sound full hlen ms (off + 1) cur.succ (acc.insert cur m)
      (by dsimp at hoff; omega)
      (fun idx hidx => by
        have := hrem (idx + 1) (by dsimp; omega)
        simpa [Nat.add_assoc, Nat.add_comm 1 idx] using this)
      (by rw [PIdx.toPosNat_succ, hcur])
      (fun k' v' hk' => ?_) k v hget
    have hcur_key : cur = ptKey off :=
      PIdx.toPosNat_inj (by rw [hcur, ptKey_toPosNat (by dsimp at hoff; omega)])
    by_cases heq : cur = k'
    · subst heq
      rw [BinTrie.get_insert_self] at hk'
      injection hk' with hmv; subst hmv
      have hm0 := hrem 0 (by simp)
      simp only [Nat.add_zero] at hm0
      exact ⟨off, by omega, hcur_key, hm0.symm⟩
    · rw [BinTrie.get_insert_ne _ _ heq] at hk'
      obtain ⟨idx, hidx, hk_eq, hv_eq⟩ := hacc k' v' hk'
      exact ⟨idx, by omega, hk_eq, hv_eq⟩

theorem getMask_sound {ctx : CertCtx} (hM : ValidMasks ctx.spec.masks)
    (hm_eq : ctx.maskTrie = buildMaskTrieAux .xH ctx.spec.masks .leaf)
    {wIdx m : ℕ} (hget : getMask ctx wIdx = some m) :
    ∃ hw : wIdx < ctx.spec.masks.length, ctx.spec.masks[wIdx]'hw = m := by
  unfold getMask at hget
  rw [hm_eq] at hget
  have hlen200 : ctx.spec.masks.length ≤ 200 := hM.1
  obtain ⟨idx, hidx, hk_eq, hv_eq⟩ := buildMaskTrieAux_sound ctx.spec.masks hlen200
    ctx.spec.masks 0 .xH .leaf (by simp) (fun _ _ => by simp) rfl
    (fun k _ hk => by rw [BinTrie.get_leaf] at hk; nomatch hk)
    (ptKey wIdx) m hget
  have hw_lt511 : wIdx < 511 := by
    by_contra hge
    have hge512 := ptKey_toPosNat_ge512 (Nat.le_of_not_lt hge)
    have hidx_pos := ptKey_toPosNat (by omega : idx < 511)
    have hpos_eq := congrArg PIdx.toPosNat hk_eq
    omega
  have heq_idx : wIdx = idx := ptKey_inj_lt511 hw_lt511 (by omega) hk_eq
  subst heq_idx
  exact ⟨hidx, hv_eq⟩

/-! ## 3. `TripleTrie` Valuation Soundness & Chirotope Literal Lemmas -/

theorem TripleTrie.get3_insert3_self (t : TripleTrie) (ki kj kk v : PIdx) :
    (t.insert3 ki kj kk v).get3 ki kj kk = some v := by
  simp only [TripleTrie.insert3, TripleTrie.get3, withStrictTrie_eq, strictPIdx_eq]
  rw [BinTrie.get_insert_self]
  dsimp only
  rw [BinTrie.get_insert_self]
  dsimp only
  rw [BinTrie.get_insert_self]

theorem TripleTrie.get3_insert3_ne (t : TripleTrie) {ki kj kk qi qj qk : PIdx} (v : PIdx)
    (hne : (ki, kj, kk) ≠ (qi, qj, qk)) :
    (t.insert3 ki kj kk v).get3 qi qj qk = t.get3 qi qj qk := by
  simp only [TripleTrie.insert3, TripleTrie.get3, withStrictTrie_eq, strictPIdx_eq]
  by_cases hi : ki = qi
  · subst hi
    rw [BinTrie.get_insert_self]
    dsimp only
    by_cases hj : kj = qj
    · subst hj
      rw [BinTrie.get_insert_self]
      dsimp only
      have hk : kk ≠ qk := fun hk => hne (by subst hk; rfl)
      cases ht1 : t.get ki with
      | none =>
        simp only [BinTrie.get_leaf]
        rw [BinTrie.get_insert_ne _ _ hk, BinTrie.get_leaf]
      | some m1 =>
        dsimp only
        cases ht2 : m1.get kj with
        | none => dsimp only; rw [BinTrie.get_insert_ne _ _ hk, BinTrie.get_leaf]
        | some m2 => dsimp only; rw [BinTrie.get_insert_ne _ _ hk]
    · rw [BinTrie.get_insert_ne _ _ hj]
      cases ht1 : t.get ki with
      | none => dsimp only; rw [BinTrie.get_leaf]
      | some m1 => rfl
  · rw [BinTrie.get_insert_ne _ _ hi]

/-- Invariant for `TripleTrie`: there exists a Boolean valuation `val` agreeing with `orientSign`
    on `X` at all registered sorted triples `(i, j, k)`, with all registered variable keys `< curVar`. -/
def TripleTrieSound {N : ℕ} (X : Fin N → ℝ × ℝ) (curVar : PIdx) (acc : TripleTrie) : Prop :=
  ∃ val : PIdx → Bool,
    ∀ {i j k : ℕ} (hij : i < j) (hjk : j < k) (hk : k < N) {v : PIdx},
      acc.get3 (ptKey i) (ptKey j) (ptKey k) = some v →
      v.toPosNat < curVar.toPosNat ∧
      val v = orientSign (X ⟨i, by omega⟩) (X ⟨j, by omega⟩) (X ⟨k, hk⟩)

private lemma stepTriple_sound {N : ℕ} (hN : N ≤ 511) (X : Fin N → ℝ × ℝ)
    {cv cv' : PIdx} {acc acc' : TripleTrie} {bs bs' : ByteStream} {done : Bool}
    (hstep : stepTriple N cv acc bs = some (done, cv', acc', bs'))
    (hs : TripleTrieSound X cv acc) :
    TripleTrieSound X cv' acc' := by
  unfold stepTriple at hstep
  cases h1 : bs.next with
  | none => simp only [h1] at hstep; nomatch hstep
  | some p1 =>
    rcases p1 with ⟨i, bs1⟩
    simp only [h1] at hstep
    cases hi255 : Nat.beq i 255
    · simp only [hi255] at hstep
      cases h2 : bs1.next with
      | none => simp only [h2] at hstep; nomatch hstep
      | some p2 =>
        rcases p2 with ⟨j, bs2⟩
        simp only [h2] at hstep
        cases h3 : bs2.next with
        | none => simp only [h3] at hstep; nomatch hstep
        | some p3 =>
          rcases p3 with ⟨k, bs3⟩
          simp only [h3] at hstep
          cases hchk : (Nat.ble j i || Nat.ble k j || Nat.ble N k)
          · simp only [hchk, withStrictTrie_eq] at hstep
            have h_or : Nat.ble j i = false ∧ Nat.ble k j = false ∧ Nat.ble N k = false := by
              revert hchk; cases Nat.ble j i <;> cases Nat.ble k j <;> cases Nat.ble N k <;> decide
            have hij : i < j := nat_ble_false_lt h_or.1
            have hjk : j < k := nat_ble_false_lt h_or.2.1
            have hkN : k < N := nat_ble_false_lt h_or.2.2
            have hcv_eq : cv' = cv.succ ∧ acc' = acc.insert3 (ptKey i) (ptKey j) (ptKey k) cv := by
              have hsp := strictPIdx_eq cv.succ
              cases hs_p : strictPIdx cv.succ <;> simp only [hs_p] at hstep hsp <;>
                injection hstep with hp <;> injection hp with _ hp2 <;>
                injection hp2 with hcv' hp3 <;> injection hp3 with hacc' _ <;>
                exact ⟨hcv'.symm.trans hsp, hacc'.symm⟩
            rcases hcv_eq with ⟨rfl, rfl⟩
            obtain ⟨val, hval⟩ := hs
            let targetSign := orientSign (X ⟨i, by omega⟩) (X ⟨j, by omega⟩) (X ⟨k, hkN⟩)
            refine ⟨fun u => if u = cv then targetSign else val u, ?_⟩
            intro qi qj qk hqij hqjk hqk v hget
            by_cases htri : (i, j, k) = (qi, qj, qk)
            · injection htri with e1 e2; injection e2 with e2 e3; subst e1 e2 e3
              rw [TripleTrie.get3_insert3_self] at hget
              injection hget with hv; subst hv
              simp only [↓reduceIte, PIdx.toPosNat_succ]
              exact ⟨by omega, rfl⟩
            · have hne_keys : (ptKey i, ptKey j, ptKey k) ≠ (ptKey qi, ptKey qj, ptKey qk) := by
                intro heq
                injection heq with k1 k2; injection k2 with k2 k3
                have hi1 : i = qi := ptKey_inj_lt511 (by omega) (by omega) k1
                have hj1 : j = qj := ptKey_inj_lt511 (by omega) (by omega) k2
                have hk1 : k = qk := ptKey_inj_lt511 (by omega) (by omega) k3
                subst hi1 hj1 hk1
                exact htri rfl
              rw [TripleTrie.get3_insert3_ne _ _ hne_keys] at hget
              obtain ⟨hv_lt, hv_eq⟩ := hval hqij hqjk hqk hget
              have hv_ne : v ≠ cv := fun e => by subst e; omega
              simp only [hv_ne, ↓reduceIte, PIdx.toPosNat_succ]
              exact ⟨by omega, hv_eq⟩
          · simp only [hchk] at hstep; nomatch hstep
    · simp only [hi255] at hstep
      injection hstep with hp; injection hp with _ hp2
      injection hp2 with hcv' hp3; injection hp3 with hacc' _
      subst hcv' hacc'
      exact hs

private lemma chainStateBlocks_inv {σ : Type} {Inv : PIdx → σ → Prop}
    {f : PIdx → σ → ByteStream → Option (Bool × PIdx × σ × ByteStream)}
    (hf : ∀ {cv cv' acc acc' bs bs' done},
      f cv acc bs = some (done, cv', acc', bs') → Inv cv acc → Inv cv' acc') :
    ∀ (k : ℕ) {cv cv' : PIdx} {acc acc' : σ} {bs bs' : ByteStream} {done : Bool},
      chainStateBlocks f k cv acc bs = some (done, cv', acc', bs') →
      Inv cv acc → Inv cv' acc'
  | 0, _, _, _, _, _, _, _, h, hinv => by
    injection h with hp; injection hp with _ hp2
    injection hp2 with hcv hp3; injection hp3 with hacc _
    subst hcv hacc; exact hinv
  | k + 1, cv, _, acc, _, bs, _, _, h, hinv => by
    unfold chainStateBlocks at h
    cases hex : f cv acc bs with
    | none => simp only [hex] at h; nomatch h
    | some res =>
      rcases res with ⟨d1, cv1, acc1, bs1⟩
      simp only [hex] at h
      have hinv1 := hf hex hinv
      cases d1
      · exact chainStateBlocks_inv hf k h hinv1
      · injection h with hp; injection hp with _ hp2
        injection hp2 with hcv hp3; injection hp3 with hacc _
        subst hcv hacc; exact hinv1

private lemma buildTripleTower_sound {N : ℕ} (hN : N ≤ 511) (X : Fin N → ℝ × ℝ) :
    ∀ (lvl : ℕ) {cv cv' : PIdx} {acc acc' : TripleTrie} {bs bs' : ByteStream} {done : Bool},
      buildTripleTower N lvl cv acc bs = some (done, cv', acc', bs') →
      TripleTrieSound X cv acc → TripleTrieSound X cv' acc'
  | 0, _, _, _, _, _, _, _, h, hs =>
    chainStateBlocks_inv (stepTriple_sound hN X) 16 h hs
  | lvl + 1, _, _, _, _, _, _, _, h, hs =>
    chainStateBlocks_inv (buildTripleTower_sound hN X lvl) 16 h hs

theorem buildTripleTrieTree_sound {N : ℕ} (hN : N ≤ 511) (X : Fin N → ℝ × ℝ)
    {varTree : ChunkTree} {tt : TripleTrie}
    (hb : buildTripleTrieTree N varTree = some tt) :
    ∃ val : PIdx → Bool,
      ∀ {i j k : ℕ} (hij : i < j) (hjk : j < k) (hk : k < N) {v : PIdx},
        tt.get3 (ptKey i) (ptKey j) (ptKey k) = some v →
        val v = orientSign (X ⟨i, by omega⟩) (X ⟨j, by omega⟩) (X ⟨k, hk⟩) := by
  unfold buildTripleTrieTree at hb
  cases hex : buildTripleTower N 3 .xH .leaf (ByteStream.ofTree varTree) with
  | none => rw [hex] at hb; nomatch hb
  | some res =>
    rcases res with ⟨done, cv', acc', bs'⟩
    rw [hex] at hb
    cases done
    · nomatch hb
    · injection hb with htt; subst htt
      have hinit : TripleTrieSound X .xH .leaf :=
        ⟨fun _ => false, by
          intro i j k hij hjk hk v hg
          unfold TripleTrie.get3 at hg
          rw [BinTrie.get_leaf] at hg
          nomatch hg⟩
      obtain ⟨val, hval⟩ := buildTripleTower_sound hN X 3 hex hinit
      exact ⟨val, by intro i j k hij hjk hk v hg; exact (hval hij hjk hk hg).2⟩

/-- `sortTriple` permutation soundness on any `NoThreeCollinear` point sequence `X`. -/
theorem sortTriple_orientSign {N : ℕ} {X : Fin N → ℝ × ℝ} (hX : NoThreeCollinear X)
    {a b c : ℕ} (ha : a < N) (hb : b < N) (hc : c < N)
    {sgn : Bool} {i j k : ℕ}
    (hsort : sortTriple a b c = some (sgn, i, j, k)) :
    a ≠ b ∧ b ≠ c ∧ a ≠ c ∧ ∃ (hij : i < j) (hjk : j < k) (hk : k < N),
      orientSign (X ⟨a, ha⟩) (X ⟨b, hb⟩) (X ⟨c, hc⟩) =
        (if sgn then orientSign (X ⟨i, by omega⟩) (X ⟨j, by omega⟩) (X ⟨k, hk⟩)
         else !orientSign (X ⟨i, by omega⟩) (X ⟨j, by omega⟩) (X ⟨k, hk⟩)) := by
  unfold sortTriple at hsort
  cases hd : (Nat.beq a b || Nat.beq b c || Nat.beq a c)
  · simp only [hd] at hsort
    have hdist : a ≠ b ∧ b ≠ c ∧ a ≠ c := by
      obtain ⟨hab0, hbc0, hac0⟩ : Nat.beq a b = false ∧ Nat.beq b c = false ∧ Nat.beq a c = false := by
        revert hd; cases Nat.beq a b <;> cases Nat.beq b c <;> cases Nat.beq a c <;> decide
      refine ⟨fun e => ?_, fun e => ?_, fun e => ?_⟩
      · have ht := Nat.beq_eq.mpr e; rw [hab0] at ht; exact Bool.noConfusion ht
      · have ht := Nat.beq_eq.mpr e; rw [hbc0] at ht; exact Bool.noConfusion ht
      · have ht := Nat.beq_eq.mpr e; rw [hac0] at ht; exact Bool.noConfusion ht
    have fa_ne_fb : (⟨a, ha⟩ : Fin N) ≠ ⟨b, hb⟩ := fun e => hdist.1 (congrArg Fin.val e)
    have fb_ne_fc : (⟨b, hb⟩ : Fin N) ≠ ⟨c, hc⟩ := fun e => hdist.2.1 (congrArg Fin.val e)
    have fa_ne_fc : (⟨a, ha⟩ : Fin N) ≠ ⟨c, hc⟩ := fun e => hdist.2.2 (congrArg Fin.val e)
    cases hba : Nat.ble b a
    · have hab_lt : a < b := nat_ble_false_lt hba
      simp only [hba] at hsort
      cases hcb : Nat.ble c b
      · have hbc_lt : b < c := nat_ble_false_lt hcb
        simp only [hcb] at hsort
        injection hsort with hp; rcases Prod.mk.inj hp with ⟨rfl, hp2⟩
        rcases Prod.mk.inj hp2 with ⟨rfl, hp3⟩; rcases Prod.mk.inj hp3 with ⟨rfl, rfl⟩
        exact ⟨hdist.1, hdist.2.1, hdist.2.2, hab_lt, hbc_lt, hc, rfl⟩
      · have hcb_le := nat_ble_true_le hcb
        have hcb_lt : c < b := by omega
        simp only [hcb] at hsort
        cases hca : Nat.ble c a
        · have hac_lt : a < c := nat_ble_false_lt hca
          simp only [hca] at hsort
          injection hsort with hp; rcases Prod.mk.inj hp with ⟨rfl, hp2⟩
          rcases Prod.mk.inj hp2 with ⟨rfl, hp3⟩; rcases Prod.mk.inj hp3 with ⟨rfl, rfl⟩
          refine ⟨hdist.1, hdist.2.1, hdist.2.2, hac_lt, hcb_lt, hb, ?_⟩
          simp only [Bool.false_eq_true, ↓reduceIte]
          exact hX.orientSign_swap23 fa_ne_fc fb_ne_fc.symm fa_ne_fb
        · have hca_lt : c < a := by have := nat_ble_true_le hca; omega
          simp only [hca] at hsort
          injection hsort with hp; rcases Prod.mk.inj hp with ⟨rfl, hp2⟩
          rcases Prod.mk.inj hp2 with ⟨rfl, hp3⟩; rcases Prod.mk.inj hp3 with ⟨rfl, rfl⟩
          refine ⟨hdist.1, hdist.2.1, hdist.2.2, hca_lt, hab_lt, hb, ?_⟩
          simp only [↓reduceIte]
          exact (orientSign_cycle (X ⟨c, hc⟩) (X ⟨a, ha⟩) (X ⟨b, hb⟩))
    · have hba_lt : b < a := by have := nat_ble_true_le hba; omega
      simp only [hba] at hsort
      cases hca : Nat.ble c a
      · have hac_lt : a < c := nat_ble_false_lt hca
        simp only [hca] at hsort
        injection hsort with hp; rcases Prod.mk.inj hp with ⟨rfl, hp2⟩
        rcases Prod.mk.inj hp2 with ⟨rfl, hp3⟩; rcases Prod.mk.inj hp3 with ⟨rfl, rfl⟩
        refine ⟨hdist.1, hdist.2.1, hdist.2.2, hba_lt, hac_lt, hc, ?_⟩
        simp only [Bool.false_eq_true, ↓reduceIte]
        exact hX.orientSign_swap12 fa_ne_fb.symm fa_ne_fc fb_ne_fc
      · have hca_lt : c < a := by have := nat_ble_true_le hca; omega
        simp only [hca] at hsort
        cases hcb : Nat.ble c b
        · have hbc_lt : b < c := nat_ble_false_lt hcb
          simp only [hcb] at hsort
          injection hsort with hp; rcases Prod.mk.inj hp with ⟨rfl, hp2⟩
          rcases Prod.mk.inj hp2 with ⟨rfl, hp3⟩; rcases Prod.mk.inj hp3 with ⟨rfl, rfl⟩
          refine ⟨hdist.1, hdist.2.1, hdist.2.2, hbc_lt, hca_lt, ha, ?_⟩
          simp only [↓reduceIte]
          exact orientSign_cycle2 (X ⟨b, hb⟩) (X ⟨c, hc⟩) (X ⟨a, ha⟩)
        · have hcb_lt : c < b := by have := nat_ble_true_le hcb; omega
          simp only [hcb] at hsort
          injection hsort with hp; rcases Prod.mk.inj hp with ⟨rfl, hp2⟩
          rcases Prod.mk.inj hp2 with ⟨rfl, hp3⟩; rcases Prod.mk.inj hp3 with ⟨rfl, rfl⟩
          refine ⟨hdist.1, hdist.2.1, hdist.2.2, hcb_lt, hba_lt, ha, ?_⟩
          simp only [Bool.false_eq_true, ↓reduceIte]
          exact hX.orientSign_swap13 fb_ne_fc.symm fa_ne_fb.symm fa_ne_fc.symm
  · simp only [hd] at hsort; nomatch hsort

/-- Exact semantics of `litSign`: `evalLit val l = (orientSign (X a) (X b) (X c) == want)`. -/
theorem litSign_eval {ctx : CertCtx} {X : Fin ctx.n_pts → ℝ × ℝ}
    (hX : NoThreeCollinear X) {val : PIdx → Bool}
    (hval : ∀ {i j k : ℕ} (hij : i < j) (hjk : j < k) (hk : k < ctx.n_pts) {v : PIdx},
      ctx.tripleTrie.get3 (ptKey i) (ptKey j) (ptKey k) = some v →
      val v = orientSign (X ⟨i, by omega⟩) (X ⟨j, by omega⟩) (X ⟨k, hk⟩))
    {want : Bool} {a b c : ℕ} {l : Lit}
    (hl : litSign ctx want a b c = some l) :
    ∃ (ha : a < ctx.n_pts) (hb : b < ctx.n_pts) (hc : c < ctx.n_pts),
      a ≠ b ∧ b ≠ c ∧ a ≠ c ∧
      (evalLit val l = true ↔ orientSign (X ⟨a, ha⟩) (X ⟨b, hb⟩) (X ⟨c, hc⟩) = want) ∧
      (evalLit val l = false ↔ orientSign (X ⟨a, ha⟩) (X ⟨b, hb⟩) (X ⟨c, hc⟩) = !want) := by
  unfold litSign at hl
  cases hbd : (Nat.ble ctx.n_pts a || Nat.ble ctx.n_pts b || Nat.ble ctx.n_pts c)
  · simp only [hbd] at hl
    have hbds : Nat.ble ctx.n_pts a = false ∧ Nat.ble ctx.n_pts b = false ∧ Nat.ble ctx.n_pts c = false := by
      revert hbd; cases Nat.ble ctx.n_pts a <;> cases Nat.ble ctx.n_pts b <;> cases Nat.ble ctx.n_pts c <;> decide
    have ha := nat_ble_false_lt hbds.1
    have hb := nat_ble_false_lt hbds.2.1
    have hc := nat_ble_false_lt hbds.2.2
    cases hst : sortTriple a b c with
    | none => simp only [hst] at hl; nomatch hl
    | some st =>
      rcases st with ⟨sgn, i, j, k⟩
      simp only [hst] at hl
      cases hg : ctx.tripleTrie.get3 (ptKey i) (ptKey j) (ptKey k) with
      | none => simp only [hg] at hl; nomatch hl
      | some v =>
        simp only [hg] at hl
        injection hl with hl_eq; subst hl_eq
        obtain ⟨hab, hbc, hac, hij, hjk, hk, hor⟩ := sortTriple_orientSign hX ha hb hc hst
        have hv_eq := hval hij hjk hk hg
        refine ⟨ha, hb, hc, hab, hbc, hac, ?_, ?_⟩
        · unfold evalLit
          dsimp only
          rw [hv_eq, hor]
          cases want <;> cases sgn <;> cases orientSign (X ⟨i, _⟩) (X ⟨j, _⟩) (X ⟨k, hk⟩) <;> decide
        · unfold evalLit
          dsimp only
          rw [hv_eq, hor]
          cases want <;> cases sgn <;> cases orientSign (X ⟨i, _⟩) (X ⟨j, _⟩) (X ⟨k, hk⟩) <;> decide
  · simp only [hbd] at hl; nomatch hl

theorem litForb_eval_false {ctx : CertCtx} {X : Fin ctx.n_pts → ℝ × ℝ}
    (hX : NoThreeCollinear X) {val : PIdx → Bool}
    (hval : ∀ {i j k : ℕ} (hij : i < j) (hjk : j < k) (hk : k < ctx.n_pts) {v : PIdx},
      ctx.tripleTrie.get3 (ptKey i) (ptKey j) (ptKey k) = some v →
      val v = orientSign (X ⟨i, by omega⟩) (X ⟨j, by omega⟩) (X ⟨k, hk⟩))
    {forb : Bool} {a b c : ℕ} {l : Lit}
    (hl : litForb ctx forb a b c = some l) (hf : evalLit val l = false) :
    ∃ (ha : a < ctx.n_pts) (hb : b < ctx.n_pts) (hc : c < ctx.n_pts),
      orientSign (X ⟨a, ha⟩) (X ⟨b, hb⟩) (X ⟨c, hc⟩) = forb := by
  unfold litForb at hl
  obtain ⟨ha, hb, hc, _, _, _, _, hfalse⟩ := litSign_eval hX hval hl
  have heq := hfalse.mp hf
  rw [Bool.not_not] at heq
  exact ⟨ha, hb, hc, heq⟩

theorem evalClause_append_right {val : PIdx → Bool} {xs ys : Clause}
    (h : evalClause val ys = true) : evalClause val (xs ++ ys) = true := by
  unfold evalClause at h ⊢
  rw [List.any_append, h, Bool.or_true]

theorem evalClause_cons_false {val : PIdx → Bool} {l : Lit} {ls : Clause}
    (h : evalClause val (l :: ls) = false) :
    evalLit val l = false ∧ evalClause val ls = false := by
  unfold evalClause at h ⊢
  rw [List.any_cons, Bool.or_eq_false_iff] at h
  exact h

theorem evalClause_append_false {val : PIdx → Bool} {xs ys : Clause}
    (h : evalClause val (xs ++ ys) = false) :
    evalClause val xs = false ∧ evalClause val ys = false := by
  unfold evalClause at h ⊢
  rw [List.any_append, Bool.or_eq_false_iff] at h
  exact h

/-- Soundness of `inTriPairLits`: if `inOpenTriBool (X y) (X w) (X u) (X v) = true`,
    then `evalClause val ls = true` for both `pairIdx = 0` and `pairIdx = 1`. -/
theorem inTriPairLits_sound {ctx : CertCtx} {X : Fin ctx.n_pts → ℝ × ℝ}
    (hX : NoThreeCollinear X) {val : PIdx → Bool}
    (hval : ∀ {i j k : ℕ} (hij : i < j) (hjk : j < k) (hk : k < ctx.n_pts) {v : PIdx},
      ctx.tripleTrie.get3 (ptKey i) (ptKey j) (ptKey k) = some v →
      val v = orientSign (X ⟨i, by omega⟩) (X ⟨j, by omega⟩) (X ⟨k, hk⟩))
    {pairIdx : ℕ} {s : Bool} {y w u v : ℕ}
    (hy : y < ctx.n_pts) (hw : w < ctx.n_pts) (hu : u < ctx.n_pts) (hv : v < ctx.n_pts)
    (htri : inOpenTriBool (X ⟨y, hy⟩) (X ⟨w, hw⟩) (X ⟨u, hu⟩) (X ⟨v, hv⟩) = true)
    {ls : Clause} (hls : inTriPairLits ctx pairIdx s y w u v = some ls) :
    evalClause val ls = true := by
  cases hev : evalClause val ls
  · exfalso
    unfold inOpenTriBool inOpenTriSideBool at htri
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at htri
    unfold inTriPairLits eqSignLits at hls
    split_ifs at hls with hp0 hp1
    · cases h1 : litForb ctx s w u y with
      | none => simp [h1, optSequence] at hls
      | some l1 =>
        cases h2 : litSign ctx s u v y with
        | none => simp [h1, h2, optSequence] at hls
        | some l2 =>
          simp only [h1, h2, optSequence] at hls
          injection hls with hls_eq; subst hls_eq
          obtain ⟨hf1, hf2⟩ := evalClause_cons_false hev
          obtain ⟨hf2', _⟩ := evalClause_cons_false hf2
          obtain ⟨_, _, _, hs_wuy⟩ := litForb_eval_false hX hval h1 hf1
          obtain ⟨_, _, _, _, _, _, _, hs_uvy_f⟩ := litSign_eval hX hval h2
          have hs_uvy := hs_uvy_f.mp hf2'
          rcases htri with ⟨⟨t1, t2⟩, _⟩ | ⟨⟨f1, f2⟩, _⟩
          · rw [t1] at hs_wuy; subst hs_wuy; rw [t2] at hs_uvy; exact Bool.noConfusion hs_uvy
          · rw [f1] at hs_wuy; subst hs_wuy; rw [f2] at hs_uvy; exact Bool.noConfusion hs_uvy
    · cases h1 : litForb ctx s w u y with
      | none => simp [h1, optSequence] at hls
      | some l1 =>
        cases h2 : litSign ctx s v w y with
        | none => simp [h1, h2, optSequence] at hls
        | some l2 =>
          simp only [h1, h2, optSequence] at hls
          injection hls with hls_eq; subst hls_eq
          obtain ⟨hf1, hf2⟩ := evalClause_cons_false hev
          obtain ⟨hf2', _⟩ := evalClause_cons_false hf2
          obtain ⟨_, _, _, hs_wuy⟩ := litForb_eval_false hX hval h1 hf1
          obtain ⟨_, _, _, _, _, _, _, hs_vwy_f⟩ := litSign_eval hX hval h2
          have hs_vwy := hs_vwy_f.mp hf2'
          rcases htri with ⟨⟨t1, _⟩, t3⟩ | ⟨⟨f1, _⟩, f3⟩
          · rw [t1] at hs_wuy; subst hs_wuy; rw [t3] at hs_vwy; exact Bool.noConfusion hs_vwy
          · rw [f1] at hs_wuy; subst hs_wuy; rw [f3] at hs_vwy; exact Bool.noConfusion hs_vwy
  · rfl

/-- If `notInTriSideLits ctx sd p a b c = some ls` evaluates to `false`, then
    `inOpenTriSideBool sd (X p) (X a) (X b) (X c) = true`. -/
theorem notInTriSideLits_eval_false {ctx : CertCtx} {X : Fin ctx.n_pts → ℝ × ℝ}
    (hX : NoThreeCollinear X) {val : PIdx → Bool}
    (hval : ∀ {i j k : ℕ} (hij : i < j) (hjk : j < k) (hk : k < ctx.n_pts) {v : PIdx},
      ctx.tripleTrie.get3 (ptKey i) (ptKey j) (ptKey k) = some v →
      val v = orientSign (X ⟨i, by omega⟩) (X ⟨j, by omega⟩) (X ⟨k, hk⟩))
    {sd : Bool} {p a b c : ℕ} {ls : Clause}
    (hls : notInTriSideLits ctx sd p a b c = some ls)
    (hf : evalClause val ls = false) :
    ∃ (hp : p < ctx.n_pts) (ha : a < ctx.n_pts) (hb : b < ctx.n_pts) (hc : c < ctx.n_pts),
      inOpenTriSideBool sd (X ⟨p, hp⟩) (X ⟨a, ha⟩) (X ⟨b, hb⟩) (X ⟨c, hc⟩) = true := by
  unfold notInTriSideLits at hls
  cases h1 : litForb ctx sd a b p with
  | none => simp [h1, optSequence] at hls
  | some l1 =>
    cases h2 : litForb ctx sd b c p with
    | none => simp [h1, h2, optSequence] at hls
    | some l2 =>
      cases h3 : litForb ctx sd c a p with
      | none => simp [h1, h2, h3, optSequence] at hls
      | some l3 =>
        simp only [h1, h2, h3, optSequence] at hls
        injection hls with heq; subst heq
        obtain ⟨hf1, hr1⟩ := evalClause_cons_false hf
        obtain ⟨hf2, hr2⟩ := evalClause_cons_false hr1
        obtain ⟨hf3, _⟩ := evalClause_cons_false hr2
        obtain ⟨ha, hb, hp, e1⟩ := litForb_eval_false hX hval h1 hf1
        obtain ⟨_, hc, _, e2⟩ := litForb_eval_false hX hval h2 hf2
        obtain ⟨_, _, _, e3⟩ := litForb_eval_false hX hval h3 hf3
        refine ⟨hp, ha, hb, hc, ?_⟩
        unfold inOpenTriSideBool
        simp [e1, e2, e3]

/-! ## 4. `EdgeTrie` & `decodeIteratedSteps` (`Tag 19` Mini-DAG) Soundness -/

theorem EdgeTrie.hasDerived_leaf (u v : ℕ) : EdgeTrie.hasDerived .leaf u v = false := by
  unfold EdgeTrie.hasDerived
  simp [BinTrie.get_leaf]

theorem EdgeTrie.hasDerived_insertEdge {et : EdgeTrie} {u v x y : ℕ}
    (hu : u < 511) (hv : v < 511) (hx : x < 511) (hy : y < 511)
    (h : (et.insertEdge u v).hasDerived x y = true) :
    (x = u ∧ y = v) ∨ (x = v ∧ y = u) ∨ et.hasDerived x y = true := by
  unfold EdgeTrie.insertEdge at h
  unfold EdgeTrie.hasDerived at h ⊢
  by_cases hp_eq : edgePair u v = edgePair x y
  · unfold edgePair at hp_eq
    split_ifs at hp_eq with huv hxy hxy'
    · injection hp_eq with e1 e2
      exact Or.inl ⟨(ptKey_inj_lt511 hu hx e1).symm, (ptKey_inj_lt511 hv hy e2).symm⟩
    · injection hp_eq with e1 e2
      exact Or.inr (Or.inl ⟨(ptKey_inj_lt511 hv hx e2).symm, (ptKey_inj_lt511 hu hy e1).symm⟩)
    · injection hp_eq with e1 e2
      exact Or.inr (Or.inl ⟨(ptKey_inj_lt511 hv hx e1).symm, (ptKey_inj_lt511 hu hy e2).symm⟩)
    · injection hp_eq with e1 e2
      exact Or.inl ⟨(ptKey_inj_lt511 hu hx e2).symm, (ptKey_inj_lt511 hv hy e1).symm⟩
  · right; right
    rcases hp_u : edgePair u v with ⟨ku, kv⟩
    rcases hp_x : edgePair x y with ⟨kx, ky⟩
    rw [hp_u] at h hp_eq
    rw [hp_x] at h hp_eq
    dsimp only at h ⊢
    by_cases hk1 : ku = kx
    · subst hk1
      have hk2 : kv ≠ ky := fun e => hp_eq (by subst e; rfl)
      rw [BinTrie.get_insert_self] at h
      cases hget : et.get ku with
      | none =>
        simp only [hget, BinTrie.get_insert_ne _ _ hk2, BinTrie.get_leaf] at h
        nomatch h
      | some sub =>
        simp only [hget, BinTrie.get_insert_ne _ _ hk2] at h ⊢
        exact h
    · rw [BinTrie.get_insert_ne _ _ hk1] at h
      exact h

private lemma checkSidePath_sound {P : Set (ℝ × ℝ)} {S : Fin 7 → ℝ × ℝ} {w : Finset (Fin 7) → ℝ × ℝ}
    (hP : ShatteredSimplePolygon P S w) {ctx : CertCtx}
    {W₀ : Fin ctx.spec.masks.length ↪ Finset (Fin 7)}
    (hn_pts : ctx.n_pts = 7 + ctx.spec.masks.length)
    {val : PIdx → Bool}
    (hval : ∀ {i j k : ℕ} (hij : i < j) (hjk : j < k) (hk : k < ctx.n_pts) {v : PIdx},
      ctx.tripleTrie.get3 (ptKey i) (ptKey j) (ptKey k) = some v →
      val v = orientSign (pointSeq S w W₀ ⟨i, by omega⟩)
                         (pointSeq S w W₀ ⟨j, by omega⟩)
                         (pointSeq S w W₀ ⟨k, by omega⟩))
    {et : EdgeTrie}
    (het : ∀ a b (ha : a < ctx.n_pts) (hb : b < ctx.n_pts),
      hasVisEdge ctx et a b = true →
      Sees P (pointSeq S w W₀ ⟨a, by omega⟩) (pointSeq S w W₀ ⟨b, by omega⟩))
    {u v : ℕ} (hu : u < ctx.n_pts) (hv : v < ctx.n_pts) (want : Bool) :
    ∀ (mids : List ℕ) (cur : ℕ) (hcur : cur < ctx.n_pts) (acc acc' : Clause),
      checkSidePath ctx et u v want cur mids acc = some acc' →
      evalClause val acc' = false →
      let X : Fin (7 + ctx.spec.masks.length) → ℝ × ℝ := pointSeq S w W₀
      evalClause val acc = false ∧
      ∃ (midsFin : List (Fin (7 + ctx.spec.masks.length))),
        midsFin.length = mids.length ∧
        IsPolygonalPathIn P (X ⟨cur, by omega⟩) (X ⟨v, by omega⟩)
          (X ⟨cur, by omega⟩ :: (midsFin.map X ++ [X ⟨v, by omega⟩])) ∧
        (∀ z ∈ midsFin,
          z ≠ ⟨u, by omega⟩ ∧ z ≠ ⟨v, by omega⟩ ∧
          orientSign (X ⟨u, by omega⟩) (X ⟨v, by omega⟩) (X z) = want)
  | [], cur, hcur, acc, acc', hchk, hf => by
    unfold checkSidePath at hchk
    split_ifs at hchk with hvis
    injection hchk with heq; subst heq
    intro X
    have hX_mem : ∀ z : Fin (7 + ctx.spec.masks.length), X z ∈ P := by
      refine Fin.addCases (fun i => ?_) (fun j => ?_)
      · simp [X, pointSeq, Fin.addCases_left, hP.s_in_P]
      · simp [X, pointSeq, Fin.addCases_right, hP.w_in_P]
    refine ⟨hf, [], rfl, ?_, fun _ hz => nomatch hz⟩
    exact ⟨List.cons_ne_nil _ _, rfl, rfl,
      fun pt hpt => by
        simp only [List.map_nil, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hpt
        rcases hpt with rfl | rfl <;> exact hX_mem _,
      List.isChain_cons_cons.mpr ⟨het cur v hcur hv hvis, List.isChain_singleton _⟩⟩
  | mid :: rest, cur, hcur, acc, acc', hchk, hf => by
    unfold checkSidePath at hchk
    split_ifs at hchk with hcond
    simp only [Bool.and_eq_true, bne_iff_ne, decide_eq_true_eq] at hcond
    rcases hcond with ⟨⟨⟨hmid_lt, hmid_u⟩, hmid_v⟩, hvis⟩
    cases hlit : litForb ctx want u v mid with
    | none => simp [hlit] at hchk
    | some l =>
      simp only [hlit] at hchk
      let X' : Fin ctx.n_pts → ℝ × ℝ := fun z => pointSeq S w W₀ ⟨z.val, by omega⟩
      have hX' : NoThreeCollinear X' := by
        obtain ⟨hinj, hcol⟩ := noThreeCollinear_pointSeq hP W₀
        exact ⟨fun a b h => Fin.ext (Fin.mk.inj (hinj h)),
          fun a b c hab hbc hac => hcol _ _ _
            (fun e => hab (Fin.ext (Fin.mk.inj e)))
            (fun e => hbc (Fin.ext (Fin.mk.inj e)))
            (fun e => hac (Fin.ext (Fin.mk.inj e)))⟩
      obtain ⟨hcons_f, midsFin, hlen, hpath, hall⟩ :=
        checkSidePath_sound hP hn_pts hval het hu hv want rest mid hmid_lt (l :: acc) acc' hchk hf
      obtain ⟨hl_f, hacc_f⟩ := evalClause_cons_false hcons_f
      obtain ⟨_, _, _, hor_mid⟩ := litForb_eval_false hX' hval hlit hl_f
      intro X
      have hcur_mem : X ⟨cur, by omega⟩ ∈ P := by
        have hX_all : ∀ z : Fin (7 + ctx.spec.masks.length), X z ∈ P := by
          refine Fin.addCases (fun i => ?_) (fun j => ?_)
          · simp [X, pointSeq, Fin.addCases_left, hP.s_in_P]
          · simp [X, pointSeq, Fin.addCases_right, hP.w_in_P]
        exact hX_all _
      refine ⟨hacc_f, ⟨mid, by omega⟩ :: midsFin, by simp [hlen], ?_, ?_⟩
      · rcases hpath with ⟨_, _, hlast, hpts, hchain⟩
        refine ⟨List.cons_ne_nil _ _, rfl, ?_, ?_, ?_⟩
        · simp only [List.map_cons, List.cons_append]
          exact hlast
        · intro pt hpt
          simp only [List.map_cons, List.cons_append] at hpt
          rcases List.mem_cons.mp hpt with rfl | hrest_pt
          · exact hcur_mem
          · exact hpts pt hrest_pt
        · simp only [List.map_cons, List.cons_append]
          exact List.isChain_cons_cons.mpr ⟨het cur mid hcur hmid_lt hvis, hchain⟩
      · intro z hz
        rcases List.mem_cons.mp hz with rfl | hz_rest
        · exact ⟨fun e => hmid_u (congrArg Fin.val e),
                 fun e => hmid_v (congrArg Fin.val e), hor_mid⟩
        · exact hall z hz_rest

lemma base_hasVisEdge_sound {P : Set (ℝ × ℝ)} {S : Fin 7 → ℝ × ℝ} {w : Finset (Fin 7) → ℝ × ℝ}
    (hP : ShatteredSimplePolygon P S w) {ctx : CertCtx}
    (hM : ValidMasks ctx.spec.masks)
    (hm_eq : ctx.maskTrie = buildMaskTrieAux .xH ctx.spec.masks .leaf)
    (hn_pts : ctx.n_pts = 7 + ctx.spec.masks.length)
    {u v : ℕ} (hu : u < ctx.n_pts) (hv : v < ctx.n_pts)
    (hvis : hasVisEdge ctx .leaf u v = true) :
    Sees P (pointSeq S w (specWitnessEmb hM) ⟨u, by omega⟩)
           (pointSeq S w (specWitnessEmb hM) ⟨v, by omega⟩) := by
  unfold hasVisEdge at hvis
  rw [EdgeTrie.hasDerived_leaf] at hvis
  split_ifs at hvis with huv7 hvu7
  · rw [Bool.or_false] at hvis
    simp only [Bool.and_eq_true, decide_eq_true_eq] at huv7
    cases hg : getMask ctx (v - 7) with
    | none => simp [hg] at hvis
    | some m =>
      simp only [hg] at hvis
      obtain ⟨hw_lt, hm_val⟩ := getMask_sound hM hm_eq hg
      have hu_in : (⟨u, huv7.1⟩ : Fin 7) ∈ (specWitnessEmb hM) ⟨v - 7, hw_lt⟩ := by
        simp [specWitnessEmb, hm_val, hvis]
      have hsees := sees_symm ((hP.shatters _ _).mpr hu_in)
      have heq_u : pointSeq S w (specWitnessEmb hM) ⟨u, by omega⟩ = S ⟨u, huv7.1⟩ := by
        have hf : (⟨u, by omega⟩ : Fin (7 + ctx.spec.masks.length)) =
            Fin.castAdd ctx.spec.masks.length ⟨u, huv7.1⟩ := Fin.ext rfl
        unfold pointSeq; rw [hf]; exact Fin.addCases_left _
      have heq_v : pointSeq S w (specWitnessEmb hM) ⟨v, by omega⟩ =
          w ((specWitnessEmb hM) ⟨v - 7, hw_lt⟩) := by
        have hf : (⟨v, by omega⟩ : Fin (7 + ctx.spec.masks.length)) =
            Fin.natAdd 7 ⟨v - 7, hw_lt⟩ := Fin.ext (by simp [Fin.natAdd]; omega)
        unfold pointSeq; rw [hf]; exact Fin.addCases_right _
      rw [heq_u, heq_v]
      exact hsees
  · rw [Bool.or_false] at hvis
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hvu7
    cases hg : getMask ctx (u - 7) with
    | none => simp [hg] at hvis
    | some m =>
      simp only [hg] at hvis
      obtain ⟨hw_lt, hm_val⟩ := getMask_sound hM hm_eq hg
      have hv_in : (⟨v, hvu7.1⟩ : Fin 7) ∈ (specWitnessEmb hM) ⟨u - 7, hw_lt⟩ := by
        simp [specWitnessEmb, hm_val, hvis]
      have hsees := (hP.shatters _ _).mpr hv_in
      have heq_u : pointSeq S w (specWitnessEmb hM) ⟨u, by omega⟩ =
          w ((specWitnessEmb hM) ⟨u - 7, hw_lt⟩) := by
        have hf : (⟨u, by omega⟩ : Fin (7 + ctx.spec.masks.length)) =
            Fin.natAdd 7 ⟨u - 7, hw_lt⟩ := Fin.ext (by simp [Fin.natAdd]; omega)
        unfold pointSeq; rw [hf]; exact Fin.addCases_right _
      have heq_v : pointSeq S w (specWitnessEmb hM) ⟨v, by omega⟩ = S ⟨v, hvu7.1⟩ := by
        have hf : (⟨v, by omega⟩ : Fin (7 + ctx.spec.masks.length)) =
            Fin.castAdd ctx.spec.masks.length ⟨v, hvu7.1⟩ := Fin.ext rfl
        unfold pointSeq; rw [hf]; exact Fin.addCases_left _
      rw [heq_u, heq_v]
      exact hsees

private lemma hasVisEdge_insertEdge {P : Set (ℝ × ℝ)} {S : Fin 7 → ℝ × ℝ} {w : Finset (Fin 7) → ℝ × ℝ}
    (hP : ShatteredSimplePolygon P S w) {ctx : CertCtx}
    (hM : ValidMasks ctx.spec.masks)
    (hm_eq : ctx.maskTrie = buildMaskTrieAux .xH ctx.spec.masks .leaf)
    (hn_pts : ctx.n_pts = 7 + ctx.spec.masks.length)
    {et : EdgeTrie}
    (het : ∀ a b (ha : a < ctx.n_pts) (hb : b < ctx.n_pts),
      hasVisEdge ctx et a b = true →
      Sees P (pointSeq S w (specWitnessEmb hM) ⟨a, by omega⟩)
             (pointSeq S w (specWitnessEmb hM) ⟨b, by omega⟩))
    {u v : ℕ} (hu : u < ctx.n_pts) (hv : v < ctx.n_pts)
    (huv_sees : Sees P (pointSeq S w (specWitnessEmb hM) ⟨u, by omega⟩)
                       (pointSeq S w (specWitnessEmb hM) ⟨v, by omega⟩)) :
    ∀ a b (ha : a < ctx.n_pts) (hb : b < ctx.n_pts),
      hasVisEdge ctx (et.insertEdge u v) a b = true →
      Sees P (pointSeq S w (specWitnessEmb hM) ⟨a, by omega⟩)
             (pointSeq S w (specWitnessEmb hM) ⟨b, by omega⟩) := by
  intro a b ha hb hvis
  have h511 : ctx.n_pts ≤ 207 := by have := hM.1; omega
  have h_from_der : (et.insertEdge u v).hasDerived a b = true →
      Sees P (pointSeq S w (specWitnessEmb hM) ⟨a, by omega⟩)
             (pointSeq S w (specWitnessEmb hM) ⟨b, by omega⟩) := by
    intro hd
    rcases EdgeTrie.hasDerived_insertEdge (by omega) (by omega) (by omega) (by omega) hd with
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | hold
    · exact huv_sees
    · exact sees_symm huv_sees
    · refine het a b ha hb ?_
      unfold hasVisEdge
      split_ifs <;> simp [hold]
  unfold hasVisEdge at hvis
  split_ifs at hvis with hab7 hba7
  · rw [Bool.or_eq_true] at hvis
    rcases hvis with hbase | hder
    · refine base_hasVisEdge_sound hP hM hm_eq hn_pts ha hb ?_
      unfold hasVisEdge; rw [ if_pos hab7, hbase, Bool.true_or ]
    · exact h_from_der hder
  · rw [Bool.or_eq_true] at hvis
    rcases hvis with hbase | hder
    · refine base_hasVisEdge_sound hP hM hm_eq hn_pts ha hb ?_
      unfold hasVisEdge; rw [ if_neg hab7, if_pos hba7, hbase, Bool.true_or ]
    · exact h_from_der hder
  · exact h_from_der hvis

/-- Soundness of `decodeIteratedSteps` (`Tag 19`): if `evalClause val lits = false`,
    then every edge in `et` is genuinely visible in `P`. -/
theorem decodeIteratedSteps_sound {P : Set (ℝ × ℝ)} {S : Fin 7 → ℝ × ℝ} {w : Finset (Fin 7) → ℝ × ℝ}
    (hP : ShatteredSimplePolygon P S w) {ctx : CertCtx}
    (hM : ValidMasks ctx.spec.masks)
    (hm_eq : ctx.maskTrie = buildMaskTrieAux .xH ctx.spec.masks .leaf)
    (hn_pts : ctx.n_pts = 7 + ctx.spec.masks.length)
    {val : PIdx → Bool}
    (hval : ∀ {i j k : ℕ} (hij : i < j) (hjk : j < k) (hk : k < ctx.n_pts) {v : PIdx},
      ctx.tripleTrie.get3 (ptKey i) (ptKey j) (ptKey k) = some v →
      val v = orientSign (pointSeq S w (specWitnessEmb hM) ⟨i, by omega⟩)
                         (pointSeq S w (specWitnessEmb hM) ⟨j, by omega⟩)
                         (pointSeq S w (specWitnessEmb hM) ⟨k, by omega⟩)) :
    ∀ (rem : ℕ) (et et' : EdgeTrie) (acc acc' : Clause) (cs cs' : ByteStream),
      decodeIteratedSteps ctx rem et acc cs = some (et', acc', cs') →
      evalClause val acc' = false →
      (∀ a b (ha : a < ctx.n_pts) (hb : b < ctx.n_pts),
        hasVisEdge ctx et a b = true →
        Sees P (pointSeq S w (specWitnessEmb hM) ⟨a, by omega⟩)
               (pointSeq S w (specWitnessEmb hM) ⟨b, by omega⟩)) →
      ∀ a b (ha : a < ctx.n_pts) (hb : b < ctx.n_pts),
        hasVisEdge ctx et' a b = true →
        Sees P (pointSeq S w (specWitnessEmb hM) ⟨a, by omega⟩)
               (pointSeq S w (specWitnessEmb hM) ⟨b, by omega⟩)
  | 0, et, et', acc, acc', cs, cs', hdec, _, het => by
    injection hdec with hp; rcases Prod.mk.inj hp with ⟨rfl, _⟩; exact het
  | rem + 1, et, et', acc, acc', cs, cs', hdec, hf_end, het => by
    let W₀ := specWitnessEmb hM
    let X : Fin (7 + ctx.spec.masks.length) → ℝ × ℝ := pointSeq S w W₀
    let X' : Fin ctx.n_pts → ℝ × ℝ := fun z => X ⟨z.val, by omega⟩
    have hX : NoThreeCollinear X := noThreeCollinear_pointSeq hP W₀
    have hX' : NoThreeCollinear X' :=
      ⟨fun a b h => Fin.ext (Fin.mk.inj (hX.1 h)),
       fun a b c hab hbc hac => hX.2 _ _ _
         (fun e => hab (Fin.ext (Fin.mk.inj e)))
         (fun e => hbc (Fin.ext (Fin.mk.inj e)))
         (fun e => hac (Fin.ext (Fin.mk.inj e)))⟩
    have hX_in_P : ∀ z : Fin (7 + ctx.spec.masks.length), X z ∈ P := by
      refine Fin.addCases (fun i => ?_) (fun j => ?_)
      · simp [X, pointSeq, Fin.addCases_left, hP.s_in_P]
      · simp [X, pointSeq, Fin.addCases_right, hP.w_in_P]
    -- First observe that every step only prepends literals onto `acc`, so `evalClause val accStep = false`!
    have h_acc_mono : ∀ (r : ℕ) (e1 e2 : EdgeTrie) (a1 a2 : Clause) (s1 s2 : ByteStream),
        decodeIteratedSteps ctx r e1 a1 s1 = some (e2, a2, s2) →
        evalClause val a2 = false → evalClause val a1 = false := by
      intro r
      induction r with
      | zero =>
        intro e1 e2 a1 a2 s1 s2 hd hf
        injection hd with hp; rcases Prod.mk.inj hp with ⟨_, hp2⟩
        rcases Prod.mk.inj hp2 with ⟨rfl, _⟩; exact hf
      | succ r ih =>
        intro e1 e2 a1 a2 s1 s2 hd hf
        unfold decodeIteratedSteps at hd
        cases hb0 : bsReadNat s1 with
        | none => simp [hb0] at hd
        | some p0 =>
          rcases p0 with ⟨sk, s1'⟩; simp only [hb0] at hd
          split_ifs at hd with hsk0 hsk1 hsk2
          · cases hb1 : bsReadNats 3 [] s1' with
            | none => simp [hb1] at hd
            | some p1 =>
              rcases p1 with ⟨l0, cs2⟩; simp only [hb1] at hd
              rcases l0 with _ | ⟨u, _ | ⟨v, _ | ⟨len1, _ | _⟩⟩⟩ <;> try (simp at hd; done)
              dsimp only at hd
              split_ifs at hd with hc1
              cases hb2 : bsReadNats len1 [] cs2 with
              | none => simp [hb2] at hd
              | some p2 =>
                rcases p2 with ⟨mids1, cs3⟩; simp only [hb2] at hd
                cases hb3 : bsReadNat cs3 with
                | none => simp [hb3] at hd
                | some p3 =>
                  rcases p3 with ⟨len2, cs4⟩; simp only [hb3] at hd
                  split_ifs at hd with hc2
                  cases hb4 : bsReadNats len2 [] cs4 with
                  | none => simp [hb4] at hd
                  | some p4 =>
                    rcases p4 with ⟨mids2, cs5⟩; simp only [hb4] at hd
                    cases hp_a : checkSidePath ctx e1 u v true u mids1 a1 with
                    | none => simp [hp_a] at hd
                    | some acc1 =>
                      simp only [hp_a] at hd
                      cases hp_b : checkSidePath ctx e1 u v false u mids2 acc1 with
                      | none => simp [hp_b] at hd
                      | some acc2 =>
                        simp only [hp_b] at hd
                        have hf2 := ih _ _ _ _ _ _ hd hf
                        have h_csp_mono : ∀ (wnt : Bool) (ms : List ℕ) (cr : ℕ) (c_in c_out : Clause),
                            checkSidePath ctx e1 u v wnt cr ms c_in = some c_out →
                            evalClause val c_out = false → evalClause val c_in = false := by
                          intro wnt ms
                          induction ms with
                          | nil =>
                            intro cr c_in c_out hc hfo
                            unfold checkSidePath at hc
                            split_ifs at hc; injection hc with he; subst he; exact hfo
                          | cons md rst ihm =>
                            intro cr c_in c_out hc hfo
                            unfold checkSidePath at hc
                            split_ifs at hc
                            cases hl : litForb ctx wnt u v md with
                            | none => simp [hl] at hc
                            | some l =>
                              simp only [hl] at hc
                              exact (evalClause_cons_false (ihm _ _ _ hc hfo)).2
                        exact h_csp_mono _ _ _ _ _ hp_a (h_csp_mono _ _ _ _ _ hp_b hf2)
          · cases hb1 : bsReadNats 6 [] s1' with
            | none => simp [hb1] at hd
            | some p1 =>
              rcases p1 with ⟨l0, cs2⟩; simp only [hb1] at hd
              rcases l0 with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨sdN, _ | ⟨u, _ | ⟨v, _ | _⟩⟩⟩⟩⟩⟩ <;> try (simp at hd; done)
              dsimp only at hd; split_ifs at hd
              cases hnt : notInTriSideLits ctx (sdN == 1) u a b c with
              | none => simp [hnt] at hd
              | some ls =>
                simp only [hnt] at hd
                exact (evalClause_append_false (ih _ _ _ _ _ _ hd hf)).2
          · cases hb1 : bsReadNats 7 [] s1' with
            | none => simp [hb1] at hd
            | some p1 =>
              rcases p1 with ⟨l0, cs2⟩; simp only [hb1] at hd
              rcases l0 with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨sdN, _ | ⟨u, _ | ⟨sd2N, _ | ⟨v, _ | _⟩⟩⟩⟩⟩⟩⟩ <;> try (simp at hd; done)
              dsimp only at hd; split_ifs at hd
              cases hnt1 : notInTriSideLits ctx (sdN == 1) u a b c with
              | none => simp [hnt1] at hd
              | some ls1 =>
                cases hnt2 : notInTriSideLits ctx (sd2N == 1) v a b c with
                | none => simp [hnt1, hnt2] at hd
                | some ls2 =>
                  simp only [hnt1, hnt2] at hd
                  exact (evalClause_append_false (ih _ _ _ _ _ _ hd hf)).2
    unfold decodeIteratedSteps at hdec
    cases hb0 : bsReadNat cs with
    | none => simp [hb0] at hdec
    | some p0 =>
      rcases p0 with ⟨stepKind, cs1⟩; simp only [hb0] at hdec
      split_ifs at hdec with hsk0 hsk1 hsk2
      · -- (E1) Two-sided path enclosure
        cases hb1 : bsReadNats 3 [] cs1 with
        | none => simp [hb1] at hdec
        | some p1 =>
          rcases p1 with ⟨l0, cs2⟩; simp only [hb1] at hdec
          rcases l0 with _ | ⟨u, _ | ⟨v, _ | ⟨len1, _ | _⟩⟩⟩ <;> try (simp at hdec; done)
          dsimp only at hdec
          split_ifs at hdec with hc1
          simp only [Bool.and_eq_true, bne_iff_ne, decide_eq_true_eq] at hc1
          rcases hc1 with ⟨⟨⟨hu_lt, hv_lt⟩, huv_ne⟩, hlen1_pos⟩
          cases hb2 : bsReadNats len1 [] cs2 with
          | none => simp [hb2] at hdec
          | some p2 =>
            rcases p2 with ⟨mids1, cs3⟩; simp only [hb2] at hdec
            have hmids1_len : mids1.length = len1 := by
              have hlen_aux : ∀ k acc s r s', bsReadNats k acc s = some (r, s') → r.length = acc.length + k := by
                intro k; induction k with
                | zero =>
                  intro acc s r s' h; injection h with hp
                  rw [← (Prod.mk.inj hp).1, fastRev_eq_reverse]; simp
                | succ k ihk =>
                  intro acc s r s' h
                  change (match bsReadNat s with | none => none | some (n, bs') => bsReadNats k (n :: acc) bs') = some (r, s') at h
                  cases hn : bsReadNat s with
                  | none => simp [hn] at h
                  | some pn => simp only [hn] at h; rw [ihk _ _ _ _ h]; simp; omega
              simpa using hlen_aux len1 [] cs2 mids1 cs3 hb2
            cases hb3 : bsReadNat cs3 with
            | none => simp [hb3] at hdec
            | some p3 =>
              rcases p3 with ⟨len2, cs4⟩; simp only [hb3] at hdec
              split_ifs at hdec with hc2
              have hlen2_pos : 1 ≤ len2 := by simpa using hc2
              cases hb4 : bsReadNats len2 [] cs4 with
              | none => simp [hb4] at hdec
              | some p4 =>
                rcases p4 with ⟨mids2, cs5⟩; simp only [hb4] at hdec
                have hmids2_len : mids2.length = len2 := by
                  have hlen_aux : ∀ k acc s r s', bsReadNats k acc s = some (r, s') → r.length = acc.length + k := by
                    intro k; induction k with
                    | zero =>
                      intro acc s r s' h; injection h with hp
                      rw [← (Prod.mk.inj hp).1, fastRev_eq_reverse]; simp
                    | succ k ihk =>
                      intro acc s r s' h
                      change (match bsReadNat s with | none => none | some (n, bs') => bsReadNats k (n :: acc) bs') = some (r, s') at h
                      cases hn : bsReadNat s with
                      | none => simp [hn] at h
                      | some pn => simp only [hn] at h; rw [ihk _ _ _ _ h]; simp; omega
                  simpa using hlen_aux len2 [] cs4 mids2 cs5 hb4
                cases hp_a : checkSidePath ctx et u v true u mids1 acc with
                | none => simp [hp_a] at hdec
                | some acc1 =>
                  simp only [hp_a] at hdec
                  cases hp_b : checkSidePath ctx et u v false u mids2 acc1 with
                  | none => simp [hp_b] at hdec
                  | some acc2 =>
                    simp only [hp_b] at hdec
                    have hf_acc2 : evalClause val acc2 = false :=
                      h_acc_mono rem (et.insertEdge u v) et' acc2 acc' cs5 cs' hdec hf_end
                    obtain ⟨hf_acc1, mf2, hmf2_len, hpath2, hall2⟩ :=
                      checkSidePath_sound hP hn_pts hval het hu_lt hv_lt false mids2 u hu_lt acc1 acc2 hp_b hf_acc2
                    obtain ⟨_, mf1, hmf1_len, hpath1, hall1⟩ :=
                      checkSidePath_sound hP hn_pts hval het hu_lt hv_lt true mids1 u hu_lt acc acc1 hp_a hf_acc1
                    have huv_fin_ne : (⟨u, by omega⟩ : Fin (7 + ctx.spec.masks.length)) ≠ ⟨v, by omega⟩ :=
                      fun e => huv_ne (congrArg Fin.val e)
                    have hL : InteriorOnLeft (X ⟨u, by omega⟩) (X ⟨v, by omega⟩)
                        (X ⟨u, by omega⟩ :: (mf1.map X ++ [X ⟨v, by omega⟩])) := by
                      refine ⟨by simp [hmf1_len, hmids1_len]; omega, fun idx hidx h0 hlt => ?_⟩
                      rcases idx with _ | idx'
                      · omega
                      · have hlen1 : (X ⟨u, by omega⟩ :: (mf1.map X ++ [X ⟨v, by omega⟩])).length =
                            mf1.length + 2 := by simp
                        have hi' : idx' < mf1.length := by omega
                        have hget_eq : (X ⟨u, by omega⟩ :: (mf1.map X ++ [X ⟨v, by omega⟩]))[idx' + 1]'hidx =
                            X (mf1[idx']'hi') := by
                          simp only [List.getElem_cons_succ]
                          rw [List.getElem_append_left (by simp [hi']), List.getElem_map]
                        rw [hget_eq]
                        exact (orientSign_eq_true_iff _ _ _).mp (hall1 _ (List.getElem_mem _)).2.2
                    have hR : InteriorOnRight (X ⟨u, by omega⟩) (X ⟨v, by omega⟩)
                        (X ⟨u, by omega⟩ :: (mf2.map X ++ [X ⟨v, by omega⟩])) := by
                      refine ⟨by simp [hmf2_len, hmids2_len]; omega, fun idx hidx h0 hlt => ?_⟩
                      rcases idx with _ | idx'
                      · omega
                      · have hlen2 : (X ⟨u, by omega⟩ :: (mf2.map X ++ [X ⟨v, by omega⟩])).length =
                            mf2.length + 2 := by simp
                        have hi' : idx' < mf2.length := by omega
                        have hget_eq : (X ⟨u, by omega⟩ :: (mf2.map X ++ [X ⟨v, by omega⟩]))[idx' + 1]'hidx =
                            X (mf2[idx']'hi') := by
                          simp only [List.getElem_cons_succ]
                          rw [List.getElem_append_left (by simp [hi']), List.getElem_map]
                        rw [hget_eq]
                        obtain ⟨hnu, hnv, hfalse⟩ := hall2 _ (List.getElem_mem _)
                        exact (orientSign_eq_false_iff_of_ne_zero
                          (hX.2 _ _ _ huv_fin_ne hnv.symm hnu.symm)).mp hfalse
                    have huv_sees : Sees P (X ⟨u, by omega⟩) (X ⟨v, by omega⟩) :=
                      hP.two_path_enclosure _ _ _ _ (hX.1.ne huv_fin_ne) hpath1 hpath2 hL hR
                    exact decodeIteratedSteps_sound hP hM hm_eq hn_pts hval rem
                      (et.insertEdge u v) et' acc2 acc' cs5 cs' hdec hf_end
                      (hasVisEdge_insertEdge hP hM hm_eq hn_pts het hu_lt hv_lt huv_sees)
      · -- (E2) Triangle-vertex enclosure
        cases hb1 : bsReadNats 6 [] cs1 with
        | none => simp [hb1] at hdec
        | some p1 =>
          rcases p1 with ⟨l0, cs2⟩; simp only [hb1] at hdec
          rcases l0 with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨sdNat, _ | ⟨u, _ | ⟨v, _ | _⟩⟩⟩⟩⟩⟩ <;> try (simp at hdec; done)
          dsimp only at hdec
          split_ifs at hdec with hc
          simp only [Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, beq_iff_eq, decide_eq_true_eq] at hc
          rcases hc with ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨ha_lt, hb_lt⟩, hc_lt⟩, hu_lt⟩, hab⟩, hbc⟩, hca⟩, hua⟩, hub⟩, huc⟩, hv_mem⟩, hab_v⟩, hbc_v⟩, hca_v⟩
          cases hnt : notInTriSideLits ctx (sdNat == 1) u a b c with
          | none => simp [hnt] at hdec
          | some ls =>
            simp only [hnt] at hdec
            have hf_ls := (evalClause_append_false (h_acc_mono rem _ _ _ _ _ _ hdec hf_end)).1
            obtain ⟨_, _, _, _, hside⟩ := notInTriSideLits_eval_false hX' hval hnt hf_ls
            have htri_P : convexHull ℝ ({X ⟨a, by omega⟩, X ⟨b, by omega⟩, X ⟨c, by omega⟩} : Set (ℝ × ℝ)) ⊆ P :=
              hP.triangle_enclosure _ (hX_in_P _) _ (hX_in_P _) _ (hX_in_P _)
                (het a b ha_lt hb_lt hab_v) (het b c hb_lt hc_lt hbc_v)
                (sees_symm (het c a hc_lt ha_lt hca_v))
            have hu_hull : X ⟨u, by omega⟩ ∈ convexHull ℝ ({X ⟨a, by omega⟩, X ⟨b, by omega⟩, X ⟨c, by omega⟩} : Set (ℝ × ℝ)) :=
              inOpenTri_mem_convexHull (inOpenTri_and_orientSign_of_side
                (hX.2 ⟨a, _⟩ ⟨b, _⟩ ⟨u, _⟩ (Fin.val_ne_iff.mp hab) (Fin.val_ne_iff.mp (Ne.symm hub)) (Fin.val_ne_iff.mp (Ne.symm hua)))
                (hX.2 ⟨b, _⟩ ⟨c, _⟩ ⟨u, _⟩ (Fin.val_ne_iff.mp hbc) (Fin.val_ne_iff.mp (Ne.symm huc)) (Fin.val_ne_iff.mp (Ne.symm hub)))
                (hX.2 ⟨c, _⟩ ⟨a, _⟩ ⟨u, _⟩ (Fin.val_ne_iff.mp hca) (Fin.val_ne_iff.mp (Ne.symm hua)) (Fin.val_ne_iff.mp (Ne.symm huc)))
                hside).1
            have hv_lt : v < ctx.n_pts := by
              rcases hv_mem with (rfl | rfl) | rfl <;> assumption
            have hv_hull : X ⟨v, by omega⟩ ∈ convexHull ℝ ({X ⟨a, by omega⟩, X ⟨b, by omega⟩, X ⟨c, by omega⟩} : Set (ℝ × ℝ)) := by
              rcases hv_mem with (rfl | rfl) | rfl
              · exact mem_convexHull_tri_left
              · exact mem_convexHull_tri_mid
              · exact mem_convexHull_tri_right
            have huv_sees := sees_of_mem_convexHull_tri htri_P hu_hull hv_hull
            exact decodeIteratedSteps_sound hP hM hm_eq hn_pts hval rem
              (et.insertEdge u v) et' (ls ++ acc) acc' cs2 cs' hdec hf_end
              (hasVisEdge_insertEdge hP hM hm_eq hn_pts het hu_lt hv_lt huv_sees)
      · -- (E2) Triangle-pair enclosure
        cases hb1 : bsReadNats 7 [] cs1 with
        | none => simp [hb1] at hdec
        | some p1 =>
          rcases p1 with ⟨l0, cs2⟩; simp only [hb1] at hdec
          rcases l0 with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨sdNat, _ | ⟨u, _ | ⟨sd2Nat, _ | ⟨v, _ | _⟩⟩⟩⟩⟩⟩⟩ <;> try (simp at hdec; done)
          dsimp only at hdec
          split_ifs at hdec with hc
          simp only [Bool.and_eq_true, bne_iff_ne, decide_eq_true_eq] at hc
          rcases hc with ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨ha_lt, hb_lt⟩, hc_lt⟩, hu_lt⟩, hv_lt⟩, hab⟩, hbc⟩, hca⟩, hua⟩, hub⟩, huc⟩, hva⟩, hvb⟩, hvc⟩, _⟩, hab_v⟩, hbc_v⟩, hca_v⟩
          cases hnt1 : notInTriSideLits ctx (sdNat == 1) u a b c with
          | none => simp [hnt1] at hdec
          | some ls1 =>
            cases hnt2 : notInTriSideLits ctx (sd2Nat == 1) v a b c with
            | none => simp [hnt1, hnt2] at hdec
            | some ls2 =>
              simp only [hnt1, hnt2] at hdec
              have hf_step := h_acc_mono rem _ _ _ _ _ _ hdec hf_end
              obtain ⟨hf_ls21, _⟩ := evalClause_append_false hf_step
              obtain ⟨hf_ls2, hf_ls1⟩ := evalClause_append_false hf_ls21
              obtain ⟨_, _, _, _, hside1⟩ := notInTriSideLits_eval_false hX' hval hnt1 hf_ls1
              obtain ⟨_, _, _, _, hside2⟩ := notInTriSideLits_eval_false hX' hval hnt2 hf_ls2
              have htri_P : convexHull ℝ ({X ⟨a, by omega⟩, X ⟨b, by omega⟩, X ⟨c, by omega⟩} : Set (ℝ × ℝ)) ⊆ P :=
                hP.triangle_enclosure _ (hX_in_P _) _ (hX_in_P _) _ (hX_in_P _)
                  (het a b ha_lt hb_lt hab_v) (het b c hb_lt hc_lt hbc_v)
                  (sees_symm (het c a hc_lt ha_lt hca_v))
              have hu_hull : X ⟨u, by omega⟩ ∈ convexHull ℝ ({X ⟨a, by omega⟩, X ⟨b, by omega⟩, X ⟨c, by omega⟩} : Set (ℝ × ℝ)) :=
                inOpenTri_mem_convexHull (inOpenTri_and_orientSign_of_side
                  (hX.2 ⟨a, _⟩ ⟨b, _⟩ ⟨u, _⟩ (Fin.val_ne_iff.mp hab) (Fin.val_ne_iff.mp (Ne.symm hub)) (Fin.val_ne_iff.mp (Ne.symm hua)))
                  (hX.2 ⟨b, _⟩ ⟨c, _⟩ ⟨u, _⟩ (Fin.val_ne_iff.mp hbc) (Fin.val_ne_iff.mp (Ne.symm huc)) (Fin.val_ne_iff.mp (Ne.symm hub)))
                  (hX.2 ⟨c, _⟩ ⟨a, _⟩ ⟨u, _⟩ (Fin.val_ne_iff.mp hca) (Fin.val_ne_iff.mp (Ne.symm hua)) (Fin.val_ne_iff.mp (Ne.symm huc)))
                  hside1).1
              have hv_hull : X ⟨v, by omega⟩ ∈ convexHull ℝ ({X ⟨a, by omega⟩, X ⟨b, by omega⟩, X ⟨c, by omega⟩} : Set (ℝ × ℝ)) :=
                inOpenTri_mem_convexHull (inOpenTri_and_orientSign_of_side
                  (hX.2 ⟨a, _⟩ ⟨b, _⟩ ⟨v, _⟩ (Fin.val_ne_iff.mp hab) (Fin.val_ne_iff.mp (Ne.symm hvb)) (Fin.val_ne_iff.mp (Ne.symm hva)))
                  (hX.2 ⟨b, _⟩ ⟨c, _⟩ ⟨v, _⟩ (Fin.val_ne_iff.mp hbc) (Fin.val_ne_iff.mp (Ne.symm hvc)) (Fin.val_ne_iff.mp (Ne.symm hvb)))
                  (hX.2 ⟨c, _⟩ ⟨a, _⟩ ⟨v, _⟩ (Fin.val_ne_iff.mp hca) (Fin.val_ne_iff.mp (Ne.symm hva)) (Fin.val_ne_iff.mp (Ne.symm hvc)))
                  hside2).1
              have huv_sees := sees_of_mem_convexHull_tri htri_P hu_hull hv_hull
              exact decodeIteratedSteps_sound hP hM hm_eq hn_pts hval rem
                (et.insertEdge u v) et' (ls2 ++ ls1 ++ acc) acc' cs2 cs' hdec hf_end
                (hasVisEdge_insertEdge hP hM hm_eq hn_pts het hu_lt hv_lt huv_sees)

end VCDim6

end
