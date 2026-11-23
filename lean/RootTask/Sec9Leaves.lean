import Mathlib

open scoped Classical BigOperators
open Finset

namespace Sec9

def permInvCount5 (σ : Equiv.Perm (Fin 5)) : ℕ :=
  ((Finset.univ.product Finset.univ).filter
    (fun p : Fin 5 × Fin 5 => p.1 < p.2 ∧ σ p.2 < σ p.1)).card

theorem v_sigma1_ne_5_and_top2_ne_45 :
    (∀ σ : Equiv.Perm (Fin 5), σ 0 = 4 → 4 ≤ permInvCount5 σ) ∧
    (∀ σ : Equiv.Perm (Fin 5), σ.symm 0 = 4 → 4 ≤ permInvCount5 σ) ∧
    (∀ σ : Equiv.Perm (Fin 5), ({σ 0, σ 1} : Finset (Fin 5)) = {3, 4} → 6 ≤ permInvCount5 σ) := by
  norm_num [permInvCount5, Finset.ext_iff]
  use fun a s => not_lt.1 fun h => ?_, fun a s => not_lt.1 fun h => ?_, fun a s => not_lt.1 fun h => ?_
  · cases Finset.ext_iff.1 (by decide : Finset.univ.filter (fun p : Equiv.Perm (Fin 5) =>
      p 0 = 4 ∧ Finset.card (Finset.univ.filter (fun q : Fin 5 × Fin 5 => q.1 < q.2 ∧ p q.2 < p q.1)) < 4) = ∅) a with
      | intro hp => aesop (config := { warnOnNonterminal := false })
  · cases Finset.ext_iff.1 (by decide : Finset.univ.filter (fun p : Equiv.Perm (Fin 5) =>
      p.symm 0 = 4 ∧ Finset.card (Finset.univ.filter (fun q : Fin 5 × Fin 5 => q.1 < q.2 ∧ p q.2 < p q.1)) < 4) = ∅) a with
      | intro hp => aesop (config := { warnOnNonterminal := false })
  · cases Finset.ext_iff.1 (by decide : Finset.univ.filter (fun p : Equiv.Perm (Fin 5) =>
      (∀ x : Fin 5, (x = p 0 ∨ x = p 1) ↔ (x = 3 ∨ x = 4)) ∧
      Finset.card (Finset.univ.filter (fun q : Fin 5 × Fin 5 => q.1 < q.2 ∧ p q.2 < p q.1)) < 6) = ∅) a with
      | intro hp => aesop (config := { warnOnNonterminal := false })

def pairBitIdx (i j : Nat) : Nat :=
  let a := if Nat.ble i j then i else j
  let b := if Nat.ble i j then j else i
  if Nat.beq a 0 && Nat.beq b 1 then 0
  else if Nat.beq a 0 && Nat.beq b 2 then 1
  else if Nat.beq a 0 && Nat.beq b 3 then 2
  else if Nat.beq a 0 && Nat.beq b 4 then 3
  else if Nat.beq a 1 && Nat.beq b 2 then 4
  else if Nat.beq a 1 && Nat.beq b 3 then 5
  else if Nat.beq a 1 && Nat.beq b 4 then 6
  else if Nat.beq a 2 && Nat.beq b 3 then 7
  else if Nat.beq a 2 && Nat.beq b 4 then 8
  else 9

def perms5 : List (Nat × Nat × Nat × Nat × Nat) :=
  let u := [0, 1, 2, 3, 4]
  u.flatMap fun s0 =>
    (u.filter (fun x => !(Nat.beq x s0))).flatMap fun s1 =>
      (u.filter (fun x => !(Nat.beq x s0) && !(Nat.beq x s1))).flatMap fun s2 =>
        (u.filter (fun x => !(Nat.beq x s0) && !(Nat.beq x s1) && !(Nat.beq x s2))).flatMap fun s3 =>
          (u.filter (fun x => !(Nat.beq x s0) && !(Nat.beq x s1) && !(Nat.beq x s2) && !(Nat.beq x s3))).map fun s4 =>
            (s0, s1, s2, s3, s4)

def checkLeftRightCertBound : Bool :=
  let pairs : List (Nat × Nat) :=
    [(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(2,3),(2,4),(3,4)]
  let ps := perms5
  (List.range 32).all fun hi =>
    (List.range 32).all fun lo =>
      let gMask := (hi <<< 5) ||| lo
      let E3 (i j : Nat) : Bool := Nat.beq ((gMask >>> pairBitIdx i j) &&& 1) 1
      ps.all fun (s0, s1, s2, s3, s4) =>
        if Nat.beq s0 4 || ((Nat.beq s0 3 && Nat.beq s1 4) || (Nat.beq s0 4 && Nat.beq s1 3)) then true
        else
          let invAt (x : Nat) : Nat :=
            if Nat.beq x s0 then 0
            else if Nat.beq x s1 then 1
            else if Nat.beq x s2 then 2
            else if Nat.beq x s3 then 3
            else 4
          let invOk := pairs.all fun (i, j) =>
            if Nat.blt (invAt j) (invAt i) then !(E3 i j) else true
          if !invOk then true
          else
            let T3bar := (pairs.filter fun (i, j) => !(E3 i j)).length
            let T1 := (pairs.filter fun (i, j) => Nat.blt (invAt i) (invAt j) && !(E3 i j)).length
            let dL := if E3 0 4 && E3 1 4 && E3 2 4 then 1 else 0
            let dR := if E3 s0 s2 && E3 s0 s3 && E3 s0 s4 then 1 else 0
            Nat.ble 2 (T3bar + T1 + dL + dR)

theorem v_left_right_cert_bound : checkLeftRightCertBound = true := by
  decide +kernel

theorem n7_perm_inv_1_or_2_has_certificate
    (σ : Equiv.Perm (Fin 5))
    (h_inv : ((Finset.univ.product Finset.univ).filter
      (fun p : Fin 5 × Fin 5 => p.1 < p.2 ∧ σ.symm p.2 < σ.symm p.1)).card ∈ ({1, 2} : Set ℕ)) :
    (∀ i : Fin 5, i.val < 3 → σ.symm i < σ.symm ⟨4, by decide⟩) ∨
    (∀ r : Fin 5, 2 ≤ r.val → σ ⟨0, by decide⟩ < σ r) := by
  revert h_inv
  by_cases h : σ ∈ Finset.univ.filter (fun p : Equiv.Perm (Fin 5) =>
      Finset.card (Finset.univ.filter (fun q : Fin 5 × Fin 5 => q.1 < q.2 ∧ p.symm q.2 < p.symm q.1)) = 1 ∨
      Finset.card (Finset.univ.filter (fun q : Fin 5 × Fin 5 => q.1 < q.2 ∧ p.symm q.2 < p.symm q.1)) = 2)
  · exact by_contra <| absurd h ∘ by decide +revert
  · simp_all

theorem n7_T3bar1_T11_has_split_mask
    (f1_tm f2_tm f3_tm f4_tm f5_tm : ℝ)
    (f1_x1 f2_x1 f3_x1 f4_x1 f5_x1 : ℝ)
    (f1_x2 f2_x2 f3_x2 f4_x2 f5_x2 : ℝ)
    (f1_x5 f2_x5 f3_x5 f4_x5 f5_x5 : ℝ)
    (f1_tp f2_tp f3_tp f4_tp f5_tp : ℝ)
    (htm : f5_tm < f4_tm ∧ f4_tm < f3_tm ∧ f3_tm < f2_tm ∧ f2_tm < f1_tm)
    (htp : f1_tp < f2_tp ∧ f2_tp < f3_tp ∧ f3_tp < f4_tp ∧ f4_tp < f5_tp)
    (hx1 : f1_x1 < f2_x1 ∧ f1_x1 < f3_x1 ∧ f1_x1 < f4_x1 ∧ f1_x1 ≠ f5_x1)
    (hx2 : f2_x2 < f1_x2 ∧ f2_x2 < f5_x2)
    (hx5 : f5_x5 < f2_x5 ∧ f5_x5 < f3_x5 ∧ f5_x5 < f4_x5 ∧ f1_x5 ≠ f5_x5) :
    (f5_tm < min (min f1_tm f2_tm) (min f3_tm f4_tm) ∧ f2_x2 < f5_x2 ∧
      f5_x5 < min (min f1_x5 f2_x5) (min f3_x5 f4_x5)) ∨
    (f1_x1 < min (min f2_x1 f3_x1) (min f4_x1 f5_x1) ∧ f2_x2 < f1_x2 ∧
      f1_tp < min (min f2_tp f3_tp) (min f4_tp f5_tp)) ∨
    (max f1_x1 f5_x1 < min f2_x1 (min f3_x1 f4_x1) ∧
      f2_x2 < max f1_x2 f5_x2 ∧
      max f1_x5 f5_x5 < min f2_x5 (min f3_x5 f4_x5)) := by
  grind

def checkN7T3bar0Diagonals : Bool :=
  let khat : Array (Fin 5) := #[0, 1, 2, 3, 4, 0, 1, 2, 3, 4]
  let diags : List (Finset (Fin 5)) := [{0, 2}, {0, 3}, {1, 3}, {1, 4}, {2, 4}]
  let interiorPos : List Nat := [1, 2, 3, 4, 5, 6, 7, 8]
  interiorPos.all fun i1 =>
    interiorPos.all fun i2 =>
      interiorPos.all fun i3 =>
        if !(i1 < i2 && i2 < i3) then true
        else
          let rem : List Nat := [i1, i2, i3]
          let hullIdx : List Nat := (List.range 10).filter (fun p => !(rem.contains p))
          let adjDistinct := (hullIdx.zip hullIdx.tail).all fun (a, b) => khat[a]! != khat[b]!
          if !adjDistinct then true
          else
            let a2 : List (Finset (Fin 5)) :=
              (hullIdx.zip hullIdx.tail).map fun (a, b) => ({khat[a]!, khat[b]!} : Finset (Fin 5))
            let b2 : List (Finset (Fin 5)) :=
              rem.flatMap fun r =>
                let leftH := (hullIdx.filter (fun p => p < r)).getLast!
                let rightH := (hullIdx.filter (fun p => r < p)).head!
                ([{khat[r]!, khat[leftH]!}, {khat[r]!, khat[rightH]!}] : List (Finset (Fin 5)))
            let realizedPairs := a2 ++ b2
            !(diags.all fun d => realizedPairs.contains d)

theorem v_n7_T3bar0_diagonals_lt_5 : checkN7T3bar0Diagonals = true := by
  decide +kernel

def bitSet (m c : Nat) : Bool := Nat.beq ((m >>> c) &&& 1) 1

def checkN5Elim : Bool :=
  let ivals : List (Nat × Nat) :=
    [(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3),(2,4),(3,3),(3,4),(4,4)]
  let masks : List Nat := 21 :: (List.range 31).map (fun x => x + 1)
  (List.range 32).all fun hi =>
    (List.range 32).all fun lo =>
      let code := (hi <<< 5) ||| lo
      let slab (c : Nat) : Nat := (code >>> (2 * c)) &&& 3
      let realizes (tMask : Nat) : Bool :=
        ivals.any fun (a, b) =>
          let baseOk := (List.range (b + 1 - a)).all fun d => bitSet tMask (a + d)
          if !baseOk then false
          else
            [0, 1, 2, 3, 4].all fun c =>
              if !(bitSet tMask c) then true
              else if Nat.ble a c && Nat.ble c b then true
              else
                let j := slab c
                Nat.ble a (j + 1) && Nat.ble j b
      !(masks.all realizes)

def checkN6Elim : Bool :=
  let words6 : List (Nat × Nat × Nat × Nat × Nat × Nat) :=
    [ (0, 1, 0, 2, 3, 4),
      (0, 1, 2, 0, 3, 4),
      (0, 1, 2, 3, 0, 4),
      (1, 0, 2, 0, 3, 4),
      (1, 0, 2, 3, 0, 4),
      (1, 0, 2, 3, 4, 0),
      (1, 2, 0, 3, 0, 4),
      (1, 2, 0, 3, 4, 0),
      (1, 2, 3, 0, 4, 0)
    ]
  let ivals6 : List (Nat × Nat) :=
    [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,2),(1,3),(1,4),(1,5),
     (2,2),(2,3),(2,4),(2,5),(3,3),(3,4),(3,5),(4,4),(4,5),(5,5)]
  let masks : List Nat := [22, 26, 17, 20, 18, 21, 19] ++ (List.range 31).map (fun x => x + 1)
  words6.all fun (c0, c1, c2, c3, c4, c5) =>
    let kAt (idx : Nat) : Nat :=
      if Nat.beq idx 0 then c0
      else if Nat.beq idx 1 then c1
      else if Nat.beq idx 2 then c2
      else if Nat.beq idx 3 then c3
      else if Nat.beq idx 4 then c4
      else c5
    (List.range 25).all fun hi =>
      (List.range 25).all fun lo =>
        let code := hi * 25 + lo
        let slab4 (c : Nat) : Nat :=
          if Nat.beq c 1 then code % 5
          else if Nat.beq c 2 then (code / 5) % 5
          else if Nat.beq c 3 then (code / 25) % 5
          else (code / 125) % 5
        let realizes (tMask : Nat) : Bool :=
          ivals6.any fun (a, b) =>
            let indices := (List.range (b + 1 - a)).map (fun d => a + d)
            let baseOk := indices.all (fun idx => bitSet tMask (kAt idx))
            if !baseOk then false
            else
              [0, 1, 2, 3, 4].all fun c =>
                if !(bitSet tMask c) then true
                else if indices.any (fun idx => Nat.beq (kAt idx) c) then true
                else if Nat.beq c 0 then false
                else
                  let j := slab4 c
                  Nat.ble a (j + 1) && Nat.ble j b
        !(masks.all realizes)

theorem v_n5_n6_island_rule_elimination : checkN5Elim = true ∧ checkN6Elim = true := by
  decide +kernel

end Sec9
