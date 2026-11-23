import RootTask.VCDim6.FastTrieRUP

/-!
# Zero-Mathlib Generative Core-Clause & RUP Certificate Format (`CaseCertFormat.lean`)

Provides an `Init`-only (zero `Mathlib` imports, `< 1s` compile time per case module)
generative chirotope clause builder and pure-kernel `FastTrieRUP` verifier for the 62
monotone canonical cases of `VC-dim(P) ≤ 6`:
- `CaseSpec`: canonical specification `(n_d, h_sz, lr_l, edges, masks)` for `|S| = 7`.
- `TripleTrie`: 3-level `BinTrie` mapping active sorted triples `(i, j, k)` (`i < j < k < n_pts`)
  to compact `PIdx` variable indices with zero large `Nat` arithmetic in Lean's kernel.
- `ClauseJust`: typed geometric clause constructors covering `(C1)` GP5, `(C2)` Hull/Interior,
  `(C4)` Obstruction, `(C5)` ExitTri & WedgeSep, `(C6)` Pocket/Neighbor/Zh/SideCorners,
  `(C7)` Two-Sided Separation, `(C8)` Half-Plane Lemma, `(C9)` `vis_SS`, `N1` Quad/Darts,
  and `IteratedCut` mini-DAGs (`bulk_cegar_enclosure`).
- `checkCaseCert`: decodes `varStr`, `justStr`, and `rupStr`, constructs the exact core CNF
  in a `BinTrie Clause`, and runs `FastTrieRUP.checkEncodedRUP`.
-/

namespace VCDim6.FastTrieRUP

noncomputable section

/-- Converts small `Nat` (`0 ↦ 1`, `n ↦ n + 1`) to `PIdx` by `n` applications of `PIdx.succ`.
    Used only on point/clause indices (`≤ 135` for points, sequentially incremented for clauses). -/
def PIdx.ofSmallNat : Nat → PIdx
  | 0 => .xH
  | n + 1 => (PIdx.ofSmallNat n).succ

/-- Canonical specification of one Stage-1 or Stage-2 task on `|S| = 7`. -/
structure CaseSpec where
  n_d : Nat
  h_sz : Nat
  lr_l : Option Nat
  edges : List (Option Nat)
  masks : List Nat
  deriving DecidableEq

/-- Builds `B_ccw` matching `gen_chiro_h1.cpp`: `0 .. n_d - 1` with `n_d .. n_d + h_sz - 1`
    inserted immediately after `d` when `h_sz > 0` and `lr_l = some d`. -/
def buildRange (start cnt : Nat) : List Nat :=
  match cnt with
  | 0 => []
  | k + 1 => start :: buildRange (start + 1) k

def buildBccwAux (n_d h_sz : Nat) (lr_l : Option Nat) (d rem : Nat) : List Nat :=
  match rem with
  | 0 => []
  | r + 1 =>
    let tail := buildBccwAux n_d h_sz lr_l (d + 1) r
    if h_sz > 0 && lr_l == some d then
      d :: (buildRange n_d h_sz ++ tail)
    else
      d :: tail

def buildBccw (spec : CaseSpec) : List Nat :=
  buildBccwAux spec.n_d spec.h_sz spec.lr_l 0 spec.n_d

/-- Builds a `BinTrie PIdx` mapping small `Nat` (`0 .. limit - 1`) to its `PIdx`,
    avoiding repeated `ofSmallNat` walks. -/
def buildPtKeysAux (cur : PIdx) (idx rem : Nat) (acc : List PIdx) : List PIdx :=
  match rem with
  | 0 => acc.reverse
  | r + 1 => buildPtKeysAux cur.succ (idx + 1) r (cur :: acc)

/-- 3-level nested `BinTrie` mapping `(i, j, k)` (`i < j < k`) to variable `PIdx`. -/
abbrev TripleTrie := BinTrie (BinTrie (BinTrie PIdx))

def TripleTrie.insert3 (t : TripleTrie) (ki kj kk val : PIdx) : TripleTrie :=
  let t1 := match t.get ki with | some m => m | none => .leaf
  let t2 := match t1.get kj with | some m => m | none => .leaf
  withStrictTrie (t2.insert (strictPIdx kk) (strictPIdx val)) (fun t2' =>
    withStrictTrie (t1.insert (strictPIdx kj) t2') (fun t1' =>
      withStrictTrie (t.insert (strictPIdx ki) t1') (fun t' => t')))

def TripleTrie.get3 (t : TripleTrie) (ki kj kk : PIdx) : Option PIdx :=
  match t.get ki with
  | none => none
  | some t1 =>
    match t1.get kj with
    | none => none
    | some t2 => t2.get kk

/-- Sorts 3 distinct `Nat`s `(a, b, c)` into `(sgn, i, j, k)` with `i < j < k` and `sgn = true`
    for even permutations, `sgn = false` for odd permutations (using `Nat.ble`/`Nat.beq`, zero `Decidable`). -/
def sortTriple (a b c : Nat) : Option (Bool × Nat × Nat × Nat) :=
  match Nat.beq a b || Nat.beq b c || Nat.beq a c with
  | true => none
  | false =>
    match Nat.ble b a with
    | false => -- a < b
      match Nat.ble c b with
      | false => some (true, a, b, c)
      | true =>
        match Nat.ble c a with
        | false => some (false, a, c, b)
        | true => some (true, c, a, b)
    | true => -- b < a
      match Nat.ble c a with
      | false => some (false, b, a, c)
      | true =>
        match Nat.ble c b with
        | false => some (true, b, c, a)
        | true => some (false, c, b, a)

/-- Precomputed lookup tables for fast `O(log N)` indexing during clause generation. -/
structure CertCtx where
  spec : CaseSpec
  n_pts : Nat
  bccw : List Nat
  ptKeyTrie : BinTrie PIdx
  maskTrie : BinTrie Nat
  tripleTrie : TripleTrie

def ptKey (u : Nat) : PIdx :=
  let n := u + 1
  match Nat.ble 64 n with
  | false => pidxTop6 n
  | true => wrapLow6 (n % 64) (pidxTop6 (n / 64))

def pow2Small (s : Nat) : Nat :=
  match Nat.ble 4 s with
  | false =>
    match Nat.ble 2 s with
    | false =>
      match Nat.ble 1 s with
      | false => 1
      | true  => 2
    | true =>
      match Nat.ble 3 s with
      | false => 4
      | true  => 8
  | true =>
    match Nat.ble 6 s with
    | false =>
      match Nat.ble 5 s with
      | false => 16
      | true  => 32
    | true =>
      match Nat.ble 7 s with
      | false => 64
      | true  => 128

def buildMaskTrieAux (cur : PIdx) : List Nat → BinTrie Nat → BinTrie Nat
  | [], acc => acc
  | m :: ms, acc => buildMaskTrieAux cur.succ ms (acc.insert cur m)

def getMask (ctx : CertCtx) (wIdx : Nat) : Option Nat :=
  ctx.maskTrie.get (ptKey wIdx)

def seesBit (mask s : Nat) : Bool :=
  Nat.beq ((mask / pow2Small s) % 2) 1

/-- Looks up the literal asserting `orientSign (X a) (X b) (X c) == want` (zero `Decidable`). -/
def litSign (ctx : CertCtx) (want : Bool) (a b c : Nat) : Option Lit :=
  match Nat.ble ctx.n_pts a || Nat.ble ctx.n_pts b || Nat.ble ctx.n_pts c with
  | true => none
  | false =>
    match sortTriple a b c with
    | none => none
    | some (sgn, i, j, k) =>
      match ctx.tripleTrie.get3 (ptKey i) (ptKey j) (ptKey k) with
      | none => none
      | some v => some ((match want with | true => sgn | false => !sgn), v)

/-- Literal asserting `orientSign (X a) (X b) (X c) != forb` (i.e. falsified when `== forb`). -/
def litForb (ctx : CertCtx) (forb : Bool) (a b c : Nat) : Option Lit :=
  litSign ctx (!forb) a b c

def optSequence : List (Option α) → Option (List α)
  | [] => some []
  | none :: _ => none
  | some x :: xs =>
    match optSequence xs with
    | none => none
    | some ys => some (x :: ys)

/-- Helper asserting `orientSign p1 p2 z == orientSign q1 q2 w` at polarity `s` (`!(lhs==s) ∨ (rhs==s)`). -/
def eqSignLits (ctx : CertCtx) (s : Bool) (p1 p2 z q1 q2 w : Nat) : Option (List Lit) :=
  optSequence [litForb ctx s p1 p2 z, litSign ctx s q1 q2 w]

/-- Helper for `inOpenTriBool y w u v = true` via its 4 pure-chirotope 2-literal clauses:
    `pairIdx = 0`: `orient(w, u, y) == orient(u, v, y)` (at polarity `s`),
    `pairIdx = 1`: `orient(w, u, y) == orient(v, w, y)` (at polarity `s`). -/
def inTriPairLits (ctx : CertCtx) (pairIdx : Nat) (s : Bool) (y w u v : Nat) : Option (List Lit) :=
  if pairIdx == 0 then
    eqSignLits ctx s w u y u v y
  else if pairIdx == 1 then
    eqSignLits ctx s w u y v w y
  else
    none

/-- Negated `inOpenTriSideBool sd p a b c = true` (3 literals: `¬(orient a b p == sd ∧ orient b c p == sd ∧ orient c a p == sd)`). -/
def notInTriSideLits (ctx : CertCtx) (sd : Bool) (p a b c : Nat) : Option (List Lit) :=
  optSequence [litForb ctx sd a b p, litForb ctx sd b c p, litForb ctx sd c a p]

/-! ## Mini-DAG Verifier for `bulk_cegar_enclosure` (`IteratedCut`, Tag `19`) -/

abbrev EdgeTrie := BinTrie (BinTrie Bool)

def edgePair (u v : Nat) : PIdx × PIdx :=
  if u ≤ v then (ptKey u, ptKey v) else (ptKey v, ptKey u)

def EdgeTrie.insertEdge (et : EdgeTrie) (u v : Nat) : EdgeTrie :=
  let (ku, kv) := edgePair u v
  let sub := match et.get ku with | some m => m | none => .leaf
  et.insert ku (sub.insert kv true)

def EdgeTrie.hasDerived (et : EdgeTrie) (u v : Nat) : Bool :=
  let (ku, kv) := edgePair u v
  match et.get ku with
  | none => false
  | some sub => sub.get kv == some true

def hasVisEdge (ctx : CertCtx) (et : EdgeTrie) (u v : Nat) : Bool :=
  if u < 7 && 7 ≤ v then
    (match getMask ctx (v - 7) with | some m => seesBit m u | none => false) || et.hasDerived u v
  else if v < 7 && 7 ≤ u then
    (match getMask ctx (u - 7) with | some m => seesBit m v | none => false) || et.hasDerived u v
  else
    et.hasDerived u v

/-- Decodes `k` `Nat`s from a character list. -/
def decodeNats : Nat → List Nat → List Char → Option (List Nat × List Char)
  | 0, acc, cs => some (acc.reverse, cs)
  | k + 1, acc, cs =>
    match decodeNat cs with
    | none => none
    | some (n, rest) => decodeNats k (n :: acc) rest

/-- Checks an `(E1)` side path from `cur` through internal vertices `mids` to `v` with side `want`,
    accumulating negated orientation literals `litForb ctx want u v mid`. -/
def checkSidePath (ctx : CertCtx) (et : EdgeTrie) (u v : Nat) (want : Bool)
    (cur : Nat) : List Nat → Clause → Option Clause
  | [], acc =>
    if hasVisEdge ctx et cur v then some acc else none
  | mid :: rest, acc =>
    if mid < ctx.n_pts && mid != u && mid != v && hasVisEdge ctx et cur mid then
      match litForb ctx want u v mid with
      | none => none
      | some l => checkSidePath ctx et u v want mid rest (l :: acc)
    else
      none

/-- Processes `remSteps` mini-DAG derivation steps for an `IteratedCut` over `ByteStream`. -/
def decodeIteratedSteps (ctx : CertCtx) : Nat → EdgeTrie → Clause → ByteStream →
    Option (EdgeTrie × Clause × ByteStream)
  | 0, et, acc, cs => some (et, acc, cs)
  | rem + 1, et, acc, cs =>
    match bsReadNat cs with
    | none => none
    | some (stepKind, cs1) =>
      if stepKind == 0 then
        -- (E1) Two-sided path enclosure: u, v, len1, mids1..., len2, mids2...
        match bsReadNats 3 [] cs1 with
        | some ([u, v, len1], cs2) =>
          if u < ctx.n_pts && v < ctx.n_pts && u != v && 1 ≤ len1 then
            match bsReadNats len1 [] cs2 with
            | none => none
            | some (mids1, cs3) =>
              match bsReadNat cs3 with
              | none => none
              | some (len2, cs4) =>
                if 1 ≤ len2 then
                  match bsReadNats len2 [] cs4 with
                  | none => none
                  | some (mids2, cs5) =>
                    match checkSidePath ctx et u v true u mids1 acc with
                    | none => none
                    | some acc1 =>
                      match checkSidePath ctx et u v false u mids2 acc1 with
                      | none => none
                      | some acc2 =>
                        decodeIteratedSteps ctx rem (et.insertEdge u v) acc2 cs5
                else none
          else none
        | _ => none
      else if stepKind == 1 then
        -- (E2) Triangle-vertex enclosure: a, b, c, sd_nat, u, v (where v ∈ {a, b, c})
        match bsReadNats 6 [] cs1 with
        | some ([a, b, c, sdNat, u, v], cs2) =>
          let sd := sdNat == 1
          if a < ctx.n_pts && b < ctx.n_pts && c < ctx.n_pts && u < ctx.n_pts &&
             a != b && b != c && c != a &&
             u != a && u != b && u != c &&
             (v == a || v == b || v == c) &&
             hasVisEdge ctx et a b && hasVisEdge ctx et b c && hasVisEdge ctx et c a then
            match notInTriSideLits ctx sd u a b c with
            | none => none
            | some ls => decodeIteratedSteps ctx rem (et.insertEdge u v) (ls ++ acc) cs2
          else none
        | _ => none
      else if stepKind == 2 then
        -- (E2) Triangle-pair enclosure: a, b, c, sd_nat, u, sd'_nat, v
        match bsReadNats 7 [] cs1 with
        | some ([a, b, c, sdNat, u, sd2Nat, v], cs2) =>
          let sd := sdNat == 1
          let sd2 := sd2Nat == 1
          if a < ctx.n_pts && b < ctx.n_pts && c < ctx.n_pts && u < ctx.n_pts && v < ctx.n_pts &&
             a != b && b != c && c != a &&
             u != a && u != b && u != c &&
             v != a && v != b && v != c && u != v &&
             hasVisEdge ctx et a b && hasVisEdge ctx et b c && hasVisEdge ctx et c a then
            match notInTriSideLits ctx sd u a b c, notInTriSideLits ctx sd2 v a b c with
            | some ls1, some ls2 =>
              decodeIteratedSteps ctx rem (et.insertEdge u v) (ls2 ++ ls1 ++ acc) cs2
            | _, _ => none
          else none
        | _ => none
      else none

/-! ## Single-Clause Stream Decoder & Generator (`decodeOneJust`) -/

def allDistinct5 (a b c d e : Nat) : Bool :=
  a != b && a != c && a != d && a != e &&
  b != c && b != d && b != e &&
  c != d && c != e && d != e

def listGetOpt : List α → Nat → Option α
  | [], _ => none
  | x :: _, 0 => some x
  | _ :: xs, k + 1 => listGetOpt xs k

/-- Decodes either end-of-stream (`tag == 20`, returning `some (none, cs1)`) or one geometric
    clause specification (`tag ∈ 0..19`, returning `some (some cl, rest)`). -/
def decodeOneJust (ctx : CertCtx) (cs : ByteStream) : Option (Option Clause × ByteStream) :=
  match bsReadNat cs with
  | none => none
  | some (tag, cs1) =>
    if tag == 20 then
      some (none, cs1)
    else if tag == 0 || tag == 1 then
      -- Tag 0 / 1: (C1) GP5 6-literal exclusion: ip, ia, ib, ic, id_, flags (0..7)
      match bsReadNats 6 [] cs1 with
      | some ([ip, ia, ib, ic, id_, flags], rest) =>
        if ip < ctx.n_pts && ia < ctx.n_pts && ib < ctx.n_pts && ic < ctx.n_pts && id_ < ctx.n_pts &&
           allDistinct5 ip ia ib ic id_ then
          let s1 := (flags % 2) == 1
          let s2 := ((flags / 2) % 2) == 1
          let s3 := ((flags / 4) % 2) == 1
          let litsOpt :=
            if tag == 0 then
              optSequence [
                litForb ctx s1 ip ia ib, litForb ctx s1 ip ic id_,
                litForb ctx s2 ip ia ic, litForb ctx (!s2) ip ib id_,
                litForb ctx s3 ip ia id_, litForb ctx s3 ip ib ic
              ]
            else
              optSequence [
                litForb ctx s1 ip ia ib, litForb ctx (!s1) ip ic id_,
                litForb ctx s2 ip ia ic, litForb ctx s2 ip ib id_,
                litForb ctx s3 ip ia id_, litForb ctx (!s3) ip ib ic
              ]
          match litsOpt with
          | some cl => some (some cl, rest)
          | none => none
        else none
      | _ => none
    else if tag == 2 then
      -- Tag 2: (C2) Hull CCW triple: i, j, k (indices in B_ccw, i < j < k)
      match bsReadNats 3 [] cs1 with
      | some ([i, j, k], rest) =>
        if i < j && j < k then
          match listGetOpt ctx.bccw i, listGetOpt ctx.bccw j, listGetOpt ctx.bccw k with
          | some pi, some pj, some pk =>
            match litSign ctx true pi pj pk with
            | some l => some (some [l], rest)
            | none => none
          | _, _, _ => none
        else none
      | _ => none
    else if tag == 3 then
      -- Tag 3: (C2) Interior point in conv(B): r, a
      match bsReadNats 2 [] cs1 with
      | some ([r, a], rest) =>
        let b_sz := ctx.bccw.length
        if r < b_sz && ctx.spec.n_d + ctx.spec.h_sz ≤ a && a < 7 then
          let r_next := if r + 1 < b_sz then r + 1 else 0
          match listGetOpt ctx.bccw r, listGetOpt ctx.bccw r_next with
          | some pr, some pr1 =>
            match litSign ctx true pr pr1 a with
            | some l => some (some [l], rest)
            | none => none
          | _, _ => none
        else none
      | _ => none
    else if tag == 4 then
      -- Tag 4: (C4) Non-certified hull obstruction: wIdx, k, s1, s2, sdNat
      match bsReadNats 5 [] cs1 with
      | some ([wIdx, k, s1, s2, sdNat], rest) =>
        match getMask ctx wIdx with
        | some m =>
          if k < ctx.spec.n_d && s1 < s2 && s2 < 7 &&
             !seesBit m k && seesBit m s1 && seesBit m s2 then
            match notInTriSideLits ctx (sdNat == 1) k (7 + wIdx) s1 s2 with
            | some cl => some (some cl, rest)
            | none => none
          else none
        | none => none
      | _ => none
    else if tag == 5 then
      -- Tag 5: (C5) Exit-edge triangle containment: eIdx, wIdx, pairIdx, sNat
      match bsReadNats 4 [] cs1 with
      | some ([eIdx, wIdx, pairIdx, sNat], rest) =>
        match listGetOpt ctx.spec.edges eIdx, getMask ctx wIdx with
        | some (some u_y), some m =>
          let n_d := ctx.spec.n_d
          if 3 ≤ n_d && u_y < n_d && eIdx < 7 - n_d then
            let v_y := if u_y + 1 < n_d then u_y + 1 else 0
            let y := n_d + eIdx
            if seesBit m u_y && seesBit m v_y then
              match inTriPairLits ctx pairIdx (sNat == 1) y (7 + wIdx) u_y v_y with
              | some cl => some (some cl, rest)
              | none => none
            else none
          else none
        | _, _ => none
      | _ => none
    else if tag == 6 then
      -- Tag 6: (C5/C6) Wedge separation: coneKind (0=exit, 1=pocket_lr, 2=nb), idx, w1, w2, wm, sNat
      match bsReadNats 6 [] cs1 with
      | some ([coneKind, idx, w1, w2, wm, sNat], rest) =>
        let uvOpt : Option (Nat × Nat × Nat) :=
          if coneKind == 0 then
            match listGetOpt ctx.spec.edges idx with
            | some (some u) =>
              let n_d := ctx.spec.n_d
              if 3 ≤ n_d && u < n_d && idx < 7 - n_d then
                some (n_d + idx, u, if u + 1 < n_d then u + 1 else 0)
              else none
            | _ => none
          else if coneKind == 1 then
            match ctx.spec.lr_l with
            | some l =>
              let n_d := ctx.spec.n_d
              if ctx.spec.h_sz > 0 && idx < ctx.spec.h_sz && l < n_d && 2 ≤ n_d then
                some (n_d + idx, l, if l + 1 < n_d then l + 1 else 0)
              else none
            | none => none
          else if coneKind == 2 then
            match ctx.spec.lr_l with
            | some l =>
              let n_d := ctx.spec.n_d
              let h_sz := ctx.spec.h_sz
              if h_sz > 1 && idx < h_sz && l < n_d && 2 ≤ n_d then
                let h := n_d + idx
                let r := if l + 1 < n_d then l + 1 else 0
                let hm := if idx == 0 then l else h - 1
                let hp := if idx + 1 == h_sz then r else h + 1
                some (h, hm, hp)
              else none
            | none => none
          else none
        match uvOpt, getMask ctx w1, getMask ctx w2, getMask ctx wm with
        | some (y, u, v), some m1, some m2, some mm =>
          if w1 != w2 &&
             seesBit m1 u && seesBit m1 v && seesBit m1 y &&
             seesBit m2 u && seesBit m2 v && seesBit m2 y &&
             seesBit mm u && seesBit mm v && !seesBit mm y then
            let s := sNat == 1
            match optSequence [
              litForb ctx s y (7 + w1) (7 + w2),
              litForb ctx s y (7 + w1) (7 + wm),
              litForb ctx s y (7 + wm) (7 + w2)
            ] with
            | some cl => some (some cl, rest)
            | none => none
          else none
        | _, _, _, _ => none
      | _ => none
    else if tag == 7 then
      -- Tag 7: (C6) Pocket (l, r) or Neighbor (hm, hp) triangle containment: isNb, hi, wIdx, pairIdx, sNat
      match bsReadNats 5 [] cs1 with
      | some ([isNb, hi, wIdx, pairIdx, sNat], rest) =>
        match ctx.spec.lr_l, getMask ctx wIdx with
        | some l, some m =>
          let n_d := ctx.spec.n_d
          let h_sz := ctx.spec.h_sz
          if h_sz > 0 && hi < h_sz && l < n_d && 2 ≤ n_d then
            let h := n_d + hi
            let r := if l + 1 < n_d then l + 1 else 0
            if isNb == 0 then
              if seesBit m l && seesBit m r then
                match inTriPairLits ctx pairIdx (sNat == 1) h (7 + wIdx) l r with
                | some cl => some (some cl, rest)
                | none => none
              else none
            else if isNb == 1 && h_sz > 1 then
              let hm := if hi == 0 then l else h - 1
              let hp := if hi + 1 == h_sz then r else h + 1
              if seesBit m hm && seesBit m hp && !seesBit m h then
                match inTriPairLits ctx pairIdx (sNat == 1) h (7 + wIdx) hm hp with
                | some cl => some (some cl, rest)
                | none => none
              else none
            else none
          else none
        | _, _ => none
      | _ => none
    else if tag == 8 then
      -- Tag 8: (C6) z_h separation (unit literal): zhIdx, hi, target, isRightNat
      match bsReadNats 4 [] cs1 with
      | some ([zhIdx, hi, target, isRightNat], rest) =>
        match ctx.spec.lr_l, getMask ctx zhIdx with
        | some l, some zm =>
          let n_d := ctx.spec.n_d
          let h_sz := ctx.spec.h_sz
          let h := n_d + hi
          let r := if l + 1 < n_d then l + 1 else 0
          if h_sz > 0 && hi < h_sz && h < 7 && l < n_d && 2 ≤ n_d && zm == (127 - pow2Small h) then
            if isRightNat == 0 then
              if (n_d ≤ target && target < h) || target == l then
                match litSign ctx true (7 + zhIdx) h target with
                | some lit => some (some [lit], rest)
                | none => none
              else none
            else
              if (h < target && target < n_d + h_sz) || target == r then
                match litSign ctx false (7 + zhIdx) h target with
                | some lit => some (some [lit], rest)
                | none => none
              else none
          else none
        | _, _ => none
      | _ => none
    else if tag == 9 then
      -- Tag 9: (C6) General side-corners: zhIdx, hi, u, v, wIdx, suNat, pairIdx, swNat
      match bsReadNats 8 [] cs1 with
      | some ([zhIdx, hi, u, v, wIdx, suNat, pairIdx, swNat], rest) =>
        match getMask ctx zhIdx, getMask ctx wIdx with
        | some zm, some mw =>
          let h := ctx.spec.n_d + hi
          if ctx.spec.h_sz > 0 && hi < ctx.spec.h_sz && h < 7 && zm == (127 - pow2Small h) &&
             u < v && v < 7 && u != h && v != h && seesBit mw u && seesBit mw v then
            let su := suNat == 1
            let sw := swNat == 1
            match litForb ctx su (7 + zhIdx) h u,
                  litForb ctx (!su) (7 + zhIdx) h v,
                  inTriPairLits ctx pairIdx sw h (7 + wIdx) u v with
            | some l1, some l2, some ls => some (some (l1 :: l2 :: ls), rest)
            | _, _, _ => none
          else none
        | _, _ => none
      | _ => none
    else if tag == 10 then
      -- Tag 10: (C7/C8) Asymmetric two-sided separation: wx, d, u, v, w1, w2, sNat
      match bsReadNats 7 [] cs1 with
      | some ([wx, d, u, v, w1, w2, sNat], rest) =>
        match getMask ctx wx, getMask ctx w1, getMask ctx w2 with
        | some mx, some m1, some m2 =>
          if d < 7 && u < 7 && v < 7 && u != v &&
             !seesBit mx d && seesBit mx u && seesBit mx v &&
             seesBit m1 d && seesBit m1 u && seesBit m2 d && seesBit m2 v then
            let s := sNat == 1
            match optSequence [
              litForb ctx s d (7 + wx) u,
              litForb ctx (!s) d (7 + wx) v,
              litForb ctx s d (7 + wx) (7 + w1),
              litForb ctx (!s) d (7 + wx) (7 + w2)
            ] with
            | some cl => some (some cl, rest)
            | none => none
          else none
        | _, _, _ => none
      | _ => none
    else if tag == 11 then
      -- Tag 11: (C8/C9) Half-Plane Lemma pure chirotope clause:
      -- wv, wq, a, p, c, sigNat, saNat, ivKind, iv1, iv2, conclKind, wx, wy
      match bsReadNats 13 [] cs1 with
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
              litForb ctx sig v q p,
              litForb ctx sig v q a,
              litForb ctx sig v q c,
              litForb ctx sig v a p,
              litForb ctx sig v p c,
              litForb ctx sa a c v,
              litForb ctx (!sa) a c p
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
      | _ => none
    else if tag == 12 then
      -- Tag 12: (C11) vis_SS Round-2 vertex clause: a, b, w1, w2, w3, wf, soppNat, sdNat
      match bsReadNats 8 [] cs1 with
      | some ([a, b, w1, w2, w3, wf, soppNat, sdNat], rest) =>
        match getMask ctx w1, getMask ctx w2, getMask ctx w3, getMask ctx wf with
        | some m1, some m2, some m3, some mf =>
          if a < b && b < 7 &&
             seesBit m1 a && seesBit m1 b &&
             seesBit m2 a && seesBit m2 b &&
             seesBit m3 a && seesBit m3 b &&
             (!seesBit mf a || !seesBit mf b) then
            let sopp := soppNat == 1
            let sd := sdNat == 1
            match litForb ctx sopp a b (7 + w1),
                  litForb ctx (!sopp) a b (7 + w2),
                  notInTriSideLits ctx sd (7 + wf) (7 + w3) a b with
            | some l1, some l2, some ls => some (some (l1 :: l2 :: ls), rest)
            | _, _, _ => none
          else none
        | _, _, _, _ => none
      | _ => none
    else if tag == 13 then
      -- Tag 13: (C11) vis_SS Round-2 pair clause: a, b, fj, w1, w2, w3, wf, soppNat, sdwNat, sdjNat
      match bsReadNats 10 [] cs1 with
      | some ([a, b, fj, w1, w2, w3, wf, soppNat, sdwNat, sdjNat], rest) =>
        match getMask ctx w1, getMask ctx w2, getMask ctx w3, getMask ctx wf with
        | some m1, some m2, some m3, some mf =>
          if a < b && b < 7 && fj < 7 && fj != a && fj != b && w3 != wf &&
             seesBit m1 a && seesBit m1 b &&
             seesBit m2 a && seesBit m2 b &&
             seesBit m3 a && seesBit m3 b &&
             !seesBit mf fj then
            let sopp := soppNat == 1
            let sdw := sdwNat == 1
            let sdj := sdjNat == 1
            match litForb ctx sopp a b (7 + w1),
                  litForb ctx (!sopp) a b (7 + w2),
                  notInTriSideLits ctx sdw (7 + wf) (7 + w3) a b,
                  notInTriSideLits ctx sdj fj (7 + w3) a b with
            | some l1, some l2, some lsw, some lsj => some (some (l1 :: l2 :: (lsw ++ lsj)), rest)
            | _, _, _, _ => none
          else none
        | _, _, _, _ => none
      | _ => none
    else if tag == 14 then
      -- Tag 14: (C10) N1 convex quad: a, b, w1, w2, wf, sNat
      match bsReadNats 6 [] cs1 with
      | some ([a, b, w1, w2, wf, sNat], rest) =>
        match getMask ctx w1, getMask ctx w2, getMask ctx wf with
        | some m1, some m2, some mf =>
          if a < 7 && b < 7 && a != b && w1 != w2 && wf != w1 && wf != w2 &&
             seesBit m1 a && seesBit m1 b && seesBit m2 a && seesBit m2 b &&
             (!seesBit mf a || !seesBit mf b) then
            let s := sNat == 1
            let p0 := 7 + w1; let p1 := a; let p2 := 7 + w2; let p3 := b; let fw := 7 + wf
            match optSequence [
              litForb ctx s p0 p1 p2, litForb ctx s p1 p2 p3,
              litForb ctx s p2 p3 p0, litForb ctx s p3 p0 p1,
              litForb ctx s p0 p1 fw, litForb ctx s p1 p2 fw,
              litForb ctx s p2 p3 fw, litForb ctx s p3 p0 fw
            ] with
            | some cl => some (some cl, rest)
            | none => none
          else none
        | _, _, _ => none
      | _ => none
    else if tag == 15 || tag == 17 then
      -- Tag 15 (r=0) / Tag 17 (r=2): N1 dart with sameSide: a, b, w1, w2, wf, sdNat, ssNat
      match bsReadNats 7 [] cs1 with
      | some ([a, b, w1, w2, wf, sdNat, ssNat], rest) =>
        match getMask ctx w1, getMask ctx w2, getMask ctx wf with
        | some m1, some m2, some mf =>
          if a < 7 && b < 7 && a != b && w1 != w2 && wf != w1 && wf != w2 &&
             seesBit m1 a && seesBit m1 b && seesBit m2 a && seesBit m2 b && !seesBit mf a then
            let sd := sdNat == 1
            let ss := ssNat == 1
            let vr := if tag == 15 then 7 + w1 else 7 + w2
            let vp := if tag == 15 then a else b
            let vq := if tag == 15 then 7 + w2 else 7 + w1
            let vs := if tag == 15 then b else a
            let sideRef := a
            match notInTriSideLits ctx sd vr vp vq vs,
                  notInTriSideLits ctx sd (7 + wf) vp vq vs,
                  litForb ctx ss vr sideRef (7 + wf),
                  litForb ctx ss vr sideRef vq with
            | some ls1, some ls2, some l3, some l4 => some (some (ls1 ++ ls2 ++ [l3, l4]), rest)
            | _, _, _, _ => none
          else none
        | _, _, _ => none
      | _ => none
    else if tag == 16 || tag == 18 then
      -- Tag 16 (r=1) / Tag 18 (r=3): N1 dart sub-triangle: a, b, w1, w2, wf, sdNat, stNat, subIdx
      match bsReadNats 8 [] cs1 with
      | some ([a, b, w1, w2, wf, sdNat, stNat, subIdx], rest) =>
        match getMask ctx w1, getMask ctx w2, getMask ctx wf with
        | some m1, some m2, some mf =>
          if a < 7 && b < 7 && a != b && w1 != w2 && wf != w1 && wf != w2 &&
             seesBit m1 a && seesBit m1 b && seesBit m2 a && seesBit m2 b && !seesBit mf a then
            let sd := sdNat == 1
            let st := stNat == 1
            let vr := if tag == 16 then a else b
            let vp := if tag == 16 then 7 + w2 else 7 + w1
            let vq := if tag == 16 then b else a
            let vs := if tag == 16 then 7 + w1 else 7 + w2
            let subOpt :=
              if subIdx == 0 then notInTriSideLits ctx st (7 + wf) vr vp vq
              else if subIdx == 1 then notInTriSideLits ctx st (7 + wf) vr vq vs
              else none
            match notInTriSideLits ctx sd vr vp vq vs, subOpt with
            | some ls1, some ls2 => some (some (ls1 ++ ls2), rest)
            | _, _ => none
          else none
        | _, _, _ => none
      | _ => none
    else if tag == 19 then
      -- Tag 19: (C11) IteratedCut mini-DAG: numSteps, steps..., forbS, forbWIdx
      match bsReadNat cs1 with
      | none => none
      | some (numSteps, cs2) =>
        match decodeIteratedSteps ctx numSteps .leaf [] cs2 with
        | none => none
        | some (et, lits, cs3) =>
          match bsReadNats 2 [] cs3 with
          | some ([forbS, forbWIdx], rest) =>
            match getMask ctx forbWIdx with
            | some mf =>
              if forbS < 7 && !seesBit mf forbS && hasVisEdge ctx et forbS (7 + forbWIdx) then
                some (some lits, rest)
              else none
            | none => none
          | _ => none
    else
      none

/-! ## Bounded-Depth Towers for `TripleTrie` & Core `BinTrie Clause` Construction -/

def stepTriple (n_pts : Nat) (curVar : PIdx) (acc : TripleTrie) (bs : ByteStream) :
    Option (Bool × PIdx × TripleTrie × ByteStream) :=
  match bs.next with
  | none => none
  | some (i, bs1) =>
    match Nat.beq i 255 with
    | true => some (true, curVar, acc, bs1)
    | false =>
      match bs1.next with
      | none => none
      | some (j, bs2) =>
        match bs2.next with
        | none => none
        | some (k, bs3) =>
          match Nat.ble j i || Nat.ble k j || Nat.ble n_pts k with
          | true => none
          | false =>
            withStrictTrie (acc.insert3 (ptKey i) (ptKey j) (ptKey k) curVar) (fun acc' =>
              match strictPIdx curVar.succ with
              | .xH => some (false, .xH, acc', bs3)
              | .xO p => some (false, .xO p, acc', bs3)
              | .xI p => some (false, .xI p, acc', bs3))

def chainStateBlocks {σ : Type}
    (f : PIdx → σ → ByteStream → Option (Bool × PIdx × σ × ByteStream)) :
    Nat → PIdx → σ → ByteStream → Option (Bool × PIdx × σ × ByteStream)
  | 0, cv, acc, bs => some (false, cv, acc, bs)
  | k + 1, cv, acc, bs =>
    match f cv acc bs with
    | none => none
    | some (true, cv', acc', bs') => some (true, cv', acc', bs')
    | some (false, cv', acc', bs') => chainStateBlocks f k cv' acc' bs'

def buildTripleTower (n_pts : Nat) : Nat → PIdx → TripleTrie → ByteStream →
    Option (Bool × PIdx × TripleTrie × ByteStream)
  | 0 => chainStateBlocks (stepTriple n_pts) 16
  | lvl + 1 => chainStateBlocks (buildTripleTower n_pts lvl) 16

def buildTripleTrieTree (n_pts : Nat) (varTree : ChunkTree) : Option TripleTrie :=
  match buildTripleTower n_pts 3 .xH .leaf (ByteStream.ofTree varTree) with
  | some (true, _, acc, _) => some acc
  | _ => none

def stepCoreClause (ctx : CertCtx) (cid : PIdx) (db : BinTrie Clause) (bs : ByteStream) :
    Option (Bool × PIdx × BinTrie Clause × ByteStream) :=
  match decodeOneJust ctx bs with
  | none => none
  | some (none, bs') => some (true, cid, db, bs')
  | some (some cl, bs') =>
    let cl' := strictClause cl
    withStrictTrie (db.insert cid cl') (fun db' =>
      match strictPIdx cid.succ with
      | .xH => some (false, .xH, db', bs')
      | .xO p => some (false, .xO p, db', bs')
      | .xI p => some (false, .xI p, db', bs'))

def buildCoreTower (ctx : CertCtx) : Nat → PIdx → BinTrie Clause → ByteStream →
    Option (Bool × PIdx × BinTrie Clause × ByteStream)
  | 0 => chainStateBlocks (stepCoreClause ctx) 16
  | lvl + 1 => chainStateBlocks (buildCoreTower ctx lvl) 16

def buildCoreDBTree (ctx : CertCtx) (justTree : ChunkTree) : Option (BinTrie Clause) :=
  match buildCoreTower ctx 4 .xH .leaf (ByteStream.ofTree justTree) with
  | some (true, _, db, _) => some db
  | _ => none

/-- Master zero-Mathlib kernel certificate verifier for a canonical case `spec` over `ChunkTree`s. -/
def checkCaseCert (spec : CaseSpec) (varTree justTree rupTree : ChunkTree) : Bool :=
  let n_pts := 7 + spec.masks.length
  match buildTripleTrieTree n_pts varTree with
  | none => false
  | some tripleTrie =>
    let ctx : CertCtx := {
      spec := spec
      n_pts := n_pts
      bccw := buildBccw spec
      ptKeyTrie := .leaf
      maskTrie := buildMaskTrieAux .xH spec.masks .leaf
      tripleTrie := tripleTrie
    }
    match buildCoreDBTree ctx justTree with
    | none => false
    | some db => checkTreeRUP db rupTree

end

end VCDim6.FastTrieRUP
