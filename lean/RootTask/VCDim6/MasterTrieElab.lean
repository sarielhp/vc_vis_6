import Lean.Elab.Term
import RootTask.VCDim6.MasterTableRUP

/-!
# Zero-`OfNat` DAG-Shared Direct-`Expr` Elaborators for `BinTrie Clause`, `List (List PIdx)`, and `ChunkTree`

Constructs `BinTrie Clause` (`mk_clause_trie`), `List (List PIdx)` (`mk_rup_steps`), `List PIdx`
(`mk_pidx_list`), `PIdx` (`mk_pidx`), and `ChunkTree` (`mk_chunk_tree`) kernel terms directly in C++/Lean
elaboration with DAG-shared `PIdx` and `Lit` subterms and zero `OfNat` syntheses.
-/

namespace VCDim6.FastTrieRUP

open Lean Elab Term

private def hexDigitVal (b : UInt8) : Nat :=
  if 48 ≤ b && b ≤ 57 then (b - 48).toNat
  else if 97 ≤ b && b ≤ 102 then (b - 87).toNat
  else if 65 ≤ b && b ≤ 70 then (b - 55).toNat
  else 0

private partial def mkPIdxExpr (n : Nat) (cXH cXO cXI : Expr) : Expr :=
  if n ≤ 1 then cXH
  else
    let sub := mkPIdxExpr (n / 2) cXH cXO cXI
    if n % 2 == 0 then mkApp cXO sub else mkApp cXI sub

elab "mk_pidx " n:num : term => do
  let v := n.getNat
  return mkPIdxExpr v (Lean.mkConst ``PIdx.xH) (Lean.mkConst ``PIdx.xO) (Lean.mkConst ``PIdx.xI)

/-- Builds shared `Array Expr` of positive and negative `Lit`s for `1 .. maxVar`. -/
private def buildLitTables (maxVar : Nat) : Array Expr × Array Expr := Id.run do
  let cXH := Lean.mkConst ``PIdx.xH
  let cXO := Lean.mkConst ``PIdx.xO
  let cXI := Lean.mkConst ``PIdx.xI
  let tBool := Lean.mkConst ``Bool
  let tPIdx := Lean.mkConst ``PIdx
  let cTrue := Lean.mkConst ``Bool.true
  let cFalse := Lean.mkConst ``Bool.false
  let cProdMk := Lean.mkConst ``Prod.mk [Level.zero, Level.zero]
  let mut pArr : Array Expr := Array.mkEmpty (maxVar + 1)
  let mut posArr : Array Expr := Array.mkEmpty (maxVar + 1)
  let mut negArr : Array Expr := Array.mkEmpty (maxVar + 1)
  pArr := pArr.push cXH
  posArr := posArr.push (mkApp4 cProdMk tBool tPIdx cTrue cXH)
  negArr := negArr.push (mkApp4 cProdMk tBool tPIdx cFalse cXH)
  for v in [1 : maxVar + 1] do
    let pe :=
      if v == 1 then cXH
      else
        let half := pArr[v / 2]!
        if v % 2 == 0 then mkApp cXO half else mkApp cXI half
    pArr := pArr.push pe
    posArr := posArr.push (mkApp4 cProdMk tBool tPIdx cTrue pe)
    negArr := negArr.push (mkApp4 cProdMk tBool tPIdx cFalse pe)
  return (posArr, negArr)

/-- Preorder format of `mk_clause_trie maxVar "..."`:
    - `.` (followed by optional `,`) => `BinTrie.leaf`
    - `-` (followed by optional `,`) => `BinTrie.node none l r`
    - `<hex_lit>+<hex_lit>+...` (ending at `,`, where `u = 2*v` for `+v` and `2*v+1` for `-v`,
      or `0` for empty clause `[]`) => `BinTrie.node (some cl) l r`. -/
private partial def parseClauseTrieBytes (bs : ByteArray) (n : Nat) (i : Nat)
    (posArr negArr : Array Expr)
    (tClause cLeaf cNode cNone cSome cNil cCons : Expr) : Expr × Nat :=
  if i ≥ n then (cLeaf, i)
  else
    let b0 := bs.get! i
    if b0 == 46 then -- '.' => .leaf
      let i' := if i + 1 < n && bs.get! (i + 1) == 44 then i + 2 else i + 1
      (cLeaf, i')
    else if b0 == 45 then -- '-' => .node none l r
      let i1 := if i + 1 < n && bs.get! (i + 1) == 44 then i + 2 else i + 1
      let (l, i2) := parseClauseTrieBytes bs n i1 posArr negArr tClause cLeaf cNode cNone cSome cNil cCons
      let (r, i3) := parseClauseTrieBytes bs n i2 posArr negArr tClause cLeaf cNode cNone cSome cNil cCons
      (mkApp4 cNode tClause cNone l r, i3)
    else
      let rec readLits (j : Nat) (acc : Array Expr) : Array Expr × Nat :=
        let rec readHex (k : Nat) (v : Nat) : Nat × Nat :=
          if k ≥ n then (v, k)
          else
            let bk := bs.get! k
            if bk == 43 || bk == 44 then (v, k) -- '+' or ','
            else readHex (k + 1) (v * 16 + hexDigitVal bk)
        let (code, j1) := readHex j 0
        let acc' :=
          if code == 0 then acc
          else
            let v := code / 2
            let le := if code % 2 == 0 then posArr[v]! else negArr[v]!
            acc.push le
        if j1 ≥ n then (acc', j1)
        else if bs.get! j1 == 44 then (acc', j1 + 1) -- ','
        else readLits (j1 + 1) acc' -- skip '+'
      let (lits, i1) := readLits i #[]
      let clExpr := Id.run do
        let mut cur := cNil
        let mut idx := lits.size
        while idx > 0 do
          idx := idx - 1
          cur := mkApp2 cCons lits[idx]! cur
        return cur
      let optExpr := mkApp2 cSome tClause clExpr
      let (l, i2) := parseClauseTrieBytes bs n i1 posArr negArr tClause cLeaf cNode cNone cSome cNil cCons
      let (r, i3) := parseClauseTrieBytes bs n i2 posArr negArr tClause cLeaf cNode cNone cSome cNil cCons
      (mkApp4 cNode tClause optExpr l r, i3)

elab "mk_clause_trie " mv:num s:str : term => do
  let maxVar := mv.getNat
  let (posArr, negArr) := buildLitTables maxVar
  let bs := s.getString.toUTF8
  let tLit := mkApp2 (Lean.mkConst ``Prod [Level.zero, Level.zero]) (Lean.mkConst ``Bool) (Lean.mkConst ``PIdx)
  let tClause := mkApp (Lean.mkConst ``List [Level.zero]) tLit
  let cLeaf := mkApp (Lean.mkConst ``BinTrie.leaf) tClause
  let cNode := Lean.mkConst ``BinTrie.node
  let cNone := mkApp (Lean.mkConst ``Option.none [Level.zero]) tClause
  let cSome := Lean.mkConst ``Option.some [Level.zero]
  let cNil := mkApp (Lean.mkConst ``List.nil [Level.zero]) tLit
  let cCons := mkApp (Lean.mkConst ``List.cons [Level.zero]) tLit
  let (e, _) := parseClauseTrieBytes bs bs.size 0 posArr negArr tClause cLeaf cNode cNone cSome cNil cCons
  return e

/-- Builds shared `Array Expr` of `PIdx` only on demand via a hash map, or computes via shared low bits!
    Using a 16-bit prefix cache (`1 .. 65535`) shares subtrees across all `PIdx`s up to millions! -/
private def buildPIdxLowCache : Array Expr := Id.run do
  let cXH := Lean.mkConst ``PIdx.xH
  let cXO := Lean.mkConst ``PIdx.xO
  let cXI := Lean.mkConst ``PIdx.xI
  let mut arr : Array Expr := Array.mkEmpty 65536
  arr := arr.push cXH
  for v in [1 : 65536] do
    let pe :=
      if v == 1 then cXH
      else
        let half := arr[v / 2]!
        if v % 2 == 0 then mkApp cXO half else mkApp cXI half
    arr := arr.push pe
  return arr

private partial def fastMkPIdx (v : Nat) (cache : Array Expr) (cXO cXI : Expr) : Expr :=
  if v < 65536 then cache[v]!
  else
    let sub := fastMkPIdx (v / 2) cache cXO cXI
    if v % 2 == 0 then mkApp cXO sub else mkApp cXI sub

/-- Format of `mk_rup_steps "..."`: semicolon-separated steps, each comma-separated hex 1-based `PIdx`s:
    `"h1,h2,h3;h4,h5;..."` (empty string `""` => `[]`). -/
elab "mk_rup_steps " s:str : term => do
  let bs := s.getString.toUTF8
  let cache := buildPIdxLowCache
  let cXO := Lean.mkConst ``PIdx.xO
  let cXI := Lean.mkConst ``PIdx.xI
  let tPIdx := Lean.mkConst ``PIdx
  let tListPIdx := mkApp (Lean.mkConst ``List [Level.zero]) tPIdx
  let cNilP := mkApp (Lean.mkConst ``List.nil [Level.zero]) tPIdx
  let cConsP := mkApp (Lean.mkConst ``List.cons [Level.zero]) tPIdx
  let cNilStep := mkApp (Lean.mkConst ``List.nil [Level.zero]) tListPIdx
  let cConsStep := mkApp (Lean.mkConst ``List.cons [Level.zero]) tListPIdx
  if bs.size == 0 then
    return cNilStep
  return Id.run do
    let n := bs.size
    let mut steps : Array Expr := #[]
    let mut curHints : Array Expr := #[]
    let mut acc : Nat := 0
    let mut hasHex : Bool := false
    for idx in [0 : n] do
      let b := bs.get! idx
      if b == 44 then -- ','
        if hasHex then
          curHints := curHints.push (fastMkPIdx acc cache cXO cXI)
          acc := 0
          hasHex := false
      else if b == 59 then -- ';'
        if hasHex then
          curHints := curHints.push (fastMkPIdx acc cache cXO cXI)
          acc := 0
          hasHex := false
        let mut hList := cNilP
        let mut k := curHints.size
        while k > 0 do
          k := k - 1
          hList := mkApp2 cConsP curHints[k]! hList
        steps := steps.push hList
        curHints := #[]
      else
        acc := acc * 16 + hexDigitVal b
        hasHex := true
    if hasHex || curHints.size > 0 then
      if hasHex then
        curHints := curHints.push (fastMkPIdx acc cache cXO cXI)
      let mut hList := cNilP
      let mut k := curHints.size
      while k > 0 do
        k := k - 1
        hList := mkApp2 cConsP curHints[k]! hList
      steps := steps.push hList
    let mut res := cNilStep
    let mut m := steps.size
    while m > 0 do
      m := m - 1
      res := mkApp2 cConsStep steps[m]! res
    return res

/-- Format of `mk_pidx_list "..."`: comma-separated hex 1-based `PIdx`s (`"h1,h2,..."`). -/
elab "mk_pidx_list " s:str : term => do
  let bs := s.getString.toUTF8
  let cache := buildPIdxLowCache
  let cXO := Lean.mkConst ``PIdx.xO
  let cXI := Lean.mkConst ``PIdx.xI
  let tPIdx := Lean.mkConst ``PIdx
  let cNilP := mkApp (Lean.mkConst ``List.nil [Level.zero]) tPIdx
  let cConsP := mkApp (Lean.mkConst ``List.cons [Level.zero]) tPIdx
  if bs.size == 0 then
    return cNilP
  return Id.run do
    let n := bs.size
    let mut curHints : Array Expr := #[]
    let mut acc : Nat := 0
    let mut hasHex : Bool := false
    for idx in [0 : n] do
      let b := bs.get! idx
      if b == 44 then
        if hasHex then
          curHints := curHints.push (fastMkPIdx acc cache cXO cXI)
          acc := 0
          hasHex := false
      else
        acc := acc * 16 + hexDigitVal b
        hasHex := true
    if hasHex then
      curHints := curHints.push (fastMkPIdx acc cache cXO cXI)
    let mut hList := cNilP
    let mut k := curHints.size
    while k > 0 do
      k := k - 1
      hList := mkApp2 cConsP curHints[k]! hList
    return hList

private partial def buildBalancedChunkExpr (arr : Array Expr) (lo hi : Nat) (cNode : Expr) : Expr :=
  if hi - lo ≤ 1 then arr[lo]!
  else
    let mid := (lo + hi) / 2
    mkApp2 cNode (buildBalancedChunkExpr arr lo mid cNode)
                 (buildBalancedChunkExpr arr mid hi cNode)

private partial def parseChunkLeaves (bs : ByteArray) (n : Nat) (i : Nat)
    (cLeaf : Expr) (acc : Array Expr) : Array Expr :=
  if i ≥ n then acc
  else
    let rec readHex (j : Nat) (v : Nat) : Nat × Nat :=
      if j ≥ n then (v, j)
      else
        let bj := bs.get! j
        if bj == 44 then (v, j + 1)
        else readHex (j + 1) (v * 16 + hexDigitVal bj)
    let (w, i1) := readHex i 0
    parseChunkLeaves bs n i1 cLeaf (acc.push (mkApp cLeaf (mkRawNatLit w)))

elab "mk_chunk_tree " s:str : term => do
  let bs := s.getString.toUTF8
  let cLeaf := Lean.mkConst ``ChunkTree.leaf
  let cNode := Lean.mkConst ``ChunkTree.node
  if bs.size == 0 then
    return mkApp cLeaf (mkRawNatLit 0)
  let leaves := parseChunkLeaves bs bs.size 0 cLeaf #[]
  return buildBalancedChunkExpr leaves 0 leaves.size cNode

end VCDim6.FastTrieRUP
