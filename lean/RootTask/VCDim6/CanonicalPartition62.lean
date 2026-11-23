import RootTask.VCDim6.GeometricCanonicalization
import RootTask.VCDim6.CasesUnsat

noncomputable section

namespace VCDim6

/-!
# Dispatch of the 62 Monotone Canonical Skeletons (`CanonicalPartition62.lean`)

Dispatches each of the 62 monotone canonical skeletons `canonSpec c` (`c : Fin 62`,
comprising the 5 certified Stage-1 cases `c = 0..4` and the 57 monotone Stage-2 cases
`c = 5..61`) to its pure-kernel `FastTrieRUP` refutation theorem `case01_unsat .. case62_unsat`,
completing the unconditional elimination of all 7-point shattered configurations `no_seven_shattered`.
-/

theorem canon_skeleton_unsat (c : Fin 62) {P : Set (ℝ × ℝ)}
    {S : Fin 7 → ℝ × ℝ} {w : Finset (Fin 7) → ℝ × ℝ}
    (hV : ValidCanonicalInstance P S w (canonSpec c)) : False := by
  match c with
  | ⟨0, _⟩ => exact case01_unsat (hV.withMasks Cases.case01_spec.masks)
  | ⟨1, _⟩ => exact case02_unsat (hV.withMasks Cases.case02_spec.masks)
  | ⟨2, _⟩ => exact case03_unsat (hV.withMasks Cases.case03_spec.masks)
  | ⟨3, _⟩ => exact case04_unsat (hV.withMasks Cases.case04_spec.masks)
  | ⟨4, _⟩ => exact case05_unsat (hV.withMasks Cases.case05_spec.masks)
  | ⟨5, _⟩ => exact case06_unsat (hV.withMasks Cases.case06_spec.masks)
  | ⟨6, _⟩ => exact case07_unsat (hV.withMasks Cases.case07_spec.masks)
  | ⟨7, _⟩ => exact case08_unsat (hV.withMasks Cases.case08_spec.masks)
  | ⟨8, _⟩ => exact case09_unsat (hV.withMasks Cases.case09_spec.masks)
  | ⟨9, _⟩ => exact case10_unsat (hV.withMasks Cases.case10_spec.masks)
  | ⟨10, _⟩ => exact case11_unsat (hV.withMasks Cases.case11_spec.masks)
  | ⟨11, _⟩ => exact case12_unsat (hV.withMasks Cases.case12_spec.masks)
  | ⟨12, _⟩ => exact case13_unsat (hV.withMasks Cases.case13_spec.masks)
  | ⟨13, _⟩ => exact case14_unsat (hV.withMasks Cases.case14_spec.masks)
  | ⟨14, _⟩ => exact case15_unsat (hV.withMasks Cases.case15_spec.masks)
  | ⟨15, _⟩ => exact case16_unsat (hV.withMasks Cases.case16_spec.masks)
  | ⟨16, _⟩ => exact case17_unsat (hV.withMasks Cases.case17_spec.masks)
  | ⟨17, _⟩ => exact case18_unsat (hV.withMasks Cases.case18_spec.masks)
  | ⟨18, _⟩ => exact case19_unsat (hV.withMasks Cases.case19_spec.masks)
  | ⟨19, _⟩ => exact case20_unsat (hV.withMasks Cases.case20_spec.masks)
  | ⟨20, _⟩ => exact case21_unsat (hV.withMasks Cases.case21_spec.masks)
  | ⟨21, _⟩ => exact case22_unsat (hV.withMasks Cases.case22_spec.masks)
  | ⟨22, _⟩ => exact case23_unsat (hV.withMasks Cases.case23_spec.masks)
  | ⟨23, _⟩ => exact case24_unsat (hV.withMasks Cases.case24_spec.masks)
  | ⟨24, _⟩ => exact case25_unsat (hV.withMasks Cases.case25_spec.masks)
  | ⟨25, _⟩ => exact case26_unsat (hV.withMasks Cases.case26_spec.masks)
  | ⟨26, _⟩ => exact case27_unsat (hV.withMasks Cases.case27_spec.masks)
  | ⟨27, _⟩ => exact case28_unsat (hV.withMasks Cases.case28_spec.masks)
  | ⟨28, _⟩ => exact case29_unsat (hV.withMasks Cases.case29_spec.masks)
  | ⟨29, _⟩ => exact case30_unsat (hV.withMasks Cases.case30_spec.masks)
  | ⟨30, _⟩ => exact case31_unsat (hV.withMasks Cases.case31_spec.masks)
  | ⟨31, _⟩ => exact case32_unsat (hV.withMasks Cases.case32_spec.masks)
  | ⟨32, _⟩ => exact case33_unsat (hV.withMasks Cases.case33_spec.masks)
  | ⟨33, _⟩ => exact case34_unsat (hV.withMasks Cases.case34_spec.masks)
  | ⟨34, _⟩ => exact case35_unsat (hV.withMasks Cases.case35_spec.masks)
  | ⟨35, _⟩ => exact case36_unsat (hV.withMasks Cases.case36_spec.masks)
  | ⟨36, _⟩ => exact case37_unsat (hV.withMasks Cases.case37_spec.masks)
  | ⟨37, _⟩ => exact case38_unsat (hV.withMasks Cases.case38_spec.masks)
  | ⟨38, _⟩ => exact case39_unsat (hV.withMasks Cases.case39_spec.masks)
  | ⟨39, _⟩ => exact case40_unsat (hV.withMasks Cases.case40_spec.masks)
  | ⟨40, _⟩ => exact case41_unsat (hV.withMasks Cases.case41_spec.masks)
  | ⟨41, _⟩ => exact case42_unsat (hV.withMasks Cases.case42_spec.masks)
  | ⟨42, _⟩ => exact case43_unsat (hV.withMasks Cases.case43_spec.masks)
  | ⟨43, _⟩ => exact case44_unsat (hV.withMasks Cases.case44_spec.masks)
  | ⟨44, _⟩ => exact case45_unsat (hV.withMasks Cases.case45_spec.masks)
  | ⟨45, _⟩ => exact case46_unsat (hV.withMasks Cases.case46_spec.masks)
  | ⟨46, _⟩ => exact case47_unsat (hV.withMasks Cases.case47_spec.masks)
  | ⟨47, _⟩ => exact case48_unsat (hV.withMasks Cases.case48_spec.masks)
  | ⟨48, _⟩ => exact case49_unsat (hV.withMasks Cases.case49_spec.masks)
  | ⟨49, _⟩ => exact case50_unsat (hV.withMasks Cases.case50_spec.masks)
  | ⟨50, _⟩ => exact case51_unsat (hV.withMasks Cases.case51_spec.masks)
  | ⟨51, _⟩ => exact case52_unsat (hV.withMasks Cases.case52_spec.masks)
  | ⟨52, _⟩ => exact case53_unsat (hV.withMasks Cases.case53_spec.masks)
  | ⟨53, _⟩ => exact case54_unsat (hV.withMasks Cases.case54_spec.masks)
  | ⟨54, _⟩ => exact case55_unsat (hV.withMasks Cases.case55_spec.masks)
  | ⟨55, _⟩ => exact case56_unsat (hV.withMasks Cases.case56_spec.masks)
  | ⟨56, _⟩ => exact case57_unsat (hV.withMasks Cases.case57_spec.masks)
  | ⟨57, _⟩ => exact case58_unsat (hV.withMasks Cases.case58_spec.masks)
  | ⟨58, _⟩ => exact case59_unsat (hV.withMasks Cases.case59_spec.masks)
  | ⟨59, _⟩ => exact case60_unsat (hV.withMasks Cases.case60_spec.masks)
  | ⟨60, _⟩ => exact case61_unsat (hV.withMasks Cases.case61_spec.masks)
  | ⟨61, _⟩ => exact case62_unsat (hV.withMasks Cases.case62_spec.masks)
  | ⟨_ + 62, h⟩ => omega

/-- No simple polygon `P ⊂ ℝ²` can visibility-shatter any `7`-point set under `(G1)–(G2)`. -/
theorem no_seven_shattered {P : Set (ℝ × ℝ)}
    (S7 : Fin 7 → ℝ × ℝ) (w7 : Finset (Fin 7) → ℝ × ℝ)
    (hP : ShatteredSimplePolygon P S7 w7) : False :=
  no_seven_shattered_of_62_skeletons canon_skeleton_unsat hP

end VCDim6

end
