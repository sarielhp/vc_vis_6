import Mathlib
import RootTask.VCDim6.DihedralSpecSymmetry
import RootTask.VCDim6.Stage1Case70Elim

open scoped Classical BigOperators
open Finset
open PolygonCore NewEnclosure ChirotopeSoundness CertifiedAndHalfPlaneSoundness
open VCDimSixMasterBridge VCDim6.FastTrieRUP

noncomputable section

namespace VCDim6

/-!
# Geometric Canonicalization & Reduction of `Fin 7` to the 62 Monotone Cases

Completes the purely geometric reduction from an arbitrary 7-point shattered configuration
`ShatteredSimplePolygon P S7 w7` to the **62 monotone canonical skeletons** `canonSpec : Fin 62 → CaseSpec`,
matching `vc_dim_6_simplified.tex` Section 3 1-to-1:
1. **Stage 1 (`A = ∅`, `|B| = 7`)**:
   - `(|D|, |H|) = (7, 0)` is eliminated **100% certificate-free** via
     `Stage1Case70Elim.no_unmarked_convex_seven_shattered`.
   - `(|D|, |H|) ∈ {(6, 1), (5, 2), (4, 3), (3, 4), (2, 5)}` maps directly by index relabeling
     along `∂ conv(B)` to `canonSpec 0 .. canonSpec 4` (`Case01 .. Case05`).
2. **Stage 2 (`|B| ≤ 6`, `3 ≤ |B|`)**:
   - `(|D|, |H|) ∈ {(2, 1), (2, 2), (2, 3), (2, 4)}` maps directly by index relabeling along
     `∂ conv(B)` to `canonSpec 58 .. canonSpec 61` (`Case59 .. Case62`).
   - For `3 ≤ |D| ≤ 6`, we extract exit edges on `∂ conv(D)` via `PolygonCore.exit_edge`,
     apply **Lemma 3.4(i)** (`exit_edge_ne_pocket_lr`) to exclude `(l, r)` when `H ≠ ∅`,
     apply **Lemma 3.4(ii)** (`pocket_exit_edge_monotonicity`) to establish
     `ν - 2 ≥ m(h₁) ≥ ... ≥ m(h_k) ≥ 0` (eliminating all 11 non-monotone Stage-2 orbits
     geometrically with zero RUP certificates), and apply `ValidCanonicalInstance.applyDihedralNorm`
     via the verified lookup table `lookupStage2Action` to reach `canonSpec 5 .. canonSpec 57`
     (`Case06 .. Case58`).
-/

/-! ## 1. Canonical 62 Skeletons & Verified 273-Configuration Dihedral Lookup Table -/

def canonSpec : Fin 62 → CaseSpec
  | ⟨0, _⟩ => { n_d := 6, h_sz := 1, lr_l := some 0, edges := [none], masks := [] }
  | ⟨1, _⟩ => { n_d := 5, h_sz := 2, lr_l := some 0, edges := [none, none], masks := [] }
  | ⟨2, _⟩ => { n_d := 4, h_sz := 3, lr_l := some 0, edges := [none, none, none], masks := [] }
  | ⟨3, _⟩ => { n_d := 3, h_sz := 4, lr_l := some 0, edges := [none, none, none, none], masks := [] }
  | ⟨4, _⟩ => { n_d := 2, h_sz := 5, lr_l := some 0, edges := [none, none, none, none, none], masks := [] }
  | ⟨5, _⟩ => { n_d := 6, h_sz := 0, lr_l := none, edges := [some 0], masks := [] }
  | ⟨6, _⟩ => { n_d := 5, h_sz := 0, lr_l := none, edges := [some 0, some 0], masks := [] }
  | ⟨7, _⟩ => { n_d := 5, h_sz := 0, lr_l := none, edges := [some 0, some 1], masks := [] }
  | ⟨8, _⟩ => { n_d := 5, h_sz := 0, lr_l := none, edges := [some 0, some 2], masks := [] }
  | ⟨9, _⟩ => { n_d := 5, h_sz := 1, lr_l := some 4, edges := [some 0, some 0], masks := [] }
  | ⟨10, _⟩ => { n_d := 5, h_sz := 1, lr_l := some 4, edges := [some 0, some 1], masks := [] }
  | ⟨11, _⟩ => { n_d := 5, h_sz := 1, lr_l := some 4, edges := [some 0, some 2], masks := [] }
  | ⟨12, _⟩ => { n_d := 5, h_sz := 1, lr_l := some 4, edges := [some 0, some 3], masks := [] }
  | ⟨13, _⟩ => { n_d := 5, h_sz := 1, lr_l := some 4, edges := [some 1, some 0], masks := [] }
  | ⟨14, _⟩ => { n_d := 5, h_sz := 1, lr_l := some 4, edges := [some 1, some 1], masks := [] }
  | ⟨15, _⟩ => { n_d := 5, h_sz := 1, lr_l := some 4, edges := [some 1, some 2], masks := [] }
  | ⟨16, _⟩ => { n_d := 5, h_sz := 1, lr_l := some 4, edges := [some 1, some 3], masks := [] }
  | ⟨17, _⟩ => { n_d := 4, h_sz := 0, lr_l := none, edges := [some 0, some 0, some 0], masks := [] }
  | ⟨18, _⟩ => { n_d := 4, h_sz := 0, lr_l := none, edges := [some 0, some 0, some 1], masks := [] }
  | ⟨19, _⟩ => { n_d := 4, h_sz := 0, lr_l := none, edges := [some 0, some 0, some 2], masks := [] }
  | ⟨20, _⟩ => { n_d := 4, h_sz := 0, lr_l := none, edges := [some 0, some 1, some 2], masks := [] }
  | ⟨21, _⟩ => { n_d := 4, h_sz := 1, lr_l := some 0, edges := [some 1, some 1, some 1], masks := [] }
  | ⟨22, _⟩ => { n_d := 4, h_sz := 1, lr_l := some 0, edges := [some 1, some 1, some 2], masks := [] }
  | ⟨23, _⟩ => { n_d := 4, h_sz := 1, lr_l := some 0, edges := [some 1, some 1, some 3], masks := [] }
  | ⟨24, _⟩ => { n_d := 4, h_sz := 1, lr_l := some 0, edges := [some 1, some 2, some 2], masks := [] }
  | ⟨25, _⟩ => { n_d := 4, h_sz := 1, lr_l := some 0, edges := [some 1, some 2, some 3], masks := [] }
  | ⟨26, _⟩ => { n_d := 4, h_sz := 1, lr_l := some 0, edges := [some 1, some 3, some 3], masks := [] }
  | ⟨27, _⟩ => { n_d := 4, h_sz := 1, lr_l := some 0, edges := [some 2, some 1, some 1], masks := [] }
  | ⟨28, _⟩ => { n_d := 4, h_sz := 1, lr_l := some 0, edges := [some 2, some 1, some 2], masks := [] }
  | ⟨29, _⟩ => { n_d := 4, h_sz := 1, lr_l := some 0, edges := [some 2, some 1, some 3], masks := [] }
  | ⟨30, _⟩ => { n_d := 4, h_sz := 1, lr_l := some 0, edges := [some 2, some 2, some 2], masks := [] }
  | ⟨31, _⟩ => { n_d := 4, h_sz := 2, lr_l := some 0, edges := [some 1, some 1, some 1], masks := [] }
  | ⟨32, _⟩ => { n_d := 4, h_sz := 2, lr_l := some 0, edges := [some 1, some 1, some 2], masks := [] }
  | ⟨33, _⟩ => { n_d := 4, h_sz := 2, lr_l := some 0, edges := [some 1, some 1, some 3], masks := [] }
  | ⟨34, _⟩ => { n_d := 4, h_sz := 2, lr_l := some 0, edges := [some 2, some 1, some 1], masks := [] }
  | ⟨35, _⟩ => { n_d := 4, h_sz := 2, lr_l := some 0, edges := [some 2, some 1, some 2], masks := [] }
  | ⟨36, _⟩ => { n_d := 4, h_sz := 2, lr_l := some 0, edges := [some 2, some 1, some 3], masks := [] }
  | ⟨37, _⟩ => { n_d := 4, h_sz := 2, lr_l := some 0, edges := [some 2, some 2, some 1], masks := [] }
  | ⟨38, _⟩ => { n_d := 4, h_sz := 2, lr_l := some 0, edges := [some 2, some 2, some 2], masks := [] }
  | ⟨39, _⟩ => { n_d := 4, h_sz := 2, lr_l := some 0, edges := [some 3, some 1, some 1], masks := [] }
  | ⟨40, _⟩ => { n_d := 4, h_sz := 2, lr_l := some 0, edges := [some 3, some 1, some 2], masks := [] }
  | ⟨41, _⟩ => { n_d := 3, h_sz := 0, lr_l := none, edges := [some 0, some 0, some 0, some 0], masks := [] }
  | ⟨42, _⟩ => { n_d := 3, h_sz := 0, lr_l := none, edges := [some 0, some 0, some 0, some 1], masks := [] }
  | ⟨43, _⟩ => { n_d := 3, h_sz := 0, lr_l := none, edges := [some 0, some 0, some 1, some 1], masks := [] }
  | ⟨44, _⟩ => { n_d := 3, h_sz := 0, lr_l := none, edges := [some 0, some 0, some 1, some 2], masks := [] }
  | ⟨45, _⟩ => { n_d := 3, h_sz := 1, lr_l := some 0, edges := [some 1, some 1, some 1, some 1], masks := [] }
  | ⟨46, _⟩ => { n_d := 3, h_sz := 1, lr_l := some 0, edges := [some 1, some 1, some 1, some 2], masks := [] }
  | ⟨47, _⟩ => { n_d := 3, h_sz := 1, lr_l := some 0, edges := [some 1, some 1, some 2, some 2], masks := [] }
  | ⟨48, _⟩ => { n_d := 3, h_sz := 1, lr_l := some 0, edges := [some 1, some 2, some 2, some 2], masks := [] }
  | ⟨49, _⟩ => { n_d := 3, h_sz := 2, lr_l := some 0, edges := [some 1, some 1, some 1, some 1], masks := [] }
  | ⟨50, _⟩ => { n_d := 3, h_sz := 2, lr_l := some 0, edges := [some 1, some 1, some 1, some 2], masks := [] }
  | ⟨51, _⟩ => { n_d := 3, h_sz := 2, lr_l := some 0, edges := [some 1, some 1, some 2, some 2], masks := [] }
  | ⟨52, _⟩ => { n_d := 3, h_sz := 2, lr_l := some 0, edges := [some 2, some 1, some 1, some 1], masks := [] }
  | ⟨53, _⟩ => { n_d := 3, h_sz := 2, lr_l := some 0, edges := [some 2, some 1, some 1, some 2], masks := [] }
  | ⟨54, _⟩ => { n_d := 3, h_sz := 3, lr_l := some 0, edges := [some 1, some 1, some 1, some 1], masks := [] }
  | ⟨55, _⟩ => { n_d := 3, h_sz := 3, lr_l := some 0, edges := [some 1, some 1, some 1, some 2], masks := [] }
  | ⟨56, _⟩ => { n_d := 3, h_sz := 3, lr_l := some 0, edges := [some 2, some 1, some 1, some 1], masks := [] }
  | ⟨57, _⟩ => { n_d := 3, h_sz := 3, lr_l := some 0, edges := [some 2, some 1, some 1, some 2], masks := [] }
  | ⟨58, _⟩ => { n_d := 2, h_sz := 1, lr_l := some 0, edges := [none, none, none, none, none], masks := [] }
  | ⟨59, _⟩ => { n_d := 2, h_sz := 2, lr_l := some 0, edges := [none, none, none, none, none], masks := [] }
  | ⟨60, _⟩ => { n_d := 2, h_sz := 3, lr_l := some 0, edges := [none, none, none, none, none], masks := [] }
  | ⟨61, _⟩ => { n_d := 2, h_sz := 4, lr_l := some 0, edges := [none, none, none, none, none], masks := [] }
  | ⟨_ + 62, h⟩ => by omega

def lookupStage2Action (n_d h_sz : ℕ) (raw : List ℕ) : Fin 62 × Bool × ℕ × List ℕ :=
  match n_d, h_sz, raw with
  | 3, 0, [0, 0, 0, 0] => (⟨41, by decide⟩, false, 0, [])
  | 3, 0, [0, 0, 0, 1] => (⟨42, by decide⟩, false, 0, [])
  | 3, 0, [0, 0, 0, 2] => (⟨42, by decide⟩, true, 0, [])
  | 3, 0, [0, 0, 1, 0] => (⟨42, by decide⟩, false, 0, [2])
  | 3, 0, [0, 0, 1, 1] => (⟨43, by decide⟩, false, 0, [])
  | 3, 0, [0, 0, 1, 2] => (⟨44, by decide⟩, false, 0, [])
  | 3, 0, [0, 0, 2, 0] => (⟨42, by decide⟩, true, 0, [2])
  | 3, 0, [0, 0, 2, 1] => (⟨44, by decide⟩, false, 0, [2])
  | 3, 0, [0, 0, 2, 2] => (⟨43, by decide⟩, false, 1, [1, 0, 2, 1])
  | 3, 0, [0, 1, 0, 0] => (⟨42, by decide⟩, false, 0, [1, 2])
  | 3, 0, [0, 1, 0, 1] => (⟨43, by decide⟩, false, 0, [1])
  | 3, 0, [0, 1, 0, 2] => (⟨44, by decide⟩, false, 0, [1])
  | 3, 0, [0, 1, 1, 0] => (⟨43, by decide⟩, false, 0, [2, 1])
  | 3, 0, [0, 1, 1, 1] => (⟨42, by decide⟩, true, 1, [0, 1, 2])
  | 3, 0, [0, 1, 1, 2] => (⟨44, by decide⟩, false, 2, [0, 1, 2])
  | 3, 0, [0, 1, 2, 0] => (⟨44, by decide⟩, false, 0, [2, 1])
  | 3, 0, [0, 1, 2, 1] => (⟨44, by decide⟩, false, 2, [0, 1, 2, 1])
  | 3, 0, [0, 1, 2, 2] => (⟨44, by decide⟩, false, 1, [1, 0, 2, 1])
  | 3, 0, [0, 2, 0, 0] => (⟨42, by decide⟩, true, 0, [1, 2])
  | 3, 0, [0, 2, 0, 1] => (⟨44, by decide⟩, false, 0, [1, 2])
  | 3, 0, [0, 2, 0, 2] => (⟨43, by decide⟩, false, 1, [0, 2, 1])
  | 3, 0, [0, 2, 1, 0] => (⟨44, by decide⟩, false, 0, [1, 2, 1])
  | 3, 0, [0, 2, 1, 1] => (⟨44, by decide⟩, false, 2, [0, 1, 0, 2, 1])
  | 3, 0, [0, 2, 1, 2] => (⟨44, by decide⟩, false, 1, [0, 2, 1])
  | 3, 0, [0, 2, 2, 0] => (⟨43, by decide⟩, false, 1, [0, 1])
  | 3, 0, [0, 2, 2, 1] => (⟨44, by decide⟩, false, 1, [0, 1])
  | 3, 0, [0, 2, 2, 2] => (⟨42, by decide⟩, false, 1, [0, 1, 2])
  | 3, 0, [1, 0, 0, 0] => (⟨42, by decide⟩, false, 0, [0, 1, 2])
  | 3, 0, [1, 0, 0, 1] => (⟨43, by decide⟩, false, 0, [0, 1])
  | 3, 0, [1, 0, 0, 2] => (⟨44, by decide⟩, false, 0, [0, 1])
  | 3, 0, [1, 0, 1, 0] => (⟨43, by decide⟩, false, 0, [0, 2, 1])
  | 3, 0, [1, 0, 1, 1] => (⟨42, by decide⟩, true, 1, [1, 2])
  | 3, 0, [1, 0, 1, 2] => (⟨44, by decide⟩, false, 2, [1, 2])
  | 3, 0, [1, 0, 2, 0] => (⟨44, by decide⟩, false, 0, [0, 2, 1])
  | 3, 0, [1, 0, 2, 1] => (⟨44, by decide⟩, false, 2, [1, 2, 1])
  | 3, 0, [1, 0, 2, 2] => (⟨44, by decide⟩, false, 1, [0, 1, 0, 2, 1])
  | 3, 0, [1, 1, 0, 0] => (⟨43, by decide⟩, false, 0, [1, 0, 2, 1])
  | 3, 0, [1, 1, 0, 1] => (⟨42, by decide⟩, true, 1, [2])
  | 3, 0, [1, 1, 0, 2] => (⟨44, by decide⟩, false, 2, [2])
  | 3, 0, [1, 1, 1, 0] => (⟨42, by decide⟩, true, 1, [])
  | 3, 0, [1, 1, 1, 1] => (⟨41, by decide⟩, false, 2, [])
  | 3, 0, [1, 1, 1, 2] => (⟨42, by decide⟩, false, 2, [])
  | 3, 0, [1, 1, 2, 0] => (⟨44, by decide⟩, false, 2, [])
  | 3, 0, [1, 1, 2, 1] => (⟨42, by decide⟩, false, 2, [2])
  | 3, 0, [1, 1, 2, 2] => (⟨43, by decide⟩, false, 2, [])
  | 3, 0, [1, 2, 0, 0] => (⟨44, by decide⟩, false, 0, [1, 0, 2, 1])
  | 3, 0, [1, 2, 0, 1] => (⟨44, by decide⟩, false, 2, [2, 1])
  | 3, 0, [1, 2, 0, 2] => (⟨44, by decide⟩, false, 1, [0, 1, 2, 1])
  | 3, 0, [1, 2, 1, 0] => (⟨44, by decide⟩, false, 2, [1])
  | 3, 0, [1, 2, 1, 1] => (⟨42, by decide⟩, false, 2, [1, 2])
  | 3, 0, [1, 2, 1, 2] => (⟨43, by decide⟩, false, 2, [1])
  | 3, 0, [1, 2, 2, 0] => (⟨44, by decide⟩, false, 1, [0, 1, 2])
  | 3, 0, [1, 2, 2, 1] => (⟨43, by decide⟩, false, 2, [2, 1])
  | 3, 0, [1, 2, 2, 2] => (⟨42, by decide⟩, true, 2, [0, 1, 2])
  | 3, 0, [2, 0, 0, 0] => (⟨42, by decide⟩, true, 0, [0, 1, 2])
  | 3, 0, [2, 0, 0, 1] => (⟨44, by decide⟩, false, 0, [0, 1, 2])
  | 3, 0, [2, 0, 0, 2] => (⟨43, by decide⟩, false, 1, [2, 1])
  | 3, 0, [2, 0, 1, 0] => (⟨44, by decide⟩, false, 0, [0, 1, 2, 1])
  | 3, 0, [2, 0, 1, 1] => (⟨44, by decide⟩, false, 2, [1, 0, 2, 1])
  | 3, 0, [2, 0, 1, 2] => (⟨44, by decide⟩, false, 1, [2, 1])
  | 3, 0, [2, 0, 2, 0] => (⟨43, by decide⟩, false, 1, [1])
  | 3, 0, [2, 0, 2, 1] => (⟨44, by decide⟩, false, 1, [1])
  | 3, 0, [2, 0, 2, 2] => (⟨42, by decide⟩, false, 1, [1, 2])
  | 3, 0, [2, 1, 0, 0] => (⟨44, by decide⟩, false, 0, [0, 1, 0, 2, 1])
  | 3, 0, [2, 1, 0, 1] => (⟨44, by decide⟩, false, 2, [0, 2, 1])
  | 3, 0, [2, 1, 0, 2] => (⟨44, by decide⟩, false, 1, [1, 2, 1])
  | 3, 0, [2, 1, 1, 0] => (⟨44, by decide⟩, false, 2, [0, 1])
  | 3, 0, [2, 1, 1, 1] => (⟨42, by decide⟩, false, 2, [0, 1, 2])
  | 3, 0, [2, 1, 1, 2] => (⟨43, by decide⟩, false, 2, [0, 1])
  | 3, 0, [2, 1, 2, 0] => (⟨44, by decide⟩, false, 1, [1, 2])
  | 3, 0, [2, 1, 2, 1] => (⟨43, by decide⟩, false, 2, [0, 2, 1])
  | 3, 0, [2, 1, 2, 2] => (⟨42, by decide⟩, true, 2, [1, 2])
  | 3, 0, [2, 2, 0, 0] => (⟨43, by decide⟩, false, 1, [])
  | 3, 0, [2, 2, 0, 1] => (⟨44, by decide⟩, false, 1, [])
  | 3, 0, [2, 2, 0, 2] => (⟨42, by decide⟩, false, 1, [2])
  | 3, 0, [2, 2, 1, 0] => (⟨44, by decide⟩, false, 1, [2])
  | 3, 0, [2, 2, 1, 1] => (⟨43, by decide⟩, false, 2, [1, 0, 2, 1])
  | 3, 0, [2, 2, 1, 2] => (⟨42, by decide⟩, true, 2, [2])
  | 3, 0, [2, 2, 2, 0] => (⟨42, by decide⟩, false, 1, [])
  | 3, 0, [2, 2, 2, 1] => (⟨42, by decide⟩, true, 2, [])
  | 3, 0, [2, 2, 2, 2] => (⟨41, by decide⟩, false, 1, [])
  | 3, 1, [1, 1, 1, 1] => (⟨45, by decide⟩, false, 0, [])
  | 3, 1, [1, 1, 1, 2] => (⟨46, by decide⟩, false, 0, [])
  | 3, 1, [1, 1, 2, 1] => (⟨46, by decide⟩, false, 0, [1])
  | 3, 1, [1, 1, 2, 2] => (⟨47, by decide⟩, false, 0, [])
  | 3, 1, [1, 2, 1, 1] => (⟨46, by decide⟩, false, 0, [0, 1])
  | 3, 1, [1, 2, 1, 2] => (⟨47, by decide⟩, false, 0, [0])
  | 3, 1, [1, 2, 2, 1] => (⟨47, by decide⟩, false, 0, [1, 0])
  | 3, 1, [1, 2, 2, 2] => (⟨48, by decide⟩, false, 0, [])
  | 3, 1, [2, 1, 1, 1] => (⟨48, by decide⟩, true, 0, [])
  | 3, 1, [2, 1, 1, 2] => (⟨47, by decide⟩, true, 0, [1, 0])
  | 3, 1, [2, 1, 2, 1] => (⟨47, by decide⟩, true, 0, [0])
  | 3, 1, [2, 1, 2, 2] => (⟨46, by decide⟩, true, 0, [0, 1])
  | 3, 1, [2, 2, 1, 1] => (⟨47, by decide⟩, true, 0, [])
  | 3, 1, [2, 2, 1, 2] => (⟨46, by decide⟩, true, 0, [1])
  | 3, 1, [2, 2, 2, 1] => (⟨46, by decide⟩, true, 0, [])
  | 3, 1, [2, 2, 2, 2] => (⟨45, by decide⟩, true, 0, [])
  | 3, 2, [1, 1, 1, 1] => (⟨49, by decide⟩, false, 0, [])
  | 3, 2, [1, 1, 1, 2] => (⟨50, by decide⟩, false, 0, [])
  | 3, 2, [1, 1, 2, 1] => (⟨50, by decide⟩, false, 0, [0])
  | 3, 2, [1, 1, 2, 2] => (⟨51, by decide⟩, false, 0, [])
  | 3, 2, [2, 1, 1, 1] => (⟨52, by decide⟩, false, 0, [])
  | 3, 2, [2, 1, 1, 2] => (⟨53, by decide⟩, false, 0, [])
  | 3, 2, [2, 1, 2, 1] => (⟨53, by decide⟩, false, 0, [0])
  | 3, 2, [2, 1, 2, 2] => (⟨52, by decide⟩, true, 0, [])
  | 3, 2, [2, 2, 1, 1] => (⟨51, by decide⟩, true, 0, [])
  | 3, 2, [2, 2, 1, 2] => (⟨50, by decide⟩, true, 0, [0])
  | 3, 2, [2, 2, 2, 1] => (⟨50, by decide⟩, true, 0, [])
  | 3, 2, [2, 2, 2, 2] => (⟨49, by decide⟩, true, 0, [])
  | 3, 3, [1, 1, 1, 1] => (⟨54, by decide⟩, false, 0, [])
  | 3, 3, [1, 1, 1, 2] => (⟨55, by decide⟩, false, 0, [])
  | 3, 3, [2, 1, 1, 1] => (⟨56, by decide⟩, false, 0, [])
  | 3, 3, [2, 1, 1, 2] => (⟨57, by decide⟩, false, 0, [])
  | 3, 3, [2, 2, 1, 1] => (⟨57, by decide⟩, true, 0, [])
  | 3, 3, [2, 2, 1, 2] => (⟨56, by decide⟩, true, 0, [])
  | 3, 3, [2, 2, 2, 1] => (⟨55, by decide⟩, true, 0, [])
  | 3, 3, [2, 2, 2, 2] => (⟨54, by decide⟩, true, 0, [])
  | 4, 0, [0, 0, 0] => (⟨17, by decide⟩, false, 0, [])
  | 4, 0, [0, 0, 1] => (⟨18, by decide⟩, false, 0, [])
  | 4, 0, [0, 0, 2] => (⟨19, by decide⟩, false, 0, [])
  | 4, 0, [0, 0, 3] => (⟨18, by decide⟩, true, 0, [])
  | 4, 0, [0, 1, 0] => (⟨18, by decide⟩, false, 0, [1])
  | 4, 0, [0, 1, 1] => (⟨18, by decide⟩, true, 1, [0, 1])
  | 4, 0, [0, 1, 2] => (⟨20, by decide⟩, false, 0, [])
  | 4, 0, [0, 1, 3] => (⟨20, by decide⟩, false, 1, [1, 0])
  | 4, 0, [0, 2, 0] => (⟨19, by decide⟩, false, 0, [1])
  | 4, 0, [0, 2, 1] => (⟨20, by decide⟩, false, 0, [1])
  | 4, 0, [0, 2, 2] => (⟨19, by decide⟩, false, 2, [0, 1])
  | 4, 0, [0, 2, 3] => (⟨20, by decide⟩, false, 2, [0, 1])
  | 4, 0, [0, 3, 0] => (⟨18, by decide⟩, true, 0, [1])
  | 4, 0, [0, 3, 1] => (⟨20, by decide⟩, false, 1, [0])
  | 4, 0, [0, 3, 2] => (⟨20, by decide⟩, false, 2, [0, 1, 0])
  | 4, 0, [0, 3, 3] => (⟨18, by decide⟩, false, 1, [0, 1])
  | 4, 0, [1, 0, 0] => (⟨18, by decide⟩, false, 0, [0, 1])
  | 4, 0, [1, 0, 1] => (⟨18, by decide⟩, true, 1, [1])
  | 4, 0, [1, 0, 2] => (⟨20, by decide⟩, false, 0, [0])
  | 4, 0, [1, 0, 3] => (⟨20, by decide⟩, false, 1, [0, 1, 0])
  | 4, 0, [1, 1, 0] => (⟨18, by decide⟩, true, 1, [])
  | 4, 0, [1, 1, 1] => (⟨17, by decide⟩, false, 3, [])
  | 4, 0, [1, 1, 2] => (⟨18, by decide⟩, false, 3, [])
  | 4, 0, [1, 1, 3] => (⟨19, by decide⟩, false, 3, [])
  | 4, 0, [1, 2, 0] => (⟨20, by decide⟩, false, 0, [1, 0])
  | 4, 0, [1, 2, 1] => (⟨18, by decide⟩, false, 3, [1])
  | 4, 0, [1, 2, 2] => (⟨18, by decide⟩, true, 2, [0, 1])
  | 4, 0, [1, 2, 3] => (⟨20, by decide⟩, false, 3, [])
  | 4, 0, [1, 3, 0] => (⟨20, by decide⟩, false, 1, [0, 1])
  | 4, 0, [1, 3, 1] => (⟨19, by decide⟩, false, 3, [1])
  | 4, 0, [1, 3, 2] => (⟨20, by decide⟩, false, 3, [1])
  | 4, 0, [1, 3, 3] => (⟨19, by decide⟩, false, 1, [0, 1])
  | 4, 0, [2, 0, 0] => (⟨19, by decide⟩, false, 0, [0, 1])
  | 4, 0, [2, 0, 1] => (⟨20, by decide⟩, false, 0, [0, 1])
  | 4, 0, [2, 0, 2] => (⟨19, by decide⟩, false, 2, [1])
  | 4, 0, [2, 0, 3] => (⟨20, by decide⟩, false, 2, [1])
  | 4, 0, [2, 1, 0] => (⟨20, by decide⟩, false, 0, [0, 1, 0])
  | 4, 0, [2, 1, 1] => (⟨18, by decide⟩, false, 3, [0, 1])
  | 4, 0, [2, 1, 2] => (⟨18, by decide⟩, true, 2, [1])
  | 4, 0, [2, 1, 3] => (⟨20, by decide⟩, false, 3, [0])
  | 4, 0, [2, 2, 0] => (⟨19, by decide⟩, false, 2, [])
  | 4, 0, [2, 2, 1] => (⟨18, by decide⟩, true, 2, [])
  | 4, 0, [2, 2, 2] => (⟨17, by decide⟩, false, 2, [])
  | 4, 0, [2, 2, 3] => (⟨18, by decide⟩, false, 2, [])
  | 4, 0, [2, 3, 0] => (⟨20, by decide⟩, false, 2, [])
  | 4, 0, [2, 3, 1] => (⟨20, by decide⟩, false, 3, [1, 0])
  | 4, 0, [2, 3, 2] => (⟨18, by decide⟩, false, 2, [1])
  | 4, 0, [2, 3, 3] => (⟨18, by decide⟩, true, 3, [0, 1])
  | 4, 0, [3, 0, 0] => (⟨18, by decide⟩, true, 0, [0, 1])
  | 4, 0, [3, 0, 1] => (⟨20, by decide⟩, false, 1, [])
  | 4, 0, [3, 0, 2] => (⟨20, by decide⟩, false, 2, [1, 0])
  | 4, 0, [3, 0, 3] => (⟨18, by decide⟩, false, 1, [1])
  | 4, 0, [3, 1, 0] => (⟨20, by decide⟩, false, 1, [1])
  | 4, 0, [3, 1, 1] => (⟨19, by decide⟩, false, 3, [0, 1])
  | 4, 0, [3, 1, 2] => (⟨20, by decide⟩, false, 3, [0, 1])
  | 4, 0, [3, 1, 3] => (⟨19, by decide⟩, false, 1, [1])
  | 4, 0, [3, 2, 0] => (⟨20, by decide⟩, false, 2, [0])
  | 4, 0, [3, 2, 1] => (⟨20, by decide⟩, false, 3, [0, 1, 0])
  | 4, 0, [3, 2, 2] => (⟨18, by decide⟩, false, 2, [0, 1])
  | 4, 0, [3, 2, 3] => (⟨18, by decide⟩, true, 3, [1])
  | 4, 0, [3, 3, 0] => (⟨18, by decide⟩, false, 1, [])
  | 4, 0, [3, 3, 1] => (⟨19, by decide⟩, false, 1, [])
  | 4, 0, [3, 3, 2] => (⟨18, by decide⟩, true, 3, [])
  | 4, 0, [3, 3, 3] => (⟨17, by decide⟩, false, 1, [])
  | 4, 1, [1, 1, 1] => (⟨21, by decide⟩, false, 0, [])
  | 4, 1, [1, 1, 2] => (⟨22, by decide⟩, false, 0, [])
  | 4, 1, [1, 1, 3] => (⟨23, by decide⟩, false, 0, [])
  | 4, 1, [1, 2, 1] => (⟨22, by decide⟩, false, 0, [0])
  | 4, 1, [1, 2, 2] => (⟨24, by decide⟩, false, 0, [])
  | 4, 1, [1, 2, 3] => (⟨25, by decide⟩, false, 0, [])
  | 4, 1, [1, 3, 1] => (⟨23, by decide⟩, false, 0, [0])
  | 4, 1, [1, 3, 2] => (⟨25, by decide⟩, false, 0, [0])
  | 4, 1, [1, 3, 3] => (⟨26, by decide⟩, false, 0, [])
  | 4, 1, [2, 1, 1] => (⟨27, by decide⟩, false, 0, [])
  | 4, 1, [2, 1, 2] => (⟨28, by decide⟩, false, 0, [])
  | 4, 1, [2, 1, 3] => (⟨29, by decide⟩, false, 0, [])
  | 4, 1, [2, 2, 1] => (⟨28, by decide⟩, false, 0, [0])
  | 4, 1, [2, 2, 2] => (⟨30, by decide⟩, false, 0, [])
  | 4, 1, [2, 2, 3] => (⟨28, by decide⟩, true, 0, [0])
  | 4, 1, [2, 3, 1] => (⟨29, by decide⟩, false, 0, [0])
  | 4, 1, [2, 3, 2] => (⟨28, by decide⟩, true, 0, [])
  | 4, 1, [2, 3, 3] => (⟨27, by decide⟩, true, 0, [])
  | 4, 1, [3, 1, 1] => (⟨26, by decide⟩, true, 0, [])
  | 4, 1, [3, 1, 2] => (⟨25, by decide⟩, true, 0, [0])
  | 4, 1, [3, 1, 3] => (⟨23, by decide⟩, true, 0, [0])
  | 4, 1, [3, 2, 1] => (⟨25, by decide⟩, true, 0, [])
  | 4, 1, [3, 2, 2] => (⟨24, by decide⟩, true, 0, [])
  | 4, 1, [3, 2, 3] => (⟨22, by decide⟩, true, 0, [0])
  | 4, 1, [3, 3, 1] => (⟨23, by decide⟩, true, 0, [])
  | 4, 1, [3, 3, 2] => (⟨22, by decide⟩, true, 0, [])
  | 4, 1, [3, 3, 3] => (⟨21, by decide⟩, true, 0, [])
  | 4, 2, [1, 1, 1] => (⟨31, by decide⟩, false, 0, [])
  | 4, 2, [1, 1, 2] => (⟨32, by decide⟩, false, 0, [])
  | 4, 2, [1, 1, 3] => (⟨33, by decide⟩, false, 0, [])
  | 4, 2, [2, 1, 1] => (⟨34, by decide⟩, false, 0, [])
  | 4, 2, [2, 1, 2] => (⟨35, by decide⟩, false, 0, [])
  | 4, 2, [2, 1, 3] => (⟨36, by decide⟩, false, 0, [])
  | 4, 2, [2, 2, 1] => (⟨37, by decide⟩, false, 0, [])
  | 4, 2, [2, 2, 2] => (⟨38, by decide⟩, false, 0, [])
  | 4, 2, [2, 2, 3] => (⟨37, by decide⟩, true, 0, [])
  | 4, 2, [3, 1, 1] => (⟨39, by decide⟩, false, 0, [])
  | 4, 2, [3, 1, 2] => (⟨40, by decide⟩, false, 0, [])
  | 4, 2, [3, 1, 3] => (⟨39, by decide⟩, true, 0, [])
  | 4, 2, [3, 2, 1] => (⟨36, by decide⟩, true, 0, [])
  | 4, 2, [3, 2, 2] => (⟨35, by decide⟩, true, 0, [])
  | 4, 2, [3, 2, 3] => (⟨34, by decide⟩, true, 0, [])
  | 4, 2, [3, 3, 1] => (⟨33, by decide⟩, true, 0, [])
  | 4, 2, [3, 3, 2] => (⟨32, by decide⟩, true, 0, [])
  | 4, 2, [3, 3, 3] => (⟨31, by decide⟩, true, 0, [])
  | 5, 0, [0, 0] => (⟨6, by decide⟩, false, 0, [])
  | 5, 0, [0, 1] => (⟨7, by decide⟩, false, 0, [])
  | 5, 0, [0, 2] => (⟨8, by decide⟩, false, 0, [])
  | 5, 0, [0, 3] => (⟨8, by decide⟩, false, 2, [0])
  | 5, 0, [0, 4] => (⟨7, by decide⟩, false, 1, [0])
  | 5, 0, [1, 0] => (⟨7, by decide⟩, false, 0, [0])
  | 5, 0, [1, 1] => (⟨6, by decide⟩, false, 4, [])
  | 5, 0, [1, 2] => (⟨7, by decide⟩, false, 4, [])
  | 5, 0, [1, 3] => (⟨8, by decide⟩, false, 4, [])
  | 5, 0, [1, 4] => (⟨8, by decide⟩, false, 1, [0])
  | 5, 0, [2, 0] => (⟨8, by decide⟩, false, 0, [0])
  | 5, 0, [2, 1] => (⟨7, by decide⟩, false, 4, [0])
  | 5, 0, [2, 2] => (⟨6, by decide⟩, false, 3, [])
  | 5, 0, [2, 3] => (⟨7, by decide⟩, false, 3, [])
  | 5, 0, [2, 4] => (⟨8, by decide⟩, false, 3, [])
  | 5, 0, [3, 0] => (⟨8, by decide⟩, false, 2, [])
  | 5, 0, [3, 1] => (⟨8, by decide⟩, false, 4, [0])
  | 5, 0, [3, 2] => (⟨7, by decide⟩, false, 3, [0])
  | 5, 0, [3, 3] => (⟨6, by decide⟩, false, 2, [])
  | 5, 0, [3, 4] => (⟨7, by decide⟩, false, 2, [])
  | 5, 0, [4, 0] => (⟨7, by decide⟩, false, 1, [])
  | 5, 0, [4, 1] => (⟨8, by decide⟩, false, 1, [])
  | 5, 0, [4, 2] => (⟨8, by decide⟩, false, 3, [0])
  | 5, 0, [4, 3] => (⟨7, by decide⟩, false, 2, [0])
  | 5, 0, [4, 4] => (⟨6, by decide⟩, false, 1, [])
  | 5, 1, [1, 1] => (⟨9, by decide⟩, false, 4, [])
  | 5, 1, [1, 2] => (⟨10, by decide⟩, false, 4, [])
  | 5, 1, [1, 3] => (⟨11, by decide⟩, false, 4, [])
  | 5, 1, [1, 4] => (⟨12, by decide⟩, false, 4, [])
  | 5, 1, [2, 1] => (⟨13, by decide⟩, false, 4, [])
  | 5, 1, [2, 2] => (⟨14, by decide⟩, false, 4, [])
  | 5, 1, [2, 3] => (⟨15, by decide⟩, false, 4, [])
  | 5, 1, [2, 4] => (⟨16, by decide⟩, false, 4, [])
  | 5, 1, [3, 1] => (⟨16, by decide⟩, true, 4, [])
  | 5, 1, [3, 2] => (⟨15, by decide⟩, true, 4, [])
  | 5, 1, [3, 3] => (⟨14, by decide⟩, true, 4, [])
  | 5, 1, [3, 4] => (⟨13, by decide⟩, true, 4, [])
  | 5, 1, [4, 1] => (⟨12, by decide⟩, true, 4, [])
  | 5, 1, [4, 2] => (⟨11, by decide⟩, true, 4, [])
  | 5, 1, [4, 3] => (⟨10, by decide⟩, true, 4, [])
  | 5, 1, [4, 4] => (⟨9, by decide⟩, true, 4, [])
  | 6, 0, [0] => (⟨5, by decide⟩, false, 0, [])
  | 6, 0, [1] => (⟨5, by decide⟩, false, 5, [])
  | 6, 0, [2] => (⟨5, by decide⟩, false, 4, [])
  | 6, 0, [3] => (⟨5, by decide⟩, false, 3, [])
  | 6, 0, [4] => (⟨5, by decide⟩, false, 2, [])
  | 6, 0, [5] => (⟨5, by decide⟩, false, 1, [])
  | _, _, _ => (⟨0, by decide⟩, false, 0, [])

/-! ## 2. Exhaustive Verification of `lookupStage2Action` Across All Monotone Stage-2 Tuples -/

private def mkRawStage2Spec (n_d h_sz : ℕ) (raw : List ℕ) : CaseSpec :=
  { n_d := n_d
    h_sz := h_sz
    lr_l := if h_sz = 0 then none else some 0
    edges := raw.map some
    masks := [] }

private def rawValidBool (n_d h_sz : ℕ) (raw : List ℕ) : Bool :=
  raw.all (fun u => decide (u < n_d) && (if h_sz == 0 then true else decide (1 ≤ u))) &&
  (List.range h_sz).all (fun i =>
    if i + 1 < h_sz then
      match raw[i]?, raw[i + 1]? with
      | some u1, some u2 => decide (u2 ≤ u1)
      | _, _ => false
    else true)

private def stage2EntryOk (n_d h_sz : ℕ) (raw : List ℕ) : Bool :=
  if !(rawValidBool n_d h_sz raw) then true
  else
    let (c, doRefl, rotSteps, swaps) := lookupStage2Action n_d h_sz raw
    decide (5 ≤ c.val ∧ c.val ≤ 57) &&
    swaps.all (fun k => decide (n_d + h_sz + k + 1 < 7)) &&
    decide (dihedralNormSpec doRefl rotSteps swaps [] (mkRawStage2Spec n_d h_sz raw) = canonSpec c)

private def checkAllStage2Norm : Bool :=
  ((List.range 6).all (fun u0 => stage2EntryOk 6 0 [u0])) &&
  ((List.range 2).all (fun h =>
    (List.range 5).all (fun u0 =>
      (List.range 5).all (fun u1 => stage2EntryOk 5 h [u0, u1])))) &&
  ((List.range 3).all (fun h =>
    (List.range 4).all (fun u0 =>
      (List.range 4).all (fun u1 =>
        (List.range 4).all (fun u2 => stage2EntryOk 4 h [u0, u1, u2]))))) &&
  ((List.range 4).all (fun h =>
    (List.range 3).all (fun u0 =>
      (List.range 3).all (fun u1 =>
        (List.range 3).all (fun u2 =>
          (List.range 3).all (fun u3 => stage2EntryOk 3 h [u0, u1, u2, u3]))))))

private theorem checkAllStage2Norm_true : checkAllStage2Norm = true := by decide

theorem stage2_monotone_to_canonical {n_d h_sz : ℕ} {raw : List ℕ}
    (hnd : 3 ≤ n_d ∧ n_d ≤ 6)
    (hh_lt : h_sz < 7 - n_d)
    (hlen : raw.length = 7 - n_d)
    (hbnd : ∀ u ∈ raw, u < n_d ∧ (0 < h_sz → 1 ≤ u))
    (hmono : ∀ i : ℕ, i + 1 < h_sz →
      ∀ u₁ u₂ : ℕ, raw[i]? = some u₁ → raw[i + 1]? = some u₂ → u₂ ≤ u₁) :
    let (c, doRefl, rotSteps, swaps) := lookupStage2Action n_d h_sz raw
    (5 ≤ c.val ∧ c.val ≤ 57) ∧
    (∀ k ∈ swaps, n_d + h_sz + k + 1 < 7) ∧
    dihedralNormSpec doRefl rotSteps swaps [] (mkRawStage2Spec n_d h_sz raw) = canonSpec c := by
  have hvalid : rawValidBool n_d h_sz raw = true := by
    unfold rawValidBool
    rw [Bool.and_eq_true, List.all_eq_true, List.all_eq_true]
    refine ⟨?_, ?_⟩
    · intro u hu
      have ⟨h1, h2⟩ := hbnd u hu
      rw [Bool.and_eq_true]
      refine ⟨decide_eq_true h1, ?_⟩
      by_cases hh0 : h_sz = 0
      · simp [hh0]
      · simp [hh0, decide_eq_true (h2 (Nat.pos_of_ne_zero hh0))]
    · intro i hi
      by_cases hi1 : i + 1 < h_sz
      · rw [if_pos hi1]
        have hi_len : i < raw.length := by omega
        have hi1_len : i + 1 < raw.length := by omega
        rw [List.getElem?_eq_getElem hi_len, List.getElem?_eq_getElem hi1_len]
        exact decide_eq_true (hmono i hi1 raw[i] raw[i + 1]
          (List.getElem?_eq_getElem hi_len) (List.getElem?_eq_getElem hi1_len))
      · rw [if_neg hi1]
  have hentry : stage2EntryOk n_d h_sz raw = true := by
    have hall := checkAllStage2Norm_true
    unfold checkAllStage2Norm at hall
    simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range] at hall
    rcases hall with ⟨⟨⟨h6, h5⟩, h4⟩, h3⟩
    have hnd_cases : n_d = 6 ∨ n_d = 5 ∨ n_d = 4 ∨ n_d = 3 := by omega
    rcases hnd_cases with rfl | rfl | rfl | rfl
    · have hh0 : h_sz = 0 := by omega
      subst hh0
      rcases raw with _ | ⟨u0, _ | _⟩ <;> try (simp at hlen; done)
      exact h6 u0 (hbnd u0 (by simp)).1
    · rcases raw with _ | ⟨u0, _ | ⟨u1, _ | _⟩⟩ <;> try (simp at hlen; done)
      exact h5 h_sz (by omega) u0 (hbnd u0 (by simp)).1 u1 (hbnd u1 (by simp)).1
    · rcases raw with _ | ⟨u0, _ | ⟨u1, _ | ⟨u2, _ | _⟩⟩⟩ <;> try (simp at hlen; done)
      exact h4 h_sz (by omega) u0 (hbnd u0 (by simp)).1 u1 (hbnd u1 (by simp)).1
        u2 (hbnd u2 (by simp)).1
    · rcases raw with _ | ⟨u0, _ | ⟨u1, _ | ⟨u2, _ | ⟨u3, _ | _⟩⟩⟩⟩ <;> try (simp at hlen; done)
      exact h3 h_sz (by omega) u0 (hbnd u0 (by simp)).1 u1 (hbnd u1 (by simp)).1
        u2 (hbnd u2 (by simp)).1 u3 (hbnd u3 (by simp)).1
  unfold stage2EntryOk at hentry
  rw [hvalid] at hentry
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hentry
  rcases htup : lookupStage2Action n_d h_sz raw with ⟨c, doRefl, rotSteps, swaps⟩
  rw [htup] at hentry
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hentry
  exact ⟨hentry.1.1, hentry.1.2, hentry.2⟩

/-! ## 3. Helper Lemmas on `buildBccw`, `CyclicSubsetBoundary`, and `hullPos` -/

private lemma append_getElem? {α : Type*} :
    ∀ (as bs : List α) (i : ℕ),
      (as ++ bs)[i]? = if i < as.length then as[i]? else bs[i - as.length]?
  | [], _, _ => by simp
  | _ :: _, _, 0 => by simp
  | _ :: as, bs, i + 1 => by
    simp only [List.cons_append, List.length_cons, List.getElem?_cons_succ]
    rw [append_getElem? as bs i]
    split_ifs <;> try rfl
    · omega
    · omega
    · congr 1; omega

private lemma buildRange_length (start cnt : ℕ) :
    (buildRange start cnt).length = cnt := by
  induction cnt generalizing start with
  | zero => rfl
  | succ k ih => simp [buildRange, ih]

private lemma buildRange_getElem? (start cnt i : ℕ) (hi : i < cnt) :
    (buildRange start cnt)[i]? = some (start + i) := by
  induction cnt generalizing start i with
  | zero => omega
  | succ k ih =>
    cases i with
    | zero => simp [buildRange]
    | succ i' =>
      simp only [buildRange, List.getElem?_cons_succ]
      rw [ih (start + 1) i' (by omega)]
      congr 1; omega

private lemma buildBccwAux_h0 (n_d : ℕ) (lr_l : Option ℕ) (d rem : ℕ) :
    buildBccwAux n_d 0 lr_l d rem = buildRange d rem := by
  induction rem generalizing d with
  | zero => rfl
  | succ r ih => simp [buildBccwAux, buildRange, ih]

private lemma buildBccwAux_some0_pos (n_d h_sz d rem : ℕ) (hd : 1 ≤ d) :
    buildBccwAux n_d h_sz (some 0) d rem = buildRange d rem := by
  induction rem generalizing d with
  | zero => rfl
  | succ r ih =>
    have hne : (some 0 == some d) = false := by simp; omega
    simp [buildBccwAux, buildRange, hne, ih (d + 1) (by omega)]

private def hullPos (n_d h_sz v : ℕ) : ℕ :=
  if v = 0 then 0 else if v < n_d then v + h_sz else (v - n_d) + 1

private def invHullPos (n_d h_sz idx : ℕ) : ℕ :=
  if idx = 0 then 0 else if idx ≤ h_sz then n_d + (idx - 1) else idx - h_sz

private lemma hullPos_lt {n_d h_sz v : ℕ} (hnd : 2 ≤ n_d) (hh : 1 ≤ h_sz)
    (hv : v < n_d + h_sz) : hullPos n_d h_sz v < n_d + h_sz := by
  dsimp [hullPos]; split_ifs <;> omega

private lemma invHullPos_lt {n_d h_sz idx : ℕ} (hnd : 2 ≤ n_d) (hh : 1 ≤ h_sz)
    (hidx : idx < n_d + h_sz) : invHullPos n_d h_sz idx < n_d + h_sz := by
  dsimp [invHullPos]; split_ifs <;> omega

private lemma invHullPos_hullPos {n_d h_sz v : ℕ} (_hnd : 2 ≤ n_d) (hh : 1 ≤ h_sz)
    (hv : v < n_d + h_sz) : invHullPos n_d h_sz (hullPos n_d h_sz v) = v := by
  by_cases hv0 : v = 0
  · subst hv0; simp [hullPos, invHullPos]
  · by_cases hvnd : v < n_d
    · have hp : hullPos n_d h_sz v = v + h_sz := by dsimp [hullPos]; rw [if_neg hv0, if_pos hvnd]
      rw [hp]; dsimp [invHullPos]; split_ifs <;> omega
    · have hp : hullPos n_d h_sz v = (v - n_d) + 1 := by dsimp [hullPos]; rw [if_neg hv0, if_neg hvnd]
      rw [hp]; dsimp [invHullPos]; split_ifs <;> omega

private lemma hullPos_invHullPos {n_d h_sz idx : ℕ} (hnd : 2 ≤ n_d) (hh : 1 ≤ h_sz)
    (hidx : idx < n_d + h_sz) : hullPos n_d h_sz (invHullPos n_d h_sz idx) = idx := by
  by_cases hi0 : idx = 0
  · subst hi0; simp [hullPos, invHullPos]
  · by_cases hih : idx ≤ h_sz
    · have hp : invHullPos n_d h_sz idx = n_d + (idx - 1) := by
        dsimp [invHullPos]; rw [if_neg hi0, if_pos hih]
      rw [hp]; dsimp [hullPos]; split_ifs <;> omega
    · have hp : invHullPos n_d h_sz idx = idx - h_sz := by
        dsimp [invHullPos]; rw [if_neg hi0, if_neg hih]
      rw [hp]; dsimp [hullPos]; split_ifs <;> omega

private lemma buildBccw_some0_eq {spec : CaseSpec}
    (hnd : 2 ≤ spec.n_d) (hh : 0 < spec.h_sz) (hlr : spec.lr_l = some 0) :
    buildBccw spec = 0 :: (buildRange spec.n_d spec.h_sz ++ buildRange 1 (spec.n_d - 1)) := by
  unfold buildBccw
  rw [hlr]
  obtain ⟨r, hr⟩ : ∃ r, spec.n_d = r + 1 := ⟨spec.n_d - 1, by omega⟩
  rw [hr]
  simp only [buildBccwAux, Nat.add_sub_cancel]
  have hcond : (decide (spec.h_sz > 0) && (some 0 == some 0)) = true := by simp [hh]
  rw [hcond, if_pos rfl, buildBccwAux_some0_pos (r + 1) spec.h_sz 1 r (by omega)]

private lemma buildBccw_some0_length {spec : CaseSpec}
    (hnd : 2 ≤ spec.n_d) (hh : 0 < spec.h_sz) (hlr : spec.lr_l = some 0) :
    (buildBccw spec).length = spec.n_d + spec.h_sz := by
  rw [buildBccw_some0_eq hnd hh hlr]
  simp only [List.length_cons, List.length_append, buildRange_length]
  omega

private lemma buildBccw_some0_get {spec : CaseSpec}
    (hnd : 2 ≤ spec.n_d) (hh : 0 < spec.h_sz) (hlr : spec.lr_l = some 0)
    {idx : ℕ} (hidx : idx < spec.n_d + spec.h_sz) :
    listGetOpt (buildBccw spec) idx = some (invHullPos spec.n_d spec.h_sz idx) := by
  rw [listGetOpt_eq_getElem?, buildBccw_some0_eq hnd hh hlr]
  cases idx with
  | zero => simp [invHullPos]
  | succ k =>
    simp only [List.getElem?_cons_succ]
    rw [append_getElem?, buildRange_length]
    by_cases hk : k < spec.h_sz
    · rw [if_pos hk, buildRange_getElem? spec.n_d spec.h_sz k hk]
      congr 1
      dsimp [invHullPos]; split_ifs <;> omega
    · rw [if_neg hk, buildRange_getElem? 1 (spec.n_d - 1) (k - spec.h_sz) (by omega)]
      congr 1
      dsimp [invHullPos]; split_ifs <;> omega

private lemma fin_succ_val_eq {m : ℕ} (i : Fin (m + 3)) :
    (i + 1).val = if i.val + 1 < m + 3 then i.val + 1 else 0 := by
  have h1 : (1 : Fin (m + 3)).val = 1 := by
    change 1 % (m + 3) = 1
    exact Nat.mod_eq_of_lt (by omega)
  change (i.val + (1 : Fin (m + 3)).val) % (m + 3) = _
  rw [h1]
  split_ifs with hlt
  · exact Nat.mod_eq_of_lt hlt
  · have : i.val + 1 = m + 3 := by have := i.isLt; omega
    rw [this, Nat.mod_self]

private lemma fin_pred_val_pos {m : ℕ} (i : Fin (m + 3)) (hi : 1 ≤ i.val) :
    (i - 1).val = i.val - 1 := by
  let j : Fin (m + 3) := ⟨i.val - 1, by have := i.isLt; omega⟩
  have hj1 : j + 1 = i := by
    ext
    rw [fin_succ_val_eq j, if_pos (by dsimp [j]; have := i.isLt; omega)]
    dsimp [j]; omega
  have hsub : (j + 1) - 1 = j := add_sub_cancel_right j 1
  rw [hj1] at hsub
  rw [hsub]

private lemma finShift_comp {N : ℕ} [NeZero N] (i : Fin N) (a b : ℕ) :
    PolygonCore.finShift (PolygonCore.finShift i a) b = PolygonCore.finShift i (a + b) := by
  ext
  simp only [PolygonCore.finShift, Nat.mod_add_mod, Nat.add_assoc]

private lemma zWitness_relabelW_local (σ : Equiv.Perm (Fin 7))
    (w : Finset (Fin 7) → ℝ × ℝ) (h : Fin 7) :
    PolygonCore.zWitness (relabelW σ w) h = PolygonCore.zWitness w (σ h) := by
  dsimp [PolygonCore.zWitness, relabelW]
  congr 1
  ext x
  simp only [Finset.mem_image, Finset.mem_erase, Finset.mem_univ, and_true]
  exact ⟨fun ⟨j, hjh, hx⟩ => hx ▸ σ.injective.ne hjh,
    fun hx => ⟨σ.symm x, fun e => hx (by rw [← e, σ.apply_symm_apply]), σ.apply_symm_apply x⟩⟩

@[reducible] private def castCB {n : ℕ} {S : Fin n → ℝ × ℝ} {C₁ C₂ : Finset (Fin n)}
    (cb : PolygonCore.CyclicSubsetBoundary S C₁) (hEq : C₁ = C₂) :
    PolygonCore.CyclicSubsetBoundary S C₂ where
  m := cb.m
  p_idx := cb.p_idx
  hp_idx_inj := cb.hp_idx_inj
  hp_idx_img := cb.hp_idx_img.trans hEq
  hstrict := cb.hstrict
  hcyc := cb.hcyc

private lemma cyclicOrder_add_const_local {N : ℕ} (sh i j k : Fin N)
    (h : PolygonCore.CyclicOrder i j k) :
    PolygonCore.CyclicOrder (i + sh) (j + sh) (k + sh) := by
  unfold PolygonCore.CyclicOrder at h ⊢
  simp only [Fin.lt_def, Fin.val_add_eq_ite] at h ⊢
  have := i.isLt; have := j.isLt; have := k.isLt; have := sh.isLt
  split_ifs <;> omega

private lemma strictConvexCCWPoly_of_hcyc_local {m : ℕ} {p : Fin (m + 3) → ℝ × ℝ}
    (hcyc : ∀ i j k : Fin (m + 3), PolygonCore.CyclicOrder i j k → 0 < orient2D (p i) (p j) (p k)) :
    StrictConvexCCWPoly p := by
  intro i j hji hj1
  have h1_eq : (1 : Fin (m + 3)) = ⟨1 % (m + 3), Nat.mod_lt 1 (by omega)⟩ := by
    ext; change 1 % (m + 3) = 1 % (m + 3); rfl
  rw [h1_eq] at hj1
  have hc := PolygonCore.cyclicOrder_succ (by omega : 3 ≤ m + 3) hji hj1
  rw [← h1_eq] at hc
  exact hcyc i (i + 1) j hc

@[reducible] private def relabelShiftCB_local {S : Fin 7 → ℝ × ℝ} (σ : Equiv.Perm (Fin 7))
    (cb : PolygonCore.CyclicSubsetBoundary S (PolygonCore.hullVertices S))
    (sh : Fin (cb.m + 3)) :
    PolygonCore.CyclicSubsetBoundary (relabelS σ S) (PolygonCore.hullVertices (relabelS σ S)) where
  m := cb.m
  p_idx := fun idx => σ.symm (cb.p_idx (idx + sh))
  hp_idx_inj := fun _ _ hij => add_right_cancel (cb.hp_idx_inj (σ.symm.injective hij))
  hp_idx_img := by
    ext x
    simp only [Finset.mem_image, Finset.mem_univ, true_and, mem_hullVertices_relabel]
    have himg := Finset.ext_iff.mp cb.hp_idx_img (σ x)
    rw [← himg]
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨fun ⟨i, hi⟩ => ⟨i + sh, hi ▸ (σ.apply_symm_apply _).symm⟩,
      fun ⟨j, hj⟩ => ⟨j - sh, by rw [sub_add_cancel, hj, σ.symm_apply_apply]⟩⟩
  hstrict := strictConvexCCWPoly_of_hcyc_local (fun i j k h => by
    simp only [relabelS, Function.comp_apply, σ.apply_symm_apply]
    exact cb.hcyc (i + sh) (j + sh) (k + sh) (cyclicOrder_add_const_local sh i j k h))
  hcyc := fun i j k h => by
    simp only [relabelS, Function.comp_apply, σ.apply_symm_apply]
    exact cb.hcyc (i + sh) (j + sh) (k + sh) (cyclicOrder_add_const_local sh i j k h)

private lemma cyclicOrder_strictMono {M N : ℕ} {g : Fin M → Fin N}
    (hg : StrictMono g) {i j k : Fin M} (h : PolygonCore.CyclicOrder i j k) :
    PolygonCore.CyclicOrder (g i) (g j) (g k) := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨hg h1, hg h2⟩
  · exact Or.inr (Or.inl ⟨hg h1, hg h2⟩)
  · exact Or.inr (Or.inr ⟨hg h1, hg h2⟩)

/-! ## 4. Precanonical Relabeling for `h_sz = 0` (`3 ≤ n_d ≤ 6`) -/

private theorem exists_precanonical_h0 {P : Set (ℝ × ℝ)}
    {S : Fin 7 → ℝ × ℝ} {w : Finset (Fin 7) → ℝ × ℝ}
    (hP : ShatteredSimplePolygon P S w)
    (hh0 : (PolygonCore.certifiedSet P S w).card = 0)
    (hnd3 : 3 ≤ (PolygonCore.hullVertices S \ PolygonCore.certifiedSet P S w).card)
    (hnd6 : (PolygonCore.hullVertices S \ PolygonCore.certifiedSet P S w).card ≤ 6) :
    let n_d := (PolygonCore.hullVertices S \ PolygonCore.certifiedSet P S w).card
    ∃ (S' : Fin 7 → ℝ × ℝ) (w' : Finset (Fin 7) → ℝ × ℝ) (raw : List ℕ),
      raw.length = 7 - n_d ∧
      (∀ u ∈ raw, u < n_d) ∧
      ValidCanonicalInstance P S' w' (mkRawStage2Spec n_d 0 raw) := by
  intro n_d
  have hH_emp : PolygonCore.certifiedSet P S w = ∅ := Finset.card_eq_zero.mp hh0
  have hD_eq_B : PolygonCore.hullVertices S \ PolygonCore.certifiedSet P S w =
      PolygonCore.hullVertices S := by rw [hH_emp, Finset.sdiff_empty]
  have hB_card : (PolygonCore.hullVertices S).card = n_d := by dsimp [n_d]; rw [hD_eq_B]
  have hA_card : (PolygonCore.interiorPoints S).card = 7 - n_d := by
    have hsum : (PolygonCore.interiorPoints S).card + (PolygonCore.hullVertices S).card = 7 := by
      unfold PolygonCore.interiorPoints
      simpa using Finset.card_sdiff_add_card_eq_card (Finset.subset_univ (PolygonCore.hullVertices S))
    omega
  obtain ⟨cb⟩ := PolygonCore.exists_cyclicSubsetBoundary hP (Finset.Subset.refl _) (by omega)
  have hcb_len : cb.m + 3 = n_d := by
    have hc := congrArg Finset.card cb.hp_idx_img
    rw [Finset.card_image_of_injective _ cb.hp_idx_inj, Finset.card_fin, hB_card] at hc
    exact hc
  let eA : PolygonCore.interiorPoints S ≃ Fin (7 - n_d) :=
    (PolygonCore.interiorPoints S).equivFinOfCardEq hA_card
  let f : Fin 7 → Fin 7 := fun x =>
    if hx : x.val < n_d then
      cb.p_idx ⟨x.val, by omega⟩
    else
      (eA.symm ⟨x.val - n_d, by omega⟩).1
  have hf_memB : ∀ {v : ℕ} (hv : v < n_d),
      cb.p_idx ⟨v, by omega⟩ ∈ PolygonCore.hullVertices S := by
    intro v hv
    exact (Finset.ext_iff.mp cb.hp_idx_img _).mp (Finset.mem_image_of_mem _ (Finset.mem_univ _))
  have hf_inj : Function.Injective f := by
    intro x y hxy
    dsimp only [f] at hxy
    by_cases hx : x.val < n_d <;> by_cases hy : y.val < n_d <;>
      simp only [hx, hy, ↓reduceDIte] at hxy
    · exact Fin.ext (Fin.mk.inj (cb.hp_idx_inj hxy))
    · exfalso
      have hmB := hf_memB hx
      rw [hxy] at hmB
      exact (Finset.mem_sdiff.mp (eA.symm _).2).2 hmB
    · exfalso
      have hmB := hf_memB hy
      rw [← hxy] at hmB
      exact (Finset.mem_sdiff.mp (eA.symm _).2).2 hmB
    · have hsub := eA.symm.injective (Subtype.ext hxy)
      have hv := congrArg Fin.val hsub
      dsimp at hv
      exact Fin.ext (by omega)
  let σ : Equiv.Perm (Fin 7) := Equiv.ofBijective f (Finite.injective_iff_bijective.mp hf_inj)
  have hσ_app : ∀ x : Fin 7, σ x = f x := fun _ => rfl
  let S' := relabelS σ S
  let w' := relabelW σ w
  have hP' : ShatteredSimplePolygon P S' w' := shattered_relabel hP σ
  have hH'_emp : PolygonCore.certifiedSet P S' w' = ∅ := by
    ext x; simp [S', w', mem_certifiedSet_relabel, hH_emp]
  have hB'_mem : ∀ x : Fin 7, x ∈ PolygonCore.hullVertices S' ↔ x.val < n_d := by
    intro x
    rw [mem_hullVertices_relabel, hσ_app]
    dsimp only [f]
    split_ifs with hx
    · exact iff_of_true (hf_memB hx) hx
    · exact iff_of_false (Finset.mem_sdiff.mp (eA.symm _).2).2 hx
  have hD'_mem : ∀ x : Fin 7,
      x ∈ PolygonCore.hullVertices S' \ PolygonCore.certifiedSet P S' w' ↔ x.val < n_d := by
    intro x; rw [hH'_emp, Finset.sdiff_empty]; exact hB'_mem x
  let cb' := relabelShiftCB_local σ cb 0
  have hcb'_idx : ∀ idx : Fin (cb.m + 3), cb'.p_idx idx = ⟨idx.val, by omega⟩ := by
    intro idx
    change σ.symm (cb.p_idx (idx + 0)) = _
    rw [add_zero]
    apply σ.injective
    rw [σ.apply_symm_apply, hσ_app]
    dsimp only [f]
    rw [dif_pos (by have := idx.isLt; omega)]
  have hD'_eq_B' : PolygonCore.hullVertices S' =
      PolygonCore.hullVertices S' \ PolygonCore.certifiedSet P S' w' := by
    rw [hH'_emp, Finset.sdiff_empty]
  let dc : PolygonCore.CyclicSubsetBoundary S'
      (PolygonCore.hullVertices S' \ PolygonCore.certifiedSet P S' w') :=
    castCB cb' hD'_eq_B'
  have hD3' : 3 ≤ (PolygonCore.hullVertices S' \ PolygonCore.certifiedSet P S' w').card := by
    have hc := congrArg Finset.card dc.hp_idx_img
    rw [Finset.card_image_of_injective _ dc.hp_idx_inj, Finset.card_fin] at hc
    change cb.m + 3 = _ at hc
    omega
  have hexit : ∀ (eIdx : ℕ) (he : eIdx < 7 - n_d),
      ∃ i : Fin (dc.m + 3),
        ∀ Tw : Finset (Fin 7), dc.p_idx i ∈ Tw → dc.p_idx (i + 1) ∈ Tw →
          inOpenTriBool (S' ⟨n_d + eIdx, by omega⟩) (w' Tw)
            (S' (dc.p_idx i)) (S' (dc.p_idx (i + 1))) = true := by
    intro eIdx he
    let fy : Fin 7 := ⟨n_d + eIdx, by omega⟩
    have hfy_M : fy ∈ PolygonCore.interiorPoints S' ∪ PolygonCore.certifiedSet P S' w' := by
      apply Finset.mem_union_left
      refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ?_⟩
      rw [hB'_mem]; dsimp [fy]; omega
    obtain ⟨i, _, hall⟩ := exit_edge_cone_clause_C5 hP' (by decide) hD3' dc hfy_M
    exact ⟨i, hall⟩
  let pickI : ∀ (eIdx : ℕ), eIdx < 7 - n_d → Fin (dc.m + 3) :=
    fun eIdx he => Classical.choose (hexit eIdx he)
  let raw : List ℕ := (List.range (7 - n_d)).map (fun eIdx =>
    if he : eIdx < 7 - n_d then (pickI eIdx he).val else 0)
  have hraw_len : raw.length = 7 - n_d := by simp [raw]
  have hraw_bnd : ∀ u ∈ raw, u < n_d := by
    intro u hu
    rcases List.mem_map.mp hu with ⟨eIdx, he_mem, rfl⟩
    have he : eIdx < 7 - n_d := List.mem_range.mp he_mem
    rw [dif_pos he]
    have := (pickI eIdx he).isLt
    change _ < cb.m + 3 at this
    omega
  refine ⟨S', w', raw, hraw_len, hraw_bnd, ?_⟩
  refine ⟨hP', by dsimp [mkRawStage2Spec]; omega, by dsimp [mkRawStage2Spec]; omega,
    by dsimp [mkRawStage2Spec]; omega, hD'_mem, ?_, ?_, ?_, ?_⟩
  · intro x
    dsimp [mkRawStage2Spec]
    rw [hH'_emp]
    simp only [Finset.notMem_empty, false_iff]
    omega
  · refine ⟨cb', ?_, ?_⟩
    · dsimp [mkRawStage2Spec, buildBccw]
      rw [buildBccwAux_h0, buildRange_length]
      exact hcb_len.symm
    · intro idx
      have hidx_lt : idx.val < cb.m + 3 := idx.isLt
      dsimp [mkRawStage2Spec, buildBccw]
      rw [listGetOpt_eq_getElem?, buildBccwAux_h0,
          buildRange_getElem? 0 n_d idx.val (by omega), zero_add, hcb'_idx idx]
  · intro hh_pos; dsimp [mkRawStage2Spec] at hh_pos; omega
  · dsimp only [mkRawStage2Spec]
    intro _ eIdx u_y he_lt hed _ Tw hfu hfv
    rw [listGetOpt_eq_getElem?, List.getElem?_map] at hed
    dsimp [raw] at hed
    rw [List.getElem?_map, List.getElem?_range he_lt] at hed
    dsimp [Option.map] at hed
    rw [dif_pos he_lt] at hed
    injection hed with hsome
    injection hsome with hu_eq
    let i := pickI eIdx he_lt
    have hi_prop := Classical.choose_spec (hexit eIdx he_lt)
    have hdc_i : dc.p_idx i = ⟨u_y, by omega⟩ := by
      change cb'.p_idx i = _
      rw [hcb'_idx i]
      ext; exact hu_eq
    have hdc_i1 : dc.p_idx (i + 1) =
        ⟨if u_y + 1 < n_d then u_y + 1 else 0, nextMod_lt_seven (by omega)⟩ := by
      change cb'.p_idx (i + 1) = _
      rw [hcb'_idx (i + 1)]
      apply Fin.ext
      dsimp only
      have hdc_m : dc.m = cb.m := rfl
      rw [fin_succ_val_eq i]
      have hi_val : i.val = u_y := hu_eq
      rw [hi_val]
      split_ifs <;> omega
    have ht := hi_prop Tw (by rwa [hdc_i]) (by rwa [hdc_i1])
    rwa [hdc_i, hdc_i1] at ht

/-! ## 5. Precanonical Relabeling & Monotone Exit-Edge Extraction for `h_sz > 0` -/

private theorem exists_precanonical_hpos {P : Set (ℝ × ℝ)}
    {S : Fin 7 → ℝ × ℝ} {w : Finset (Fin 7) → ℝ × ℝ}
    (hP : ShatteredSimplePolygon P S w)
    (hh_pos : 0 < (PolygonCore.certifiedSet P S w).card)
    (hnd2 : 2 ≤ (PolygonCore.hullVertices S \ PolygonCore.certifiedSet P S w).card)
    (hbsz3 : 3 ≤ (PolygonCore.hullVertices S).card) :
    let n_d := (PolygonCore.hullVertices S \ PolygonCore.certifiedSet P S w).card
    let h_sz := (PolygonCore.certifiedSet P S w).card
    ∃ (S' : Fin 7 → ℝ × ℝ) (w' : Finset (Fin 7) → ℝ × ℝ),
      ValidCanonicalInstance P S' w'
        { n_d := n_d, h_sz := h_sz, lr_l := some 0,
          edges := List.replicate (7 - n_d) none, masks := [] } ∧
      (3 ≤ n_d → n_d + h_sz ≤ 6 →
        ∃ raw : List ℕ,
          raw.length = 7 - n_d ∧
          (∀ u ∈ raw, u < n_d ∧ (0 < h_sz → 1 ≤ u)) ∧
          (∀ i : ℕ, i + 1 < h_sz →
            ∀ u₁ u₂ : ℕ, raw[i]? = some u₁ → raw[i + 1]? = some u₂ → u₂ ≤ u₁) ∧
          ValidCanonicalInstance P S' w' (mkRawStage2Spec n_d h_sz raw)) := by
  intro n_d h_sz
  have hnd2' : 2 ≤ n_d := hnd2
  have hh_pos' : 1 ≤ h_sz := hh_pos
  have hH_sub_B : PolygonCore.certifiedSet P S w ⊆ PolygonCore.hullVertices S :=
    Finset.filter_subset _ _
  have hB_eq : (PolygonCore.hullVertices S).card = n_d + h_sz := by
    dsimp [n_d, h_sz]
    exact (Finset.card_sdiff_add_card_eq_card hH_sub_B).symm
  have htot7 : n_d + h_sz ≤ 7 := by
    rw [← hB_eq]
    simpa using Finset.card_le_univ (PolygonCore.hullVertices S)
  have hA_card : (PolygonCore.interiorPoints S).card = 7 - (n_d + h_sz) := by
    have hsum : (PolygonCore.interiorPoints S).card + (PolygonCore.hullVertices S).card = 7 := by
      unfold PolygonCore.interiorPoints
      simpa using Finset.card_sdiff_add_card_eq_card (Finset.subset_univ (PolygonCore.hullVertices S))
    omega
  obtain ⟨cb⟩ := PolygonCore.exists_cyclicSubsetBoundary hP (Finset.Subset.refl _) hbsz3
  have hcb_len : cb.m + 3 = n_d + h_sz := by
    have hc := congrArg Finset.card cb.hp_idx_img
    rw [Finset.card_image_of_injective _ cb.hp_idx_inj, Finset.card_fin, hB_eq] at hc
    exact hc
  haveI : NeZero (cb.m + 3) := ⟨by omega⟩
  have hH_ne : (PolygonCore.certifiedSet P S w).Nonempty := Finset.card_pos.mp hh_pos
  obtain ⟨h₀, hh₀⟩ := hH_ne
  obtain ⟨vc⟩ := PolygonCore.exists_q_visibleContour hP (by decide) cb (Finset.mem_filter.mp hh₀).2
  obtain ⟨k_f, k_g, l, r, hkf0, hkfg, hkg_lt, hl_eq, hr_eq, hlD, hrD, hlr, hblock, htri_lr, _, _⟩ :=
    certified_pocket_lr_C6 hP (by decide) cb vc ⟨h₀, hh₀⟩
  have hd_lt := vc.hd_lt
  -- Prove k_g - k_f + 1 = h_sz
  have hkg_kf_card : k_g - k_f + 1 = h_sz := by
    let embH : Fin (k_g - k_f + 1) → Fin 7 :=
      fun t => cb.p_idx (PolygonCore.finShift vc.i_max (k_f + t.val))
    have hemb_inj : Function.Injective embH := by
      intro t₁ t₂ heq
      have hsh := cb.hp_idx_inj heq
      rw [PolygonCore.finShift_eq_add vc.i_max (by omega),
          PolygonCore.finShift_eq_add vc.i_max (by omega)] at hsh
      have hfin := add_left_cancel hsh
      have hv := congrArg Fin.val hfin
      dsimp at hv
      exact Fin.ext (by omega)
    have hemb_img : Finset.univ.image embH = PolygonCore.certifiedSet P S w := by
      ext x
      simp only [Finset.mem_image, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨t, rfl⟩
        exact (hblock (k_f + t.val) (by omega)).mp ⟨by omega, by omega⟩
      · intro hxH
        have hxB : x ∈ PolygonCore.hullVertices S := hH_sub_B hxH
        rw [← cb.hp_idx_img] at hxB
        rcases Finset.mem_image.mp hxB with ⟨j, _, rfl⟩
        let k := (j - vc.i_max).val
        have hk_lt : k < cb.m + 3 := (j - vc.i_max).isLt
        have hj_sh : PolygonCore.finShift vc.i_max k = j := PolygonCore.finShift_sub vc.i_max j
        have hkr := (hblock k hk_lt).mpr (by rwa [hj_sh])
        refine ⟨⟨k - k_f, by omega⟩, ?_⟩
        dsimp [embH]
        rw [show k_f + (k - k_f) = k by omega, hj_sh]
    have hc := congrArg Finset.card hemb_img
    rw [Finset.card_image_of_injective _ hemb_inj, Finset.card_fin] at hc
    exact hc
  let i_l : Fin (cb.m + 3) := PolygonCore.finShift vc.i_max (k_f - 1)
  let eA : PolygonCore.interiorPoints S ≃ Fin (7 - (n_d + h_sz)) :=
    (PolygonCore.interiorPoints S).equivFinOfCardEq hA_card
  let f : Fin 7 → Fin 7 := fun x =>
    if hx : x.val < n_d + h_sz then
      cb.p_idx (⟨hullPos n_d h_sz x.val, by have := hullPos_lt hnd2' hh_pos' hx; omega⟩ + i_l)
    else
      (eA.symm ⟨x.val - (n_d + h_sz), by omega⟩).1
  have hf_memB : ∀ {v : ℕ} (hv : v < n_d + h_sz),
      cb.p_idx (⟨hullPos n_d h_sz v, by have := hullPos_lt hnd2' hh_pos' hv; omega⟩ + i_l) ∈
        PolygonCore.hullVertices S := by
    intro v hv
    exact (Finset.ext_iff.mp cb.hp_idx_img _).mp (Finset.mem_image_of_mem _ (Finset.mem_univ _))
  have hf_inj : Function.Injective f := by
    intro x y hxy
    dsimp only [f] at hxy
    by_cases hx : x.val < n_d + h_sz <;> by_cases hy : y.val < n_d + h_sz <;>
      simp only [hx, hy, ↓reduceDIte] at hxy
    · have h1 := add_right_cancel (cb.hp_idx_inj hxy)
      have hv := congrArg Fin.val h1
      dsimp at hv
      have hxy_val : x.val = y.val := by
        rw [← invHullPos_hullPos hnd2' hh_pos' hx, ← invHullPos_hullPos hnd2' hh_pos' hy, hv]
      exact Fin.ext hxy_val
    · exfalso
      have hmB := hf_memB hx
      rw [hxy] at hmB
      exact (Finset.mem_sdiff.mp (eA.symm _).2).2 hmB
    · exfalso
      have hmB := hf_memB hy
      rw [← hxy] at hmB
      exact (Finset.mem_sdiff.mp (eA.symm _).2).2 hmB
    · have hsub := eA.symm.injective (Subtype.ext hxy)
      have hv := congrArg Fin.val hsub
      dsimp at hv
      exact Fin.ext (by omega)
  let σ : Equiv.Perm (Fin 7) := Equiv.ofBijective f (Finite.injective_iff_bijective.mp hf_inj)
  have hσ_app : ∀ x : Fin 7, σ x = f x := fun _ => rfl
  have hsh_il : ∀ {p : ℕ} (hp : p < cb.m + 3),
      (⟨p, hp⟩ : Fin (cb.m + 3)) + i_l = PolygonCore.finShift vc.i_max (k_f - 1 + p) := by
    intro p hp
    exact (add_comm _ i_l).trans
      ((PolygonCore.finShift_eq_add i_l hp).symm.trans (finShift_comp vc.i_max (k_f - 1) p))
  have hσ_0 : σ ⟨0, by omega⟩ = l := by
    rw [hσ_app]; dsimp [f]
    rw [dif_pos (by omega)]
    have hp0 : hullPos n_d h_sz 0 = 0 := rfl
    have hidx : (⟨hullPos n_d h_sz 0, by omega⟩ : Fin (cb.m + 3)) + i_l = i_l := by
      ext; simp [hp0]
    rw [hidx, hl_eq]
  have hσ_1 : σ ⟨1, by omega⟩ = r := by
    rw [hσ_app]; dsimp [f]
    rw [dif_pos (by omega)]
    have hp1 : hullPos n_d h_sz 1 = 1 + h_sz := by dsimp [hullPos]; split_ifs <;> omega
    have hidx : (⟨hullPos n_d h_sz 1, by omega⟩ : Fin (cb.m + 3)) + i_l =
        PolygonCore.finShift vc.i_max (k_g + 1) := by
      rw [hsh_il, hp1, show k_f - 1 + (1 + h_sz) = k_g + 1 by omega]
    rw [hidx, hr_eq]
  have hσ_h : ∀ (hi : ℕ) (hhi : hi < h_sz),
      σ ⟨n_d + hi, by omega⟩ = cb.p_idx (PolygonCore.finShift vc.i_max (k_f + hi)) := by
    intro hi hhi
    rw [hσ_app]; dsimp [f]
    rw [dif_pos (by omega)]
    have hph : hullPos n_d h_sz (n_d + hi) = hi + 1 := by dsimp [hullPos]; split_ifs <;> omega
    congr 1
    rw [hsh_il, hph, show k_f - 1 + (hi + 1) = k_f + hi by omega]
  let S' := relabelS σ S
  let w' := relabelW σ w
  have hP' : ShatteredSimplePolygon P S' w' := shattered_relabel hP σ
  have hB'_mem : ∀ x : Fin 7, x ∈ PolygonCore.hullVertices S' ↔ x.val < n_d + h_sz := by
    intro x
    rw [mem_hullVertices_relabel, hσ_app]
    dsimp only [f]
    split_ifs with hx
    · exact iff_of_true (hf_memB hx) hx
    · exact iff_of_false (Finset.mem_sdiff.mp (eA.symm _).2).2 hx
  have hH'_mem : ∀ x : Fin 7,
      x ∈ PolygonCore.certifiedSet P S' w' ↔ n_d ≤ x.val ∧ x.val < n_d + h_sz := by
    intro x
    rw [mem_certifiedSet_relabel]
    constructor
    · intro hxH
      have hxB : x.val < n_d + h_sz := (hB'_mem x).mp (mem_hullVertices_relabel σ S x |>.mpr (hH_sub_B hxH))
      refine ⟨?_, hxB⟩
      by_contra hlt
      have hnd_x : x.val < n_d := by omega
      -- Every element of H is cb.p_idx (finShift vc.i_max k) with k_f ≤ k ≤ k_g
      rw [hσ_app] at hxH; dsimp only [f] at hxH; rw [dif_pos hxB] at hxH
      let idx_x : Fin (cb.m + 3) := ⟨hullPos n_d h_sz x.val, by have := hullPos_lt hnd2' hh_pos' hxB; omega⟩ + i_l
      let k := (idx_x - vc.i_max).val
      have hk_lt : k < cb.m + 3 := (idx_x - vc.i_max).isLt
      have hsh_k : PolygonCore.finShift vc.i_max k = idx_x := PolygonCore.finShift_sub vc.i_max idx_x
      have hkr := (hblock k hk_lt).mpr (by change cb.p_idx idx_x ∈ _ at hxH; rwa [hsh_k])
      let hi := k - k_f
      have hhi : hi < h_sz := by omega
      have hk_eq : k = k_f + hi := by omega
      have hidx_h : PolygonCore.finShift vc.i_max (k_f + hi) =
          (⟨hi + 1, by omega⟩ : Fin (cb.m + 3)) + i_l := by
        rw [show k_f + hi = k_f - 1 + (hi + 1) by omega]
        exact (hsh_il (by omega)).symm
      rw [← hk_eq, hsh_k] at hidx_h
      have hp_eq := congrArg Fin.val (add_right_cancel hidx_h)
      dsimp at hp_eq
      dsimp [hullPos] at hp_eq
      split_ifs at hp_eq <;> omega
    · rintro ⟨hge, hlt⟩
      let hi := x.val - n_d
      have hhi : hi < h_sz := by omega
      have hx_eq : x = ⟨n_d + hi, by omega⟩ := by ext; dsimp; omega
      rw [hx_eq, hσ_h hi hhi]
      exact (hblock (k_f + hi) (by omega)).mp ⟨by omega, by omega⟩
  have hD'_mem : ∀ x : Fin 7,
      x ∈ PolygonCore.hullVertices S' \ PolygonCore.certifiedSet P S' w' ↔ x.val < n_d := by
    intro x
    rw [Finset.mem_sdiff, hB'_mem, hH'_mem]
    omega
  let cb' := relabelShiftCB_local σ cb i_l
  have hcb'_m : cb'.m = cb.m := rfl
  have hcb'_idx : ∀ idx : Fin (cb.m + 3),
      cb'.p_idx idx = ⟨invHullPos n_d h_sz idx.val, by
        have hlt : idx.val < n_d + h_sz := by have := idx.isLt; omega
        have := invHullPos_lt hnd2' hh_pos' hlt; omega⟩ := by
    intro idx
    change σ.symm (cb.p_idx (idx + i_l)) = _
    apply σ.injective
    rw [σ.apply_symm_apply, hσ_app]
    dsimp only [f]
    have hlt : idx.val < n_d + h_sz := by have := idx.isLt; omega
    have hv_lt : invHullPos n_d h_sz idx.val < n_d + h_sz :=
      invHullPos_lt hnd2' hh_pos' hlt
    rw [dif_pos hv_lt]
    congr 2
    ext
    exact (hullPos_invHullPos hnd2' hh_pos' hlt).symm
  -- Prove h_pocket once for any spec sharing (n_d, h_sz, lr_l = some 0)
  have hpocket_all :
      let r_idx := if 0 + 1 < n_d then 0 + 1 else 0
      let fl : Fin 7 := ⟨0, by omega⟩
      let fr : Fin 7 := ⟨r_idx, nextMod_lt_seven (by omega)⟩
      (∀ hi (hhi : hi < h_sz) (Tw : Finset (Fin 7)), {fl, fr} ⊆ Tw →
        inOpenTriBool (S' ⟨n_d + hi, by omega⟩) (w' Tw) (S' fl) (S' fr) = true) ∧
      (h_sz > 1 → ∀ hi (hhi : hi < h_sz),
        let hm := if hi == 0 then 0 else (n_d + hi) - 1
        let hp := if hi + 1 == h_sz then r_idx else (n_d + hi) + 1
        let fhm : Fin 7 := ⟨hm, hm_lt_seven htot7 (by omega) hhi⟩
        let fhp : Fin 7 := ⟨hp, hp_lt_seven htot7 hhi⟩
        fhm ≠ ⟨n_d + hi, by omega⟩ ∧
        fhp ≠ ⟨n_d + hi, by omega⟩ ∧
        fhm ≠ fhp ∧
        ∀ (Tw : Finset (Fin 7)), {fhm, fhp} ⊆ Tw →
          inOpenTriBool (S' ⟨n_d + hi, by omega⟩) (w' Tw) (S' fhm) (S' fhp) = true) ∧
      (∀ hi (hhi : hi < h_sz) (target : ℕ) (ht : target < 7),
        (((n_d ≤ target ∧ target < n_d + hi) ∨ target = 0) →
          orientSign (PolygonCore.zWitness w' ⟨n_d + hi, by omega⟩)
            (S' ⟨n_d + hi, by omega⟩) (S' ⟨target, ht⟩) = true) ∧
        (((n_d + hi < target ∧ target < n_d + h_sz) ∨ target = r_idx) →
          orientSign (PolygonCore.zWitness w' ⟨n_d + hi, by omega⟩)
            (S' ⟨n_d + hi, by omega⟩) (S' ⟨target, ht⟩) = false)) := by
    intro r_idx fl fr
    have hr_idx1 : r_idx = 1 := if_pos (by omega)
    have hfr_eq : fr = ⟨1, by omega⟩ := by ext; exact hr_idx1
    refine ⟨?_, ?_, ?_⟩
    · intro hi hhi Tw hsub
      have hl_in : l ∈ Tw.image σ := by
        rw [← hσ_0]; exact Finset.mem_image_of_mem σ (hsub (Finset.mem_insert_self fl {fr}))
      have hr_in : r ∈ Tw.image σ := by
        rw [← hσ_1, ← hfr_eq]
        exact Finset.mem_image_of_mem σ (hsub (Finset.mem_insert_of_mem (Finset.mem_singleton_self fr)))
      have hlr_sub : {l, r} ⊆ Tw.image σ := by
        intro z hz; simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl <;> assumption
      have hh_in : σ ⟨n_d + hi, by omega⟩ ∈ PolygonCore.certifiedSet P S w := by
        rw [hσ_h hi hhi]; exact (hblock (k_f + hi) (by omega)).mp ⟨by omega, by omega⟩
      have ht := htri_lr _ hh_in (Tw.image σ) hlr_sub
      dsimp only [S', w', relabelS, relabelW, Function.comp_apply]
      rwa [hσ_0, hfr_eq, hσ_1]
    · intro hh1 hi hhi hm hp fhm fhp
      have hfhm_ne : fhm ≠ ⟨n_d + hi, by omega⟩ := by
        intro e; have hv : hm = n_d + hi := congrArg Fin.val e; dsimp [hm] at hv
        by_cases h0 : hi = 0
        · simp only [h0, beq_self_eq_true, ↓reduceIte] at hv; omega
        · simp only [beq_false_of_ne h0, Bool.false_eq_true, ↓reduceIte] at hv; omega
      have hfhp_ne : fhp ≠ ⟨n_d + hi, by omega⟩ := by
        intro e; have hv : hp = n_d + hi := congrArg Fin.val e; dsimp [hp] at hv
        rw [hr_idx1] at hv
        by_cases h1 : hi + 1 = h_sz
        · simp only [h1, beq_self_eq_true, ↓reduceIte] at hv; omega
        · simp only [beq_false_of_ne h1, Bool.false_eq_true, ↓reduceIte] at hv; omega
      have hmp_ne : fhm ≠ fhp := by
        intro e; have hv : hm = hp := congrArg Fin.val e; dsimp [hm, hp] at hv
        rw [hr_idx1] at hv
        by_cases h0 : hi = 0 <;> by_cases h1 : hi + 1 = h_sz
        · omega
        · rw [beq_iff_eq.mpr h0, beq_false_of_ne h1] at hv; dsimp at hv; omega
        · rw [beq_false_of_ne h0, beq_iff_eq.mpr h1] at hv; dsimp at hv; omega
        · rw [beq_false_of_ne h0, beq_false_of_ne h1] at hv; dsimp at hv; omega
      refine ⟨hfhm_ne, hfhp_ne, hmp_ne, fun Tw hsub => ?_⟩
      let i_h : Fin (cb'.m + 3) := ⟨hi + 1, by change hi + 1 < cb.m + 3; omega⟩
      have hcb'_ih : cb'.p_idx i_h = ⟨n_d + hi, by omega⟩ := by
        rw [hcb'_idx i_h]
        apply Fin.ext
        change invHullPos n_d h_sz (hi + 1) = n_d + hi
        dsimp [invHullPos]; split_ifs <;> omega
      have hcb'_pred : cb'.p_idx (i_h - 1) = fhm := by
        rw [hcb'_idx (i_h - 1)]
        have hp_val : (i_h - 1).val = hi := by
          rw [fin_pred_val_pos i_h (by dsimp [i_h]; omega)]
          dsimp [i_h]
        apply Fin.ext
        change invHullPos n_d h_sz (i_h - 1).val = hm
        rw [hp_val]; dsimp [hm, invHullPos]
        by_cases h0 : hi = 0
        · simp only [h0, beq_self_eq_true, ↓reduceIte]
        · simp only [beq_false_of_ne h0, Bool.false_eq_true, ↓reduceIte]
          split_ifs <;> omega
      have hcb'_succ : cb'.p_idx (i_h + 1) = fhp := by
        rw [hcb'_idx (i_h + 1)]
        have hs_val : (i_h + 1).val = hi + 2 := by
          rw [fin_succ_val_eq i_h]
          dsimp [i_h]
          have : hi + 1 + 1 < cb'.m + 3 := by change hi + 1 + 1 < cb.m + 3; omega
          rw [if_pos this]
        apply Fin.ext
        change invHullPos n_d h_sz (i_h + 1).val = hp
        rw [hs_val]; dsimp [hp, invHullPos]
        rw [hr_idx1]
        by_cases h1 : hi + 1 = h_sz
        · simp only [h1, beq_self_eq_true, ↓reduceIte]
          split_ifs <;> omega
        · simp only [beq_false_of_ne h1, Bool.false_eq_true, ↓reduceIte]
          split_ifs <;> omega
      have hh_cb' : cb'.p_idx i_h ∈ PolygonCore.certifiedSet P S' w' := by
        rw [hcb'_ih, hH'_mem]; dsimp; omega
      have ht := certified_neighbor_tri_indexed_C6 hP' (by decide) cb' i_h hh_cb'
        (Tw := Tw) (by rwa [hcb'_pred, hcb'_succ])
      rwa [hcb'_ih, hcb'_pred, hcb'_succ] at ht
    · intro hi hhi target ht
      let h_orig := σ ⟨n_d + hi, by omega⟩
      have hh_orig_eq : h_orig = cb.p_idx (PolygonCore.finShift vc.i_max (k_f + hi)) := hσ_h hi hhi
      have hh_in : h_orig ∈ PolygonCore.certifiedSet P S w := by
        rw [hh_orig_eq]; exact (hblock (k_f + hi) (by omega)).mp ⟨by omega, by omega⟩
      obtain ⟨kh, hkh0, hkh_lt, hkh_eq, hleft_s, hright_s, _⟩ :=
        certified_zh_separation_C6 hP (by decide) cb vc hh_in
      have hkh_val : kh = k_f + hi := by
        have hinj := cb.hp_idx_inj (hkh_eq.trans hh_orig_eq)
        rw [PolygonCore.finShift_eq_add vc.i_max (by omega),
            PolygonCore.finShift_eq_add vc.i_max (by omega)] at hinj
        exact congrArg Fin.val (add_left_cancel hinj)
      have hzw : PolygonCore.zWitness w' ⟨n_d + hi, by omega⟩ = PolygonCore.zWitness w h_orig :=
        zWitness_relabelW_local σ w ⟨n_d + hi, by omega⟩
      constructor
      · intro hL
        rw [hzw]
        change orientSign (PolygonCore.zWitness w h_orig) (S h_orig) (S (σ ⟨target, ht⟩)) = true
        rcases hL with ⟨hge, hlt⟩ | rfl
        · let hj := target - n_d
          have htarget_eq : (⟨target, ht⟩ : Fin 7) = ⟨n_d + hj, by omega⟩ := by ext; dsimp [hj]; omega
          rw [htarget_eq, hσ_h hj (by omega)]
          exact hleft_s (k_f + hj) (by omega)
        · rw [hσ_0, hl_eq]
          exact hleft_s (k_f - 1) (by omega)
      · intro hR
        rw [hzw]
        change orientSign (PolygonCore.zWitness w h_orig) (S h_orig) (S (σ ⟨target, ht⟩)) = false
        rcases hR with ⟨hgt, hlt⟩ | rfl
        · let hj := target - n_d
          have htarget_eq : (⟨target, ht⟩ : Fin 7) = ⟨n_d + hj, by omega⟩ := by ext; dsimp [hj]; omega
          rw [htarget_eq, hσ_h hj (by omega)]
          exact hright_s (k_f + hj) (by omega) (by omega)
        · have ht1 : (⟨r_idx, ht⟩ : Fin 7) = ⟨1, by omega⟩ := by ext; exact hr_idx1
          rw [ht1, hσ_1, hr_eq]
          exact hright_s (k_g + 1) (by omega) (by omega)
  have hV_none : ValidCanonicalInstance P S' w'
      { n_d := n_d, h_sz := h_sz, lr_l := some 0,
        edges := List.replicate (7 - n_d) none, masks := [] } := by
    let sp0 : CaseSpec :=
      { n_d := n_d, h_sz := h_sz, lr_l := some 0,
        edges := List.replicate (7 - n_d) none, masks := [] }
    refine ⟨hP', hnd2', htot7, by dsimp; omega, hD'_mem, hH'_mem, ?_, ?_, ?_⟩
    · refine ⟨cb', ?_, ?_⟩
      · rw [buildBccw_some0_length (spec := sp0) hnd2' hh_pos rfl]
        exact hcb_len.symm
      · intro idx
        have hidx_lt : idx.val < n_d + h_sz := by have h1 : idx.val < cb.m + 3 := idx.isLt; omega
        rw [buildBccw_some0_get (spec := sp0) hnd2' hh_pos rfl hidx_lt, hcb'_idx idx]
    · intro _; exact ⟨0, by dsimp; omega, rfl, hpocket_all⟩
    · intro _ eIdx u_y he_lt hed
      rw [listGetOpt_eq_getElem?, List.getElem?_replicate] at hed
      rw [if_pos he_lt] at hed
      nomatch hed
  refine ⟨S', w', hV_none, fun hnd3 htot6 => ?_⟩
  -- Construct dc : CyclicSubsetBoundary S' D' via monotone restriction of cb'
  let m_d := n_d - 3
  have hmd_len : m_d + 3 = n_d := by omega
  let subMap : Fin (m_d + 3) → Fin (cb'.m + 3) := fun k =>
    if k.val = 0 then ⟨0, by omega⟩
    else ⟨k.val + h_sz, by have := k.isLt; omega⟩
  have hsub_mono : StrictMono subMap := by
    intro a b hab
    change (subMap a).val < (subMap b).val
    have ha := a.isLt; have hb := b.isLt; have hab' : a.val < b.val := hab
    by_cases ha0 : a.val = 0 <;> by_cases hb0 : b.val = 0
    · omega
    · dsimp [subMap]; rw [if_pos ha0, if_neg hb0]; dsimp; omega
    · omega
    · dsimp [subMap]; rw [if_neg ha0, if_neg hb0]; dsimp; omega
  have hcb'_sub : ∀ k : Fin (m_d + 3), cb'.p_idx (subMap k) = ⟨k.val, by have := k.isLt; omega⟩ := by
    intro k
    rw [hcb'_idx (subMap k)]
    apply Fin.ext
    change invHullPos n_d h_sz (subMap k).val = k.val
    have hk_lt := k.isLt
    by_cases hk0 : k.val = 0
    · dsimp [subMap]; rw [if_pos hk0, hk0]; rfl
    · dsimp [subMap]; rw [if_neg hk0]; dsimp [invHullPos]; split_ifs <;> omega
  have hdc_hcyc : ∀ i j k : Fin (m_d + 3), PolygonCore.CyclicOrder i j k →
      0 < orient2D (S' ⟨i.val, by have := i.isLt; omega⟩)
                   (S' ⟨j.val, by have := j.isLt; omega⟩)
                   (S' ⟨k.val, by have := k.isLt; omega⟩) := by
    intro i j k hcyc_ijk
    rw [← hcb'_sub i, ← hcb'_sub j, ← hcb'_sub k]
    exact cb'.hcyc (subMap i) (subMap j) (subMap k) (cyclicOrder_strictMono hsub_mono hcyc_ijk)
  let dc : PolygonCore.CyclicSubsetBoundary S'
      (PolygonCore.hullVertices S' \ PolygonCore.certifiedSet P S' w') := {
    m := m_d
    p_idx := fun k => ⟨k.val, by have := k.isLt; omega⟩
    hp_idx_inj := fun _ _ hab => Fin.ext (Fin.mk.inj hab)
    hp_idx_img := by
      ext x
      simp only [Finset.mem_image, Finset.mem_univ, true_and, hD'_mem]
      exact ⟨fun ⟨k, hk⟩ => by have hv : k.val = x.val := congrArg Fin.val hk; have := k.isLt; omega,
        fun hx => ⟨⟨x.val, by omega⟩, rfl⟩⟩
    hstrict := strictConvexCCWPoly_of_hcyc_local hdc_hcyc
    hcyc := hdc_hcyc
  }
  have hdc_m : dc.m = m_d := rfl
  have hD3' : 3 ≤ (PolygonCore.hullVertices S' \ PolygonCore.certifiedSet P S' w').card := by
    have hc := congrArg Finset.card dc.hp_idx_img
    rw [Finset.card_image_of_injective _ dc.hp_idx_inj, Finset.card_fin] at hc
    omega
  let D' := PolygonCore.hullVertices S' \ PolygonCore.certifiedSet P S' w'
  have hexit : ∀ (eIdx : ℕ) (he : eIdx < 7 - n_d),
      let fy : Fin 7 := ⟨n_d + eIdx, by omega⟩
      ∃ i : Fin (m_d + 3),
        0 < orient2D (S' (dc.p_idx i)) (S' (dc.p_idx (i + 1))) (w' D') ∧
        InOpenTri (w' D') (S' (dc.p_idx i)) (S' (dc.p_idx (i + 1))) (S' fy) ∧
        ∀ Tw : Finset (Fin 7), dc.p_idx i ∈ Tw → dc.p_idx (i + 1) ∈ Tw →
          inOpenTriBool (S' fy) (w' Tw) (S' (dc.p_idx i)) (S' (dc.p_idx (i + 1))) = true := by
    intro eIdx he fy
    have hfy_M : fy ∈ PolygonCore.interiorPoints S' ∪ PolygonCore.certifiedSet P S' w' := by
      by_cases hB : fy ∈ PolygonCore.hullVertices S'
      · apply Finset.mem_union_right
        by_contra hnotH
        have hD : fy ∈ D' := Finset.mem_sdiff.mpr ⟨hB, hnotH⟩
        rw [hD'_mem] at hD; dsimp [fy] at hD; omega
      · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hB⟩)
    obtain ⟨⟨i, ⟨hu_pos, hy_tri⟩, _⟩, hall⟩ := PolygonCore.exit_edge hP' (by decide) hD3' dc fy hfy_M
    refine ⟨i, hu_pos, hy_tri, fun Tw hi1 hi2 => ?_⟩
    have htri_Tw := (hall i hu_pos hy_tri).1 Tw
      ((hP'.shatters Tw _).mpr hi1) ((hP'.shatters Tw _).mpr hi2)
    have hy_ne1 : fy ≠ dc.p_idx i := by
      intro e; have hv : n_d + eIdx = i.val := congrArg Fin.val e; have := i.isLt; omega
    have hy_ne2 : fy ≠ dc.p_idx (i + 1) := by
      intro e; have hv : n_d + eIdx = (i + 1).val := congrArg Fin.val e
      have := (i + 1).isLt; change (i + 1).val < m_d + 3 at this; omega
    have hi_ne12 : dc.p_idx i ≠ dc.p_idx (i + 1) := by
      intro e; have hv : i.val = (i + 1).val := Fin.mk.inj e
      rw [fin_succ_val_eq i] at hv
      have := i.isLt; split_ifs at hv <;> omega
    exact (inOpenTriBool_S_w_S_S hP' hy_ne1 hy_ne2 hi_ne12 Tw).mpr htri_Tw
  let pickI : ∀ (eIdx : ℕ), eIdx < 7 - n_d → Fin (m_d + 3) :=
    fun eIdx he => Classical.choose (hexit eIdx he)
  -- Prepare pocket vertices & triangles on D' for Lemma 3.4(i)-(ii)
  let i_lr : Fin (m_d + 3) := ⟨0, by omega⟩
  let fl' : Fin 7 := ⟨0, by omega⟩
  let fr' : Fin 7 := ⟨1, by omega⟩
  have hil_dc : dc.p_idx i_lr = fl' := rfl
  have hir_dc : dc.p_idx (i_lr + 1) = fr' := by
    apply Fin.ext; change (i_lr + 1).val = 1
    rw [fin_succ_val_eq i_lr, if_pos (by dsimp [i_lr]; omega)]
  have hlr_sub_D' : {fl', fr'} ⊆ D' := by
    intro z hz; simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl <;> rw [hD'_mem] <;> dsimp [fl', fr'] <;> omega
  have htri_D'_h : ∀ (hi : ℕ) (hhi : hi < h_sz),
      InOpenTri (w' D') (S' fl') (S' fr') (S' ⟨n_d + hi, by omega⟩) := by
    intro hi hhi
    have hfr_cast : (⟨if 0 + 1 < n_d then 0 + 1 else 0, nextMod_lt_seven (by omega)⟩ : Fin 7) = fr' := by
      ext; dsimp [fr']; exact if_pos (by omega)
    have hbool := hpocket_all.1 hi hhi D' (by rwa [hfr_cast])
    rw [hfr_cast] at hbool
    exact (inOpenTriBool_S_w_S_S hP'
      (fun e => by have hv : n_d + hi = 0 := Fin.mk.inj e; omega)
      (fun e => by have hv : n_d + hi = 1 := Fin.mk.inj e; omega)
      (fun e => by have hv : (0 : ℕ) = 1 := Fin.mk.inj e; omega) D').mp hbool
  have hccw_cb' : ∀ (a b c : ℕ) (hab : a < b) (hbc : b < c) (hc : c < cb'.m + 3),
      0 < orient2D (S' (cb'.p_idx ⟨a, by omega⟩))
                   (S' (cb'.p_idx ⟨b, by omega⟩))
                   (S' (cb'.p_idx ⟨c, hc⟩)) := by
    intro a b c hab hbc hc
    exact cb'.hcyc ⟨a, by omega⟩ ⟨b, by omega⟩ ⟨c, hc⟩ (Or.inl ⟨hab, hbc⟩)
  have hcb'_0 : cb'.p_idx ⟨0, by omega⟩ = fl' := by
    rw [hcb'_idx]; apply Fin.ext; simp [invHullPos, fl']
  have hcb'_r : cb'.p_idx ⟨h_sz + 1, by omega⟩ = fr' := by
    rw [hcb'_idx]; apply Fin.ext
    change invHullPos n_d h_sz (h_sz + 1) = 1
    dsimp [invHullPos]; split_ifs <;> omega
  have hcb'_h : ∀ (hi : ℕ) (hhi : hi < h_sz),
      cb'.p_idx ⟨hi + 1, by omega⟩ = ⟨n_d + hi, by omega⟩ := by
    intro hi hhi
    rw [hcb'_idx]; apply Fin.ext
    change invHullPos n_d h_sz (hi + 1) = n_d + hi
    dsimp [invHullPos]; split_ifs <;> omega
  have hl_h0_r : 0 < orient2D (S' fl') (S' ⟨n_d + 0, by omega⟩) (S' fr') := by
    rw [← hcb'_0, ← hcb'_h 0 hh_pos, ← hcb'_r]
    exact hccw_cb' 0 1 (h_sz + 1) (by omega) (by omega) (by omega)
  -- Lemma 3.4(i): every pickI eIdx he ≠ 0, so 1 ≤ (pickI eIdx he).val
  have hpick_ge1 : ∀ (eIdx : ℕ) (he : eIdx < 7 - n_d), 1 ≤ (pickI eIdx he).val := by
    intro eIdx he
    have hspec := Classical.choose_spec (hexit eIdx he)
    have hne : pickI eIdx he ≠ i_lr :=
      exit_edge_ne_pocket_lr dc hil_dc hir_dc hl_h0_r (htri_D'_h 0 hh_pos) hspec.1
    have hv_ne : (pickI eIdx he).val ≠ 0 := fun e => hne (Fin.ext e)
    omega
  -- Lemma 3.4(ii): pocket exit-edge monotonicity
  have hpick_mono : ∀ (hi : ℕ) (hhi1 : hi + 1 < h_sz),
      (pickI (hi + 1) (by omega)).val ≤ (pickI hi (by omega)).val := by
    intro hi hhi1
    let i₁ := pickI hi (by omega)
    let i₂ := pickI (hi + 1) (by omega)
    have hs1 := Classical.choose_spec (hexit hi (by omega))
    have hs2 := Classical.choose_spec (hexit (hi + 1) (by omega))
    have hl12 : 0 < orient2D (S' fl') (S' ⟨n_d + hi, by omega⟩) (S' ⟨n_d + (hi + 1), by omega⟩) := by
      rw [← hcb'_0, ← hcb'_h hi (by omega), ← hcb'_h (hi + 1) hhi1]
      exact hccw_cb' 0 (hi + 1) (hi + 2) (by omega) (by omega) (by omega)
    have h12r : 0 < orient2D (S' ⟨n_d + hi, by omega⟩) (S' ⟨n_d + (hi + 1), by omega⟩) (S' fr') := by
      rw [← hcb'_h hi (by omega), ← hcb'_h (hi + 1) hhi1, ← hcb'_r]
      exact hccw_cb' (hi + 1) (hi + 2) (h_sz + 1) (by omega) (by omega) (by omega)
    have hl1r : 0 < orient2D (S' fl') (S' ⟨n_d + hi, by omega⟩) (S' fr') := by
      rw [← hcb'_0, ← hcb'_h hi (by omega), ← hcb'_r]
      exact hccw_cb' 0 (hi + 1) (h_sz + 1) (by omega) (by omega) (by omega)
    haveI : NeZero (dc.m + 3) := ⟨by change m_d + 3 ≠ 0; omega⟩
    have hstep := pocket_exit_edge_monotonicity dc hil_dc hir_dc hl12 h12r hl1r
      (htri_D'_h hi (by omega)) (htri_D'_h (hi + 1) hhi1)
      hs1.1 hs1.2.1 hs2.1 hs2.2.1
    have hge1 : 1 ≤ i₁.val := hpick_ge1 hi (by omega)
    have hge2 : 1 ≤ i₂.val := hpick_ge1 (hi + 1) (by omega)
    have hilr1 : i_lr + 1 = (1 : Fin (m_d + 3)) := by
      ext; rw [fin_succ_val_eq i_lr, if_pos (by dsimp [i_lr]; omega)]
      change 1 = 1 % (m_d + 3); exact (Nat.mod_eq_of_lt (by omega)).symm
    have hst1 : stepFromR i_lr i₁ = i₁.val - 1 := by
      unfold stepFromR; rw [hilr1]; exact fin_pred_val_pos i₁ hge1
    have hst2 : stepFromR i_lr i₂ = i₂.val - 1 := by
      unfold stepFromR; rw [hilr1]; exact fin_pred_val_pos i₂ hge2
    change stepFromR i_lr i₂ ≤ stepFromR i_lr i₁ at hstep
    rw [hst1, hst2] at hstep
    omega
  let raw : List ℕ := (List.range (7 - n_d)).map (fun eIdx =>
    if he : eIdx < 7 - n_d then (pickI eIdx he).val else 0)
  have hraw_len : raw.length = 7 - n_d := by simp [raw]
  have hraw_bnd : ∀ u ∈ raw, u < n_d ∧ (0 < h_sz → 1 ≤ u) := by
    intro u hu
    rcases List.mem_map.mp hu with ⟨eIdx, he_mem, rfl⟩
    have he : eIdx < 7 - n_d := List.mem_range.mp he_mem
    rw [dif_pos he]
    exact ⟨by have := (pickI eIdx he).isLt; omega, fun _ => hpick_ge1 eIdx he⟩
  have hraw_mono : ∀ i : ℕ, i + 1 < h_sz →
      ∀ u₁ u₂ : ℕ, raw[i]? = some u₁ → raw[i + 1]? = some u₂ → u₂ ≤ u₁ := by
    intro i hi1 u₁ u₂ hu1 hu2
    have hi_lt : i < 7 - n_d := by omega
    have hi1_lt : i + 1 < 7 - n_d := by omega
    dsimp [raw] at hu1 hu2
    rw [List.getElem?_map, List.getElem?_range hi_lt] at hu1
    rw [List.getElem?_map, List.getElem?_range hi1_lt] at hu2
    dsimp [Option.map] at hu1 hu2
    rw [dif_pos hi_lt] at hu1
    rw [dif_pos hi1_lt] at hu2
    injection hu1 with e1; injection hu2 with e2
    rw [← e1, ← e2]
    exact hpick_mono i hi1
  refine ⟨raw, hraw_len, hraw_bnd, hraw_mono, ?_⟩
  let sp_raw := mkRawStage2Spec n_d h_sz raw
  have hlr_raw : sp_raw.lr_l = some 0 := by
    dsimp [sp_raw, mkRawStage2Spec]; rw [if_neg (by omega)]
  refine ⟨hP', hnd2', htot7, by dsimp [mkRawStage2Spec]; omega, hD'_mem, hH'_mem, ?_, ?_, ?_⟩
  · refine ⟨cb', ?_, ?_⟩
    · rw [buildBccw_some0_length (spec := sp_raw) hnd2' hh_pos hlr_raw]
      exact hcb_len.symm
    · intro idx
      have hidx_lt : idx.val < n_d + h_sz := by have := idx.isLt; omega
      rw [buildBccw_some0_get (spec := sp_raw) hnd2' hh_pos hlr_raw hidx_lt, hcb'_idx idx]
      rfl
  · intro _; exact ⟨0, by dsimp [mkRawStage2Spec]; omega, hlr_raw, hpocket_all⟩
  · dsimp only [mkRawStage2Spec]
    intro _ eIdx u_y he_lt hed _ Tw hfu hfv
    rw [listGetOpt_eq_getElem?, List.getElem?_map] at hed
    dsimp [raw] at hed
    rw [List.getElem?_map, List.getElem?_range he_lt] at hed
    dsimp [Option.map] at hed
    rw [dif_pos he_lt] at hed
    injection hed with hsome
    injection hsome with hu_eq
    let i := pickI eIdx he_lt
    have hi_prop := (Classical.choose_spec (hexit eIdx he_lt)).2.2
    have hdc_i : dc.p_idx i = ⟨u_y, by omega⟩ := by
      ext; exact hu_eq
    have hdc_i1 : dc.p_idx (i + 1) =
        ⟨if u_y + 1 < n_d then u_y + 1 else 0, nextMod_lt_seven (by omega)⟩ := by
      apply Fin.ext
      change (i + 1).val = if u_y + 1 < n_d then u_y + 1 else 0
      rw [fin_succ_val_eq i]
      have hi_val : i.val = u_y := hu_eq
      rw [hi_val]
      split_ifs <;> omega
    have ht := hi_prop Tw (by rwa [hdc_i]) (by rwa [hdc_i1])
    rwa [hdc_i, hdc_i1] at ht

/-! ## 6. Master Exhaustive Reduction on `Fin 7` (`no_seven_shattered_of_62_skeletons`) -/

theorem no_seven_shattered_of_62_skeletons
    (h62 : ∀ (c : Fin 62) {P' : Set (ℝ × ℝ)} {S' : Fin 7 → ℝ × ℝ}
      {w' : Finset (Fin 7) → ℝ × ℝ},
      ValidCanonicalInstance P' S' w' (canonSpec c) → False)
    {P : Set (ℝ × ℝ)} {S : Fin 7 → ℝ × ℝ} {w : Finset (Fin 7) → ℝ × ℝ}
    (hP : ShatteredSimplePolygon P S w) : False := by
  have hB_le7 : (PolygonCore.hullVertices S).card ≤ 7 := by
    simpa using Finset.card_le_univ (PolygonCore.hullVertices S)
  by_cases hB7 : (PolygonCore.hullVertices S).card = 7
  · -- Stage 1: |B| = 7 (A = ∅)
    have hB_univ : PolygonCore.hullVertices S = Finset.univ :=
      Finset.eq_univ_of_card _ hB7
    have hA_emp_pc : PolygonCore.interiorPoints S = ∅ := by
      unfold PolygonCore.interiorPoints
      rw [hB_univ, Finset.sdiff_self]
    have hA_emp_rt : _root_.interiorPoints S = ∅ := by
      rwa [← SourceGapAndCaseSplits.interiorPoints_eq]
    have hcs := SourceGapAndCaseSplits.case_split_convex_seven hP hA_emp_rt
    dsimp only at hcs
    rw [← SourceGapAndCaseSplits.hullVertices_eq] at hcs
    rcases hcs with ⟨hH_mem_set, hD_eq, hD2, _⟩
    have hH_cases : (PolygonCore.certifiedSet P S w).card = 0 ∨
        (PolygonCore.certifiedSet P S w).card = 1 ∨
        (PolygonCore.certifiedSet P S w).card = 2 ∨
        (PolygonCore.certifiedSet P S w).card = 3 ∨
        (PolygonCore.certifiedSet P S w).card = 4 ∨
        (PolygonCore.certifiedSet P S w).card = 5 := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hH_mem_set
      exact hH_mem_set
    rcases hH_cases with hh0 | hh1 | hh2 | hh3 | hh4 | hh5
    · -- Stage 1 Case (7, 0): 100% certificate-free deductive elimination!
      exact no_unmarked_convex_seven_shattered S w hP hA_emp_pc (Finset.card_eq_zero.mp hh0)
    · obtain ⟨S', w', hV, _⟩ := exists_precanonical_hpos hP (by omega) hD2 (by omega)
      rw [hD_eq, hh1] at hV
      exact h62 ⟨0, by decide⟩ hV
    · obtain ⟨S', w', hV, _⟩ := exists_precanonical_hpos hP (by omega) hD2 (by omega)
      rw [hD_eq, hh2] at hV
      exact h62 ⟨1, by decide⟩ hV
    · obtain ⟨S', w', hV, _⟩ := exists_precanonical_hpos hP (by omega) hD2 (by omega)
      rw [hD_eq, hh3] at hV
      exact h62 ⟨2, by decide⟩ hV
    · obtain ⟨S', w', hV, _⟩ := exists_precanonical_hpos hP (by omega) hD2 (by omega)
      rw [hD_eq, hh4] at hV
      exact h62 ⟨3, by decide⟩ hV
    · obtain ⟨S', w', hV, _⟩ := exists_precanonical_hpos hP (by omega) hD2 (by omega)
      rw [hD_eq, hh5] at hV
      exact h62 ⟨4, by decide⟩ hV
  · -- Stage 2: |B| ≤ 6
    have hB6_rt : (_root_.hullVertices S).card ≤ 6 := by
      rw [← SourceGapAndCaseSplits.hullVertices_eq]; omega
    have hcs := SourceGapAndCaseSplits.case_split_seven_ub6 hP hB6_rt
    dsimp only at hcs
    rw [← SourceGapAndCaseSplits.hullVertices_eq] at hcs
    rcases hcs with ⟨hB3, hB6, _, hcases⟩
    let n_d := (PolygonCore.hullVertices S \ PolygonCore.certifiedSet P S w).card
    let h_sz := (PolygonCore.certifiedSet P S w).card
    have hBDH : (PolygonCore.hullVertices S).card = n_d + h_sz :=
      (Finset.card_sdiff_add_card_eq_card (Finset.filter_subset _ _)).symm
    by_cases hnd2_eq : n_d = 2
    · -- Stage 2 with n_d = 2 (h_sz ∈ {1, 2, 3, 4}): Cases 59..62 (indices 58..61)
      have hh_cases : h_sz = 1 ∨ h_sz = 2 ∨ h_sz = 3 ∨ h_sz = 4 := by omega
      obtain ⟨S', w', hV, _⟩ := exists_precanonical_hpos hP (by omega) (by omega) hB3
      change ValidCanonicalInstance P S' w'
        { n_d := n_d, h_sz := h_sz, lr_l := some 0,
          edges := List.replicate (7 - n_d) none, masks := [] } at hV
      rcases hh_cases with hh | hh | hh | hh
      · rw [hnd2_eq, hh] at hV; exact h62 ⟨58, by decide⟩ hV
      · rw [hnd2_eq, hh] at hV; exact h62 ⟨59, by decide⟩ hV
      · rw [hnd2_eq, hh] at hV; exact h62 ⟨60, by decide⟩ hV
      · rw [hnd2_eq, hh] at hV; exact h62 ⟨61, by decide⟩ hV
    · -- Stage 2 with 3 ≤ n_d ≤ 6: monotone exit edges + dihedral normalization to 5..57!
      have hnd_range : 3 ≤ n_d ∧ n_d ≤ 6 := by
        rcases hcases with ⟨hd, _⟩ | ⟨hd, _⟩ | ⟨hd, _⟩ | ⟨hd, _⟩ | ⟨hd, _⟩ <;>
          (change n_d = _ at hd; omega)
      have hh_lt : h_sz < 7 - n_d := by omega
      have hraw_ex : ∃ (S' : Fin 7 → ℝ × ℝ) (w' : Finset (Fin 7) → ℝ × ℝ) (raw : List ℕ),
          raw.length = 7 - n_d ∧
          (∀ u ∈ raw, u < n_d ∧ (0 < h_sz → 1 ≤ u)) ∧
          (∀ i : ℕ, i + 1 < h_sz →
            ∀ u₁ u₂ : ℕ, raw[i]? = some u₁ → raw[i + 1]? = some u₂ → u₂ ≤ u₁) ∧
          ValidCanonicalInstance P S' w' (mkRawStage2Spec n_d h_sz raw) := by
        by_cases hh0 : h_sz = 0
        · obtain ⟨S', w', raw, hlen, hbnd0, hV⟩ :=
            exists_precanonical_h0 hP hh0 hnd_range.1 hnd_range.2
          refine ⟨S', w', raw, hlen, ?_, ?_, ?_⟩
          · intro u hu; exact ⟨hbnd0 u hu, fun hp => by omega⟩
          · intro i hi1; omega
          · rw [hh0]; exact hV
        · obtain ⟨S', w', _, hex⟩ :=
            exists_precanonical_hpos hP (Nat.pos_of_ne_zero hh0) (by omega) hB3
          obtain ⟨raw, hlen, hbnd, hmono, hV⟩ := hex hnd_range.1 (by omega)
          exact ⟨S', w', raw, hlen, hbnd, hmono, hV⟩
      obtain ⟨S', w', raw, hlen, hbnd, hmono, hV⟩ := hraw_ex
      have hnorm := stage2_monotone_to_canonical hnd_range hh_lt hlen hbnd hmono
      rcases htup : lookupStage2Action n_d h_sz raw with ⟨c, doRefl, rotSteps, swaps⟩
      rw [htup] at hnorm
      rcases hnorm with ⟨_, hswaps, hspec_eq⟩
      have hed_wf : EdgesBounded (mkRawStage2Spec n_d h_sz raw) := by
        intro eIdx u hed
        dsimp [mkRawStage2Spec] at hed
        rw [listGetOpt_eq_getElem?, List.getElem?_map] at hed
        cases hr : raw[eIdx]? with
        | none => rw [hr] at hed; nomatch hed
        | some u0 =>
          rw [hr] at hed; dsimp [Option.map] at hed
          injection hed with hsome; injection hsome with hu0
          subst hu0
          exact (hbnd u0 (List.mem_of_getElem? hr)).1
      obtain ⟨P'', S'', w'', hV''⟩ :=
        hV.applyDihedralNorm rfl hed_wf doRefl rotSteps swaps [] hswaps
      rw [hspec_eq] at hV''
      exact h62 c hV''

end VCDim6

end
