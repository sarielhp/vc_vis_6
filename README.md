# The VC-dimension of visibility in simple polygons is six

Supplementary material for the paper

> Dror Aiger and Sariel Har-Peled,
> *The VC-Dimension of Visibility in Simple Polygons Is Six*.

The paper proves that no simple polygon shatters seven targets by
visibility. Together with Valtr's construction of a polygon shattering six
targets, this shows that the maximum visibility VC-dimension of a simple
polygon is six. This repository contains the computational evidence for
the upper bound and an independent Lean 4 formalization.

## Contents

| Directory | What it contains |
|---|---|
| [`certificates/`](certificates/) | The formula generator, a manifest of the 74 hull cases with formula digests, and one DRAT refutation per case. This is the computation the paper's proof relies on. |
| [`lean/`](lean/) | An independent Lean 4 proof of the upper bound, `simple_polygon_vcdim_le_six`. |
| [`earlier_encoder/`](earlier_encoder/) | The earlier encoder, its solver records, and algebraic checks with Z3. The proof does not depend on it. |
| [`replay.sh`](replay.sh) | Regenerates every formula and checks its refutation. |

## Replaying the certificates

Requirements: a C compiler, [Julia](https://julialang.org/), and the
QuickEnv.jl package.

```sh
sh replay.sh                 # all 74 cases
sh replay.sh s1-d2-h5-none   # a single case (IDs are listed in certificates/manifest.tsv)
```

For each case the replay checks that the manifest agrees with the
exhaustive enumeration of hull cases, regenerates the DIMACS formula,
rechecks the geometric derivation of every saved cut, compares the
formula's SHA-256 digest with the manifest, and verifies the saved proof
with the bundled `drat-trim` checker. A successful run prints one
`verified` line per case. See [`certificates/README.md`](certificates/README.md)
for how the clauses correspond to the clause families of the paper.

## Building the Lean proof

```sh
cd lean
lake exe cache get   # download prebuilt Mathlib
lake build
```

The project uses Lean 4.31.0 and Mathlib v4.31.0, as pinned in
`lean-toolchain` and `lake-manifest.json`. The statements are in
[`lean/RootTask/VCDimSixFullTheorem.lean`](lean/RootTask/VCDimSixFullTheorem.lean):

- `simple_polygon_vcdim_le_six`: no configuration of seven or more
  targets and their witnesses satisfies `ShatteredSimplePolygon`;
- `simple_polygon_vcdim_le_eleven`: the intermediate bound of eleven.

For both theorems `#print axioms` reports only `propext`,
`Classical.choice`, and `Quot.sound`. There is no `sorry`, no custom
axiom, and no `native_decide`.

The predicate `ShatteredSimplePolygon` (see
[`lean/RootTask/PolygonDefs.lean`](lean/RootTask/PolygonDefs.lean)) is an
interface for simple polygons. It provides general position, open
neighborhoods of the witnesses, and enclosure properties. The paper
justifies applying this interface to ordinary simple polygons.

The Lean development follows an earlier version of the case analysis
than the paper. Formalized geometric arguments eliminate the all-hull
case (7,0) and the 11 cases in which the exit edges of consecutive
certified vertices are out of order. A RUP checker proved sound in Lean
refutes the remaining 62 cases from 1,596 certificate files. Theorem and
section numbers in the Lean comments refer to that earlier manuscript.
The paper instead checks DRAT certificates for all 74 cases.

## Authors

- Dror Aiger
- Sariel Har-Peled
