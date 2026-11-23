# Independent certificates for polygon visibility

The simplest way to replay everything is `sh replay.sh` from the repository root (see the top-level README). Equivalently, from this directory, build the bundled drat-trim checker and run the following commands with Julia and QuickEnv.jl. Add a case ID from `manifest.tsv` to the final command to replay just that case.

```sh
review_tmp="/tmp/$USER/vc_dim_vis_polys/replay"
mkdir -p "$review_tmp"
cc -std=gnu99 -O2 drat-trim/drat-trim.c -o "$review_tmp/drat-trim"
julia replay.jl "$review_tmp" "$review_tmp/drat-trim"
```

For each case the program regenerates the DIMACS formula, independently validates any learned geometric cuts, checks the SHA-256 digest against the manifest, and passes the saved proof to drat-trim. It requires a successful exit and the explicit verification status. The `-U -p` options check reverse-unit-propagation steps with clause deletions ignored. The program removes the large regenerated CNF after success and retains its checker log. Only one case at a time is stored when replay runs sequentially.

## From geometry to clauses

`cases.jl` enumerates the six convex cases and all dihedral orbits for the five general-case splits. For a nonempty certified block, the distinguished pocket edge is the last edge of D. A reflection reverses the order of certified vertices and permutes the unordered interior vertices. The code numbers the targets from 1 to 7. Bit number k, counting from zero, refers to target k+1.

`encoding.jl` assigns one Boolean variable to each free unordered triple, with signed literals for permutations. It fixes the counterclockwise hull triples and constrains interior targets to the inward side of every hull edge. For an actual configuration, assign every other sign its Euclidean value and every graph edge the true visibility of its endpoints. These values obey the Grassmann–Plücker relations, the four-point signed-area identity, and the non-certified hull, exit-edge, certified pocket and half-plane implications proved in the paper. Each auxiliary implication variable for the half-plane rule may be set to the truth of its antecedent. In particular, the universal witness sees every target.

The variables in `enclosure.jl` and `eager.jl` encode consequences of Jordan enclosure. For an invisible pair u,v, at least one of the two sides of the line uv has no visibility path from u to v through internal vertices on that side. Select such a side, mark its points and the two endpoints active, and color connected components of the induced visible-edge graph so the endpoints have opposite colors. All active visible edges then have equal-colored ends. This supplies a satisfying assignment to every such side and color variable. A visible triangle contains its interior and gives visibility from each interior point to each corner. The base and strong encodings use different subsets of these necessary conditions. Omitting a condition preserves soundness of an UNSAT result.

For a saved refinement clause, `cuts.jl` assumes its negation. It restores the fixed hull signs and the specified signs only, seeds the graph with the prescribed positive witness–target incidences, and repeatedly applies same-triangle and two-sided-path enclosure. It accepts the clause only on deriving a prescribed missed edge. Unknown orientations are excluded from all side and triangle tests. This check requires no saved SAT model.

Two variants encode radial order in `angular.jl`. At a fixed pivot p, choose a reference vector r−p. Reverse each other direction i−p if it lies on the right of the reference vector. All transformed directions fit in the same open half-plane. Their pairwise comparison signs equal the original comparison signs multiplied by the two reversal signs, and their order must be transitive. One triangular-hull case uses the usual unaugmented family plus the first eight extra four-target masks in increasing numeric order. In the dart variant, `darts.jl` explicitly checks convex four-cycles and each possible reflex vertex, using the triangle and same-side visibility implications of the quadrilateral and dart lemma in the paper.

## What is supplied

- `manifest.tsv` specifies each independently generated formula, its variant, variable and clause counts, and SHA-256 digest.
- Each `cases/<id>/proof.drat` is the trimmed proof for the indicated formula. A case with learned cuts also contains `cuts.txt` with their exact literals in DIMACS order.
- `replay.jl` regenerates and checks the evidence. It requires no original Lean, Z3, or SAT files from the authors.
- `controls.jl` exercises the encodings on integer-coordinate polygons with known partial visibility data. It includes a case where the half-plane antecedent holds. It uses MiniSat. Run it from a scratch directory with a `controls` subdirectory. The seven saved results are in `positive-controls.log`.

The certificate producer was CaDiCaL 1.9.5. The checker was built from drat-trim source with SHA-256 `d834b649f437e091597f5347f259b9f681087f89ca0844d0cee250a1a1a0c2ee` for `drat-trim.c`, using `cc -std=gnu99 -O2 drat-trim.c -o drat-trim`. The replay was tested with Julia 1.13.3. [CaDiCaL source](https://github.com/arminbiere/cadical/tree/rel-1.9.5) · [drat-trim source](https://github.com/marijnheule/drat-trim)

