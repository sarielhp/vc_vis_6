# `VC-dim(P) <= 6` (`|S| = 7`, `128` masks) Closure Ledger — ALL `68 / 68` Orbits `UNSAT`!

**Workspace:** `verification/sat_cegar/`

Combining the blind-certified `|B| <= 6` theorem (`convex7_close/`, which proves no simple polygon shatters a strictly convex 7-gon) with the results below proves **no simple polygon $P \subset \mathbb{R}^2$ shatters any $7$-point set $S$**, i.e., **$\operatorname{VC-dim}(P) \le 6$** (matching the $\ge 6$ lower bound `seed46_k6` for $\operatorname{VC-dim}(P) = 6$).

All runs streamed clauses via stdout (`0` `.cnf` files on disk) into `cadical195` (with `glucose4` cross-check on `(6, 1)`) under `systemd-run --user --scope -p MemoryMax=6G` with `exit 0`.

---

## 1. Ground-Truth Soundness Validation (`|S| = 7`, `0` Violations, `exit 0`)

Script: [validate_ub6.py](file://verification/sat_cegar/validate_ub6.py)

| Certificate | Split `(n_d, |H|, |A|)` | `m` | Clauses | Result | Missing Masks by Popcount |
| :--- | :---: | :---: | :---: | :--- | :--- |
| `CORNER_CERT_85` (`h1`) | `(4, 1, 2)` | `28/85` | `19,275,765` | `SAT (0 violations, CEGAR rnd=0, n1=0)` | `{2:3, 3:13, 4:16, 5:9, 6:2}` (`36.16s`) |
| `CERTV2_85` (`h1`) | `(5, 1, 1)` | `28/85` | `19,846,746` | `SAT (0 violations, CEGAR rnd=0, n1=0)` | `{2:3, 3:14, 4:18, 5:8}` (`35.75s`) |
| `CERTV2_82` (`h1`) | `(4, 2, 1)` | `28/82` | `19,363,779` | `SAT (0 violations, CEGAR rnd=0, n1=0)` | `{2:6, 3:16, 4:16, 5:7, 6:1}` (`34.13s`) |
| `c6free_94_D3` (`h1`) | `(3, 0, 4)` | `28/94` | `18,844,398` | `SAT (0 violations, CEGAR rnd=0, n1=0)` | `{2:1, 3:10, 4:14, 5:7, 6:2}` (`34.95s`) |
| `c6free_109` (`h1`) | `(4, 0, 3)` | `28/109` | `18,665,989` | `SAT (0 violations, CEGAR rnd=0, n1=0)` | `{3:6, 4:7, 5:5, 6:1}` (`34.18s`) |
| `c6free_112` (`h0 gap=1`) | `(5, 0, 2)` | `28/112` | `18,543,580` | `SAT (0 violations, CEGAR rnd=0, n1=0)` | `{3:4, 4:6, 5:5, 6:1}` (`34.72s`) |
| `HOPPERV2_116` (`h0 gap=1`) | `(6, 0, 1)` | `28/116` | `19,334,338` | `SAT (0 violations, CEGAR rnd=0, n1=0)` | `{3:4, 4:5, 5:3}` (`35.78s`) |

---

## 2. Exhaustive `UNSAT` Ledger Across All `5` Chunks (`68 / 68` Orbits)

| Chunk `(n_d, |M|)` | Subcases (`|H|`) | Orbits | `m` | CEGAR Iters / Cuts | Time | Result |
| :--- | :--- | :---: | :---: | :---: | :---: | :--- |
| **`(6, 1)`** (`solve_ub6_61.py`) | `|H|=0` (`e="0"`) | `1 / 1` | `34` | `12 iters / 15,404` (`cadical195`, also `11 iters` `gap=0` in `27.9s` & `glucose4` `gap=1` in `13.8s`) | `20.0s` | **`UNSAT`** |
| **`(5, 2)`** (`solve_ub6_52.py`) | `|H|=0` (`00, 01, 02`) | `3 / 3` | `36` | `7..14 iters / 9,866..17,576` | `19.7s..36.8s` | **`UNSAT`** |
| **`(5, 2)`** (`solve_ub6_52.py`) | `|H|=1` (`lr=40, h in {0,1}, a in {0..3}`) | `8 / 8` | `36` | `2..6 iters / 2,988..6,907` | `4.8s..6.1s` | **`UNSAT`** |
| **`(4, 3)`** (`solve_ub6_43_34_25.py`) | `|H|=0` (`4`), `|H|=1` (`10`), `|H|=2` (`15`) | `29 / 29` | `34..36` | `0..78 iters / 0..33,694` | `4.3s..136.6s` (tot `136.7s`) | **`UNSAT`** |
| **`(3, 4)`** (`solve_ub6_43_34_25.py`) | `|H|=0` (`4`), `|H|=1` (`4`), `|H|=2` (`7`), `|H|=3` (`8`) | `23 / 23` | `37..40` (`22`), `68` (`#02`) | `0..116 iters / 0..40,937` | `4.9s..258.7s` (tot `258.9s`) | **`UNSAT`** |
| **`(2, 5)`** (`solve_ub6_43_34_25.py`) | `|H|=1` (`1`), `|H|=2` (`1`), `|H|=3` (`1`), `|H|=4` (`1`) | `4 / 4` | `47` | `3..5 iters / 4,617..7,623` | `9.9s..217.4s` (tot `217.5s`) | **`UNSAT`** |
| **Total** | **All `|B| <= 6` partitions of `|S| = 7`** | **`68 / 68`** | `34..68` | — | — | **`68 / 68 UNSAT`** |

Note on `(2, 5)`: `edge_str = "xxxxx"` disables `lem:exit-edge` (`|D| = 2 < 3`); only `|B| >= 3` / `|D| = 2`-sound clauses (`Prop certified-structure`, `Def certified`, `Lemma separation`, `Lemma side-corners`, `Lemma 2.1(ii)`, `Lemma 4.4`, `vis_SS`, CEGAR enclosure + `N1`) are emitted.
