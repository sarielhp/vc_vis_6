#!/usr/bin/env python3
"""Self-contained streaming CNF + CEGAR (bulk_cegar_enclosure + lazy N1) engine for ub7."""
import subprocess
from collections import deque
from pysat.solvers import Solver


def o_pos(n_pts, a, b, c):
    lst = [a, b, c]
    inv = 0
    if lst[0] > lst[1]:
        lst[0], lst[1] = lst[1], lst[0]
        inv += 1
    if lst[1] > lst[2]:
        lst[1], lst[2] = lst[2], lst[1]
        inv += 1
    if lst[0] > lst[1]:
        lst[0], lst[1] = lst[1], lst[0]
        inv += 1
    i, j, k = lst
    idx = 0
    for x in range(i):
        idx += (n_pts - 1 - x) * (n_pts - 2 - x) // 2
    for y in range(i + 1, j):
        idx += n_pts - 1 - y
    idx += (k - j)
    return idx if inv % 2 == 0 else -idx


def stream_clauses(bin_path, args, solver_name="cadical195"):
    proc = subprocess.Popen(
        [bin_path] + args,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        bufsize=4 * 1024 * 1024,
    )
    nv, ncl = 0, 0
    s = Solver(name=solver_name)
    batch = []
    for line in proc.stdout:
        c = line[0]
        if c == 'c':
            continue
        if c == 'p':
            parts = line.split()
            nv, ncl = int(parts[2]), int(parts[3])
            continue
        batch.append(list(map(int, line.split()[:-1])))
        if len(batch) >= 100000:
            s.append_formula(batch)
            batch.clear()
    if batch:
        s.append_formula(batch)
    proc.wait()
    err = proc.stderr.read().strip()
    if proc.returncode != 0:
        raise RuntimeError(f"{bin_path} failed ({proc.returncode}): {err}")
    return s, nv, ncl


def build_sgn_tlit(n_pts, model_set):
    sgn = [[[0] * n_pts for _ in range(n_pts)] for _ in range(n_pts)]
    tlit = [[[0] * n_pts for _ in range(n_pts)] for _ in range(n_pts)]
    for i in range(n_pts):
        for j in range(i + 1, n_pts):
            for k in range(j + 1, n_pts):
                v = o_pos(n_pts, i, j, k)
                is_pos = (v in model_set) if v > 0 else ((-v) not in model_set)
                sg, lt = (1, v) if is_pos else (-1, -v)
                sgn[i][j][k] = sg; tlit[i][j][k] = lt
                sgn[j][k][i] = sg; tlit[j][k][i] = lt
                sgn[k][i][j] = sg; tlit[k][i][j] = lt
                sgn[j][i][k] = -sg; tlit[j][i][k] = lt
                sgn[i][k][j] = -sg; tlit[i][k][j] = lt
                sgn[k][j][i] = -sg; tlit[k][j][i] = lt
    return sgn, tlit


def bulk_cegar_enclosure(n_s, masks, sgn, tlit, max_rounds=6):
    n_pts = n_s + len(masks)
    adj = [set() for _ in range(n_pts)]
    deriv = {}
    for idx, m in enumerate(masks):
        w = n_s + idx
        for s in range(n_s):
            if (m >> s) & 1:
                adj[w].add(s)
                adj[s].add(w)
                deriv[(s, w)] = frozenset()

    def get_deriv(u, v):
        return deriv[(u, v) if u < v else (v, u)]

    def find_side_paths(u, v, want, max_paths=2):
        q = deque()
        dist = {u: 0}
        preds = {}
        for nb in adj[u]:
            if nb == v:
                return [[u, v]]
            if sgn[u][v][nb] == want:
                dist[nb] = 1
                preds[nb] = [u]
                q.append(nb)
        best_d = None
        v_preds = []
        while q:
            cur = q.popleft()
            if best_d is not None and dist[cur] >= best_d:
                continue
            for nb in adj[cur]:
                if nb == v:
                    best_d = dist[cur] + 1
                    v_preds.append(cur)
                elif sgn[u][v][nb] == want:
                    if nb not in dist:
                        dist[nb] = dist[cur] + 1
                        preds[nb] = [cur]
                        q.append(nb)
                    elif dist[nb] == dist[cur] + 1 and len(preds[nb]) < 2:
                        preds[nb].append(cur)
        if not v_preds:
            return []
        paths = []
        for vp in v_preds[:max_paths]:
            p = [v, vp]
            cur = vp
            while cur != u:
                cur = preds[cur][0]
                p.append(cur)
            p.reverse()
            paths.append(p)
        return paths

    all_cuts = set()
    first_bad_rnd = 0
    for rnd in range(1, max_rounds + 1):
        new_edges = {}
        for u in range(n_pts):
            for v in range(u + 1, n_pts):
                if v in adj[u]:
                    continue
                p1s = find_side_paths(u, v, 1, max_paths=2)
                if not p1s:
                    continue
                p2s = find_side_paths(u, v, -1, max_paths=2)
                if not p2s:
                    continue
                best_lits = None
                for p1 in p1s:
                    for p2 in p2s:
                        lits = set()
                        for pi in range(len(p1) - 1):
                            lits |= get_deriv(p1[pi], p1[pi + 1])
                            if pi > 0:
                                lits.add(tlit[u][v][p1[pi]])
                        for pi in range(len(p2) - 1):
                            lits |= get_deriv(p2[pi], p2[pi + 1])
                            if pi > 0:
                                lits.add(tlit[u][v][p2[pi]])
                        is_forb = (u < n_s and v >= n_s and not ((masks[v - n_s] >> u) & 1))
                        if is_forb:
                            all_cuts.add(tuple(sorted(-l for l in lits)))
                        if best_lits is None or len(lits) < len(best_lits):
                            best_lits = frozenset(lits)
                new_edges[(u, v)] = best_lits

        for a in range(n_pts):
            for b in adj[a]:
                if b <= a:
                    continue
                for c in (adj[a] & adj[b]):
                    if c <= b:
                        continue
                    base = get_deriv(a, b) | get_deriv(b, c) | get_deriv(c, a)
                    s1 = sgn[a][b][c]
                    inside = []
                    for u in range(n_pts):
                        if u in (a, b, c):
                            continue
                        if sgn[a][b][u] == s1 and sgn[b][c][u] == s1 and sgn[c][a][u] == s1:
                            inside.append(u)
                    for u in inside:
                        ul = base | {tlit[a][b][u], tlit[b][c][u], tlit[c][a][u]}
                        for v in (a, b, c):
                            key = (min(u, v), max(u, v))
                            if key[1] not in adj[key[0]]:
                                is_forb = (key[0] < n_s and key[1] >= n_s and not ((masks[key[1] - n_s] >> key[0]) & 1))
                                if is_forb:
                                    all_cuts.add(tuple(sorted(-l for l in ul)))
                                if key not in new_edges or len(ul) < len(new_edges[key]):
                                    new_edges[key] = frozenset(ul)
                        for v in inside:
                            if v > u and v not in adj[u]:
                                uvl = ul | {tlit[a][b][v], tlit[b][c][v], tlit[c][a][v]}
                                is_forb = (u < n_s and v >= n_s and not ((masks[v - n_s] >> u) & 1))
                                if is_forb:
                                    all_cuts.add(tuple(sorted(-l for l in uvl)))
                                key = (u, v)
                                if key not in new_edges or len(uvl) < len(new_edges[key]):
                                    new_edges[key] = frozenset(uvl)

        if not new_edges:
            break
        for (u, v), dl in new_edges.items():
            adj[u].add(v)
            adj[v].add(u)
            deriv[(u, v)] = dl
        if all_cuts and first_bad_rnd == 0:
            first_bad_rnd = rnd
            break

    return first_bad_rnd, [list(c) for c in sorted(all_cuts, key=len)]


def find_violated_n1_cuts(n_s, masks, sgn, tlit, max_cuts=1500):
    cuts = []
    seen_cuts = set()
    for fj in range(n_s):
        for b in range(n_s):
            if b == fj:
                continue
            sees_jb = [n_s + i for i, m in enumerate(masks) if ((m >> fj) & 1) and ((m >> b) & 1)]
            misses_j = [n_s + i for i, m in enumerate(masks) if not ((m >> fj) & 1)]
            for idx1 in range(len(sees_jb)):
                w1 = sees_jb[idx1]
                for idx2 in range(idx1 + 1, len(sees_jb)):
                    w2 = sees_jb[idx2]
                    s1 = sgn[w1][fj][w2]
                    if sgn[fj][w2][b] == s1 and sgn[w2][b][w1] == s1 and sgn[b][w1][fj] == s1:
                        base = [tlit[w1][fj][w2], tlit[fj][w2][b], tlit[w2][b][w1], tlit[b][w1][fj]]
                        for fw in misses_j:
                            if fw == w1 or fw == w2:
                                continue
                            if sgn[w1][fj][fw] == s1 and sgn[fj][w2][fw] == s1 and sgn[w2][b][fw] == s1 and sgn[b][w1][fw] == s1:
                                cl = tuple(sorted(-l for l in (base + [tlit[w1][fj][fw], tlit[fj][w2][fw], tlit[w2][b][fw], tlit[b][w1][fw]])))
                                if cl not in seen_cuts:
                                    seen_cuts.add(cl)
                                    cuts.append(list(cl))
                                    if len(cuts) >= max_cuts:
                                        return cuts
                        continue
                    pts = (w1, fj, w2, b)
                    for r in range(4):
                        i0, i1, i2, i3 = r, (r + 1) % 4, (r + 2) % 4, (r + 3) % 4
                        vr, vp, vq, vs = pts[i0], pts[i1], pts[i2], pts[i3]
                        sd = sgn[vp][vq][vs]
                        if sgn[vp][vq][vr] == sd and sgn[vq][vs][vr] == sd and sgn[vs][vp][vr] == sd:
                            dart_lits = [tlit[vp][vq][vr], tlit[vq][vs][vr], tlit[vs][vp][vr]]
                            for fw in misses_j:
                                if fw == w1 or fw == w2:
                                    continue
                                if i0 == 1 or i2 == 1:
                                    for a1, a2, a3 in ((vr, vp, vq), (vr, vq, vs)):
                                        st = sgn[a1][a2][a3]
                                        if sgn[a1][a2][fw] == st and sgn[a2][a3][fw] == st and sgn[a3][a1][fw] == st:
                                            cl = tuple(sorted(-l for l in (dart_lits + [tlit[a1][a2][fw], tlit[a2][a3][fw], tlit[a3][a1][fw]])))
                                            if cl not in seen_cuts:
                                                seen_cuts.add(cl)
                                                cuts.append(list(cl))
                                                if len(cuts) >= max_cuts:
                                                    return cuts
                                elif i1 == 1:
                                    if sgn[vp][vq][fw] == sd and sgn[vq][vs][fw] == sd and sgn[vs][vp][fw] == sd and sgn[vr][vp][fw] == sgn[vr][vp][vq]:
                                        l1 = tlit[vr][vp][fw]; l2 = tlit[vr][vp][vq]
                                        cl = tuple(sorted(-l for l in (dart_lits + [tlit[vp][vq][fw], tlit[vq][vs][fw], tlit[vs][vp][fw], l1, l2])))
                                        if cl not in seen_cuts:
                                            seen_cuts.add(cl)
                                            cuts.append(list(cl))
                                            if len(cuts) >= max_cuts:
                                                return cuts
                                elif i3 == 1:
                                    if sgn[vp][vq][fw] == sd and sgn[vq][vs][fw] == sd and sgn[vs][vp][fw] == sd and sgn[vr][vs][fw] == sgn[vr][vs][vq]:
                                        l1 = tlit[vr][vs][fw]; l2 = tlit[vr][vs][vq]
                                        cl = tuple(sorted(-l for l in (dart_lits + [tlit[vp][vq][fw], tlit[vq][vs][fw], tlit[vs][vp][fw], l1, l2])))
                                        if cl not in seen_cuts:
                                            seen_cuts.add(cl)
                                            cuts.append(list(cl))
                                            if len(cuts) >= max_cuts:
                                                return cuts
                            break
    return cuts
