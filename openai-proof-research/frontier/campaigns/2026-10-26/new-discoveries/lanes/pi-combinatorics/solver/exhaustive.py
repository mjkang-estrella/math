#!/usr/bin/env python3
"""EXHAUSTIVE search over all plane Game of Cycles boards with n <= 6 vertices
(and also n=7 for m=7, handled separately: only C7).

Completeness argument:
 - A board with min degree >= 2 and m edges has n <= m vertices (handshake).
 - So all boards with m <= 7 edges have n <= 7. For n <= 6 we enumerate EVERY
   simple graph on n vertices (edge subsets of K_n), keep connected min-deg>=2,
   enumerate EVERY rotation system (all cyclic orders of incident edges at each
   vertex), keep planar ones (face count == m - n + 2), and try EVERY face as
   the outer face. This covers every plane embedding of every candidate graph.
 - n = 7, m = 7 forces 2-regular connected = C_7, whose play is parity-determined
   by AMM Theorem 3. (n=7, m<=6 impossible: min degree 2 => m >= n.)

For each board we solve the game under:
  - face rule (AMM canonical): winning cycles = bounded simple-cycle faces
  - chordless rule (BBFS gloss): winning cycles = all chordless cycles
and report any parity violation (odd edges should be P1, even P2).
"""
import sys, json
from itertools import combinations, permutations
import brute

def rotation_systems(adj):
    """yield dict v -> cyclic tuple of neighbors, all cyclic orders."""
    # for each vertex, cyclic permutations of its neighbor list
    def cyc_perms(lst):
        n = len(lst)
        if n == 0: yield (); return
        for p in permutations(lst):
            # canonical rotation: rotate so min element first
            i = p.index(min(p))
            yield p[i:] + p[:i]
    vs = sorted(adj.keys())
    def rec(i, cur):
        if i == len(vs):
            yield dict(cur)
            return
        v = vs[i]
        for c in cyc_perms(adj[v]):
            cur.append((v, c))
            yield from rec(i + 1, cur)
            cur.pop()
    yield from rec(0, [])

def faces_from_rotation(n, edges, rot):
    """return list of faces, each a list of darts [(v,w),...]"""
    # next dart in face: from (v,w), go to w; take the neighbor of w that comes
    # right BEFORE v in rot[w] (standard face traversal)
    nxt = {}
    for w, cyc in rot.items():
        d = len(cyc)
        for i, v in enumerate(cyc):
            prev = cyc[(i - 1) % d]
            nxt[(v, w)] = (w, prev)
    darts = [(u, v) for (u, v) in edges] + [(v, u) for (u, v) in edges]
    darts = list(dict.fromkeys(darts))
    seen = set()
    faces = []
    for d in darts:
        if d in seen: continue
        cyc = [d]; seen.add(d)
        x = nxt[d]
        while x != d:
            if x in seen: return None  # shouldn't happen for permutation
            cyc.append(x); seen.add(x)
            x = nxt[x]
        faces.append(cyc)
    return faces

def darts_to_verts(cyc):
    return [cyc[0][0]] + [d[1] for d in cyc[:-1]]

def face_cells(n, edges, faces):
    """given face dart-cycles, return (cells, deads, outer_candidates)
    cells: list of (vertexseq); a face is a simple cycle iff len(set(verts))==len."""
    simple = []
    dead = []
    for f in faces:
        vs = darts_to_verts(f)
        if len(set(vs)) == len(vs) and len(vs) >= 3:
            simple.append(vs)
        else:
            dead.append(vs)
    return simple, dead

def board_cells_from_outer(simple_faces, outer):
    """cells = simple faces except outer (as cyclic vertex seqs); dead = simple
    faces that equal outer are dropped; deads unchanged (non-simple faces are
    never cells). We also must include non-simple faces in 'dead' for nothing —
    solver only needs cells."""
    cells = []
    for f in simple_faces:
        if cyclic_eq(f, outer): continue
        cells.append(f)
    return cells

def cyclic_eq(a, b):
    if len(a) != len(b): return False
    if len(set(a)) != len(a): return False
    aa = a.index(min(a)); a = a[aa:] + a[:aa]
    for i in range(len(b)):
        if b[i:] + b[:i] == a: return True
    # reversed
    bb = b[::-1]
    for i in range(len(bb)):
        if bb[i:] + bb[:i] == a: return True
    return False

def edges_as_indexed(n, edge_list):
    return list(edge_list)

def solve_board(n, edges, cells_vseqs, variant):
    """cells_vseqs: list of cyclic vertex sequences (bounded simple faces).
    variant: 'face' or 'chordless'."""
    idx = {}
    for i, e in enumerate(edges):
        idx[e] = i; idx[(e[1], e[0])] = i
    faces = []
    for seq in cells_vseqs:
        k = len(seq)
        ed = []; rq = []
        for p in range(k):
            u, v = seq[p], seq[(p + 1) % k]
            e = idx[(u, v)]
            ed.append(e); rq.append(1 if edges[e][0] == u else 2)
        faces.append((ed, rq))
    if variant == 'chordless':
        # replace cells by all chordless cycles of the graph
        cc = brute.chordless_cycles(n, edges)
        faces = cc
    return brute.solve(n, edges, faces, chordless=False)

def main(maxm=7):
    seen_boards = set()
    results = {}  # m -> list of violation descriptors
    total_boards = 0
    for n in range(3, 7):
        all_pairs = list(combinations(range(n), 2))
        for m in range(n, maxm + 1):
            if m > len(all_pairs): break
            for esub in combinations(all_pairs, m):
                # connected + min degree >= 2
                deg = [0]*n
                for u, v in esub: deg[u] += 1; deg[v] += 1
                if min(deg) < 2: continue
                # connected
                adjsets = {v: set() for v in range(n)}
                for u, v in esub: adjsets[u].add(v); adjsets[v].add(u)
                seen = {0}; st = [0]
                while st:
                    x = st.pop()
                    for y in adjsets[x]:
                        if y not in seen: seen.add(y); st.append(y)
                if len(seen) != n: continue
                adj = {v: sorted(adjsets[v]) for v in range(n)}
                for rot in rotation_systems(adj):
                    faces = faces_from_rotation(n, list(esub), rot)
                    if faces is None: continue
                    if len(faces) != m - n + 2: continue  # not planar
                    simple, dead = face_cells(n, list(esub), faces)
                    outer_candidates = simple + dead  # outer face may be non-simple (cut vertices)
                    for outer in outer_candidates:
                        cells = board_cells_from_outer(simple, outer)
                        if not cells: continue
                        # dedup boards: (graph, multiset of cell cycles, outer)
                        key = (tuple(sorted(esub)),
                               tuple(sorted(tuple(sorted(set(c))) for c in simple)),
                               tuple(sorted(outer)))
                        # note: cells determined by simple+outer; dedup on that
                        bkey = (key, tuple(sorted(tuple(c) for c in dead)))
                        if bkey in seen_boards: continue
                        seen_boards.add(bkey)
                        total_boards += 1
                        for variant in ('face', 'chordless'):
                            w = solve_board(n, list(esub), cells, variant)
                            pred = 1 if m % 2 == 1 else 2
                            if w != pred:
                                results.setdefault(m, []).append({
                                    'n': n, 'edges': sorted(esub), 'variant': variant,
                                    'winner': w, 'cells': cells, 'outer': outer,
                                    'dead': dead})
                                print(f"VIOLATION m={m} n={n} variant={variant} winner=P{w} edges={sorted(esub)}")
                                print(f"  cells={cells} outer={outer} dead={dead}")
    print(f"total boards solved (per variant): {total_boards}")
    for m in sorted(results):
        print(f"m={m}: {len(results[m])} violating boards (with variants)")
    json.dump({str(k): v for k, v in results.items()}, open('exhaustive_results.json', 'w'))

if __name__ == '__main__':
    main(int(sys.argv[1]) if len(sys.argv) > 1 else 7)
