# 346320: exhaustive confluence check of the Kobeaga-Merino-Lozano shrinking strategies
# on all half-integral points of the assignment polytope P_A^G (scaled by 2):
#   Y_v in {1,2} (y_v = Y_v/2 in {1/2,1}; y_v = 0 vertices are isolated and excluded),
#   X_e in {0,1,2} (x_e = X_e/2), sum_{e in delta(v)} X_e = 2 Y_v (degree eq. 7a),
#   X_e <= min(Y_u, Y_v) (logical constraint 7b).  Bounds 7e, 7f hold automatically.
# Rules follow Theorems 3.6, 4.4, 4.5 of arXiv:2004.14574v4 (all rules are homogeneous,
# so the factor-2 scaling is harmless).  For each input and each strategy we compute the
# set of isomorphism classes of terminal weighted support graphs over ALL maximal move
# sequences (memoised DFS on canonical forms).
import itertools, sys, json, time
from functools import lru_cache

STRATS = ['C1', 'C1C2', 'C1C2C3', 'S1', 'S1S2']

def moves(Y, X, strat):
    n = len(Y); out = []
    for u, v in itertools.combinations(range(n), 2):
        c = Y[u]
        if c > 0 and Y[v] == c and X[u][v] == c:
            others = [t for t in range(n) if t != u and t != v]
            if strat in ('S1', 'S1S2'):
                if any(Y[t] >= c for t in others): out.append((u, v))
            elif strat == 'C1':
                if any(Y[t] == c and (X[t][u] == c or X[t][v] == c) for t in others): out.append((u, v))
            else:  # C1C2, C1C2C3 (C2 contains C1)
                if any(Y[t] == c and X[t][u] + X[t][v] == c for t in others): out.append((u, v))
        elif strat == 'S1S2' and X[u][v] > max(Y[u], Y[v]):
            out.append((u, v))
    if strat == 'C1C2C3':
        for s in itertools.combinations(range(n), 3):
            c = Y[s[0]]
            if c > 0 and all(Y[v] == c for v in s) and \
               X[s[0]][s[1]] + X[s[0]][s[2]] + X[s[1]][s[2]] == 2 * c and \
               any(Y[t] == c and sum(X[t][v] for v in s) == c for t in range(n) if t not in s):
                out.append(s)
    return out

def shrink(Y, X, S):
    groups = [(i,) for i in range(len(Y)) if i not in S] + [tuple(S)]
    XX = tuple(tuple(sum(X[a][b] for a in A for b in B) if i != j else 0
                     for j, B in enumerate(groups)) for i, A in enumerate(groups))
    for row in XX: assert sum(row) % 2 == 0
    YY = tuple(sum(row) // 2 for row in XX)   # y[S](s) = x(delta(S))/2 ; others unchanged
    for i in range(len(groups) - 1): assert YY[i] == Y[groups[i][0]]
    return YY, XX

def canon(Y, X):
    n = len(Y)
    col = [(Y[u], tuple(sorted(X[u]))) for u in range(n)]
    for _ in range(n):  # colour refinement (isomorphism-invariant)
        new = [(col[u], tuple(sorted((X[u][v], col[v]) for v in range(n) if X[u][v]))) for u in range(n)]
        keys = sorted(set(new)); new = [keys.index(c) for c in new]
        if len(set(new)) == len(set(col)) and _ > 0: col = new; break
        col = new
    order = sorted(range(n), key=lambda u: col[u])
    classes = [list(g) for k, g in itertools.groupby(order, key=lambda u: col[u])]
    best = None
    for perms in itertools.product(*[itertools.permutations(c) for c in classes]):
        p = [u for c in perms for u in c]
        key = (tuple(Y[u] for u in p), tuple(tuple(X[a][b] for b in p) for a in p))
        if best is None or key < best: best = key
    return best

@lru_cache(maxsize=None)
def terminals(state, strat):
    Y, X = state
    ms = moves(Y, X, strat)
    if not ms: return frozenset([state])
    res = set()
    for m in ms:
        res |= terminals(canon(*shrink(Y, X, m)), strat)
    return frozenset(res)

KONLY = None
CHUNK = None  # (a, b): keep inputs whose row-0 tuple index mod b == a (deterministic)
STRATS_RUN = None
def inputs(n):
    edges = list(itertools.combinations(range(n), 2))
    for Yt in itertools.product((1, 2), repeat=n):
        if list(Yt) != sorted(Yt): continue
        if KONLY is not None and Yt.count(1) != KONLY: continue  # vertices sorted by Y (WLOG, isomorphism)
        X = [[0] * n for _ in range(n)]; deg = [0] * n
        def rec(k):
            if k == len(edges):
                if all(deg[v] == 2 * Yt[v] for v in range(n)):
                    if CHUNK is None or (sum(X[0][j] * 3 ** j for j in range(n)) % CHUNK[1]) == CHUNK[0]:
                        yield tuple(Yt), tuple(map(tuple, X))
                return
            u, v = edges[k]
            # prune: remaining capacity
            for val in range(0, min(Yt[u], Yt[v]) + 1):
                if deg[u] + val > 2 * Yt[u] or deg[v] + val > 2 * Yt[v]: break
                X[u][v] = X[v][u] = val; deg[u] += val; deg[v] += val
                # vertex u finished when all its edges processed: check at last edge of u
                ok = True
                if v == n - 1 and deg[u] != 2 * Yt[u]: ok = False
                if ok: yield from rec(k + 1)
                X[u][v] = X[v][u] = 0; deg[u] -= val; deg[v] -= val
        yield from rec(0)

if __name__ == '__main__':
    nmax = int(sys.argv[1]); out = sys.argv[2]; nmin = int(sys.argv[3]) if len(sys.argv) > 3 else 3
    if len(sys.argv) > 4: KONLY = int(sys.argv[4])
    if len(sys.argv) > 6: CHUNK = (int(sys.argv[5]), int(sys.argv[6]))
    if len(sys.argv) > 7: STRATS_RUN = sys.argv[7].split(',')
    found = {s: None for s in STRATS}; stats = {}
    seen = set()
    t0 = time.time()
    for n in range(nmin, nmax + 1):
        cnt = 0
        for Y, X in inputs(n):
            c = (Y, X); cnt += 1
            for s in (STRATS_RUN or STRATS):
                T = terminals(c, s)
                if len(T) > 1:
                    sizes = sorted({len(t[0]) for t in T})
                    rec_ = {'n': n, 'Y': c[0], 'X': c[1], 'num_terminal_classes': len(T),
                            'terminal_vertex_counts': sizes,
                            'terminals': [{'Y': t[0], 'X': t[1]} for t in sorted(T)]}
                    if found[s] is None or (len(sizes) > 1 and len(found[s]['terminal_vertex_counts']) == 1):
                        found[s] = rec_
                        print('FOUND', s, n, 'classes', len(T), 'vertex counts', sizes, flush=True)
        stats[n] = cnt
        print('n', n, 'labelled inputs (Y sorted)', cnt, 'time', round(time.time() - t0, 1), flush=True)
    json.dump({'stats': stats, 'first_found': found}, open(out, 'w'), indent=1)
