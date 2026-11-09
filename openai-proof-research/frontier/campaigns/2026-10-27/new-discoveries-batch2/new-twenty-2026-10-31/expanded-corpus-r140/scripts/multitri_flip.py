"""Flip-graph exploration of k-triangulations on the half-cylinder C_n (MathDB 368931).
Same model as multitri.py.  Starting from a greedy k-triangulation, for each
relevant edge e of T we enumerate ALL maximal crossing-free supersets of T-e
(not just one flip), so the explored set is the connected component of the
'share k(n-1)-1 ... all-but-one-edge' graph; it is exhaustive iff that graph is
connected (unknown for k>=3), hence results are a bounded non-exhaustive search
unless the count matches an independent exhaustive enumeration.
"""
import sys, json, itertools
sys.setrecursionlimit(10000)
import pathlib; sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent)); from multitri import check

def make(n, k):
    C = [(r, l) for l in range(k + 1, k * n + 1) for r in range(n)]
    def lifted(S, lo, hi):
        out = []
        for (r, l) in S:
            a0 = lo + ((r - lo) % n)
            for a in range(a0, hi, n):
                out.append((a, a + l))
        return out
    def crossing_with(S, c):
        """does S u {c} contain a (k+1)-crossing using some translate of c? (S crossing-free)"""
        r, l = c
        a0, b0 = r, r + l
        L = max([l] + [ll for _, ll in S])
        E = lifted(set(S) | {c}, a0 - L - 1, b0 + 1)
        X = [(a, b) for (a, b) in E if (a < a0 < b < b0) or (a0 < a < b0 < b)]
        X.sort()
        # need k edges from X, pairwise crossing (they all cross e0)
        def dfs(start, chosen, depth):
            if depth == k:
                return True
            for i in range(start, len(X)):
                a, b = X[i]
                ok = True
                for (a2, b2) in chosen:
                    if not (a2 < a < b2 < b):
                        ok = False; break
                if ok:
                    chosen.append((a, b))
                    if dfs(i + 1, chosen, depth + 1):
                        return True
                    chosen.pop()
            return False
        return dfs(0, [], 0)
    def maximal_supersets(S):
        """all maximal crossing-free supersets of crossing-free S"""
        S = frozenset(S)
        cand = [c for c in C if c not in S and not crossing_with(S, c)]
        res = set()
        def rec(i, cur, cands):
            # cands: classes compatible with cur, index >= i
            if not cands:
                # maximal? every class not in cur must be blocked
                for c in C:
                    if c not in cur and not crossing_with(cur, c):
                        return
                res.add(frozenset(cur))
                return
            c = cands[0]
            cur2 = cur | {c}
            rest = [d for d in cands[1:] if not crossing_with(cur2, d)]
            rec(i + 1, cur2, rest)
            # exclude c: only if c ends blocked; continue
            rec(i + 1, cur, cands[1:])
        rec(0, S, cand)
        return res
    def greedy():
        S = frozenset()
        for c in C:
            if not crossing_with(S, c):
                S = S | {c}
        return S
    return C, crossing_with, maximal_supersets, greedy

if __name__ == '__main__':
    k = int(sys.argv[1]); n = int(sys.argv[2]); limit = int(sys.argv[3]) if len(sys.argv) > 3 else 10 ** 9
    C, cw, ms, greedy = make(n, k)
    T0 = greedy()
    seen = {T0}; queue = [T0]; qi = 0
    while qi < len(queue) and len(seen) < limit:
        T = queue[qi]; qi += 1
        for e in T:
            for T2 in ms(T - {e}):
                if T2 not in seen:
                    seen.add(T2); queue.append(T2)
    nbad = 0; ex = None; sizes = {}
    tot = {'angles': 0, 'relevant': 0}
    for T in seen:
        sizes[len(T)] = sizes.get(len(T), 0) + 1
        bad, st = check(T, n, k)
        for x in tot: tot[x] += st[x]
        if bad:
            nbad += 1
            if ex is None: ex = {'T': sorted(T), 'bad': bad[:4]}
    from math import comb
    print(json.dumps({'k': k, 'n': n, 'explored': len(seen), 'complete_bfs': qi >= len(queue),
                      'conj67_prediction': comb(2 * (n - 1), n - 1) ** k,
                      'relevant_edge_count_hist': sizes, 'num_failing': nbad, 'angle_stats': tot, 'example': ex}), flush=True)
