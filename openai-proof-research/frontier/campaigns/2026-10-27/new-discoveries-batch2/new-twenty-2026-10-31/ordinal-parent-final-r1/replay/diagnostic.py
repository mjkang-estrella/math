"""Exact diagnostic for the MathDB 366371 dossier (corroboration only; not a premise of the Lean theorem).

Usage: python3 -I diagnostic.py OUT.json      (standard library only)

1. Parses the value table D from proof/OrdinalLine.lean and checks it is symmetric, zero exactly
   on the diagonal, and a bijection from the 15 pairs onto 1..15.
2. Checks Definition 1.1 (i)-(vii) for delta = compare(D(x,y), D(z,w)) by brute force.
3. Checks Definition 7.1 LITERALLY for k = 1..4: all pairs of nondecreasing tuples (repeats
   allowed), all permutations of {1..k}, both readings of "but not (7.4)".
4. Checks the threshold-count reduction used in the Lean finite check: for all 64 x 64 pairs of
   strictly increasing lists and thresholds t = 1..15 (the content of `okB`), and independently
   that threshold-count dominance equals sorted-value dominance on every pair.
5. Re-checks the non-embeddability certificate: the forced order and the five comparisons, whose
   gap-coefficient vectors sum to the same vector [1, 2, 2, 2, 1] on both sides.
6. Confirms that the perturbed table used by the negative control `negative-perturbed-table`
   (values of the pairs {0,3} and {0,4} exchanged) FAILS the finite check, so that control
   rejects for a real reason.
"""
import itertools, json, pathlib, re, sys

ROOT = pathlib.Path(__file__).resolve().parent
SRC = (ROOT / 'proof' / 'OrdinalLine.lean').read_text(encoding='utf-8')
N = 6


def parse_table(src):
    block = re.search(r'def D \(a b : Fin 6\) : ℕ :=\n\s*\[(.*?)\]\.getD', src, re.S).group(1)
    rows = re.findall(r'\[([0-9, ]+)\]', block)
    return [[int(v) for v in r.split(',')] for r in rows]


def check_table(D):
    assert len(D) == N and all(len(r) == N for r in D)
    for a in range(N):
        for b in range(N):
            assert D[a][b] == D[b][a]
            assert (D[a][b] == 0) == (a == b)
    vals = sorted(D[a][b] for a in range(N) for b in range(a + 1, N))
    assert vals == list(range(1, 16)), vals


def cmp(a, b):
    return (a > b) - (a < b)          # -1 '<', 0 '=', 1 '>'


def check_axioms(D):
    d = lambda x, y, z, w: cmp(D[x][y], D[z][w])
    P = range(N)
    for x, y, z, w in itertools.product(P, repeat=4):
        assert d(x, y, x, y) == 0                                        # (i)
        assert d(x, y, z, w) == d(y, x, z, w) == d(x, y, w, z)           # (ii)
        assert d(x, y, z, w) == -d(z, w, x, y)                           # (iii)
        assert d(x, x, z, w) == (-1 if z != w else 0)                    # (vii)
    for x, y, u, v, z, w in itertools.product(P, repeat=6):
        a, b, c = d(x, y, u, v), d(u, v, z, w), d(x, y, z, w)
        if a == 0 and b == 0: assert c == 0                              # (iv)
        if a == -1 and b <= 0: assert c == -1                            # (v)
        if a <= 0 and b == -1: assert c == -1                            # (vi)
    return N ** 6


def literal_majorization(D, kmax):
    stats = {}
    for k in range(1, kmax + 1):
        chains = list(itertools.combinations_with_replacement(range(N), k + 1))
        pieces = {c: [D[c[l - 1]][c[l]] for l in range(1, k + 1)] for c in chains}
        perms = list(itertools.permutations(range(k)))
        pairs = prec = sim = viol = 0
        for I in chains:
            f = pieces[I]
            for J in chains:
                g = pieces[J]
                pairs += 1
                is_prec_a = is_sim = dom = False
                for p in perms:
                    le = all(f[l] <= g[p[l]] for l in range(k))
                    eq = all(f[l] == g[p[l]] for l in range(k))
                    dom = dom or le
                    if eq: is_sim = True
                    if le and not eq: is_prec_a = True                  # reading A: not all equal under this pi
                is_prec_b = dom and not is_sim                          # reading B: dominated and not I ~ J
                assert is_prec_a == is_prec_b, (I, J)
                lhs, rhs = D[I[0]][I[-1]], D[J[0]][J[-1]]
                if is_prec_a:
                    prec += 1
                    if not lhs < rhs: viol += 1
                if is_sim:
                    sim += 1
                    if lhs != rhs: viol += 1
        stats[k] = {'chain_pairs': pairs, 'prec_pairs': prec, 'sim_pairs': sim, 'violations': viol}
    return stats


def adj(D, t, A):
    return sum(1 for a, b in zip(A, A[1:]) if t <= D[a][b])


def finite_check(D):
    """Mirror of `okB` over all sublists of [0..5] (64 x 64), thresholds 1..15."""
    lists = [list(c) for r in range(0, N + 1) for c in itertools.combinations(range(N), r)]
    bad, pairs = [], 0
    for A in lists:
        for B in lists:
            if not A or not B:
                continue
            pairs += 1
            ca = [adj(D, t, A) for t in range(1, 16)]
            cb = [adj(D, t, B) for t in range(1, 16)]
            le = all(x <= y for x, y in zip(ca, cb))
            lt = any(x < y for x, y in zip(ca, cb))
            eq = ca == cb
            ea, eb = D[A[0]][A[-1]], D[B[0]][B[-1]]
            if le and lt and not ea < eb: bad.append((A, B, 'prec'))
            if eq and ea != eb: bad.append((A, B, 'sim'))
    return len(lists), pairs, bad


def sorted_dominance_agrees(D):
    """Threshold-count dominance <=> termwise dominance of the zero-padded sorted value lists."""
    lists = [list(c) for r in range(1, N + 1) for c in itertools.combinations(range(N), r)]
    for A in lists:
        for B in lists:
            fa = sorted((D[a][b] for a, b in zip(A, A[1:])), reverse=True)
            fb = sorted((D[a][b] for a, b in zip(B, B[1:])), reverse=True)
            k = max(len(fa), len(fb))
            fa += [0] * (k - len(fa)); fb += [0] * (k - len(fb))
            sd = all(x <= y for x, y in zip(fa, fb))
            td = all(adj(D, t, A) <= adj(D, t, B) for t in range(1, 16))
            if sd != td:
                return False
    return True


def certificate(D):
    # forced order: {0,5} is the unique largest pair; every x in 1..4 is closer to 0 and to 5
    top = max(D[a][b] for a in range(N) for b in range(N))
    assert D[0][5] == top and sum(1 for a in range(N) for b in range(a + 1, N) if D[a][b] == top) == 1
    for x in range(1, 5):
        assert D[0][x] < D[0][5] and D[x][5] < D[0][5]
    assert D[0][1] < D[0][2] < D[0][3] < D[0][4]
    gap = lambda a, b: [1 if min(a, b) < i <= max(a, b) else 0 for i in range(1, N)]   # g_1..g_5
    comps = [((2, 3), (3, 4)), ((1, 2), (2, 4)), ((0, 1), (1, 3)), ((1, 4), (4, 5)), ((3, 5), (0, 2))]
    lhs, rhs = [0] * 5, [0] * 5
    for (a, b), (c, e) in comps:
        assert D[a][b] < D[c][e]
        lhs = [s + v for s, v in zip(lhs, gap(a, b))]
        rhs = [s + v for s, v in zip(rhs, gap(c, e))]
    assert lhs == rhs == [1, 2, 2, 2, 1], (lhs, rhs)
    return {'comparisons': [[list(p), list(q), D[p[0]][p[1]], D[q[0]][q[1]]] for p, q in comps],
            'lhs_gap_coefficients': lhs, 'rhs_gap_coefficients': rhs}


def main():
    D = parse_table(SRC)
    check_table(D)
    out = {'table': D, 'axiom_sextuples_checked': check_axioms(D)}
    out['literal_majorization'] = lit = literal_majorization(D, 4)
    assert all(s['violations'] == 0 for s in lit.values())
    nl, pairs, bad = finite_check(D)
    assert nl == 64 and pairs == 63 * 63 and not bad
    out['finite_check'] = {'sublists': nl, 'nonempty_pairs': pairs, 'thresholds': '1..15', 'violations': 0}
    assert sorted_dominance_agrees(D)
    out['threshold_equals_sorted_dominance'] = True
    out['certificate'] = certificate(D)
    P = [row[:] for row in D]
    P[0][3], P[0][4] = D[0][4], D[0][3]
    P[3][0], P[4][0] = P[0][3], P[0][4]
    check_table(P)
    _, _, pbad = finite_check(P)
    assert pbad, 'perturbed table unexpectedly passes'
    out['perturbed_table'] = {'exchange': 'values of {0,3} and {0,4}', 'finite_check_violations': len(pbad),
                              'first_violation': pbad[0]}
    out['status'] = 'PASS'
    pathlib.Path(sys.argv[1]).write_text(json.dumps(out, indent=1))
    print(json.dumps({k: out[k] for k in ('literal_majorization', 'finite_check', 'perturbed_table', 'status')}))


if __name__ == '__main__':
    main()
