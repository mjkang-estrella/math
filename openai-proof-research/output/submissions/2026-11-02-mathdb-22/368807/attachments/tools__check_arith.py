"""Exact stdlib re-check of the numbers quoted in the manuscript (diagnostic; Lean is authoritative).

    python3 -I check_arith.py LEAN_DIR OUT.json

Checks, with Fractions and integers only:
  1. x* = X/4 (read from ASEPData.lean) is in P_ASEP^8; its tight cuts are exactly the 8 listed ones;
     smallest positive entry 1/4, smallest non-tight cut value 5/4; tight-system rank 56 (vertex).
  2. Every one of the 5040 stored certificates, decoded independently of Lean, satisfies the
     mathematical conditions of the non-adjacency argument with the cuts recomputed from scratch
     (not from the stored list): support, zero row/column sums, zero flux on every cut tight at both
     x* and T, sum |v| <= 64, a non-parallelism 2x2 minor, and successor map = cyclic order.
     The cyclic orders are exactly the 5040 orders 0,p1,...,p7.
  3. Source control n = 4 (Example 1): x is a vertex of P_ASEP^4 and is adjacent to exactly 5 of the
     6 tours (adjacency by the rank of the common tight system, r(4) - 1 = 11).
"""
import itertools, json, re, sys
from fractions import Fraction as Fr
from pathlib import Path


def rank(rows):
    m = [list(map(Fr, r)) for r in rows]
    rk, col, ncol = 0, 0, (len(m[0]) if m else 0)
    while rk < len(m) and col < ncol:
        piv = next((i for i in range(rk, len(m)) if m[i][col] != 0), None)
        if piv is None:
            col += 1
            continue
        m[rk], m[piv] = m[piv], m[rk]
        for i in range(len(m)):
            if i != rk and m[i][col] != 0:
                f = m[i][col] / m[rk][col]
                m[i] = [a - f * b for a, b in zip(m[i], m[rk])]
        rk += 1
        col += 1
    return rk


def arcs(n):
    return [(i, j) for i in range(n) for j in range(n) if i != j]


def cuts(n):
    return [frozenset(S) for k in range(2, n - 1) for S in itertools.combinations(range(n), k)]


def flux(x, S, n):
    return sum(x[i][j] for i in S for j in range(n) if j not in S)


def tight_rows(x, n, extra_zero=None):
    """Rows of the degree equations plus every constraint tight at x (zero arcs, tight cuts)."""
    A = arcs(n)
    idx = {a: k for k, a in enumerate(A)}
    rows = []
    for v in range(n):
        rows.append([1 if a[1] == v else 0 for a in A])
        rows.append([1 if a[0] == v else 0 for a in A])
    for a in A:
        if x[a[0]][a[1]] == 0 and (extra_zero is None or extra_zero[a[0]][a[1]] == 0):
            r = [0] * len(A)
            r[idx[a]] = 1
            rows.append(r)
    for S in cuts(n):
        if flux(x, S, n) == 1 and (extra_zero is None or flux(extra_zero, S, n) == 1):
            rows.append([1 if (a[0] in S and a[1] not in S) else 0 for a in A])
    return rows


def parse_data(lean_dir):
    src = (Path(lean_dir) / 'ASEPData.lean').read_text()
    tab = re.search(r'def XNtab : List \(List Nat\) :=\s*(\[\[.*?\]\])', src, re.S).group(1)
    X = json.loads(tab.replace('\n', ''))
    tl = re.search(r'def tightCutList : List \(List \(Fin 8\)\) := (\[.*?\]\])', src).group(1)
    T = [frozenset(s) for s in json.loads(tl)]
    chunks = {}
    for m in re.finditer(r'def certChunk(\d+) : List Nat := \[(.*?)\]', src, re.S):
        chunks[int(m.group(1))] = [int(t) for t in m.group(2).replace('\n', '').split(',') if t.strip()]
    order = re.search(r'def certData : List Nat :=(.*?)(\n\n|\nend)', src, re.S)
    names = re.findall(r'certChunk(\d+)', order.group(1)) if order else []
    data = [N for k in map(int, names) for N in chunks[k]]
    return X, T, chunks, data, names


def decode(N):
    d = []
    for _ in range(90):
        d.append(N % 128)
        N //= 128
    g = lambda k: d[k] if k < len(d) else 0
    tl = [x % 8 for x in d[:7]]
    s = [x % 8 for x in d[7:15]]
    es, rest, cnt = [], d[20:], g(19)
    for k in range(cnt):
        if len(rest) < 3:
            break
        a, b, c, rest = rest[0], rest[1], rest[2], rest[3:]
        es.append((a % 8, b % 8, c - 64))
    return dict(tl=tl, s=s, a1=g(15) % 8, a2=g(16) % 8, b1=g(17) % 8, b2=g(18) % 8, es=es, ncount=cnt)


def main():
    lean_dir, out = sys.argv[1], sys.argv[2]
    n = 8
    X, Tlist, chunks, data, names = parse_data(lean_dir)
    x = [[Fr(v, 4) for v in row] for row in X]
    res = {}
    # 1. vertex facts
    deg_ok = all(sum(x[i]) == 1 for i in range(n)) and all(sum(x[i][j] for i in range(n)) == 1 for j in range(n))
    nonneg = all(v >= 0 for row in x for v in row) and all(x[i][i] == 0 for i in range(n))
    allcuts = cuts(n)
    vals = {S: flux(x, S, n) for S in allcuts}
    tight = sorted((sorted(S) for S, v in vals.items() if v == 1), key=lambda s: (len(s), s))
    res['vertex'] = {
        'support_size': sum(1 for row in x for v in row if v > 0),
        'degree_equations_hold': deg_ok, 'nonnegative_zero_diagonal': nonneg,
        'num_cuts_checked': len(allcuts), 'all_cuts_at_least_1': all(v >= 1 for v in vals.values()),
        'tight_cuts': tight, 'tight_cuts_equal_stored_list': set(map(frozenset, tight)) == set(Tlist),
        'min_positive_entry': str(min(v for row in x for v in row if v > 0)),
        'min_nontight_cut_value': str(min(v for v in vals.values() if v != 1)),
        'num_zero_arcs': sum(1 for (i, j) in arcs(n) if x[i][j] == 0),
        'tight_system_rank': rank(tight_rows(x, n)), 'm': n * (n - 1),
    }
    res['vertex']['is_vertex'] = res['vertex']['tight_system_rank'] == n * (n - 1)
    # 2. certificates
    tight_sets = [S for S, v in vals.items() if v == 1]
    orders, bad, max_l1, max_terms = set(), [], 0, 0
    for k, N in enumerate(data):
        c = decode(N)
        succ = c['s']
        order = [0] + c['tl']
        ok_cycle = all(succ[order[i]] == order[(i + 1) % 8] for i in range(8)) and sorted(order) == list(range(8))
        T = [[1 if succ[i] == j else 0 for j in range(n)] for i in range(n)]
        v = [[0] * n for _ in range(n)]
        for a, b, w in c['es']:
            v[a][b] += w
        ok_supp = all(a != b and (X[a][b] > 0 or succ[a] == b) for a, b, _ in c['es'])
        ok_rows = all(sum(v[i]) == 0 for i in range(n)) and all(sum(v[i][j] for i in range(n)) == 0 for j in range(n))
        ok_cuts = all(flux(v, S, n) == 0 for S in tight_sets if flux(T, S, n) == 1)
        l1 = sum(abs(w) for _, _, w in c['es'])
        d = lambda i, j: Fr(X[i][j], 4) - T[i][j]
        ok_np = d(c['a1'], c['a2']) * v[c['b1']][c['b2']] != d(c['b1'], c['b2']) * v[c['a1']][c['a2']]
        max_l1, max_terms = max(max_l1, l1), max(max_terms, len(c['es']))
        if not (ok_cycle and ok_supp and ok_rows and ok_cuts and l1 <= 64 and ok_np and len(c['es']) == c['ncount']):
            bad.append(k)
        orders.add(tuple(order))
    expected = {tuple([0] + list(p)) for p in itertools.permutations(range(1, 8))}
    res['certificates'] = {
        'chunks': len(chunks), 'chunk_order_in_certData': names[:3] + ['...'] + names[-2:],
        'num_certificates': len(data), 'num_failing': len(bad), 'failing_indices': bad[:20],
        'cyclic_orders_exactly_all_5040': orders == expected and len(data) == 5040,
        'max_l1_norm': max_l1, 'max_nonzero_terms': max_terms,
    }
    # 3. n = 4 control (source Example 1)
    n4 = 4
    x4 = [[Fr(0), Fr(1, 2), Fr(0), Fr(1, 2)], [Fr(1, 2), Fr(0), Fr(1, 2), Fr(0)],
          [Fr(1, 2), Fr(0), Fr(0), Fr(1, 2)], [Fr(0), Fr(1, 2), Fr(1, 2), Fr(0)]]
    m4 = n4 * (n4 - 1)
    feas = (all(sum(r) == 1 for r in x4) and all(sum(x4[i][j] for i in range(n4)) == 1 for j in range(n4))
            and all(flux(x4, S, n4) >= 1 for S in cuts(n4)))
    adj = []
    for p in itertools.permutations(range(1, n4)):
        order = (0,) + p
        T = [[0] * n4 for _ in range(n4)]
        for i in range(n4):
            T[order[i]][order[(i + 1) % n4]] = 1
        r = rank(tight_rows(x4, n4, extra_zero=T))
        adj.append({'tour': list(order), 'common_tight_rank': r, 'adjacent': r == m4 - 1})
    res['n4_control'] = {'feasible': feas, 'vertex_rank': rank(tight_rows(x4, n4)), 'm': m4,
                         'tours': adj, 'num_adjacent_tours': sum(a['adjacent'] for a in adj)}
    res['all_ok'] = (res['vertex']['is_vertex'] and res['vertex']['tight_cuts_equal_stored_list'] and
                     deg_ok and nonneg and res['vertex']['all_cuts_at_least_1'] and len(tight) == 8 and
                     res['vertex']['support_size'] == 19 and res['vertex']['min_positive_entry'] == '1/4' and
                     res['vertex']['min_nontight_cut_value'] == '5/4' and
                     not bad and res['certificates']['cyclic_orders_exactly_all_5040'] and
                     feas and res['n4_control']['vertex_rank'] == m4 and res['n4_control']['num_adjacent_tours'] == 5)
    Path(out).write_text(json.dumps(res, indent=1))
    print(json.dumps({'all_ok': res['all_ok'], 'rank': res['vertex']['tight_system_rank'],
                      'failing': len(bad), 'n4_adjacent': res['n4_control']['num_adjacent_tours']}))
    sys.exit(0 if res['all_ok'] else 1)


if __name__ == '__main__':
    main()
