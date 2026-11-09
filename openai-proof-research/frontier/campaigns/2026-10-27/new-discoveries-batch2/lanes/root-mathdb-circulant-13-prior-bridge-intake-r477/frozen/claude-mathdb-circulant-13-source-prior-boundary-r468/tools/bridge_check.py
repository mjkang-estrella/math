"""Corroboration (NOT a certificate, NOT a proof) of the KHS-2017 bridge to C_n(1,3).

(a) Pull-back lemma: phi(x,y) = x+3y mod n maps P_m x C_n (cycle along x) to C_n(1,3).
    Check by BFS, for m=5 and n in [19,200]: phi is a graph homomorphism, phi(u)!=phi(v)
    whenever d_cyl(u,v)<=3, and d_C(phi u, phi v) <= d_cyl(u,v) whenever d_cyl<=3.
(b) KHS Lemma 5 Table 6 patterns as extracted from the KJM PDF (cases (3),(6)):
    case3 rows: f(i,j) = 8-3i+7j (mod 12), case6 rows: f(i,j) = 8-5i-3j (mod 12).
    Confirm the extracted printed rows equal these forms, they are valid L(3,2,1)
    labelings of P_3 x C_N for N = 12 (case3) / 4,8,12 (case6), and their minimal
    row periods are 12 and 4.
(c) Modular facts used: in C_n(1,3) (n>=19) offsets 1,2,3,4,6 have distance <=2;
    so f(x+d)=f(x) for d in {1,2,3,4,6} is impossible.
(d) Every symmetry image (inversion, j->-j, i->2-i, translations) of case6 has row
    period 4 and of case3 row period 12 (period preserved).
Writes JSON to argv[1]; exit 1 if any check fails.
"""
import json, sys
from collections import deque


def bfs(adj, s):
    d = {s: 0}; q = deque([s])
    while q:
        u = q.popleft()
        if d[u] >= 3:
            continue
        for v in adj(u):
            if v not in d:
                d[v] = d[u] + 1; q.append(v)
    return d


fail = []
res = {}

# (a)
def cyl_adj(n, m):
    def a(u):
        x, y = u
        out = [((x + 1) % n, y), ((x - 1) % n, y)]
        if y > 0: out.append((x, y - 1))
        if y < m - 1: out.append((x, y + 1))
        return out
    return a

def circ_adj(n):
    return lambda u: [(u + s) % n for s in (1, -1, 3, -3)]

checked = 0
for n in range(19, 201):
    m = 5
    ca, cc = cyl_adj(n, m), circ_adj(n)
    dist_c = {}
    for u in [(x, y) for x in range(n) for y in range(m)]:
        pu = (u[0] + 3 * u[1]) % n
        if pu not in dist_c:
            dist_c[pu] = bfs(cc, pu)
        for v, dv in bfs(ca, u).items():
            if v == u:
                continue
            pv = (v[0] + 3 * v[1]) % n
            if pv == pu:
                fail.append(['a-collision', n, u, v]); continue
            dc = dist_c[pu].get(pv, 99)
            if dc > dv:
                fail.append(['a-distance-increase', n, u, v, dv, dc])
            checked += 1
res['a_pairs_checked'] = checked

# (b)
printed = {
    'case3': ['8 3 10 5 0 7 2 9 4 11 6 1 8 3', '5 0 7 2 9 4 11 6 1 8 3 10 5 0 7',
              '2 9 4 11 6 1 8 3 10 5 0 7 2 9'],
    'case6': ['8 5 2 11 8 5', '3 0 9 6 3 0 9', '10 7 4 1 10 7'],
}
forms = {'case3': lambda i, j: (8 - 3 * i + 7 * j) % 12,
         'case6': lambda i, j: (8 - 5 * i - 3 * j) % 12}
for k, rows in printed.items():
    for i, r in enumerate(rows):
        vals = [int(t) for t in r.split()]
        if vals != [forms[k](i, j) for j in range(len(vals))]:
            fail.append(['b-printed-mismatch', k, i])

def valid_strip(f, N, m=3):
    a = cyl_adj(N, m)
    for x in range(N):
        for y in range(m):
            for v, d in bfs(a, (x, y)).items():
                if v != (x, y) and abs(f(y, x) - f(v[1], v[0])) < 4 - d:
                    return False
    return True

def row_period(f):
    for p in range(1, 13):
        if all(f(i, j) == f(i, j + p) for i in range(3) for j in range(24)):
            return p

res['b_case3_valid_N12'] = valid_strip(forms['case3'], 12)
res['b_case6_valid_N'] = {N: valid_strip(forms['case6'], N) for N in (4, 8, 12)}
res['b_case3_row_period'] = row_period(forms['case3'])
res['b_case6_row_period'] = row_period(forms['case6'])
if not res['b_case3_valid_N12'] or not all(res['b_case6_valid_N'].values()):
    fail.append(['b-pattern-invalid'])
if res['b_case3_row_period'] != 12 or res['b_case6_row_period'] != 4:
    fail.append(['b-period'])

# (c)
for n in range(19, 201):
    d = bfs(circ_adj(n), 0)
    for off in (1, 2, 3, 4, 6):
        if d.get(off, 99) > 2:
            fail.append(['c', n, off])
res['c_offsets_distance'] = {off: bfs(circ_adj(50), 0)[off] for off in (1, 2, 3, 4, 6)}

# (d) symmetry images keep row periods
def images(f):
    out = []
    for inv in (0, 1):
        for refl in (0, 1):
            for flip in (0, 1):
                for t in range(12):
                    def g(i, j, inv=inv, refl=refl, flip=flip, t=t):
                        ii = 2 - i if flip else i
                        jj = (-j if refl else j) + t
                        v = f(ii, jj)
                        return 11 - v if inv else v
                    out.append(g)
    return out
res['d_case3_periods'] = sorted({row_period(g) for g in images(forms['case3'])})
res['d_case6_periods'] = sorted({row_period(g) for g in images(forms['case6'])})
if res['d_case3_periods'] != [12] or res['d_case6_periods'] != [4]:
    fail.append(['d'])

# consistency with r376 by-product: pull-back of c+-5x (mod 12) has row form like case3
res['pullback_5x_rowform'] = [[(5 * (j + 3 * i)) % 12 for j in range(12)] for i in range(3)]

res['failures'] = fail
res['status'] = 'PASS' if not fail else 'FAIL'
json.dump(res, open(sys.argv[1], 'w'), indent=1, sort_keys=True, default=str)
print(res['status'], len(fail), res['a_pairs_checked'])
sys.exit(1 if fail else 0)
