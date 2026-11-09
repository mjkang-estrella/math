"""Exact maximum number of nonzeros in a minimally AP-irreducible zero-diagonal n x n
sign pattern (Das, arXiv:2112.00442v3, Conjecture 5.1 asserts <= 2n-2), via MILP.

Variables p[i,j], m[i,j] in {0,1} (a_ij = '+' / '-'), p+m <= 1, zero diagonal.
AP-irreducible:
  rows/cols:  sum_j p[i,j] >= 1, sum_i p[i,j] >= 1
  D(A) strong: for all proper nonempty U: sum_{i in U, j notin U} (p+m)[i,j] >= 1
  D(B) strong: for all proper nonempty U: sum_{i in U, j notin U} (p[i,j] + m[j,i]) >= 1
Minimality (each nonzero entry has a witness that its deletion breaks AP-irreducibility):
  p[i,j] <= r[i,j] + c[i,j] + sum_U wA[(i,j),U] + sum_U wB[(i,j),U]
     r[i,j]=1 forces p[i,j'] = 0 for j' != j (unique '+' in row) ; c similarly for column
     wA[(i,j),U] (i in U, j notin U) forces every other A-arc leaving U to be absent
     wB[(i,j),U]  forces every other B-arc leaving U to be absent (B-arc of p[i,j] is i->j)
  m[i,j] <= sum_U wA[(i,j),U] + sum_V wB'[(i,j),V]
     A-arc of m[i,j] is i->j; B-arc is j->i, so V contains j, not i.
Each solution is re-verified independently by apirr.ap_irr / apirr.minimal.
Usage: apmilp.py N [time_limit_seconds]
"""
import sys, itertools, json, pathlib
import numpy as np
from scipy.optimize import milp, LinearConstraint, Bounds
from scipy.sparse import lil_matrix
sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
from apirr import ap_irr, minimal, show

n = int(sys.argv[1]); tl = float(sys.argv[2]) if len(sys.argv) > 2 else 150
V = range(n)
cells = [(i, j) for i in V for j in V if i != j]
idx = {}
def var(key):
    if key not in idx:
        idx[key] = len(idx)
    return idx[key]
for e in cells:
    var(('p', e)); var(('m', e))
subsets = [frozenset(U) for k in range(1, n) for U in itertools.combinations(V, k)]
# arcs leaving U in A and in B, as lists of variable keys
def A_out(U):
    return [(t, (i, j)) for i in U for j in V if j not in U for t in ('p', 'm')]
def B_out(U):
    return [('p', (i, j)) for i in U for j in V if j not in U] + [('m', (j, i)) for i in U for j in V if j not in U]
rows = []  # (dict coeffs, lo, hi)
for i in V:
    rows.append(({('p', (i, j)): 1 for j in V if j != i}, 1, np.inf))
    rows.append(({('p', (j, i)): 1 for j in V if j != i}, 1, np.inf))
for e in cells:
    rows.append(({('p', e): 1, ('m', e): 1}, -np.inf, 1))
for U in subsets:
    rows.append(({k: 1 for k in A_out(U)}, 1, np.inf))
    rows.append(({k: 1 for k in B_out(U)}, 1, np.inf))
BIG = 2 * n * n
for (i, j) in cells:
    wit_p = {}
    r = ('r', (i, j)); c = ('c', (i, j))
    rows.append(({r: BIG, **{('p', (i, jj)): 1 for jj in V if jj not in (i, j)}}, -np.inf, BIG))
    rows.append(({c: BIG, **{('p', (ii, j)): 1 for ii in V if ii not in (i, j)}}, -np.inf, BIG))
    wit_p[r] = -1; wit_p[c] = -1
    wit_m = {}
    for U in subsets:
        if i in U and j not in U:
            # A-arc i->j is shared by p[i,j] and m[i,j]; B-arc i->j from p[i,j] (or m[j,i])
            for kind, arcs in (('wA', A_out(U)), ('wB', B_out(U))):
                for t in ('p', 'm'):
                    if kind == 'wB' and t == 'm':
                        continue  # m[i,j] is not a B-arc i->j
                    w = (kind + t, (i, j), U)
                    others = [k for k in arcs if k != (t, (i, j))]
                    rows.append(({w: BIG, **{k: 1 for k in others}}, -np.inf, BIG))
                    (wit_p if t == 'p' else wit_m)[w] = -1
        if j in U and i not in U:
            # B-arc of m[i,j] is j->i, leaving U
            w = ('wBm_rev', (i, j), U)
            others = [k for k in B_out(U) if k != ('m', (i, j))]
            rows.append(({w: BIG, **{k: 1 for k in others}}, -np.inf, BIG))
            wit_m[w] = -1
    rows.append(({('p', (i, j)): 1, **wit_p}, -np.inf, 0))
    rows.append(({('m', (i, j)): 1, **wit_m}, -np.inf, 0))
for coeffs, lo, hi in rows:
    for k in coeffs:
        var(k)
N = len(idx)
A = lil_matrix((len(rows), N)); lo = np.empty(len(rows)); hi = np.empty(len(rows))
for r_, (coeffs, l, h) in enumerate(rows):
    for k, v in coeffs.items():
        A[r_, idx[k]] = v
    lo[r_] = l; hi[r_] = h
cvec = np.zeros(N)
for e in cells:
    cvec[idx[('p', e)]] = -1; cvec[idx[('m', e)]] = -1
# Direct HiGHS call so that threads=1 can be set (multi-threaded HiGHS exceeds the
# fixed 512 MiB address-space cap); same model as scipy.optimize.milp.
from scipy.optimize._milp import _milp_iv
from scipy.optimize._highspy._highs_wrapper import _highs_wrapper
c_, integ_, lb_, ub_, indptr_, indices_, data_, bl_, bu_, opts_ = _milp_iv(
    cvec, np.ones(N), Bounds(0, 1), LinearConstraint(A.tocsr(), lo, hi), {'time_limit': tl, 'disp': False})
res = _highs_wrapper(c_, indptr_, indices_, data_, bl_, bu_, lb_, ub_, integ_, dict(opts_, threads=1))
out = {'n': n, 'vars': N, 'rows': len(rows), 'status': str(res.get('status')), 'message': str(res.get('message')),
       'mip_dual_bound': res.get('mip_dual_bound'), 'mip_gap': res.get('mip_gap')}
if res.get('x') is not None:
    x = np.round(np.asarray(res['x'])).astype(int)
    pat = {e: 1 for e in cells if x[idx[('p', e)]]}
    pat.update({e: -1 for e in cells if x[idx[('m', e)]]})
    out.update(nonzeros=len(pat), pattern=show(n, pat), verified_ap_irr=ap_irr(n, pat),
               verified_minimal=minimal(n, pat),
               bound_2n_minus_2=2 * n - 2)
print(json.dumps(out))
