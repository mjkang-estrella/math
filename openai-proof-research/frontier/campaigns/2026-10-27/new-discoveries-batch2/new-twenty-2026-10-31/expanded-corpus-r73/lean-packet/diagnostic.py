"""Independent exact corroboration (not a proof) for MathDB 378395.

Parses the integer tables of the facet functional `ellZ` directly from proof/MathDB378395.lean and
checks with exact rational arithmetic (fractions.Fraction):
  * l(col(i,j,k)) = a_ij + b_ik + c_jk >= 0 for all 80 cells of the 4x4x5 table (validity);
  * rank of all 80 columns = 44 = pq+pr+qr-p-q-r+1 (dimension of the marginal cone);
  * rank of the tight columns = 43 (facet);
  * the five slices k have pairwise distinct zero patterns {(i,j): l(col(i,j,k)) = 0};
  * a deliberately perturbed table fails validity (negative control).
Usage: python3 -I diagnostic.py OUT.json
"""
import itertools, json, pathlib, re, sys
from fractions import Fraction
ROOT = pathlib.Path(__file__).resolve().parent
src = (ROOT / 'proof/MathDB378395.lean').read_text(encoding='utf-8')
blk = src[src.index('def ellZ : Margin 4 4 5 → ℤ :='):]
blk = blk[:blk.index('theorem ell_nonneg')]
lits = re.findall(r'!\[(!\[.*?\](?:, !\[.*?\])*)\]', blk)
assert len(lits) == 3, lits
tabs = [[[int(x) for x in row.split(',')] for row in re.findall(r'!\[([^\[\]]*)\]', L)] for L in lits]
A, B, C = tabs
assert len(A) == 4 and all(len(r) == 4 for r in A) and len(B) == 4 and all(len(r) == 5 for r in B)
p, q, r = 4, 4, 5

def rank(rows):
    M = [list(map(Fraction, x)) for x in rows]; rk = 0
    for c in range(len(M[0]) if M else 0):
        piv = next((i for i in range(rk, len(M)) if M[i][c] != 0), None)
        if piv is None: continue
        M[rk], M[piv] = M[piv], M[rk]
        for i in range(len(M)):
            if i != rk and M[i][c] != 0:
                f = M[i][c] / M[rk][c]; M[i] = [x - f * y for x, y in zip(M[i], M[rk])]
        rk += 1
    return rk

def check(A, B, C):
    coords = [('12', i, j) for i in range(p) for j in range(q)] + [('13', i, k) for i in range(p) for k in range(r)] + [('23', j, k) for j in range(q) for k in range(r)]
    ix = {c: n for n, c in enumerate(coords)}
    cells = list(itertools.product(range(p), range(q), range(r)))
    def col(c):
        i, j, k = c; v = [0] * len(coords); v[ix[('12', i, j)]] = 1; v[ix[('13', i, k)]] = 1; v[ix[('23', j, k)]] = 1; return v
    w = {c: A[c[0]][c[1]] + B[c[0]][c[2]] + C[c[1]][c[2]] for c in cells}
    tight = [c for c in cells if w[c] == 0]
    pats = [frozenset((i, j) for i in range(p) for j in range(q) if w[(i, j, k)] == 0) for k in range(r)]
    return dict(valid=min(w.values()) >= 0, min_value=min(w.values()), tight=len(tight), rank_all=rank([col(c) for c in cells]),
                rank_tight=rank([col(c) for c in tight]), distinct_patterns=len(set(pats)) == r)

res = check(A, B, C)
bad = [row[:] for row in A]; bad[1][3] = -bad[1][3] - 1
neg = check(bad, B, C)
ok = res['valid'] and res['rank_all'] == 44 and res['rank_tight'] == 43 and res['distinct_patterns'] and not neg['valid']
out = dict(status='PASS' if ok else 'FAIL', tables=dict(a=A, b=B, c=C), result=res, perturbed=neg)
pathlib.Path(sys.argv[1]).write_text(json.dumps(out, indent=2))
print(out['status'], res, 'perturbed valid:', neg['valid'])
sys.exit(0 if ok else 1)
