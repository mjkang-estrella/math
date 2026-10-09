"""Independent exact checks; finite algebra tests, not a substitute for PDE proofs."""
from fractions import Fraction as F
from collections import defaultdict
from pathlib import Path
import json
import random
import runpy
import shutil

HERE = Path(__file__).resolve().parent
old = HERE.parent / 'hotspots_multiplicity_r2/check_corner_parity.py'
# Rerun the original unchanged script in OUR directory: its output is relative
# to __file__, so executing the original in place would violate write scope.
copy = HERE / 'hotspots_polygon_proof_r3_original_corner_check.py'
shutil.copyfile(old, copy)
runpy.run_path(str(copy), run_name='__main__')
(HERE / 'results.json').rename(HERE / 'original_corner_results.json')

angles = [F(3, 5), F(2, 3), F(3, 4), F(9, 10), F(501, 1000), F(500001, 1000000)]
checks = 0
for nu in angles:
    for n in range(13):
        for m in range(13):
            for j in range(4):
                for k in range(4):
                    # Bessel powers r^(n*nu+2*j); constants differentiate to zero.
                    p, q = n * nu + 2*j, m * nu + 2*k
                    if not p or not q:
                        continue
                    if (n + m) % 2:
                        continue  # Exact cancellation on the two rays.
                    exponent = p + q - 2
                    if (n, m, j, k) != (1, 1, 0, 0):
                        assert exponent > 0, (nu, n, m, j, k, exponent)
                    checks += 1
assert 3 * F(2, 3) - 2 == 0
assert 4 * F(1, 2) - 2 == 0  # Endpoint exclusion is substantive.

# Exact cosine-series arithmetic on a rectangle (0,pi*A)x(0,pi*B).
# Frequencies are integers in x/A or y/B; derivatives use physical length.
def trace(modes, coeffs, axis, end):
    out = defaultdict(F)
    for (m, n), c in zip(modes, coeffs):
        varying, fixed = (m, n) if axis == 0 else (n, m)
        out[varying] += c * (-1)**(fixed*end)
    return out

def stress(a, b, lam, scale):
    out = defaultdict(F)
    for n, an in a.items():
        for m, bm in b.items():
            out[abs(n-m)] += an*bm*(F(n*m)/scale**2-lam)/2
            out[n+m] += an*bm*(-F(n*m)/scale**2-lam)/2
    return {str(n): str(c) for n, c in out.items() if c}

def stresses(modes, a, b, lam, A, B):
    return [stress(trace(modes,a,axis,end),trace(modes,b,axis,end),lam,scale)
            for axis,scale in enumerate([A,B]) for end in [0,1]]

rng = random.Random(369)
rect_tests = 0
max_dimension = 0
for A, B in [(F(1),F(1)), (F(2),F(1)), (F(3,2),F(1))]:
    levels = defaultdict(list)
    for m in range(11):
        for n in range(11):
            lam = F(m*m)/A**2 + F(n*n)/B**2
            if 0 < lam <= 100:
                levels[lam].append((m,n))
    for lam, modes in levels.items():
        d = len(modes)
        if d < 2:
            continue
        max_dimension = max(max_dimension,d)
        for i in range(d):
            for j in range(i+1,d):
                a,b=[0]*d,[0]*d
                a[i]=a[j]=b[i]=1
                b[j]=-1
                assert any(stresses(modes,a,b,lam,A,B))
                rect_tests += 1
        for _ in range(40):
            a=[rng.randint(-3,3) for _ in modes]
            b=[rng.randint(-3,3) for _ in modes]
            if not any(a) or not any(b):
                continue
            assert any(stresses(modes,a,b,lam,A,B))
            rect_tests += 1

square_examples = {}
for lam,modes in [(F(1),[(1,0),(0,1)]),(F(5),[(1,2),(2,1)])]:
    square_examples[str(lam)]=stresses(modes,[1,1],[1,-1],lam,F(1),F(1))

# Explicit slit-endpoint local solution h=k=exp(sqrt(lambda)*x)
# *cos(sqrt(2*lambda)*y): on both rays y=0, h'=sqrt(lambda)h,
# and Delta h=(lambda-2lambda)h=-lambda h. Record algebra exactly.
assert F(1)-F(2)==-1
out = {
    'status':'passed',
    'kind':'exact rational finite checks; no finite-element eigenvalue approximation',
    'corner_even_parity_bessel_products':checks,
    'tested_nu':[str(nu) for nu in angles],
    'near_slit_decay_exponents':[str(4*nu-2) for nu in angles[-2:]],
    'rectangle_cross_stress_tests':rect_tests,
    'largest_tested_eigenspace_dimension':max_dimension,
    'square_h_f_plus_g_k_f_minus_g_stresses':square_examples,
    'slit_local_solution':'exp(sqrt(lambda)*x)*cos(sqrt(2*lambda)*y)',
    'limitations':'Finite mode/correction enumeration verifies algebra only. Infinite tails, uniqueness, perturbation and topology are proved in the review.'
}
(HERE/'results.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
