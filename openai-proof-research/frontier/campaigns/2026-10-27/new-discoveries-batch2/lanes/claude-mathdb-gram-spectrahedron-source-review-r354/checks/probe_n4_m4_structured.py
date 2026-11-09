"""EXPLORATORY bounded probe (instance-level, no credit), n = m = 4: inertia of the socle moment
matrix for structured seeds and their integer perturbations. Variables (a,b,c,d) with z1=a+ib, z2=c+id.
Seeds: (Re z1^2, Im z1^2, Re z2^2, Im z2^2) and the quaternion square map. Asserts nothing about outcome."""
import json, random, sys
from collections import Counter
sys.path.insert(0, __file__.rsplit('/', 1)[0])
from gramlib import quad_monomials, quartic_monomials, add, nullspace_Q, inertia_symmetric
n = 4
v = quad_monomials(n); quart = quartic_monomials(n); qi = {e: i for i, e in enumerate(quart)}
vi = {e: i for i, e in enumerate(v)}
def Q(terms):
    q = [0] * len(v)
    for c, (i, j) in terms:
        e = [0] * 4; e[i] += 1; e[j] += 1; q[vi[tuple(e)]] += c
    return q
seeds = {
 'z1^2,z2^2': [Q([(1, (0, 0)), (-1, (1, 1))]), Q([(2, (0, 1))]), Q([(1, (2, 2)), (-1, (3, 3))]), Q([(2, (2, 3))])],
 # quaternion x^2 for x = a + b i + c j + d k: (a^2-b^2-c^2-d^2, 2ab, 2ac, 2ad)
 'quaternion_square': [Q([(1, (0, 0)), (-1, (1, 1)), (-1, (2, 2)), (-1, (3, 3))]), Q([(2, (0, 1))]), Q([(2, (0, 2))]), Q([(2, (0, 3))])],
 # z1*z2 and z1^2 - z2^2 style: (Re z1z2, Im z1z2, Re(z1^2-z2^2), Im(z1^2-z2^2))
 'z1z2,z1^2-z2^2': [Q([(1, (0, 2)), (-1, (1, 3))]), Q([(1, (0, 3)), (1, (1, 2))]), Q([(1, (0, 0)), (-1, (1, 1)), (-1, (2, 2)), (1, (3, 3))]), Q([(2, (0, 1)), (-2, (2, 3))])],
}
def inertia(qs):
    rows = []
    for q in qs:
        for g in v:
            row = [0] * len(quart)
            for c, e in zip(q, v):
                row[qi[add(e, g)]] += c
            rows.append(row)
    ker = nullspace_Q(rows, len(quart))
    if len(ker) != 1:
        return 'dim_I4_perp=%d' % len(ker)
    E = ker[0]
    return str(inertia_symmetric([[E[qi[add(a, b)]] for b in v] for a in v]))
rng = random.Random(4067)
out = {}
for name, qs in seeds.items():
    h = Counter(); h['seed:' + inertia(qs)] += 1
    for scale in (20, 6):
        for _ in range(40):
            pert = [[scale * c + rng.randint(-1, 1) for c in q] for q in qs]
            h['pert%d:' % scale + inertia(pert)] += 1
    out[name] = dict(h)
print(json.dumps(out, indent=1))
