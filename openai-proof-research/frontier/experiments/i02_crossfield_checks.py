"""Exact, finite checks for i02-crossfield; not evidence of universal truth."""
from fractions import Fraction as Q
from itertools import product, combinations
import json
from pathlib import Path


def mul(a, b):
    return [[sum(a[i][k] * b[k][j] for k in range(2)) for j in range(2)] for i in range(2)]


def sub(a, b):
    return [[a[i][j] - b[i][j] for j in range(2)] for i in range(2)]


def scale(a, q):
    return [[q * a[i][j] for j in range(2)] for i in range(2)]


def det(a):
    return a[0][0] * a[1][1] - a[0][1] * a[1][0]


I = [[Q(1), Q(0)], [Q(0), Q(1)]]
S = [[Q(0), Q(1)], [Q(0), Q(0)]]
F = [[Q(0), Q(-1)], [Q(1), Q(0)]]
transfer = []
for z in [Q(i, 7) for i in range(-14, 15)]:
    # S^2=0, hence (I-zS)^-1=I+zS.
    resolvent = sub(I, scale(S, -z))
    value = det(sub(I, scale(mul(resolvent, F), z)))
    assert value == 1
    transfer.append([str(z), str(value)])

transversals = []
for k, m in [(1, 3), (2, 2), (3, 2), (2, 3)]:
    n = k * m
    family = [sum(1 << (i * m + w[i]) for i in range(k)) for w in product(range(m), repeat=k)]
    for p in [Q(1, 2*m), Q(1, m), Q(1, 2)]:
        hit = Q(0)
        for mask in range(1 << n):
            if any(mask & a == a for a in family):
                hit += p**mask.bit_count() * (1-p)**(n-mask.bit_count())
        formula = (1-(1-p)**m)**k
        assert hit == formula
        transversals.append({'rank': k, 'block_size': m, 'p': str(p), 'hit': str(hit)})
    for mask in range(1 << n):
        count = sum(mask & a == mask for a in family)
        assert Q(count, len(family)) <= Q(1,m)**mask.bit_count()
    if k >= 2:
        # Every edge splits into two independent proper subsets.
        for a in family:
            b = a & -a
            c = a ^ b
            assert b | c == a
            assert not any(b & e == e for e in family)
            assert not any(c & e == e for e in family)

sunflower_free = []
for k in range(1, 5):
    fam = [frozenset((i,w[i]) for i in range(k)) for w in product(range(2), repeat=k)]
    count = sum(a & b == a & c == b & c for a,b,c in combinations(fam,3))
    assert count == 0
    sunflower_free.append({'rank':k, 'alphabet':2, 'members':len(fam), 'three_sunflowers':count})

out = {'status':'passed', 'limitations':'Finite rational identities and small families only; universal proofs are in the report.', 'transversal_probabilities':transversals, 'binary_product_checks':sunflower_free, 'rank_two_transfer_determinants':transfer}
destination = Path(__file__).with_name('i02_crossfield_checks.json')
destination.write_text(json.dumps(out, indent=2)+'\n')
print(json.dumps({'status':'passed', 'probability_checks':len(transversals), 'rank_two_checks':len(transfer), 'output':str(destination)}))
