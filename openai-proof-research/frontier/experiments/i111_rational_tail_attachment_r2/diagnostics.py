"""Independent finite bookkeeping, not a proof of any actual spectral map."""
from collections import Counter
from itertools import combinations


def exterior_degrees(degrees):
    return Counter(sum(degrees[i] for i in range(len(degrees)) if mask >> i & 1)
                   for mask in range(1 << len(degrees)))


def wedge(left, right):
    if set(left) & set(right):
        return 0, ()
    sign = (-1) ** sum(a > b for a in left for b in right)
    return sign, tuple(sorted(left + right))


def run():
    source = exterior_degrees((-1, -3, -5))
    lower = exterior_degrees((-1, -3))
    assert source[-5] == 1 and lower[-5] == 0 and lower[-4] == 1
    k2 = lower + Counter({d - 1: m for d, m in lower.items()})
    assert k2[-5] == 1
    gamma_a2 = Counter({-4: 2, -5: 1})
    gamma_w = gamma_a2 + Counter({d-1: m for d, m in gamma_a2.items()})
    gamma_f4 = gamma_w + Counter({-5: 1, -6: 1})
    boundary = {d: gamma_f4[d-1] for d in (-5, -6, -8, -9)}
    assert gamma_f4 == {-4: 2, -5: 4, -6: 2}
    assert boundary == {-5: 2, -6: 0, -8: 0, -9: 0}
    overlap = Counter({0: 1, -1: 1})
    total = overlap + Counter({d-1: 2*m for d, m in overlap.items()}) + Counter({d-2: m for d, m in overlap.items()})
    assert sorted(total) == [-3, -2, -1, 0] and total[-4] == total[-5] == 0
    # The universal proof uses period >= 8 and width 5; samples only check bookkeeping.
    edges = {}
    for p in (5, 7, 11, 13, 17, 19):
        period = 2*(p-1)
        points = [(s, s-5) for s in range(6) if (s-5) % period == 0]
        differentials = [r for r in range(2, 6) if (r-1) % period == 0]
        assert points == [(5, 0)] and differentials == [] and 6 % p != 0
        edges[p] = points
    # Abstract two-term trivial-action model: multiplication by tau is an
    # injection of the lower exterior basis into its disjoint second copy.
    basis = [c for n in range(3) for c in combinations((1, 2), n)]
    images = [wedge((0,), b) for b in basis]
    assert len(set(images)) == len(basis) and all(sign != 0 for sign, _ in images)
    assert wedge((0,), (1, 2)) == (1, (0, 1, 2))
    assert wedge((0,), (0,)) == (0, ())
    # The mixed Levi monomial is present, so generic algebra dimensions
    # cannot impose its coefficient in the actual additive primitive.
    levi = exterior_degrees((1, 3, 1))
    assert levi[5] == 1
    # A finite family of torsion quotients has no bound on exponents as
    # length grows. This is only the finite diagnostic for the written example.
    assert [max(e for e in range(l+1) if 5**e <= 5**l) for l in range(1,9)] == list(range(1,9))
    return {
        'source_degree_minus5_dimension': source[-5],
        'K2_corner_degree_minus5_dimension': k2[-5],
        'Gamma_F4': dict(sorted(gamma_f4.items())),
        'boundary_dimensions': boundary,
        'overlap_rational_degrees': sorted(total),
        'edge_sample_primes': list(edges),
        'abstract_tau_cup_injection_basis_size': len(basis),
        'mixed_Levi_degree5_dimension': levi[5],
        'scope': 'Finite algebra and degree bookkeeping only; no actual-map, limit, universal-proof or contribution certification.'
    }


if __name__ == '__main__':
    import json
    print(json.dumps(run(), sort_keys=True))
