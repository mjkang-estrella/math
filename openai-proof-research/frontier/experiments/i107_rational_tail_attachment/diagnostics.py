"""Finite bookkeeping only. Does not verify actual spectral/coefficient maps."""
from collections import Counter
from itertools import combinations, product


def shift(a, n):
    return Counter({d+n: m for d, m in a.items()})


def exterior(degrees):
    result = Counter()
    for mask in range(1 << len(degrees)):
        result[sum(x for i, x in enumerate(degrees) if mask & (1 << i))] += 1
    return result


def multiply(a, b):
    if a & b:
        return 0, 0
    sign = (-1) ** sum(i > j for i in range(3) for j in range(3)
                       if a & (1 << i) and b & (1 << j))
    return sign, a | b


def run():
    gamma_a1 = Counter({-2: 1})
    gamma_a2 = Counter({-4: 2, -5: 1})
    gamma_w = gamma_a2 + shift(gamma_a2, -1)
    gamma_u = shift(gamma_a1, -3) + shift(gamma_a1, -4)
    gamma_f4 = gamma_w + gamma_u
    assert gamma_f4 == Counter({-4: 2, -5: 4, -6: 2})
    targets = shift(gamma_f4, 1)
    boundary = {d: targets[d] for d in (-5, -6, -8, -9)}
    assert boundary == {-5: 2, -6: 0, -8: 0, -9: 0}
    r1 = exterior((-1,))
    overlap = r1 + shift(r1, -1) + shift(r1, -1) + shift(r1, -2)
    assert overlap[-4] == overlap[-5] == 0
    r2 = exterior((-1, -3))
    k2_target = r2 + shift(r2, -1)
    assert r2[-5] == 0 and r2[-4] == 1 and k2_target[-5] == 1
    k1_target = r1 + shift(r1, -1) + shift(r1, -3) + shift(r1, -4)
    assert k1_target[-5] == 1
    assert exterior((-1, -3, -5))[-5] == 1
    # Only t=0 lies in [-5,0] among multiples of any period >=8.
    assert all(not (-5 <= 8*k <= 0) for k in (-2, -1, 1, 2))
    # Symbolic exterior sign bookkeeping, independent of any realization.
    for a, b, c in product(range(8), repeat=3):
        ab, mab = multiply(a, b)
        bc, mbc = multiply(b, c)
        left, lm = multiply(mab, c)
        right, rm = multiply(a, mbc)
        ls, rs = ab*left, bc*right
        assert ls == rs and (ls == 0 or lm == rm)
    assert multiply(1, 6) == (1, 7)  # tau times lower top class
    return {
        'Gamma_F4': dict(sorted(gamma_f4.items())),
        'boundary_dimensions': boundary,
        'overlap_rational_degrees': sorted(overlap),
        'K1_and_K2_degree_minus5_dimensions': [1, 1],
        'source_degree_minus5_dimension': 1,
        'exterior_associativity_triples': 512,
        'scope': 'Finite bookkeeping; actual maps, uniform limits and universal proofs are in the report.'
    }


if __name__ == '__main__':
    import json
    print(json.dumps(run(), sort_keys=True))
