#!/usr/bin/env python3
"""MIT, Myeongjin Kang. Exact supporting arithmetic, not a proof of R.

No file/network access, imports only standard-library arithmetic and JSON.
The three-color, simple-label algebra is the actual source algebra for
S={s}, X=empty. Composition is in path order.
"""
from fractions import Fraction
import hashlib
import json


def rank(a):
    if not a:
        return 0
    a = [[Fraction(v) for v in row] for row in a]
    r = 0
    for c in range(len(a[0])):
        k = next((k for k in range(r, len(a)) if a[k][c]), None)
        if k is None:
            continue
        a[r], a[k] = a[k], a[r]
        q = a[r][c]
        a[r] = [x/q for x in a[r]]
        for k in range(len(a)):
            if k != r and a[k][c]:
                q = a[k][c]
                a[k] = [x-q*y for x, y in zip(a[k], a[r])]
        r += 1
        if r == len(a):
            break
    return r


def paths(a, b):
    return (0, 2) if a == b else (1,)


def compose(a, b, c, l, k):
    """Path a->b length l followed by b->c length k, or zero."""
    return l+k if l+k in paths(a, c) else None


# Summands are (color, cochain placement, internal placement).
# Differentials are (source summand, target summand, length, coefficient).
P = ([('f', 0, 0)], [])
E1 = ([('s', -1, 1), ('f', 0, 0)], [(0, 1, 1, 1)])
E2 = ([('s', -2, 3), ('s', -1, 1), ('f', 0, 0)],
      [(0, 1, 2, 1), (1, 2, 1, 1)])


def validate(C):
    summands, d = C
    for i, j, l, q in d:
        a, c, u = summands[i]
        b, e, v = summands[j]
        assert e == c+1 and v+l == u and l in paths(a, b)
        assert q and l > 0
    out = {}
    for i, j, l, q in d:
        for jj, k, t, v in d:
            if j == jj:
                x = compose(summands[i][0], summands[j][0],
                            summands[k][0], l, t)
                if x is not None:
                    key = (i, k, x)
                    out[key] = out.get(key, 0)+q*v
    assert all(q == 0 for q in out.values())


def layer(C, lev):
    summands, d = C
    ids = [i for i, (_, c, u) in enumerate(summands) if c+u == lev]
    idx = {i: j for j, i in enumerate(ids)}
    return ([summands[i] for i in ids],
            [(idx[i], idx[j], l, q) for i, j, l, q in d
             if i in idx and j in idx and l == 1])


def direct_sum(C, D):
    a, b = C
    c, d = D
    return (a+c, b+[(i+len(a), j+len(a), l, q) for i, j, l, q in d])


def hom(C, D, linear=False):
    """Full bigraded Hom, or its length-one linear-page homology."""
    s, ds = C
    t, dt = D
    basis = {}
    for i, (a, c, u) in enumerate(s):
        for j, (b, e, v) in enumerate(t):
            for l in paths(a, b):
                n, w = e-c, v+l-u
                key = (n, w, l) if linear else (n, w)
                basis.setdefault(key, []).append((i, j, l))

    def nxt(key):
        return (key[0]+1, key[1], key[2]+1) if linear else (key[0]+1, key[1])

    def prev(key):
        return (key[0]-1, key[1], key[2]-1) if linear else (key[0]-1, key[1])

    matrices = {}
    for key, source_basis in basis.items():
        target_basis = basis.get(nxt(key), [])
        index = {x: k for k, x in enumerate(target_basis)}
        mat = [[0]*len(source_basis) for _ in target_basis]
        for col, (i, j, l) in enumerate(source_basis):
            # d_D phi
            for jj, k, a, q in dt:
                if jj != j or (linear and a != 1):
                    continue
                z = compose(s[i][0], t[j][0], t[k][0], l, a)
                if z is not None:
                    mat[index[(i, k, z)]][col] += q
            # -(-1)^n phi d_C
            for k, ii, a, q in ds:
                if ii != i or (linear and a != 1):
                    continue
                z = compose(s[k][0], s[i][0], t[j][0], a, l)
                if z is not None:
                    mat[index[(k, j, z)]][col] -= (-1 if key[0] % 2 else 1)*q
        matrices[key] = mat
    for key, mat in matrices.items():
        nm = matrices.get(nxt(key), [])
        for row in nm:
            for col in range(len(basis[key])):
                assert sum(row[k]*mat[k][col] for k in range(len(mat))) == 0
    ans = []
    for key in sorted(basis):
        if linear and key[2] != 1:
            continue
        out_rank = rank(matrices[key])
        in_rank = rank(matrices.get(prev(key), []))
        h = len(basis[key])-out_rank-in_rank
        assert h >= 0
        if h:
            ans.append({'degree': list(key), 'dimension': h,
                        'term_dimension': len(basis[key]),
                        'out_rank': out_rank, 'in_rank': in_rank})
    return ans


def perm_mul(a, b):
    return tuple(a[b[i]] for i in range(len(a)))


def main():
    for C in [P, E1, E2]:
        validate(C)
    # Associativity across all source-algebra path bases.
    assoc = 0
    for a in 'fso':
        for b in 'fso':
            for c in 'fso':
                for d in 'fso':
                    for l in paths(a, b):
                        for k in paths(b, c):
                            for j in paths(c, d):
                                x, y = compose(a, b, c, l, k), compose(b, c, d, k, j)
                                lhs = None if x is None else compose(a, c, d, x, j)
                                rhs = None if y is None else compose(a, b, d, l, y)
                                assert lhs == rhs
                                assoc += 1
    expected = [{'degree': [-2, 4, 1], 'dimension': 1,
                 'term_dimension': 1, 'out_rank': 0, 'in_rank': 0}]
    cross = hom(P, layer(E2, 1), linear=True)
    assert cross == expected
    same = []
    for name, C in [('P', P), ('E1', E1), ('E2', E2)]:
        levels = sorted({c+u for _, c, u in C[0]})
        for l in levels:
            for k in levels:
                v = hom(layer(C, l), layer(C, k), linear=True)
                assert not v
                same.append([name, l, k])
    summed = direct_sum(P, E2)
    aggregate = hom(layer(summed, 0), layer(summed, 1), linear=True)
    assert [(x["degree"], x["dimension"]) for x in aggregate] == [([-2, 4, 1], 1)]
    assert aggregate[0]["term_dimension"] == 2 and aggregate[0]["out_rank"] == 1
    full = hom(P, E2)
    assert [(x['degree'], x['dimension']) for x in full] == [([-2, 4], 1), ([0, 0], 1)]
    # Deliberately asserted blanket middle vanishing is rejected.
    assert sum(x['dimension'] for x in cross) != 0
    # Token*arrow must be zero; a fabricated length-3 path is detected.
    assert compose('s', 's', 'f', 2, 1) is None
    s, t = (1, 0, 2), (0, 2, 1)
    st, ts = perm_mul(s, t), perm_mul(t, s)
    assert st != ts
    assert perm_mul(perm_mul(st, st), st) == (0, 1, 2)
    assert perm_mul(perm_mul(ts, ts), ts) == (0, 1, 2)
    data = {'associativity_basis_triples': assoc,
            'same_transport_layer_pairs_with_zero_h1': same,
            'cross_middle': cross, 'sum_middle': aggregate,
            'actual_bigraded_hom_P_E2': full,
            'braid_distinct_S3_images': [list(st), list(ts)],
            'negative_controls': ['blanket_middle_vanishing_rejected',
                                  'spurious_length3_path_rejected'],
            'scope': 'finite supporting algebra only; full R UNRESOLVED'}
    raw = json.dumps(data, sort_keys=True, separators=(',', ':')).encode()
    print(json.dumps({'data': data, 'data_sha256': hashlib.sha256(raw).hexdigest()},
                     sort_keys=True, indent=2))


if __name__ == '__main__':
    main()
