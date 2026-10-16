"""One exact D4 junction example; not a tensor decomposition engine.
Myeongjin Kang; no affiliation. Original code MIT.
Affine expressions are certified on [0,1] by their endpoint values.
"""
from fractions import Fraction as F
import json


def A(c=0, slope=0):
    return (F(c), F(slope))


def add(a, b):
    return (a[0] + b[0], a[1] + b[1])


def mul(a, q):
    return (a[0] * q, a[1] * q)


def sub(a, b):
    return add(a, mul(b, -1))


def nonnegative(a):
    assert a[0] >= 0 and a[0] + a[1] >= 0, a


def vecadd(a, b):
    return [add(x, y) for x, y in zip(a, b)]


def vecsub(a, b):
    return [sub(x, y) for x, y in zip(a, b)]


def rootmul(root, q):
    return [mul(q, x) for x in root]


def dot(a, b):
    return sum(x * y for x, y in zip(a, b))


def affdot(a, b):
    out = A()
    for x, y in zip(a, b):
        out = add(out, mul(x, y))
    return out


def show(a):
    return [str(a[0]), str(a[1])]


def schedule(initial, velocity, roots, coefficients):
    displacement = [A() for _ in initial]
    times, gaps = [], []
    previous_time = A()
    for root, coefficient in zip(roots, coefficients):
        assert dot(root, root) == 2
        total = -dot(root, velocity)
        assert total > 0
        time = mul(coefficient, F(1, total))
        nonnegative(sub(time, previous_time))
        nonnegative(sub(A(1), time))
        position = vecsub(vecadd(initial, rootmul(velocity, time)), displacement)
        gap = affdot(position, root)
        nonnegative(gap)
        velocity = [x - dot(root, velocity) * y for x, y in zip(velocity, root)]
        displacement = vecadd(displacement, rootmul(root, coefficient))
        previous_time = time
        times.append(time)
        gaps.append(gap)
    endpoint = vecsub(vecadd(initial, [A(x) for x in velocity]), displacement)
    return endpoint, {"times": list(map(show, times)), "gaps": list(map(show, gaps))}


def in_root_lattice(v):
    return all(x.denominator == 1 for x in v) and sum(v) % 2 == 0


def solve(columns, target):
    mat = [[F(columns[j][i]) for j in range(len(columns))] + [F(target[i])]
           for i in range(len(target))]
    for col in range(len(columns)):
        pivot = next(i for i in range(col, len(mat)) if mat[i][col])
        mat[col], mat[pivot] = mat[pivot], mat[col]
        divisor = mat[col][col]
        mat[col] = [x / divisor for x in mat[col]]
        for row in range(len(mat)):
            if row != col:
                divisor = mat[row][col]
                mat[row] = [x - divisor * y for x, y in zip(mat[row], mat[col])]
    return [row[-1] for row in mat]


def main():
    a = [10, 7, 4, 1]
    b = c = [2, 0, 0, 0]
    d = [11, 7, 5, 1]
    bm, bp = [1, -1, 0, 0], [1, 1, 0, 0]
    dm, dp = [0, 0, 1, -1], [0, 0, 1, 1]
    bridge = [0, 1, -1, 0]
    assert in_root_lattice([x + y + z + t for x, y, z, t in zip(a, b, c, d)])
    ai, di = [A(x) for x in a], [A(x) for x in d]
    half = A(F(1, 2))

    z0, bad1 = schedule(ai, [-2, 0, 0, 0], [bm, bp], [half, half])
    end, bad2 = schedule(z0, [0, 0, -2, 0], [dm, dp], [half, half])
    assert end == di
    assert z0 == [A(x) for x in [11, 7, 4, 1]]
    assert not in_root_lattice([z[0] - x - y for z, x, y in zip(z0, a, b)])
    assert solve([bm, bp, dm, dp], [1, 0, 1, 0]) == [F(1, 2)] * 4

    z_alt, alt1 = schedule(ai, [-2, 0, 0, 0], [bm, bp], [A(1), A(1)])
    assert z_alt == ai
    end, alt2 = schedule(z_alt, [0, 0, 2, 0], [[1, 0, -1, 0]], [A(1)])
    assert end == di

    z, family1 = schedule(ai, [-2, 0, 0, 0], [bp, bm],
                          [A(F(1, 2), F(-1, 2)), A(F(1, 2), F(1, 2))])
    assert z == [A(11), A(7, 1), A(4), A(1)]
    end, family2 = schedule(z, [0, -2, 0, 0], [bridge, dm, dp],
                            [A(0, 1), A(F(1, 2), F(1, 2)), A(F(1, 2), F(1, 2))])
    assert end == di
    assert [x[0] for x in z] == [x[0] for x in z0]
    z1 = [x[0] + x[1] for x in z]
    assert z1 == [11, 8, 4, 1]
    assert in_root_lattice([q - x - y for q, x, y in zip(z1, a, b)])
    for i in range(2):
        nonnegative(sub(z[i], z[i + 1]))
    nonnegative(sub(z[2], z[3]))
    nonnegative(add(z[2], z[3]))
    assert [sum(k * r[i] for k, r in zip([-1, 1, 2, 1, 1], [bp, bm, bridge, dm, dp]))
            for i in range(4)] == [0, 0, 0, 0]

    result = {"status": "ONE_EXACT_D4_SCHEDULE_DIAGNOSTIC_ONLY",
              "full_Q4": "UNRESOLVED", "counted": False,
              "affine_certification": "nonnegative at both ends proves affine inequalities on [0,1]",
              "bad_fixed_system": [bad1, bad2],
              "alternative_good_system": [alt1, alt2],
              "feasible_bridge_family": [family1, family2],
              "junction_family": list(map(show, z)),
              "tensor_decompositions_computed": False,
              "universal_schedule_or_integrality_proof": False}
    print(json.dumps(result, sort_keys=True))


if __name__ == "__main__":
    main()
