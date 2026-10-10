#!/usr/bin/env python3
"""Read-only exact finite stress tests. These are not analytic proofs."""
import itertools
import json
from fractions import Fraction


def run():
    cases = edges_checked = loop_cases = 0
    for nv in range(1, 4):
        perms = list(itertools.permutations(range(nv)))
        for p1, p2 in itertools.product(perms, repeat=2):
            inc = []
            outgoing = [[] for _ in range(nv)]
            for perm in (p1, p2):
                for x, y in enumerate(perm):
                    i = len(inc)
                    inc.extend([(x, y, i + 1), (y, x, i)])
                    outgoing[x].append(i)
                    outgoing[y].append(i + 1)
            assert all(len(o) == 4 for o in outgoing)
            for bits in itertools.product((False, True), repeat=nv * 2):
                compatible = lambda x, j: bits[2 * x + j]
                for cross in (False, True):
                    trans = lambda j, k: j == k or cross
                    # r[e,j] is maximum matched length, truncated at n.
                    r = {(e, j): 0 for e in range(len(inc)) for j in range(2)}
                    for n in range(1, 5):
                        old = r
                        r = {}
                        for e, (x, y, rev) in enumerate(inc):
                            for j in range(2):
                                candidates = []
                                if compatible(x, j):
                                    for k in range(2):
                                        if trans(j, k) and compatible(y, k):
                                            candidates.append(1 + max(old[(f, k)] for f in outgoing[y] if f != rev))
                                r[e, j] = max(candidates, default=0)
                        if n < 2:
                            continue
                        bad = [any(r[e, j] == n for e in outgoing[x] for j in range(2)) for x in range(nv)]
                        def exceptional(e, j):
                            x = inc[e][0]
                            return bad[x] or all(r[e, j] > r[f, j] for f in outgoing[x] if f != e)
                        for x in range(nv):
                            if not bad[x]:
                                assert all(sum(exceptional(e, j) for e in outgoing[x]) <= 1 for j in range(2))
                        for e, (x, y, rev) in enumerate(inc):
                            for j, k in itertools.product(range(2), repeat=2):
                                if compatible(x, j) and compatible(y, k) and trans(j, k):
                                    assert exceptional(e, j) or exceptional(rev, k)
                                    edges_checked += 1
                        cases += 1
                        loop_cases += any(x == y for x, y, _ in inc)
    constants = []
    for p in range(1, 5):
        L, R = 10 * p, 30 * p
        K = 10 * p * (R + 1)
        D = K + 2 * L + 5
        B = 4 * R + D
        V = 1 + 4 * p * B
        delta = 20 * V + 2
        Q, H = delta ** (2 * L + 1), delta ** (D + 1)
        k = 2 * delta * Q * H + 1
        rho = Fraction(delta * Q * H, k)
        assert rho < Fraction(1, 2)
        assert Fraction(2 * p * R + 1, K) <= Fraction(1, 5)
        assert Fraction(V, delta) < Fraction(1, 20)
        lower = Fraction(3 * L, 2) - 4 * L * (Fraction(V, delta) + Fraction(1, 20))
        assert lower > 11 * p > 2 * p
        constants.append(dict(p=p, L=L, R=R, K=K, D=D, B=B, V=V, delta=delta,
                              k_bits=k.bit_length(), gap_above_2p=str(lower - 2*p)))
    diffuse = []
    for N in (2, 8, 64, 256):
        B = 455
        threshold = Fraction(1, 4 * B)
        for s in range(N // 2 + 1):
            assert Fraction(N-s, 2*B*N) >= threshold
        diffuse.append(dict(N=N, support_at_most=N//2, norm_error_at_least=str(threshold)))
    return dict(status='PASS_FINITE_STRESS_TESTS_ONLY', continuation_cases=cases,
                compatible_edge_state_checks=edges_checked, cases_with_loops=loop_cases,
                constants=constants, diffuse_rank_one=diffuse)


if __name__ == '__main__':
    print(json.dumps(run(), indent=2, sort_keys=True))
