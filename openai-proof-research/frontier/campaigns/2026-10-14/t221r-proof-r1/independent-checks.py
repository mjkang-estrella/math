#!/usr/bin/env python3
"""MIT. Reviewer's independent exact finite replays for T221R interfaces.

These are finite sanity checks of counting identities re-derived by the
reviewer. They are NOT a proof of T221R or of any asymptotic statement.
"""
from collections import Counter
from fractions import Fraction as F
from itertools import combinations, product
from math import comb
import json
import random


def matchings(ports):
    ports = tuple(sorted(ports))
    if not ports:
        yield ()
        return
    x = ports[0]
    for j in range(1, len(ports)):
        for tail in matchings(ports[1:j] + ports[j + 1:]):
            yield tuple(sorted(((x, ports[j]),) + tail))


def dfact(m):
    out = 1
    while m > 1:
        out *= m
        m -= 2
    return out


def check_deletion():
    """Deleting a prescribed port pair with splicing maps uniform to uniform."""
    ports = range(10)
    a, b = 3, 7
    out = Counter()
    for m in matchings(ports):
        mate = {u: v for u, v in m} | {v: u for u, v in m}
        edges = set(m)
        if mate[a] == b:
            edges.discard(tuple(sorted((a, b))))
        else:
            za, zb = mate[a], mate[b]
            edges.discard(tuple(sorted((a, za))))
            edges.discard(tuple(sorted((b, zb))))
            edges.add(tuple(sorted((za, zb))))
        out[tuple(sorted(edges))] += 1
    target = list(matchings([p for p in ports if p not in (a, b)]))
    assert set(out) == set(target)
    assert set(out.values()) == {1 + 2 * 4}
    return {'ports': 10, 'targets': len(target), 'preimages_each': 9}


def full_edge_sets(m, d, holes, k):
    eligible = [e for e in m if e[0] // d != e[1] // d
                and e[0] // d not in holes and e[1] // d not in holes]
    return sum(len({p // d for e in es for p in e}) == 2 * k
               for es in combinations(eligible, k))


def check_normalization_and_identity(n, d, q, ks):
    """E M_k formula, and E=(dn-q)/2-q(d-1)+E_hh-L_ff on every matching."""
    holes = set(range(q))
    missing = {v * d + d - 1 for v in holes}
    ports = [p for p in range(n * d) if p not in missing]
    N = len(ports)
    ms = list(matchings(ports))
    tot = {k: 0 for k in ks}
    for m in ms:
        E = sum(1 for u, v in m if u // d != v // d
                and u // d not in holes and v // d not in holes)
        Ehh = sum(1 for u, v in m if u // d in holes and v // d in holes)
        Lff = sum(1 for u, v in m if u // d == v // d and u // d not in holes)
        assert 2 * E == (d * n - q) - 2 * q * (d - 1) + 2 * Ehh - 2 * Lff
        for k in ks:
            tot[k] += full_edge_sets(m, d, holes, k)
    res = {}
    for k in ks:
        den = 1
        for j in range(1, k + 1):
            den *= N - (2 * j - 1)
        formula = F(comb(n - q, 2 * k) * dfact(2 * k - 1) * d ** (2 * k), den)
        assert F(tot[k], len(ms)) == formula
        res[str(k)] = str(formula)
    return {'n': n, 'd': d, 'q': q, 'matchings': len(ms), 'E_M_k': res,
            'edge_identity_all_matchings': True}


def check_bond_full_randomness(n, d, q):
    """Bond completion from C(n,q+2d) with ALL missing ports random.

    Final law of (A, missing ports, matching) must be proportional to M_d,
    and the marginal of (A, missing ports) must be uniform."""
    final = Counter()
    V = range(n)
    for cav in combinations(V, q + 2 * d):
        for prt in product(range(d), repeat=q + 2 * d):
            miss = {v * d + p for v, p in zip(cav, prt)}
            rest = [x for x in range(n * d) if x not in miss]
            for old in matchings(rest):
                for filled in combinations(range(q + 2 * d), 2 * d):
                    fill_ports = [cav[i] * d + prt[i] for i in filled]
                    A = tuple(cav[i] for i in range(q + 2 * d) if i not in filled)
                    Ap = tuple(prt[i] for i in range(q + 2 * d) if i not in filled)
                    for added in matchings(fill_ports):
                        final[(A, Ap, tuple(sorted(old + added)))] += 1
    by_key = Counter()
    for (A, Ap, m), c in final.items():
        by_key[(A, Ap)] += c
    assert len(set(by_key.values())) == 1
    assert len(by_key) == comb(n, q) * d ** q
    keys = 0
    for (A, Ap), _ in by_key.items():
        miss = {v * d + p for v, p in zip(A, Ap)}
        rest = [x for x in range(n * d) if x not in miss]
        cands = list(matchings(rest))
        ratios = set()
        for m in cands:
            M = full_edge_sets(m, d, set(A), d)
            c = final.get((A, Ap, m), 0)
            if M == 0:
                assert c == 0
            else:
                ratios.add(F(c, M))
        assert len(ratios) == 1
        keys += 1
    return {'n': n, 'd': d, 'q': q, 'cavity_port_keys': keys,
            'density_proportional_to_M_d': True,
            'cavity_and_port_marginal_uniform': True}


def check_star_sequential(n, d, q):
    """Exact law of the sequential star switch on a tiny instance."""
    holes = set(range(q))
    missing = {v * d + d - 1 for v in holes}
    old = [p for p in range(n * d) if p not in missing]
    new = list(range(n * d, n * d + 2 * d))
    allp = old + new
    ms = list(matchings(allp))
    state = Counter({m: F(1, len(ms)) for m in ms})
    vert = lambda p: p // d
    full_old = [v for v in range(n) if v not in holes]
    exp_switch = F(0)
    for j, x in enumerate(new):
        nxt = Counter()
        p_illegal = F(0)
        legal_sizes = set()
        for m, pr in state.items():
            mate = {u: v for u, v in m} | {v: u for u, v in m}
            used = {vert(mate[y]) for y in new[:j]}
            legal = {p for v in full_old if v not in used
                     for p in range(v * d, v * d + d)}
            legal_sizes.add(len(legal))
            z = mate[x]
            if z in legal:
                nxt[m] += pr
                continue
            p_illegal += pr
            for y in sorted(legal):
                w = mate[y]
                e = set(m)
                e.remove(tuple(sorted((x, z))))
                e.remove(tuple(sorted((y, w))))
                e.add(tuple(sorted((x, y))))
                e.add(tuple(sorted((z, w))))
                nxt[tuple(sorted(e))] += pr / len(legal)
        assert legal_sizes == {d * (n - q - j)}
        # uniform conditional law: illegal probability equals the port fraction
        frozen_ports = 2 * j
        remaining = len(allp) - frozen_ports - 1
        assert p_illegal == F(remaining - d * (n - q - j), remaining)
        exp_switch += p_illegal
        state = nxt
    good = []
    for m in ms:
        mate = {u: v for u, v in m} | {v: u for u, v in m}
        nb = [vert(mate[x]) for x in new]
        if all(v in full_old for v in nb) and len(set(nb)) == 2 * d:
            good.append(m)
    assert set(state) == set(good)
    assert set(state.values()) == {F(1, len(good))}
    return {'n': n, 'd': d, 'q': q, 'matchings': len(ms),
            'conditional_matchings': len(good), 'exact_uniform_on_G': True,
            'expected_switches': str(exp_switch)}


def check_interface_algebra():
    """LO site/edge terms versus scope V_s, V_e at one RS evaluation."""
    rng = random.Random(221)
    import math
    worst = 0.0
    for _ in range(200):
        d = rng.randint(3, 6)
        beta = rng.uniform(0.1, 2.0)
        H = rng.uniform(-2, 2)
        J = [rng.uniform(-2, 2) for _ in range(d + 1)]
        x = [rng.uniform(-3, 3) for _ in range(d + 2)]
        q = lambda xx, s: math.exp(xx * s) / (2 * math.cosh(xx))
        U = lambda j, sig: math.log(sum(math.exp(beta * J[j] * e * sig) * q(x[j], e)
                                        for e in (-1, 1)))
        lo_site = sum(math.exp(sum(U(j, sig) for j in range(d)) + beta * H * sig)
                      for sig in (-1, 1))
        vs = 0.5 * sum(math.exp(beta * H * eps) *
                       math.prod(sum(math.exp(beta * J[j] * s * eps) * q(x[j], s)
                                     for s in (-1, 1)) for j in range(d))
                       for eps in (-1, 1))
        lo_edge = sum(math.exp(beta * J[d] * a * b) * q(x[d], a) * q(x[d + 1], b)
                      for a in (-1, 1) for b in (-1, 1))
        a = math.cosh(beta * J[d]); bb = math.tanh(beta * J[d])
        fact = sum(a * (1 + bb * a1 * b1) * q(x[d], a1) * q(x[d + 1], b1)
                   for a1 in (-1, 1) for b1 in (-1, 1))
        worst = max(worst, abs(math.log(lo_site) - math.log(2) - math.log(vs)),
                    abs(lo_edge - fact))
    assert worst < 1e-12
    return {'samples': 200, 'site_term_equals_log2_plus_logVs': True,
            'ising_factorization_a_cosh_b_tanh': True}


def check_constants():
    janson = {}
    for d in range(3, 21):
        lam = F(d - 1, 2)
        assert lam + lam * lam == F(d * d - 1, 4)
        janson[str(d)] = str(lam + lam * lam)
    a, b, rho = F(9, 10), F(3, 4), F(1, 8)
    exps = {'q_over_n': a - 1, 's_over_q': b - a, 'bond_tilt_sqrt_q_over_n': (a - 1) / 2,
            'star_q_over_n': a - 1, 'convex_sqrt_n_over_rho_s': F(1, 2) + rho - b,
            'rho': -rho, 's_increment': b - 1, 'collision_one_over_q': -a,
            'bad_index_density': a - 1, 'pressure_shift_q_plus_s_over_n': a - 1}
    assert all(v < 0 for v in exps.values())
    return {'janson_lambda_plus_lambda_sq': janson,
            'exponents': {k: str(v) for k, v in exps.items()}}


def main():
    out = {
        'status': 'PASS_REVIEWER_FINITE_REPLAYS_ONLY_NOT_A_PROOF',
        'matching_deletion': check_deletion(),
        'normalization': [check_normalization_and_identity(4, 2, 0, [1, 2]),
                          check_normalization_and_identity(6, 2, 2, [1, 2]),
                          check_normalization_and_identity(4, 3, 0, [1, 2]),
                          check_normalization_and_identity(4, 3, 2, [1])],
        'bond_full_randomness': [check_bond_full_randomness(4, 2, 0),
                                 check_bond_full_randomness(6, 2, 2)],
        'star_sequential': [check_star_sequential(4, 2, 0),
                            check_star_sequential(6, 2, 2)],
        'interface_algebra': check_interface_algebra(),
        'constants': check_constants(),
    }
    print(json.dumps(out, sort_keys=True, indent=2))


if __name__ == '__main__':
    main()
