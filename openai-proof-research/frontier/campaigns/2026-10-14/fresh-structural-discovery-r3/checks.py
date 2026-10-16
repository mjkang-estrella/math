#!/usr/bin/env python3
# Copyright (c) 2026 Myeongjin Kang. SPDX-License-Identifier: MIT
"""Exact finite diagnostics. Writes nothing; JSON goes only to stdout.

These are supporting finite tests, not a proof or independent review.
Only the Python standard library is used.
"""
from collections import Counter, deque
from itertools import product
import json


class Group:
    def __init__(self, elements, mul):
        self.elements = tuple(elements)
        self.n = len(elements)
        self.index = {x: i for i, x in enumerate(elements)}
        self.m = [[self.index[mul(x, y)] for y in elements] for x in elements]
        assert all(self.m[0][i] == self.m[i][0] == i for i in range(self.n))
        self.inv = [next(j for j in range(self.n)
                         if self.m[i][j] == self.m[j][i] == 0)
                    for i in range(self.n)]
        assert all(self.m[self.m[i][j]][k] == self.m[i][self.m[j][k]]
                   for i in range(self.n) for j in range(self.n)
                   for k in range(self.n))

    def closure(self, generators):
        seen = {0}
        todo = deque([0])
        while todo:
            x = todo.popleft()
            for g in generators:
                y = self.m[x][g]
                if y not in seen:
                    seen.add(y)
                    todo.append(y)
        return frozenset(seen)

    def subgroups(self):
        seed = frozenset([0])
        result = {seed: ()}
        todo = deque([seed])
        while todo:
            H = todo.popleft()
            remaining = set(range(self.n)) - H
            while remaining:
                x = min(remaining)
                remaining.difference_update(self.m[h][x] for h in H)
                generators = result[H] + (x,)
                K = self.closure(generators)
                if K not in result:
                    result[K] = generators
                    todo.append(K)
        return sorted(result, key=lambda H: (len(H), tuple(sorted(H))))

    def conjugate(self, H, x):
        return frozenset(self.m[self.m[x][h]][self.inv[x]] for h in H)


def semidirect(N, alpha, L, p):
    power = [tuple(range(N.n))]
    for _ in range(1, p**L):
        power.append(tuple(alpha[x] for x in power[-1]))
    assert tuple(alpha[x] for x in power[-1]) == power[0]
    for x in range(N.n):
        for y in range(N.n):
            assert alpha[N.m[x][y]] == N.m[alpha[x]][alpha[y]]
    return Group(list(product(range(N.n), range(p**L))),
                 lambda x, y: (N.m[x[0]][power[x[1]][y[0]]],
                                (x[1] + y[1]) % (p**L)))


def abelian(moduli):
    return Group(list(product(*(range(m) for m in moduli))),
                 lambda x, y: tuple((a+b) % m for a, b, m in zip(x, y, moduli)))


def index_level(order, size, p):
    n, h = order // size, 0
    while n > 1:
        assert n % p == 0
        n //= p
        h += 1
    return h


def abelian_count(p, d, h):
    a = [1] + [0]*h
    for i in range(d):
        for j in range(1, h+1):
            a[j] += p**i * a[j-1]
    return a[h]


def run():
    diagnostics = []
    mutations = Counter()
    # Finite kernels exercise the unrestricted semidirect lemma, including
    # conjugacy classes in a nonabelian kernel. L >= tested index depth.
    V = abelian([2, 2])
    shear = tuple(V.index[((x+y) % 2, y)] for x, y in V.elements)
    C = abelian([4])
    inversion = tuple(C.index[((-x) % 4,)] for (x,) in C.elements)
    D = Group(list(product(range(4), range(2))),
              lambda x, y: ((x[0] + (-1)**x[1]*y[0]) % 4,
                            (x[1]+y[1]) % 2))
    outer = tuple(D.index[((x+y) % 4, y)] for x, y in D.elements)
    for name, N, alpha, p, L in [
            ('C2^2_shear', V, shear, 2, 3),
            ('C4_inversion', C, inversion, 2, 3),
            ('D8_outer_order4', D, outer, 2, 2)]:
        S = N.subgroups()
        classes, unseen = [], set(S)
        while unseen:
            H = min(unseen, key=lambda K: (len(K), tuple(sorted(K))))
            orbit = frozenset(N.conjugate(H, x) for x in range(N.n))
            classes.append(orbit)
            unseen.difference_update(orbit)
        class_index = {H: i for i, cl in enumerate(classes) for H in cl}
        perm = [class_index[frozenset(alpha[x] for x in next(iter(cl)))]
                for cl in classes]
        by_level = Counter(index_level(N.n, len(next(iter(cl))), p)
                           for cl in classes)
        def fixed(b, exponent):
            total = 0
            for i, cl in enumerate(classes):
                if index_level(N.n, len(next(iter(cl))), p) != b:
                    continue
                j = i
                for _ in range(exponent):
                    j = perm[j]
                total += j == i
            return total
        G = semidirect(N, alpha, L, p)
        SG = G.subgroups()
        direct = semidirect(N, tuple(range(N.n)), L, p)
        SD = direct.subgroups()
        row = {'name': name, 'kernel_order': N.n, 'quotient_order': p**L,
               'group_order': G.n, 'kernel_subgroups': len(S),
               'kernel_conjugacy_classes': len(classes),
               'all_finite_subgroups': len(SG), 'depths': []}
        for h in range(L+1):
            actual = sum(index_level(G.n, len(H), p) == h for H in SG)
            actual_direct = sum(index_level(direct.n, len(H), p) == h for H in SD)
            formula = sum(p**b * fixed(b, p**(h-b)) for b in range(h+1))
            formula_direct = sum(p**b * by_level[b] for b in range(h+1))
            assert actual == formula and actual_direct == formula_direct
            assert (actual-actual_direct) % p**(h+1) == 0
            if actual != sum(p**b * fixed(b, 1) for b in range(h+1)):
                mutations['freeze_action_power'] += 1
            if actual != sum(fixed(b, p**(h-b)) for b in range(h+1)):
                mutations['omit_index_weight'] += 1
            # Incorrectly use actual subgroups in the direct-product formula.
            bad = sum(p**b * sum(index_level(N.n, len(H), p) == b for H in S)
                      for b in range(h+1))
            if actual_direct != bad:
                mutations['omit_conjugacy_quotient'] += 1
            row['depths'].append({'h': h, 'actual': actual,
                                  'direct': actual_direct,
                                  'difference': actual-actual_direct,
                                  'modulus': p**(h+1)})
        diagnostics.append(row)

    poly = []
    # Quotients of actual torsion-free poly-Z_p groups. Coordinate p^L-powers
    # are killed; L >= h captures every coset action of degree p^h.
    examples = []
    for p, L in [(2, 2), (3, 1)]:
        q = p**L
        H = Group(list(product(range(q), repeat=3)),
                  lambda x, y, q=q: ((x[0]+y[0]) % q,
                                      (x[1]+y[1]) % q,
                                      (x[2]+y[2]+x[0]*y[1]) % q))
        examples.append((f'Heisenberg_p{p}_L{L}', H, p, L, 3))
    A = abelian([4, 4])
    diag = tuple(A.index[((3*x) % 4, y)] for x, y in A.elements)
    examples.append(('Z2^2_by_diag3_1', semidirect(A, diag, 2, 2), 2, 2, 3))
    flags = 0
    for name, G, p, L, t in examples:
        S = G.subgroups()
        counts = []
        for h in range(L+1):
            a = sum(index_level(G.n, len(H), p) == h for H in S)
            baseline = abelian_count(p, t, h)
            assert (a-baseline) % p**(h+1) == 0
            if (a-baseline) % p**(h+2):
                mutations['overstate_modulus'] += 1
            counts.append({'h': h, 'actual': a, 'abelian': baseline,
                           'difference': a-baseline})
        # Independent fixed-coset calculation of the full mark sums.
        for U in S:
            depth_U = index_level(G.n, len(U), p)
            if depth_U > L:
                continue
            subs = [W for W in S if W <= U]
            for W in subs:
                if index_level(G.n, len(W), p) > L:
                    continue
                cosets, remaining = [], set(U)
                while remaining:
                    x = min(remaining)
                    coset = frozenset(G.m[x][w] for w in W)
                    cosets.append(coset)
                    remaining.difference_update(coset)
                for h in range(L-depth_U+1):
                    total = 0
                    for Vsub in subs:
                        if index_level(len(U), len(Vsub), p) != h:
                            continue
                        fix = sum(all(frozenset(G.m[v][x] for x in coset) == coset
                                      for v in Vsub) for coset in cosets)
                        total += fix-len(cosets)
                    assert total % p**(h+1) == 0
                    flags += 1
        poly.append({'name': name, 'order': G.n, 'all_finite_subgroups': len(S),
                     'length': t, 'counts': counts})

    # Exact abelian truncation/limit residues and separation of lengths.
    residues = 0
    for p in [2, 3, 5, 7]:
        for t in range(1, 9):
            for h in range(10):
                modulus = p**(h+1)
                denominator = 1
                for i in range(1, t):
                    denominator *= 1-p**i
                assert (abelian_count(p, t, h)-pow(denominator, -1, modulus)) % modulus == 0
                residues += 1
    required = {'freeze_action_power', 'omit_index_weight',
                'omit_conjugacy_quotient', 'overstate_modulus'}
    assert set(mutations) == required and all(mutations[x] for x in required)
    return {'status': 'PASS', 'arithmetic': 'exact integers only',
            'semidirect_tests': diagnostics, 'poly_Zp_quotients': poly,
            'fixed_coset_flags': flags, 'abelian_residue_tests': residues,
            'mutation_rejections': dict(sorted(mutations.items())),
            'scope': 'Finite support only; not a universal proof or independent review.'}


if __name__ == '__main__':
    print(json.dumps(run(), indent=2, sort_keys=True))
