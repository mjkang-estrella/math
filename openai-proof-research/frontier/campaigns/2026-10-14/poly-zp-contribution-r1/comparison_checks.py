#!/usr/bin/env python3
# Copyright (c) 2026 Myeongjin Kang. SPDX-License-Identifier: MIT
"""Independent finite check of the GRV Euler-factor reduction; stdout only."""
from collections import Counter
import json


def subgroups(table):
    def generate(seed):
        group = {0}
        todo = [0]
        while todo:
            x = todo.pop()
            for y in seed:
                z = table[x][y]
                if z not in group:
                    group.add(z)
                    todo.append(z)
        return frozenset(group)
    known = {frozenset({0})}
    todo = list(known)
    while todo:
        group = todo.pop()
        for x in range(len(table)):
            if x not in group:
                nxt = generate(tuple(group) + (x,))
                if nxt not in known:
                    known.add(nxt)
                    todo.append(nxt)
    return known


def euler_subgroup_counts(factors, maximum):
    coefficients = [1] + [0] * maximum
    for degree in factors:
        if degree <= maximum:
            for n in range(degree, maximum + 1):
                coefficients[n] += coefficients[n - degree]
    # x F'(x) = (sum s_n x^n) F(x): s_n counts actual subgroups.
    counts = [0] * (maximum + 1)
    for n in range(1, maximum + 1):
        counts[n] = n * coefficients[n] - sum(
            counts[k] * coefficients[n-k] for k in range(1, n))
    return counts


def run():
    # D8 = {(r,s)} with r^4=s^2=1 and srs=r^-1.
    pairs = [(r,s) for r in range(4) for s in range(2)]
    index = {v:i for i,v in enumerate(pairs)}
    def mul(x,y):
        r,s = pairs[x]; u,v = pairs[y]
        return index[((r + (-1)**s * u) % 4, (s+v) % 2)]
    table = [[mul(x,y) for y in range(8)] for x in range(8)]
    inverse = [next(y for y in range(8) if mul(x,y)==mul(y,x)==0) for x in range(8)]
    subs = subgroups(table)
    classes = set()
    for group in subs:
        classes.add(frozenset(frozenset(mul(mul(x,y),inverse[x]) for y in group)
                              for x in range(8)))
    class_of = {group:cl for cl in classes for group in cl}
    alpha = [index[((r+s)%4,s)] for r,s in pairs] # r -> r, s -> rs
    unseen = set(classes)
    orbits = []
    while unseen:
        cl = min(unseen, key=lambda c: sorted(sorted(s) for s in c))
        orbit = set(); current = cl
        while current not in orbit:
            orbit.add(current)
            representative = next(iter(current))
            current = class_of[frozenset(alpha[x] for x in representative)]
        unseen -= orbit
        b = (8 // len(next(iter(cl)))).bit_length()-1
        j = len(orbit).bit_length()-1
        assert len(orbit)==2**j
        orbits.append((b,j))
    orbits.sort()
    action_factors = [2**(b+j) for b,j in orbits]
    direct_factors = [2**b for b,j in orbits for _ in range(2**j)]
    action = euler_subgroup_counts(action_factors, 4)
    direct = euler_subgroup_counts(direct_factors, 4)
    def extension(twisted):
        elements = [(x,z) for x in range(8) for z in range(4)]
        position = {v:i for i,v in enumerate(elements)}
        def multiply(x,y):
            n,z=elements[x]; m,w=elements[y]
            if twisted:
                for _ in range(z): m=alpha[m]
            return position[(mul(n,m),(z+w)%4)]
        return [[multiply(x,y) for y in range(32)] for x in range(32)]
    twisted_subgroups=subgroups(extension(True))
    product_subgroups=subgroups(extension(False))
    rows=[]
    for h in range(3):
        actual=sum(32//len(s)==2**h for s in twisted_subgroups)
        baseline=sum(32//len(s)==2**h for s in product_subgroups)
        weighted=sum(2**b * 2**j for b,j in orbits if b<=h and j<=h-b)
        omitted=-sum(2**(b+j) for b,j in orbits if b<=h and b+j>h)
        assert actual==action[2**h]==weighted
        assert baseline==direct[2**h]
        assert actual-baseline==omitted
        assert omitted % 2**(h+1)==0
        rows.append(dict(h=h,actual=actual,direct=baseline,difference=omitted,
                         quotient=omitted//2**(h+1)))
    trials=0
    # Synthetic orbit blocks test the exact boundary h=b+j and omitted terms.
    for p in [2,3,5]:
        for b in range(4):
            for j in range(4):
                for h in range(8):
                    left=p**(b+j) if b+j<=h else 0
                    right=p**(b+j) if b<=h else 0
                    if b<=h and b+j>h:
                        assert (left-right)%p**(h+1)==0
                    else: assert left==right
                    trials+=1
    return dict(status='PASS',kernel='D8',alpha='r->r,s->rs',
                orbit_pairs_b_j=orbits,grv_factor_degrees=action_factors,
                direct_factor_degrees=direct_factors,rows=rows,
                literal_twisted_subgroups=len(twisted_subgroups),
                literal_product_subgroups=len(product_subgroups),
                synthetic_orbit_block_trials=trials,
                scope='Independent finite comparison support; no universal proof gate or significance certificate.')

if __name__=='__main__':
    print(json.dumps(run(),indent=2,sort_keys=True))
