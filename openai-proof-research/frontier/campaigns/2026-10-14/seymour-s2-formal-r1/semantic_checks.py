#!/usr/bin/env python3
"""Copyright 2026 Myeongjin Kang. MIT. Bounded semantic support, not S2 proof."""
from itertools import product
import json


def require(statement, label):
    if not statement:
        raise AssertionError(label)


def main():
    counts = {'boundary': 0, 'families': 0, 'complement': 0, 'pruning': 0}
    for hits, avoids, returns in product([False, True], repeat=3):
        a, q, b = int(hits), int(hits and avoids), int(not hits and returns)
        for dD in range(-9, 0):
            dH = dD - q - b + a
            require(dH <= 0 and (not avoids or dH <= -1), 'boundary case')
            counts['boundary'] += 1
    for n in range(1, 15):
        m = n*n+2
        f = [n-m]*(m-1)+[n]*(n*m-(m-1))
        require(len(f) == n*m and sum(f) == -m, 'aggregate tight instance')
        counts['families'] += 1
        old = n*n+1
        old_f = [n-old]*(old-1)+[n]*(n*old-(old-1))
        require(sum(old_f) == 0, 'threshold counterexample')
        weak = [n-m]*(m-2)+[n]*(n*m-(m-2))
        require(sum(weak) == 0, 'missing anchor counterexample')
    U = frozenset(range(3))
    sets = [frozenset(i for i in U if mask & (1 << i)) for mask in range(8)]
    for JP, JQ in product(sets, repeat=2):
        if JP & JQ:
            continue
        d = len(U-(JP|JQ))
        for P, Q, JJP, JJQ in product(sets, repeat=4):
            if not (len(P)+len(JJP)<2*len(JP) and len(Q)+len(JJQ)<2*len(JQ)):
                continue
            require(len(P)+len(Q)+2*d < len(U-JJQ)+len(U-JJP), 'finite complement')
            counts['complement'] += 1
    for R, C, P, Q in product(sets, repeat=4):
        if not (P <= R and Q <= C):
            continue
        for M, d, dp in product(range(7), range(4), range(4)):
            if M+2*d < len(R)+len(C) and len(R-P)+len(C-Q) <= d+dp:
                require(M+d < len(P)+len(Q)+dp, 'finite pruning')
                counts['pruning'] += 1
    # Explicit failure examples: weakened strictness and overlapping old images.
    require(3 < 6 and not (3+3 < 3+3), 'disjointness control')
    require(6+2*2 == 5+5 and 1+1 <= 2+0 and 4+4+0 == 6+2, 'strict gain control')
    print(json.dumps({'status':'PASS bounded semantic checks', 'counts':counts,
                      'full_S2_theorem_proved_by_enumeration':False}, sort_keys=True))

if __name__ == '__main__':
    main()
