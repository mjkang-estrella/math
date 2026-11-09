#!/usr/bin/env python3
"""
verify23.py -- finite verification for the theorem  g(S(2,3,z)) = z mod 2  (z >= 14).

Everything here is computed from the spider-state recursion (Prop. 6.1 of the paper) and the run
values of Theorem 4.3.  Nothing else from the paper is used.

Notation (as in the paper):
  status s in {'n','i','o','f'};  far end phi in {'*','I','O'}  ('I' = IN = towards the centre,
  'O' = OUT = away from the centre);  a leg is a pair (h, phi) with h >= 1 unmarked edges.
  Gamma(s, L) = Grundy value of the centre component, L = multiset of attached legs (sorted tuple).

What is verified (exhaustively):
  (V1) Table B: for every short configuration kappa=(s,K) reachable from (n,{(2,*),(3,*)}) by moves on
       the two short legs, every phi in {I,O} and every 1 <= r <= RMAX,
          Gamma(s, K + {(r,phi)}) == closed form of Table B.
  (V2) W := Gamma(i, {(2,*),(3,*)}) = Gamma(o, {(2,*),(3,*)}) = 3.
  (V3) The structural constants used in the proof of Lemma B:
         every value of a type-P family is <= 7, every threshold r0 <= 8,
         every detached run created by a short-leg move has value <= 2.
  (V4) (sanity, not needed for the proof) g(S(2,3,z)) for 1 <= z <= ZMAX, equal to z mod 2
       exactly for z >= 14 in that range.
Usage:  python3 verify23.py [RMAX] [ZMAX]      (defaults 100, 160)
"""
import sys
from functools import lru_cache

sys.setrecursionlimit(100000)
RMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 100
ZMAX = int(sys.argv[2]) if len(sys.argv) > 2 else 160


# ---------------------------------------------------------------- runs (Theorem 4.3)
def A(k): return k % 2
def B(k): return k
def C(k): return k % 2
def D(k): return 1 if (k >= 2 and k % 2 == 0) else 0


def rho(k, delta, phi):
    """detached run of k edges, near end blocked in direction delta (I/O), far end phi"""
    if k == 0:
        return 0
    if phi == '*':
        return B(k)
    return C(k) if phi == delta else D(k)


def rho_free(k, phi):
    """run of k edges with free near end and far end phi"""
    if k == 0:
        return 0
    return A(k) if phi == '*' else B(k)


def dot(s, delta):
    """status of the centre after an arc at it pointing IN (delta='I') or OUT (delta='O')"""
    if delta == 'I':
        return {'n': 'i', 'i': 'i', 'o': 'f', 'f': 'f'}[s]
    return {'n': 'o', 'o': 'o', 'i': 'f', 'f': 'f'}[s]


def mex(S):
    g = 0
    while g in S:
        g += 1
    return g


@lru_cache(maxsize=None)
def Gamma(s, L):
    L = tuple(sorted(L))
    if len(L) == 0:                                   # (N3)
        return 0
    if s == 'f':                                      # (N1)
        v = 0
        for (h, phi) in L:
            v ^= rho_free(h, phi)
        return v
    if s in ('i', 'o') and len(L) == 1:               # (N2)
        (h, phi), = L
        return rho(h, 'O' if s == 'i' else 'I', phi)
    opts = set()                                      # Proposition 6.1
    for idx, (h, phi) in enumerate(L):
        rest = L[:idx] + L[idx + 1:]
        for j in range(1, h + 1):
            for delta in ('I', 'O'):
                if j == h and phi != '*' and delta != phi:
                    continue
                det = rho(h - j, delta, phi)
                if j >= 2:
                    val = Gamma(s, tuple(sorted(rest + ((j - 1, delta),))))
                else:
                    val = Gamma(dot(s, delta), rest)
                opts.add(det ^ val)
    return mex(opts)


# ---------------------------------------------------------------- Table B
# closed forms for phi = 'I' and 'O'; entries: (initial values for r=1..r0-1, eventual rule)
# eventual rules: ('par', a, b) -> a if r even else b ;  ('lin', c) -> r + c ; ('xor1',) -> r XOR 1
def P(even, odd): return ('par', even, odd)


EV = P(0, 1)     # r mod 2
OD = P(1, 0)     # (r+1) mod 2
TABLE = {
    # n-configurations  (K as a sorted tuple of legs)
    ('n', ((2, '*'), (3, '*'))): {'I': ([2, 6, 7, 5, 4], ('lin', 2)), 'O': ([2, 6, 7, 5, 4], ('lin', 2))},
    ('n', ((1, 'I'), (2, '*'))): {'I': ([2], EV), 'O': ([], OD)},
    ('n', ((1, 'O'), (2, '*'))): {'I': ([], OD), 'O': ([2], EV)},
    ('n', ((2, '*'), (2, 'I'))): {'I': ([], OD), 'O': ([], EV)},
    ('n', ((2, '*'), (2, 'O'))): {'I': ([], EV), 'O': ([], OD)},
    ('n', ((1, 'I'), (3, '*'))): {'I': ([5, 4, 5], P(3, 2)), 'O': ([1], P(2, 3))},
    ('n', ((1, 'O'), (3, '*'))): {'I': ([1], P(2, 3)), 'O': ([5, 4, 5], P(3, 2))},
    ('n', ((1, 'I'), (1, 'I'))): {'I': ([], OD), 'O': ([], EV)},
    ('n', ((1, 'O'), (1, 'O'))): {'I': ([], EV), 'O': ([], OD)},
    ('n', ((1, 'I'), (1, 'O'))): {'I': ([], ('lin', 0)), 'O': ([], ('lin', 0))},
    ('n', ((1, 'I'), (2, 'I'))): {'I': ([], EV), 'O': ([2], OD)},
    ('n', ((1, 'I'), (2, 'O'))): {'I': ([], OD), 'O': ([2], EV)},
    ('n', ((1, 'O'), (2, 'I'))): {'I': ([2], EV), 'O': ([], OD)},
    ('n', ((1, 'O'), (2, 'O'))): {'I': ([2], OD), 'O': ([], EV)},
    # i-configurations
    ('i', ((2, '*'),)): {'I': ([3], OD), 'O': ([], EV)},
    ('i', ((1, 'I'),)): {'I': ([], EV), 'O': ([], OD)},
    ('i', ((1, 'O'),)): {'I': ([], ('xor1',)), 'O': ([], ('xor1',))},
    ('i', ((3, '*'),)): {'I': ([], P(5, 4)), 'O': ([0, 4, 5, 7, 6, 7, 6], P(4, 5))},
    ('i', ((2, 'I'),)): {'I': ([], OD), 'O': ([3], EV)},
    ('i', ((2, 'O'),)): {'I': ([], EV), 'O': ([3], OD)},
}
FL = {'I': 'O', 'O': 'I', '*': '*'}
# o-configurations by reversal symmetry (Lemma R):  V_{(o,K)}^phi = V_{(i,Kbar)}^{phibar}
for (s, K), row in list(TABLE.items()):
    if s == 'i':
        Kb = tuple(sorted((h, FL[p]) for (h, p) in K))
        TABLE[('o', Kb)] = {'I': row['O'], 'O': row['I']}


def closed(kappa, phi, r):
    init, rule = TABLE[kappa][phi]
    if r <= len(init):
        return init[r - 1]
    if rule[0] == 'par':
        return rule[1] if r % 2 == 0 else rule[2]
    if rule[0] == 'lin':
        return r + rule[1]
    if rule[0] == 'xor1':
        return r ^ 1
    raise ValueError


def reachable():
    """short configurations reachable from (n,{(2,*),(3,*)}) by short-leg moves, long leg attached"""
    start = ('n', ((2, '*'), (3, '*')))
    seen, stack = {start}, [start]
    while stack:
        s, K = stack.pop()
        for idx, (h, phi) in enumerate(K):
            rest = K[:idx] + K[idx + 1:]
            for j in range(1, h + 1):
                for delta in ('I', 'O'):
                    if j == h and phi != '*' and delta != phi:
                        continue
                    if j >= 2:
                        nk = (s, tuple(sorted(rest + ((j - 1, delta),))))
                    else:
                        s2 = dot(s, delta)
                        if s2 == 'f' or len(rest) == 0:
                            continue          # long leg alone / centre free: cases (a2),(a3)
                        nk = (s2, rest)
                    if nk not in seen:
                        seen.add(nk)
                        stack.append(nk)
    return seen


def main():
    ok = True
    confs = reachable()
    assert confs == set(TABLE.keys()), (sorted(confs ^ set(TABLE.keys())))
    print('reachable short configurations:', len(confs))
    # (V1)
    nchk = 0
    for r in range(1, RMAX + 1):
        for kappa in sorted(confs):
            s, K = kappa
            for phi in ('I', 'O'):
                v = Gamma(s, tuple(sorted(K + ((r, phi),))))
                if v != closed(kappa, phi, r):
                    ok = False
                    print('MISMATCH', kappa, phi, r, v, closed(kappa, phi, r))
                nchk += 1
    print('(V1) Table B checked for %d (kappa,phi,r) with r <= %d: %s' % (nchk, RMAX, 'OK' if ok else 'FAIL'))
    # (V2)
    W1, W2 = Gamma('i', ((2, '*'), (3, '*'))), Gamma('o', ((2, '*'), (3, '*')))
    print('(V2) Gamma(i,{2*,3*}) =', W1, ' Gamma(o,{2*,3*}) =', W2)
    ok &= (W1 == 3 and W2 == 3)
    # (V3)
    typeL = {k for k in TABLE if TABLE[k]['I'][1][0] != 'par'}
    maxP = max(max(TABLE[k][p][0] + [TABLE[k][p][1][1], TABLE[k][p][1][2]]) for k in TABLE if k not in typeL for p in 'IO')
    maxr0 = max(len(TABLE[k][p][0]) + 1 for k in TABLE for p in 'IO')
    maxdet = 0
    for (s, K) in confs:
        for (h, phi) in K:
            for j in range(1, h + 1):
                for delta in ('I', 'O'):
                    if j == h and phi != '*' and delta != phi:
                        continue
                    maxdet = max(maxdet, rho(h - j, delta, phi))
    print('(V3) type-L configurations:', sorted(typeL))
    print('     max value of type-P families = %d, max threshold r0 = %d, max short-leg det = %d' % (maxP, maxr0, maxdet))
    ok &= (maxP <= 7 and maxr0 <= 8 and maxdet <= 2)
    # (V4)
    g = [Gamma('n', tuple(sorted(((2, '*'), (3, '*'), (z, '*'))))) for z in range(1, ZMAX + 1)]
    good = [z for z in range(1, ZMAX + 1) if g[z - 1] == z % 2]
    first_bad_from_top = max(z for z in range(1, ZMAX + 1) if g[z - 1] != z % 2)
    print('(V4) g(S(2,3,z)), z=1..30:', g[:30])
    print('     largest z <= %d with g != z mod 2: %d' % (ZMAX, first_bad_from_top))
    ok &= (first_bad_from_top == 13)
    print('ALL CHECKS PASSED' if ok else 'SOME CHECK FAILED')
    return 0 if ok else 1


if __name__ == '__main__':
    sys.exit(main())
