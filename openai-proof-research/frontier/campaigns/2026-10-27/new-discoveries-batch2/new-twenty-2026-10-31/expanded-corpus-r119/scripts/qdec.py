"""353177: q-decreasing words W_{q,n} (Baril-Kirgizov-Vajnovszki): every maximal factor 0^a 1^b with a>0 has a*q > b.
Brute force for small n (validation), and a transfer DP for the parity imbalance (#even weight - #odd weight)."""
import sys, itertools
from fractions import Fraction
def ok(w, q):
    i, n = 0, len(w)
    while i < n:
        if w[i] == 1: i += 1; continue
        a = 0
        while i < n and w[i] == 0: a += 1; i += 1
        b = 0
        while i < n and w[i] == 1: b += 1; i += 1
        if not (a * q > b): return False
    return True
def brute(q, n):
    W = [w for w in itertools.product((0, 1), repeat=n) if ok(w, q)]
    ev = sum(1 for w in W if sum(w) % 2 == 0); return len(W), ev, len(W) - ev
def dp(q, n):
    # states: (phase, a, b, parity) where phase 'L' = in leading 1s, 'Z' = in 0-run of length a, 'O' = in 1-run b after a zeros
    from collections import defaultdict
    S = defaultdict(int); S[('L', 0, 0, 0)] = 1
    for _ in range(n):
        T = defaultdict(int)
        for (ph, a, b, p), c in S.items():
            # append 0
            if ph == 'L': T[('Z', 1, 0, p)] += c
            elif ph == 'Z': T[('Z', a + 1, 0, p)] += c
            else: T[('Z', 1, 0, p)] += c  # previous block 0^a1^b closed, already valid
            # append 1
            if ph == 'L': T[('L', 0, 0, p ^ 1)] += c
            else:
                nb = b + 1 if ph == 'O' else 1
                if a * q > nb: T[('O', a, nb, p ^ 1)] += c
        S = T
    ev = sum(c for (ph, a, b, p), c in S.items() if p == 0); od = sum(c for (ph, a, b, p), c in S.items() if p == 1)
    return ev + od, ev, od
if __name__ == '__main__':
    for q in range(1, 6):
        for n in range(0, 13):
            assert brute(q, n) == dp(q, n), (q, n)
    print('brute == dp for q<=5, n<=12')
    bad = []
    for q in range(1, 13):
        row = []
        for n in range(0, 41):
            t, e, o = dp(q, n); row.append(e - o)
            if abs(e - o) > 1: bad.append((q, n, t, e, o))
        print('q=%d imbalance n=0..40:' % q, row)
    print('violations of |even-odd|<=1:', bad[:20], len(bad))
