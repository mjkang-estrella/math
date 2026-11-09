#!/usr/bin/env python3
"""
Verification artifacts for lane pi-discrete-discovery-r2, FINDINGS.md section 1.

Establishes, with exact integer arithmetic:
  (A) [B_n]_q = prod_{i=1}^n [2i]_q                       (type-B Poincare polynomial)
  (B) P_{n,k}(q) = [n choose k]_q prod_{j=k+1}^n (1+q^j)
      == sum_{w in B_n, Des_B(w) subseteq {k}} q^{len_B(w)}        (n <= 8, all k)
  (C) sum_{w: Des_B(w) subseteq {k}} q^{len_B(w)}
      == F(B_n,q) / (F(B_k,q) F(S_{n-k},q))                        (n <= 8, all k)
      (Stanley 1980 sec.2 pts (4),(5): rank GF of the parabolic quotient W^J,
       J = S \\ {s_k}; W_J = B_k x S_{n-k})
  (D) P_{n,k} is symmetric and unimodal for n <= 40, all k (no counterexample).

Conventions (Bjorner-Brenti):
  len_B(w) = #{i<j: w_i > w_j} + #{i<j: w_i + w_j < 0} + #neg(w),
with the first term in the signed total order -n < ... < -1 < 1 < ... < n;
  Des_B(w) = {0} if w_1 < 0, plus {i in [1,n-1]: w_i > w_{i+1}} (signed order).

Together with Stanley 1980, Theorem 3.1 ("W^J is rank-symmetric, rank-unimodal,
and has property S" for every Weyl group and every J subseteq S) this proves
ABR Conjecture 5.3 (MathDB 379218) as a corollary of a known theorem.
"""
from itertools import permutations, product

def key(v):  # signed total order
    return (0, -v) if v < 0 else (1, v)

def lenB(w):
    n = len(w); L = 0
    for i in range(n):
        for j in range(i + 1, n):
            if key(w[i]) > key(w[j]): L += 1
            if w[i] + w[j] < 0: L += 1
    return L + sum(1 for x in w if x < 0)

def desB(w):
    n = len(w); D = set()
    if w[0] < 0: D.add(0)
    for i in range(1, n):
        if key(w[i - 1]) > key(w[i]): D.add(i)
    return D

def B_n(n):
    for p in permutations(range(1, n + 1)):
        for s in product([1, -1], repeat=n):
            yield tuple(s[i] * p[i] for i in range(n))

def pmul(a, b):
    r = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b): r[i + j] += x * y
    return r

def iseq(a, b):
    a = list(a); b = list(b)
    while a and a[-1] == 0: a.pop()
    while b and b[-1] == 0: b.pop()
    return a == b

def qint(m): return [1] * m

def factq(m):
    f = [1]
    for i in range(1, m + 1): f = pmul(f, qint(i))
    return f

def FB(k):  # F(B_k, q) = [2][4]...[2k]
    p = [1]
    for i in range(1, k + 1): p = pmul(p, qint(2 * i))
    return p

_gcache = {}
def gauss(n, k):  # [n choose k]_q via [n k] = [n-1 k] + q^{n-k} [n-1 k-1], memoized
    if k < 0 or k > n: return [0]
    if k == 0: return [1]
    if (n, k) in _gcache: return _gcache[(n, k)]
    a = gauss(n - 1, k); b = gauss(n - 1, k - 1)
    r = [0] * max(len(a), len(b) + n - k)
    for i, c in enumerate(a): r[i] += c
    for i, c in enumerate(b): r[i + n - k] += c
    _gcache[(n, k)] = r
    return r

def P_nk(n, k):
    p = gauss(n, k)
    for j in range(k + 1, n + 1): p = pmul(p, [1] + [0] * (j - 1) + [1])
    return p

def divexact(num, den):
    num = num[:]; dq = len(den) - 1
    qu = [0] * (len(num) - dq)
    for i in range(len(qu) - 1, -1, -1):
        c = num[i + dq]; qu[i] = c
        for j in range(dq + 1): num[i + j] -= c * den[j]
    assert not any(num), "division not exact"
    return qu

def is_sym(p): return all(p[i] == p[len(p) - 1 - i] for i in range(len(p)))

def is_unim(p):
    n = len(p); i = 0
    while i + 1 < n and p[i + 1] >= p[i]: i += 1
    while i + 1 < n and p[i + 1] <= p[i]: i += 1
    return i == n - 1

def main():
    # (A) + (B) + (C)
    for n in range(1, 9):
        B = list(B_n(n))
        dist = [0] * (n * n + 1)
        for w in B: dist[lenB(w)] += 1
        assert iseq(dist, FB(n)), ("A failed", n)
        for k in range(n):
            gf = [0] * (n * n + 2)
            for w in B:
                if desB(w) <= {k}: gf[lenB(w)] += 1
            while gf and gf[-1] == 0: gf.pop()
            assert iseq(gf, P_nk(n, k)), ("B failed", n, k)
            q = divexact(FB(n), pmul(FB(k), factq(n - k)))
            assert iseq(gf, q), ("C failed", n, k)
    print("(A) [B_n]=prod[2i]; (B) P_{n,k}=descent-class GF; "
          "(C) GF=F(B_n)/F(B_k)F(S_{n-k}): all verified for n<=8, all k")

    # (D) no violation up to n = 40
    NMAX = 40
    for n in range(1, NMAX + 1):
        for k in range(n):
            p = P_nk(n, k)
            assert is_sym(p) and is_unim(p), ("D failed", n, k)
    print(f"(D) P_{{n,k}} symmetric and unimodal for all n <= {NMAX}, all k: no violations")

if __name__ == "__main__":
    main()
