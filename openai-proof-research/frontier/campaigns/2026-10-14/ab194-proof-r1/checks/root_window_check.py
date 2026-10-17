#!/usr/bin/env python3
"""MIT License. Myeongjin Kang (author of record); written by the AB194 proof reviewer.
Exact rational checks of the combinatorial ingredients of the AB194 abstract
estimate. Not a proof: it checks finitely many (h, i, s) only.
Checks, for 1<=h<=HMAX and 0<=i<=h:
 (A) roots rho_1>...>rho_{h-1} of H_i' lie in -(j+1)<rho_j<-(j-1) (Rolle pattern);
 (B) the weighted node identity sum_k (-1)^k b_k (H_i(0)-H_i(-k))/h = -b_i i!(h-i)!/h
     on the alternating-rank-zero hyperplane (coefficient-wise, exact);
 (C) for listed s, the nearest-integer rounding r_j of s*rho_j is strictly
     decreasing, satisfies the wider windows, and the layer degrees satisfy
     v(l-ks)<=k for l>=0 and v(l-ks)>=k-1 for l<0 on a window of l;
 (D) exact layer sums s^-h sum_{l=-ks}^{-1} prod(l-r_a) versus the integral
     (H_i(0)-H_i(-k))/h, reporting s*max|error|;
 (E) whether the source's narrower windows -(j+1)s<r_j<-js hold (expected to
     fail for 0<i), showing the widening is used, not cosmetic.
"""
from fractions import Fraction as Fr
from math import factorial, comb
import sys
HMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 10

def polymul(a, b):
    out = [0]*(len(a)+len(b)-1)
    for x, u in enumerate(a):
        for y, v in enumerate(b):
            out[x+y] += u*v
    return out
def H(h, i):  # coefficients, low->high, of prod_{0<=j<=h, j!=i} (x+j)
    p = [1]
    for j in range(h+1):
        if j != i:
            p = polymul(p, [j, 1])
    return p
def ev(p, x):
    s = 0
    for c in reversed(p):
        s = s*x + c
    return s
def deriv(p):
    return [k*p[k] for k in range(1, len(p))]
def bisect(p, lo, hi, bits=90):
    lo, hi = Fr(lo), Fr(hi)
    flo = ev(p, lo)
    if flo == 0: return lo, lo
    if ev(p, hi) == 0: return hi, hi
    assert (flo > 0) != (ev(p, hi) > 0)
    for _ in range(bits):
        m = (lo+hi)/2; fm = ev(p, m)
        if fm == 0: return m, m
        if (fm > 0) == (flo > 0): lo, flo = m, fm
        else: hi = m
    return lo, hi

ok = True
report = []
for h in range(1, HMAX+1):
    for i in range(h+1):
        Hp = H(h, i); dP = deriv(Hp)
        roots_H = sorted([-j for j in range(h+1) if j != i], reverse=True)
        rho = []
        for j in range(h-1):
            a, b = roots_H[j+1], roots_H[j]
            lo, hi = bisect(dP, a, b)
            rho.append((lo, hi))
        # (A)
        for j, (lo, hi) in enumerate(rho, start=1):
            if not (-(j+1) < lo and hi < -(j-1)):
                ok = False; report.append(f"A FAIL h={h} i={i} j={j}")
        if len(rho) != h-1: ok = False
        margin = min([min(lo+(j+1), -(j-1)-hi) for j, (lo, hi) in enumerate(rho, 1)] or [Fr(1)])
        gap = min([rho[j][0]-rho[j+1][1] for j in range(len(rho)-1)] or [Fr(1)])
        # (B) coefficient vector c_k; must equal alpha*(-1)^k - i!(h-i)!/h*delta_{ki}
        c = [Fr((-1)**k*(ev(Hp, 0)-ev(Hp, -k)), h) for k in range(h+1)]
        alpha = Fr(ev(Hp, 0), h)
        for k in range(h+1):
            want = alpha*(-1)**k - (Fr(factorial(i)*factorial(h-i), h) if k == i else 0)
            if c[k] != want:
                ok = False; report.append(f"B FAIL h={h} i={i} k={k}")
        assert Fr(factorial(i)*factorial(h-i), h)/factorial(h-1) == Fr(1, comb(h, i))
        # threshold s0 guaranteeing windows and distinctness after |r-s rho|<=1/2+tiny
        s0 = max(int(Fr(3, 2)/margin)+1, int(Fr(3)/gap)+1, 1) if h > 1 else 1
        maxerr = Fr(0); narrow_fail = False; per_s = []
        for s in [s0, 4*s0, 16*s0, 64*s0]:
            serr = Fr(0)
            mid = [(lo+hi)/2 for lo, hi in rho]
            r = [int((s*m + Fr(1, 2)).__floor__()) for m in mid]
            # (C)
            if any(r[j] <= r[j+1] for j in range(len(r)-1)):
                ok = False; report.append(f"C distinct FAIL h={h} i={i} s={s}")
            for j, rj in enumerate(r, 1):
                if not (-(j+1)*s < rj < -(j-1)*s):
                    ok = False; report.append(f"C window FAIL h={h} i={i} s={s} j={j}")
                if not (-(j+1)*s < rj < -j*s):
                    narrow_fail = True
            for k in range(h+1):
                for l in range(-(h+2)*s, (h+2)*s+1):
                    a = l-k*s
                    if a in r: continue
                    v = sum(1 for rj in r if rj > a)
                    if l >= 0 and v > k: ok = False; report.append(f"C pos FAIL h={h} i={i} s={s} k={k} l={l}")
                    if l < 0 and v < k-1: ok = False; report.append(f"C neg FAIL h={h} i={i} s={s} k={k} l={l}")
            # (D)
            for k in range(h+1):
                tot = 0
                for l in range(-k*s, 0):
                    pr = 1
                    for ra in r: pr *= (l-ra)
                    tot += pr
                err = abs(Fr(tot, s**h) - Fr(ev(Hp, 0)-ev(Hp, -k), h))
                maxerr = max(maxerr, err*s); serr = max(serr, err*s)
            per_s.append(f"{s}:{float(serr):.2f}")
        report.append(f"h={h} i={i} margin={float(margin):.4f} s0={s0} s*maxerr={float(maxerr):.3f} narrow_windows_hold={not narrow_fail} s*err_by_s=[{' '.join(per_s)}]")
print("\n".join(report))
print("ALL_CHECKS_OK" if ok else "SOME_CHECK_FAILED")
