#!/usr/bin/env python3
"""Mod-p (p = 2^31-1) version of checks D/E for larger n (needs numpy).
Full rank mod p implies full rank over Q; orthogonality mod p is a necessary
condition for the exact identity (exact version is in kn_minus_e_checks.py)."""
import sys, random
import numpy as np
from math import comb
sys.path.insert(0, '.')
from kn_minus_e_checks import (twopage_J, rect_J, relabel, Tset, params, target, symbasis)
p = 2147483647

def inv(a): return pow(int(a) % p, p-2, p)
def frmod(x): return x.numerator % p * inv(x.denominator) % p

def rank_kernel(M):
    """row-reduce M (np int64 mod p); return rank and pivot info"""
    M = M.copy() % p; r = 0; rows, cols = M.shape; piv = []
    for c in range(cols):
        nz = np.nonzero(M[r:, c])[0]
        if len(nz) == 0: continue
        i = r + nz[0]
        M[[r, i]] = M[[i, r]]
        M[r] = M[r] * inv(M[r, c]) % p
        f = M[:, c].copy(); f[r] = 0
        M = (M - (f[:, None] * M[r][None, :]) % p) % p
        piv.append(c); r += 1
        if r == rows: break
    return r, M[:r], piv

def kernel(rowsM, ncol):
    if rowsM.shape[0] == 0: return np.eye(ncol, dtype=np.int64)
    r, R, piv = rank_kernel(rowsM)
    free = [c for c in range(ncol) if c not in piv]
    K = np.zeros((len(free), ncol), dtype=np.int64)
    for j, fc in enumerate(free):
        K[j, fc] = 1
        for i, pc in enumerate(piv): K[j, pc] = (-R[i, fc]) % p
    return K

def matmul(A, B):
    out = np.zeros((A.shape[0], B.shape[1]), dtype=np.int64)
    for k in range(A.shape[1]):
        out = (out + (A[:, k:k+1] * B[k:k+1, :]) % p) % p
    return out

def symvals(d, x, u):
    return [(pow(x, a, p)*pow(u, b, p) + (pow(x, b, p)*pow(u, a, p) if a != b else 0)) % p for (a, b) in symbasis(d)]

def run(n, name, E, J):
    t = [3*i*i + i + 1 for i in range(n)]
    w = []
    for i in range(n):
        d = 1
        for j in range(n):
            if j != i: d = d * (t[i]-t[j]) % p
        w.append(inv(d))
    al, be = params(n)
    T = Tset(J)
    def evalmat(a1, a2):
        rows = []
        for (e, f) in T:
            s1 = symvals(a1, t[e[0]], t[e[1]]); s2 = symvals(a2, t[f[0]], t[f[1]])
            rows.append([x*y % p for x in s1 for y in s2])
        return np.array(rows, dtype=np.int64)
    B1, B2 = symbasis(al), symbasis(be)
    # S_a(al,be): P(t0,t1,y,v)=0
    ra = []
    s01 = symvals(al, t[0], t[1])
    for q0 in range(len(B2)):
        ra.append([s01[pi] if qi == q0 else 0 for pi in range(len(B1)) for qi in range(len(B2))])
    Ka = kernel(np.array(ra, dtype=np.int64), len(B1)*len(B2))
    # S_b(be,al): Q(x,u,t0,t1)=0 ; basis order (p in sym(be)) x (q in sym(al))
    rb = []
    s01b = symvals(al, t[0], t[1])
    for p0 in range(len(B2)):
        rb.append([s01b[qi] if pi == p0 else 0 for pi in range(len(B2)) for qi in range(len(B1))])
    Kb = kernel(np.array(rb, dtype=np.int64), len(B1)*len(B2))
    EA = matmul(evalmat(al, be), Ka.T)   # |T| x dimSa
    EB = matmul(evalmat(be, al), Kb.T)
    coef = []
    for (e, f) in T:
        x, u, y, v = t[e[0]], t[e[1]], t[f[0]], t[f[1]]
        Dl = (x-u)*(y-v)*(x-y)*(x-v)*(u-y)*(u-v) % p
        c = frmod(J[(e, f)]) * w[e[0]] % p * w[e[1]] % p * w[f[0]] % p * w[f[1]] % p * Dl % p
        assert c != 0
        coef.append(c)
    coef = np.array(coef, dtype=np.int64)
    G = matmul(((EA * coef[:, None]) % p).T, EB)
    orth = not G.any()
    rkA = rank_kernel(EA.T)[0]; rkB = rank_kernel(EB.T)[0]
    dim = Ka.shape[0]
    ok = orth and rkA == dim and rkB == Kb.shape[0] and dim == target(n) and len(T) >= 2*dim
    print(f"n={n} {name}: |T|/2={len(T)//2} target={target(n)} dimSa={dim} rankA={rkA} rankB={rkB} orth={orth} -> {'ok' if ok else 'FAIL'}", flush=True)
    return ok

if __name__ == '__main__':
    ns = [int(a) for a in sys.argv[1:]] or [13, 14, 15, 16]
    allok = True
    for n in ns:
        me = (0, (n-1)//2)
        E, J, nc, page = twopage_J(n, removed=(me,))
        E2, J2 = relabel(n, E, J, me)
        allok &= run(n, 'twopage-minus-max', E2, J2)
        rnd = random.Random(1000+n)
        pts = [(rnd.random(), rnd.random()) for _ in range(n)]
        E, J = rect_J(pts, removed=((2, n-1),))
        E2, J2 = relabel(n, E, J, (2, n-1))
        allok &= run(n, 'rect', E2, J2)
    print('ALL OK' if allok else 'SOME FAIL')
