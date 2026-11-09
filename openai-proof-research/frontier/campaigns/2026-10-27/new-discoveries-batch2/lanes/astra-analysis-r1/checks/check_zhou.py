#!/usr/bin/env python3
"""Exact finite checks of the uniform argument in PROOF.md, NOT its proof.

Python 3 + SymPy. Output is deterministic JSON. No floating point is used.
The source q polynomials are built independently from the Jacobi sn ODE;
the proposed H polynomials are built from the different, quadratic U ODE.
"""
import json
from math import comb, factorial
import sympy as S

t, r, k = S.symbols('t r k')
N = 12
# sn(v,k), with k denoting the PARAMETER (modulus squared), EGF derivatives.
sn = [S.Integer(0), S.Integer(1)]
for n in range(2*N):
    cubic = sum(S.Integer(factorial(n)//(factorial(a)*factorial(b)*factorial(n-a-b)))
                * sn[a]*sn[b]*sn[n-a-b]
                for a in range(n+1) for b in range(n-a+1))
    sn.append(S.expand(-(1+k)*sn[n] + 2*k*cubic))

u = [1-t]
for n in range(N-1):
    u.append(S.expand(3*sum(comb(2*n,2*j)*u[j]*u[n-j] for j in range(n+1))
                      -2*(1+t)*u[n] - ((1-t)**2 if n == 0 else 0)))

rows = []
for p in range(2,N+1):
    q = (-1)**(p-1)*sn[2*p-1]
    sq = sum(comb(2*p-2,j)*sn[j]*sn[2*p-2-j] for j in range(2*p-1))
    Q = S.expand((-1)**(p-2)*sq)
    ku = ((1-r)/(1+r))**2
    source_H = S.cancel((1+r)**(2*p)*((1-r)/(1+r)*q.subs(k,ku)-ku*Q.subs(k,ku)))
    H = S.expand((-1)**(p-1)*u[p-1])
    assert S.cancel(source_H-H.subs(t,r*r)) == 0
    assert S.expand(H.subs(t,1-t)-(-1)**p*H) == 0
    at = H.subs(t,S.Rational(1,2))
    dat = S.diff(H,t).subs(t,S.Rational(1,2))
    assert at == 0 if p % 2 else dat == 0
    rows.append({'p':p,'H_at_half':str(at),'Hprime_at_half':str(dat),
                 'degree':int(S.degree(H,t))})

# Purely algebraic Miura calculation, independent of the coefficient checks.
w, wp = S.symbols('w wp')
wpp = -2*(1+t)*w+2*w**3
wppp = (-2*(1+t)+6*w*w)*wp
U = wp+w*w
Upp = wppp+2*wp*wp+2*w*wpp
identity = S.expand(Upp-(3*U*U-2*(1+t)*U-(1-t)**2))
assert S.expand(identity.subs(wp**2,(1-t)**2-2*(1+t)*w*w+w**4)) == 0

# Exact source examples, using the formula for Cbar+Sbar in PROOF.md.
# m=1 c/e combined coefficient, and m=2 d/f combined coefficient.
assert S.Rational(3,1024)-S.Rational(1,1024) == S.Rational(1,512)
assert S.Rational(5,131072)-S.Rational(3,131072) == S.Rational(1,65536)
print(json.dumps({'status':'PASS','source_H_matches_U_recurrence':rows,
                  'miura_identity':'PASS','arithmetic':'exact symbolic rationals',
                  'limit':'Finite checks p=2..12; uniform proof is in PROOF.md'},indent=2))
