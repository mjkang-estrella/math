#!/usr/bin/env python3
"""FINAL REVIEWER independent mathematical check (Gate 2).

Written from scratch by the final reviewer; not the parent's check_exact.py.
Verifies, independently of the Lean proof:
  A. Actual Euler numbers E_n from the literal EGF sec(t)+tan(t) (high precision),
     a_n = E_n/n!, and the source sign (-1)^(n-1)(a_n a_{n+j+k} - a_{n+j} a_{n+k}) > 0
     over a large grid. Finite evidence only, NOT proof.
  B. Source normalization: a_n = 2(2/pi)^(n+1) * (beta(n+1) if n even else lambda(n+1)).
  C. Error contraction c_{n+2} <= c_n/3, 0 < c_n < 1, for the ACTUAL series:
     even n: c_n = sum_k [(4k+3)^-(n+1) - (4k+5)^-(n+1)]
     odd  n: c_n = sum_k (2k+3)^-(n+1)
     n = 0 : c_0 = 1 - pi/4.
  D. corrected a_n: a_n = 2(2/pi)^(n+1) * (1 + (-1)^(n+1) c_n) for all n.
  E. Abstract criterion: both L-X>0 and L+X>0 in all four parity cases
     (randomized falsification attempt under the exact hypotheses).
  F. Paired-power polynomial identity (exact, sympy).
  G. sec z + tan z = cot(pi/4 - z/2) numerically.
"""
import mpmath as mp
import sympy as sp
import random

mp.mp.dps = 50

# --- A. actual Euler numbers from the literal EGF ---
# Exact rational Taylor coefficients of sec(t)+tan(t) via sympy series.
N = 130
t = sp.Symbol('t')
ser = sp.series(1/sp.cos(t) + sp.tan(t), t, 0, N).removeO()
coeffs = []  # cs[n] = coefficient of t^n (exact Rational) = E_n/n!
for n in range(N):
    c = ser.coeff(t, n)
    coeffs.append(sp.Rational(c) if c != 0 else sp.Rational(0))
Euler = [coeffs[n]*sp.factorial(n) for n in range(N)]   # E_n exact integers
expected = [1,1,1,2,5,16,61,272,1385,7936,50521]
assert all(Euler[i] == expected[i] for i in range(len(expected))), "E_n mismatch vs A000111"
print("A1. exact E_n from literal sec+tan series match A000111:", expected, "... OK")
a = [mp.mpf(str(coeffs[n])) for n in range(N)]          # a_n = E_n/n! exact -> mp
# cross-check numerically against the transcendental EGF
tv = mp.mpf('0.3')
assert abs(sum(a[n]*tv**n for n in range(60)) - (1/mp.cos(tv)+mp.tan(tv))) < mp.mpf('1e-30')
print("A2. exact series equals sec+tan at t=0.3 to <1e-30  OK")

fails = 0
checked = 0
for n in range(0, 60):
    for j in range(1, 8):
        for k in range(1, 8):
            val = (-1)**(n-1)*(a[n]*a[n+j+k] - a[n+j]*a[n+k])
            checked += 1
            if not (val > 0):
                fails += 1
                print("FAIL", n, j, k, val)
print(f"A3. source sign checked on {checked} (n,j,k) triples with actual a_n; failures: {fails}")

# --- B. normalization from source (3.3)/(3.4) ---
def beta(s):  # Dirichlet beta
    return mp.nsum(lambda k: (-1)**k/(2*k+1)**s, [0, mp.inf])
def lam(s):
    return mp.nsum(lambda k: 1/(2*k+1)**s, [0, mp.inf])
okb = True
for n in range(0, 40):
    b = beta(n+1) if n % 2 == 0 else lam(n+1)
    if abs(a[n] - 2*(2/mp.pi)**(n+1)*b) > mp.mpf('1e-30'):
        okb = False; print("B FAIL", n, a[n], 2*(2/mp.pi)**(n+1)*b)
print("B. a_n = 2(2/pi)^(n+1)(beta/lambda) matches actual a_n for n<40:", okb)

# --- C/D. error sequence and corrected identity ---
def c_actual(n):
    if n == 0:
        return 1 - mp.pi/4
    if n % 2 == 0:
        return mp.nsum(lambda k: (4*k+3)**(-(n+1)) - (4*k+5)**(-(n+1)), [0, mp.inf])
    return mp.nsum(lambda k: (2*k+3)**(-(n+1)), [0, mp.inf])

okc = okd = True
for n in range(0, 60):
    cn = c_actual(n)
    if not (0 < cn < 1): okc = False; print("C range FAIL", n, cn)
    if n+2 <= 100 and c_actual(n+2) > cn/3: okc = False; print("C contraction FAIL", n)
    corr = 1 + (-1)**(n+1)*cn
    if abs(a[n] - 2*(2/mp.pi)**(n+1)*corr) > mp.mpf('1e-25'):
        okd = False; print("D FAIL", n, a[n], 2*(2/mp.pi)**(n+1)*corr)
print("C. 0<c_n<1 and c_{n+2}<=c_n/3 for actual series (n<60):", okc)
print("D. a_n = 2(2/pi)^(n+1)(1+(-1)^(n+1)c_n) for all n<60:", okd)

# --- E. abstract criterion falsification attempt ---
random.seed(7)
def criterion_ok(a_, b, c, d):
    # hypotheses: 0<a,b,c,d<1 ; b,c <= a/3 (even shifts), etc. handled per case
    return None
bad = 0
for _ in range(200000):
    case = random.choice(['oo', 'ee', 'oe'])
    if case == 'oo':   # j,k both odd: only 0<a,b,c,d<1
        a_, b, c, d = (random.random() for _ in range(4))
        L = a_+b+c+d; X = a_*d-b*c
    elif case == 'ee':  # both even: b,c <= a/3, a<1
        a_ = random.random(); b = a_/3*random.random(); c = a_/3*random.random()
        d = random.random()
        L = a_+d-b-c; X = a_*d-b*c
    else:              # mixed: c <= a/3, d <= b/3
        a_ = random.random(); b = random.random()
        c = a_/3*random.random(); d = b/3*random.random()
        L = a_+b-c-d; X = a_*d-b*c
    if L-X <= 0 or L+X <= 0:
        bad += 1; print("E FAIL", case, a_, b, c, d)
print("E. abstract criterion: 200000 random instances, counterexamples:", bad)

# --- F. paired-power identity, exact ---
A, B, s = sp.symbols('A B s', positive=True)
s = sp.Symbol('s', integer=True, positive=True)
expr = sp.expand((A**2+A*B+B**2)*(A**s-B**s) - (A**(s+2)-B**(s+2)) - A*B*(A+B)*(A**s-1 - (B**s-1)))
# sympy can't do symbolic s; verify for s=1..8 exactly
okf = all(sp.simplify((A**2+A*B+B**2)*(A**m-B**m) - (A**(m+2)-B**(m+2))
                      - A*B*(A+B)*(A**(m-1)-B**(m-1))) == 0 for m in range(1, 9))
print("F. (A^2+AB+B^2)(A^s-B^s)-(A^{s+2}-B^{s+2}) = AB(A+B)(A^{s-1}-B^{s-1}) for s=1..8:", okf)

# --- G. cot identity ---
z = mp.mpc('0.2', '0.4')
lhs = 1/mp.cos(z) + mp.tan(z)
rhs = 1/mp.tan(mp.pi/4 - z/2)
print("G. sec z + tan z = cot(pi/4 - z/2): diff =", abs(lhs-rhs))
