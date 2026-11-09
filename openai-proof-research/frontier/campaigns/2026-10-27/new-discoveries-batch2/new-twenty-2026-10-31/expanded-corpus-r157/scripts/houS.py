# Hou arXiv:1303.0568 Conjecture 7.3: S(a) mod 3 pattern. Exact rational computation.
import sys
from fractions import Fraction as F
from math import comb
def binq(x, k):  # generalized binomial, x rational, k>=0 integer
    if k < 0: return F(0)
    r = F(1)
    for i in range(k): r = r * (x - i) / (i + 1)
    return r
def S(a):
    e = 1 if a % 2 == 0 else 0        # 2{(a-1)/2}
    tot = F(0)
    for j in range(0, (a-1)//2 + 1) if a >= 1 else []:
        top = 2*j + e
        for i in range(0, top + 1):
            tot += (-2)**j * comb(a, i) * comb(a + top - i, top - i) * (binq(F(a//2 + j), top) + binq(F(a//2) + F(1, 2) + j, top))
    return tot
def mod3(x):
    assert x.denominator % 3 != 0
    return (x.numerator * pow(x.denominator, -1, 3)) % 3
def pred(a):
    if a == 0: return 0
    k = 0
    while 3**(2*k+1) <= a:
        if a <= 3**(2*k+2) - 1: return 0
        k += 1
    return 2
A = int(sys.argv[1]); bad = []
vals = []
for a in range(A+1):
    r = mod3(S(a)); vals.append(r)
    if r != pred(a): bad.append(a)
print('a<=', A, 'mismatches:', bad[:30], len(bad))
print('first values mod 3:', vals[:40])
