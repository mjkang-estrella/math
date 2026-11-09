# Check exact identity: dd({p+2}; p+q+3)/(p+q+3)! = sum_{s<=p,t<=q} c_s c_t/(s+t+3)! a_{p-s} a_{q-t},
# a_L = dd(empty;L)/L!, c = coefficients of 1/(1+z+z^2) = 1,-1,0,1,-1,0,...
import sys
from fractions import Fraction
from math import factorial
sys.path.insert(0, sys.argv[1])
from dd344302 import dd_single
def dd_empty(n):
    # permutations with no double descent via the same DP machinery: use i = 0 sentinel (never hit)
    return dd_single(n, -1) if n >= 1 else 1
c = lambda s: (1, -1, 0)[s % 3]
N = int(sys.argv[2])
a = [Fraction(dd_empty(L), factorial(L)) for L in range(N)]
ok = True
for n in range(3, N):
    for i in range(2, n):
        p, q = i-2, n-i-1
        D = sum(Fraction(c(s)*c(t), factorial(s+t+3))*a[p-s]*a[q-t] for s in range(p+1) for t in range(q+1))
        if D*factorial(n) != dd_single(n, i): ok = False; print('FAIL', n, i)
print('identity verified for all 3<=n<', N, ':', ok, '; a_0..a_6*L! =', [dd_empty(L) for L in range(7)])
