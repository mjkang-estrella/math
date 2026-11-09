"""323795/323796/323799: exact evaluation of the monotone-triangle polynomial alpha(n;k_1..k_n) at arbitrary
integer points via Fischer's recursion with generalized summation (Fischer, Adv. Appl. Math. 2006):
  Sum^{(k_1..k_n)}_{(l)} A = Sum^{(k_1..k_{n-1})} Sum_{l_{n-1}=k_{n-1}+1}^{k_n} A + Sum^{(k_1..k_{n-2},k_{n-1}-1)} A(..,k_{n-1}),
  Sum_{x=a}^{b} f = usual if b>=a, 0 if b=a-1, -Sum_{x=b+1}^{a-1} f if b<a-1;  alpha(1;k)=1.
Every step preserves polynomiality, so this equals the polynomial alpha at all integer points.
usage: mono_alpha.py MODE NMAX   (MODE in check, c1, c2, c3)"""
import sys
from functools import lru_cache
sys.setrecursionlimit(100000)
MODE = sys.argv[1]; NMAX = int(sys.argv[2])

def gsum(a, b, f):
    if b >= a: return sum(f(x) for x in range(a, b + 1))
    if b == a - 1: return 0
    return -sum(f(x) for x in range(b + 1, a))

@lru_cache(maxsize=None)
def F(k, tail):
    if len(k) == 1: return alpha(tail)
    t1 = gsum(k[-2] + 1, k[-1], lambda x: F(k[:-1], (x,) + tail))
    t2 = F(k[:-2] + (k[-2] - 1,), (k[-2],) + tail)
    return t1 + t2

@lru_cache(maxsize=None)
def alpha(k):
    if len(k) <= 1: return 1
    return F(k, ())

def A(n): return alpha(tuple(range(1, n + 1)))

if MODE == 'check':
    print('ASM', [A(n) for n in range(1, NMAX + 1)])
    print('alpha(n;2,4,..,2n)', [alpha(tuple(range(2, 2 * n + 1, 2))) for n in range(1, NMAX + 1)])
    print('combRec alpha(2n;n,n,..,1,1)', [alpha(tuple(x for j in range(n, 0, -1) for x in (j, j))) for n in range(1, NMAX // 2 + 1)])
elif MODE == 'c1':  # 323795
    for n in range(1, NMAX + 1):
        lhs = alpha(tuple(range(2 * n + 1, 0, -1))); rhs = (-1) ** n * alpha(tuple(range(2, 2 * n + 1, 2)))
        print('n', n, lhs, rhs, 'OK' if lhs == rhs else 'FAIL', flush=True); F.cache_clear(); alpha.cache_clear()
elif MODE == 'c2':  # 323796
    for n in range(1, NMAX + 1):
        lhs = alpha(tuple(range(2, 2 * n + 1, 2))); rhs = alpha(tuple(x for j in range(n, 0, -1) for x in (2 * j, 2 * j)))
        print('n', n, lhs, rhs, 'OK' if lhs == rhs else 'FAIL', flush=True); F.cache_clear(); alpha.cache_clear()
elif MODE == 'c3':  # 323799, all i,k for fixed n = NMAX
    n = NMAX; An = A(n); bad = 0; cnt = 0
    for k in range(1, n + 1):
        for i in range(1, n - k + 2):
            arg = tuple(range(1, i)) + tuple(x for j in range(i + k - 1, i - 1, -1) for x in (j, j)) + tuple(range(i + k, n + 1))
            v = alpha(arg); cnt += 1
            if v != An: bad += 1; print('FAIL', n, k, i, v, An, flush=True)
    print('n', n, 'A_n', An, 'cases', cnt, 'failures', bad, 'cache', alpha.cache_info().currsize, F.cache_info().currsize)
