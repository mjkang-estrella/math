"""347991: Wahl (arXiv:2009.08181v1) Lemma 5.8 array K(n,k,l) and Conjecture 5.9:
  K(n-2,k,l)/K(n,k,l) >= max( K(n-2,k+1,l)/K(n,k+1,l), K(n-2,k,l+2)/K(n,k,l+2) )
  for n >= 3, 2k+l < n-2, 2k+l = n (mod 2)  [authors: verified n <= 20].
K(0,0,0)=1; K(n,k,l)=(2k+l)!/(2^k k! l!) if 2k+l=n; else (2k+l<n, same parity)
K(n,k,l)=K(n-1,k,l-1)+(l+1)(K(n-1,k,l+1)+K(n-1,k-1,l+1))+(k+1)K(n-1,k+1,l-1).
Also checks the 'in particular' maximum statement. Exact integer cross-multiplication.
Usage: wahl_K.py NMAX"""
import sys
from math import factorial
NMAX = int(sys.argv[1])
def boundary(k, l): return factorial(2 * k + l) // (2 ** k * factorial(k) * factorial(l))
levels = {0: {(0, 0): 1}}
def get(n, k, l):
    if k < 0 or l < 0: return 0
    return levels[n].get((k, l), 0)
viol = 0; maxviol = 0; checked = 0
for n in range(1, NMAX + 1):
    cur = {}
    for k in range(0, n // 2 + 1):
        for l in range(0, n - 2 * k + 1):
            if (2 * k + l - n) % 2: continue
            if 2 * k + l == n: cur[(k, l)] = boundary(k, l)
            else:
                cur[(k, l)] = (get(n - 1, k, l - 1) + (l + 1) * (get(n - 1, k, l + 1) + get(n - 1, k - 1, l + 1))
                               + (k + 1) * get(n - 1, k + 1, l - 1))
    levels[n] = cur
    if n >= 3:
        # check conjecture at level n
        best = None
        for (k, l) in cur:
            if 2 * k + l < n - 2:
                checked += 1
                a, b = get(n - 2, k, l), cur[(k, l)]
                for (k2, l2) in ((k + 1, l), (k, l + 2)):
                    c, d = get(n - 2, k2, l2), cur[(k2, l2)]
                    if a * d < c * b:
                        viol += 1
                        if viol <= 10: print('VIOLATION n', n, 'k,l', (k, l), 'vs', (k2, l2), flush=True)
            if 2 * k + l < n and (k, l) in levels[n - 2]:
                r = (get(n - 2, k, l), cur[(k, l)])
                if best is None or r[0] * best[1][1] > best[1][0] * r[1]: best = ((k, l), r)
        delta = n % 2
        if best is not None:
            a, b = best[1]; c, d = get(n - 2, 0, delta), cur[(0, delta)]
            if a * d != c * b:
                print('MAX STATEMENT FAILS n', n, 'argmax', best[0], flush=True)
    if n - 3 in levels: del levels[n - 3]
print('NMAX', NMAX, 'inequalities checked', checked, 'violations', viol)
