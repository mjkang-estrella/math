"""346999/347000: rank-selected homology of subword order as a polynomial in x = n-1
(x^j <-> j-th tensor power of S_(n-1,1)), via Sundaram (5.1)-(5.4):
  alpha(S) = prod_r sum_{i=0}^{s_r - s_{r-1}} C(s_r, i) x^i   (s_0 = 0 convention for the first factor:
             first factor sum_{i=0}^{s_1} C(s_1,i) x^i = (1+x)^{s_1})
  beta(T)  = sum_{S subset T} (-1)^{|T|-|S|} alpha(S).
Checks every nonempty T subset [1,K] for negative coefficients.
Usage: subword_beta.py K"""
import sys, itertools
from math import comb
K = int(sys.argv[1])
def mul(a, b):
    r = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b):
                r[i + j] += x * y
    return r
def add(a, b, s=1):
    n = max(len(a), len(b)); r = [0] * n
    for i, x in enumerate(a): r[i] += x
    for i, y in enumerate(b): r[i] += s * y
    return r
def factor(prev, cur):
    return [comb(cur, i) for i in range(cur - prev + 1)]
# beta via recursion over subsets: alpha(S) computed by DP on sorted tuple
from functools import lru_cache
@lru_cache(None)
def alpha(S):
    if not S: return (1,)
    a = list(alpha(S[:-1])); prev = S[-2] if len(S) > 1 else 0
    return tuple(mul(a, factor(prev, S[-1])))
neg = []; count = 0; minc = None
for m in range(1, K + 1):
    for rest in itertools.product([0, 1], repeat=m - 1):
        T = tuple([i + 1 for i in range(m - 1) if rest[i]] + [m])
        b = [0]
        for r in range(len(T) + 1):
            for S in itertools.combinations(T, r):
                b = add(b, list(alpha(S)), (-1) ** (len(T) - r))
        count += 1
        while len(b) > 1 and b[-1] == 0: b.pop()
        assert b[0] == 0
        if any(c < 0 for c in b):
            neg.append((T, b))
print('K', K, 'sets checked', count, 'with negative coefficient', len(neg))
for T, b in neg[:25]:
    print(T, b)
for T in [(1,), (2,), (1, 2), (1, 3), (2, 3), (1, 2, 3), (1, 3, 5)]:
    if max(T) <= K:
        b = [0]
        for r in range(len(T) + 1):
            for S in itertools.combinations(T, r):
                b = add(b, list(alpha(S)), (-1) ** (len(T) - r))
        print('example', T, b)
