# Agent E2: t = 15 brute force by DIGIT STRINGS (no smoothness assumption needed to enumerate):
# every n with digit multiset {3,5} + 1s, length 2..LMAX, tested for 7-smoothness by trial division by 2,3,5,7.
import sys, json
from math import gcd
LMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 300
P = 1
for p in (11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97): P *= p
def smooth(n):
    for p in (2, 3, 5, 7):
        while n % p == 0: n //= p
    return n == 1
res = []; cnt = 0
for L in range(2, LMAX + 1):
    rep = (10 ** L - 1) // 9
    for p5 in range(L):
        b5 = 4 * 10 ** p5
        for p3 in range(L):
            if p3 == p5: continue
            n = rep + b5 + 2 * 10 ** p3
            cnt += 1
            if gcd(n % P, P) != 1: continue
            if smooth(n): res.append(n)
print('strings scanned', cnt, 'to length', LMAX)
print('t=15 members (len>=2):', res)
json.dump(res, open('i3_brute15_%d.json' % LMAX, 'w'))
