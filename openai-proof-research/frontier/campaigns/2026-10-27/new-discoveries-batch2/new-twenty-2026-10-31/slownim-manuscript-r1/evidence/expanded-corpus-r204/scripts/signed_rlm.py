"""Alexandersson-Kebede conjecture (arXiv:2105.08455 v3, Sec. 'A generalization'; MathDB 350721):
for 1<=k<=n, sum over pi in S_n with all cycle lengths >= k of (-1)^inv(pi) x_{RLMv(pi)} y_{EXCv(pi)} has
nonnegative coefficients.  RLMv = values pi_i with pi_i < pi_j for all j > i; EXCv = {pi(i): pi(i) > i}.
usage: signed_rlm.py n   (checks every k = 1..n; reports negative coefficients)"""
import sys, itertools, json
n = int(sys.argv[1])
coef = [dict() for _ in range(n + 1)]   # coef[k][(rlm,exc)] for min cycle length exactly k (accumulated later)
for p in itertools.permutations(range(1, n + 1)):
    # cycle lengths
    seen = [False] * (n + 1); mn = n
    for s in range(1, n + 1):
        if not seen[s]:
            L = 0; x = s
            while not seen[x]: seen[x] = True; x = p[x - 1]; L += 1
            mn = min(mn, L)
    inv = sum(1 for i in range(n) for j in range(i + 1, n) if p[i] > p[j])
    rlm = 0; cur = n + 1
    for i in range(n - 1, -1, -1):
        if p[i] < cur: rlm |= 1 << p[i]; cur = p[i]
    exc = 0
    for i in range(n):
        if p[i] > i + 1: exc |= 1 << p[i]
    key = (rlm, exc); d = coef[mn]
    d[key] = d.get(key, 0) + (-1 if inv % 2 else 1)
res = {}; acc = {}
for k in range(n, 0, -1):
    for key, v in coef[k].items(): acc[key] = acc.get(key, 0) + v
    neg = [(bin(r), bin(e), v) for (r, e), v in acc.items() if v < 0]
    res[k] = dict(terms=sum(1 for v in acc.values() if v), negative=len(neg), example=neg[:3])
print(json.dumps(dict(n=n, by_k=res)))
