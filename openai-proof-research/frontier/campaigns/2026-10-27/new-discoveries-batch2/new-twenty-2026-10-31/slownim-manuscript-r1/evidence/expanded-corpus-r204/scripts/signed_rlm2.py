"""Sign pattern of the Alexandersson-Kebede signed sums (see signed_rlm.py): for each k, number of positive and
negative coefficients, with the positive / negative minority terms listed (values as sets).  usage: signed_rlm2.py n"""
import sys, itertools, json
n = int(sys.argv[1])
coef = [dict() for _ in range(n + 1)]; wit = {}
for p in itertools.permutations(range(1, n + 1)):
    seen = [False] * (n + 1); mn = n
    for s in range(1, n + 1):
        if not seen[s]:
            L = 0; x = s
            while not seen[x]: seen[x] = True; x = p[x - 1]; L += 1
            mn = min(mn, L)
    inv = sum(1 for i in range(n) for j in range(i + 1, n) if p[i] > p[j])
    rlm = []; cur = n + 1
    for i in range(n - 1, -1, -1):
        if p[i] < cur: rlm.append(p[i]); cur = p[i]
    exc = [p[i] for i in range(n) if p[i] > i + 1]
    key = (tuple(sorted(rlm)), tuple(sorted(exc)))
    coef[mn][key] = coef[mn].get(key, 0) + (-1 if inv % 2 else 1)
    wit.setdefault((mn, key), []).append(p)
out = {}; acc = {}; accw = {}
for k in range(n, 0, -1):
    for key, v in coef[k].items():
        acc[key] = acc.get(key, 0) + v
        accw.setdefault(key, []).extend(wit[(k, key)])
    pos = [(key, v) for key, v in acc.items() if v > 0]; neg = [(key, v) for key, v in acc.items() if v < 0]
    minority = pos if len(pos) <= len(neg) else neg
    out[k] = dict(pos=len(pos), neg=len(neg), minority=[dict(rlm=key[0], exc=key[1], coef=v, perms=accw[key][:6]) for key, v in minority[:4]])
print(json.dumps(dict(n=n, by_k=out)))
