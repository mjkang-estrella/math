"""Coefficient of x_R y_E (R = {1, n-4, n-2, n-1}, E = [n] minus R, n >= 8) in the Alexandersson-Kebede signed sum
sum_{pi in S_n, min cycle >= k} (-1)^inv(pi) x_RLMv(pi) y_EXCv(pi), for each k, by a pruned DFS over permutations
(value v in E must sit at a position < v; value v in R at a position >= v; RLMv checked at the leaves).
Also reports (-1)^(n-1) * coefficient (the AJC version-of-record normalisation).  usage: signed_rlm_family.py n"""
import sys, json
n = int(sys.argv[1])
R = {1, n - 4, n - 2, n - 1}; E = set(range(1, n + 1)) - R
rows = []
perm = [0] * (n + 1); used = [False] * (n + 1)
def leaf():
    p = perm[1:]
    rlm = set(); cur = n + 1
    for i in range(n - 1, -1, -1):
        if p[i] < cur: rlm.add(p[i]); cur = p[i]
    if rlm != R: return
    seen = [False] * (n + 1); cyc = []
    for s in range(1, n + 1):
        if not seen[s]:
            L = 0; x = s
            while not seen[x]: seen[x] = True; x = p[x - 1]; L += 1
            cyc.append(L)
    inv = sum(1 for i in range(n) for j in range(i + 1, n) if p[i] > p[j])
    rows.append((''.join(map(str, p)) if n < 10 else '.'.join(map(str, p)), sorted(cyc, reverse=True), -1 if inv % 2 else 1))
def dfs(pos):
    if pos > n: leaf(); return
    for v in range(1, n + 1):
        if used[v]: continue
        if v in E and not pos < v: continue
        if v in R and not pos >= v: continue
        used[v] = True; perm[pos] = v; dfs(pos + 1); used[v] = False
dfs(1)
coef = {k: sum(s for _, c, s in rows if min(c) >= k) for k in range(1, n + 1)}
print(json.dumps(dict(n=n, R=sorted(R), E=sorted(E), contributors=len(rows), coefficient_by_k=coef,
                      normalised_by_k={k: (-1) ** (n - 1) * v for k, v in coef.items()},
                      rows=[dict(perm=a, cycle_type=c, sign=s) for a, c, s in rows])))
