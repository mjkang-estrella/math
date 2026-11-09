# Exact check of n+(L(G)) and n-(L(G)) via the integer characteristic polynomial of A(L(G)) and Descartes'
# rule of signs (exact since all roots are real for a real symmetric matrix).
import sys, json, sympy as sp, numpy as np
d = json.load(open(sys.argv[1])); E = [tuple(e) for e in d['edges']]; n = d['n']; m = len(E)
V = sorted({v for e in E for v in e}); assert len(V) == n
# connectivity of G (so L(G) connected as m>=1 and G connected without isolated vertices)
adj = {v: set() for v in V}
for u, v in E: adj[u].add(v); adj[v].add(u)
seen = {V[0]}; st = [V[0]]
while st:
    u = st.pop()
    for w in adj[u]:
        if w not in seen: seen.add(w); st.append(w)
assert len(seen) == n
L = sp.zeros(m, m)
for i in range(m):
    for j in range(i + 1, m):
        if set(E[i]) & set(E[j]): L[i, j] = L[j, i] = 1
x = sp.symbols('x'); p = sp.Poly(L.charpoly(x).as_expr(), x)
coeffs = p.all_coeffs()
def changes(cs):
    cs = [c for c in cs if c != 0]; return sum(1 for a, b in zip(cs, cs[1:]) if a * b < 0)
mult0 = 0
while p.eval(0) == 0: p = sp.Poly(sp.quo(p.as_expr(), x), x); mult0 += 1
npos = changes(p.all_coeffs()); nneg = changes(sp.Poly(p.as_expr().subs(x, -x), x).all_coeffs())
assert npos + nneg + mult0 == m
ev = np.linalg.eigvalsh(np.array(L.tolist(), dtype=float))
print(dict(n=n, m=m, degrees=sorted(len(adj[v]) for v in V), n_plus=npos, n_minus=nneg, nullity=mult0, conjecture_holds=npos <= nneg + 1, numeric_pos=int((ev > 1e-9).sum()), numeric_neg=int((ev < -1e-9).sum())))
print('edges', E)
