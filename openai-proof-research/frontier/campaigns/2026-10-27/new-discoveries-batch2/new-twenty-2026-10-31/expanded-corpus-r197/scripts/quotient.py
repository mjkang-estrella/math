"""Explicit quotient dissections of annuli (Banaian-Chen, arXiv:2106.06679, Def. 5.3) and positivity
of their frieze patterns (Conjecture 9.5, MathDB 350973).

Model of a SKELETAL dissection of the annulus A_{n,m} (all arcs bridging, Def. 3.x): a cyclic
sequence of r >= 1 bridging arcs; region t lies between arc t and arc t+1 and contains a_t >= 0
consecutive outer boundary edges and b_t >= 0 inner boundary edges, a_t + b_t >= 1,
sum a_t = n, sum b_t = m.  Region t is a (a_t + b_t + 2)-gon.  Arc t joins outer vertex o_t to
inner vertex i_t with o_{t+1} = o_t + a_t.  The outer vertices of region t are o_t, ..., o_t + a_t.
We require a_t < n so no region has two corners at one outer vertex.

Quotient (Def. 5.3): identify pairs of regions of the same size sharing an outer vertex, never two
regions sharing an edge (cyclically adjacent regions share an arc; with r = 2 both arcs).
Regions here always have an inner vertex, so the 'all vertices on the outer boundary' ban never
applies.  Quiddity: m_{v} = sum over identification classes incident to v of lambda_size.

Writes JSON with every negative quotient frieze found. Float diagnostic (exact check separately).
usage: quotient.py nmax mmax rmax pairs(1|2) rows
"""
import sys, math, itertools, json
NMAX, MMAX, RMAX, PAIRS, ROWS = map(int, sys.argv[1:6])
lam = lambda p: 2 * math.cos(math.pi / p)

def compositions(total, parts, minpart=0):
    if parts == 1:
        if total >= minpart:
            yield (total,)
        return
    for x in range(minpart, total + 1):
        for rest in compositions(total - x, parts - 1, minpart):
            yield (x,) + rest

def frieze_negative(q):
    n = len(q)
    prev = [0.0] * n; cur = [1.0] * n
    for k in range(2, ROWS + 2):
        nxt = [q[(i + k - 1) % n] * cur[i] - prev[i] for i in range(n)]
        if all(abs(x) < 1e-9 for x in nxt):
            return ('finite', k)
        if any(x < 1e-9 for x in nxt):
            return ('nonpositive', k, [round(x, 6) for x in nxt])
        prev, cur = cur, nxt
    return None

def trace(q):
    a, b, c, d = 1.0, 0.0, 0.0, 1.0
    for x in q:
        a, b, c, d = a * x + b * 1, -a, c * x + d, -c
    return a + d

found = []; tested = 0; seen = set()
for n in range(1, NMAX + 1):
    for m in range(1, MMAX + 1):
        for r in range(1, RMAX + 1):
            for A in compositions(n, r):
                for B in compositions(m, r):
                    if any(a + b == 0 for a, b in zip(A, B)) or any(a >= n for a in A):
                        continue
                    sizes = [a + b + 2 for a, b in zip(A, B)]
                    o = [0]
                    for a in A[:-1]:
                        o.append(o[-1] + a)
                    verts = [set((o[t] + s) % n for s in range(A[t] + 1)) for t in range(r)]
                    # candidate pairs
                    cand = []
                    for t, u in itertools.combinations(range(r), 2):
                        if sizes[t] != sizes[u]:
                            continue
                        if r == 2 or (u - t) % r in (1, r - 1):
                            continue
                        if not (verts[t] & verts[u]):
                            continue
                        cand.append((t, u))
                    for k in range(1, PAIRS + 1):
                        for chosen in itertools.combinations(cand, k):
                            cls = list(range(r))
                            def f(x):
                                while cls[x] != x: x = cls[x]
                                return x
                            for t, u in chosen:
                                cls[f(u)] = f(t)
                            q = []
                            for v in range(n):
                                inc = {f(t) for t in range(r) if v in verts[t]}
                                q.append(sum(lam(sizes[c]) for c in inc))
                            key = (n, tuple(round(x, 9) for x in q))
                            canon = min(tuple(round(x, 9) for x in (q[i:] + q[:i])) for i in range(n))
                            tested += 1
                            res = frieze_negative(q)
                            if res and res[0] == 'nonpositive':
                                if canon in seen: continue
                                seen.add(canon)
                                found.append(dict(n=n, m=m, r=r, a=A, b=B, sizes=sizes, identified=chosen,
                                                  quiddity=[round(x, 6) for x in q], trace=round(trace(q), 6), result=res))
print(json.dumps(dict(params=dict(nmax=NMAX, mmax=MMAX, rmax=RMAX, pairs=PAIRS, rows=ROWS),
                      tested=tested, negative_classes=len(found), examples=found[:40])))
