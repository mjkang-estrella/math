"""Check that the cyclic bridging-arc model of quotient.py reproduces the source's Example 5.4:
a dissection of an annulus with n = 2 outer vertices with quiddity (2+2sqrt2, 3sqrt2) whose
identification of two squares gives (2+sqrt2, 2sqrt2).  Lists all model dissections (n=2, m<=4,
r<=6) with that base quiddity and the quiddities after each allowed single identification."""
import itertools, math, json
lam = lambda p: 2 * math.cos(math.pi / p)
def comps(t, k):
    if k == 1: yield (t,); return
    for x in range(t + 1):
        for r in comps(t - x, k - 1): yield (x,) + r
target = sorted([round(2 + 2 * math.sqrt(2), 6), round(3 * math.sqrt(2), 6)])
hits = []
n = 2
for m in range(1, 7):
    for r in range(1, 7):
        for A in comps(n, r):
            for B in comps(m, r):
                if any(a + b == 0 for a, b in zip(A, B)) or any(a >= n for a in A): continue
                sizes = [a + b + 2 for a, b in zip(A, B)]
                o = [0]
                for a in A[:-1]: o.append(o[-1] + a)
                verts = [set((o[t] + s) % n for s in range(A[t] + 1)) for t in range(r)]
                base = [round(sum(lam(sizes[t]) for t in range(r) if v in verts[t]), 6) for v in range(n)]
                if sorted(base) != target: continue
                after = []
                for t, u in itertools.combinations(range(r), 2):
                    if sizes[t] != sizes[u] or r == 2 or (u - t) % r in (1, r - 1) or not (verts[t] & verts[u]): continue
                    q = []
                    for v in range(n):
                        inc = {min(t, x) if x in (t, u) else x for x in range(r) if v in verts[x]}
                        q.append(round(sum(lam(sizes[c]) for c in inc), 6))
                    after.append(dict(identified=(t, u), quiddity=q))
                hits.append(dict(m=m, r=r, a=A, b=B, sizes=sizes, base=base, after=after))
print(json.dumps(dict(target_base=target, expected_after=sorted([round(2 + math.sqrt(2), 6), round(2 * math.sqrt(2), 6)]), hits=hits[:10], count=len(hits))))
