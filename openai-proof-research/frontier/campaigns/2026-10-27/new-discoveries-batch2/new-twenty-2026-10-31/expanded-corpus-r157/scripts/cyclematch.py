# Conjecture 30 (Aprile-Di Summa arXiv:2603.18754): cycle C_{2l}, edges 0..2l-1 colored with h colors,
# M0 = even edges, M1 = odd edges; for every integer k on segment [p_M0, p_M1] there is a matching M
# with |M| >= l-h+2, p_M <= k componentwise (then ||p_M-k||_1 = l-|M| <= h-2 automatically).
# Exhaustive over colorings in restricted-growth form (colour permutation symmetry), edge 0 fixed colour 0.
import sys, itertools, math, json, time
def matchings(l, smin):
    E = 2*l; res = []
    for s in range(smin, l+1):
        for c in itertools.combinations(range(E), s):
            ok = all(c[i+1]-c[i] >= 2 for i in range(s-1)) and not (s >= 2 and c[0] == 0 and c[-1] == E-1)
            if ok: res.append(c)
    return res
def rgs(n, h):
    # restricted growth strings of length n with values < h
    a = [0]*n
    def rec(i, mx):
        if i == n:
            yield tuple(a); return
        for v in range(min(mx+2, h)):
            a[i] = v
            yield from rec(i+1, max(mx, v))
    yield from rec(1, 0)
def check(col, l, h, Ms):
    p0 = [0]*h; p1 = [0]*h
    for i, c in enumerate(col):
        (p0 if i % 2 == 0 else p1)[c] += 1
    d = [p1[c]-p0[c] for c in range(h)]
    g = 0
    for x in d: g = math.gcd(g, abs(x))
    if g == 0: return None
    pts = []
    for j in range(g+1):
        pts.append(tuple(p0[c] + d[c]*j//g for c in range(h)))
    pvs = set()
    for M in Ms:
        v = [0]*h
        for e in M: v[col[e]] += 1
        pvs.add(tuple(v))
    for k in pts:
        if not any(all(v[c] <= k[c] for c in range(h)) for v in pvs):
            return k
    return None
l, h = int(sys.argv[1]), int(sys.argv[2])
t = time.time()
Ms = matchings(l, max(0, l-h+2))
cnt = 0; bad = []
for col in rgs(2*l, h):
    cnt += 1
    k = check(col, l, h, Ms)
    if k is not None:
        bad.append((col, k))
        if len(bad) >= 5: break
print(json.dumps({'l': l, 'h': h, 'colorings_checked': cnt, 'matchings': len(Ms), 'counterexamples': bad, 'sec': round(time.time()-t, 1)}))
