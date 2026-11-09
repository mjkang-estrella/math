# Sanity check (diagnostic only) of the two constructions in the proof of Conjecture 6.2
# (Dovgoshey-Cantor-Rovenska). Finite truncations with an explicit decreasing tail so all suffix maxima
# and limit distances are exactly computable.  Exact rationals.
import random, json
from fractions import Fraction as F
def path_max(adj, lab, u, v):
    # tree path max of labels including endpoints
    prev = {u: None}; st = [u]
    while st:
        x = st.pop()
        for y in adj[x]:
            if y not in prev: prev[y] = x; st.append(y)
    m = lab[v]; x = v
    while x != u: x = prev[x]; m = max(m, lab[x])
    return m
def test_i_to_ii(rnd, N):
    # ray labels l_1..l_N random (with zeros allowed but no two consecutive zeros), tail l_{N+k} = t/2^k tiny, t < all positive
    l = []
    for k in range(N):
        if l and l[-1] == 0: l.append(F(rnd.randint(1, 20), rnd.randint(1, 5)))
        else: l.append(F(0) if rnd.random() < 0.2 else F(rnd.randint(1, 20), rnd.randint(1, 5)))
    tail = F(1, 1000)  # l_{N+1}=tail, decreasing afterwards; all tail entries are records
    def M(n):  # sup_{k>=n} l_k, n 0-based within first N
        return max(max(l[n:]), tail)
    def dray(n, m):
        a, b = min(n, m), max(n, m); return max(l[a:b+1])
    # records among first N: k with l_k >= all later labels (including tail)
    rec = [k for k in range(N) if l[k] >= M(k) and l[k] > 0 and all(l[k] >= x for x in l[k+1:]) and l[k] >= tail]
    # legs: (r_{i-1}, r_i]; trailing part after last record attaches to the tail (first tail record) -> treat
    # tail vertex N (label tail) as next record, attached to p
    rec2 = rec + [N]; labs = l + [tail]
    adj = {('p',): set()}; lab = {('p',): F(0)}
    for v in range(N+1): adj[v] = set(); lab[v] = labs[v]
    prevr = -1
    for r in rec2:
        seg = list(range(prevr+1, r+1))
        for a, b in zip(seg, seg[1:]): adj[a].add(b); adj[b].add(a)
        adj[r].add(('p',)); adj[('p',)].add(r); prevr = r
    ok = True
    for n in range(N):
        for m in range(N):
            if n != m and path_max(adj, lab, n, m) != dray(n, m): ok = False
        if path_max(adj, lab, n, ('p',)) != M(n): ok = False
    return ok
def test_ii_to_i(rnd, legs):
    # center c label 0; legs random finite paths with random positive labels (zeros allowed if neighbours positive)
    adj = {'c': set()}; lab = {'c': F(0)}; hval = {}; groups = []
    for j in range(legs):
        r = rnd.randint(1, 5); prev = 'c'; pm = F(0); grp = None
        for a in range(r):
            v = (j, a)
            if prev == 'c' or lab[prev] == 0: x = F(rnd.randint(1, 30), rnd.randint(1, 4))
            else: x = F(0) if rnd.random() < 0.2 else F(rnd.randint(1, 30), rnd.randint(1, 4))
            adj[v] = {prev}; adj[prev].add(v); lab[v] = x; prev = v
            if x > pm:
                pm = x; grp = [v]; groups.append((pm, grp))
            else:
                grp.append(v)
            hval[v] = pm
    # ray order: groups by decreasing h; within group: members after record in leg order, then record
    groups.sort(key=lambda g: -g[0])
    order = []
    for h, g in groups: order += g[1:] + [g[0]]
    l = [lab[v] for v in order]
    ok = True
    for i in range(len(order)):
        if path_max(adj, lab, order[i], 'c') != hval[order[i]]: ok = False
        # limit distance in ray: max over suffix within block of current group... = h of its group
        for k in range(i+1, len(order)):
            if path_max(adj, lab, order[i], order[k]) != max(l[i:k+1]): ok = False
    # ray distance to the limit point (later groups' h are smaller) equals h of own group
    return ok
rnd = random.Random(2026)
r1 = all(test_i_to_ii(rnd, rnd.randint(3, 25)) for _ in range(300))
r2 = all(test_ii_to_i(rnd, rnd.randint(2, 12)) for _ in range(300))
print(json.dumps({'i_to_ii_constructions_ok': r1, 'ii_to_i_constructions_ok': r2, 'trials_each': 300}))
