"""Perturbation check of the core theorem at larger sizes: start from K_{s,t}; for every single and double edge flip
(and R random k-flips, k=3..8, seeded), verify that the PD family differs from K_{s,t}'s (via minimal PD / maximal
non-PD sets, exact).  usage: perturb.py s t R seed"""
import sys, itertools, random
sys.path.insert(0, 'scripts'); import pdlib
s, t, R, seed = map(int, sys.argv[1:5]); n = s + t
n_, K = pdlib.kst_adj(s, t)
E = list(itertools.combinations(range(n), 2))
def flip(adj, es):
    a = list(adj)
    for u, v in es: a[u] ^= 1 << v; a[v] ^= 1 << u
    return a
checked = same = 0; ex = []
def test(es):
    global checked, same
    a = flip(K, es); checked += 1
    ok, why = pdlib.same_family_as_kst(s, t, a)
    if ok:
        same += 1
        if len(ex) < 5: ex.append(es)
for e in E: test([e])
for e1, e2 in itertools.combinations(E, 2): test([e1, e2])
rng = random.Random(seed)
for _ in range(R):
    k = rng.randint(3, 8); test(rng.sample(E, k))
print('s t', s, t, 'checked', checked, 'same family as K', same, 'examples', ex)
