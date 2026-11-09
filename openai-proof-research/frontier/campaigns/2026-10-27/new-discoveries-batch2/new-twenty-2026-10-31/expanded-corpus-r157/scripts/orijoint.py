# Joint local search over (underlying graph G = K_n - H with s*(G) >= 2, orientation) minimizing
# maxsigma(D) - ceil((n+s*)/2); seeded from Construction 1.7 of the source (tight examples). Diagnostic.
import sys, json, random, time, itertools
sys.path.insert(0, sys.argv[0].rsplit('/', 1)[0])
from oriexact import evaluate
n = int(sys.argv[1]); secs = float(sys.argv[2]); seed = int(sys.argv[3])
rnd = random.Random(seed); pairs = list(itertools.combinations(range(n), 2))
def sval(H):
    if not H: return n-2
    d = [n-1]*n
    for (a, b) in H: d[a] -= 1; d[b] -= 1
    return min(d[a]+d[b] for (a, b) in H) - n
def margin(H, O):
    s = sval(H)
    if s < 2: return None
    edges = [p for p in pairs if p not in H]
    T = -(-(n+s)//2)
    return evaluate(n, edges, [O[p] for p in edges]) - T, s, T
def seed_construction(k):
    c = (n + k) % 2; a = (n - k - c)//2
    A = list(range(a)); B = list(range(a, n))
    H = set(itertools.combinations(A, 2))
    if c == 1: H.add((A[0], B[0]))
    O = {}
    for (u, v) in pairs:
        if u in A and v in B: O[(u, v)] = 0      # B -> A : orientation flag 0 means v->u
        else: O[(u, v)] = rnd.randrange(2)
    return H, O
t = time.time(); best = (99,); found = None; restarts = 0
while time.time() - t < secs and found is None:
    restarts += 1
    k = rnd.randrange(2, max(3, n-3))
    H, O = seed_construction(k)
    m = margin(H, O)
    if m is None: continue
    cur = m
    for it in range(400):
        if time.time() - t > secs: break
        H2, O2 = set(H), dict(O)
        if rnd.random() < 0.7:
            p = rnd.choice(pairs); O2[p] ^= 1
        else:
            p = rnd.choice(pairs)
            if p in H2: H2.discard(p)
            else: H2.add(p)
        m2 = margin(H2, O2)
        if m2 is None: continue
        if m2[0] <= cur[0] or rnd.random() < 0.03:
            H, O, cur = H2, O2, m2
        if cur[0] < best[0]: best = cur
        if cur[0] < 0:
            found = {'H': sorted(H), 's': cur[1], 'T': cur[2], 'orientation': {f'{a}-{b}': O[(a, b)] for (a, b) in pairs if (a, b) not in H}}
            break
print(json.dumps({'n': n, 'seed': seed, 'restarts': restarts, 'best_margin_s_T': best, 'found': found}))
