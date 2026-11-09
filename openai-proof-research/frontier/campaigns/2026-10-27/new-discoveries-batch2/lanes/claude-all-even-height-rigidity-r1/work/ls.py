"""Bounded incremental local search for line-all-even subsets of a finite
lattice universe U (dimension 2 control or 3 target).  Support evidence only.

For each primitive direction d realised by U we precompute the partition of U
into lines parallel to d.  Parity of n_S(d) = #occupied fibres is maintained
incrementally.  Objective = #odd directions (+ big if |S| odd).
Usage: ls.py dim side seed iters [restarts]
"""
import sys, random, itertools, json, time
from math import gcd

dim, side, seed, iters = map(int, sys.argv[1:5])
restarts = int(sys.argv[5]) if len(sys.argv) > 5 else 1
rng = random.Random(seed)
U = list(itertools.product(range(side), repeat=dim))
idx = {p: i for i, p in enumerate(U)}
N = len(U)


def prim(v):
    g = 0
    for x in v:
        g = gcd(g, abs(x))
    v = tuple(x // g for x in v)
    for x in v:
        if x:
            return v if x > 0 else tuple(-y for y in v)


dirs = sorted({prim(tuple(b - a for a, b in zip(p, q))) for p, q in itertools.combinations(U, 2)})
# fibre id of point i in direction k: canonical = minimal point on its line inside U
fib = []
for d in dirs:
    f = [0] * N
    for i, p in enumerate(U):
        q = p
        while True:
            r = tuple(a - b for a, b in zip(q, d))
            if r in idx:
                q = r
            else:
                break
        f[i] = idx[q]
    fib.append(f)
D = len(dirs)


def rank(S):
    import sympy
    if not S:
        return -1
    M = sympy.Matrix([[x - y for x, y in zip(U[i], U[S[0]])] for i in S])
    return M.rank()


def run(seed2):
    r = random.Random(seed2)
    inS = [r.random() < 0.5 for _ in range(N)]
    cnt = [dict() for _ in range(D)]
    par = [0] * D
    for k in range(D):
        for i in range(N):
            if inS[i]:
                c = cnt[k]
                c[fib[k][i]] = c.get(fib[k][i], 0) + 1
        par[k] = len(cnt[k]) % 2
    size = sum(inS)

    def delta(i):
        # change in #odd directions if toggling i
        ch = 0
        for k in range(D):
            c = cnt[k].get(fib[k][i], 0)
            if (inS[i] and c == 1) or ((not inS[i]) and c == 0):
                ch += -1 if par[k] else 1
        return ch

    def toggle(i):
        nonlocal size
        for k in range(D):
            f = fib[k][i]
            c = cnt[k].get(f, 0)
            if inS[i]:
                if c == 1:
                    del cnt[k][f]
                    par[k] ^= 1
                else:
                    cnt[k][f] = c - 1
            else:
                if c == 0:
                    par[k] ^= 1
                cnt[k][f] = c + 1
        inS[i] = not inS[i]
        size += 1 if inS[i] else -1

    best = None
    found = []
    T = 1.0
    bestodd = 10**9
    for it in range(iters):
        odd = sum(par) + (0 if size % 2 == 0 else 3)
        bestodd = min(bestodd, odd)
        if odd == 0 and size > 0:
            S = [i for i in range(N) if inS[i]]
            rk = rank(S)
            key = tuple(S)
            found.append((rk, [U[i] for i in S]))
            if rk == dim:
                return found, True, bestodd
            # planar/low-dim solution: kick
            for _ in range(3):
                toggle(r.randrange(N))
            continue
        i = r.randrange(N)
        dl = delta(i) + ((-3 if size % 2 else 3))
        if dl <= 0 or r.random() < pow(2.718, -dl / T):
            toggle(i)
        T = max(0.15, 1.0 - it / iters)
    return found, False, bestodd


out = {'dim': dim, 'side': side, 'dirs': D, 'points': N, 'runs': []}
t0 = time.time()
for rr in range(restarts):
    found, ok, bo = run(seed * 1000 + rr)
    ranks = {}
    for rk, S in found:
        ranks[rk] = ranks.get(rk, 0) + 1
    rec = {'restart': rr, 'zero_hits_by_affine_dim': ranks, 'spanning_found': ok, 'best_odd': bo}
    if found:
        rec['example'] = found[-1][1]
    out['runs'].append(rec)
    if ok:
        break
out['seconds'] = time.time() - t0
print(json.dumps(out))
