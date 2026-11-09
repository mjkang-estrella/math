# Simulated-annealing search for counterexamples to Bang-Jensen-Gutin-Li
# Conjecture 6.1 (MathDB 330821): strong digraph D on n vertices (no loops,
# no parallel arcs; 2-cycles allowed) such that d(x)+d(y) >= 2n-1 for every
# non-adjacent pair {x,y} that is dominating (common out-neighbour) or
# dominated (common in-neighbour), yet D is not Hamiltonian.
# Usage: python3 -I bjgl_sa.py n seed seconds outfile
import sys, random, time, json

n = int(sys.argv[1]); seed = int(sys.argv[2]); secs = float(sys.argv[3]); outf = sys.argv[4]
MODE = sys.argv[5] if len(sys.argv) > 5 else 'both'
MODE_SEED = sys.argv[6] if len(sys.argv) > 6 else 'random'  # 'both' = Conj 6.1/1.3 (MathDB 330821); 'dominated' = Conj 6.2/1.4 (calibration only)
rng = random.Random(seed)
FULL = (1 << n) - 1
T = 2 * n - 1

def hamiltonian(out):
    # dp[mask] = set of end vertices v of a path from 0 covering exactly mask
    dp = [0] * (1 << n)
    dp[1] = 1
    for mask in range(1, 1 << n, 2):
        e = dp[mask]
        if not e:
            continue
        v = 0
        while e:
            if e & 1:
                nxt = out[v] & ~mask
                while nxt:
                    b = nxt & -nxt
                    dp[mask | b] |= b
                    nxt ^= b
            e >>= 1; v += 1
    e = dp[FULL]; v = 0
    while e:
        if (e & 1) and (out[v] & 1):
            return True
        e >>= 1; v += 1
    return False

def strong(out, inn):
    for adj in (out, inn):
        seen = 1; stack = [0]
        while stack:
            v = stack.pop(); nb = adj[v] & ~seen
            seen |= nb
            while nb:
                b = nb & -nb; stack.append(b.bit_length() - 1); nb ^= b
        if seen != FULL:
            return False
    return True

def deficit(out, inn):
    deg = [bin(out[i]).count('1') + bin(inn[i]).count('1') for i in range(n)]
    tot = 0; worst = []
    for i in range(n):
        for j in range(i + 1, n):
            if (out[i] >> j) & 1 or (out[j] >> i) & 1:
                continue
            if (MODE == 'both' and (out[i] & out[j])) or (inn[i] & inn[j]):
                d = T - deg[i] - deg[j]
                if d > 0:
                    tot += d
    return tot

def score(out, inn):
    if not strong(out, inn):
        return 20000 + sum(bin(o).count('1') for o in out)
    if hamiltonian(out):
        return 10000 + sum(bin(o).count('1') for o in out)
    return deficit(out, inn)

def tough_start():
    # non-Hamiltonian seed: cut set S of size s whose deletion leaves s+1 weak components,
    # each a complete digraph; arcs between S and the components and inside S random.
    s = rng.randrange(1, max(2, (n - 1) // 2) + 1)
    rest = list(range(s, n)); rng.shuffle(rest)
    comps = [[] for _ in range(s + 1)]
    for k, v in enumerate(rest):
        comps[k % (s + 1) if k < s + 1 else rng.randrange(s + 1)].append(v)
    out = [0] * n; inn = [0] * n
    def arc(i, j):
        out[i] |= 1 << j; inn[j] |= 1 << i
    for c in comps:
        for i in c:
            for j in c:
                if i != j: arc(i, j)
    q = rng.uniform(0.5, 1.0)
    for i in range(s):
        for j in range(n):
            if i != j and (j < s or rng.random() < q):
                if rng.random() < q: arc(i, j)
                if rng.random() < q: arc(j, i)
    return out, inn

def random_start():
    if MODE_SEED == 'tough' or (MODE_SEED == 'mix' and rng.random() < 0.5):
        return tough_start()
    p = rng.uniform(0.3, 0.8)
    out = [0] * n; inn = [0] * n
    for i in range(n):
        for j in range(n):
            if i != j and rng.random() < p:
                out[i] |= 1 << j; inn[j] |= 1 << i
    return out, inn

def flip(out, inn, i, j):
    out[i] ^= 1 << j; inn[j] ^= 1 << i

best_overall = None; found = []
t0 = time.time(); restarts = 0; steps = 0
while time.time() - t0 < secs:
    restarts += 1
    out, inn = random_start()
    cur = score(out, inn); best = cur; temp = 3.0
    for it in range(20000):
        if time.time() - t0 > secs:
            break
        i = rng.randrange(n); j = rng.randrange(n - 1)
        if j >= i: j += 1
        flip(out, inn, i, j)
        if rng.random() < 0.3:
            k = rng.randrange(n); l = rng.randrange(n - 1)
            if l >= k: l += 1
            flip(out, inn, k, l); two = (k, l)
        else:
            two = None
        new = score(out, inn); steps += 1
        if new <= cur or (new < 10000 and rng.random() < pow(2.718, (cur - new) / temp)):
            cur = new
            if cur < best:
                best = cur
            if cur == 0:
                rec = [[j for j in range(n) if (out[i] >> j) & 1] for i in range(n)]
                if rec not in found:
                    found.append(rec)
                    print('FOUND', json.dumps(rec), flush=True)
        else:
            if two: flip(out, inn, *two)
            flip(out, inn, i, j)
        temp = max(0.05, temp * 0.9997)
    if best_overall is None or best < best_overall:
        best_overall = best
print(json.dumps(dict(mode=MODE, seedmode=MODE_SEED, n=n, seed=seed, secs=secs, restarts=restarts, steps=steps, best_deficit=best_overall, found=len(found))))
with open(outf, 'w') as f:
    json.dump(dict(mode=MODE, seedmode=MODE_SEED, n=n, seed=seed, secs=secs, restarts=restarts, steps=steps, best_deficit=best_overall, found=found), f)
