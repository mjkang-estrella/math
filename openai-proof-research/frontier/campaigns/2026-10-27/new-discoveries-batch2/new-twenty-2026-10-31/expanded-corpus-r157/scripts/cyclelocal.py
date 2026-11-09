# Local search for Conjecture 30 (Aprile-Di Summa). slack(col) = min over integer k on [p0,p1] of
# (max |M| s.t. p_M <= k) - (l-h+2). Counterexample iff slack < 0.
import sys, math, random, json, time
def maxmatch_path(cols, k, h):
    # cols: list of edge colours along a path; returns max matching size with colour counts <= k
    # states: dict (last_used, countvec) ; use set of (last, vec)
    states = {(0, (0,)*h)}
    for c in cols:
        new = set()
        for last, v in states:
            new.add((0, v))
            if not last and v[c] < k[c]:
                w = list(v); w[c] += 1; new.add((1, tuple(w)))
        states = new
    return max(sum(v) for _, v in states)
def maxmatch_cycle(col, k, h):
    E = len(col)
    a = maxmatch_path(col[1:], k, h)
    c0 = col[0]
    if k[c0] >= 1:
        k2 = list(k); k2[c0] -= 1
        b = 1 + maxmatch_path(col[2:E-1], k2, h)
        a = max(a, b)
    return a
def slack(col, l, h):
    p0 = [0]*h; p1 = [0]*h
    for i, c in enumerate(col): (p0 if i % 2 == 0 else p1)[c] += 1
    d = [p1[c]-p0[c] for c in range(h)]
    g = 0
    for x in d: g = math.gcd(g, abs(x))
    if g == 0: return (99, 0, None)
    best = (99, 0, None)
    for j in range(g+1):
        k = tuple(p0[c] + d[c]*j//g for c in range(h))
        s = maxmatch_cycle(col, k, h) - (l-h+2)
        if s < best[0]: best = (s, 1, k)
        elif s == best[0]: best = (s, best[1]+1, k)
    return best
l, h, seed, secs = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), float(sys.argv[4])
rnd = random.Random(seed); t = time.time()
found = []; restarts = 0; bestever = 99; bestcol = None
while time.time()-t < secs:
    restarts += 1
    col = [rnd.randrange(h) for _ in range(2*l)]
    cur = slack(col, l, h)
    for it in range(400):
        i = rnd.randrange(2*l); old = col[i]; col[i] = rnd.randrange(h)
        if rnd.random() < 0.3:
            j = rnd.randrange(2*l); col[i], col[j] = col[j], col[i]
        new = slack(col, l, h)
        if (new[0], -new[1]) <= (cur[0], -cur[1]) or rnd.random() < 0.02:
            cur = new
        else:
            col[i] = old if col[i] != old else col[i]
            cur = slack(col, l, h)
        if cur[0] < bestever: bestever = cur[0]; bestcol = (list(col), cur[2])
        if cur[0] < 0:
            found.append((list(col), cur[2])); break
    if found: break
print(json.dumps({'l': l, 'h': h, 'seed': seed, 'restarts': restarts, 'best_slack': bestever, 'best_col': bestcol, 'found': found, 'sec': round(time.time()-t,1)}))
