"""Independent bounded search (own code). Bitmask IR-graph evaluation.
Modes:
  gen OUT_GRAPHS OUT_RESULTS NMAX : all non-isomorphic graphs (connected or not) on 1..NMAX vertices
       (orderly-by-dedup: extensions of non-iso (n-1)-graphs, canonical form via colour refinement +
       permutations within cells), evaluate IR-graph of each, write graph list and summary.
  ext IN_GRAPHS N LO HI OUT : evaluate every one-vertex extension (all 2^N neighbourhoods) of the
       non-isomorphic N-vertex graphs with index in [LO,HI) of IN_GRAPHS; summary to OUT.
Outputs are created with mode 'x' (never overwritten)."""
import json, sys, itertools, time

def ir_info(n, adj):
    # adj: list of neighbour bitmasks (open). closed masks:
    N = [adj[v] | (1 << v) for v in range(n)]
    full = 1 << n
    irr = bytearray(full)
    irr[0] = 1
    best = 0
    # irredundant sets are hereditary: S irredundant => S minus top bit irredundant; use as quick filter
    for S in range(1, full):
        top = S.bit_length() - 1
        if not irr[S & ~(1 << top)]:
            continue
        ok = True
        T = S
        while T:
            low = T & -T; v = low.bit_length() - 1; T ^= low
            other = 0
            R = S ^ low
            while R:
                l2 = R & -R; other |= N[l2.bit_length() - 1]; R ^= l2
            if not (N[v] & ~other):
                ok = False; break
        if ok:
            irr[S] = 1
            c = bin(S).count("1")
            if c > best: best = c
    sets = [S for S in range(full) if irr[S] and bin(S).count("1") == best]
    idx = {S: i for i, S in enumerate(sets)}
    edges = []
    for i, A in enumerate(sets):
        for j in range(i + 1, len(sets)):
            B = sets[j]
            X = A & ~B; Y = B & ~A
            if bin(X).count("1") == 1 and bin(Y).count("1") == 1:
                u = X.bit_length() - 1; v = Y.bit_length() - 1
                if adj[u] >> v & 1:
                    edges.append((i, j))
    return best, len(sets), edges

def classify(m, edges):
    if m == 1: return "P1"
    deg = [0] * m; nb = [[] for _ in range(m)]
    for i, j in edges:
        deg[i] += 1; deg[j] += 1; nb[i].append(j); nb[j].append(i)
    seen = {0}; st = [0]
    while st:
        x = st.pop()
        for y in nb[x]:
            if y not in seen: seen.add(y); st.append(y)
    if len(seen) != m: return None
    if len(edges) == m - 1 and max(deg) <= 2: return "P%d" % m
    if len(edges) == m and all(d == 2 for d in deg): return "C%d" % m
    return None

def connected(n, adj):
    seen = 1; st = [0]
    while st:
        x = st.pop(); new = adj[x] & ~seen; seen |= new
        while new:
            l = new & -new; st.append(l.bit_length() - 1); new ^= l
    return seen == (1 << n) - 1

def canon(n, adj):
    col = [0] * n
    while True:
        sig = [(col[v], tuple(sorted(col[u] for u in range(n) if adj[v] >> u & 1))) for v in range(n)]
        ranks = {s: r for r, s in enumerate(sorted(set(sig)))}
        new = [ranks[s] for s in sig]
        if len(set(new)) == len(set(col)) and new == [ranks[s] for s in sig] and len(set(new)) == len(set(col)):
            col = new; break
        col = new
    cells = [[v for v in range(n) if col[v] == c] for c in sorted(set(col))]
    best = None
    for choice in itertools.product(*[itertools.permutations(c) for c in cells]):
        order = [v for part in choice for v in part]  # new label i -> old vertex order[i]
        pos = {v: i for i, v in enumerate(order)}
        code = 0
        for i in range(n):
            for j in range(i + 1, n):
                code = (code << 1) | (adj[order[i]] >> order[j] & 1)
        if best is None or code > best: best = code
    return best

def record(stats, hits, n, adj):
    IR, m, edges = ir_info(n, adj)
    c = classify(m, edges)
    conn = connected(n, adj)
    key = "%s|%s" % (c, "conn" if conn else "disc")
    stats[key] = stats.get(key, 0) + 1
    if c is not None:
        kind, k = c[0], int(c[1:])
        if (kind == "P" and k >= 3) or (kind == "C" and k >= 5):
            hits.append({"n": n, "adj": adj, "IR": IR, "type": c, "connected": conn})
        if kind == "C" and k in (3, 4):
            stats.setdefault("C34_examples", []) if False else None

def extend(n, adj, mask):
    return [adj[v] | ((mask >> v & 1) << n) for v in range(n)] + [mask]

if __name__ == "__main__":
    t0 = time.time()
    mode = sys.argv[1]
    if mode == "gen":
        outg, outr, nmax = sys.argv[2], sys.argv[3], int(sys.argv[4])
        levels = {1: [[0]]}
        for n in range(2, nmax + 1):
            seen = {}
            for adj in levels[n - 1]:
                for mask in range(1 << (n - 1)):
                    a = extend(n - 1, adj, mask)
                    k = canon(n, a)
                    if k not in seen: seen[k] = a
            levels[n] = list(seen.values())
        stats = {}; hits = []
        counts = {n: len(levels[n]) for n in levels}
        for n in levels:
            for adj in levels[n]:
                record(stats, hits, n, adj)
        with open(outg, "x") as f: json.dump({str(n): levels[n] for n in levels}, f)
        with open(outr, "x") as f:
            json.dump({"noniso_counts": counts, "stats": stats, "hits": hits, "secs": time.time() - t0}, f, indent=1)
        print(json.dumps({"noniso_counts": counts, "n_hits": len(hits), "secs": round(time.time() - t0, 1)}))
    elif mode == "ext":
        ing, n, lo, hi, out = sys.argv[2], int(sys.argv[3]), int(sys.argv[4]), int(sys.argv[5]), sys.argv[6]
        base = json.load(open(ing))[str(n)]
        stats = {}; hits = []; cnt = 0
        for adj in base[lo:hi]:
            for mask in range(1 << n):
                record(stats, hits, n + 1, extend(n, adj, mask)); cnt += 1
        with open(out, "x") as f:
            json.dump({"base_n": n, "lo": lo, "hi": min(hi, len(base)), "n_base_total": len(base), "evaluated": cnt,
                       "stats": stats, "hits": hits, "secs": time.time() - t0}, f, indent=1)
        print(json.dumps({"evaluated": cnt, "n_hits": len(hits), "types": sorted({h["type"] for h in hits}), "secs": round(time.time() - t0, 1)}))
