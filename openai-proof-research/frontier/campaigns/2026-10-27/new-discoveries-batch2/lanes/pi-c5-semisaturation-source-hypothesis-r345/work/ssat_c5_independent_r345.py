# Independent verification, lane pi-c5-semisaturation-source-hypothesis-r345.
# Target: Furedi-Kim arXiv:1103.0067v1 Eq.(6) and Conjecture 4.1 (MathDB 396813).
#
# Source definition (Section 4): G is C5-semisaturated iff for every non-edge e,
# G+e has STRICTLY more C5 copies than G.  C5 copies = subgraphs (not induced).
#
# Two INDEPENDENT implementations:
#   (A) literal C5-count: 5-cycles as ordered vertex tuples / 10; semisat iff
#       count(G+e) > count(G) for every non-edge e.
#   (B) 4-path: G+e gains a C5 through e=uv iff G has a path u-a-b-c-v with
#       a,b,c distinct and distinct from u,v  (any new C5 must contain e).
#
# Caps: 210s wall / 512MiB group RSS under the fixed guard.

import itertools, sys, time, random, math

T0 = time.time()
DEADLINE = T0 + 185.0

def log(*a):
    print(f"[{time.time()-T0:7.2f}s]", *a, flush=True)

def to_adj(n, edges):
    adj = [0]*n
    for a, b in edges:
        adj[a] |= 1 << b
        adj[b] |= 1 << a
    return adj

def c5_count(n, adj):
    """(A) literal count: ordered 5-tuples forming a directed cycle, /10."""
    cnt = 0
    for t in itertools.permutations(range(n), 5):
        a, b, c, d, e = t
        if (adj[a] >> b) & 1 and (adj[b] >> c) & 1 and (adj[c] >> d) & 1 \
           and (adj[d] >> e) & 1 and (adj[e] >> a) & 1:
            cnt += 1
    return cnt // 10

def semisat_count(n, edges):
    # normalize orientation; a reversed duplicate here once corrupted the
    # add/restore cycle (failure preserved in the run log of the first attempt)
    edges = [(min(a, b), max(a, b)) for a, b in edges]
    assert len(set(edges)) == len(edges)
    adj = to_adj(n, edges)
    base = c5_count(n, adj)
    es = set(edges)
    for u in range(n):
        for v in range(u+1, n):
            if (u, v) in es:
                continue
            adj[u] |= 1 << v; adj[v] |= 1 << u
            more = c5_count(n, adj) > base
            adj[u] &= ~(1 << v); adj[v] &= ~(1 << u)
            if not more:
                return False
    return True

def has_path4(adj, u, v):
    au = adj[u] & ~(1 << v)
    m1 = au
    while m1:
        b1 = m1 & -m1; m1 ^= b1
        a = b1.bit_length() - 1
        m2 = adj[a] & ~((1 << u) | (1 << v) | (1 << a))
        while m2:
            b2 = m2 & -m2; m2 ^= b2
            b = b2.bit_length() - 1
            if adj[b] & adj[v] & ~((1 << u) | (1 << v) | (1 << a) | (1 << b)):
                return True
    return False

def semisat_path(n, adj):
    for u in range(n):
        au = adj[u]
        for v in range(u+1, n):
            if (au >> v) & 1:
                continue
            if not has_path4(adj, u, v):
                return False
    return True

def deg1_neighbor_ge3(adj, n):
    """Lemma 7.1(ii) pruning: deg-1 vertices need a neighbor of degree >= 3."""
    for v in range(n):
        if adj[v].bit_count() == 1:
            w = adj[v].bit_length() - 1
            if adj[w].bit_count() < 3:
                return False
    return True

def connected(adj, n):
    if any(a == 0 for a in adj):
        return False
    seen = 1; stack = [0]
    while stack:
        v = stack.pop()
        m = adj[v] & ~seen
        while m:
            b = m & -m; m ^= b
            i = b.bit_length() - 1
            if not (seen >> i) & 1:
                seen |= 1 << i; stack.append(i)
    return seen == (1 << n) - 1

# ---------------------------------------------------------------- Part A
# Definitional agreement: all n=5 graphs; all n=6 graphs with m<=6 plus all
# n=6 graphs flagged semisaturated by (B) at any m; random samples elsewhere.
log("Part A: literal-count (A) vs 4-path (B) agreement")
agree = disagree = 0
rng = random.Random(20261031)
def check_one(n, edges):
    global agree, disagree
    adj = to_adj(n, edges)
    sB = semisat_path(n, adj)
    sA = semisat_count(n, edges)
    if sA == sB: agree += 1
    else:
        disagree += 1
        log(f"  *** DEFINITION DISAGREEMENT n={n} edges={edges} A={sA} B={sB}")

for n in (5, 6):
    all_edges = list(itertools.combinations(range(n), 2))
    for m in range(0, len(all_edges)+1):
        if n == 6 and m > 6:
            break
        for es in itertools.combinations(all_edges, m):
            check_one(n, es)
for n, m in ((6, 7), (6, 8), (7, 8), (7, 9), (8, 9), (8, 10)):
    all_edges = list(itertools.combinations(range(n), 2))
    pool = itertools.combinations(all_edges, m)
    for es in itertools.islice(pool, 0, 400):
        if rng.random() < 0.5:
            check_one(n, es)
log(f"  agree={agree} disagree={disagree}")
assert disagree == 0
log(f"  (A)-(B) agreement confirmed on {agree} graphs incl. all n=5 graphs and all n=6 m<=6")

# ---------------------------------------------------------------- Part B
# Exact ssat(n) for n=5,6,7 (full), n=8 (m<=9, time-boxed).
def search(n, m, deadline, find_all=False):
    all_edges = list(itertools.combinations(range(n), 2))
    cnt = checked = 0
    for es in itertools.combinations(all_edges, m):
        cnt += 1
        if cnt % 2 == 0 and time.time() > deadline:
            return None, cnt, False
        adj = to_adj(n, es)
        # cheap filters first
        ok = True
        for v in range(n):
            d = adj[v].bit_count()
            if d < 1:
                ok = False; break
        if not ok or not deg1_neighbor_ge3(adj, n):
            continue
        if not semisat_path(n, adj):
            continue
        if not connected(adj, n):
            continue
        log(f"  n={n} m={m}: SEMISATURATED graph found: {list(es)}")
        if not find_all:
            return es, cnt, True
    return None, cnt, True

log("Part B: exact minima (full enumeration per m)")
summary = {}
plan = [(5, [5, 6, 7]), (6, [5, 6, 7, 8]), (7, [6, 7, 8, 9]), (8, [7, 8, 9])]
for n, ms in plan:
    found = None
    for m in ms:
        if time.time() > DEADLINE:
            log(f"  n={n}: global deadline hit"); break
        es, cnt, complete = search(n, m, min(DEADLINE, T0 + 40 + 45*(n-5)))
        log(f"  n={n} m={m}: {'HIT '+str(list(es)) if es else 'no semisaturated graph'} ({cnt} edge-sets, complete={complete})")
        if es:
            found = (m, es); break
        if not complete:
            log(f"  n={n} m={m}: INCOMPLETE (time)"); break
    summary[n] = found
    log(f"  ==> n={n}: ssat = {found[0] if found else '>=' + str(ms[-1]+1) + (' (complete)' if found is None else '')}")
    if time.time() > DEADLINE:
        break
log(f"  SUMMARY exact minima: {summary}")

# ---------------------------------------------------------------- Part C
# r343 witnesses re-verified under the literal count definition (A).
log("Part C: r343 witnesses under literal definition (A)")
# (r343 proposals.json lists the n=5 witness as {01,02,03,04,12,34}; the first
# run here accidentally dropped (3,4) and recorded semisat(A)=False -- fixed.)
w343 = {
    5: [(0,1),(0,2),(0,3),(0,4),(1,2),(3,4)],
    6: [(0,1),(0,2),(0,3),(0,4),(0,5),(1,2),(1,3),(2,4)],
    7: [(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,2),(3,4),(5,6)],
}
for n, es in w343.items():
    log(f"  n={n}: r343 witness semisat(A)={semisat_count(n, es)}")

# ---------------------------------------------------------------- Part D
# Paper's construction, decoded from the v1 figure (ar5iv asset es1_2.png):
# per block i: tree edges (1-2,3-4,5-6,7-8,1-3,3-5,5-7 on local labels 0..7)
# plus 4 spokes y-0,y-2,y-4,y-6.  Triangle join: y-a,y-b,a-b.  Pendant drop:
# remove leaf of block 0 (local vertex 1) and its edge.
def fk_construction(t, tri=0, drop=False):
    edges = []; y = 8*t
    norm = lambda e: (min(e), max(e))
    for i in range(t):
        o = 8*i
        edges += [(o+0,o+1),(o+2,o+3),(o+4,o+5),(o+6,o+7),
                  (o+0,o+2),(o+2,o+4),(o+4,o+6),
                  (y,o+0),(y,o+2),(y,o+4),(y,o+6)]
    for j in range(tri):
        a, b = 8*t+1+2*j, 8*t+2+2*j
        edges += [(y,a),(a,b),(b,y)]
    if drop:
        # delete the leaf (paper vertex 2, local 1) itself, per Lemma 7.1(iii),
        # then relabel compactly
        drop_v = 1
        edges = [e for e in edges if drop_v not in e]
        edges = [(a if a < drop_v else a-1, b if b < drop_v else b-1) for a, b in edges]
    edges = [norm(e) for e in edges]
    return 1 + 8*t + 2*tri - (1 if drop else 0), edges

log("Part D: Furedi-Kim construction, verified semisaturated")
checks = [
    (1, 0, False, "n=9,  e=11  base t=1            [class 8t+1]"),
    (2, 0, False, "n=17, e=22  base t=2            [class 8t+1]"),
    (1, 1, False, "n=11, e=14  one triangle        [class 8t+3]"),
    (1, 2, False, "n=13, e=17  two triangles       [class 8t+5]"),
    (1, 3, False, "n=15, e=20  three triangles     [class 8t+7]"),
    (1, 0, True,  "n=8,  e=10  pendant dropped     [class 8t]"),
    (1, 1, True,  "n=10, e=13  pendant dropped     [class 8t+2]"),
    (1, 2, True,  "n=12, e=16  pendant dropped     [class 8t+4]"),
    (1, 3, True,  "n=14, e=19  pendant dropped     [class 8t+6]"),
]
for t, tri, drop, label in checks:
    n, es = fk_construction(t, tri, drop)
    adj = to_adj(n, es)
    y = 8*t - (1 if drop else 0)   # y label shifts down when the leaf is deleted
    dist2 = all((adj[y] >> v) & 1 or (adj[y] & adj[v]) for v in range(n) if v != y)
    if n <= 13:
        ok = semisat_count(n, es); method = "literal(A)"
    else:
        ok = semisat_path(n, adj); method = "4-path(B)"
    log(f"  {label}: semisat={ok} [{method}] dist2_from_y={dist2}")

# ---------------------------------------------------------------- Part E
# Eq.(6) ceil(11(n-1)/8) vs the paper's own construction values, all n in [5,30].
log("Part E: (6) vs paper's constructions")
def constr_value(n):
    t, r = divmod(n, 8)
    odd  = {1: 11*t, 3: 11*t+3, 5: 11*t+6, 7: 11*t+9}          # n=8t+{1,3,5,7}, t>=1 for 1
    even = {0: 11*t-1, 2: 11*t+2, 4: 11*t+5, 6: 11*t+8}        # n=8t+{0,2,4,6}
    return (odd if n % 2 else even)[r]
bad = []
for n in range(5, 31):
    b6 = math.ceil(11*(n-1)/8)
    cv = constr_value(n)
    tag = "ok" if cv <= b6 else "<-- construction EXCEEDS displayed bound (6)"
    if cv > b6: bad.append(n)
    log(f"  n={n:3d}: (6)={b6:3d}  construction={cv:3d}  {tag}")
log(f"  Classes where the paper's own construction exceeds (6): n%8==6 (e.g. {bad[:4]}), incl. n=6 itself")

log("DONE OK")
