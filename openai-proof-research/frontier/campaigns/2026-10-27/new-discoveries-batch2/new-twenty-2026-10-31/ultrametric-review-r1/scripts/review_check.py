"""Independent reviewer check for MathDB 367834 (Dovgoshey-Cantor-Rovenska Conj. 6.2).

Written from scratch in the review lane; it does not import or read the discovery lane's scripts.
Diagnostic only: finite truncations of infinite objects, exact rational arithmetic.

Part I  ((i) => (ii)): a ray label sequence = finite random/exhaustive head + an explicit tail that
        tends to 0 (strictly decreasing, or decreasing with interleaved zeros).  We compute
        suffix maxima M_n exactly, the limit point p with d(p,x_n)=M_n, the records, the legs,
        build the starlike tree on {x_1..x_R} + {p}, and compare the tree path-maximum metric with
        the ray metric (extended to p) on every pair.  We also check the degree/edge conditions.
Part II ((ii) => (i)): a starlike tree = centre c (label 0) + finitely many random head legs +
        tail legs whose labels are below every head height.  We form the strict-prefix-record
        groups, enumerate groups by decreasing height with RANDOM tie breaking, write each group as
        y_{s+1..e}, y_s, and compare the ray path-maximum metric with the tree metric on all pairs
        among the enumerated prefix.  We also check the ray edge condition.
Part III: negative controls (mutations that must be detected), so a vacuous checker cannot pass.
"""
from fractions import Fraction as F
import itertools, random, sys, json

LOG = []
def log(*a):
    s = ' '.join(str(x) for x in a)
    LOG.append(s)
    print(s)

# ---------------------------------------------------------------- Part I helpers
def make_ray(head, tail_kind, tail_start, tail_len):
    """Return a function lam(n) (1-indexed) on the infinite sequence and a suffix-max oracle."""
    N = len(head)
    def lam(n):
        if n <= N:
            return head[n - 1]
        k = n - N  # 1,2,...
        if tail_kind == 'dec':
            return tail_start / (2 ** (k - 1))
        else:  # 'zig': tau, 0, tau/2, 0, tau/4, ...
            return tail_start / (2 ** ((k - 1) // 2)) if k % 2 == 1 else F(0)
    def M(n):  # sup_{k>=n} lam(k), exact: tail is eventually dominated by its first positive term
        if n > N:
            k = n - N
            if tail_kind == 'dec':
                return lam(n)
            return lam(n) if k % 2 == 1 else lam(n + 1)
        return max(max(head[n - 1:]), M(N + 1))
    return lam, M

def ray_dist(lam, a, b):
    if a == b:
        return F(0)
    lo, hi = min(a, b), max(a, b)
    return max(lam(k) for k in range(lo, hi + 1))

def tree_pathmax(adj, label, u, v):
    if u == v:
        return F(0)
    # BFS parents from u
    par = {u: None}
    q = [u]
    for x in q:
        for y in adj[x]:
            if y not in par:
                par[y] = x
                q.append(y)
    w, best = v, F(0)
    while w is not None:
        best = max(best, label[w]); w = par[w]
    return best

def check_part1(head, tail_kind, tail_start, tail_len=8):
    lam, M = make_ray(head, tail_kind, tail_start, tail_len)
    N = len(head)
    R = N + tail_len
    # valid ray labelling: no two consecutive zeros (check far enough)
    for n in range(1, R + 3):
        if max(lam(n), lam(n + 1)) <= 0:
            return 'invalid'
    # records: lam(r) >= lam(k) for all k>r  <=>  lam(r) >= M(r+1)
    recs = [r for r in range(1, R + 1) if lam(r) >= M(r + 1)]
    assert recs, 'no record'
    last = recs[-1]
    # independent sanity: least record >= n has label M(n)
    for n in range(1, last + 1):
        rn = min(r for r in recs if r >= n)
        assert lam(rn) == M(n), ('record label', head, n)
        assert M(n) > 0
    # build tree on 1..last plus 'p'
    adj = {n: set() for n in range(1, last + 1)}; adj['p'] = set()
    label = {n: lam(n) for n in range(1, last + 1)}; label['p'] = F(0)
    prev = 0
    legs = []
    for r in recs:
        leg = list(range(prev + 1, r + 1)); legs.append(leg)
        for a, b in zip(leg, leg[1:]):
            adj[a].add(b); adj[b].add(a)
        adj[r].add('p'); adj['p'].add(r)
        prev = r
    # tree checks: edges = vertices - 1, connected
    V = list(adj); E = sum(len(s) for s in adj.values()) // 2
    assert E == len(V) - 1
    seen = {'p'}; q = ['p']
    for x in q:
        for y in adj[x]:
            if y not in seen: seen.add(y); q.append(y)
    assert len(seen) == len(V)
    assert all(len(adj[v]) <= 2 for v in V if v != 'p')
    for u in V:
        for v in adj[u]:
            assert max(label[u], label[v]) > 0, 'edge condition'
    # metric comparison: ray metric extended by d(p,x_n)=M(n)
    def dX(a, b):
        if a == b: return F(0)
        if a == 'p': return M(b)
        if b == 'p': return M(a)
        return ray_dist(lam, a, b)
    bad = 0
    for a, b in itertools.combinations(V, 2):
        if tree_pathmax(adj, label, a, b) != dX(a, b):
            bad += 1
    return ('ok' if bad == 0 else 'BAD', len(recs), len(legs[-1]) if legs else 0)

# ---------------------------------------------------------------- Part II helpers
def check_part2(head_legs, tail_legs, rng):
    """head_legs, tail_legs: lists of label lists (index 0 = vertex adjacent to centre)."""
    legs = head_legs + tail_legs
    # vertices: ('c',) and (i, a) for leg i, position a (1-based)
    label = {'c': F(0)}
    adj = {'c': set()}
    for i, leg in enumerate(legs):
        prevv = 'c'
        for a, lab in enumerate(leg, start=1):
            v = (i, a); label[v] = lab; adj[v] = set()
            adj[v].add(prevv); adj[prevv].add(v); prevv = v
    for u in adj:
        for v in adj[u]:
            if max(label[u], label[v]) <= 0:
                return 'invalid'
    # heights
    h = {}
    for i, leg in enumerate(legs):
        m = F(0)
        for a, lab in enumerate(leg, start=1):
            m = max(m, lab); h[(i, a)] = m
    # strict prefix record groups
    groups = []
    for i, leg in enumerate(legs):
        m = F(0); cur = None
        for a, lab in enumerate(leg, start=1):
            if lab > m:
                if cur: groups.append(cur)
                cur = [(i, a)]; m = lab
            else:
                cur.append((i, a))
        groups.append(cur)
    for g in groups:
        hg = label[g[0]]
        assert all(h[v] == hg for v in g) and all(label[v] <= hg for v in g)
    # order by decreasing height, random tie-breaking
    keyed = [(-label[g[0]], rng.random(), g) for g in groups]
    keyed.sort(key=lambda t: (t[0], t[1]))
    seq = []
    for _, _, g in keyed:
        seq.extend(g[1:] + g[:1])
    # tail legs must come last (they are below all head heights): only compare head-complete prefix
    lab_seq = [label[v] for v in seq]
    for a, b in zip(lab_seq, lab_seq[1:]):
        assert max(a, b) > 0, 'ray edge condition'
    bad = 0
    n = len(seq)
    for i in range(n):
        mx = lab_seq[i]
        for j in range(i + 1, n):
            mx = max(mx, lab_seq[j])
            if mx != tree_pathmax(adj, label, seq[i], seq[j]):
                bad += 1
    return 'ok' if bad == 0 else 'BAD'

# ---------------------------------------------------------------- Part III negative controls
def control_wrong_group_order(rng):
    """Writing a group as y_s, y_{s+1}, ..., y_e (leader FIRST) must break the metric somewhere."""
    # leg c - y1(3) - y2(1) - y3(1), another leg c - z1(2): group {y1,y2,y3} leader y1.
    legs = [[F(3), F(1), F(1)], [F(2)]]
    label = {'c': F(0)}; adj = {'c': set()}
    for i, leg in enumerate(legs):
        prevv = 'c'
        for a, lab in enumerate(leg, start=1):
            v = (i, a); label[v] = lab; adj[v] = {prevv}; adj[prevv].add(v); prevv = v
    seq = [(0, 1), (0, 2), (0, 3), (1, 1)]  # leader first: d_ray(y3, z1) = max(1,2)=2 but tree gives 3
    labs = [label[v] for v in seq]
    bad = 0
    for i in range(len(seq)):
        for j in range(i + 1, len(seq)):
            if max(labs[i:j + 1]) != tree_pathmax(adj, label, seq[i], seq[j]): bad += 1
    return bad

def control_wrong_cut(head):
    """Cutting legs at every index (a star) instead of at records must break the metric for a
    non-decreasing head such as (1,2,...)."""
    lam, M = make_ray(head, 'dec', F(1, 2), 4)
    R = len(head) + 4
    label = {n: lam(n) for n in range(1, R + 1)}; label['p'] = F(0)
    adj = {n: {'p'} for n in range(1, R + 1)}; adj['p'] = set(range(1, R + 1))
    bad = 0
    for a, b in itertools.combinations(range(1, R + 1), 2):
        if tree_pathmax(adj, label, a, b) != ray_dist(lam, a, b): bad += 1
    return bad

def main():
    rng = random.Random(20261104)
    stats = {'p1_exhaustive': 0, 'p1_random': 0, 'p1_invalid': 0, 'p2_random': 0, 'p2_exhaustive': 0, 'p2_invalid': 0}
    vals = [F(0), F(1), F(2), F(3)]
    # Part I exhaustive: heads of length 1..6 over {0,1,2,3}; two tail kinds; tail starts 1/2 and 5/2
    for L in range(1, 7):
        for head in itertools.product(vals, repeat=L):
            for kind in ('dec', 'zig'):
                for ts in (F(1, 2), F(5, 2)):
                    r = check_part1(list(head), kind, ts, tail_len=5)
                    if r == 'invalid': stats['p1_invalid'] += 1; continue
                    assert r[0] == 'ok', (head, kind, ts, r)
                    stats['p1_exhaustive'] += 1
    log('Part I exhaustive OK:', stats['p1_exhaustive'], 'cases; skipped invalid (two consecutive zeros):', stats['p1_invalid'])
    # Part I random: longer heads, rational labels with many ties
    for _ in range(400):
        L = rng.randint(5, 14)
        head = [F(rng.choice([0, 1, 1, 2, 3, 3, 5, 7]), rng.choice([1, 2, 3])) for _ in range(L)]
        kind = rng.choice(['dec', 'zig']); ts = F(rng.randint(1, 12), rng.choice([2, 3, 4]))
        r = check_part1(head, kind, ts, tail_len=rng.randint(2, 7))
        if r == 'invalid': continue
        assert r[0] == 'ok', (head, kind, ts, r)
        stats['p1_random'] += 1
    log('Part I random OK:', stats['p1_random'])
    # Part II exhaustive: up to 2 head legs, each of length 1..3, labels in {0,1,2,3}; tail legs
    small = [F(0), F(1), F(2), F(3)]
    head_leg_shapes = [list(t) for L in (1, 2, 3) for t in itertools.product(small, repeat=L)]
    for l1 in head_leg_shapes:
        for l2 in head_leg_shapes:
            tail = [[F(1, 2 ** (k + 1))] for k in range(2)] + [[F(1, 64), F(0), F(1, 64)], [F(1, 128), F(1, 256)]]
            r = check_part2([l1, l2], tail, rng)
            if r == 'invalid': stats['p2_invalid'] += 1; continue
            assert r == 'ok', (l1, l2)
            stats['p2_exhaustive'] += 1
    log('Part II exhaustive OK:', stats['p2_exhaustive'], 'cases; skipped invalid:', stats['p2_invalid'])
    # Part II random: 2..6 head legs, lengths 1..6, many ties, random tie breaking
    for _ in range(400):
        heads = []
        for _ in range(rng.randint(2, 6)):
            heads.append([F(rng.choice([0, 1, 1, 2, 2, 3, 4]), rng.choice([1, 2])) for _ in range(rng.randint(1, 6))])
        tail = []
        for k in range(rng.randint(1, 4)):
            t = F(1, 2 ** (k + 4))
            tail.append(rng.choice([[t], [t, t], [t, F(0), t / 2], [t / 3, t]]))
        r = check_part2(heads, tail, rng)
        if r == 'invalid': continue
        assert r == 'ok', heads
        stats['p2_random'] += 1
    log('Part II random OK:', stats['p2_random'])
    c1 = control_wrong_group_order(rng)
    c2 = control_wrong_cut([F(1), F(2), F(3)])
    log('Negative control (leader-first group order) mismatches:', c1)
    log('Negative control (star cut instead of record cut) mismatches:', c2)
    assert c1 > 0 and c2 > 0
    stats['neg_controls'] = {'leader_first_mismatches': c1, 'star_cut_mismatches': c2}
    json.dump({'stats': stats, 'log': LOG}, open(sys.argv[1], 'w'), indent=1)
    log('ALL CHECKS PASSED')

if __name__ == '__main__':
    main()
