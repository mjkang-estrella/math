"""Unique rectification target screen for Ilango-Pechenik-Zlatin Conjecture 6.3 (MathDB 339156).

Posets: heaps of lambda-minuscule elements (lambda = fundamental weight omega_i) for a
simply-laced Dynkin graph; first reflection at the bottom, so the heap has a unique minimum
and its order ideals are the heaps of prefixes (IPZ orientation: straight shapes = order ideals).
Proctor: such heaps are exactly the (connected) d-complete posets (dualised to IPZ's orientation).
We additionally verify Proctor's three d-complete axioms (dualised) directly.

K-jdt (IPZ Defs 2.8-2.15): Slide_gamma for nonempty gamma subset of inner corners (maximal elements
of the inner shape), Swap_{.,n} for n = 1..max label, RemoveDots.  rects(T) = all straight-shape
results over all slide sequences.  URT: straight tableau U such that every skew increasing tableau
having U among its rectifications has rects = {U}.  Conjecture 6.3: the minimally labelled
tableau M_lambda (M(x) = 1 + max_{y<x in lambda} M(y)) is a URT for every order ideal lambda.

usage:
  urt.py heaps GRAPH NODE MAXLEN TAG     GRAPH like "star:2,2,3" or "path:5"
  urt.py test  TAG [MAXSKEW] [IDX_FROM IDX_TO]
"""
import itertools
import json
import os
import sys
import time

LANE = '/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/expanded-corpus-r245'
OUT = os.path.join(LANE, 'outputs', 'claude-urt')


# ---------------------------------------------------------------- Dynkin graphs and heaps
def make_graph(spec):
    kind, arg = spec.split(':')
    if kind == 'path':
        n = int(arg)
        return n, [(i, i + 1) for i in range(n - 1)]
    if kind == 'star':
        arms = [int(a) for a in arg.split(',')]
        edges = []
        nxt = 1
        for a in arms:
            prev = 0
            for _ in range(a):
                edges.append((prev, nxt))
                prev = nxt
                nxt += 1
        return nxt, edges
    raise ValueError(spec)


def heaps(spec, node, maxlen):
    n, edges = make_graph(spec)
    adj = [set() for _ in range(n)]
    for a, b in edges:
        adj[a].add(b)
        adj[b].add(a)

    def canon_word(word):
        # elements e_k with label word[k]; e_a < e_b (a<b) if labels equal or adjacent (closure)
        L = len(word)
        below = [set() for _ in range(L)]
        for b in range(L):
            for a in range(b):
                if word[a] == word[b] or word[a] in adj[word[b]]:
                    below[b].add(a)
        used = [False] * L
        out = []
        for _ in range(L):
            cands = [k for k in range(L) if not used[k] and all(used[a] for a in below[k])]
            k = min(cands, key=lambda k: (word[k], k))
            used[k] = True
            out.append(word[k])
        return tuple(out)

    start = [0] * n
    start[node] = 1
    frontier = {(): tuple(start)}
    allh = {}
    for length in range(maxlen + 1):
        nxt = {}
        for w, c in frontier.items():
            ext = False
            for j in range(n):
                if c[j] == 1:
                    ext = True
                    c2 = list(c)
                    cj = c[j]
                    c2[j] -= 2 * cj
                    for k in adj[j]:
                        c2[k] += cj
                    w2 = canon_word(w + (j,))
                    nxt[w2] = tuple(c2)
            allh[w] = (c, ext)
        if length == maxlen:
            break
        frontier = nxt
    return n, adj, allh


def heap_poset(word, adj):
    L = len(word)
    less = [[False] * L for _ in range(L)]
    for b in range(L):
        for a in range(b):
            if word[a] == word[b] or word[a] in adj[word[b]]:
                less[a][b] = True
    for k in range(L):
        for i in range(L):
            if less[i][k]:
                for j in range(L):
                    if less[k][j]:
                        less[i][j] = True
    return less


# ---------------------------------------------------------------- generic poset tools
class Poset:
    def __init__(self, less):
        self.N = N = len(less)
        self.less = less
        self.up = [[y for y in range(N) if less[x][y] and not any(less[x][z] and less[z][y] for z in range(N))]
                   for x in range(N)]
        self.down = [[y for y in range(N) if x in self.up[y]] for x in range(N)]
        self.downmask = [sum(1 << y for y in range(N) if less[y][x]) for x in range(N)]
        ideals = []
        for m in range(1 << N):
            ok = True
            mm = m
            while mm:
                b = mm & -mm
                x = b.bit_length() - 1
                if self.downmask[x] & ~m:
                    ok = False
                    break
                mm ^= b
            if ok:
                ideals.append(m)
        self.ideals = ideals

    def maxima(self, m):
        res = []
        mm = m
        while mm:
            b = mm & -mm
            x = b.bit_length() - 1
            if not any(m >> y & 1 for y in self.up[x]):
                res.append(x)
            mm ^= b
        return res


def is_d_complete(P):
    """Proctor's axioms, dualised (unique minimum orientation).  d_k (k>=3): chain a_1<..<a_{k-2},
    two incomparable x,y above a_{k-2}, chain b_1<..<b_{k-2} above both.  d_k-interval [w,z]:
    interval isomorphic to d_k.  Dual 'd_k^+ convex set': convex set isomorphic to d_k minus its
    minimum.  Axioms (dual): (1) every d_k^+ convex set I has w covered by the minimal elements of I
    with I+{w} a d_k interval; (2) if [w,z] is a d_k interval, w is covered by no element outside it;
    (3) no two d_k^+ convex sets differ only in their maximal elements."""
    N = P.N
    less = P.less

    def interval(w, z):
        return [v for v in range(N) if (v == w or less[w][v]) and (v == z or less[v][z])]

    def iso_dk(S, k, drop_min=False):
        # check whether induced subposet on S is isomorphic to d_k (or d_k minus minimum)
        S = list(S)
        if len(S) != 2 * k - 2 - (1 if drop_min else 0):
            return False
        # d_k is determined by: unique pair of incomparable elements x,y; all others comparable to all
        inc = [(a, b) for a, b in itertools.combinations(S, 2) if not less[a][b] and not less[b][a]]
        if len(inc) != 1:
            return False
        x, y = inc[0]
        others = [v for v in S if v not in (x, y)]
        lowers = [v for v in others if less[v][x] and less[v][y]]
        uppers = [v for v in others if less[x][v] and less[y][v]]
        if len(lowers) + len(uppers) != len(others):
            return False
        need_low = k - 2 - (1 if drop_min else 0)
        return len(lowers) == need_low and len(uppers) == k - 2

    def convex(S):
        s = set(S)
        for a in S:
            for b in S:
                if less[a][b]:
                    for v in range(N):
                        if less[a][v] and less[v][b] and v not in s:
                            return False
        return True

    maxk = N // 2 + 2
    for k in range(3, maxk + 1):
        # d_k intervals
        dk_int = []
        for w in range(N):
            for z in range(N):
                if less[w][z]:
                    I = interval(w, z)
                    if iso_dk(I, k):
                        dk_int.append((w, z, frozenset(I)))
        # (2)
        for w, z, I in dk_int:
            for v in P.up[w]:
                if v not in I:
                    return False, f'axiom2 k={k}'
        # d_k^+ convex sets: take each pair x,y incomparable with common upper chain
        plus_sets = set()
        size = 2 * k - 3
        # generate candidates: for each z (top) and each element set... brute force over subsets of
        # intervals [m, z] would be costly; instead build from incomparable pair x,y
        for x, y in itertools.combinations(range(N), 2):
            if less[x][y] or less[y][x]:
                continue
            for z in range(N):
                if not (less[x][z] and less[y][z]):
                    continue
                # elements between {x or y} and z: must form chain of k-2 above both; lower chain of k-3 below both
                ups = [v for v in range(N) if less[x][v] and less[y][v] and (v == z or less[v][z])]
                if len(ups) != k - 2:
                    continue
                lowall = [v for v in range(N) if less[v][x] and less[v][y]]
                # choose the top k-3 elements of the lower chain: the lower part must be a chain
                # consisting of the k-3 elements immediately below; enumerate chains ending under both
                for low in itertools.combinations(lowall, k - 3):
                    S = set(ups) | {x, y} | set(low)
                    if convex(list(S)) and iso_dk(S, k, drop_min=True):
                        # minimal elements of S must be covered-by relation compatible: S convex suffices
                        plus_sets.add(frozenset(S))
        for S in plus_sets:
            mins = [v for v in S if not any(less[u][v] for u in S)]
            # (1): exists w covered by every minimal element of S (w below all) with S+{w} a d_k interval
            ok = False
            for w in range(N):
                if w in S:
                    continue
                if all(w in P.down[m] for m in mins):
                    zs = [v for v in S if not any(less[v][u] for u in S)]
                    I = interval(w, zs[0])
                    if set(I) == set(S) | {w} and iso_dk(I, k):
                        ok = True
                        break
            if not ok:
                return False, f'axiom1 k={k}'
        # (3): no two d_k^+ convex sets differing only in their maximal elements
        byrest = {}
        for S in plus_sets:
            mx = frozenset(v for v in S if not any(less[v][u] for u in S))
            rest = S - mx
            byrest.setdefault(rest, set()).add(mx)
        for rest, mxs in byrest.items():
            if len(mxs) > 1:
                return False, f'axiom3 k={k}'
    return True, 'ok'


# ---------------------------------------------------------------- K-jdt
def slide(P, mu, T, gamma):
    """T: dict cell->label on nu/mu. gamma: list of inner corners. returns (mu', T')."""
    lab = dict(T)
    dots = set(gamma)
    mx = max(lab.values()) if lab else 0
    for n in range(1, mx + 1):
        newdots = set()
        newlab = {}
        for x in dots:
            if any(lab.get(y) == n for y in P.up[x]):
                newlab[x] = n
            else:
                newdots.add(x)
        for y, v in lab.items():
            if v == n and any(x in dots for x in P.down[y]):
                newdots.add(y)
            else:
                newlab.setdefault(y, v)
        # cells that were n and became dots must be removed from labels
        for y in list(newlab):
            if y in newdots:
                del newlab[y]
        lab, dots = newlab, newdots
    mu2 = mu
    for g in gamma:
        mu2 &= ~(1 << g)
    return mu2, lab


def key(mu, lab):
    return (mu, tuple(sorted(lab.items())))


def rects(P, mu, lab, memo):
    k = key(mu, lab)
    if k in memo:
        return memo[k]
    if mu == 0:
        r = frozenset([tuple(sorted(lab.items()))])
        memo[k] = r
        return r
    ic = P.maxima(mu)
    res = set()
    for r in range(1, len(ic) + 1):
        for gamma in itertools.combinations(ic, r):
            mu2, lab2 = slide(P, mu, lab, gamma)
            # sanity: increasing
            for x, v in lab2.items():
                for y in P.up[x]:
                    if y in lab2 and lab2[y] <= v:
                        raise RuntimeError('non-increasing after slide')
                if (mu2 >> x) & 1:
                    raise RuntimeError('label inside inner shape')
            res |= rects(P, mu2, lab2, memo)
    r = frozenset(res)
    memo[k] = r
    return r


def is_min_labeled(P, lab):
    for x, v in lab.items():
        m = max((lab[y] for y in P.down[x] if y in lab), default=0)
        if v != m + 1:
            return False
    return True


def labelings(P, cells, h):
    """increasing labelings of cell list (topologically sorted) with labels 1..h, surjective."""
    order = sorted(cells, key=lambda x: bin(P.downmask[x]).count('1'))
    lab = {}

    def rec(i):
        if i == len(order):
            if len(set(lab.values())) == h:
                yield dict(lab)
            return
        x = order[i]
        lo = max((lab[y] for y in P.down[x] if y in lab), default=0) + 1
        # must leave room above: labels must be <= h - (longest chain above x within cells)
        for v in range(lo, h + 1):
            lab[x] = v
            yield from rec(i + 1)
        lab.pop(x, None)
    yield from rec(0)


def height_of(P, mask):
    cells = [x for x in range(P.N) if mask >> x & 1]
    h = {}
    for x in sorted(cells, key=lambda x: bin(P.downmask[x]).count('1')):
        h[x] = 1 + max((h[y] for y in P.down[x] if y in h), default=0)
    return max(h.values(), default=0)


MULTI = [0]


def test_poset(P, maxskew, deadline):
    MULTI[0] = 0
    memo = {}
    found = []
    checked = 0
    hmax = height_of(P, (1 << P.N) - 1)
    for nu in P.ideals:
        for mu in P.ideals:
            if mu & ~nu or mu == nu or mu == 0:
                continue
            skew = nu & ~mu
            cells = [x for x in range(P.N) if skew >> x & 1]
            if len(cells) > maxskew:
                continue
            for h in range(1, min(hmax, len(cells)) + 1):
                for lab in labelings(P, cells, h):
                    checked += 1
                    R = rects(P, mu, lab, memo)
                    if len(R) > 1:
                        MULTI[0] += 1
                        mins = [r for r in R if is_min_labeled(P, dict(r))]
                        if mins:
                            found.append({'nu': nu, 'mu': mu, 'T': sorted(lab.items()),
                                          'rects': [list(r) for r in R], 'min_labeled_among': [list(m) for m in mins]})
                            return found, checked, True
                    if time.time() > deadline:
                        return found, checked, False
    return found, checked, True


def poset_canon(less):
    N = len(less)
    best = None
    # refine by (number below, number above)
    sig = [(sum(less[y][x] for y in range(N)), sum(less[x][y] for y in range(N))) for x in range(N)]
    cells = {}
    for x in range(N):
        cells.setdefault(sig[x], []).append(x)
    groups = [cells[s] for s in sorted(cells)]
    cnt = 0
    for perms in itertools.product(*[itertools.permutations(g) for g in groups]):
        order = [v for p in perms for v in p]
        code = tuple(tuple(int(less[a][b]) for b in order) for a in order)
        if best is None or code < best:
            best = code
        cnt += 1
        if cnt > 200000:
            break
    return best


def main():
    os.makedirs(OUT, exist_ok=True)
    mode = sys.argv[1]
    t0 = time.time()
    if mode == 'heaps':
        spec, node, maxlen, tag = sys.argv[2], int(sys.argv[3]), int(sys.argv[4]), sys.argv[5]
        n, adj, allh = heaps(spec, node, maxlen)
        # keep heaps that are maximal: either terminal (no extension) or of length maxlen
        keep = {}
        for w, (c, ext) in allh.items():
            if (not ext) or len(w) == maxlen:
                less = heap_poset(w, adj)
                cf = poset_canon(less)
                if cf not in keep:
                    keep[cf] = w
        rows = []
        for cf, w in keep.items():
            P = Poset(heap_poset(w, adj))
            dc, why = is_d_complete(P)
            rows.append({'word': list(w), 'size': len(w), 'd_complete_check': dc, 'why': why})
        with open(os.path.join(OUT, f'heaps-{tag}.json'), 'x') as f:
            json.dump({'graph': spec, 'node': node, 'maxlen': maxlen, 'adj': [sorted(a) for a in adj],
                       'n_all': len(allh), 'heaps': rows}, f, indent=1)
        print(tag, 'all', len(allh), 'kept', len(rows), 'dcomplete', sum(r['d_complete_check'] for r in rows),
              round(time.time() - t0, 1), 's')
        return
    if mode == 'heapsmany':
        # heapsmany "spec/node;spec/node;..." MAXLEN TAG : union of distinct maximal heaps (by poset iso)
        specs, maxlen, tag = sys.argv[2], int(sys.argv[3]), sys.argv[4]
        keep = {}
        items = []
        for item in specs.split(';'):
            if item.startswith('starall:'):
                arms = [int(x) for x in item.split(':')[1].split(',')]
                items += [f"star:{','.join(map(str, arms))}/{v}" for v in range(1 + sum(arms))]
            else:
                items.append(item)
        for item in items:
            spec, node = item.split('/')
            n, adj, allh = heaps(spec, int(node), maxlen)
            for w, (c, ext) in allh.items():
                if (not ext) or len(w) == maxlen:
                    less = heap_poset(w, adj)
                    cf = poset_canon(less)
                    if cf not in keep:
                        keep[cf] = (item, w, [sorted(a) for a in adj])
        rows = []
        for cf, (item, w, adjl) in keep.items():
            P = Poset(heap_poset(w, [set(a) for a in adjl]))
            dc, why = is_d_complete(P)
            rows.append({'source': item, 'word': list(w), 'adj': adjl, 'size': len(w),
                         'd_complete_check': dc, 'why': why})
        rows.sort(key=lambda r: r['size'])
        with open(os.path.join(OUT, f'heaps-{tag}.json'), 'x') as f:
            json.dump({'specs': specs, 'maxlen': maxlen, 'heaps': rows}, f, indent=1)
        print(tag, 'kept', len(rows), 'dcomplete', sum(r['d_complete_check'] for r in rows),
              'sizes', sorted(set(r['size'] for r in rows)), round(time.time() - t0, 1), 's')
        return
    if mode == 'test':
        tag = sys.argv[2]
        maxskew = int(sys.argv[3]) if len(sys.argv) > 3 else 99
        D = json.load(open(os.path.join(OUT, f'heaps-{tag}.json')))
        gadj = [set(a) for a in D['adj']] if 'adj' in D else None
        a = int(sys.argv[4]) if len(sys.argv) > 4 else 0
        b = int(sys.argv[5]) if len(sys.argv) > 5 else len(D['heaps'])
        deadline = t0 + 85
        out = []
        for idx in range(a, b):
            row = D['heaps'][idx]
            adj = [set(a) for a in row['adj']] if 'adj' in row else gadj
            P = Poset(heap_poset(tuple(row['word']), adj))
            found, checked, complete = test_poset(P, maxskew, deadline)
            out.append({'idx': idx, 'word': row['word'], 'size': row['size'], 'dc': row['d_complete_check'],
                        'checked_tableaux': checked, 'multi_rect_tableaux': MULTI[0], 'complete': complete,
                        'violations': found})
            print(idx, row['size'], 'dc', row['d_complete_check'], 'checked', checked, 'multi', MULTI[0],
                  'complete', complete,
                  'VIOLATION' if found else '', flush=True)
            if time.time() > deadline:
                break
        with open(os.path.join(OUT, f'test-{tag}-{a}-{b}-s{maxskew}.json'), 'x') as f:
            json.dump(out, f, indent=1)
        print('seconds', round(time.time() - t0, 1))


if __name__ == '__main__':
    main()
