"""
Generator for TWIN-FREE pieces in the Question 11.4 class.

Class: tree, leaves status f, others n; internal threads (both ends deg >= 3)
<= 2 edges; leaf threads <= 3 edges.  Equivalently a subdivision of a
series-reduced skeleton with branch-branch weights 1..2 and branch-leaf
weights 1..3.

Twin branches at v = two isomorphic branches (components of X - v).  A twin
branch pair is exactly two equal children items (w, subtree) at some vertex,
so twin-free pieces are found among "locally twin-free" trees: at every
vertex the children items are pairwise distinct.  We generate planted trees
under that constraint (combinations without repetition), build unrooted
candidates, and apply the full twin check (parent-side branches) at the end.

Paths of 1..3 edges are in-class but excluded (parity known, Cor 4.4).
"""
import sys
sys.path.insert(0, '.')
from cycles_solver import canon


def piece_status_of(n, edges):
    deg = [0] * n
    for u, v in edges:
        deg[u] += 1
        deg[v] += 1
    return tuple(3 if deg[i] == 1 else 0 for i in range(n))


def form_to_tree(form, shift=0):
    if form[0] == 'L':
        return 1, [], shift
    edges = []
    nxt = shift + 1
    root = shift
    for (w, child) in form[1]:
        cur = root
        for _ in range(w - 1):
            edges.append((cur, nxt))
            cur = nxt
            nxt += 1
        cn, ce, croot = form_to_tree(child, nxt)
        edges.append((cur, croot))
        edges.extend(ce)
        nxt += cn
    return nxt - shift, edges, root


def _enum_sets(items, total, mincount, out, formkey):
    """Enumerate SUBSETS (no repeats) of items (size, w, form) with size sum
    == total and at least mincount items, in nondecreasing item order."""
    m = len(items)
    smin = [10 ** 9] * (m + 1)
    for i in range(m - 1, -1, -1):
        smin[i] = min(smin[i + 1], items[i][0])
    chosen = []

    def dfs(i, remaining):
        if remaining == 0:
            if len(chosen) >= mincount:
                out.append(formkey(chosen))
            return
        if i >= m or smin[i] > remaining:
            return
        for j in range(i, m):
            k, w, f = items[j]
            if k > remaining:
                continue
            chosen.append((w, f))
            dfs(j + 1, remaining - k)
            chosen.pop()
    dfs(0, total)


def gen_planted_lf(nmax, verbose=False):
    """P[n]: set of locally-twin-free canonical planted forms, n vertices."""
    P = [set() for _ in range(nmax + 1)]
    P[1].add(('L',))
    for n in range(2, nmax + 1):
        items = []
        for k in range(1, n - 1):
            for f in P[k]:
                for w in ((1, 2, 3) if f[0] == 'L' else (1, 2)):
                    items.append((k + w - 1, w, f))
        items.sort()
        forms = []
        _enum_sets(items, n - 1, 2, forms, lambda ch: ('B', tuple(sorted(ch))))
        P[n] = set(forms)
        if verbose:
            print(f"|P[{n}]| = {len(P[n])}", file=sys.stderr)
    return P


def is_twinfree(n, edges):
    """Full check: at every vertex, all branches (components of X - v,
    rooted at the neighbour, with piece statuses) are pairwise distinct."""
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    for v in range(n):
        branches = []
        for c in adj[v]:
            seen = {v, c}
            stack = [c]
            vert = []
            while stack:
                x = stack.pop()
                vert.append(x)
                for y in adj[x]:
                    if y not in seen:
                        seen.add(y)
                        stack.append(y)
            idx = {x: i for i, x in enumerate(vert)}
            be = [(idx[x], idx[y]) for x in vert for y in adj[x]
                  if y in idx and idx[y] > idx[x]]
            bdeg = {x: sum(1 for y in adj[x] if y in idx) for x in vert}
            st = []
            for x in vert:
                if x == c:
                    st.append(3 if bdeg[x] == 0 else 0)
                else:
                    st.append(3 if bdeg[x] == 1 else 0)
            branches.append(canon(len(vert), be, tuple(st)))
        if len(set(branches)) != len(branches):
            return False
    return True


def gen_twinfree_pieces(nmax, verbose=False, shard=None, nshards=1):
    """All twin-free class pieces with nmin < n <= nmax... actually all
    n <= nmax.  Returns dict canonkey -> (n, edges).  shard/nshards split
    the work by skeleton-centre-case for parallelism (results merge)."""
    # planted levels needed: 1-centre items k <= nmax-7; pairs a <= nmax-4
    P = gen_planted_lf(nmax - 3, verbose=verbose)
    out = {}

    def add(n, edges):
        st = piece_status_of(n, edges)
        key = canon(n, edges, st)
        if key not in out:
            out[key] = (n, [tuple(e) for e in edges])

    def items_for(budget):
        items = []
        for k in range(1, budget + 1):
            for f in P[k]:
                for w in ((1, 2, 3) if f[0] == 'L' else (1, 2)):
                    items.append((k + w - 1, w, f))
        items.sort()
        return items

    # case A: one skeleton centre (shard 0)
    if shard in (None, 0):
        for n in range(2, nmax + 1):
            forms = []
            _enum_sets(items_for(n - 3), n - 1, 3, forms,
                       lambda ch: ('B', tuple(sorted(ch))))
            for form in forms:
                cnt, edges, root = form_to_tree(form)
                if cnt <= nmax:
                    add(cnt, edges)
    # case B: two skeleton centres (shards by a)
    for total in range(2, nmax + 1):
        for w in (1, 2):
            rem = total - 1 - (w - 1)
            if rem < 2:
                continue
            for a in range(1, rem):
                b = rem - a
                if b < a:
                    continue
                if shard is not None and (a % nshards) != shard:
                    continue
                A = [f for f in P[a] if f[0] == 'B' and len(f[1]) >= 2]
                if not A:
                    continue
                B = [f for f in P[b] if f[0] == 'B' and len(f[1]) >= 2]
                if not B:
                    continue
                # precompute item sets for the parent-side distinction
                for fa in A:
                    fa_items = set(fa[1])
                    na, ea, ra = form_to_tree(fa, 0)
                    for fb in B:
                        if (w, fb) in fa_items:
                            continue  # twin at centre a
                        if (w, fa) in set(fb[1]):
                            continue  # twin at centre b
                        nb, eb, rb = form_to_tree(fb, na)
                        edges = list(ea) + list(eb)
                        if w == 2:
                            iv = na + nb
                            edges.append((ra, iv))
                            edges.append((iv, rb))
                            nn = na + nb + 1
                        else:
                            edges.append((ra, rb))
                            nn = na + nb
                        if nn <= nmax:
                            add(nn, edges)
    return out


if __name__ == '__main__':
    import time
    from collections import Counter
    t0 = time.time()
    nmax = int(sys.argv[1]) if len(sys.argv) > 1 else 22
    pieces = gen_twinfree_pieces(nmax, verbose=True)
    print(f"twin-free candidates: {len(pieces)}  ({time.time()-t0:.1f}s)")
    cnt = Counter(n for n, e in pieces.values())
    for n in sorted(cnt):
        print(f"  n={n}: {cnt[n]}")
    tf = {k: v for k, v in pieces.items() if is_twinfree(v[0], v[1])}
    print(f"fully twin-free: {len(tf)}  ({time.time()-t0:.1f}s total)")
    cnt2 = Counter(n for n, e in tf.values())
    for n in sorted(cnt2):
        print(f"  n={n}: {cnt2[n]}")
