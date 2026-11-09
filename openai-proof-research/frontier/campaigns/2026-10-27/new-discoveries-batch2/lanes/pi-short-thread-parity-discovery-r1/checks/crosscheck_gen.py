"""
Independent cross-check of the piece generator: enumerate ALL unlabelled
trees up to n vertices by leaf extension with canonical dedup (no theory
from the paper used), then filter by the literal class condition
  - every maximal path whose interior vertices have degree 2 (thread):
    internal threads (both ends deg >= 3) length <= 2,
    leaf threads (at least one end deg 1) length <= 3,
and by twin-freeness, and compare per-n counts with genpieces.
"""
import sys
sys.path.insert(0, '.')
from cycles_solver import canon


def threads_ok(n, edges):
    deg = [0] * n
    for u, v in edges:
        deg[u] += 1
        deg[v] += 1
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    # walk from every degree != 2 vertex through degree-2 chains
    seen_edges = set()
    for s in range(n):
        if deg[s] == 2:
            continue
        for nxt in adj[s]:
            if (s, nxt) in seen_edges:
                continue
            # walk the chain starting s -> nxt
            prev, cur = s, nxt
            length = 1
            chain = [(s, nxt)]
            while deg[cur] == 2:
                a, b = adj[cur]
                step = b if a == prev else a
                if (cur, step) in seen_edges:
                    break
                chain.append((cur, step))
                prev, cur = cur, step
                length += 1
            for e in chain:
                seen_edges.add(e)
                seen_edges.add((e[1], e[0]))
            end_prev, end_cur = prev, cur
            # classify
            s_internal = deg[s] >= 3
            e_internal = deg[cur] >= 3
            if s_internal and e_internal:
                if length > 2:
                    return False
            else:
                if length > 3:
                    return False
    return True


def is_twinfree_indep(n, edges):
    from cycles_solver import canon as cn
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
            branches.append(cn(len(vert), be, tuple(st)))
        if len(set(branches)) != len(branches):
            return False
    return True


def enumerate_trees(nmax):
    """allTrees[n] = dict canonkey -> edges, for connected trees."""
    from collections import defaultdict
    allT = [dict() for _ in range(nmax + 1)]
    allT[1][(0, ())] = (1, [])  # single vertex; key placeholder
    # represent tree as (n, edges); canonical key via canon with fake statuses
    def key_of(n, edges):
        return canon(n, edges, tuple(0 for _ in range(n)))

    allT[1] = {key_of(1, []): (1, [])}
    for n in range(2, nmax + 1):
        cur = {}
        for k, (pn, pe) in allT[n - 1].items():
            for v in range(pn):
                ne = list(pe) + [(v, pn)]
                kk = key_of(pn + 1, ne)
                if kk not in cur:
                    cur[kk] = (pn + 1, ne)
        allT[n] = cur
    return allT


def main():
    nmax = int(sys.argv[1]) if len(sys.argv) > 1 else 13
    allT = enumerate_trees(nmax)
    from genpieces import gen_twinfree_pieces, is_twinfree
    pieces = gen_twinfree_pieces(nmax)
    from collections import Counter
    cnt_gen = Counter(n for n, e in pieces.values())
    cnt_gen_tf = Counter(n for n, e in pieces.values() if is_twinfree(n, e))
    ok = True
    for n in range(4, nmax + 1):
        cls = []
        tf = []
        cnt = 0
        for k, (pn, pe) in allT[n].items():
            if pn < 3:
                continue
            if threads_ok(pn, pe):
                cnt += 1
                if is_twinfree_indep(pn, pe):
                    tf.append(k)
        g2 = cnt_gen_tf.get(n, 0)
        match = (g2 == len(tf))
        print(f"n={n}: indep tf={len(tf)}  gen tf={g2}  "
              + ("OK" if match else "MISMATCH"))
        ok &= match
    print("ALL OK" if ok else "MISMATCH FOUND")


if __name__ == '__main__':
    main()
