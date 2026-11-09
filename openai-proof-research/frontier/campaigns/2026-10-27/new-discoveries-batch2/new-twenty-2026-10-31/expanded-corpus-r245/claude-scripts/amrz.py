"""AMRZ conjecture (Aboulker-Matamala-Rochet-Zamora, Conj. 2.3; Chvatal survey Conj. 5) screen.

For a connected graph G, the line L(uv) = {w : d(u,v) = |d(u,w) +- d(w,v)|}
(i.e. one of u, v, w lies between the other two).  lambda(G) = number of distinct
lines, mu(G) = number of unordered pairs uv with L(uv) = V.  Conjecture:
lambda(G) + mu(G) >= |V|.

Modes
  gen N            : read outputs/claude-amrz/conn-(N-1).txt (or seed for N<=2) and write
                     the canonical list of connected graphs on N vertices to conn-N.txt.
                     Every connected graph on N vertices has a non-cut vertex, so it is a
                     one-vertex extension of a connected graph on N-1 vertices.
  check N          : check every graph in conn-N.txt.
  ext N A B        : check every one-vertex extension (nonempty neighbourhood) of graphs
                     A..B-1 of conn-(N-1).txt (no isomorph rejection; complete coverage of
                     connected graphs on N vertices when all chunks are run).
Results are written with exclusive-create to outputs/claude-amrz/.
"""
import itertools
import json
import os
import sys
import time

LANE = '/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/expanded-corpus-r245'
OUT = os.path.join(LANE, 'outputs', 'claude-amrz')


def layers_of(n, adj):
    full = (1 << n) - 1
    L = []
    for u in range(n):
        seen = 1 << u
        fr = seen
        lay = [fr]
        while True:
            nx = 0
            f = fr
            while f:
                b = f & -f
                nx |= adj[b.bit_length() - 1]
                f ^= b
            nx &= ~seen
            if not nx:
                break
            seen |= nx
            lay.append(nx)
            fr = nx
        if seen != full:
            return None
        L.append(lay)
    return L


def lam_mu(n, adj):
    L = layers_of(n, adj)
    if L is None:
        return None
    full = (1 << n) - 1
    dist = [[0] * n for _ in range(n)]
    for u in range(n):
        for k, m in enumerate(L[u]):
            while m:
                b = m & -m
                dist[u][b.bit_length() - 1] = k
                m ^= b
    lines = set()
    mu = 0
    for u in range(n):
        Lu = L[u]
        for v in range(u + 1, n):
            Lv = L[v]
            D = dist[u][v]
            line = 0
            for k in range(D + 1):
                if k < len(Lu) and D - k < len(Lv):
                    line |= Lu[k] & Lv[D - k]
            # v between u and w: d(u,w) = D + d(v,w)
            for k in range(len(Lv)):
                if k + D < len(Lu):
                    line |= Lu[k + D] & Lv[k]
                else:
                    break
            for k in range(len(Lu)):
                if k + D < len(Lv):
                    line |= Lv[k + D] & Lu[k]
                else:
                    break
            lines.add(line)
            if line == full:
                mu += 1
    return len(lines), mu


def refine(n, adj):
    col = [bin(a).count('1') for a in range(0)] or [bin(adj[v]).count('1') for v in range(n)]
    while True:
        sig = []
        for v in range(n):
            nb = sorted(col[w] for w in range(n) if adj[v] >> w & 1)
            sig.append((col[v], tuple(nb)))
        keys = sorted(set(sig))
        new = [keys.index(s) for s in sig]
        if len(set(new)) == len(set(col)):
            return new
        col = new


def canon(n, adj):
    col = refine(n, adj)
    cells = {}
    for v in range(n):
        cells.setdefault(col[v], []).append(v)
    order_cells = [cells[c] for c in sorted(cells)]
    best = None
    for perms in itertools.product(*[itertools.permutations(c) for c in order_cells]):
        order = [v for p in perms for v in p]
        pos = [0] * n
        for i, v in enumerate(order):
            pos[v] = i
        code = []
        for v in order:
            m = 0
            a = adj[v]
            while a:
                b = a & -a
                m |= 1 << pos[b.bit_length() - 1]
                a ^= b
            code.append(m)
        code = tuple(code)
        if best is None or code < best:
            best = code
    return best


def read_list(N):
    if N == 1:
        return [(0,)]
    with open(os.path.join(OUT, f'conn-{N}.txt')) as f:
        return [tuple(int(x) for x in line.split(',')) for line in f if line.strip()]


def extensions(base):
    m = len(base)
    for S in range(1, 1 << m):
        adj = list(base)
        for w in range(m):
            if S >> w & 1:
                adj[w] |= 1 << m
        adj.append(S)
        yield adj


def main():
    os.makedirs(OUT, exist_ok=True)
    mode = sys.argv[1]
    N = int(sys.argv[2])
    t0 = time.time()
    if mode == 'gen':
        base = read_list(N - 1)
        seen = set()
        for g in base:
            for adj in extensions(g):
                seen.add(canon(N, adj))
        res = sorted(seen)
        with open(os.path.join(OUT, f'conn-{N}.txt'), 'x') as f:
            for c in res:
                f.write(','.join(map(str, c)) + '\n')
        print('gen', N, len(res), 'from', len(base), round(time.time() - t0, 1), 's')
        return
    if mode == 'check':
        graphs = read_list(N)
        tag = f'check-{N}'
        it = ((i, list(g)) for i, g in enumerate(graphs))
    else:
        A, B = int(sys.argv[3]), int(sys.argv[4])
        base = read_list(N - 1)[A:B]
        tag = f'ext-{N}-{A}-{B}'

        def gen():
            for i, g in enumerate(base):
                for adj in extensions(g):
                    yield A + i, adj
        it = gen()
    cnt = 0
    viol = []
    margin_hist = {}
    tight = []
    for i, adj in it:
        r = lam_mu(N, adj)
        if r is None:
            continue
        cnt += 1
        lam, mu = r
        mg = lam + mu - N
        margin_hist[mg] = margin_hist.get(mg, 0) + 1
        if mg < 0:
            viol.append({'base': i, 'adj': adj, 'lambda': lam, 'mu': mu})
        elif mg == 0 and len(tight) < 20:
            tight.append({'base': i, 'adj': adj, 'lambda': lam, 'mu': mu})
    out = {'tag': tag, 'n': N, 'graphs_checked': cnt, 'violations': viol[:50],
           'violation_count': len(viol), 'margin_hist': {str(k): v for k, v in sorted(margin_hist.items())},
           'tight_examples': tight, 'seconds': round(time.time() - t0, 1)}
    with open(os.path.join(OUT, tag + '.json'), 'x') as f:
        json.dump(out, f, indent=1)
    print(json.dumps({k: out[k] for k in ('tag', 'graphs_checked', 'violation_count', 'margin_hist', 'seconds')}))


if __name__ == '__main__':
    main()
