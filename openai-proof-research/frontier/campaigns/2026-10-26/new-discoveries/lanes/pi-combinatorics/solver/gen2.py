#!/usr/bin/env python3
"""Broad search for Game of Cycles parity-conjecture violations on plane boards
with minimum degree >= 2.

Board = simple plane graph + list of bounded faces (each a simple cyclic vertex
sequence) + outer boundary walk. Generation ops (all preserve min degree >= 2,
simplicity, and simple-cycle bounded faces):
  1. new vertex inside a bounded face, adjacent to 2 of its boundary vertices
  2. chord inside a bounded face between non-adjacent boundary vertices
  3. new vertex inside a bounded face, adjacent to >= 3 boundary vertices
  4. attach a new cycle at a vertex, inside the outer face
  5. new edge between two vertices on a simple segment of the outer walk
  6. attach a new cycle at a vertex, nested inside a bounded face (old face dies)
"""
import sys, subprocess, json, random, hashlib
from collections import deque

def canon_key(bd):
    n = max(v for e in bd['edges'] for v in e) + 1
    adj = [[] for _ in range(n)]
    fcnt = [0]*n
    for f in bd['faces']:
        for v in set(f): fcnt[v] += 1
    for u,v in bd['edges']:
        adj[u].append(v); adj[v].append(u)
    col = [hash((adj[v].__len__(), fcnt[v])) for v in range(n)]
    for _ in range(4):
        newc = []
        for v in range(n):
            newc.append(hash((col[v], tuple(sorted(col[u] for u in adj[v])))))
        col = newc
    fsz = tuple(sorted(len(f) for f in bd['faces']))
    return (n, len(bd['edges']), fsz, tuple(sorted(col)))

def board(n_edges_list, faces, outer, dead=()):
    e = sorted(tuple(sorted(x)) for x in n_edges_list)
    assert len(set(e)) == len(e), "duplicate edge created"
    return {'edges': e,
            'faces': [list(f) for f in faces], 'outer': list(outer),
            'dead': [list(f) for f in dead]}

def cycles_positions(cyc, a, b):
    """two paths: a->b along the cycle, and b->a."""
    i = cyc.index(a)
    r = cyc[i:] + cyc[:i]   # rotated to start at a
    ja = r.index(b)
    p1 = r[:ja+1]          # a ... b
    p2 = r[ja:] + [a]      # b ... a
    return p1, p2

def op_vertices_and_chords(bd):
    out = []
    n = max(v for e in bd['edges'] for v in e) + 1
    es = set(bd['edges'])
    for fi, F in enumerate(bd['faces']):
        k = len(F)
        for ai in range(k):
            for bi in range(ai+1, k):
                a, b = F[ai], F[bi]
                adjacent = (bi - ai == 1) or (ai == 0 and bi == k-1)
                p1, p2 = cycles_positions(F, a, b)
                # op1: new vertex adjacent to a,b (any two distinct)
                w = n
                ne = list(bd['edges']) + [(a,w),(w,b)]
                if (a,w) not in es and (w,b) not in es:
                    out.append(board(ne, bd['faces'][:fi] + [p1+[w], p2+[w]] + bd['faces'][fi+1:], bd['outer'], bd['dead']))
                # op3: new vertex adjacent to 3 boundary vertices (a,b,c)
                if k >= 3:
                    for ci in range(k):
                        c = F[ci]
                        if c in (a, b): continue
                        def seg(x, y):
                            rx = F[F.index(x):] + F[:F.index(x)]
                            return rx[:rx.index(y)+1]
                        seg1 = seg(a, b); seg2 = seg(b, c); seg3 = seg(c, a)
                        ne3 = list(bd['edges']) + [(a,w),(b,w),(c,w)]
                        if all(e not in es for e in [(a,w),(b,w),(c,w)]):
                            nf = bd['faces'][:fi] + [seg1+[w], seg2+[w], seg3+[w]] + bd['faces'][fi+1:]
                            out.append(board(ne3, nf, bd['outer']))
                # op2: chord between non-adjacent
                if not adjacent and tuple(sorted((a,b))) not in es:
                    ne2 = list(bd['edges']) + [(a,b)]
                    out.append(board(ne2, bd['faces'][:fi] + [p1, p2] + bd['faces'][fi+1:], bd['outer'], bd['dead']))
    return out

def op_attach_outer(bd, L):
    """attach cycle of length L at each vertex of outer walk (inside outer face)."""
    out = []
    n = max(v for e in bd['edges'] for v in e) + 1
    es = set(bd['edges'])
    ow = bd['outer']
    for i, v in enumerate(ow):
        ws = list(range(n, n+L-1))
        cyc = [v] + ws
        ne = list(bd['edges']) + [(v,ws[0])] + [(ws[t],ws[t+1]) for t in range(L-2)] + [(ws[-1],v)]
        if any(e in es for e in ne): continue
        # outer walk has outer region on left; new bounded face cyc has its
        # interior on left; splice reversed cycle into the outer walk
        newouter = ow[:i+1] + cyc[:0:-1] + [v] + ow[i+1:]
        out.append(board(ne, bd['faces'] + [cyc], newouter, bd['dead']))
    return out

def op_attach_nested(bd, L):
    out = []
    n = max(v for e in bd['edges'] for v in e) + 1
    es = set(bd['edges'])
    for fi, F in enumerate(bd['faces']):
        for v in set(F):
            ws = list(range(n, n+L-1))
            cyc = [v] + ws
            ne = list(bd['edges']) + [(v,ws[0])] + [(ws[t],ws[t+1]) for t in range(L-2)] + [(ws[-1],v)]
            if any(e in es for e in ne): continue
            out.append(board(ne, bd['faces'][:fi] + [cyc] + bd['faces'][fi+1:], bd['outer'], bd['dead']))
    return out

def op_outer_edge(bd):
    """edge between a,b on a simple segment of the outer walk; new bounded face."""
    out = []
    n = max(v for e in bd['edges'] for v in e) + 1
    es = set(bd['edges'])
    ow = bd['outer']
    L = len(ow)
    for i in range(L):
        for j in range(i+2, L):
            a, b = ow[i], ow[j]
            if tuple(sorted((a,b))) in es: continue
            seg = ow[i:j+1]
            rest = ow[j:] + ow[:i+1]
            if len(set(seg)) != len(seg) or len(set(rest)) != len(rest):
                # allow repeated in rest (outer walk may repeat), but seg must be simple
                if len(set(seg)) != len(seg): continue
            out.append(board(list(bd['edges']) + [(a,b)], bd['faces'] + [seg[::-1]], rest, bd['dead']))
    return out

def seed_cycle(n):
    edges = [(i,(i+1)%n) for i in range(n)]
    faces = [list(range(n))]
    outer = list(range(n))[::-1]   # outer walk: interior (of outer region) on left
    return board(edges, faces, outer)

def to_text(bd):
    n = max(v for e in bd['edges'] for v in e) + 1
    lines = [f"{n} {len(bd['edges'])}"]
    lines += [f"{u} {v}" for u,v in bd['edges']]
    lines.append(str(len(bd['faces'])))
    for f in bd['faces']:
        lines.append(str(len(f)) + " " + " ".join(map(str,f)))
    return "\n".join(lines) + "\n"

def enumerate_boards(maxm, cap=20000):
    seen = set()
    out = []
    q = deque()
    for s in (3,4,5,6):
        b = seed_cycle(s)
        k = canon_key(b)
        if k not in seen:
            seen.add(k); q.append(b)
    while q:
        bd = q.popleft()
        m = len(bd['edges'])
        if m >= 3: out.append(bd)
        if m + 1 > maxm: continue
        nxt = op_vertices_and_chords(bd) + op_attach_outer(bd,3) + op_attach_nested(bd,3) + op_outer_edge(bd)
        if m + 2 <= maxm:
            nxt += op_attach_outer(bd,4) + op_attach_nested(bd,4)
        for c in nxt:
            if len(c['edges']) > maxm: continue
            k = canon_key(c)
            if k not in seen:
                seen.add(k); q.append(c)
        if len(out) > cap: 
            print("cap reached", file=sys.stderr); break
    return out

def _work(args):
    import gen
    i, text = args
    tot = text.count('\n')  # unused fallback
    return (i, text)

def solve_all(boards):
    import gen
    from multiprocessing import Pool
    texts = [(i, to_text(bd)) for i, bd in enumerate(boards)]
    def work(arg):
        i, text = arg
        bd = boards[i]
        tot = len(bd['edges'])
        pred = "P1" if tot % 2 == 1 else "P2"
        try:
            w = gen.solve(text)
        except Exception as e:
            return (i, None, str(e), text)
        return (i, w, pred, text)
    viols = 0
    with Pool(30) as pool:
        for i, w, pred, text in pool.imap_unordered(work, texts, chunksize=8):
            if w is None:
                print(f"ERROR board #{i}: {pred}", file=sys.stderr)
                continue
            if w != pred:
                viols += 1
                print(f"VIOLATION board #{i}: edges={len(boards[i]['edges'])} winner={w} predicted={pred}")
                print(text)
                json.dump(boards[i], open(f'violation_{i}.json','w'))
    return viols

def _solve_worker(arg):
    i, text, pred = arg
    import gen
    try:
        w = gen.solve(text)
    except Exception as e:
        return (i, None, str(e), text, pred)
    return (i, w, pred, text, pred)

if __name__ == '__main__':
    maxm = int(sys.argv[1]) if len(sys.argv) > 1 else 10
    boards = enumerate_boards(maxm)
    print(f"{len(boards)} boards with <= {maxm} edges", file=sys.stderr)
    from multiprocessing import Pool
    tasks = []
    for i, bd in enumerate(boards):
        tot = len(bd['edges'])
        pred = "P1" if tot % 2 == 1 else "P2"
        tasks.append((i, to_text(bd), pred))
    viols = 0
    with Pool(30) as pool:
        for i, w, pred, text, _p in pool.imap_unordered(_solve_worker, tasks, chunksize=8):
            if w is None:
                print(f"ERROR board #{i}: {pred}", file=sys.stderr)
                continue
            if w != pred:
                viols += 1
                print(f"VIOLATION board #{i}: edges={len(boards[i]['edges'])} winner={w} predicted={pred}")
                print(text)
                json.dump(boards[i], open(f'violation_{i}.json','w'))
    print(f"done: {len(boards)} boards, {viols} violations", file=sys.stderr)
