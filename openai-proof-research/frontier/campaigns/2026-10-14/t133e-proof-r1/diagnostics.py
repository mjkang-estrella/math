#!/usr/bin/env python3
"""Reviewer-designed finite diagnostics for T133E (proof-r1).

Independent implementation of (a) the Margulis-Gabber-Galil frame in the
Hoory-Linial-Wigderson Construction 8.1 convention, (b) toy affine block data
of the source shape, (c) the source section-06 colored graph Y, and (d) the
candidate station-frame graph X.  It tests implementation claims on finite
instances only.  It is not a proof of any theorem.
"""
import itertools
import json
import math
import random
import sys
from collections import deque

LIMITS = 'Finite implementation diagnostics only; not a proof, not a contribution verdict.'


def need(ok, why):
    if not ok:
        raise SystemExit('DIAGNOSTIC_FAIL: ' + why)


# ---------------------------------------------------------------- frame

def hlw_maps(m):
    """HLW Construction 8.1: T1=[[1,2],[0,1]], T2=[[1,0],[2,1]], e1, e2."""
    def T1(v):
        x, y = v
        return ((x + 2 * y) % m, y)

    def T2(v):
        x, y = v
        return (x, (2 * x + y) % m)
    return [T1, lambda v: ((T1(v)[0] + 1) % m, T1(v)[1]),
            T2, lambda v: (T2(v)[0], (T2(v)[1] + 1) % m)]


def candidate_maps(m):
    return [lambda v: ((v[0] + 2 * v[1]) % m, v[1]),
            lambda v: ((v[0] + 2 * v[1] + 1) % m, v[1]),
            lambda v: (v[0], (v[1] + 2 * v[0]) % m),
            lambda v: (v[0], (v[1] + 2 * v[0] + 1) % m)]


def frame_checks():
    out = {}
    for m in range(2, 41):
        V = [(x, y) for x in range(m) for y in range(m)]
        H, C = hlw_maps(m), candidate_maps(m)
        for i in range(4):
            need(all(H[i](v) == C[i](v) for v in V), 'HLW convention m=%d i=%d' % (m, i))
            need(len({C[i](v) for v in V}) == m * m, 'not a permutation')
    out['convention_m_range'] = [2, 40]
    exact = {}
    for m in (2, 3, 4):
        V = [(x, y) for x in range(m) for y in range(m)]
        idx = {v: j for j, v in enumerate(V)}
        T = candidate_maps(m)
        arcs = [(idx[v], idx[T[i](v)]) for v in V for i in range(4)]
        n = len(V)
        best = None
        for mask in range(1, 1 << n):
            k = bin(mask).count('1')
            if k > n // 2:
                continue
            cut = sum(1 for a, b in arcs if ((mask >> a) & 1) != ((mask >> b) & 1))
            r = (cut, k)
            if best is None or cut * best[1] < best[0] * k:
                best = r
            # indicator Rayleigh identity: crossing arcs = 1_A^T (8I - A) 1_A
            if mask % 977 == 1:
                q = 8 * k - sum(2 for a, b in arcs if (mask >> a) & 1 and (mask >> b) & 1)
                need(q == cut, 'Rayleigh identity')
        need(best[0] * 5 > 2 * best[1], 'h(F)>2/5 fails m=%d' % m)
        exact[m] = '%d/%d' % best
    out['exact_frame_h'] = exact
    # power iteration estimate of lambda_2 (a lower estimate; sanity only)
    worst = 0.0
    for m in range(2, 17):
        V = [(x, y) for x in range(m) for y in range(m)]
        idx = {v: j for j, v in enumerate(V)}
        T = candidate_maps(m)
        nb = [[] for _ in V]
        for v in V:
            for i in range(4):
                a, b = idx[v], idx[T[i](v)]
                nb[a].append(b)
                nb[b].append(a)
        rng = random.Random(m)
        f = [rng.random() - 0.5 for _ in V]
        lam = 0.0
        for _ in range(400):
            mu = sum(f) / len(f)
            f = [t - mu for t in f]
            g = [sum(f[u] for u in nb[a]) + 8 * f[a] for a in range(len(V))]
            nf = math.sqrt(sum(t * t for t in f))
            lam = sum(a * b for a, b in zip(f, g)) / (nf * nf) - 8
            ng = math.sqrt(sum(t * t for t in g))
            f = [t / ng for t in g]
        worst = max(worst, lam)
    need(worst <= 5 * math.sqrt(2) + 1e-9, 'power-iteration lambda2 exceeds 5 sqrt 2')
    out['max_power_iteration_lambda2_m2_16'] = round(worst, 6)
    return out


# ---------------------------------------------------------------- toy block data

def make_instance(seed, nh, nv, nsites, nsquares):
    rng = random.Random(seed)
    dims = {}
    for j in range(nh):
        dims['H%d' % j] = rng.choice([1, 2])
    for j in range(nv):
        dims['V%d' % j] = 1
    blocks = []
    for j in range(nsites):
        blocks.append({'id': 'S%d' % j, 'names': ['H%d' % (j % nh)], 'eq': None})
    for j in range(nsquares):
        h = rng.sample(range(nh), 2)
        v = rng.sample(range(nv), 2)
        names = ['H%d' % h[0], 'H%d' % h[1], 'V%d' % v[0], 'V%d' % v[1]]
        a = sum(dims[x] for x in names)
        coeff = [rng.randint(0, 1) for _ in range(a - 2)] + [1, 1]
        blocks.append({'id': 'Q%d' % j, 'names': names, 'eq': (coeff, rng.randint(0, 1))})
    for B in blocks:
        B['slices'] = {}
        p = 0
        for x in B['names']:
            B['slices'][x] = list(range(p, p + dims[x]))
            p += dims[x]
        B['a'] = p
        need(p <= 6 and len(B['names']) <= 4, 'block size')
        for eps in (0, 1):
            Z = []
            for t in itertools.product((0, 1), repeat=p):
                if B['eq'] is None or sum(c * z for c, z in zip(B['eq'][0], t)) % 2 == eps * B['eq'][1]:
                    Z.append(t)
            B['Z%d' % eps] = Z
        Z0, Z1 = set(B['Z0']), set(B['Z1'])
        need(Z1 and all({add(z, xi) for z in Z0} == Z1 for xi in Z1), 'affine translate')
        for x in B['names']:
            for eps in (0, 1):
                need(len({restrict(B, z, x) for z in B['Z%d' % eps]}) == 2 ** dims[x], 'full projection')
    return dims, blocks


def add(a, b):
    return tuple((s + t) % 2 for s, t in zip(a, b))


def restrict(B, z, x):
    return tuple(z[i] for i in B['slices'][x])


def channels(blocks):
    ch = {}
    for B in blocks:
        L = [('0',)]
        for C in blocks:
            if C is B:
                continue
            for x in sorted(set(B['names']) & set(C['names'])):
                L.append((C['id'], x))
        ch[B['id']] = L
    return ch


def corder(B, c):
    if c == ('0',):
        return list(range(B['a']))
    first = B['slices'][c[1]]
    return first + [i for i in range(B['a']) if i not in first]


def build_Y(dims, blocks, eps):
    ch = channels(blocks)
    adj, sort, owner = {}, {}, {}

    def vert(v, s, b):
        adj.setdefault(v, set())
        sort[v] = s
        owner[v] = b

    def edge(u, v):
        need(u != v and v not in adj[u], 'Y simple')
        adj[u].add(v)
        adj[v].add(u)
    for B in blocks:
        b = B['id']
        Z = B['Z%d' % eps]
        vert(('a', b), ('a', b), b)
        for c in ch[b]:
            o = corder(B, c)
            q = 0 if c == ('0',) else dims[c[1]]
            for z in Z:
                vert(('s', b, c, z), ('s', b, c), b)
            for h in range(q, B['a'] + 1):
                for u in {tuple(z[i] for i in o[:h]) for z in Z}:
                    vert(('f', b, c, h, u), ('f', b, c, h), b)
            for h in range(q + 1, B['a'] + 1):
                for u in {tuple(z[i] for i in o[:h]) for z in Z}:
                    edge(('f', b, c, h, u), ('f', b, c, h - 1, u[:-1]))
            for z in Z:
                edge(('f', b, c, B['a'], tuple(z[i] for i in o)), ('s', b, c, z))
        for j in range(len(ch[b]) - 1):
            for z in Z:
                edge(('s', b, ch[b][j], z), ('s', b, ch[b][j + 1], z))
        edge(('a', b), ('f', b, ('0',), 0, ()))
    for j in range(len(blocks) - 1):
        edge(('a', blocks[j]['id']), ('a', blocks[j + 1]['id']))
    for B in blocks:
        for c in ch[B['id']][1:]:
            C, x = c
            if B['id'] < C:
                q = dims[x]
                for u in itertools.product((0, 1), repeat=q):
                    r1, r2 = ('f', B['id'], c, q, u), ('f', C, (B['id'], x), q, u)
                    need(r1 in adj and r2 in adj, 'roots exist')
                    edge(r1, r2)
    need(max(len(s) for s in adj.values()) <= 3, 'subcubic')
    return {'adj': adj, 'sort': sort, 'owner': owner, 'ch': ch}


def translate(B, ch, v, xi):
    if v[0] == 'a':
        return v
    if v[0] == 's':
        return ('s', v[1], v[2], add(v[3], xi))
    o = corder(B, v[2])
    return ('f', v[1], v[2], v[3], add(v[4], tuple(xi[i] for i in o[:v[3]])))


# ---------------------------------------------------------------- station frame graph X

ROOT_DEG, STATION_DEG, ORIG_DEG = 101, 100, 20


def build_X(Y, sorts, blocks):
    s = len(sorts)
    m = max(2, math.isqrt(s - 1) + 1 if s > 1 else 2)
    need(m * m >= s, 'stations')
    V0 = [(x, y) for x in range(m) for y in range(m)]
    T = candidate_maps(m)
    station_of = {srt: V0[j] for j, srt in enumerate(sorts)}
    sort_at = {V0[j]: srt for j, srt in enumerate(sorts)}
    adj, own = {}, {}
    block_of_sort = {}
    for v, srt in Y['sort'].items():
        block_of_sort[srt] = Y['owner'][v]
    dummy_owner = blocks[0]['id']

    def vert(v, o):
        need(v not in adj, 'X vertex once')
        adj[v] = set()
        own[v] = o

    def edge(u, v):
        need(u != v and v not in adj[u], 'X simple')
        adj[u].add(v)
        adj[v].add(u)
    for v in V0:
        vert(('q', v), block_of_sort.get(sort_at.get(v), dummy_owner))
    for v in V0:
        for i in range(4):
            vert(('pa', v, i), own[('q', v)])
            vert(('pb', v, i), own[('q', v)])
    for y in Y['adj']:
        vert(('Y', y), Y['owner'][y])
    for y, nb in Y['adj'].items():
        for z in nb:
            if ('Y', z) not in adj[('Y', y)]:
                edge(('Y', y), ('Y', z))
        edge(('Y', y), ('q', station_of[Y['sort'][y]]))
    for v in V0:
        for i in range(4):
            edge(('q', v), ('pa', v, i))
            edge(('pa', v, i), ('pb', v, i))
            edge(('pb', v, i), ('q', T[i](v)))
    target = {}
    for v in list(adj):
        if v[0] == 'q':
            target[v] = ROOT_DEG if v[1] == (0, 0) else STATION_DEG
        elif v[0] == 'pa':
            target[v] = 30 + 2 * v[2]
        elif v[0] == 'pb':
            target[v] = 31 + 2 * v[2]
        else:
            target[v] = ORIG_DEG
    for v, t in target.items():
        k = t - len(adj[v])
        need(k >= 0, 'leaf count nonnegative')
        for j in range(k):
            vert(('leaf', v, j), own[v])
            edge(v, ('leaf', v, j))
    return {'adj': adj, 'own': own, 'm': m, 'V0': V0, 'T': T, 'station_of': station_of}


def connected(adj):
    start = next(iter(adj))
    seen, dq = {start}, deque([start])
    while dq:
        u = dq.popleft()
        for w in adj[u]:
            if w not in seen:
                seen.add(w)
                dq.append(w)
    return len(seen) == len(adj)


def psi(B, ch, X0, xi):
    def f(v):
        if v[0] == 'Y':
            return ('Y', translate(B, ch, v[1], xi))
        if v[0] == 'leaf' and v[1][0] == 'Y':
            return ('leaf', ('Y', translate(B, ch, v[1][1], xi)), v[2])
        return v
    return {v: f(v) for v, o in X0['own'].items() if o == B['id']}


def union_iso(maps, X0, X1):
    """Bijection + edge preservation + equal induced edge counts => induced isomorphism."""
    F = {}
    for mp in maps:
        F.update(mp)
    img = set(F.values())
    if len(img) != len(F):
        return 'not injective'
    if any(v not in X1['adj'] for v in img):
        return 'image outside X1'
    e0 = e1 = 0
    for u in F:
        for w in X0['adj'][u]:
            if w in F:
                e0 += 1
                if F[w] not in X1['adj'][F[u]]:
                    return 'edge not preserved: %r -- %r' % (u[0], w[0])
    for u in img:
        e1 += sum(1 for w in X1['adj'][u] if w in img)
    if e0 != e1:
        return 'nonedge not preserved'
    return None


def compatible(blocks_by_id, lst):
    for (b, xb), (c, xc) in itertools.combinations(lst, 2):
        B, C = blocks_by_id[b], blocks_by_id[c]
        for x in set(B['names']) & set(C['names']):
            if restrict(B, xb, x) != restrict(C, xc, x):
                return False
    return True


def refine(adjs):
    """Color refinement with common color names on a disjoint union."""
    col = {(g, v): 0 for g, adj in enumerate(adjs) for v in adj}
    ncls = 1
    while True:
        sig = {}
        new = {}
        for (g, v), c in col.items():
            key = (c, tuple(sorted(col[(g, w)] for w in adjs[g][v])))
            new[(g, v)] = sig.setdefault(key, len(sig))
        if len(sig) == ncls:
            return col
        col, ncls = new, len(sig)


def readout_route(blocks_by_id, dims, ch, b, c, x):
    B, C = blocks_by_id[b], blocks_by_id[c]
    cb, cc = (c, x), (b, x)
    ib, ic = ch[b].index(cb), ch[c].index(cc)
    q = dims[x]
    seq = [('s', b, ch[b][j]) for j in range(ib + 1)]
    seq += [('f', b, cb, h) for h in range(B['a'], q - 1, -1)]
    seq += [('f', c, cc, h) for h in range(q, C['a'] + 1)]
    seq += [('s', c, ch[c][j]) for j in range(ic, -1, -1)]
    return seq


def toy_checks(seed, nh, nv, nsites, nsquares, cut_trials):
    dims, blocks = make_instance(seed, nh, nv, nsites, nsquares)
    by_id = {B['id']: B for B in blocks}
    Y = [build_Y(dims, blocks, e) for e in (0, 1)]
    ch = Y[0]['ch']
    res = {'blocks': len(blocks)}
    for e in (0, 1):
        need(connected(Y[e]['adj']), 'Y connected')
    sizes = [{}, {}]
    for e in (0, 1):
        for v, srt in Y[e]['sort'].items():
            sizes[e][srt] = sizes[e].get(srt, 0) + 1
    need(sizes[0] == sizes[1], 'sort cardinalities agree')
    need(max(sizes[0].values()) <= 64, 'sort size <= 64')
    sorts = sorted(sizes[0], key=repr)
    res['sorts'] = len(sorts)
    res['max_sort_size'] = max(sizes[0].values())
    X = [build_X(Y[e], sorts, blocks) for e in (0, 1)]
    res['frame_side_m'] = X[0]['m']
    for e in (0, 1):
        A = X[e]['adj']
        need(connected(A), 'X connected')
        degs = [len(n) for n in A.values()]
        need(max(degs) == 101 and degs.count(101) == 1, 'unique root degree 101')
        allowed = {1, 20, 100, 101} | set(range(30, 38))
        need(set(degs) <= allowed, 'degree classes')
    need(len(X[0]['adj']) == len(X[1]['adj']), 'equal order')
    res['order'] = len(X[0]['adj'])
    # offset-local degree invariance and single-block bijections
    nmaps = 0
    for B in blocks:
        for xi in B['Z1']:
            mp = psi(B, ch, X[0], xi)
            need(set(mp.values()) == {v for v, o in X[1]['own'].items() if o == B['id']}, 'Psi onto part')
            need(len(set(mp.values())) == len(mp), 'Psi injective')
            for u, w in mp.items():
                need(len(X[0]['adj'][u]) == len(X[1]['adj'][w]), 'degree preserved')
            nmaps += 1
            need(union_iso([mp], X[0], X[1]) is None, 'single-block induced isomorphism')
    res['single_block_maps_checked'] = nmaps
    # compatible unions; reason-checked incompatible negatives
    rng = random.Random(seed + 7)
    pos = neg = 0
    neg_reasons = set()
    for _ in range(60):
        U = rng.sample(blocks, rng.randint(2, min(4, len(blocks))))
        choices = [[(B['id'], xi) for xi in B['Z1']] for B in U]
        lists = list(itertools.product(*choices))
        rng.shuffle(lists)
        for lst in lists[:40]:
            maps = [psi(by_id[b], ch, X[0], xi) for b, xi in lst]
            r = union_iso(maps, X[0], X[1])
            if compatible(by_id, lst):
                need(r is None, 'compatible union not isomorphism: %s' % r)
                pos += 1
            elif r is not None:
                neg += 1
                neg_reasons.add(r.split(':')[0])
    need(pos > 0 and neg > 0, 'union controls exercised')
    need(neg_reasons <= {'edge not preserved', 'nonedge not preserved'}, 'negative reasons')
    res['compatible_unions_iso'] = pos
    res['incompatible_unions_rejected'] = neg
    # readout-walk lemma in both versions
    walks = 0
    for B in blocks:
        for c in ch[B['id']][1:]:
            C, x = c
            seq = readout_route(by_id, dims, ch, B['id'], C, x)
            for e in (0, 1):
                for z in B['Z%d' % e]:
                    cur = {('s', B['id'], ('0',), z)}
                    for srt in seq[1:]:
                        cur = {w for u in cur for w in Y[e]['adj'][u] if Y[e]['sort'][w] == srt}
                    want = {('s', C, ('0',), w) for w in by_id[C]['Z%d' % e]
                            if restrict(by_id[C], w, x) == restrict(B, z, x)}
                    need(cur == want, 'readout walk lemma')
                    walks += 1
    res['readout_walk_cases'] = walks
    # color refinement: frame labels and sorts recovered (2-variable proxy only)
    col = refine([X[0]['adj'], X[1]['adj']])
    classes = {}
    for key, c in col.items():
        classes.setdefault(c, []).append(key)
    for c, mem in classes.items():
        frame = [k for k in mem if k[1][0] in ('q', 'pa', 'pb')]
        if frame:
            need(len(mem) == 2 and mem[0][1] == mem[1][1] and {mem[0][0], mem[1][0]} == {0, 1},
                 'frame vertex individualized')
        ys = {Y[k[0]]['sort'][k[1][1]] for k in mem if k[1][0] == 'Y'}
        need(len(ys) <= 1, 'sort mixed in refinement class')
    res['refinement_classes'] = len(classes)
    # cut diagnostics (bound claimed: h >= 1/163840)
    A = X[0]['adj']
    N = len(A)
    cell = {}
    for v in A:
        w = v[1] if v[0] == 'leaf' else v
        if w[0] == 'q':
            cell[v] = w[1]
        elif w[0] in ('pa', 'pb'):
            cell[v] = w[1]
        else:
            cell[v] = X[0]['station_of'][Y[0]['sort'][w[1]]]
    cells = {}
    for v, c in cell.items():
        cells.setdefault(c, []).append(v)
    need(max(len(c) for c in cells.values()) <= 1641, 'cell size bound')
    res['max_cell_size'] = max(len(c) for c in cells.values())

    def ratio(S):
        b = sum(1 for u in S for w in A[u] if w not in S)
        return b / len(S)
    worst = float('inf')
    tests = 0
    keys = list(cells)
    if len(keys) <= 16:
        kid = {k: j for j, k in enumerate(keys)}
        csize = [len(cells[k]) for k in keys]
        cross = {}
        for u in A:
            for w in A[u]:
                a, b = kid[cell[u]], kid[cell[w]]
                if a < b:
                    cross[(a, b)] = cross.get((a, b), 0) + 1
        for mask in range(1, (1 << len(keys)) - 1):
            size = sum(csize[j] for j in range(len(keys)) if mask >> j & 1)
            if size <= N // 2:
                b = sum(c for (a, bb), c in cross.items() if (mask >> a & 1) != (mask >> bb & 1))
                worst = min(worst, b / size)
                tests += 1
    for t in range(cut_trials):
        k = rng.randint(1, len(keys))
        S = set()
        for c in rng.sample(keys, k):
            mem = cells[c]
            if rng.random() < 0.3:
                S |= set(rng.sample(mem, rng.randint(1, len(mem))))
            else:
                S |= set(mem)
        if len(S) > N // 2:
            S = set(A) - S
        if S and len(S) <= N // 2:
            worst = min(worst, ratio(S))
            tests += 1
    root = ('q', (0, 0))
    seen, order, dq = {root}, [root], deque([root])
    while dq and len(order) < N // 2:
        u = dq.popleft()
        for w in sorted(A[u], key=repr):
            if w not in seen and len(order) < N // 2:
                seen.add(w)
                order.append(w)
                dq.append(w)
    for k in range(1, len(order) + 1, max(1, len(order) // 50)):
        worst = min(worst, ratio(set(order[:k])))
        tests += 1
    need(worst >= 1 / 163840, 'cut below claimed constant')
    res['cut_tests'] = tests
    res['min_observed_cut_ratio'] = round(worst, 6)
    return res


def main():
    out = {'limits': LIMITS, 'frame': frame_checks()}
    out['toy_small'] = toy_checks(seed=11, nh=1, nv=2, nsites=2, nsquares=0, cut_trials=200)
    out['toy_a'] = toy_checks(seed=3, nh=3, nv=3, nsites=3, nsquares=2, cut_trials=300)
    out['toy_b'] = toy_checks(seed=5, nh=3, nv=3, nsites=2, nsquares=3, cut_trials=300)
    out['status'] = 'PASS_FINITE_DIAGNOSTICS'
    print(json.dumps(out, sort_keys=True, indent=1))


if __name__ == '__main__':
    main()
