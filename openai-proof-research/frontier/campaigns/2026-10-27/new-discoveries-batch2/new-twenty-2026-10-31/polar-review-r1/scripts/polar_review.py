#!/usr/bin/env python3
"""Independent (infinity,k)-polarity code for cographs -- polar-review-r1.

Written from scratch by the reviewer; does not import or execute any discovery-lane script.

Cographs are represented by canonical cotrees (nested tuples):
  LEAF = ('L',)
  ('U', c1, ..., cm)  disjoint union, m >= 2, children are LEAF or 'J'-nodes, sorted
  ('J', c1, ..., cm)  join,           m >= 2, children are LEAF or 'U'-nodes, sorted
Canonical cotrees are unique per isomorphism class (Corneil-Lerchs-Stewart), so isomorphism
of cographs = equality of canonical tuples.

Polarity DP. A partition (A,B) is summarised by
  a in {0: A empty, 1: A nonempty edgeless, 2: A complete multipartite with an edge}
  b in {0: B empty, 1: B a single nonempty clique, 2: B a cluster with >= 2 cliques}
and the table maps (a,b) -> minimum number of cliques of B.  Rules (proved in REVIEW.md, sec. B.3):
  union: A-sides X+Y is CM iff one side empty or both edgeless; clusters add.
  join : A-sides X(+)Y is CM iff both CM (always, given validity);  B-sides X(+)Y is a cluster
         iff one side empty or both are single cliques (result: one clique).
G is (inf,k)-polar iff min table value <= k; (1,k)-polar iff min over a in {0,1} <= k.

Subcommands (each writes its own log/JSON with open(...,'x'), never overwriting):
  selftest NMAX_BRUTE LOG
  census NMAX KMAX OUTJSON
  structured QMIN QMAX KMAX OUTJSON
  lemmas QMAX OUTJSON
"""
import itertools, json, sys, time
from functools import lru_cache

LEAF = ('L',)
EMPTY = None

# ---------------------------------------------------------------- canonical builders
def make(kind, children):
    """Normalise: drop EMPTY, flatten same-kind children, collapse singletons, sort."""
    flat = []
    for ch in children:
        if ch is EMPTY:
            continue
        if ch[0] == kind:
            flat.extend(ch[1:])
        else:
            flat.append(ch)
    if not flat:
        return EMPTY
    if len(flat) == 1:
        return flat[0]
    return (kind,) + tuple(sorted(flat))

def union(*gs): return make('U', gs)
def join(*gs): return make('J', gs)
def K(n): return join(*([LEAF] * n)) if n > 1 else (LEAF if n == 1 else EMPTY)
def Kbar(n): return union(*([LEAF] * n)) if n > 1 else (LEAF if n == 1 else EMPTY)
def Kab(a, b): return join(Kbar(a), Kbar(b))
def times(n, g): return union(*([g] * n))

@lru_cache(maxsize=None)
def order(t):
    if t is EMPTY: return 0
    if t == LEAF: return 1
    return sum(order(c) for c in t[1:])

def ctype(t):
    """(number of components, number of isolated vertices)."""
    if t is EMPTY: return (0, 0)
    if t == LEAF: return (1, 1)
    if t[0] == 'J': return (1, 0)
    return (len(t) - 1, sum(1 for c in t[1:] if c == LEAF))

# ---------------------------------------------------------------- enumeration
def partitions(n, maxpart):
    """integer partitions of n as nonincreasing lists with parts <= maxpart."""
    if n == 0:
        yield []; return
    for p in range(min(n, maxpart), 0, -1):
        for rest in partitions(n - p, p):
            yield [p] + rest

def multisets(bysize, n):
    """All multisets (>= 2 members) of trees from bysize[s] with total order n."""
    out = []
    for part in partitions(n, n - 1):          # >= 2 parts since parts <= n-1
        groups = [(s, part.count(s)) for s in sorted(set(part))]
        choices = [list(itertools.combinations_with_replacement(bysize[s], m)) for s, m in groups]
        for combo in itertools.product(*choices):
            out.append(tuple(x for grp in combo for x in grp))
    return out

def enumerate_cographs(nmax):
    """Return CONN[n], COCONN[n] lists of canonical cotrees, n = 1..nmax."""
    CONN = {1: [LEAF]}; COCONN = {1: [LEAF]}
    for n in range(2, nmax + 1):
        CONN[n] = [('J',) + tuple(sorted(ms)) for ms in multisets(COCONN, n)]
        COCONN[n] = [('U',) + tuple(sorted(ms)) for ms in multisets(CONN, n)]
    return CONN, COCONN

# ---------------------------------------------------------------- polarity DP
def _ua(a1, a2):
    if a1 == 0: return a2
    if a2 == 0: return a1
    if a1 == 1 and a2 == 1: return 1
    return None

def _ub(b1, b2):
    if b1 == 0: return b2
    if b2 == 0: return b1
    return 2

def t_union(T1, T2):
    out = {}
    for (a1, b1), c1 in T1.items():
        for (a2, b2), c2 in T2.items():
            a = _ua(a1, a2)
            if a is None: continue
            key = (a, _ub(b1, b2)); c = c1 + c2
            if c < out.get(key, 1 << 30): out[key] = c
    return out

def t_join(T1, T2):
    out = {}
    for (a1, b1), c1 in T1.items():
        for (a2, b2), c2 in T2.items():
            a = a2 if a1 == 0 else (a1 if a2 == 0 else 2)
            if b1 == 0: b, c = b2, c2
            elif b2 == 0: b, c = b1, c1
            elif b1 == 1 and b2 == 1: b, c = 1, 1
            else: continue
            key = (a, b)
            if c < out.get(key, 1 << 30): out[key] = c
    return out

LEAF_T = {(1, 0): 0, (0, 1): 1}
EMPTY_T = {(0, 0): 0}

_TAB = {}
def table(t):
    if t is EMPTY: return EMPTY_T
    if t == LEAF: return LEAF_T
    r = _TAB.get(t)
    if r is not None: return r
    f = t_union if t[0] == 'U' else t_join
    acc = table(t[1])
    for ch in t[2:]:
        acc = f(acc, table(ch))
    _TAB[t] = acc
    return acc

def minval(t):
    """least k with t (inf,k)-polar."""
    return min(table(t).values(), default=1 << 30)

def minval1(t):
    """least k with t (1,k)-polar."""
    return min((v for (a, b), v in table(t).items() if a <= 1), default=1 << 30)

def summary(t):
    """(m0,m1,m2): min #cliques of B over partitions with A-state a (inf if none)."""
    INF = 1 << 30
    m = [INF, INF, INF]
    for (a, b), v in table(t).items():
        if v < m[a]: m[a] = v
    return tuple(m)

def union_min(s1, s2):
    """min #cliques of B for a disjoint union, from the two summaries."""
    best = 1 << 30
    for a1 in range(3):
        for a2 in range(3):
            if _ua(a1, a2) is None: continue
            v = s1[a1] + s2[a2]
            if v < best: best = v
    return best

# ---------------------------------------------------------------- one-vertex deletions
_DEL = {}
def dels(t):
    """set of canonical cotrees t - v over all leaves v (EMPTY allowed)."""
    if t == LEAF: return frozenset([EMPTY])
    r = _DEL.get(t)
    if r is not None: return r
    kind = t[0]; ch = t[1:]
    res = set()
    seen = set()
    for j, c in enumerate(ch):
        if c in seen: continue
        seen.add(c)
        rest = ch[:j] + ch[j + 1:]
        for d in dels(c):
            res.add(make(kind, rest + (d,)))
    r = frozenset(res)
    _DEL[t] = r
    return r

# ---------------------------------------------------------------- explicit graphs / brute force
def to_graph(t):
    """labelled graph: (n, adjacency sets)."""
    adj = []
    def build(t):
        if t == LEAF:
            adj.append(set()); return [len(adj) - 1]
        parts = [build(c) for c in t[1:]]
        if t[0] == 'J':
            for x, y in itertools.combinations(range(len(parts)), 2):
                for u in parts[x]:
                    for v in parts[y]:
                        adj[u].add(v); adj[v].add(u)
        return [v for p in parts for v in p]
    if t is not EMPTY: build(t)
    return len(adj), adj

def is_p4free(n, adj):
    for a, b, c, d in itertools.permutations(range(n), 4):
        if b in adj[a] and c in adj[b] and d in adj[c] and c not in adj[a] and d not in adj[b] and d not in adj[a]:
            return False
    return True

def brute_minvals(n, adj):
    """(least k: (inf,k)-polar, least k: (1,k)-polar) by trying all 2^n subsets A."""
    best_inf = best_one = 1 << 30
    for mask in range(1 << n):
        A = [v for v in range(n) if mask >> v & 1]
        B = [v for v in range(n) if not mask >> v & 1]
        # A complete multipartite: non-adjacency transitive on distinct vertices
        cm = all(not (y not in adj[x] and z not in adj[y] and z in adj[x])
                 for x, y, z in itertools.permutations(A, 3))
        if not cm: continue
        edgeless = all(y not in adj[x] for x, y in itertools.combinations(A, 2))
        # B cluster: adjacency transitive
        cl = all(not (y in adj[x] and z in adj[y] and z not in adj[x])
                 for x, y, z in itertools.permutations(B, 3))
        if not cl: continue
        # components of B
        Bs = set(B); comp = 0; seen = set()
        for v in B:
            if v in seen: continue
            comp += 1; stack = [v]; seen.add(v)
            while stack:
                u = stack.pop()
                for w in adj[u]:
                    if w in Bs and w not in seen:
                        seen.add(w); stack.append(w)
        best_inf = min(best_inf, comp)
        if edgeless: best_one = min(best_one, comp)
    return best_inf, best_one

def brute_canon(n, adj):
    best = None
    for p in itertools.permutations(range(n)):
        key = tuple(sorted((min(p[u], p[v]), max(p[u], p[v])) for u in range(n) for v in adj[u] if u < v))
        if best is None or key < best: best = key
    return best

# ---------------------------------------------------------------- normal forms
def P(k, c, i):
    """Candidate normal form P(k,c,i) = iK1 + (c-i-1)K2 + X."""
    if c == k + 2: X = Kab(i, i)
    elif c == k + 1: X = join(Kbar(2), union(K(2), Kbar(i)))
    else: X = join(LEAF, union(times(k - c + 2, K(2)), Kbar(i)))
    return union(Kbar(i), times(c - i - 1, K(2)), X)

def in_range(k, c, i):
    return 1 <= i <= c - 2 <= k

def show(t):
    if t is EMPTY: return '0'
    if t == LEAF: return 'K1'
    if all(c == LEAF for c in t[1:]):
        m = len(t) - 1
        return f'K{m}' if t[0] == 'J' else f'{m}K1'
    parts = []
    for c in sorted(set(t[1:]), key=lambda x: (order(x), x)):
        mult = t[1:].count(c); s = show(c)
        if c != LEAF and not (c[0] == 'J' and all(x == LEAF for x in c[1:])) and mult == 1 and len(t) > 2:
            s = '(' + s + ')'
        if mult > 1:
            s = f'{mult}' + (s if (c == LEAF or (c[0] == 'J' and all(x == LEAF for x in c[1:]))) else '(' + s + ')')
        parts.append(s)
    return (' + ' if t[0] == 'U' else ' (+) ').join(parts)

def openx(path):
    return open(path, 'x')

# ---------------------------------------------------------------- subcommands
def cmd_selftest(nbrute, logpath):
    log = openx(logpath)
    def p(*a):
        s = ' '.join(str(x) for x in a); print(s); log.write(s + '\n'); log.flush()
    t0 = time.time()
    CONN, COCONN = enumerate_cographs(12)
    counts = [1] + [len(CONN[n]) + len(COCONN[n]) for n in range(2, 13)]
    p('cograph counts n=1..12:', counts)
    p('connected counts n=1..12:', [len(CONN[n]) for n in range(1, 13)])
    known = [1, 2, 4, 10, 24, 66, 180, 522, 1532, 4624, 14136, 43930]
    p('match standard unlabelled cograph counts 1,2,4,10,...,43930:', counts == known)
    # canonical forms are distinct and P4-free; DP vs brute force
    bad = 0; checked = 0
    for n in range(1, nbrute + 1):
        allt = CONN[n] + (COCONN[n] if n > 1 else [])
        assert len(set(allt)) == len(allt)
        for t in allt:
            nn, adj = to_graph(t)
            assert nn == n
            if n <= 7 and not is_p4free(nn, adj): p('NOT P4-free', t); bad += 1
            bi, bo = brute_minvals(nn, adj)
            if bi != minval(t) or bo != minval1(t):
                p('DP MISMATCH', show(t), bi, minval(t), bo, minval1(t)); bad += 1
            # deletions agree with explicit vertex deletion (brute iso for n<=6)
            checked += 1
        p(f'n={n}: {len(allt)} cographs, DP==brute (inf and 1), cumulative bad={bad}, t={time.time()-t0:.1f}s')
    # completeness for n<=5: every labelled P4-free graph is isomorphic to a generated one
    for n in range(1, 6):
        gen = set(brute_canon(*to_graph(t)) for t in (CONN[n] + (COCONN[n] if n > 1 else [])))
        pairs = list(itertools.combinations(range(n), 2)); found = set()
        for mask in range(1 << len(pairs)):
            adj = [set() for _ in range(n)]
            for j, (u, v) in enumerate(pairs):
                if mask >> j & 1: adj[u].add(v); adj[v].add(u)
            if is_p4free(n, adj): found.add(brute_canon(n, adj))
        p(f'n={n}: labelled P4-free iso classes={len(found)}, generated={len(gen)}, equal={found == gen}')
        bad += (found != gen)
    # deletion routine vs explicit deletion for n<=6
    for n in range(2, 7):
        for t in CONN[n] + COCONN[n]:
            nn, adj = to_graph(t)
            exp = set()
            for v in range(nn):
                keep = [u for u in range(nn) if u != v]; idx = {u: j for j, u in enumerate(keep)}
                a2 = [set(idx[w] for w in adj[u] if w != v) for u in keep]
                exp.add(brute_canon(nn - 1, a2))
            got = set(brute_canon(*to_graph(d)) if d is not EMPTY else () for d in dels(t))
            if exp != got: p('DEL MISMATCH', show(t)); bad += 1
    p('deletion routine == explicit deletion for all cographs n<=6 :', bad == 0)
    p('TOTAL BAD', bad, f'time {time.time()-t0:.1f}s')
    log.close()

def cmd_census(nmax, kmax, outpath):
    out = openx(outpath)
    t0 = time.time()
    CONN, COCONN = enumerate_cographs(nmax)
    obs = {k: [] for k in range(kmax + 1)}
    ngraphs = 0
    for n in range(1, nmax + 1):
        allt = CONN[n] + (COCONN[n] if n > 1 else [])
        for t in allt:
            ngraphs += 1
            mv = minval(t)
            if mv == 0: continue
            md = max(minval(d) if d is not EMPTY else 0 for d in dels(t))
            for k in range(md, min(mv - 1, kmax) + 1):
                obs[k].append(t)
        print(f'n={n} done, {len(allt)} graphs, {time.time()-t0:.1f}s', flush=True)
    res = {'nmax': nmax, 'kmax': kmax, 'graphs_enumerated': ngraphs, 'per_k': {}}
    for k in range(kmax + 1):
        bytype = {}
        for t in obs[k]:
            bytype.setdefault(str(ctype(t)), []).append({'order': order(t), 'graph': show(t)})
        conj = {}
        for c in range(3, k + 3):
            for i in range(1, c - 1):
                pk = P(k, c, i)
                found = [t for t in obs[k] if ctype(t) == (c, i)]
                conj[f'({c},{i})'] = {
                    'P_order': order(pk), 'P_within_nmax': order(pk) <= nmax,
                    'P_is_obstruction_found': pk in found, 'P': show(pk),
                    'found_count': len(found), 'found': [show(t) for t in found],
                    'ok': (found == [pk]) if order(pk) <= nmax else (found == [])}
        res['per_k'][k] = {'total': len(obs[k]), 'max_order': max((order(t) for t in obs[k]), default=0),
                           'type_counts': {ty: len(v) for ty, v in sorted(bytype.items())},
                           'conjecture_range': conj, 'all_ok': all(v['ok'] for v in conj.values()),
                           'list': bytype}
        print(f'k={k}: total={len(obs[k])} type_counts={res["per_k"][k]["type_counts"]} '
              f'conj_range_all_ok={res["per_k"][k]["all_ok"]}', flush=True)
    res['seconds'] = round(time.time() - t0, 1)
    json.dump(res, out, indent=1); out.close()
    print('wrote', outpath)

def cmd_structured(qmin, qmax, kmax, outpath):
    """Exhaustive over G = iK1 + sum K_{s_j} + Q (Q connected non-complete cograph, |Q| in
    [qmin,qmax], s_j in {2,3}) and clusters G = iK1 + sum K_{s_j} (s_j in {2,3,4}), for all
    admissible (k,c,i) with k <= kmax.  Coverage of all obstructions of type (c,i), i>=1, with
    |Q| in range rests on Lemma 2 (<= 1 non-complete component); s_j <= 3 tests Lemma 4."""
    out = openx(outpath)
    t0 = time.time()
    CONN, _ = enumerate_cographs(qmax)
    types = [(k, c, i) for k in range(1, kmax + 1) for c in range(3, k + 3) for i in range(1, c - 1)]
    # rests R = iK1 + sum K_s ; record summary and summaries of R - v
    rests = {}
    for i in range(1, kmax + 1):
        for r in range(0, kmax + 2):
            for sizes in itertools.combinations_with_replacement((2, 3), r):
                R = union(Kbar(i), *[K(s) for s in sizes])
                rd = set(summary(d) for d in dels(R))
                rests[(i, sizes)] = (summary(R), rd)
    found = {t: [] for t in types}
    nQ = 0; groups = {}
    for n in range(max(3, qmin), qmax + 1):
        for Q in CONN[n]:
            if all(c == LEAF for c in Q[1:]): continue  # complete
            nQ += 1
            key = (summary(Q), frozenset(summary(d) for d in dels(Q)))
            groups.setdefault(key, []).append(Q)
        print(f'|Q|={n}: cumulative non-complete connected Q={nQ}, groups={len(groups)}, {time.time()-t0:.1f}s', flush=True)
    for (sQ, sdQ), Qs in groups.items():
        for (i, sizes), (sR, sdR) in rests.items():
            v0 = union_min(sQ, sR)
            vmax = max(max(union_min(d, sR) for d in sdQ), max(union_min(sQ, d) for d in sdR))
            if vmax >= v0: continue
            c = 1 + i + len(sizes)
            for k in range(vmax, min(v0 - 1, kmax) + 1):
                if (k, c, i) in found:
                    for Q in Qs:
                        found[(k, c, i)].append(union(Kbar(i), *[K(s) for s in sizes], Q))
    # cluster case
    for k, c, i in types:
        for sizes in itertools.combinations_with_replacement((2, 3, 4), c - i):
            G = union(Kbar(i), *[K(s) for s in sizes])
            mv = minval(G); md = max(minval(d) for d in dels(G))
            if md <= k < mv: found[(k, c, i)].append(G)
    res = {'qmin': qmin, 'qmax': qmax, 'kmax': kmax, 'nonComplete_connected_Q': nQ,
           'distinct_summary_groups': len(groups), 'types': {}}
    allok = True
    for (k, c, i) in types:
        pk = P(k, c, i); qord = order(pk) - i - 2 * (c - i - 1)
        lst = found[(k, c, i)]
        inwin = (qmin <= qord <= qmax) or (c == k + 2 and i == 1)
        ok = (lst == [pk]) if inwin else (lst == [])
        allok &= ok
        res['types'][f'k={k},(c,i)=({c},{i})'] = {'P': show(pk), 'P_order': order(pk), 'Q_order_of_P': qord,
            'found': [show(t) for t in lst], 'ok': ok,
            'source_settled': c >= k, 'open_before': c <= k - 1}
        print(f'k={k} (c,i)=({c},{i}) found={len(lst)} ok={ok} {"OPEN-TYPE" if c <= k-1 else ""}', flush=True)
    res['all_ok'] = allok; res['seconds'] = round(time.time() - t0, 1)
    json.dump(res, out, indent=1); out.close()
    print('ALL_OK', allok, 'wrote', outpath, f'{time.time()-t0:.1f}s')

def is_edgeless_tree(t):
    return t == LEAF or (t[0] == 'U' and all(c == LEAF for c in t[1:]))

def cluster_cliques(t):
    """number of cliques if t is a cluster, else None."""
    def isclique(x): return x == LEAF or (x[0] == 'J' and all(c == LEAF for c in x[1:]))
    if isclique(t): return 1
    if t[0] == 'U' and all(isclique(c) for c in t[1:]): return len(t) - 1
    return None

def cmd_lemmas(qmax, outpath):
    out = openx(outpath); t0 = time.time(); res = {}
    CONN, COCONN = enumerate_cographs(qmax)
    # Lemma 5: connected Q, (1,l+1)-polar and not (1,l)-polar, l>=1  =>  Q = Kbar_a (+) C, C cluster, l+1 cliques
    n5 = 0; bad5 = []
    for n in range(2, qmax + 1):
        for Q in CONN[n]:
            m1 = minval1(Q)  # least l with (1,l)-polar (1<<30 if not (1,inf)-polar)
            if m1 >= 1 << 30: continue   # first run (outputs-lemmas-Q13.json) lacked this guard
            l = m1 - 1
            if l < 1: continue
            n5 += 1
            ok = False
            if Q[0] == 'J' and len(Q) == 3:
                X, Y = Q[1], Q[2]
                for A, B in ((X, Y), (Y, X)):
                    if is_edgeless_tree(A) and cluster_cliques(B) == l + 1: ok = True
            if not ok: bad5.append(show(Q))
    res['lemma5'] = {'instances': n5, 'violations': bad5}
    print('Lemma5 instances', n5, 'violations', len(bad5), flush=True)
    # Lemma 6
    n6 = 0; bad6 = []
    for a in range(1, 7):
        for m in range(2, 7):
            for sizes in itertools.combinations_with_replacement((1, 2, 3, 4), m):
                beta = sum(1 for s in sizes if s >= 2)
                Q = join(Kbar(a), union(*[K(s) for s in sizes]))
                T = table(Q)
                for p in range(0, m + 3):
                    inf_dp = min(T.values()) <= p
                    inf_f = min(beta, m - 1) <= p
                    n6 += 1
                    if inf_dp != inf_f: bad6.append(('inf', a, sizes, p))
                    if 1 <= p <= m - 1:
                        one_dp = minval1(Q) <= p
                        one_f = (a == 1 and beta <= 1) or (beta == 0 and a <= p)
                        n6 += 1
                        if one_dp != one_f: bad6.append(('one', a, sizes, p))
    res['lemma6'] = {'instances': n6, 'violations': bad6}
    print('Lemma6 instances', n6, 'violations', len(bad6), flush=True)
    # Lemma 1 (clusters) and Lemma 3 (criterion)
    n1 = 0; bad1 = []
    for c in range(1, 8):
        for sizes in itertools.combinations_with_replacement((1, 2, 3, 4), c):
            G = union(*[K(s) for s in sizes]); rp = sum(1 for s in sizes if s >= 2)
            for k in range(0, 9):
                n1 += 1
                if (minval(G) <= k) != (min(rp, c - 1) <= k): bad1.append((sizes, k))
    res['lemma1'] = {'instances': n1, 'violations': bad1}
    n3 = 0; bad3 = []
    for n in range(3, min(qmax, 9) + 1):
        for Q in CONN[n]:
            if all(c == LEAF for c in Q[1:]): continue
            for i in range(0, 4):
                for sizes in itertools.combinations_with_replacement((2, 3), 3):
                    for r in range(0, 4):
                        G = union(Kbar(i), *[K(s) for s in sizes[:r]], Q)
                        for k in range(0, 9):
                            n3 += 1
                            lhs = minval(G) <= k
                            rhs = (minval1(Q) <= k - r) or (minval(Q) <= k - r - i)
                            if lhs != rhs: bad3.append((show(G), k))
    res['lemma3'] = {'instances': n3, 'violations': bad3[:20], 'violation_count': len(bad3)}
    print('Lemma1 instances', n1, 'violations', len(bad1), '; Lemma3 instances', n3, 'violations', len(bad3))
    res['seconds'] = round(time.time() - t0, 1)
    json.dump(res, out, indent=1); out.close()
    print('wrote', outpath)

if __name__ == '__main__':
    sys.setrecursionlimit(10000)
    cmd = sys.argv[1]
    if cmd == 'selftest': cmd_selftest(int(sys.argv[2]), sys.argv[3])
    elif cmd == 'census': cmd_census(int(sys.argv[2]), int(sys.argv[3]), sys.argv[4])
    elif cmd == 'structured': cmd_structured(int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]), sys.argv[5])
    elif cmd == 'lemmas': cmd_lemmas(int(sys.argv[2]), sys.argv[3])
    else: sys.exit('unknown')
