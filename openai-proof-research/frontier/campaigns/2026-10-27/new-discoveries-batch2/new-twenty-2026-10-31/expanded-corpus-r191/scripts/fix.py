# Independent implementation of Cranston-Rabern (L,P)-fixability (arXiv:1507.05600, Definition 1)
# and superabundance (Section 2.3), for MathDB 330961 / 330962 / 330963 diagnostics.
#
# State: tuple of colour bitmasks L(v) (v = 0..m-1); pot P = [k] (fixability is monotone in P).
# Fixable = least fixed point: W0 = L-edge-colourable states; L in W_{h+1} iff L in W_h or there are
# distinct a,b in P such that for every partition X_1..X_t of S_{L,a,b} into parts of size <= 2 there
# is J with L' (swap a,b at the vertices of the parts in J) in W_h.
#
# Modes:
#   python3 -I fix.py closure GRAPH LISTS k        -> fixability of one assignment via its swap closure
#   python3 -I fix.py exhaust GRAPH SIZES k OUT    -> all assignments with the given list sizes and pot in [k]
# GRAPH: JSON list of edges [[u,v],...] (multi-edges allowed by repetition); LISTS: JSON list of lists;
# SIZES: JSON list of list sizes.
import sys, json, itertools, time

def partitions_small(s):
    """All partitions of range(s) into parts of size 1 or 2, as lists of bitmasks."""
    res = []
    def rec(rem, acc):
        if not rem:
            res.append(list(acc)); return
        x = rem[0]; rest = rem[1:]
        rec(rest, acc + [1 << x])
        for i, y in enumerate(rest):
            rec(rest[:i] + rest[i + 1:], acc + [(1 << x) | (1 << y)])
    rec(list(range(s)), [])
    return res

UNION = {}
SUBMASKS = {}
def union_masks(s):
    """For each partition of range(s): a 2^s-bit integer whose bit U is set iff U is a union of parts."""
    if s in UNION: return UNION[s]
    out = []
    for parts in partitions_small(s):
        bits = 0
        for J in range(1 << len(parts)):
            U = 0
            for i, p in enumerate(parts):
                if (J >> i) & 1: U |= p
            bits |= 1 << U
        out.append(bits)
    UNION[s] = out
    return out

class Solver:
    """States are canonical: sorted tuple of k colour-membership vectors (bit v set iff colour in L(v))."""
    def __init__(self, edges, k):
        self.edges = [tuple(e) for e in edges]
        self.m = 1 + max(max(e) for e in self.edges)
        self.k = k
        E = len(self.edges); subs = []
        for mask in range(1, 1 << E):
            es = [self.edges[i] for i in range(E) if (mask >> i) & 1]
            vs = set(x for e in es for x in e)
            comp = {es[0][0]}; ch = True
            while ch:
                ch = False
                for (u, v) in es:
                    if (u in comp) != (v in comp):
                        comp |= {u, v}; ch = True
            if comp == vs:
                subs.append((sum(1 << x for x in vs), len(es)))
        self.subs = subs
        self.cache_col = {}

    def from_lists(self, lists):
        return tuple(sorted(sum(1 << v for v in range(self.m) if c in lists[v]) for c in range(self.k)))

    def to_lists(self, st):
        return [[c for c in range(self.k) if (st[c] >> v) & 1] for v in range(self.m)]

    def colourable(self, st):
        E = len(self.edges); k = self.k
        used = [0] * self.m  # bitmask over colour indices
        def rec(t):
            if t == E: return True
            u, v = self.edges[t]
            for c in range(k):
                x = st[c]
                if (x >> u) & 1 and (x >> v) & 1 and not (used[u] >> c) & 1 and not (used[v] >> c) & 1:
                    if c > 0 and st[c - 1] == x and not ((used[u] >> (c - 1)) & 1 or (used[v] >> (c - 1)) & 1):
                        # symmetry: among identical colours, try the first unused one only
                        pass
                    used[u] |= 1 << c; used[v] |= 1 << c
                    if rec(t + 1): return True
                    used[u] ^= 1 << c; used[v] ^= 1 << c
            return False
        return rec(0)

    def psi(self, st, vmask):
        return sum(bin(x & vmask).count('1') // 2 for x in st)

    def superabundant(self, st):
        return all(self.psi(st, vm) >= ne for vm, ne in self.subs)

    def moves(self, st):
        res = []; seenpairs = set()
        k = self.k
        for i in range(k):
            for j in range(i + 1, k):
                x, y = st[i], st[j]
                if (x, y) in seenpairs: continue
                seenpairs.add((x, y))
                Sm = x ^ y
                ums = SUBMASKS.get(Sm)
                if ums is None:
                    bits = [v for v in range(self.m) if (Sm >> v) & 1]
                    ums = []
                    for U in range(1 << len(bits)):
                        Um = 0
                        for t, v in enumerate(bits):
                            if (U >> t) & 1: Um |= 1 << v
                        ums.append(Um)
                    SUBMASKS[Sm] = ums
                rest = st[:i] + st[i + 1:j] + st[j + 1:]
                outs = [tuple(sorted(rest + (x ^ Um, y ^ Um))) for Um in ums]
                res.append((bin(Sm).count('1'), outs))
        return res

    def solve(self, states):
        states = list(states)
        h = {}
        for L in states:
            h[L] = 0 if self.colourable(L) else None
        pending = [L for L in states if h[L] is None]
        mv = {L: self.moves(L) for L in pending}
        level = 0
        while True:
            level += 1
            won = []
            for L in pending:
                for s, outs in mv[L]:
                    good = 0
                    for U, L2 in enumerate(outs):
                        if h.get(L2) is not None: good |= 1 << U
                    if good and all(good & um for um in union_masks(s)):
                        won.append(L); break
            if not won: break
            for L in won: h[L] = level
            ws = set(won)
            pending = [L for L in pending if L not in ws]
        return h

def closure(solver, L0):
    seen = {L0}; st = [L0]
    while st:
        L = st.pop()
        for s, outs in solver.moves(L):
            for L2 in outs:
                if L2 not in seen:
                    seen.add(L2); st.append(L2)
    return seen

def all_states(solver, sizes):
    """All canonical states (multisets of k vectors) whose vertex v lies in exactly sizes[v] vectors."""
    m = solver.m; k = solver.k; vecs = list(range(1 << m)); out = []
    def rec(idx, start, cnt, acc):
        if idx == k:
            if cnt == list(sizes): out.append(tuple(acc))
            return
        left = k - idx
        for t in range(start, len(vecs)):
            x = vecs[t]; nc = [cnt[v] + ((x >> v) & 1) for v in range(m)]
            if any(nc[v] > sizes[v] or nc[v] + 0 < sizes[v] - (left - 1) * 1 for v in range(m)):
                continue
            rec(idx + 1, t, nc, acc + [x])
    rec(0, 0, [0] * m, [])
    return out

def main():
    mode = sys.argv[1]
    edges = json.loads(sys.argv[2])
    if mode == 'closure':
        lists = json.loads(sys.argv[3]); k = int(sys.argv[4])
        S = Solver(edges, k)
        L0 = S.from_lists(lists)
        cl = closure(S, L0); t = time.time(); h = S.solve(cl)
        print(json.dumps(dict(mode=mode, edges=edges, lists=lists, k=k, closure=len(cl),
            superabundant=S.superabundant(L0), colourable=S.colourable(L0), height=h[L0], secs=round(time.time() - t, 2))))
    elif mode == 'exhaust':
        sizes = json.loads(sys.argv[3]); k = int(sys.argv[4]); outf = sys.argv[5]
        S = Solver(edges, k)
        states = all_states(S, sizes)
        t = time.time(); h = S.solve(states)
        E = len(edges); full = (1 << S.m) - 1
        bad = []; nsup = 0; lemma22_viol = 0
        for L in states:
            sa = S.superabundant(L)
            if not sa and h[L] is not None: lemma22_viol += 1
            if sa:
                nsup += 1
                if h[L] is None:
                    bad.append(dict(lists=S.to_lists(L), psi=S.psi(L, full)))
        res = dict(mode=mode, edges=edges, sizes=sizes, k=k, states=len(states), superabundant=nsup,
                   superabundant_not_fixable=len(bad), fixable_not_superabundant=lemma22_viol, max_height=max((v for v in h.values() if v is not None), default=0),
                   secs=round(time.time() - t, 2), examples=bad[:20],
                   bad_with_psi_gt_E=sum(1 for b in bad if b['psi'] > E))
        print(json.dumps({x: res[x] for x in res if x != 'examples'}))
        if bad: print('EXAMPLE', json.dumps(bad[0]))
        with open(outf, 'w') as f: json.dump(res, f)

def sweep(edges, k, outf, budget, profiles):
    # profiles: list of size lists. Runs each exhaustively until the time budget is spent.
    t0 = time.time(); S = Solver(edges, k); E = len(edges); full = (1 << S.m) - 1; recs = []
    for sizes in profiles:
        if time.time() - t0 > budget: recs.append(dict(sizes=sizes, skipped='budget')); continue
        states = all_states(S, sizes); h = S.solve(states)
        bad = [L for L in states if h[L] is None and S.superabundant(L)]
        viol = sum(1 for L in states if h[L] is not None and not S.superabundant(L))
        nsup = sum(1 for L in states if S.superabundant(L))
        r = dict(sizes=sizes, states=len(states), superabundant=nsup, superabundant_not_fixable=len(bad),
                 bad_with_psi_gt_E=sum(1 for L in bad if S.psi(L, full) > E),
                 bad_profile_counts=sorted(set(tuple(bin(x).count('1') for x in L) for L in bad))[:3],
                 fixable_not_superabundant=viol, max_height=max((v for v in h.values() if v is not None), default=0),
                 examples=[dict(lists=S.to_lists(L), psi=S.psi(L, full)) for L in bad[:5]])
        recs.append(r)
        print(json.dumps({x: r[x] for x in r if x != 'examples'}), flush=True)
        if bad: print('EXAMPLE', json.dumps(r['examples'][0]), flush=True)
    with open(outf, 'w') as f: json.dump(dict(edges=edges, k=k, budget=budget, results=recs), f)

if __name__ == '__main__':
    if sys.argv[1] == 'sweep':
        sweep(json.loads(sys.argv[2]), int(sys.argv[3]), sys.argv[4], float(sys.argv[5]), json.loads(sys.argv[6]))
    else:
        main()
