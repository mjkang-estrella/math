"""Independent review library for MathDB 372205 (XOR-magic regular graphs).

Written from scratch for xor-magic-review-r1; it does not import or copy the
focused lane's scripts.  All checks use exact integer arithmetic.

Conventions.  A graph on N = 2^n vertices is "identity labelled": vertex v
carries the label v read as an n-bit vector, so XOR of labels is integer XOR.
F4 = F2[w]/(w^2+w+1) is encoded by integers 0..3, bit 0 = coefficient of 1,
bit 1 = coefficient of w; addition is XOR.  A lifted vertex (u, x) is 4u + x,
so its label is (label(u), x) and the lift is again identity labelled.
"""
import random
from collections import deque

# ---------- F4 arithmetic (own tables, checked by f4_selftest) ----------
W, W2 = 2, 3
def f4mul(a, b):
    # (a0 + a1 w)(b0 + b1 w) with w^2 = w + 1
    a0, a1, b0, b1 = a & 1, a >> 1, b & 1, b >> 1
    c0 = (a0 & b0) ^ (a1 & b1)
    c1 = (a0 & b1) ^ (a1 & b0) ^ (a1 & b1)
    return c0 | (c1 << 1)
MUL = [[f4mul(a, b) for b in range(4)] for a in range(4)]
INV = {1: 1, W: W2, W2: W}
def f4_selftest():
    assert MUL[W][W] == W2 and MUL[W][W2] == 1 and MUL[W2][W2] == W
    assert W ^ W2 == 1                      # w + w^-1 = 1
    assert 0 ^ 1 ^ W ^ W2 == 0              # sum of F4 is zero
    for a in range(4):
        for b in range(4):
            for c in range(4):
                assert MUL[a][b ^ c] == MUL[a][b] ^ MUL[a][c]
                assert MUL[MUL[a][b]][c] == MUL[a][MUL[b][c]]
    for a in (1, W, W2):
        assert MUL[a][INV[a]] == 1
    return True

# ---------- graph checks ----------
def adjacency(N, edges):
    adj = [set() for _ in range(N)]
    for u, v in edges:
        adj[u].add(v); adj[v].add(u)
    return adj

def components(N, adj):
    seen = [False] * N; comps = 0
    for s in range(N):
        if seen[s]: continue
        comps += 1; seen[s] = True; q = deque([s])
        while q:
            x = q.popleft()
            for y in adj[x]:
                if not seen[y]: seen[y] = True; q.append(y)
    return comps

def check_graph(N, edges, closed):
    """Full literal check of the source definition for an identity-labelled graph."""
    r = {"N": N, "closed": closed, "edges": len(edges)}
    assert N >= 1 and N & (N - 1) == 0
    keys = set(); loops = dups = oob = 0
    for u, v in edges:
        if not (0 <= u < N and 0 <= v < N): oob += 1; continue
        if u == v: loops += 1; continue
        k = (min(u, v), max(u, v))
        if k in keys: dups += 1
        keys.add(k)
    adj = adjacency(N, keys)
    degs = {len(a) for a in adj}
    sums_ok = True
    for v in range(N):
        s = v if closed else 0
        for y in adj[v]: s ^= y
        if s != 0: sums_ok = False; break
    r.update(loops=loops, duplicates=dups, out_of_range=oob, simple=(loops == 0 and dups == 0 and oob == 0),
             degrees=sorted(degs), regular=(len(degs) == 1), degree=(min(degs) if len(degs) == 1 else None),
             zero_sums=sums_ok, components=components(N, adj))
    r["connected"] = r["components"] == 1
    r["ok"] = r["simple"] and r["regular"] and r["zero_sums"] and r["connected"]
    return r

def complement(N, edges):
    keys = {(min(u, v), max(u, v)) for u, v in edges}
    return [(u, v) for u in range(N) for v in range(u + 1, N) if (u, v) not in keys]

def is_perfect_matching(N, M):
    seen = set()
    for u, v in M:
        if u == v or u in seen or v in seen: return False
        seen.add(u); seen.add(v)
    return len(seen) == N

def check_decomposition(N, edges, factors):
    """factors must be perfect matchings partitioning exactly the edge set."""
    keys = {(min(u, v), max(u, v)) for u, v in edges}
    got = []
    for M in factors:
        if not is_perfect_matching(N, M): return False, "not a perfect matching"
        got += [(min(u, v), max(u, v)) for u, v in M]
    if len(got) != len(set(got)): return False, "factors overlap"
    if set(got) != keys: return False, "factors do not cover exactly the edges"
    return True, "ok"

def two_factor_cycles(N, M1, M2):
    """Cycle list (each a vertex sequence) of the 2-regular graph M1 u M2."""
    adj = adjacency(N, list(M1) + list(M2))
    assert all(len(a) == 2 for a in adj), "M1 u M2 is not 2-regular (matchings share an edge?)"
    seen = [False] * N; cyc = []
    for s in range(N):
        if seen[s]: continue
        c = [s]; seen[s] = True; prev, cur = s, min(adj[s])
        while cur != s:
            assert not seen[cur], "bad cycle walk"
            seen[cur] = True; c.append(cur)
            nxt = [y for y in adj[cur] if y != prev]
            assert len(nxt) == 1
            prev, cur = cur, nxt[0]
        cyc.append(c)
    return cyc

# ---------- F4 linear algebra ----------
def kernel_basis(rows, ncols):
    """Basis of {x in F4^ncols : R x = 0} by Gaussian elimination over F4."""
    R = [list(r) for r in rows]; piv = []; r = 0
    for c in range(ncols):
        p = next((i for i in range(r, len(R)) if R[i][c]), None)
        if p is None: continue
        R[r], R[p] = R[p], R[r]
        inv = INV[R[r][c]]; R[r] = [MUL[inv][x] for x in R[r]]
        for i in range(len(R)):
            if i != r and R[i][c]:
                f = R[i][c]; R[i] = [x ^ MUL[f][y] for x, y in zip(R[i], R[r])]
        piv.append(c); r += 1
        if r == len(R): break
    free = [c for c in range(ncols) if c not in set(piv)]
    basis = []
    for fc in free:
        x = [0] * ncols; x[fc] = 1
        for i, pc in enumerate(piv):
            x[pc] = R[i][fc]          # char 2: -R = R
        basis.append(x)
    return basis, len(piv)

def matvec_rank(rows, ncols):
    return ncols - len(kernel_basis(rows, ncols)[0])

# ---------- the four-fold affine lift ----------
class Lift:
    """Base data: identity-labelled G (m vertices, d-regular), its perfect matching
    factors M (list of d matchings), complement factors C (m-1-d matchings),
    closed flag.  Orientation and slopes follow PROOF.md's lift lemma."""
    def __init__(self, m, edges, M, C, closed):
        self.m, self.closed = m, closed
        self.M, self.C = [list(map(tuple, x)) for x in M], [list(map(tuple, x)) for x in C]
        self.d = len(self.M)
        # orient the cycles of F = M[0] u M[1]; slope w forward
        self.cycles = two_factor_cycles(m, self.M[0], self.M[1])
        orient = {}
        for cyc in self.cycles:
            L = len(cyc)
            for i in range(L):
                t, h = cyc[i], cyc[(i + 1) % L]
                orient[(min(t, h), max(t, h))] = (t, h, W)
        self.E = []      # list of (tail, head, slope); index = edge id
        self.eid = {}
        for u, v in sorted({(min(a, b), max(a, b)) for a, b in edges}):
            t, h, a = orient.get((u, v), (u, v, 1))
            self.eid[(u, v)] = len(self.E); self.E.append((t, h, a))
        assert len(self.E) == m * self.d // 2

    def B_rows(self):
        rows = [[0] * len(self.E) for _ in range(self.m)]
        for e, (t, h, a) in enumerate(self.E):
            rows[t][e] ^= 1; rows[h][e] ^= INV[a]
        return rows

    def D_apply(self, b):
        return [b[h] ^ MUL[a][b[t]] for (t, h, a) in self.E]

    def in_image_D(self, c):
        """Decide c in im D by propagation from vertex 0 over a BFS tree (4 root values)."""
        adj = [[] for _ in range(self.m)]
        for e, (t, h, a) in enumerate(self.E):
            adj[t].append((h, e, True)); adj[h].append((t, e, False))
        for b0 in range(4):
            b = [None] * self.m; b[0] = b0; q = deque([0]); ok = True
            while q and ok:
                x = q.popleft()
                for y, e, fwd in adj[x]:
                    t, h, a = self.E[e]
                    # constraint c_e = b_h + a b_t
                    val = (c[e] ^ MUL[a][b[t]]) if fwd else MUL[INV[a]][c[e] ^ b[h]]
                    if b[y] is None: b[y] = val; q.append(y)
                    elif b[y] != val: ok = False; break
            if ok and self.D_apply(b) == list(c): return True
        return False

    def build(self, c):
        self.c = list(c)
        self.phi = {}    # edge key -> (tail, head, map list x -> y)
        edges = []
        for e, (t, h, a) in enumerate(self.E):
            mp = [MUL[a][x] ^ c[e] for x in range(4)]
            self.phi[(min(t, h), max(t, h))] = (t, h, mp)
            edges += [(4 * t + x, 4 * h + mp[x]) for x in range(4)]
        return edges

    def lifted_factors(self):
        m = self.m
        Mf = []
        for Mi in self.M:
            f = []
            for u, v in Mi:
                t, h, mp = self.phi[(min(u, v), max(u, v))]
                f += [(4 * t + x, 4 * h + mp[x]) for x in range(4)]
            Mf.append(f)
        Cf = []
        for s in (1, 2, 3):                               # K4 in each fibre
            Cf.append([(4 * u + x, 4 * u + (x ^ s)) for u in range(m) for x in range(4) if x < x ^ s])
        for Mi in self.M:                                 # K4,4 minus designated matching
            for s in (1, 2, 3):
                f = []
                for u, v in Mi:
                    t, h, mp = self.phi[(min(u, v), max(u, v))]
                    f += [(4 * t + x, 4 * h + (mp[x] ^ s)) for x in range(4)]
                Cf.append(f)
        for Cj in self.C:                                 # full K4,4 over complement edges
            for s in range(4):
                Cf.append([(4 * u + x, 4 * v + (x ^ s)) for u, v in Cj for x in range(4)])
        return Mf, Cf

    def interpolate(self, K, J):
        """Replace the lifted matching over base matchings K by K4,4 minus it;
        add full K4,4 blocks over complement matchings J."""
        Kset = set()
        for i in K:
            for u, v in self.M[i]: Kset.add((min(u, v), max(u, v)))
        edges = []
        for key, (t, h, mp) in self.phi.items():
            if key in Kset:
                edges += [(4 * t + x, 4 * h + y) for x in range(4) for y in range(4) if y != mp[x]]
            else:
                edges += [(4 * t + x, 4 * h + mp[x]) for x in range(4)]
        for j in J:
            for u, v in self.C[j]:
                edges += [(4 * u + x, 4 * v + y) for x in range(4) for y in range(4)]
        return edges

def choose_c(lift, rng, tries=200):
    """Pick a random c in ker B outside im D (independent of the focused lane's
    deterministic first-basis-vector rule).  Returns c, stats."""
    basis, rankB = kernel_basis(lift.B_rows(), len(lift.E))
    stats = {"rank_B": rankB, "dim_ker_B": len(basis), "m": lift.m, "E": len(lift.E), "tries": 0, "in_im_D_hits": 0}
    for _ in range(tries):
        coef = [rng.randrange(4) for _ in basis]
        c = [0] * len(lift.E)
        for k, vec in zip(coef, basis):
            if k:
                for i, x in enumerate(vec): c[i] ^= MUL[k][x]
        stats["tries"] += 1
        if lift.in_image_D(c): stats["in_im_D_hits"] += 1; continue
        return c, stats
    raise RuntimeError("no c outside im D found")
