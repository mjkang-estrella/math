# gen_hd.py -- high-dimensional covering-sieve generator emitting the indep `nd` JSONL format.
#
# Problem on one slice:  X(L,q_1..q_k) = 10^L + sum_i c_i 10^{q_i} + K = 2^t0 3^a 7^w,
# t0 = v2(K), all coordinates >= qmin > t0 (so v2(X) = t0 on the whole domain).
#
# Method (see notes/highdim.md):
#   Phase A: flat breadth-first refinement along a fixed modulus schedule (e.g. 2,3,7,2,3,2,2,3,5).
#     The schedule is chosen so that the *double-ladder* classes (X == 0 mod 3^{j+2} AND
#     mod 7^{i+1}, i.e. a and w both unbounded) are killed by <3,7>-coset tests at primes with
#     ord_p(10) | M, before the 3-adic ladder is refined further.  The double-ladder test does
#     not depend on the 3-/7-adic depth at all (3,7 lie in <3,7>), only on x mod ord_p(10);
#     so it pays to make M rich in small divisors (2^4 3^3 5 7) rather than deep in 3.
#   Phase B: per-node deepening for the few survivors: refine by 3 while a is unbounded, by 7
#     while w is unbounded (or the factor with fewest surviving lifts); classes whose (a,w) is
#     exact and not prime-killed become `sz` leaves (all domain points with X = N listed).
# Every kill is a plain `prime` kill of the existing format; no new kill types.
#
# domain modes:  ordered   -> L > q_k > ... > q_1 >= qmin (checknd semantics; coefs[i] at q_{i+1})
#                unordered -> q_i pairwise distinct, qmin <= q_i < L, any order (checkhd semantics)
import sys, os, json, math, time, itertools
import multiprocessing as mp
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from hnt import vp

HERE = os.path.dirname(os.path.abspath(__file__))

def sz_points(N, coefs, K, qmin, ordered, cls=None):
    """all domain points with X = N (exact).  Lowest used position = v10 of the remainder and
    the coefficient there is forced by its last digit (no c_i is divisible by 10)."""
    R = N - K
    if R <= 0: return []
    L = len(str(R)) - 1
    if L < qmin: return []
    R1 = R - 10 ** L
    k = len(coefs)
    out = set()
    def dfs(rem, left, assign):
        if not left:
            if rem == 0: out.add(tuple(assign[i] for i in range(k)))
            return
        if rem <= 0: return
        v = 0; t = rem
        while t % 10 == 0: t //= 10; v += 1
        if v < qmin or v >= L: return
        dig = t % 10
        tried = set()
        for i in left:
            c = coefs[i]
            if c % 10 != dig or c in tried: continue
            tried.add(c)                     # equal coefficients: one representative, permute below
            assign[i] = v
            dfs(rem - c * 10 ** v, [j for j in left if j != i], assign)
            del assign[i]
    dfs(R1, list(range(k)), {})
    # expand permutations among equal coefficients
    full = set()
    for qs in out:
        groups = {}
        for i, c in enumerate(coefs): groups.setdefault(c, []).append(i)
        perms = [[]]
        for c, idxs in groups.items():
            vals = [qs[i] for i in idxs]
            perms = [pp + [(idxs, pv)] for pp in perms for pv in set(itertools.permutations(vals))]
        for pp in perms:
            q = [0] * k
            for idxs, pv in pp:
                for i, v in zip(idxs, pv): q[i] = v
            full.add(tuple(q))
    res = []
    for q in full:
        pt = (L,) + q
        if ordered and any(pt[i + 1] >= pt[i + 2] for i in range(k - 1)): continue
        X = 10 ** L + K + sum(c * 10 ** e for c, e in zip(coefs, q))
        assert X == N
        if cls is not None and not all(x % cls[1] == r % cls[1] for x, r in zip(pt, cls[0])): continue
        res.append(list(pt))
    return sorted(res)

class Gen:
    def __init__(self, coefs, K, qmin, supply, ordered, maxp=None):
        self.coefs = list(coefs); self.dim = len(coefs) + 1; self.K = K; self.qmin = qmin
        self.t0 = vp(K, 2); self.ordered = ordered
        assert K > 0 and K % 5 and qmin > self.t0
        self.byd = {}
        for p, d, o3, o7 in supply:
            if maxp and p > maxp: continue
            H = o3 * o7 // math.gcd(o3, o7)
            self.byd.setdefault(d, []).append((p, d, o3, o7, H))
        self._al = {}; self.tabs = {}; self.ptab = {}; self._alk = {}
    def aligned(self, M):
        if M not in self._al:
            dk = tuple(sorted(d for d in self.byd if M % d == 0))
            if dk in self._alk:
                self._al[M] = self._alk[dk]; return self._al[M]
            v = []
            for d, L in self.byd.items():
                if M % d == 0:
                    for (p, d, o3, o7, H) in L:
                        if p not in self.ptab:
                            if d <= 50000:
                                pw = [pow(10, r, p) for r in range(d)]
                                cw = [[c * x % p for x in pw] for c in self.coefs]
                            else: pw = cw = None
                            self.ptab[p] = (p, d, o3, o7, H, pw, cw, pow(2, -self.t0, p))
                        v.append(self.ptab[p])
            # orderings by strength for each signature type
            o = {}
            o['uu'] = sorted(v, key=lambda e: -(e[0] - 1) // e[4])
            o['ue'] = sorted(v, key=lambda e: -(e[0] - 1) // e[2])   # a unbounded, w exact
            o['eu'] = sorted(v, key=lambda e: -(e[0] - 1) // e[3])
            o['ee'] = sorted(v, key=lambda e: -e[0])
            o['uu'] = [e for e in o['uu'] if (e[0] - 1) // e[4] > 1]
            self._al[M] = o; self._alk[dk] = o
        return self._al[M]
    def modtab(self, m, per):
        k = (m, per)
        if k not in self.tabs:
            pw = [pow(10, r, m) for r in range(per)]
            self.tabs[k] = (pw, [[c * x % m for x in pw] for c in self.coefs])
        return self.tabs[k]
    def xm(self, r, m, per):
        if per > 50000:
            return (pow(10, r[0] % per, m) + self.K + sum(c * pow(10, e % per, m) for c, e in zip(self.coefs, r[1:]))) % m
        pw, cw = self.modtab(m, per)
        return (pw[r[0] % per] + self.K + sum(cw[i][r[i + 1] % per] for i in range(self.dim - 1))) % m
    def sig(self, r, M):
        j = vp(M, 3); m3 = 3 ** (j + 2); per = 3 ** j
        x = self.xm(r, m3, per)
        a = (j + 2, None) if x == 0 else (vp(x, 3), vp(x, 3))
        if M % 6 == 0:
            i = vp(M, 7); m7 = 7 ** (i + 1); per = 6 * 7 ** i
            x = self.xm(r, m7, per)
            w = (i + 1, None) if x == 0 else (vp(x, 7), vp(x, 7))
        else: w = (0, None)
        return a, w
    def test(self, e, r, a, w):
        p, d, o3, o7, H, pw, cw, i2 = e
        if pw is None:
            T = (pow(10, r[0] % d, p) + self.K + sum(c * pow(10, x % d, p) for c, x in zip(self.coefs, r[1:]))) * i2 % p
        else:
            T = (pw[r[0] % d] + self.K + sum(cw[i][r[i + 1] % d] for i in range(self.dim - 1))) * i2 % p
        if T == 0: return True
        x = T * pow(3, -a[0], p) * pow(7, -w[0], p) % p
        af, wf = a[1] is None, w[1] is None
        if af and wf: return pow(x, H, p) != 1
        if af: return pow(x, o3, p) != 1
        if wf: return pow(x, o7, p) != 1
        return x != 1
    def kill(self, r, M, a, w, used):
        """prime killing class r mod M (all primes aligned with M), preferring `used`"""
        key = ('u' if a[1] is None else 'e') + ('u' if w[1] is None else 'e')
        o = self.aligned(M)[key]
        for e in used:
            if self.test(e, r, a, w): return e
        for e in o:
            if self.test(e, r, a, w): return e
        return None
    def expand(self, r, M, f):
        """lifts of r mod M to M*f: returns (alive list [(r2,a,w)], used prime entries)"""
        M2 = M * f; used = []; alive = []
        for t in itertools.product(range(f), repeat=self.dim):
            r2 = tuple(x + k * M for x, k in zip(r, t))
            a, w = self.sig(r2, M2)
            e = self.kill(r2, M2, a, w, used)
            if e is None: alive.append((r2, a, w))
            elif e not in used: used.append(e)
        return alive, used

_G = None
class NodeBudgetExceeded(Exception):
    pass

def _expand_chunk(args):
    G, M, f = _G
    out = []
    for r in args:
        alive, used = G.expand(r, M, f)
        out.append((r, alive, [e[0] for e in used]))
    return out

def run(G, schedule, workers=24, cap_level=600000, mcap=10 ** 12, maxdepthB=40, budget_s=1100,
        max_nodes=None):
    t_start = time.time()
    nodes = {}
    nid = [0]
    def new(rec):
        if max_nodes is not None and len(nodes) >= max_nodes:
            raise NodeBudgetExceeded(f'node cap {max_nodes}')
        rec['id'] = nid[0]; nodes[nid[0]] = rec; nid[0] += 1; return rec['id']
    root = new({"p": -1, "r": [0] * G.dim, "m": 1})
    frontier = [(root, (0,) * G.dim, 1)]   # internal-to-be nodes: (id, r, M)
    info = []
    def finalize_leaf_or_keep(i, r2, M2, a, w):
        if a[1] is not None and w[1] is not None:
            N = 2 ** G.t0 * 3 ** a[0] * 7 ** w[0]
            nodes[i].update({"k": "l", "x": {"sz": [a[0], w[0]],
                             "sol": sz_points(N, G.coefs, G.K, G.qmin, G.ordered, (r2, M2))}})
            return False
        return True
    # root itself: kill / sz check
    a, w = G.sig((0,) * G.dim, 1)
    e = G.kill((0,) * G.dim, 1, a, w, [])
    if e is not None:
        nodes[root].update({"k": "l", "x": {"prime": e[0]}}); frontier = []
    M = 1
    for f in schedule:
        if not frontier: break
        if hasattr(G, 'before_level'):
            G.before_level(len(frontier), f)
        M2 = M * f; G.aligned(M2)
        rs = [r for _, r, _ in frontier]
        if len(rs) * f ** G.dim > 100000 and workers > 1:
            global _G; _G = (G, M, f)
            chunks = [rs[i::workers * 8] for i in range(workers * 8)]
            with mp.get_context("fork").Pool(workers) as pool:
                parts = pool.map(_expand_chunk, chunks)
            res = {}
            for part in parts:
                for r, alive, used in part: res[r] = (alive, used)
        else:
            res = {}
            for r in rs:
                alive, used = G.expand(r, M, f)
                res[r] = (alive, [e[0] for e in used])
        nf = []
        for i, r, _ in frontier:
            alive, used = res[r]
            nodes[i].update({"k": "i", "m2": M2, "c": [], "rest": used})
            for r2, a, w in alive:
                c = new({"p": i, "r": list(r2), "m": M2})
                nodes[i]["c"].append(c)
                if finalize_leaf_or_keep(c, r2, M2, a, w): nf.append((c, r2, M2))
        frontier = nf; M = M2
        info.append((M, len(frontier)))
        print(f"   A: M={M} frontier={len(frontier)} nodes={len(nodes)} {time.time()-t_start:.0f}s", file=sys.stderr, flush=True)
        if len(frontier) > cap_level: return None, info, "level cap"
        if time.time() - t_start > budget_s: return None, info, "time"
    # Phase B: per-node deepening
    stack = [(i, r, Mi, 0) for i, r, Mi in frontier]
    while stack:
        i, r, Mi, dep = stack.pop()
        if time.time() - t_start > budget_s: return None, info, "time B"
        a, w = G.sig(r, Mi)
        exp = {}
        def E(f):
            if f not in exp: exp[f] = G.expand(r, Mi, f)
            return exp[f]
        if Mi % 6:
            f = 6 // math.gcd(Mi, 6)
        else:
            f = None
            for g in (2, 3, 5, 7):                 # a factor that kills the whole class outright
                if g ** G.dim <= 20000 and not E(g)[0]: f = g; break
            if f is None:
                au, wu = a[1] is None, w[1] is None
                if au and not wu: f = 3            # pin a (3-adic ladder): refine along 3
                elif wu and not au: f = 7          # pin w (7-adic ladder): refine along 7
                else:
                    sc = lambda g: (sum(1 for _, a2, w2 in E(g)[0] if a2[1] is None and w2[1] is None),
                                    sum(1 for _, a2, w2 in E(g)[0] if a2[1] is None or w2[1] is None), g != 3)
                    f = min((3, 7), key=sc)
        alive, used = E(f)
        M2 = Mi * f
        if dep > maxdepthB or M2 > mcap: return None, info, f"depth/mcap at {r} mod {Mi}"
        nodes[i].update({"k": "i", "m2": M2, "c": [], "rest": [e[0] for e in used]})
        for r2, a2, w2 in alive:
            c = new({"p": i, "r": list(r2), "m": M2})
            nodes[i]["c"].append(c)
            if finalize_leaf_or_keep(c, r2, M2, a2, w2): stack.append((c, r2, M2, dep + 1))
    return nodes, info, "ok"

def write_cert(fn, G, nodes, extra_meta):
    meta = {"k": "meta", "dim": G.dim, "coefs": G.coefs, "K": G.K, "qmin": G.qmin,
            "root": {"r": [0] * G.dim, "m": 1},
            "domain": "ordered" if G.ordered else "unordered"}
    meta.update(extra_meta)
    with open(fn, "w") as fo:
        fo.write(json.dumps(meta) + "\n")
        for i in sorted(nodes):
            nd = nodes[i]
            rec = {"id": i, "p": nd["p"], "k": nd["k"], "r": nd["r"], "m": nd["m"]}
            if nd["k"] == "i":
                rec.update({"m2": nd["m2"], "c": nd["c"], "rest": nd["rest"]})
            else: rec["x"] = nd["x"]
            fo.write(json.dumps(rec, separators=(",", ":")) + "\n")

def solutions(nodes):
    s = set()
    for nd in nodes.values():
        if nd.get("k") == "l" and "sz" in nd["x"]:
            for q in nd["x"]["sol"]: s.add(tuple(q))
    return sorted(s)

if __name__ == "__main__":
    coefs = eval(sys.argv[1]); K = int(sys.argv[2]); qmin = int(sys.argv[3])
    sched = eval(sys.argv[4]); fn = sys.argv[5]; ordered = sys.argv[6] == "ordered"
    sup = json.load(open(os.path.join(HERE, "supply_B.json")))
    G = Gen(coefs, K, qmin, sup, ordered, maxp=float(sys.argv[7]) if len(sys.argv) > 7 else None)
    nodes, info, st = run(G, sched)
    print(st, info)
    if nodes:
        write_cert(fn, G, nodes, {})
        print("solutions", solutions(nodes), "nodes", len(nodes))
