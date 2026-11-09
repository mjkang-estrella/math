# L2c pipeline.py — general automated pipeline for Level 2 targets t with 5 -! t.
#
# Master equation (notes/L2_large_glm.md): n = 2^i 3^j 7^k, digits in {1,...,9} \ {0,5},
# n = R_L + S (R_L = L-digit repunit, S = sum (d-1)10^p over non-1 digits), so
#     9n = 10^L + sum_far A_i 10^{q_i} + K,   A_i = 9(c_i-1),  K = 9*S_low - 1.
# low = positions 0..2, far = positions 3..L-1 (distinct, < L).  On a slice where every
# free far digit sits at q >= t0'+1 (t0' = v2(K')) and L > t0', v2(RHS) = t0' exactly,
# so the sieve solves 3^a 7^w = (RHS)/2^{t0'}.
#
# Certificate format: the audited `nd` JSONL format of verification/indep (meta
# {"k":"meta","dim","coefs","K","qmin","root",...}; internal {"id","p","k":"i",
# "r","m","m2","c","rest":[primes]}; leaves {..., "x":{"prime":p}|{"sz":[a0,w0],"sol":[...]}}).
#   0 far digits -> dim 1 (v12-equivalent), 1 far -> dim 2 (cert2d-equivalent),
#   k >= 2 far -> k-D generalization (same schema, DIM = k+1, domain = all tuples of
#   DISTINCT positions q_i >= qmin, q_i < L; coefs listed in canonical sorted order).
# NO pin kills anywhere (the r8 pin divided by 2^t0 twice; primes suffice).
#
# modes:
#   stats t...     - multiset/config/parity/slice census
#   solve t...     - slices, sieve trees, certs (cert_t*.jsonl), coverage solve_t*.json
import sys, os, json, math, time
from itertools import product

HERE = os.path.dirname(os.path.abspath(__file__))
SLICE_BUDGET = 4000
SLICE_SECONDS = 25.0                   # wall-clock budget per slice tree
NODE_CAP = 200_000
MCAP = 10 ** 9
BRUTE_B = 300          # ground-truth digit bound (matches the parent's v13 range)
DEEP = 8
NMAX = 8

def vp(n, p):
    c = 0
    while n % p == 0:
        n //= p; c += 1
    return c

def prime_set(n):
    ps = set()
    for p in (2, 3, 5, 7):
        if n % p == 0:
            ps.add(p)
            while n % p == 0: n //= p
    assert n == 1, "target has a prime factor > 7"
    return ps

# ---------------- front end ----------------

def digit_multisets(t):
    ps = prime_set(t)
    assert 5 not in ps, "5 | t: out of scope"
    digs = [d for d in (2, 3, 4, 6, 7, 8, 9) if prime_set(d) <= ps]
    out = set()
    def rec(rem, start, cur):
        if rem == 1:
            out.add(tuple(cur)); return
        for d in digs:
            if d < start or rem % d: continue
            rec(rem // d, d, cur + [d])
    rec(t, 2, [])
    return sorted(out)

def enum_configs(ms):
    """Configs as S_low in [0,999] with decimal digits 0..8 (digit e at position p
    means c = e+1 there); the multiset must contain the implied digits.  The map
    config -> S_low is injective (no carries since c-1 <= 8)."""
    cnt = {}
    for d in ms: cnt[d] = cnt.get(d, 0) + 1
    out = []
    for a in range(9):
        for b in range(9):
            for c in range(9):
                S = a + 10 * b + 100 * c
                need = {}
                for e in (a, b, c):
                    if e: need[e + 1] = need.get(e + 1, 0) + 1
                if any(cnt.get(d, 0) < n for d, n in need.items()): continue
                rem = list(ms)
                for d, n in need.items():
                    for _ in range(n): rem.remove(d)
                out.append((S, tuple(sorted(9 * (d - 1) for d in rem))))
    return out

def build_R40():
    return {(2 ** i) * (3 ** j) * (7 ** k) % 40
            for i in range(7) for j in range(4) for k in range(4)}
R40 = build_R40()

def parity_dead(S_low, has_far):
    """n = R_L + S_low (mod 40) must lie in R40 = {2^i 3^j 7^k mod 40} for some
    admissible L.  R_L mod 40 = 1, 11, 31 for L = 1, 2, >= 3.  A low digit at
    position p requires L >= p+1; any far digit requires L >= 4.  Dead iff no
    admissible L works.  S_low = 0 with far digits gives 31 for all L >= 3:
    dead by the all-far lemma."""
    occ = [p for p in range(3) if (S_low // 10 ** p) % 10]
    Lmin = max(occ) + 1 if occ else 1
    if has_far: Lmin = max(Lmin, 4)
    for L in range(Lmin, 3):
        if ((R_L40[L] + S_low) % 40) in R40: return False
    return ((31 + S_low) % 40) not in R40
R_L40 = {1: 1, 2: 11}

# ---------------- slices ----------------

def slices(K0, far, budget=SLICE_BUDGET):
    """Partition all far-position assignments into reduced problems (K', free_coefs)
    such that on each, v2(10^L + sum A_i 10^{q_i} + K') = t0' at every domain point.
    Worklist over states (K, free tuple, floors tuple); while some free digit has
    floors[i] <= t0 it may sit at q <= t0 (breaking v2-constancy), so branch:
    fix it at each such q, or raise its floor to t0+1.  Emit when all floors >= t0+1;
    then qmin = t0+1 and v2(RHS) = t0' on the whole domain."""
    far = tuple(sorted(far))
    out, seen = [], set()
    stack = [(K0, far, (3,) * len(far))]
    while stack:
        K, free, fl = stack.pop()
        t0 = vp(K, 2)
        key = (K, free, fl)
        if key in seen: continue
        seen.add(key)
        pick = next((i for i in range(len(free)) if fl[i] <= t0), None)
        if pick is None:
            out.append((K, free, t0))
            if len(out) > budget:
                raise RuntimeError("slice budget")
            continue
        A = free[pick]
        nfree = free[:pick] + free[pick + 1:]
        for q in range(fl[pick], t0 + 1):
            stack.append((K + A * 10 ** q, nfree, fl[:pick] + fl[pick + 1:]))
        stack.append((K, free, fl[:pick] + (t0 + 1,) + fl[pick + 1:]))
    return out

# ---------------- prime universe ----------------
# primes p > 7 with ord_p(10) | 2^6 3^6 5^2 7^4 (Agent A's universe, p <= 2e7),
# cached as [p, d, o3, o7]; rebuilt with a sieve if the cache is missing.

def build_universe():
    fn = os.path.join(HERE, "univ_20M.json")
    if os.path.exists(fn):
        return [tuple(x) for x in json.load(open(fn))]
    PMAX = 20_000_000
    MU = 2 ** 7 * 3 ** 10 * 5 ** 2 * 7 ** 5   # wider than Agent A's (3^6): ladder
                                              # classes need ord ~ 3^7..3^8 primes
    sv = bytearray([1]) * (PMAX + 1); sv[0] = sv[1] = 0
    for p in range(2, int(PMAX ** .5) + 1):
        if sv[p]: sv[p * p::p] = bytearray(len(range(p * p, PMAX + 1, p)))
    def order(a, p, grp):
        d = grp
        for f in range(2, 100):
            if d % f: continue
            while d % f == 0 and pow(a, d // f, p) == 1: d //= f
        return d
    out = []
    for p in range(11, PMAX + 1):
        if sv[p] and pow(10, MU, p) == 1:
            d = order(10, p, p - 1)
            o3 = order(3, p, p - 1); o7 = order(7, p, p - 1)
            out.append((p, d, o3, o7))
            if p % 100000 < 2: print("univ", p, file=sys.stderr)
    json.dump(out, open(fn, "w"))
    return out

UNIV = None
def get_universe():
    global UNIV
    if UNIV is None: UNIV = build_universe()
    return UNIV

# ---------------- sieve engine ----------------

class Sieve:
    def __init__(self, coefs, K, qmin):
        self.coefs = list(coefs)          # A values, canonical sorted order
        self.dim = len(coefs) + 1
        self.K = K
        self.qmin = qmin                  # domain floor for every far coordinate
        self.t0 = vp(K, 2)
        assert K > 0 and K % 5 != 0 and qmin > self.t0
        self.PT = {}
        for (p, d, o3, o7) in get_universe():
            H = o3 * o7 // math.gcd(o3, o7)
            self.PT.setdefault(d, []).append(((p - 1) // H, p, o3, o7, H, pow(2, -self.t0, p)))
        for d in self.PT:
            self.PT[d].sort(key=lambda e: -e[0])
        self._al, self._inv = {}, {}
        self.nodes = []
        self.unresolved = []
        self.deadline = None
        self.root = ([0] * self.dim, 1)

    def Xmod(self, r, m):
        s = pow(10, r[0], m) + self.K
        for c, e in zip(self.coefs, r[1:]):
            s += c * pow(10, e, m)
        return s % m

    def sig(self, r, M):
        j = vp(M, 3); m3 = 3 ** (j + 2)
        x = self.Xmod(r, m3)
        a = (j + 2, None) if x == 0 else (vp(x, 3), vp(x, 3))
        if M % 6 == 0:
            i = vp(M, 7); m7 = 7 ** (i + 1)
            x = self.Xmod(r, m7)
            w = (i + 1, None) if x == 0 else (vp(x, 7), vp(x, 7))
        else:
            w = (0, None)
        return a, w

    def aligned(self, M):
        v = self._al.get(M)
        if v is None:
            v = []
            for d, L in self.PT.items():
                if M % d == 0: v.extend(L)
            v.sort(key=lambda e: -e[0])   # strongest (largest subgroup index) first
            self._al[M] = v
        return v

    def inv(self, g, e, p):
        k = (g, e, p)
        return self._inv[k] if k in self._inv else self._inv.setdefault(k, pow(g, -e, p))

    def kill_by(self, r, M, a, w):
        """A prime killing the whole class, or None.  Aligned primes only; the tree
        reaches finer moduli via splits, which is how non-aligned primes get used."""
        af, wf = a[1] is None, w[1] is None
        a0, w0 = a[0], w[0]
        coefs, K = self.coefs, self.K
        for (idx, p, o3, o7, H, i2) in self.aligned(M):
            T = K
            for c, e in zip(coefs, r[1:]):
                T += c * pow(10, e, p)
            T = (T + pow(10, r[0], p)) % p * i2 % p
            if T == 0:
                return p
            x = T * self.inv(3, a0, p) % p * self.inv(7, w0, p) % p
            if af and wf:
                if idx > 1 and pow(x, H, p) != 1: return p
            elif af:
                if pow(x, o3, p) != 1: return p
            elif wf:
                if pow(x, o7, p) != 1: return p
            elif x != 1:
                return p
        return None

    def lifts(self, r, M, M2):
        f = M2 // M
        for t in product(range(f), repeat=self.dim):
            yield tuple((x % M) + k * M for x, k in zip(r, t))

    def sz_solutions(self, a0, w0, M, r):
        """All domain points with X = 2^t0 3^a0 7^w0: L = len(str(N-K))-1 is forced
        (N-K = 10^L + sum A_i 10^{q_i} < 10^L + 80*10^{L-1}), then DFS-decode the
        rest.  Exact big-integer checks; valid for any DIM."""
        N = 2 ** self.t0 * 3 ** a0 * 7 ** w0
        R = N - self.K
        if R <= 0: return []
        s = str(R)
        L = len(s) - 1
        sols = set()
        if s[0] == '0' or L < 1: return []
        Rp = R - 10 ** L
        if Rp < 0: return []
        def dfs(res, rem, pos):
            if not rem:
                if res != 0: return
                if self.dim == 1:
                    if L >= self.qmin and L % M == r[0] % M and 10 ** L + self.K == N:
                        sols.add((L,))
                else:
                    qs = tuple(sorted(pos))
                    if (len(set(qs)) == len(qs) and qs[0] >= self.qmin and qs[-1] < L
                            and all(qi % M == ri % M for qi, ri in zip(qs, r[1:]))
                            and L % M == r[0] % M):
                        X = 10 ** L + self.K
                        for c, e in zip(self.coefs, qs): X += c * 10 ** e
                        if X == N:
                            sols.add((L,) + qs)
                return
            if res <= 0: return
            P = len(str(res)) - 1                # top digit position (leading digit != 0)
            for A in sorted(set(rem)):
                la = len(str(A))
                q = P - la + 1
                if q < 0: continue
                cand = A * 10 ** q
                if cand > res: continue
                rem2 = list(rem); rem2.remove(A)
                dfs(res - cand, rem2, pos + [q])
        dfs(Rp, list(self.coefs), [])
        return sorted(sols)

    def evaluate(self, r, M, f):
        M2 = M * f
        alive, used, unres = [], [], 0
        for r2 in self.lifts(r, M, M2):
            a, w = self.sig(r2, M2)
            p = self.kill_by(r2, M2, a, w)
            if p is None:
                alive.append(r2)
                if a[1] is None or w[1] is None: unres += 1
            elif p not in used:
                used.append(p)
        return M2, alive, used, unres

    def run(self, mcap=None, node_cap=NODE_CAP, root_m=None, deadline=None):
        self.deadline = deadline
        # The root class mod 1 is the whole domain; splits cover all residues, so
        # the tree is a complete cover.  (Rooting at a larger M would cover only
        # that residue class -- unsound.)  dim >= 4 trees can explode on 3-adic
        # ladder families; the node cap then leaves a precise residual.
        if mcap is None: mcap = MCAP
        if root_m is None: root_m = 1
        self.root = ([0] * self.dim, root_m)
        def process(r, M, parent, depth=0):
            if len(self.nodes) > node_cap:
                raise RuntimeError("node cap")
            if self.deadline and time.time() > self.deadline:
                raise RuntimeError("deadline")
            nid = len(self.nodes)
            a, w = self.sig(r, M)
            # direct kill of the whole class (sig is constant on it: the orders
            # ord_{3^{j+2}}(10) | M and 6*7^{i+1} | M hold by construction)
            pk = self.kill_by(r, M, a, w)
            if pk is not None:
                self.nodes.append({"id": nid, "p": parent, "k": "l", "r": list(r), "m": M,
                                   "a": [a[0], a[1]], "w": [w[0], w[1]], "x": {"prime": pk}})
                return nid
            if a[1] is not None and w[1] is not None:
                sols = self.sz_solutions(a[0], w[0], M, r)
                self.nodes.append({"id": nid, "p": parent, "k": "l", "r": list(r), "m": M,
                                   "a": [a[0], a[1]], "w": [w[0], w[1]],
                                   "x": {"sz": [a[0], w[0]], "sol": [list(s) for s in sols]}})
                return nid
            if M > mcap:
                self.unresolved.append((r, M))
                return nid
            cand = {f for f in range(2, NMAX + 1) if f ** self.dim <= 3000}
            if self.dim >= 3: cand &= {2, 3, 7}   # keep high-dim trees narrow
            if a[1] is None: cand.add(3)
            if w[1] is None and M % 6 == 0: cand.add(7)
            if depth >= DEEP: cand &= {2, 3, 7}
            best = None
            for f in sorted(cand):
                M2, alive, used, unres = self.evaluate(r, M, f)
                score = (unres, len(alive),
                         0 if ((f == 3 and a[1] is None) or (f == 7 and w[1] is None)) else 1, f)
                if best is None or score < best[0]:
                    best = (score, f, M2, alive, used)
                if not alive: break
            if best is None:
                self.unresolved.append((r, M))
                return nid
            _, f, M2, alive, used = best
            nd = {"id": nid, "p": parent, "k": "i", "r": [x % M for x in r], "m": M,
                  "m2": M2, "c": [], "rest": used if len(alive) < f ** self.dim else None}
            self.nodes.append(nd)
            nd["c"] = [process(r2, M2, nid, depth + 1) for r2 in alive]
            return nid
        self.nodes = []; self.unresolved = []
        process((0,) * self.dim, root_m, -1)
        return self.unresolved

    def solutions(self):
        out = set()
        for nd in self.nodes:
            if nd["k"] == "l" and "sz" in nd.get("x", {}):
                for s in nd["x"]["sol"]: out.add(tuple(s))
        return sorted(out)

# ---------------- brute ground truth (bucketed; also used for cross-validation) -----

def brute_bucket(ts, B):
    """All multi-digit 2^i 3^j 7^k <= 10^B with no digit 0/5, bucketed by Pi value."""
    out = {t: [] for t in ts}
    i = 0; n2 = 1
    while n2 <= 10 ** B:
        j = 0; n3 = n2
        while n3 <= 10 ** B:
            k = 0; n = n3
            while n <= 10 ** B:
                s = str(n)
                if len(s) >= 2 and '0' not in s and '5' not in s:
                    p = 1
                    for ch in s: p *= ord(ch) - 48
                    if p in out: out[p].append(n)
                k += 1; n *= 7
            j += 1; n3 *= 3
        i += 1; n2 *= 2
    return {t: sorted(set(v)) for t, v in out.items()}

def slice_for_point(K0, far_positions):
    """Replay the slice-worklist decision path for one concrete assignment
    far_positions = [(A, q), ...] (same pick order as slices(): digits in sorted-A
    order, first with floor <= t0).  Returns (K', free_coefs, floors) of the emitting
    slice that contains this point (used for cross-validation)."""
    K = K0
    rem = sorted(far_positions)                     # by A, matching slices()' order
    fl = [3] * len(rem)
    while True:
        t0 = vp(K, 2)
        pick = next((i for i in range(len(rem)) if fl[i] <= t0), None)
        if pick is None:
            return K, tuple(A for A, q in rem), list(fl)
        A, q = rem[pick]
        if q <= t0:
            K += A * 10 ** q
            rem.pop(pick); fl.pop(pick)
        else:
            fl[pick] = t0 + 1

def bfs_residual(coefs, K, qmin, maxlvl=9, cap=60000):
    """Precise residual for an exploded high-dim config: refine the root class by
    f=3 and report the alive-class count at the last level within budget.  The
    alive classes sit on the 3-adic ladder (X == 0 mod 3^{j+2}); they survive all
    aligned prime kills at their modulus."""
    sv = Sieve(list(coefs), K, qmin)
    cur = [((0,) * sv.dim, 1)]
    stats = []
    try:
        for lvl in range(maxlvl):
            nxt = []
            for r, M in cur:
                a, w = sv.sig(r, M)
                if sv.kill_by(r, M, a, w) is not None: continue
                M2, alive, used, unres = sv.evaluate(r, M, 3)
                nxt += [(r2, M2) for r2 in alive]
                if len(nxt) > cap: break
            stats.append((len(cur), cur[0][1] if cur else 0))
            cur = nxt
            if len(cur) > cap: break
            if not cur: return {"exploded": False}
    except MemoryError:
        return {"exploded": True, "levels": stats, "alive_at_last": ">cap",
                "M_at_last": stats[-1][1] * 3 if stats else 3}
    return {"exploded": True, "levels": stats, "alive_at_last": len(cur),
            "M_at_last": cur[0][1] if cur else 0}

# ---------------- driver ----------------

def sol_to_n(coefs, K, sol):
    X = 10 ** sol[0] + K
    for c, e in zip(coefs, sol[1:]): X += c * 10 ** e
    assert X % 9 == 0
    return X // 9

def solve_target(t, brutes=None):
    mss = digit_multisets(t)
    report = {"target": t, "multisets": [], "members": set(), "open": []}
    for ms in mss:
        mrep = {"multiset": list(ms), "configs": []}
        for S, far in enum_configs(ms):
            crep = {"S_low": S, "far": list(far)}
            if parity_dead(S, bool(far)):
                crep["status"] = "parity-dead"
            else:
                K = 9 * S - 1
                try:
                    sl = slices(K, far)
                except RuntimeError:
                    # the low-q fix cascade (t0 grows as far digits are folded)
                    # explodes the slice space; the residual is the same 3-adic
                    # ladder family, now inside the slice enumeration
                    crep["status"] = "OPEN (slice budget)"
                    crep["residual"] = {"kind": "slice-budget-overflow",
                                        "nfar": len(far)}
                    report["open"].append((ms, S)); mrep["configs"].append(crep); continue
                if any(len(free) >= 3 for _, free, _ in sl):
                    # a dim >= 4 slice makes the config OPEN as a whole; sieving its
                    # dim <= 3 slices would not change the status
                    crep["status"] = "OPEN (dim>=4 slice)"
                    crep["residual"] = {"kind": "3-adic-ladder-family",
                                        "nfar_hi": max(len(f) for _, f, _ in sl)}
                    report["open"].append((ms, S)); mrep["configs"].append(crep); continue
                certs, ok = [], True
                for (K2, free, t02) in sl:
                    coefs = list(free)
                    # far positions >= 3 (config constraint); 1-D domain is L >= t0+1
                    qmin = max(t02 + 1, 3) if coefs else t02 + 1
                    fn = os.path.join(HERE, f"cert_t{t}_S{S}_K{K2}_c{'_'.join(map(str, coefs)) or 'none'}.jsonl")
                    sv = Sieve(coefs, K2, qmin)
                    if len(coefs) >= 3:
                        # dim >= 4 trees explode on 3-adic ladder families (r7/r8
                        # needed special QR arguments even at dim 3); record the
                        # precise residual instead of an unbounded run.  The family
                        # {X == 0 mod 3^{j+2}} has dimension dim-1 >= 3 and grows
                        # ~3^{dim-2}-fold per 3-adic level (verified on samples);
                        # it affects only L > 300, which the brute force covers.
                        unres = [(0, 0)]
                        crep.setdefault("residual", []).append(
                            {"K2": K2, "free": list(coefs), "qmin": qmin,
                             "kind": "3-adic-ladder-family"})
                    else:
                        try:
                            unres = sv.run(deadline=time.time() + SLICE_SECONDS)
                        except RuntimeError as e:
                            ok = False
                            certs.append([os.path.basename(fn), f"OPEN-budget ({e})"])
                            continue
                    if unres:
                        ok = False
                        crep.setdefault("residual", [])
                        certs.append([os.path.basename(fn), f"UNRESOLVED {len(unres)} classes maxM={max((u[1] for u in unres), default=0)}"])
                        continue
                    meta = {"k": "meta", "dim": len(coefs) + 1, "coefs": coefs, "K": K2,
                            "qmin": qmin, "root": {"r": list(sv.root[0]), "m": sv.root[1]},
                            "target": t, "S_low": S}
                    with open(fn, "w") as fo:
                        fo.write(json.dumps(meta) + "\n")
                        for nd in sv.nodes: fo.write(json.dumps(nd) + "\n")
                    certs.append([os.path.basename(fn), "closed"])
                    for s in sv.solutions():
                        n = sol_to_n(coefs, K2, s)
                        if len(str(n)) < 2: continue   # single-digit n excluded
                        # the slice equation may admit points whose digit structure
                        # (after carries) differs from this config; keep only true
                        # config points -- completeness is unaffected
                        if math.prod(int(ch) for ch in str(n)) != t: continue
                        dig = str(n)[::-1]
                        if sum((int(ch) - 1) * 10 ** p for p, ch in enumerate(dig)
                               if p < 3 and ch != '1') != S: continue
                        report["members"].add(n)
                crep["slices"] = len(sl)
                crep["certs"] = certs
                crep["status"] = "PROVED" if ok else "OPEN"
                if not ok: report["open"].append((ms, S))
            mrep["configs"].append(crep)
        report["multisets"].append(mrep)
        print(f"  [t={t}] ms {list(ms)}: {sum(1 for c in mrep['configs'] if c.get('status')=='PROVED')} proved, "
              f"{sum(1 for c in mrep['configs'] if c.get('status','').startswith('OPEN'))} open, "
              f"{sum(1 for c in mrep['configs'] if c.get('status')=='parity-dead')} parity-dead", file=sys.stderr, flush=True)
    # ground truth to L <= BRUTE_B and cross-validation of coverage
    if brutes is None:
        brutes = brute_bucket([t], BRUTE_B)[t]
    cert_ns = set(report["members"])
    brute_only, gaps = [], []
    closed_keys = {(tuple(sorted(far)), S) for ms2, S in []}  # populated below
    for mrep2 in report["multisets"]:
        for c in mrep2["configs"]:
            if c.get("status") == "PROVED":
                closed_keys.add((tuple(sorted(c["far"])), c["S_low"]))
    for n in brutes:
        if n in cert_ns: continue
        s = str(n); L = len(s)
        dig = s[::-1]   # dig[p] = digit at position p
        far_pos = [(9 * (int(ch) - 1), p) for p, ch in enumerate(dig) if p >= 3 and ch != '1']
        S_low = sum((int(ch) - 1) * 10 ** p for p, ch in enumerate(dig) if p < 3 and ch != '1')
        if (tuple(sorted(A for A, q in far_pos)), S_low) not in closed_keys:
            brute_only.append([n, L, "config OPEN (residual above)"])
            continue
        K2, free, floors = slice_for_point(9 * S_low - 1, far_pos)
        qmin = max(min(floors), 3) if floors else vp(K2, 2) + 1
        qmax = max((q for A, q in far_pos), default=0)
        if L > qmax and all(q >= max(3, vp(K2, 2) + 1) for A, q in far_pos) and (far_pos or L >= vp(K2, 2) + 1):
            gaps.append([n, L, qmin, list(free), "should have been a cert sol"])
        else:
            brute_only.append([n, L, "below domain floor"])
    report["cert_members"] = sorted(cert_ns)
    report["members"] = sorted(set(report["members"]) | set(brutes))
    report["brute_count"] = len(brutes)
    report["brute_only"] = brute_only
    report["coverage_gaps"] = gaps
    return report

if __name__ == "__main__":
    mode = sys.argv[1]
    if mode == "stats":
        for t in map(int, sys.argv[2:]):
            print(f"== target {t} ==")
            for ms in digit_multisets(t):
                cfgs = enum_configs(ms)
                surv = [(S, far) for S, far in cfgs if not parity_dead(S, bool(far))]
                ks, st = {}, 0
                for S, far in surv:
                    ks[len(far)] = ks.get(len(far), 0) + 1
                    st += len(slices(9 * S - 1, far))
                print(f"  {ms}: configs={len(cfgs)} alive={len(surv)} k-dist={dict(sorted(ks.items()))} slices={st}")
    elif mode == "solve":
        ts = list(map(int, sys.argv[2:]))
        bucket = brute_bucket(ts, BRUTE_B)   # enumerate 2^i 3^j 7^k <= 10^B once
        for t in ts:
            rep = solve_target(t, bucket[t])
            print(f"== target {t}: {len(rep['members'])} members: {rep['members']}")
            print(f"   brute(L<={BRUTE_B})={rep['brute_count']} brute_only={rep['brute_only']} gaps={rep['coverage_gaps']}")
            print(f"   open configs: {len(rep['open'])}: {rep['open'][:10]}")
            json.dump({"target": t, "members": rep["members"], "cert_members": rep["cert_members"],
                       "brute_count": rep["brute_count"], "brute_only": rep["brute_only"],
                       "coverage_gaps": rep["coverage_gaps"],
                       "open": [[list(o[0]), o[1]] for o in rep["open"]],
                       "multisets": rep["multisets"]},
                      open(os.path.join(HERE, f"solve_t{t}.json"), "w"), indent=1)
    else:
        print("modes: stats | solve")
