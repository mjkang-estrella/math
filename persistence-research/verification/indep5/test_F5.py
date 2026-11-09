"""[F5] Soundness tests for check_sym_F5.py (deep decimal-tail pins, k <= qmin).

Run:  bash -c 'ulimit -v 6000000; python3 -I test_F5.py [sections]'
Sections: T1 (differential vs the unmodified checker, small E), T2 (deep-k unit
tests), T3 (positive controls: valid deep-pin certificates are accepted, and the
deep pin is load-bearing).  Tamper tests are in tamper_F5.py, the certificate
regression in regress_F5.py.
"""
import sys, os, random, json, itertools
sys.dont_write_bytecode = True
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import check_sym_F5 as F5
import check_sym_F_base as B
import certkit as CK

FAILS = []
def check(name, cond, msg=""):
    print(("  ok   " if cond else "  FAIL ") + name + ("  " + str(msg) if msg and not cond else ""))
    if not cond: FAILS.append(name + " " + str(msg))

def mk(mod, kt):
    c = mod.Cert.__new__(mod.Cert)
    c.kt = kt; c._pairs = {}
    if mod is F5: c._ps = {}; c._admc = {}
    return c

# ---------------------------------------------------------------- allowed sets
_PCACHE = {}
def old_pairs(kt, E):
    key = (kt, E)
    r = _PCACHE.get(key)
    if r is None:
        c = mk(B, kt)
        r = B.Cert.pairs(c, E)
        _PCACHE[key] = r
    return r

def allowed_old(kt, E, sg, p):
    """Exactly the semantics of check_sym_F.kill_variant: union of cosets 3^ae 7^be H."""
    A, W, P = old_pairs(kt, E)
    a0, aex, w0, wex = sg
    h = []
    if not aex: h.append(pow(3, A, p))
    if not wex: h.append(pow(7, W, p))
    nH = 1
    for x in h: nH = B.lcm(nH, B.order(x, p))
    img = set()
    for al, be in P:
        if aex and (al - a0) % A: continue
        if wex and (be - w0) % W: continue
        ae = a0 if aex else al
        be_ = w0 if wex else be
        img.add(pow(pow(3, ae, p) * pow(7, be_, p) % p, nH, p))
    if not img: return None
    return {y for y in range(1, p) if pow(y, nH, p) in img}

def allowed_new(kt, E, sg, p):
    c = mk(F5, kt)
    rep, nU = F5.Cert._adm(c, p, E, sg)
    if rep is None: return None
    return {y for y in range(1, p) if pow(y, nU, p) == pow(rep, nU, p)}

# ---------------------------------------------------------------- T1 differential
def T1(ncases=24000, seed=7):
    print("T1: differential allowed-set equality, F5 vs unmodified check_sym_F (small E)")
    rnd = random.Random(seed)
    shapes = []
    for e2 in range(0, 7):
        for e5 in range(0, 6):
            E = 2 ** e2 * 5 ** e5
            if E == 0 or E > 200000: continue
            A = B.order(3, E) if E > 1 else 1
            W = B.order(7, E) if E > 1 else 1
            if A * W > 400000: continue          # keep the reference enumeration cheap
            shapes.append((e2, e5, E))
    primes = [11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 73, 97, 9901]
    n = bad = 0
    tries = 0
    while n < ncases and tries < 4 * ncases:
        tries += 1
        e2, e5, E = rnd.choice(shapes)
        kt = rnd.randrange(1, 10 ** 7, 2)
        if e5 and rnd.random() < 0.2: kt *= 5     # exercise tau == 0 mod 5
        sgs = []
        for aex in (0, 1):
            for wex in (0, 1):
                for _ in range(2):
                    sgs.append((rnd.randrange(0, 16), aex, rnd.randrange(0, 16), wex))
        rnd.shuffle(sgs)
        for sg in sgs[:3]:
            for p in rnd.sample(primes, 3):
                o = allowed_old(kt, E, sg, p) or set()
                v = allowed_new(kt, E, sg, p)
                v = set() if v is None else v
                n += 1
                if o != v:
                    bad += 1
                    if bad <= 5: print("    MISMATCH E=%d kt=%d sg=%s p=%d |old|=%d |new|=%d" % (E, kt, sg, p, len(o), len(v)))
    check("T1 allowed-set equality (%d comparisons)" % n, bad == 0, "%d mismatches" % bad)

# ---------------------------------------------------------------- T2 deep-k units
def T2(seed=11):
    print("T2: deep-k structural tests")
    rnd = random.Random(seed)
    # --- order identities (task brief: ord_{5^k}(3) = 4*5^(k-1); mod 2^j orders divide 2^(j-2))
    ok = True; msg = []
    for k in range(1, 7):
        o3 = B.order(3, 5 ** k); o7 = B.order(7, 5 ** k)
        if o3 != 4 * 5 ** (k - 1): ok = False; msg.append("ord_5^%d(3)=%d" % (k, o3))
        if o7 != 4 * 5 ** max(k - 2, 0): ok = False; msg.append("ord_5^%d(7)=%d" % (k, o7))
    for j in range(1, 13):
        if j >= 3 and B.order(3, 2 ** j) != 2 ** (j - 2): ok = False; msg.append("ord_2^%d(3)" % j)
        o7 = B.order(7, 2 ** j) if j >= 2 else 1
        if j >= 3 and (2 ** (j - 2)) % o7 != 0:
            ok = False; msg.append("ord_2^%d(7)=%d does not divide 2^(j-2)" % (j, o7))
        if pow(7, o7, 2 ** j) != 1 % (2 ** j):
            ok = False; msg.append("ord_2^%d(7) wrong" % j)
    check("T2a order identities", ok, msg)
    # --- dlog round trips
    ok = True; msg = []
    for k in range(1, 9):
        m = 5 ** k; A5 = 4 * 5 ** (k - 1)
        for _ in range(6):
            r = rnd.randrange(A5)
            h = pow(3, r, m)
            x = F5._dlog3_5k(h, k)
            if x is None or pow(3, x, m) != h or not (0 <= x < A5):
                ok = False; msg.append("dlog3_5k k=%d h=%d" % (k, h))
        if F5._dlog3_5k(5 * rnd.randrange(1, 100), k) is not None:
            ok = False; msg.append("dlog3_5k accepts h divisible by 5")
    for j in range(3, 13):
        m = 2 ** j; A2 = 2 ** (j - 2)
        for _ in range(6):
            r = rnd.randrange(A2)
            t = pow(3, r, m)
            x = F5._dlog3_2j(t, j)
            if pow(3, x, m) != t or not (0 <= x < A2):
                ok = False; msg.append("dlog3_2j j=%d t=%d" % (j, t))
    check("T2b dlog round trips", ok, msg)
    # --- _solve_gx vs brute force (small E)
    ok = True; msg = []
    for (e2, e5) in [(0, 2), (1, 2), (2, 2), (3, 2), (4, 2), (0, 3), (2, 3), (3, 3), (1, 4), (3, 4)]:
        E = 2 ** e2 * 5 ** e5
        for g in (3, 7):
            period = B.order(g, E)
            for _ in range(8):
                x0 = rnd.randrange(period)
                h = pow(g, x0, E)
                if e2 >= 1 and h % 2 == 0: continue
                r = mk(F5, 1)._solve_gx(E, g, h)
                if r is None: ok = False; msg.append("solve_gx None E=%d g=%d h=%d" % (E, g, h)); continue
                x, M = r
                if M != period: ok = False; msg.append("solve_gx period E=%d g=%d M=%d != %d" % (E, g, M, period))
                for xx in range(0, 2 * period):
                    if (pow(g, xx, E) == h) != ((xx - x) % M == 0):
                        ok = False; msg.append("solve_gx set E=%d g=%d h=%d x=%d" % (E, g, h, xx))
                if e5 and rnd.random() < 0.3:
                    h5 = h * 5 % E
                    if mk(F5, 1)._solve_gx(E, g, h5) is not None and e2 == 0:
                        pass  # 5 | h with no 2-part: truly unsolvable, must be None
                    if mk(F5, 1)._solve_gx(E, g, h5) is not None:
                        ok = False; msg.append("solve_gx accepts 5|h E=%d" % E)
    check("T2c _solve_gx vs brute force", ok, msg)
    # --- _solve_free invariants + never kill a true point, deep k
    ok = True; msg = []
    primes = [11, 13, 17, 19, 29, 31, 41, 73, 9901]
    for k in (4, 5, 6, 8, 10, 14):
        for t0 in (0, 1, 3, max(k - 1, 0), k):        # k vs t0: below, equal, above
            e2 = max(k - t0, 0)
            if rnd.random() < 0.5: e2 = max(e2, 3)     # pin2 combined
            E = 2 ** e2 * 5 ** k
            for _ in range(4):
                a = rnd.randrange(0, 10 ** 6); w = rnd.randrange(0, 10 ** 6)
                tau = pow(3, a, E) * pow(7, w, E) % E
                kt = tau
                if kt % 2 == 0: kt += E                # kt must be odd (E odd here)
                ct = mk(F5, kt)
                sol = F5.Cert._solve_free(ct, E)
                if sol is None:
                    ok = False; msg.append("solve_free None for a true point k=%d t0=%d E=%d" % (k, t0, E)); continue
                (ra, rw), gens = sol
                if pow(3, ra, E) * pow(7, rw, E) % E != kt % E:
                    ok = False; msg.append("rep violates pin k=%d t0=%d" % (k, t0))
                for ga, gw in gens:
                    if (ga, gw) != (0, 0) and pow(3, ga, E) * pow(7, gw, E) % E != 1:
                        # every generator must be a pseudo-unit: 3^ga 7^gw == 1 mod E
                        ok = False; msg.append("gen violates kernel k=%d t0=%d gen=%s" % (k, t0, (ga, gw)))
                for p in primes:
                    rep, nU = F5.Cert._adm(ct, p, E, (0, 0, 0, 0))
                    y = pow(3, a, p) * pow(7, w, p) % p
                    if pow(y, nU, p) != pow(rep, nU, p):
                        ok = False; msg.append("TRUE POINT EXCLUDED k=%d t0=%d E=%d p=%d" % (k, t0, E, p))
    check("T2d deep-k: rep/gen invariants + true point never excluded", ok, msg)
    # --- allowed set == rep * <gen images> exactly (small p, deep k)
    ok = True; msg = []
    for (k, t0, e2x) in [(5, 0, 0), (5, 2, 0), (6, 3, 3), (5, 5, 0)]:
        e2 = max(k - t0, 0)
        if e2x: e2 = max(e2, e2x)
        E = 2 ** e2 * 5 ** k
        kt = rnd.randrange(1, 10 ** 9, 2)
        ct = mk(F5, kt)
        for p in (11, 13, 41, 61):
            sol = F5.Cert._solve_free(ct, E)
            if sol is None: continue
            (ra, rw), gens = sol
            rep, nU = F5.Cert._adm(ct, p, E, (0, 0, 0, 0))
            # build <gen images> by explicit powers
            sub = {1}
            for ga, gw in gens:
                x = pow(3, ga, p) * pow(7, gw, p) % p
                sub |= {x * s % p for s in list(sub)}
            while True:
                new = {a * b % p for a in sub for b in ( [pow(3, ga, p) * pow(7, gw, p) % p for ga, gw in gens] )}
                if new == sub: break
                sub = new
            expect = {rep * s % p for s in sub}
            got = {y for y in range(1, p) if pow(y, nU, p) == pow(rep, nU, p)}
            if expect != got:
                ok = False; msg.append("coset mismatch k=%d t0=%d p=%d" % (k, t0, p))
            if len(sub) != nU:
                ok = False; msg.append("nU != |subgroup| k=%d t0=%d p=%d (%d vs %d)" % (k, t0, p, nU, len(sub)))
    check("T2e allowed set is exactly rep*<gens>", ok, msg)
    # --- medium-k differential (k = 5: old enumeration still feasible)
    ok = True; msg = []
    for e2 in (0, 3, 5):
        E = 2 ** e2 * 5 ** 5
        for _ in range(2):
            kt = rnd.randrange(1, 10 ** 9, 2)
            for sg in ((0, 0, 0, 0), (3, 1, 2, 0), (1, 0, 0, 1), (2, 1, 1, 1)):
                for p in (11, 9901):
                    o = allowed_old(kt, E, sg, p) or set()
                    v = allowed_new(kt, E, sg, p); v = set() if v is None else v
                    if o != v: ok = False; msg.append("medium k=5 mismatch E=%d kt=%d sg=%s p=%d" % (E, kt, sg, p))
    check("T2f medium-k (k=5) differential vs old enumeration", ok, msg)

# ---------------------------------------------------------------- T3 positive controls
def build_valid_deep(dirpath, seed, pin2=False, t0=None, k=None, qmin=None):
    """Build a VALID certificate with a deep pin: root -> mod 2, all lifts killed
    by rest primes; no sz leaves; brute box clean.  Returns (path, loadbearing)."""
    rnd = random.Random(seed)
    for _ in range(400):
        qmin = qmin or rnd.choice([4, 5, 6, 7])
        kk = k if k is not None else qmin
        t0 = t0 if t0 is not None else rnd.choice([0, 1, min(2, qmin - 1), qmin - 1])
        if not (qmin > t0 and 1 <= kk <= qmin): continue
        if pin2 and qmin < t0 + 3: continue
        c = rnd.choice([9, 18, 27, 45, 54, 7, 11, 13])
        K = rnd.randrange(1, 10 ** 12, 2) << t0
        meta = CK.make_meta([[c, 1]], K, qmin, k=kk, pin2=pin2)
        ct = F5.Cert(meta)
        clses = CK.classes_mod(2, [[c, 1]])
        rest = CK.find_killing_primes(ct, clses, 2, pmax=40000)
        if rest is None: continue
        path = os.path.join(dirpath, "valid_deep_s%d.jsonl" % seed)
        CK.write_cert(path, meta, [CK.root_node_for(meta, 2, rest)])
        res = CK.run_check(path)
        if res["result"] != "PASS": continue
        # load-bearing: same certificate without the pin must FAIL
        meta0 = CK.make_meta([[c, 1]], K, qmin, k=0, pin2=pin2)
        path0 = os.path.join(dirpath, "valid_deep_nopin_s%d.jsonl" % seed)
        CK.write_cert(path0, meta0, [CK.root_node_for(meta0, 2, rest)])
        res0 = CK.run_check(path0)
        if res0["result"] != "FAIL": continue
        # brute box sanity: no smooth points at all (independently enumerated)
        pts = CK.brute_smooth_points([[c, 1]], K, qmin, ct.t0, 11)
        if pts: continue
        return path, path0, res
    return None, None, None

def T3(dirpath):
    print("T3: positive controls (valid deep-pin certificates accepted; pin load-bearing)")
    os.makedirs(dirpath, exist_ok=True)
    cases = [dict(seed=101), dict(seed=102), dict(seed=103),
             dict(seed=104, pin2=True), dict(seed=105, t0=3, k=5, qmin=7),
             dict(seed=106, t0=1, k=6, qmin=6), dict(seed=107, pin2=True, t0=0, k=6, qmin=6)]
    for i, kw in enumerate(cases):
        path, path0, res = build_valid_deep(dirpath, **kw)
        if path is None:
            check("T3 case %d (kw=%s)" % (i, kw), False, "could not build"); continue
        check("T3 case %d (kw=%s) valid cert PASS + pin load-bearing" % (i, kw),
              res["result"] == "PASS", res["problems"])
        # re-run through the CLI form for good measure
        import io, contextlib
        r2 = CK.run_check(path)
        check("T3 case %d rerun" % i, r2["result"] == "PASS", r2["problems"])

if __name__ == "__main__":
    args = sys.argv[1:]
    todo = args or ["T1", "T2", "T3"]
    if "T1" in todo: T1()
    if "T2" in todo: T2()
    if "T3" in todo: T3(os.path.join(HERE, "ctrl"))
    print("\nFAILURES:", FAILS if FAILS else "none")
    sys.exit(1 if FAILS else 0)
