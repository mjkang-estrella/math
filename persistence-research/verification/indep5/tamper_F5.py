"""[F5] Tamper tests: certificates that F5 must reject.
Run:  bash -c 'ulimit -v 6000000; python3 -I tamper_F5.py'

T4a  pin_digits > qmin (meta-level rejection), several shapes.
T4b  a genuine smooth point planted in an unlisted lift of a deep-pin certificate
     with t0 = v2(K) >= 1: F5 must refuse to kill it (certificate rejected, the
     planted lift named).  A checker that forgot to divide out 2^t0 (modulus
     2^k * 5^k against K instead of 2^(k-t0) * 5^k against K/2^t0) would wrongly
     accept the same file -- this establishes that the test discriminates.
T4c  same planting with t0 = 0 (pure 5-adic deep pin).
"""
import sys, os, json, random
sys.dont_write_bytecode = True
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import check_sym_F5 as F5
import certkit as CK

FAILS = []
def check(name, cond, msg=""):
    print(("  ok   " if cond else "  FAIL ") + name + ("  " + str(msg) if msg and not cond else ""))
    if not cond: FAILS.append(name + " " + str(msg))

def primes_up_to(n):
    return [p for p in CK._primes(n) if p > 7]

def build_planted(dirpath, seed, t0, k=None, qmin=None, Lmin=12):
    """Certificate whose domain contains a genuine smooth point (L, q), L >= Lmin so
    that it is invisible to the L <= 11 brute box, and NOT declared anywhere.
    The other lifts mod 2 are killed by rest primes, so the only reason for
    rejection is the planted lift surviving."""
    rnd = random.Random(seed)
    for _ in range(2000):
        qmin = qmin if qmin is not None else rnd.choice([4, 5, 6, 7, 11])
        kk = k if k is not None else qmin
        t0v = t0 if t0 is not None else rnd.choice([0, 1, 2])
        if not (qmin > t0v and 1 <= kk <= qmin): continue
        c = rnd.choice([9, 18, 27, 45, 54, 7, 11, 13])
        L = Lmin + rnd.randint(0, 1)
        q = rnd.randrange(max(qmin, Lmin - 2), L)
        a = rnd.randrange(3, 45); w = rnd.randrange(2, 30)
        N = (1 << t0v) * 3 ** a * 7 ** w
        X0 = 10 ** L + c * 10 ** q
        K = N - X0
        if K <= 0: continue
        if K % (1 << t0v) or (K >> t0v) % 2 == 0: continue
        # brute box must stay clean (no smooth points with L <= 11)
        if CK.brute_smooth_points([[c, 1]], K, qmin, t0v, 11): continue
        meta = CK.make_meta([[c, 1]], K, qmin, k=kk)
        ct = F5.Cert(meta)
        assert ct.t0 == t0v
        planted = (L % 2, (q % 2,))
        others = [cl for cl in CK.classes_mod(2, [[c, 1]]) if cl != planted]
        rest = CK.find_killing_primes(ct, others, 2, pmax=40000)
        if rest is None: continue
        # independent sanity: the planted point really is smooth and in the domain
        X = 10 ** L + K + c * 10 ** q
        assert X == N
        path = os.path.join(dirpath, "planted_s%d.jsonl" % seed)
        CK.write_cert(path, meta, [CK.root_node_for(meta, 2, rest)])
        return path, planted, str(planted), meta
    return None, None, None, None

class ForgotDivideCert(F5.Cert):
    """Tampered checker: pin congruence 3^a7^w == K (mod 2^k * 5^k) — the 2^t0 was
    NOT divided out (K used in place of K/2^t0, and exponent k instead of k-t0)."""
    def __init__(self, meta):
        super().__init__(meta)                 # original Cert.__init__ (bound at class creation)
        self.kt = self.K                       # [TAMPER] K instead of K/2^t0
    def Eset(self, variant):
        e2 = 0; e5 = 0
        if self.pin2 and variant in ('p2', 'both'): e2 = 3
        if self.k and variant in ('tail', 'both'):
            e2 = max(e2, self.k); e5 = self.k  # [TAMPER] 2^k, not 2^max(k-t0,0)
        return 2 ** e2 * 5 ** e5

def T4(dirpath):
    os.makedirs(dirpath, exist_ok=True)
    print("T4a: pin_digits > qmin must be rejected at meta level")
    variants = [dict(qmin=3, k=5), dict(qmin=6, k=7), dict(qmin=4, k=6), dict(qmin=7, k=8)]
    for i, v in enumerate(variants):
        meta = CK.make_meta([[9, 1]], 12345, v['qmin'], k=v['k'])
        path = os.path.join(dirpath, "tamper_k%d_q%d.jsonl" % (v['k'], v['qmin']))
        CK.write_cert(path, meta, [CK.root_node_for(meta, 2, [11])])
        res = CK.run_check(path)
        check("T4a.%d k=%d > qmin=%d rejected" % (i, v['k'], v['qmin']),
              res["result"] == "FAIL" and any("pin_digits" in p for p in res["problems"]),
              res["problems"])

    print("T4b: planted smooth point, t0 >= 1 deep pin (modulus-does-not-divide discriminator)")
    for seed, t0, kk, qmin in [(201, 1, 11, 11), (202, 2, 6, 6), (203, 3, 5, 7), (204, 1, 6, 6)]:
        path, planted, planteds, meta = build_planted(dirpath, seed, t0, k=kk, qmin=qmin)
        if path is None:
            check("T4b seed %d build" % seed, False, "could not build"); continue
        res = CK.run_check(path)
        named = any("neither child nor killed" in p and planteds in p for p in res["problems"])
        check("T4b seed %d (t0=%d): F5 rejects naming planted lift %s" % (seed, t0, planteds),
              res["result"] == "FAIL" and named, res["problems"])
        # discriminator: the forgot-to-divide checker accepts the same file
        resw = CK.check_with_patched(path, ForgotDivideCert)
        check("T4b seed %d: forgot-divide checker wrongly accepts" % seed,
              resw["result"] == "PASS", resw["problems"])
        # kill-level discriminator on the planted class itself
        ct_ok = F5.Cert(meta); ct_bad = ForgotDivideCert(meta)
        p_ok = [ct_ok.kills(p, planted, 2)[0] for p in primes_up_to(200)]
        p_bad = [ct_bad.kills(p, planted, 2)[0] for p in primes_up_to(200)]
        check("T4b seed %d: planted class never killed by F5, always by forgot-divide" % seed,
              not any(p_ok) and all(p_bad), (p_ok, p_bad))

    print("T4c: planted smooth point, t0 = 0 (pure 5-adic deep pin)")
    for seed, qmin in [(211, 11), (212, 6), (213, 7)]:
        path, planted, planteds, _m = build_planted(dirpath, seed, 0, qmin=qmin)
        if path is None:
            check("T4c seed %d build" % seed, False, "could not build"); continue
        res = CK.run_check(path)
        named = any("neither child nor killed" in p and planteds in p for p in res["problems"])
        check("T4c seed %d: F5 rejects naming planted lift %s" % (seed, planteds),
              res["result"] == "FAIL" and named, res["problems"])

if __name__ == "__main__":
    T4(os.path.join(HERE, "tamper"))
    print("\nFAILURES:", FAILS if FAILS else "none")
    sys.exit(1 if FAILS else 0)
