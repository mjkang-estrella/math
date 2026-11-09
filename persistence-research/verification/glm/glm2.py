"""glm2.py — memory-bounded BCGN-style cascade for the single-exceptional-digit
1-insertion families.

Family F_delta (delta = 1..9):  n = R_L + (delta-1)*10^e,  L >= 1, 0 <= e < L
  (decimal digits: all 1s except one digit equal to delta).  9n = 10^L + 9(delta-1)10^e - 1.

(★delta)   9n = 2^t * 3^(u+2) * 7^w,   t <= t_max(delta)   [Fonga V, verified]

Cascade moduli M_K = (10^(12*2^K)-1)/189:
  stage 0: (L,e) mod 12,      (u+2,w) mod (9900, 900)          [M0]
  stage 1: (L,e) mod 24,      (u+2,w) mod (849915000, 673200)  [M1]
  stage 2: (L,e) mod 48,      u+2 = U1 + O3_1*k_u, k_u ≡ r (mod kappa_u);
                               w   = W1 + O7_1*k_w, k_w ≡ r (mod kappa_w)   [M2]

Stage 2 is a GENERATOR: classes are streamed one at a time into the pinning
checker (Theorem P of notes/proof_attempt_glm.md) — O(1) memory.

Run everything under:  bash -c 'ulimit -v 3000000; python3 -I glm2.py ...'
"""
import sys, time, json, random, argparse, os
from math import gcd, log10, ceil, floor, isqrt

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
sys.set_int_max_str_digits(30000000)

# ---------------------------- constants (asserted) ----------------------------
M0 = (10**12 - 1) // 189
O3_0, O7_0 = 9900, 900                      # ord_{M0}(3), ord_{M0}(7); ord_{M0}(10)=12
P1 = [(73, 12, 24), (137, 136, 68), (99990001, 16665000, 39600)]  # (p, ord_p(3), ord_p(7))
M1 = M0 * 73 * 137 * 99990001               # = (10^24-1)/189
O3_1, O7_1 = 849915000, 673200              # ord_{M1}(3), ord_{M1}(7)
M2 = M1 * 17 * 5882353 * 9999999900000001   # = (10^48-1)/189
BIGP = 9999999900000001                     # largest new prime of stage 2 (10^24+1 factor)

# stage-2 small primes: (p, ord_p(3), ord_p(7))
P2_SMALL = [(17, 16, 16), (5882353, 735294, 210084)]

LOG10_2 = 0.30102999566398119521
LOG10_3 = 0.47712125471966243540
LOG10_7 = 0.84509804001425683071
LOG10_8_2 = log10(8.2)

T_MAX = {1: 0, 2: 4, 3: 0, 4: 2, 5: 0, 6: 4, 7: 0, 8: 3, 9: 0}   # Fonga V, verified


def _assert_constants():
    assert M0 == 5291005291
    assert pow(3, O3_0, M0) == 1 and pow(7, O7_0, M0) == 1 and pow(10, 12, M0) == 1
    for q in (2, 3, 5, 11):
        assert pow(3, O3_0 // q, M0) != 1
        if O7_0 % q == 0:
            assert pow(7, O7_0 // q, M0) != 1
    # uniqueness of the (U,W) representation mod M0
    x, s3 = 1, set()
    for _ in range(O3_0):
        s3.add(x); x = x * 3 % M0
    x, s7 = 1, set()
    for _ in range(O7_0):
        s7.add(x); x = x * 7 % M0
    assert len(s3) == O3_0 and len(s7) == O7_0 and (s3 & s7) == {1}
    assert M1 == (10**24 - 1) // 189
    assert pow(3, O3_1, M1) == 1 and pow(7, O7_1, M1) == 1
    for (p, o3p, o7p) in P1:
        assert pow(3, o3p, p) == 1 and pow(7, o7p, p) == 1
    assert M2 == (10**48 - 1) // 189
    assert pow(3, O3_1, BIGP) != 1 and pow(7, O7_1, BIGP) != 1


# ---------------------------- generic helpers ----------------------------
def crt1(a1, m1, a2, m2):
    """Solve x ≡ a1 (mod m1), x ≡ a2 (mod m2).  Returns (x, lcm) or None."""
    g = gcd(m1, m2)
    if (a2 - a1) % g:
        return None
    l = m1 // g * m2
    m1g, m2g = m1 // g, m2 // g
    t = ((a2 - a1) // g) * pow(m1g % m2g, -1, m2g) % m2g
    return ((a1 + m1 * t) % l, l)


def solve_2d_prime(p, A, B, target, s3, s7):
    """All (hu mod s3, hw mod s7) with A^hu * B^hw == target (mod p)."""
    table = {}
    x = 1
    for hw in range(s7):
        if x not in table:
            table[x] = hw
        x = x * B % p
    sols = []
    Ainv = pow(A, -1, p)
    x = target % p
    for hu in range(s3):
        hw = table.get(x)
        if hw is not None:
            sols.append((hu, hw))
        x = x * Ainv % p
    return sols


def merge_classes(sols_by_prime, periods):
    classes = [(0, 1, 0, 1)]
    for sols, (s3p, s7p) in zip(sols_by_prime, periods):
        new = []
        for (hu1, Lu1, hw1, Lw1) in classes:
            for (hu2, hw2) in sols:
                cu = crt1(hu1, Lu1, hu2, s3p)
                cw = crt1(hw1, Lw1, hw2, s7p)
                if cu is not None and cw is not None:
                    new.append((cu[0], cu[1], cw[0], cw[1]))
        classes = new
        if not classes:
            return []
    return classes


# ---------------------------- stage 0 ----------------------------
def stage0(delta, t_max):
    """Survivors (L12, e12, t, U, W):  V := (10^L + 9(delta-1)10^e - 1) 2^{-t}
    ≡ 3^U 7^W (mod M0).  Meet-in-the-middle, O(1) memory."""
    c = 9 * (delta - 1)
    p10 = [pow(10, i, M0) for i in range(12)]
    inv2 = pow(2, -1, M0)
    inv3 = pow(3, -1, M0)
    tbl7 = {}
    x = 1
    for W in range(O7_0):
        tbl7[x] = W
        x = x * 7 % M0
    out = []
    for e12 in range(12):
        ce = c * p10[e12] % M0
        for L12 in range(12):
            x = (p10[L12] + ce - 1) % M0
            for t in range(t_max + 1):
                V = x
                y = V
                for U in range(O3_0):
                    W = tbl7.get(y)
                    if W is not None:
                        out.append((L12, e12, t, U, W))
                        break
                    y = y * inv3 % M0
                x = x * inv2 % M0
    return out


# ---------------------------- stage 1 ----------------------------
def stage1(surv0, delta):
    p10 = [pow(10, i, M1) for i in range(24)]
    c = 9 * (delta - 1)
    out = []
    for (L12, e12, t, U, W) in surv0:
        it2 = pow(2, -t, M1)
        for L24 in (L12, L12 + 12):
            for e24 in (e12, e12 + 12):
                V = (p10[L24] + c * p10[e24] - 1) * it2 % M1
                sols_by, periods, dead = [], [], False
                for (p, o3p, o7p) in P1:
                    s3p = o3p // gcd(9900, o3p)
                    s7p = o7p // gcd(900, o7p)
                    A, B = pow(3, 9900, p), pow(7, 900, p)
                    base = pow(3, U % o3p, p) * pow(7, W % o7p, p) % p
                    target = V * pow(base, -1, p) % p
                    sols = solve_2d_prime(p, A, B, target, s3p, s7p)
                    if not sols:
                        dead = True
                        break
                    sols_by.append(sols)
                    periods.append((s3p, s7p))
                if dead:
                    continue
                for (hu, Lu, hw, Lw) in merge_classes(sols_by, periods):
                    out.append((L24, e24, t, (U + 9900 * hu) % O3_1,
                                (W + 900 * hw) % O7_1, hu, hw))
    return sorted(set(out))


# ---------------------------- stage 2 context ----------------------------
class Stage2Ctx:
    """Precomputations for the streaming stage-2 sieve."""

    def __init__(self):
        self.p10 = [pow(10, i, M2) for i in range(48)]
        self._inv2t = {}
        # p = 17
        self.A17 = pow(3, O3_1, 17)
        self.B17 = pow(7, O7_1, 17)
        self.s3_17 = 2
        self.s7_17 = 1
        assert pow(self.A17, self.s3_17, 17) == 1 and pow(self.B17, self.s7_17, 17) == 1
        # p = 5882353
        p = 5882353
        self.s3_588, self.s7_588 = 122549, 17507
        self.o3p_588, self.o7p_588 = 735294, 210084
        self.A588 = pow(3, O3_1, p)
        self.A588inv = pow(self.A588, -1, p)
        B = pow(7, O7_1, p)
        assert pow(self.A588, self.s3_588, p) == 1 and pow(B, self.s7_588, p) == 1
        self.tbl588 = {}
        x = 1
        for kw in range(self.s7_588):
            self.tbl588[x] = kw
            x = x * B % p
        assert len(self.tbl588) == self.s7_588
        # B must lie in <A> mod 5882353 so that membership in <A,B> = <A> is testable
        k = self._dlog_in(self.A588, B, p, self.s3_588)
        assert k is not None and pow(B, self.s3_588, p) == 1
        # big prime (Pohlig-Hellman; p-1 smooth)
        self.bigp = BIGP
        self.bigN = BIGP - 1
        from ntlib import factorint
        fs = factorint(self.bigN)
        assert set(fs) == {2, 3, 5, 11, 73, 101, 137}, fs
        self.o3p_big = self._order(3, fs)
        self.o7p_big = self._order(7, fs)
        assert self.o3p_big == 1666666650000000 and self.o7p_big == self.bigN
        A = pow(3, O3_1, self.bigp)
        Bb = pow(7, O7_1, self.bigp)
        self.qctx = []
        for (q, f) in sorted(fs.items()):
            qq = q ** f
            while True:
                h = random.randrange(2, self.bigp - 1)
                g = pow(h, self.bigN // qq, self.bigp)
                if g != 1 and pow(g, qq // q, self.bigp) != 1:
                    break  # order exactly qq
            m = isqrt(qq) + 1
            baby = {}
            x = 1
            for j in range(m):
                if x not in baby:
                    baby[x] = j
                x = x * g % self.bigp
            gm = pow(g, -m, self.bigp)
            aq = self._dlog(baby, gm, pow(A, self.bigN // qq, self.bigp), qq, m)
            bq = self._dlog(baby, gm, pow(Bb, self.bigN // qq, self.bigp), qq, m)
            self.qctx.append((qq, baby, gm, m, aq, bq))

    def _order(self, a, fs):
        o = self.bigN
        for q in fs:
            while o % q == 0 and pow(a, o // q, self.bigp) == 1:
                o //= q
        return o

    def _dlog_in(self, g, val, p, order):
        """dlog of val base g where ord(g) = order (small). Returns None if absent."""
        m = isqrt(order) + 1
        baby = {}
        x = 1
        for j in range(m):
            if x not in baby:
                baby[x] = j
            x = x * g % p
        gm = pow(g, -m, p)
        y = val % p
        for i in range(m + 1):
            j = baby.get(y)
            if j is not None:
                return (i * m + j) % order
            y = y * gm % p
        return None

    def _dlog(self, baby, gm, val, qq, m):
        if val == 1:
            return 0
        y = val
        for i in range(m + 1):
            j = baby.get(y)
            if j is not None:
                return (i * m + j) % qq
            y = y * gm % self.bigp
        raise ValueError("dlog failed")

    def inv2t(self, t):
        v = self._inv2t.get(t)
        if v is None:
            v = self._inv2t[t] = pow(2, -t, M2)
        return v

    def ku_projection(self, V, U1, W1):
        """Necessary condition on k_u from the big prime: k_u ≡ x0 (mod P),
        or None if the congruence A^{k_u} B^{k_w} = target is unsolvable."""
        p, N = self.bigp, self.bigN
        if V % p == 0:
            # 3^{u+2} 7^w is a unit mod p; V = 0 makes the congruence unsolvable
            return None
        base = pow(3, U1 % self.o3p_big, p) * pow(7, W1 % self.o7p_big, p) % p
        target = V * pow(base, -1, p) % p
        a, am, b, bm, c, cm = 0, 1, 0, 1, 0, 1
        for (qq, baby, gm, m, aq, bq) in self.qctx:
            Cq = pow(target, N // qq, p)
            cq = self._dlog(baby, gm, Cq, qq, m)
            r = crt1(a, am, aq, qq)
            if r is None:
                return None
            a, am = r
            r = crt1(b, bm, bq, qq)
            if r is None:
                return None
            b, bm = r
            r = crt1(c, cm, cq, qq)
            if r is None:
                return None
            c, cm = r
        assert am == bm == cm == N
        G = gcd(gcd(a, b), N)
        if c % G:
            return None
        D = gcd(b, N)
        g = gcd(a, D)
        if c % g:
            return None
        P = D // g
        x0 = ((c // g) * pow((a // g) % P, -1, P)) % P if P > 1 else 0
        return (x0, P)


# ---------------------------- stage 2 stream ----------------------------
def stage2_classes(surv1, delta, ctx, stats):
    """Yield (L48, e48, t, U1, W1, ku_res, ku_mod, kw_res, kw_mod) for every
    stage-2 survivor class.  O(1) memory."""
    c = 9 * (delta - 1)
    for (L24, e24, t, U1, W1, hu, hw) in surv1:
        it2 = ctx.inv2t(t)
        for L48 in (L24, L24 + 24):
            peL = ctx.p10[L48 % 48]
            for e48 in (e24, e24 + 24):
                V = (peL + c * ctx.p10[e48 % 48] - 1) * it2 % M2
                stats['positions'] += 1
                proj = ctx.ku_projection(V, U1, W1)
                if proj is None:
                    stats['pos_dead_bigp'] += 1
                    continue
                x0, P = proj
                base17 = pow(3, U1 % 16, 17) * pow(7, W1 % 16, 17) % 17
                t17 = V * pow(base17, -1, 17) % 17
                sols17 = solve_2d_prime(17, ctx.A17, ctx.B17, t17,
                                        ctx.s3_17, ctx.s7_17)
                if not sols17:
                    stats['pos_dead_17'] += 1
                    continue
                p = 5882353
                base58 = pow(3, U1 % ctx.o3p_588, p) * pow(7, W1 % ctx.o7p_588, p) % p
                t58 = V * pow(base58, -1, p) % p
                if pow(t58, ctx.s3_588, p) != 1:
                    stats['pos_dead_588'] += 1
                    continue
                Ainv = ctx.A588inv
                x = t58
                hit = 0
                for ku588 in range(ctx.s3_588):
                    kw588 = ctx.tbl588.get(x)
                    if kw588 is not None:
                        for (ku17, _kw17) in sols17:
                            m = crt1(ku17, ctx.s3_17, ku588, ctx.s3_588)
                            if m is None:
                                continue
                            k2 = crt1(m[0], m[1], x0, P)
                            if k2 is None:
                                continue
                            hit += 1
                            yield (L48 % 48, e48 % 48, t, U1, W1,
                                   k2[0], k2[1], kw588, ctx.s7_588)
                    x = x * Ainv % p
                if hit == 0:
                    stats['pos_dead_588'] += 1
                else:
                    stats['pos_alive'] += 1


# ---------------------------- pinning checker ----------------------------
def _xmax(base, L):
    """Conservative upper bound for the exponent x such that base^x can divide
    9n for a solution of (ST delta) with digit length <= L:  9n < 8.2*10^L, so
    base^x < 8.2*10^L.  Float estimate + slack 3; an OVER-estimate is always
    sound (it only weakens the dead-check), an under-estimate would not be."""
    return int((LOG10_8_2 + L) / log10(base)) + 3


def pow10_exp(Q):
    """Exact e with 10^e == Q, else None."""
    if Q <= 0:
        return None
    e = round(log10(Q))
    return e if 10 ** e == Q else None


def check_stream(classes, delta, L_check, found, stats, phantoms=None):
    """Consume survivor classes; pin (t, u+2, w) and check the exact equation for
    L <= L_check.  found: list of dicts (members re-derived)."""
    ucap = _xmax(3, L_check)      # u+2 <= ucap for any solution with L <= L_check
    wcap = _xmax(7, L_check)
    if phantoms is None:
        phantoms = []
    assert ucap < O3_1 and wcap < O7_1 * 17507, "pinning periods too small for L_check"
    c = 9 * (delta - 1)
    seen = {}
    for cls in classes:
        stats['classes'] += 1
        (L48, e48, t, U1, W1, ku_res, ku_mod, kw_res, kw_mod) = cls
        Pu = O3_1 * ku_mod
        Pw = O7_1 * kw_mod
        if Pu <= ucap or Pw <= wcap:
            stats['unpinned'] += 1
            continue
        U2 = U1 + O3_1 * ku_res
        if U2 < 2:
            U2 += Pu
        if U2 > ucap:
            stats['dead_ubound'] += 1
            continue
        W2 = W1 + O7_1 * kw_res
        if W2 > wcap:
            stats['dead_wbound'] += 1
            continue
        stats['pinned'] += 1
        N0 = pow(2, t) * pow(3, U2) * pow(7, W2)
        S = t * LOG10_2 + U2 * LOG10_3 + W2 * LOG10_7
        hit = None
        for L in range(max(1, floor(S) - 2), floor(S) + 3):
            if L > L_check or L % 48 != L48:
                continue
            D = N0 + 1 - 10 ** L
            if delta == 1:
                if D == 0:
                    hit = (L, 0, t, U2 - 2, W2)
                    break
                continue
            if D <= 0 or D % c:
                continue
            e = pow10_exp(D // c)
            if e is None or e >= L or e % 48 != e48:
                continue
            hit = (L, e, t, U2 - 2, W2)
            break
        if hit is not None:
            L, e, t, u, w = hit
            prev = seen.get((L, e))
            if prev is not None:
                # the same solution reached via two class variants; must agree
                assert prev == (t, u, w), f"inconsistent re-derivation at {(L, e)}"
                stats['dup_member_classes'] += 1
            else:
                seen[(L, e)] = (t, u, w)
                found.append(dict(L=L, e=e, t=t, u=u, w=w,
                                  n=(N0 // 9) if L <= 20000 else None))
                stats['member_classes'] += 1
        else:
            stats['dead_pinned'] += 1
            phantoms.append(dict(L48=L48, e48=e48, t=t, U2=U2, W2=W2,
                                 S=S, Pu=Pu, Pw=Pw))


# ---------------------------- driver ----------------------------
def load_members(path):
    out = []
    if os.path.exists(path):
        with open(path) as f:
            for line in f:
                line = line.strip()
                if not line or line.startswith("#"):
                    continue
                out.append(tuple(json.loads(line)))
    return out


def run_delta(delta, lcheck, enum_L=3000, crosscheck=True):
    from vunga import Vunga
    t0 = time.time()
    _assert_constants()
    t_max = 0 if delta == 1 else Vunga((delta,))
    assert t_max == T_MAX[delta], (delta, t_max, T_MAX[delta])
    members = [m for m in load_members(f"members_delta{delta}.jsonl") if m[0] <= enum_L]
    print(f"delta={delta}: t_max={t_max}, enum members L<={enum_L}: {len(members)}", flush=True)

    s0 = stage0(delta, t_max)
    print(f"  |s0| = {len(s0)}  ({time.time()-t0:.1f}s)", flush=True)
    for (L, e, t, u, w) in members:
        cls = (L % 12, e % 12, t, (u + 2) % O3_0, w % O7_0)
        assert cls in s0, f"stage0 lost member {(L, e, t, u, w)}"
    if crosscheck:
        import pickle
        old = pickle.load(open("level1_results.pkl", "rb"))
        assert sorted(old[delta][2]) == sorted(s0), f"stage0 mismatch vs round-1 pkl (delta {delta})"
    print("  stage0 soundness + crosscheck OK", flush=True)

    s1 = stage1(s0, delta)
    print(f"  |s1| = {len(s1)}  ({time.time()-t0:.1f}s)", flush=True)
    for (L, e, t, u, w) in members:
        cls = (L % 24, e % 24, t, (u + 2) % O3_1, w % O7_1)
        assert any(r[:5] == cls for r in s1), f"stage1 lost member {(L, e, t, u, w)}"
    if crosscheck:
        import pickle
        old = pickle.load(open("level1_results.pkl", "rb"))
        assert sorted(old[delta][3]) == sorted(s1), f"stage1 mismatch vs round-1 pkl (delta {delta})"
    print("  stage1 soundness + crosscheck OK", flush=True)

    ctx = Stage2Ctx()
    print(f"  stage2 ctx ready  ({time.time()-t0:.1f}s)", flush=True)
    stats = dict(positions=0, pos_dead_bigp=0, pos_dead_17=0, pos_dead_588=0,
                 pos_alive=0, classes=0, unpinned=0, dead_ubound=0,
                 dead_wbound=0, pinned=0, member_classes=0, dead_pinned=0,
                 dup_member_classes=0)
    found = []
    phantoms = []
    check_stream(stage2_classes(s1, delta, ctx, stats), delta, lcheck, found, stats,
                 phantoms)
    print(f"  stage2: {stats}", flush=True)

    # cross-validation: pinned re-derivation must reproduce the enum exactly (L <= enum_L)
    enum_set = sorted((L, e, t, u, w) for (L, e, t, u, w) in members)
    sieve_small = sorted((f['L'], f['e'], f['t'], f['u'], f['w'])
                         for f in found if f['L'] <= enum_L)
    assert sieve_small == enum_set, (
        f"MISMATCH delta={delta}: sieve {sieve_small[:10]}... vs enum {enum_set[:10]}...")
    print(f"  cross-validation sieve vs enum (L<={enum_L}, full (L,e,t,u,w)): EXACT MATCH",
          flush=True)

    res = dict(delta=delta, t_max=t_max, lcheck=lcheck, stats=stats,
               members=sorted(found, key=lambda f: (f['L'], f['e'])),
               phantoms=phantoms, s0=sorted(s0), s1=sorted(s1))
    with open(f"results_delta{delta}.json", "w") as f:
        json.dump(res, f)
    small = [(f['L'], f['e'], f['t'], f['u'], f['w']) for f in sorted(found, key=lambda f: (f['L'], f['e']))]
    print(f"  MEMBERS (L <= {lcheck}): {small}", flush=True)
    print(f"  done in {time.time()-t0:.1f}s", flush=True)
    return res


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--delta", type=int, required=True)
    ap.add_argument("--lcheck", type=int, default=10**7)
    ap.add_argument("--no-crosscheck", action="store_true")
    a = ap.parse_args()
    run_delta(a.delta, a.lcheck, crosscheck=not a.no_crosscheck)
