"""
BCGN-style cascade for the 1-insertion families (Pi(n) = delta, delta in 1..9).

Family: n = R_L + (delta-1)*10^e  (0 <= e < L),  Pi(n) = delta.
Equation: 9n = 10^L + 9(delta-1)10^e - 1 = 2^t * 3^(u+2) * 7^w,  t <= t_max(delta) [Fonga V].

Moduli: M_K = (10^(12*2^K) - 1) / 189 = M_{K-1} * (10^(12*2^(K-1)) + 1).
  3 and 7 are UNITS mod M_K. ord_{M0}(3)=9900, ord_{M0}(7)=900.
Stage 0: positions mod 12; (u+2, w) known mod (9900, 900).
Stage 1: positions mod 24; (u+2, w) known mod (849915000, 673200).
Stage 2: positions mod 48; (u+2, w) known mod (o3_2, o7_2) via 2-var congruences.

All arithmetic exact.
"""
import sys, time
from bisect import bisect_left
from math import gcd
sys.set_int_max_str_digits(1000000)
from ntlib import factorint, invmod

M0 = (10**12 - 1) // 189
assert M0 == 5291005291 and factorint(M0) == {11: 1, 13: 1, 37: 1, 101: 1, 9901: 1}
O3_0, O7_0 = 9900, 900

# ---------------- image table for stage 0 ----------------
def build_image():
    """Sorted packed keys: value*2^24 + (U*900+W). Returns lookup fn."""
    t0 = time.time()
    keys = []
    ap = 1
    for U in range(O3_0):
        pw = ap
        base = U * O7_0
        for W in range(O7_0):
            keys.append(((pw << 24) | (base + W)))
            pw = pw * 7 % M0
        ap = ap * 3 % M0
    keys.sort()
    print(f"  image table: {len(keys)} entries in {time.time()-t0:.1f}s", flush=True)
    def lookup(V):
        i = bisect_left(keys, V << 24)
        if i < len(keys) and (keys[i] >> 24) == V:
            return keys[i] & 0xFFFFFF
        return None
    return lookup

# ---------------- stage 0 ----------------
def stage0(delta, t_max, lookup):
    c = 9 * (delta - 1)
    p10 = [pow(10, i, M0) for i in range(12)]
    out = []
    for e12 in range(12):
        be = c * p10[e12]
        for L12 in range(12):
            base = (p10[L12] + be - 1) % M0
            for t in range(t_max + 1):
                V = base * invmod(pow(2, t, M0), M0) % M0
                hit = lookup(V)
                if hit is not None:
                    U, W = divmod(hit, O7_0)
                    out.append((L12, e12, t, U, W))
    return out

# ---------------- per-prime 2D dlog (enumerative; small domains) ----------------
def solve_2d_prime(p, A, B, target, s3, s7):
    """Solve A^hu * B^hw == target (mod p) for (hu mod s3, hw mod s7)."""
    table = {}
    x = 1
    for hw in range(s7):
        if x not in table:
            table[x] = hw
        x = x * B % p
    sols = []
    Ainv = invmod(A, p)
    x = target
    for hu in range(s3):
        hw = table.get(x)
        if hw is not None:
            sols.append((hu, hw))
        x = x * Ainv % p
    return sols

def crt1(a1, m1, a2, m2):
    g = gcd(m1, m2)
    if (a2 - a1) % g:
        return None
    l = m1 // g * m2
    m1g, m2g = m1 // g, m2 // g
    t = ((a2 - a1) // g) * invmod(m1g % m2g, m2g) % m2g
    return ((a1 + m1 * t) % l, l)

def merge_classes(sols_by_prime, periods):
    """CRT-merge per-prime (hu mod s3p, hw mod s7p) classes.
    Returns list of (hu, Lu, hw, Lw)."""
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

# ---------------- stage 1 ----------------
M1 = M0 * 73 * 137 * 99990001
M1_NEW = [(73, 12, 24), (137, 136, 68), (99990001, 16665000, 39600)]
O3_1, O7_1 = 849915000, 673200
LAM1, MU1 = O3_1 // O3_0, O7_1 // O7_0   # 85850, 748

def stage1(surv0, delta):
    """Refine stage-0 survivors mod M1. Output: (L24, e24, t, U1, W1, hu, hw)."""
    p10 = [pow(10, i, M1) for i in range(24)]
    c = 9 * (delta - 1)
    out = []
    for (L12, e12, t, U, W) in surv0:
        it2 = invmod(pow(2, t, M1), M1)
        for L24 in (L12, L12 + 12):
            for e24 in (e12, e12 + 12):
                lhs = (p10[L24] + c * p10[e24] - 1) % M1
                V = lhs * it2 % M1
                sols_by, periods, dead = [], [], False
                for (p, o3p, o7p) in M1_NEW:
                    s3p = o3p // gcd(9900, o3p)
                    s7p = o7p // gcd(900, o7p)
                    A, B = pow(3, 9900, p), pow(7, 900, p)
                    target = V * invmod(pow(3, U % o3p, p) * pow(7, W % o7p, p) % p, p) % p
                    sols = solve_2d_prime(p, A, B, target, s3p, s7p)
                    if not sols:
                        dead = True
                        break
                    sols_by.append(sols); periods.append((s3p, s7p))
                if dead:
                    continue
                for (hu, Lu, hw, Lw) in merge_classes(sols_by, periods):
                    out.append((L24, e24, t, (U + 9900 * hu) % O3_1, (W + 900 * hw) % O7_1, hu, hw))
    return sorted(set(out))
