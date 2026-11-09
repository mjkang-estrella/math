#!/usr/bin/env python3
"""Round 5, v6: certificates for the elementary facts used in the L>6000 reduction.

(C1) For every j = 3..15 and every K ≡ -1 (mod 9) (sampled from our configs'
     K = 9S-1 forms and random K), 10^x ≡ -K (mod 3^j) is solvable with a
     UNIQUE class mod 3^(j-2). [transfer of r3b F1/F3; needs only K ≡ -1 mod 9]
(C2) For every j = 1..8 and every unit target u ≡ -K (mod 7) ≠ 0 with
     K = 9S-1, 10^x ≡ u (mod 7^j) has a unique class mod 6*7^(j-1).
     [transfer of r3b F2/F3]
(C3) Size inequalities: 10^L > 9216*L for L >= 5 and 10^L > 10752*L^2 for L >= 6,
     hence also for all larger L (10^L/L and 10^L/L^2 eventually increase and
     are checked monotone on the range).
(C4) t-bound: for every essential config (S_low from positions <= 10, any far
     multiset), v2(9*S_low - 1) <= 10, i.e. no deep-low config exists, so
     t = v2(K) <= 10 for every solution (K ≡ 9S_low - 1 mod 2^11).
(C5) Dichotomy residues: S mod 21 in {0,2,10,15,19,20} <=> lambda_3 ≡ mu_1
     (mod 3), where lambda_3 solves 10^x ≡ -K (mod 27) and mu_1 solves
     10^x ≡ 1-9S (mod 7); verified by direct enumeration over S mod 21.
"""
import itertools, math, random

ok = True
def chk(cond, msg):
    global ok
    if not cond:
        ok = False; print("FAIL:", msg)

# (C1)
def v3(x):
    n = 0
    while x % 3 == 0: x //= 3; n += 1
    return n
random.seed(7)
for j in range(3, 16):
    P = 3**j
    # period of 10 mod 3^j is 3^(j-2) (r3b F1); verify and count classes
    seen = {}
    per = 3**(j-2) if j >= 3 else 1
    # verify order
    chk(pow(10, per, P) == 1, f"order 3^{j}")
    chk(pow(10, per//3 if j > 3 else 1, P) != 1 or j == 3, f"order exact 3^{j}")
    vals = set(pow(10, x, P) for x in range(per))
    chk(all(v % 9 == 1 for v in vals), f"image ≡ 1 mod 9, j={j}")
    chk(len(vals) == per, f"image size, j={j}")
    for K in [9*S - 1 for S in range(0, 200)] + [9*random.randrange(0, 10**6) - 1 for _ in range(50)]:
        if K % 9 != -1 % 9: continue
        tgt = (-K) % P
        if tgt % 9 != 1: continue  # unsolvable, but K ≡ -1 mod 9 => tgt ≡ 1 mod 9
        sols = [x for x in range(per) if pow(10, x, P) == tgt]
        chk(len(sols) == 1, f"unique class j={j} K={K}")
print("(C1) unique-class transfer for 3-adic pins: done")

# (C2)
for j in range(1, 9):
    P = 7**j
    per = 6 * 7**(j-1)
    chk(pow(10, per, P) == 1, f"order 7^{j}")
    vals = set(pow(10, x, P) for x in range(per))
    chk(len(vals) == per, f"image size 7^{j}")
print("(C2) ord_{7^j}(10) = 6*7^(j-1): done")

# (C3)
def mono(f, lo, hi):
    return all(f(x+1) > f(x) for x in range(lo, hi))
chk(all(10**L > 9216*L for L in range(5, 30)), "10^L > 9216 L, L>=5")
chk(mono(lambda L: 10**L/L, 5, 200), "10^L/L increasing")
chk(all(10**L > 10752*L*L for L in range(6, 30)), "10^L > 10752 L^2, L>=6")
chk(mono(lambda L: 10**L/L**2, 6, 200), "10^L/L^2 increasing")
print("(C3) size inequalities: done")

# (C4): deep-low check over all essential configs of all five multisets
import sys
sys.path.insert(0, '.')
from v4_filter import essential_configs, v2
deeplow = 0; total = 0
for ms in [(2,2),(2,3),(2,4),(3,3),(2,2,2)]:
    delta = {}
    for d in ms: delta[d-1] = delta.get(d-1, 0) + 1
    for S_low, far in essential_configs(delta):
        total += 1
        if (9*S_low - 1) % (1 << 11) == 0: deeplow += 1
chk(deeplow == 0, "no deep-low configs")
print(f"(C4) deep-low configs: {deeplow} of {total} (t = v2(9S_low-1) <= 10 always)")

# (C5) dichotomy residues
for S21 in range(21):
    # lambda_3 mod 3: 10^x ≡ -K mod 27, K = 9S-1 => -K = 1-9S ≡ 1 - 2S mod 27... 
    # mod 3: 10^x ≡ 1, -K ≡ 1-9S ≡ 1 mod 3 -- need mod 27 for the class value;
    # lambda_3 mod 3 is determined by 10^x ≡ -K mod 27 => x ≡ ? mod 3 via
    # 10^x = (1+9)^x ≡ 1 + 9x mod 27 => 1 + 9x ≡ 1 - 9S => x ≡ -S mod 3.
    lam3 = (-S21) % 3
    # mu_1 mod 3: 3^L ≡ 1-9S ≡ 1-2S mod 7 (10 ≡ 3); 3^0=1,3^1=3,3^2=2 mod 7
    inv = {1:0, 3:1, 2:2, 6:0, 4:1, 5:2}  # 3^L mod 7 -> L mod 3
    r = (1 - 2*S21) % 7
    if r == 0:
        # S ≡ 4 (mod 7): 7 | 9n impossible for EVERY L -> B = 0 forced outright
        chk(S21 in (4, 11, 18), f"S={S21} ≡ 4 mod 7")
        print(f"  S mod 21 = {S21}: 7-adic class void (B=0 always)")
    else:
        mu1 = inv[r]
        sep = (lam3 != mu1 % 3)   # good case: A=0 or B=0 at every L
        bad = S21 in (0, 2, 10, 15, 19, 20)  # lambda3 ≡ mu1 (mod 3)
        chk(sep != bad, f"dichotomy S={S21}: sep={sep} bad={bad}")
print("(C5) dichotomy residues S mod 21: done")
print("ALL CERTIFICATES PASS" if ok else "SOME CERTIFICATES FAILED")
