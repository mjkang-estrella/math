# L2b/diag_ladder.py — for an unresolved ladder class, check every aligned prime's test.
import sys, os
sys.path.insert(0, "/home/mj-kang/Documents/Dev/math/persistence-research/verification/indep")
from sievelib import Sieve
from universe import build

coefs = [18]; K = 98
S = Sieve(coefs, K, 3, pmax=2000000)
r = (100818950405, 3); M = 226842638400
t0 = 1
a0 = 12; w0 = 0
U = build(2000000, 64*729*25*2401, None)
n_ok = n_bad = 0
shown = 0
for (p, d, o3, o7) in U:
    if M % d: continue
    X = (pow(10, r[0] % d, p) + coefs[0]*pow(10, r[1] % d, p) + K) % p
    T = X * pow(2, -t0, p) % p
    if T == 0:
        print(f"p={p} d={d}: T=0 -> KILL"); n_bad += 1; continue
    x = T * pow(3, -a0, p) % p * pow(7, -w0, p) % p
    # w exact 0 => kill iff x not in <3>
    if pow(x, o3, p) != 1:
        n_bad += 1
        if shown < 5:
            print(f"p={p} d={d}: KILLS (x={x} not in <3>)"); shown += 1
    else:
        n_ok += 1
print(f"aligned primes: {n_ok} survive-class, {n_bad} kill")
