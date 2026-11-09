# L2b presieve.py — count surviving classes mod M0 for X = 10^L + sum coefs 10^q + K
# using Agent A's sievelib (sig + kill_by). Usage: presieve.py A[,A2] K M0
import sys, os
sys.path.insert(0, "/home/mj-kang/Documents/Dev/math/persistence-research/verification/indep")
from sievelib import Sieve

coefs = [int(x) for x in sys.argv[1].split(",")]
K = int(sys.argv[2]); M0 = int(sys.argv[3])
S = Sieve(coefs, K, max(3, (K & -K).bit_length()), pmax=2000000)
DIM = len(coefs) + 1
surv = []
for r in range(M0 ** DIM):
    rr = []
    x = r
    for _ in range(DIM):
        rr.append(x % M0); x //= M0
    a, w = S.sig(tuple(rr), M0)
    p = S.kill_by(tuple(rr), M0, a, w)
    if p is None:
        surv.append((rr, a, w))
print(f"coefs={coefs} K={K} M0={M0}: {M0**DIM} classes, {len(surv)} survive")
for rr, a, w in surv[:40]:
    print("  ", rr, a, w)
