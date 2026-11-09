# Corrected O(1/t) local expansion of Delta(1_B) = T(1_B)+T(-1_B)-2T(0) (units u = h_o/(2t)):
#   singles a in B:            -3 (continuum) + lattice: total 0 (even) / -6 (odd)
#   pairs a,b in B:            P2(pi_a,pi_b)   (2-D lattice second difference along (1,1), unit density)
#   cross pairs a in B, b not: Q2(pi_a,pi_b)   (2-D lattice second difference along (1,0); continuum 0)
# Consistency: Delta(1_{g=1}) must vanish for EVERY parity functional psi' (exact identity).
# One-coordinate move: lim t*(8 sigma(e_j) - 1) = 4 * (h_o/2) * Delta(1_{g perp}) = 2 h_o Delta(1_{gperp}).
from fractions import Fraction
import itertools
def h2(za, zb):
    if za < 0 or zb < 0: return Fraction(0)
    return Fraction(1, 1 + (za == 0) + (zb == 0))
def sec(pa, pb, ya, yb, R=30):
    s = Fraction(0)
    for i in range(-R, R + 1):
        for j in range(-R, R + 1):
            za, zb = pa + 2 * i, pb + 2 * j
            s += 4 * (h2(za + ya, zb + yb) + h2(za - ya, zb - yb) - 2 * h2(za, zb))
    return s
def single(p): return sec(p, 1, 1, 0, R=30) if False else None
P2 = {(p, q): sec(p, q, 1, 1) for p in (0, 1) for q in (0, 1)}
Q2 = {(p, q): sec(p, q, 1, 0) for p in (0, 1) for q in (0, 1)}
# the 2-D sums along (1,1) include the two strips; at unit density strips cancel, so P2 is the pure pair part
print('P2', {k: str(v) for k, v in P2.items()}, ' Q2', {k: str(v) for k, v in Q2.items()})
def fval(f, a): return bin(f & a).count('1') & 1
SING = {0: Fraction(0), 1: Fraction(-6)}
def Delta(B, par):
    s = sum(SING[par[a]] for a in B)
    s += sum(P2[(par[a], par[b])] for a, b in itertools.combinations(B, 2))
    s += sum(Q2[(par[a], par[b])] for a in B for b in range(1, 8) if b not in B)
    return s
ho = 0.00833056532535052
for g in [1]:
    Bp = [a for a in range(1, 8) if fval(g, a) == 0]; B1 = [a for a in range(1, 8) if fval(g, a) == 1]
    for psi in range(8):
        par = {a: fval(psi, a) for a in range(1, 8)}
        d1 = Delta(B1, par); dp = Delta(Bp, par)
        print("psi'=%d (g=1): Delta(1_g1) = %s [must be 0]   Delta(1_gperp) = %s   predicted lim t*(8sigma(e_j)-1) = %+.5f"
              % (psi, d1, dp, 2 * ho * float(dp)))
