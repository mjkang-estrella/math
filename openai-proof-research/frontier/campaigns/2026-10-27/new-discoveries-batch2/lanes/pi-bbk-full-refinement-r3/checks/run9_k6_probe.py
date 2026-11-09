"""Run 9: k=6 reconnaissance — does the tail-regime quadrant certificate survive on a sample?
G_{6,n}: A = {a,a+2,a+4,a+6}, B = {1,3,5,7,9,11}, period L = 3465, h degree 5.
T6(m,a) = sum_{S subset A} (-1)^{|S|} h(m - sigma(S)); tail regime m >= 4a+12 (quadrant).
Sample (alpha, rho) classes; 21-point staircase (i+k <= 5).
"""
import sys, math
from fractions import Fraction as F
from itertools import combinations
sys.path.insert(0, '.')
from gkn_core import series_inv, q_pochhammer_odd

L = 3465
N = 115000
H = series_inv(q_pochhammer_odd(1, 6), N)
def h(x): return H[x] if 0 <= x < len(H) else None

def T6(m, a):
    s = F(h(m)) if m >= 0 else F(0)
    for r in range(1, 5):
        for comb in combinations([0, 2, 4, 6], r):
            sg = r*a + sum(comb)
            if m - sg >= 0:
                s += F(-1)**r * h(m - sg)
    return s

fails = []; tested = 0
alphas = [3, 50, 100, 500, 1000, 1732, 2000, 2500, 3000, 3464, 104, 105, 210, 315, 525]
rhos   = [0, 1, 7, 100, 500, 1000, 1733, 2000, 2500, 3000, 3464, 105, 210, 315, 525]
for alpha in alphas:
    alpha0 = alpha if alpha >= 3 else alpha + L
    for rho in rhos:
        def m0(t):
            b = 4*(alpha0 + L*t) + 12
            return b + ((rho - b) % L)
        vals = {(i,j): T6(m0(i) + L*j, alpha0 + L*i) for i in range(6) for j in range(6-i)}
        data = {}
        for i in range(6):
            for j in range(6-i):
                d = F(0)
                for p in range(i+1):
                    for q in range(j+1):
                        d += F((-1)**(i+j-p-q)) * math.comb(i,p) * math.comb(j,q) * vals[(p,q)]
                data[(i,j)] = d
        tested += 1
        neg = {k: str(v) for k, v in data.items() if v < 0}
        if neg: fails.append((alpha, rho, neg))
print("k=6 tail sample: classes tested:", tested, " failures:", len(fails))
for f_ in fails[:8]: print("  ", f_)
