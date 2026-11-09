"""Run 5: test whether the k=5 analog of the k=4 machine is viable.
G_{5,n} = prod_{i=0}^{2}(1-q^{a+2i}) / ((1-q)(1-q^3)(1-q^5)(1-q^7)), a = 2n+3.
[q^m] = sum_{S subset A} (-1)^{|S|} h(m - sigma(S)), h = denumerant of {1,3,5,7}.
Tail regime: m >= a+(a+2)+(a+4) = 3a+6.
"""
import sys
sys.path.insert(0, '.')
from gkn_core import series_inv, q_pochhammer_odd, series_mul

H = series_inv(q_pochhammer_odd(1,4), 60000)   # 1/((1-q)(1-q^3)(1-q^5)(1-q^7))
def h(x): return H[x] if x >= 0 else 0

def T5(m, a):
    s = h(m)
    for c in (a, a+2, a+4): s -= h(m-c)
    s += h(m-a-(a+2)) + h(m-a-(a+4)) + h(m-(a+2)-(a+4))
    s -= h(m-a-(a+2)-(a+4))
    return s

worst = None
neg = []
for n in range(0, 200):
    a = 2*n+3
    m0 = 3*a+6
    if m0 + 4000 >= len(H): break
    for m in range(m0, m0+3000):
        t = T5(m, a)
        if t < 0:
            neg.append((n,a,m,t))
            if len(neg) > 5: break
        if worst is None or t < worst[0]: worst = (t,n,m)
    if len(neg) > 5: break
print("k=5 tail-regime scan (n<200, window 3000): negatives:", neg[:5], "count", len(neg))
print("worst:", worst)

# initial-segment regimes for k=5 (partial activity), quick scan
neg2 = []
for n in range(0, 200):
    a = 2*n+3
    if 3*a+6 >= len(H): break
    for m in range(0, 3*a+6):
        t = T5(m, a)
        if t < 0:
            neg2.append((n,a,m,t))
            if len(neg2) > 5: break
    if len(neg2) > 5: break
print("k=5 full scan m<3a+6: negatives:", neg2[:5], "count", len(neg2))

# cross-check T5 against direct series
for n in [0,1,2,3,10]:
    a = 2*n+3
    g = series_mul(q_pochhammer_odd(a,3), series_inv(q_pochhammer_odd(1,4), 4000))[:4001]
    print(f"k=5 n={n}: direct min coeff (m<=4000): {min(g)}")
