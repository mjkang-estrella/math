"""Run 3: wide sanity check of T_a(m) >= 0 for G_{4,n}, a = 2n+3 odd.
T_a(m) = h(m) - h(m-a) - h(m-a-2) + h(m-2a-2), h = denumerant{1,3,5}."""
import sys
sys.path.insert(0, '.')
from gkn_core import series_inv, q_pochhammer_odd, series_mul

H = series_inv(q_pochhammer_odd(1,3), 9000)
def h(x): return H[x] if 0 <= x < len(H) else None

worst = None
for n in range(0, 2000):
    a = 2*n+3
    mmax = 2*a+2 + 3*225 + 100
    if mmax >= len(H): break
    for m in range(0, mmax):
        t = h(m) - (h(m-a) if m-a>=0 else 0) - (h(m-a-2) if m-a-2>=0 else 0) + (h(m-2*a-2) if m-2*a-2>=0 else 0)
        if t < 0:
            print("NEGATIVE:", n, a, m, t); sys.exit()
        if worst is None or t < worst[0]: worst = (t, n, m)
print("k=4 scan: no negative coefficients. worst (min T, n, m):", worst)

# cross-check against direct series for a few n
for n in [0,1,2,5,10,30]:
    a = 2*n+3
    g = series_mul(q_pochhammer_odd(a,2), series_inv(q_pochhammer_odd(1,3), 2000))
    mn = min(g)
    print(f"n={n}: min coeff of G_{{4,{n}}} up to deg 2000 = {mn}")
