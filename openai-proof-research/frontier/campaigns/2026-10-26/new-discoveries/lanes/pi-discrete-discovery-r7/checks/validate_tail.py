import sys
sys.path.insert(0, '/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-26/new-discoveries/lanes/pi-discrete-discovery-r7/checks')
from fractions import Fraction as F
from gkn_tail import tail_data, series_div_frac, trim, pmul, F
from gkn_series import G_num_den

def check(k, n, extra=300):
    C, fds = tail_data(k, n)
    m0 = n*(2*k+n-2)
    N, D = G_num_den(k, n)
    M = m0 + extra
    c = series_div_frac(N, D, M)
    ok = True
    for m in range(m0, M+1):
        t = C + sum(fds[d][m % d] for d in fds)
        if t != c[m]:
            print(f"MISMATCH k={k} n={n} m={m}: tail={t} direct={c[m]}")
            ok = False
            break
    print(f"k={k} n={n}: tail formula {'OK' if ok else 'FAIL'} (checked m in [{m0},{M}]); C={C}; active d: {sorted(fds)}")
    return ok

for (k,n) in [(4,2),(5,3),(6,4),(7,3),(10,5),(8,6),(12,7),(3,4),(2,5),(5,8)]:
    check(k,n)
