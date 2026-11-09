# Morse link numbers L_n = weighted Catalan numbers C^b_n, b(h) = (2h+1)^2 (Postnikov; Gao-Gu arXiv:1908.03914).
# C^b_n = sum over Dyck paths of length 2n of prod over up-steps from height h of b(h).
# Test Conjecture (Gao-Gu): exists 3-adic alpha s.t. for odd n>=3, v3(L_n - 1) depends only on
# (v3(n-alpha), last ternary digit of (n-alpha)/3^{v3(n-alpha)}).
import sys, json
N = int(sys.argv[1]); M = int(sys.argv[2]); Kmax = int(sys.argv[3])
mod = 3**M
# DP over steps: f[h] = weighted count of paths of current length ending at height h
L = [0]*(N+1)
f = [0]*(N+2); f[0] = 1
for step in range(1, 2*N+1):
    g = [0]*(N+2)
    for h in range(0, min(step, 2*N-step+1, N)+1):
        val = 0
        if h >= 1: val += f[h-1]*((2*(h-1)+1)**2)   # up-step from h-1
        if h+1 <= N: val += f[h+1]                  # down-step from h+1
        g[h] = val % mod
    f = g
    if step % 2 == 0: L[step//2] = f[0]
def v3(x, cap):
    if x % mod == 0: return cap
    c = 0
    while x % 3 == 0: x //= 3; c += 1
    return c
# sanity: first values (Postnikov: 1, 1, 10, 325? check by brute small)
small = [L[i] for i in range(6)]
val = {n: v3((L[n]-1) % mod, M) for n in range(3, N+1, 2)}
# alpha tree search
alive = [(0, 0)]  # (alpha mod 3^K, K)
log = []
for K in range(1, Kmax+1):
    new = []
    for a, _ in alive:
        for d in range(3):
            A = a + d*3**(K-1)
            F = {}; ok = True
            for n, w in val.items():
                if w >= M: continue
                x = (n - A) % 3**K
                if x == 0: continue  # v >= K: undetermined at this level
                v = 0; y = n - A
                while (y % 3**(v+1)) == 0: v += 1
                dig = (y // 3**v) % 3
                key = (v, dig)
                if key in F and F[key] != w: ok = False; break
                F[key] = w
            if ok: new.append((A, K))
    alive = new
    log.append({'K': K, 'alive_count': len(alive), 'alive': [a for a, _ in alive][:20]})
    print('K', K, 'alive residues alpha mod 3^K:', len(alive), [a for a, _ in alive][:12], flush=True)
    if not alive: break
print('first L_n mod 3^M:', small)
print('v3(L_n-1) for odd n<=60:', {n: val[n] for n in range(3, 61, 2)})
