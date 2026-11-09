"""Numerical check of Ballantine-Merca Conjecture 4 (MathDB 382086):
(i)  sum_{j=0}^{3k} rho_j b6(n - j(j+1)/2) >= beta_n, strict if n >= (3k+1)(3k+2)/2
(ii) sum_{j=0}^{3k+2} rho_j b6(n - j(j+1)/2) <= beta_n, strict if n >= (3k+2)(3k+3)/2
rho_j = -2 if j = 1 mod 3 else 1; beta_n = (-1)^m if n = m(3m-2), m in Z, else 0.
Usage: bm_conj4.py N kmax"""
import sys
N, kmax = int(sys.argv[1]), int(sys.argv[2])
# b6 via product prod (1-q^{6i})/(1-q^i)
b = [0] * (N + 1); b[0] = 1
for i in range(1, N + 1):
    if i % 6 == 0: continue
    for m in range(i, N + 1):
        b[m] += b[m - i]
# careful: parts not divisible by 6 -> 6-regular partitions count (Glaisher)
beta = [0] * (N + 1)
for m in range(-200, 201):
    v = m * (3 * m - 2)
    if 0 <= v <= N: beta[v] = (-1) ** (m % 2)
rho = lambda j: -2 if j % 3 == 1 else 1
B = lambda n: b[n] if n >= 0 else 0
bad = []
for k in range(0, kmax + 1):
    for n in range(N + 1):
        s1 = sum(rho(j) * B(n - j * (j + 1) // 2) for j in range(3 * k + 1))
        s2 = sum(rho(j) * B(n - j * (j + 1) // 2) for j in range(3 * k + 3))
        if s1 < beta[n] or (n >= (3*k+1)*(3*k+2)//2 and s1 == beta[n]): bad.append(('i', k, n, s1, beta[n]))
        if s2 > beta[n] or (n >= (3*k+2)*(3*k+3)//2 and s2 == beta[n]): bad.append(('ii', k, n, s2, beta[n]))
# sanity: full infinite identity (Theorem 1.10)
full_ok = all(sum(rho(j) * B(n - j*(j+1)//2) for j in range(0, 2*N)) == beta[n] for n in range(min(N, 400) + 1))
print('N', N, 'kmax', kmax, 'Theorem1.10 sanity', full_ok, 'violations', len(bad), bad[:10])
# classify: are all violations equality cases of (ii) with (3k+2)(3k+3)/2 <= n < (3k+3)(3k+4)/2 ?
other = [x for x in bad if not (x[0] == 'ii' and x[3] == x[4] and x[2] < (3*x[1]+3)*(3*x[1]+4)//2)]
print('violations outside the (ii) endpoint window [(3k+2)(3k+3)/2, (3k+3)(3k+4)/2):', len(other), other[:10])
