"""Sign patterns of b_m in prod_{i<n} (1-q^{a+iK})(1-q^{K-a+iK}) (Ismail-Kim-Stanton, MathDB 353446).
For each residue r mod K report the set of observed signs over all m (zero coefficients reported separately).
Usage: iks_signs.py K a nmax"""
import sys
K, a, nmax = map(int, sys.argv[1:4])
def poly(n):
    p = [1]
    for i in range(n):
        for e in (a + i * K, K - a + i * K):
            q = p + [0] * e
            for j in range(len(p)):
                q[j + e] -= p[j]
            p = q
    return p
for n in range(1, nmax + 1):
    p = poly(n)
    sg = {r: set() for r in range(K)}
    for m, c in enumerate(p):
        sg[m % K].add('+' if c > 0 else '-' if c < 0 else '0')
    print('n', n, ' '.join(f'{r}:{"".join(sorted(sg[r]))}' for r in range(K)))
