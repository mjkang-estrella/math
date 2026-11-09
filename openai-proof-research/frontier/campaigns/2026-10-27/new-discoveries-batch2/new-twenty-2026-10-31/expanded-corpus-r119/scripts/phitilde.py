"""353451: coefficients of tilde-phi_{r,s,n}(t) (source arXiv:2201.12442 eq. (tildephi), Thm thm:Ehrhart-relaxation-improved).
If all coefficients are positive, relaxation of a stressed hyperplane of size s adds a positive-coefficient polynomial."""
import sys
from sympy import symbols, binomial, factorial, Poly, expand, ff
t = symbols('t')
def binp(top, k):  # binomial(top, k) as polynomial in t for integer k>=0
    if k < 0: return 0
    return expand(ff(top, k) / factorial(k))
def phitilde(r, s, n):
    tot = 0
    for i in range(0, s - r + 1):
        inner = 0
        for l in range(0, s):
            inner += factorial(n - 2 - l) * factorial(l) * binp(s - 2 - l - i + t * (s - r - i + 1), s - 1 - l) * binp(s - 1 - i + t * (s - r - i), l)
        tot += (-1) ** i * binomial(s, i) * inner
    return Poly(expand(tot), t)
if __name__ == '__main__':
    N = int(sys.argv[1]); bad = []; cnt = 0
    for n in range(3, N + 1):
        for r in range(1, n):
            for s in range(r, n):
                c = phitilde(r, s, n).all_coeffs(); cnt += 1
                if any(x < 0 for x in c): bad.append((r, s, n, [int(x) for x in c])); print('NEG', r, s, n, c, flush=True)
    print('checked', cnt, 'triples n<=', N, 'negative:', len(bad))
