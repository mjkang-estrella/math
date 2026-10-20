"""Exact-rational control for the completeness arc colouring of T106O133 (not a proof).

For N = 2k+1, rho = 1/(2N), c(a) = floor(N*a) mod N and psi = -2c, check on the grid
(1/(2*N*M))Z/Z, which contains every arc endpoint and every point at distance exactly rho
from an antipode, that d_T(b, a+1/2) <= rho implies psi(b) - psi(a) = +-1 mod N.
"""
from fractions import Fraction as Fr
import math
import sys


def d_circle(x, y):
    t = (x - y) % 1
    return min(t, 1 - t)


def check(k, M):
    n = 2 * k + 1
    rho = Fr(1, 2 * n)
    den = 2 * n * M
    pts = [Fr(i, den) for i in range(den)]
    c = {p: math.floor(n * p) % n for p in pts}
    edges = 0
    for a in pts:
        anti = (a + Fr(1, 2)) % 1
        for b in pts:
            if d_circle(b, anti) <= rho:
                edges += 1
                diff = (-2 * c[b] + 2 * c[a]) % n
                if diff not in (1, n - 1):
                    return False, (a, b), edges
    return True, None, edges


def main():
    ok_all = True
    for k in range(1, 8):
        for M in (1, 2, 3):
            ok, bad, edges = check(k, M)
            print(f"k={k} N={2*k+1} M={M} pairs_within_rho={edges} ok={ok}" + (f" counterexample={bad}" if bad else ""))
            ok_all &= ok
    print("ALL_OK" if ok_all else "FAILED")
    return 0 if ok_all else 1


if __name__ == "__main__":
    sys.exit(main())
