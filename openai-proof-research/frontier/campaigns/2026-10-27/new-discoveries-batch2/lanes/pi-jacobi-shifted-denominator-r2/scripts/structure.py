"""Structure extraction: exact ImB_{2m+1}, factorization attempts, top layers,
normal form mod 2^(3m+1), and the s = u+v collapse."""
import sys
from math import comb, factorial
from fractions import Fraction
from core import (compute_AB, p_im, p_re, p_min_vp, p_degree, swap_uv, padd, pmul,
                  vp, gi_mul, gi_add)

def poly_str(p):
    # p: dict {(a,b): int} (imaginary parts)
    return " + ".join(f"{z}*u^{a}*v^{b}" for (a, b), z in sorted(p.items()))

def main(N):
    A, B = compute_AB(N)
    for m in range(0, (N - 1) // 2 + 1):
        n = 2 * m + 1
        im = p_im(B[n])
        print(f"=== m={m} (n={n}), min_v2={p_min_vp(im)}, deg={p_degree(im)}")
        # normalized by 2^(3m)
        norm = {k: z >> (3 * m) if z % (1 << (3 * m)) == 0 else None for k, z in im.items()}
        if any(v is None for v in norm.values()):
            print("  NOT divisible by 2^3m !")
        print("  ImB/2^3m:", {k: v for k, v in sorted(norm.items())})
        # check normal form: ImB - 2^3m[(u+v)^(m+1) + delta(u+v)^m] divisible by 2^(3m+1)?
        # build (u+v)^k with integer coeffs
        def spow(k):
            r = {(0, 0): 1}
            for _ in range(k):
                r = {ka + kb: va + vb for (ka, ka2), va in list({(a, 0): v for (a, b), v in [(k2, v2) for k2, v2 in r.items()]}[0].items()) for (kb, kb2), vb in [{(1, 0): 0}]}  # placeholder
            return r
        # simpler: (u+v)^k
        def spow2(k):
            r = {(0, 0): 1}
            for _ in range(k):
                nr = {}
                for (a, b), z in r.items():
                    nr[(a + 1, b)] = nr.get((a + 1, b), 0) + z
                    nr[(a, b + 1)] = nr.get((a, b + 1), 0) + z
                r = nr
            return r
        target = {(a, b): z for (a, b), z in spow2(m + 1).items()}
        if m % 4 == 1:
            for (a, b), z in spow2(m).items():
                target[(a, b)] = target.get((a, b), 0) + z
        # ImB - 2^3m * target  divisible by 2^(3m+1)?
        diff = dict(im)
        for (a, b), z in target.items():
            diff[(a, b)] = diff.get((a, b), 0) - (1 << (3 * m)) * z
        diff = {k: v for k, v in diff.items() if v}
        nf_ok = all(v % (1 << (3 * m + 1)) == 0 for v in diff.values())
        print(f"  mod2 unit law (m={m}): {nf_ok}", "" if nf_ok else f"  diff={diff}")

if __name__ == "__main__":
    main(int(sys.argv[1]) if len(sys.argv) > 1 else 10)
