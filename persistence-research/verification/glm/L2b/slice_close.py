#!/usr/bin/env python3
# slice_close.py — rigorous closure of a restricted slice (odd-C' two-term Pillai problem).
#
# Slice: solutions (L, q=q0) with L ≡ r (mod M), L ≥ Lmin, satisfying
#     10^L + K' = 2^{t0} · 3^a · 7^{w0},   K' = A·10^q0 + K,  t0 = v2(K'),  C' = K'/2^{t0}.
# On the AP, X = 10^L + K' ≡ 10^r + K' (mod 7) is constant (6 | M), so w = w0 is forced
# (w0 recorded from the sieve sig). Then
#     3^a · 7^{w0} − C' = 2^{L−t0} · 5^L     (v2 = L−t0 EXACT, v5 = L EXACT)
# Pins on a:
#   (2-pin) 3^a ≡ C'·7^{−w0} (mod 2^{L−t0})  ⟺  a ≡ a2 (mod 2^{L−t0−2})   [ord_{2^m}(3)=2^{m−2}]
#   (5-pin) 3^a ≡ C'·7^{−w0} (mod 5^L)       ⟺  a ≡ a5 (mod 4·5^{L−1})   [ord_{5^m}(3)=4·5^{m−1}]
#   (size)  a < 2.1·L + 2   since 3^a = (10^L/2^{t0} + C')/7^{w0} < 10^L·1.1.
# For L with 2^{L−t0−2} > 2.1L+2 and 4·5^{L−1} > 2.1L+2 (L ≥ ~12), a is the LEAST residue
# c(L) of the CRT pins; survival needs c(L) ≤ 2.1L+2, then the exact equation is checked.
# c2(L) (the 2-adic least residue) is non-decreasing in L and jumps by ≥ 2^j at each set
# bit j of the 2-adic log a2 — a phase-loop over the bits kills all L below an enormous
# bound; the residue tail (L beyond the computed bit length) is reported explicitly.
#
# usage: python3 -I slice_close.py A K q0 r M w0 [--json out.json] [--bits D]
import sys, json

def v2(n):
    return (n & -n).bit_length() - 1

def _plog(y, D, p):
    """p-adic log(y) mod p^D for y ≡ 1 (mod p), via Σ (−1)^{k+1} x^k/k."""
    x = (y - 1) % (p ** (D + 2))
    v0 = 0; t = x
    while t % p == 0 and t: t //= p; v0 += 1
    xodd = t
    M = p ** D
    total = 0; xok = 1; k = 1
    while True:
        kk = k; vk = 0
        while kk % p == 0: kk //= p; vk += 1
        if k * v0 - vk >= D: break
        xok = xok * xodd % M
        if k * v0 - vk < D:
            term = xok * pow(kk, -1, M) % M * pow(p, k * v0 - vk, M) % M
            total = (total + term) % M if k % 2 == 1 else (total - term) % M
        k += 1
    return total % M

def log2ad(C, D):
    """a with 3^a ≡ C mod 2^D; needs C ≡ 1,3 mod 8.  a = b0 + 2s, 9^s ≡ C·3^{−b0} (2-adic log)."""
    assert C % 8 in (1, 3), f"C mod 8 = {C%8}: 3^a ≡ C mod 8 unsolvable"
    b0 = 0 if C % 8 == 1 else 1
    mod = 1 << D
    y = C * pow(pow(3, b0, mod), -1, mod) % mod   # ≡ 1 mod 8
    Ly = _plog(y, D + 2, 2); LB = _plog(9, D + 2, 2)   # both ≡ 0 mod 8
    s = (Ly >> 3) * pow(LB >> 3, -1, 1 << (D - 1)) % (1 << (D - 2))
    a = b0 + 2 * s
    assert pow(3, a, mod) == C % mod, "log2ad self-check failed"
    return a

def log5ad(C, D):
    """a with 3^a ≡ C mod 5^D (3 is a primitive root mod 5): a = a4 + 4s, 81^s ≡ C·3^{−a4}."""
    a4 = next(a for a in range(4) if pow(3, a, 5) == C % 5)
    mod = 5 ** D
    y = C * pow(pow(3, a4, mod), -1, mod) % mod   # ≡ 1 mod 5
    Ly = _plog(y, D + 1, 5); LB = _plog(81, D + 1, 5)  # both ≡ 0 mod 5
    s = (Ly // 5) * pow(LB // 5, -1, mod) % (mod // 5)
    a = a4 + 4 * s
    assert pow(3, a, mod) == C % mod, "log5ad self-check failed"
    return a

def main():
    args = [x for x in sys.argv[1:] if not x.startswith('--')]
    A, K, q0, r, M, w0 = map(int, args[:6])
    D = 20000
    if '--bits' in sys.argv: D = int(sys.argv[sys.argv.index('--bits') + 1])
    outj = None
    if '--json' in sys.argv: outj = sys.argv[sys.argv.index('--json') + 1]

    Kp = A * 10 ** q0 + K
    t0 = v2(Kp); C = Kp >> t0
    rep = {"A": A, "K": K, "q0": q0, "r": r, "M": M, "w0": w0, "Kp": Kp, "t0": t0, "C": C}
    assert M % 6 == 0, "AP must fix X mod 7"
    Xr = (pow(10, r, 7 ** (w0 + 1)) + Kp) % 7 ** (w0 + 1)
    assert Xr % 7 ** w0 == 0 and Xr % 7 ** (w0 + 1) != 0, "w0 inconsistent with the AP"
    assert q0 + 1 > t0, "v2(10^L + K') = t0 needs L > t0"

    # solvability of 3^a ≡ C·7^{−w0} mod 8
    Cin8 = (C * pow(pow(7, w0, 8), -1, 8)) % 8
    if Cin8 not in (1, 3):
        rep.update(verdict="CLOSED", reason=f"C·7^(-w0) ≡ {Cin8} mod 8 not in <3>; no solutions at all",
                   survivors=[], checked="all L")
        print(json.dumps(rep));  rep and outj and open(outj, "w").write(json.dumps(rep)); return

    D2 = D
    inv7 = pow(pow(7, w0, 1 << (D2 + 3)), -1, 1 << (D2 + 3))
    Cin = (C * inv7) % (1 << (D2 + 3))
    D5 = D
    C5 = (C * pow(pow(7, w0, 5 ** (D5 + 1)), -1, 5 ** (D5 + 1))) % (5 ** (D5 + 1))
    a5 = log5ad(C5, D5)

    a2 = log2ad(Cin, D2)   # 2-adic integer: a ≡ a2 mod 2^{L−t0−2} ⟺ 3^a ≡ C·7^{−w0} mod 2^{L−t0}
    def c2(L):             # least residue of a2 mod 2^{L−t0−2}
        return a2 % (1 << (L - t0 - 2))

    def c5(L):
        return a5 % (4 * 5 ** (L - 1))

    survivors = []
    def try_L(L):
        """a is pinned to c2(L) (= c5(L) must agree); check the exact equation."""
        a = c2(L)
        if a > 2.1 * L + 2 or a != c5(L):
            return
        lhs = 3 ** a * 7 ** w0
        rhs = 10 ** L // 2 ** t0 + C
        if lhs == rhs and L % M == r % M and L >= max(q0 + 1, r) and L >= 2:
            survivors.append({"L": L, "a": a, "n": (10 ** L + Kp) // 9})

    # small L: brute force over the size window
    Lmin = max(q0 + 1, r, 2)
    small_end = 14
    for L in range(Lmin, small_end):
        if L % M != r % M:
            continue
        rhs = 10 ** L // 2 ** t0 + C
        a = 0; p = 1
        while p * 7 ** w0 <= rhs * 2:
            if p * 7 ** w0 == rhs:
                survivors.append({"L": L, "a": a, "n": (10 ** L + Kp) // 9})
            a += 1; p *= 3
    # large L: phase loop on the 2-adic bits
    L = max(Lmin, small_end)
    while L <= D2 + t0 + 2:
        cv = c2(L)
        if cv > 2.1 * L + 2:
            # dead at L.  c2 is non-decreasing; it stays cv until the next position where
            # a2's binary expansion differs from cv's, i.e. the next set bit of a2 at index
            # ≥ L−t0−2 that is not part of cv — equivalently c2 jumps by ≥ 2^j at the first
            # j > L−t0−2 with bit_j(a2) = 1.  Constant-phase end: p + t0 + 2.
            j = L - t0 - 2
            p = next((i for i in range(j, D2) if (a2 >> i) & 1 and i >= j), D2)
            phase_end = p + t0 + 2
            if cv > 2.1 * phase_end + 2:
                L = phase_end
                continue
            for Lp in range(max(L, int(cv / 2.1)), phase_end + 1):
                try_L(Lp)
            L = phase_end
        else:
            try_L(L)
            L += 1
    lastc = c2(D2 + t0 + 2)
    bound = lastc // 2  # any solution needs L ≥ c2(L)/2.1 ≥ lastc/2.1 (c2 non-decreasing)
    rep.update(verdict="CLOSED" if not survivors else "SOLUTIONS",
               reason=f"2/5-adic pins: a = c2(L) forced; no valid a for L < ~2^{D2} "
                      f"(verified range L < {bound}); beyond that the residual is a genuine "
                      f"two-term S-unit (Pillai/Baker) problem",
               survivors=survivors, verified_L_below=bound, bits_computed=D2)
    print(json.dumps(rep))
    if outj: open(outj, "w").write(json.dumps(rep))

if __name__ == "__main__":
    main()
