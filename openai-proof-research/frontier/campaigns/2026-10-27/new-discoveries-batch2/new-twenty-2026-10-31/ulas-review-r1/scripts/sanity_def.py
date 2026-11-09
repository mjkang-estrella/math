"""Sanity checks of the definition and colour convention (ulas-review-r1)."""
import itertools, math
L = 200
def mulgeo(f, s):
    f = f[:]
    for n in range(s, len(f)): f[n] += f[n - s]
    return f
def C_pow(m, L):
    f = [1] + [0]*(L-1)
    for _ in range(m):
        f = mulgeo(f, 1); s = 1
        while s < L: f = mulgeo(f, s); s *= 2
    return f
C = C_pow(1, L)
# b(n): binary partitions, from prod_{i>=0} 1/(1-x^{2^i})
B = [1] + [0]*(2*L)
s = 1
while s < 2*L+1: B = mulgeo(B, s); s *= 2
print("c_1(0..10)", C[:11]); print("b(2n) 0..10", [B[2*n] for n in range(11)])
assert all(C[n] == B[2*n] for n in range(L)), "c_1(n) != b(2n)"
# functional equation (1-x)C(x) = (1+x)C(x^2)
lhs = [C[n] - (C[n-1] if n else 0) for n in range(L)]
C2 = [C[n//2] if n % 2 == 0 else 0 for n in range(L)]
rhs = [C2[n] + (C2[n-1] if n else 0) for n in range(L)]
assert lhs == rhs; print("functional equation (1-x)C(x)=(1+x)C(x^2): OK to x^%d" % (L-1))
# colour convention by direct enumeration: part 1 has 2m colours, part 2^i (i>=1) has m colours.
# number of ways to choose a multiset of size t from q colours = binom(q+t-1, t)
def colored_count(m, n):
    parts = [1]; s = 2
    while s <= n: parts.append(s); s *= 2
    tot = 0
    def rec(i, rem, ways):
        nonlocal tot
        if i == len(parts):
            if rem == 0: tot += ways
            return
        p = parts[i]; q = 2*m if p == 1 else m
        for t in range(rem//p + 1):
            rec(i+1, rem - t*p, ways * math.comb(q+t-1, t))
    rec(0, n, 1)
    return tot
bad = 0
for m in range(1, 9):
    F = C_pow(m, 40)
    for n in range(40):
        if colored_count(m, n) != F[n]: bad += 1
print("colour-convention enumeration mismatches (m<=8, n<40):", bad)
F15 = C_pow(15, 5)
print("c_15(1) =", F15[1], " c_15(4) =", F15[4], " diff =", F15[4]-F15[1], " diff/2^7 =", (F15[4]-F15[1]) / 128)
