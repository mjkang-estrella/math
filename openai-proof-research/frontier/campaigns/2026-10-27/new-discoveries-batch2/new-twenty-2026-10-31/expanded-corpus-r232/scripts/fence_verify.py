"""Independent verifier for a single rowmotion orbit on the fence F(beta), Elizalde-Sagan convention:
covering relations x_1 < ... < x_{b1+1} > ... (beta_i = number of cover edges of segment i).
Rowmotion computed as the composition of Cameron-Fon-der-Flaass toggles along a linear extension
(toggle top-down), using explicit Python sets (no bitmasks), and checked against the definition
rho(I) = P minus upset(max I) of EPRS (which is the inverse map; orbits coincide).
Usage: fence_verify.py k t SEEDMASK   (beta = (k-1, k, ..., k, k-1), t parts)"""
import sys
k, t, seed = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
beta = [k - 1] + [k] * (t - 2) + [k - 1]
n = sum(beta) + 1
P = list(range(1, n + 1))  # elements x_1..x_n
less = set()  # cover pairs (u, v) meaning u < v
pos = 1; upward = True
for b in beta:
    for _ in range(b):
        u, v = pos, pos + 1
        less.add((u, v) if upward else (v, u))
        pos += 1
    upward = not upward
assert pos == n
lo = {x: {u for (u, v) in less if v == x} for x in P}
hi = {x: {v for (u, v) in less if u == x} for x in P}
# transitive order
def below(x):
    s, st = set(), [x]
    while st:
        y = st.pop()
        for z in lo[y]:
            if z not in s: s.add(z); st.append(z)
    return s
def above(x):
    s, st = set(), [x]
    while st:
        y = st.pop()
        for z in hi[y]:
            if z not in s: s.add(z); st.append(z)
    return s
B = {x: below(x) for x in P}; A = {x: above(x) for x in P}
def is_ideal(I):
    return all(B[x] <= I for x in I)
# linear extension: sort by height
height = {}
def h(x):
    if x not in height:
        height[x] = 0 if not lo[x] else 1 + max(h(y) for y in lo[x])
    return height[x]
lin = sorted(P, key=h)
def toggle(I, x):
    if x in I:
        if not (hi[x] & I):
            return I - {x}
        return I
    if lo[x] <= I:
        return I | {x}
    return I
def rho_toggle(I):
    for x in reversed(lin):  # top-down
        I = toggle(I, x)
    return I
def rho_eprs(I):  # P - upset(max I): EPRS definition
    mx = {x for x in I if not (hi[x] & I)}
    U = set(mx)
    for x in mx: U |= A[x]
    return set(P) - U
I0 = {i + 1 for i in range(n) if seed >> i & 1}
assert is_ideal(I0), 'seed is not an ideal'
orb = [I0]; I = rho_toggle(I0)
while I != I0:
    assert is_ideal(I)
    orb.append(I); I = rho_toggle(I)
# EPRS map must step backwards along the same cycle
for j in range(len(orb)):
    assert rho_eprs(orb[(j + 1) % len(orb)]) == orb[j]
tot = sum(len(J) for J in orb)
from fractions import Fraction
print('beta', beta, 'n', n, 'orbit length', len(orb), 'sum |I|', tot,
      'average', Fraction(tot, len(orb)), 'n/2', Fraction(n, 2), 'equal?', Fraction(tot, len(orb)) == Fraction(n, 2))
