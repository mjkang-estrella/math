"""Exact check of EPRS Conjecture 5.4(b) / MathDB 353231 on F̆(a^t), t odd:
order-ideal cardinality is n/2-mesic under rowmotion, n = a*t - 1.
Fence convention (EPRS arXiv:2108.12443v2): x1 < ... < x_{a} > ... ; edge j joins x_j, x_{j+1};
first a-1 edges go up, then blocks of a edges alternate down/up, the last block has a-1 edges.
Rowmotion rho(I) = downset(min(P minus I)).  Orbits are those of rowmotion (rho and its inverse
have the same orbits).  Usage: fence_rowmotion.py a t [maxideals]"""
import sys
a, t = int(sys.argv[1]), int(sys.argv[2])
cap = int(sys.argv[3]) if len(sys.argv) > 3 else 3_000_000
n = a * t - 1
lens = [a - 1] + [a] * (t - 2) + [a - 1]
up = []  # up[j] True if x_j < x_{j+1} (0-based j)
d = True
for L in lens:
    up += [d] * L
    d = not d
assert len(up) == n - 1
lower = [0] * n  # mask of lower covers
for j, u in enumerate(up):
    if u:
        lower[j + 1] |= 1 << j
    else:
        lower[j] |= 1 << (j + 1)
# downsets: along the line, downset of x extends left while edges go down-from-x direction
down = [0] * n
for x in range(n):
    m = 1 << x
    j = x - 1
    while j >= 0 and up[j]:  # x_j < x_{j+1}: going left goes down
        m |= 1 << j; j -= 1
    j = x
    while j < n - 1 and not up[j]:  # x_j > x_{j+1}: going right goes down
        m |= 1 << (j + 1); j += 1
    down[x] = m
# enumerate ideals by DFS over x_0..x_{n-1}
ideals = []
def ok(mask):
    for x in range(n):
        if mask >> x & 1 and (lower[x] & ~mask):
            return False
    return True
# incremental: decide membership left to right; constraint only between neighbours
stack = [(0, 0)]
while stack:
    i, m = stack.pop()
    if i == n:
        ideals.append(m)
        if len(ideals) > cap:
            print('CAP_EXCEEDED', a, t); sys.exit(2)
        continue
    for b in (0, 1):
        if i > 0:
            prev = m >> (i - 1) & 1
            if up[i - 1]:  # x_{i-1} < x_i : x_i in I needs x_{i-1} in I
                if b and not prev: continue
            else:          # x_{i-1} > x_i : x_{i-1} in I needs x_i in I
                if prev and not b: continue
        stack.append((i + 1, m | (b << i)))
full = (1 << n) - 1
def rho(I):
    C = full & ~I
    r = 0
    x = C
    while x:
        lb = x & -x
        k = lb.bit_length() - 1
        if not (lower[k] & ~I):
            r |= down[k]
        x ^= lb
    return r
seen = set()
orbits = 0; bad = []; sizes = {}
for I0 in ideals:
    if I0 in seen:
        continue
    orbits += 1
    tot = 0; L = 0; I = I0
    while True:
        seen.add(I); tot += 2 * bin(I).count('1') - n; L += 1
        I = rho(I)
        if I == I0:
            break
    sizes[L] = sizes.get(L, 0) + 1
    if tot != 0:
        if len(bad) < 5:
            bad.append((L, tot, I0))
print('a', a, 't', t, 'n', n, 'ideals', len(ideals), 'orbits', orbits,
      'violations', len(bad), 'first_bad(len,sum(2|I|-n),seed_mask)', bad[:5])
print('orbit sizes', sorted(sizes.items())[:40])
