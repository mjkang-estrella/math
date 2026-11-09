"""Sweep fence_rowmotion logic over all (a, t), t odd >= 3, a >= 2, a + t <= LIMIT, ideal count <= CAP.
Usage: fence_sweep.py LIMIT CAP.  Re-implements the bitmask checker inline (same code as fence_rowmotion.py)."""
import sys
LIMIT, CAP = int(sys.argv[1]), int(sys.argv[2])
def check(a, t):
    n = a * t - 1
    lens = [a - 1] + [a] * (t - 2) + [a - 1]
    up = []; d = True
    for L in lens:
        up += [d] * L; d = not d
    lower = [0] * n
    for j, u in enumerate(up):
        if u: lower[j + 1] |= 1 << j
        else: lower[j] |= 1 << (j + 1)
    down = [0] * n
    for x in range(n):
        m = 1 << x; j = x - 1
        while j >= 0 and up[j]: m |= 1 << j; j -= 1
        j = x
        while j < n - 1 and not up[j]: m |= 1 << (j + 1); j += 1
        down[x] = m
    ideals = []; stack = [(0, 0)]
    while stack:
        i, m = stack.pop()
        if i == n:
            ideals.append(m)
            if len(ideals) > CAP: return None
            continue
        for b in (0, 1):
            if i > 0:
                prev = m >> (i - 1) & 1
                if up[i - 1]:
                    if b and not prev: continue
                else:
                    if prev and not b: continue
            stack.append((i + 1, m | (b << i)))
    full = (1 << n) - 1
    seen = set(); orbits = 0; bad = 0
    for I0 in ideals:
        if I0 in seen: continue
        orbits += 1; tot = 0; I = I0
        while True:
            seen.add(I); tot += 2 * bin(I).count('1') - n
            C = full & ~I; r = 0; x = C
            while x:
                lb = x & -x; k = lb.bit_length() - 1
                if not (lower[k] & ~I): r |= down[k]
                x ^= lb
            I = r
            if I == I0: break
        if tot: bad += 1
    return len(ideals), orbits, bad
for s in range(5, LIMIT + 1):
    for t in range(3, s - 1, 2):
        a = s - t
        if a < 2: continue
        r = check(a, t)
        print('a', a, 't', t, 'a+t', s, 'result(ideals, orbits, violating_orbits)', r, flush=True)
