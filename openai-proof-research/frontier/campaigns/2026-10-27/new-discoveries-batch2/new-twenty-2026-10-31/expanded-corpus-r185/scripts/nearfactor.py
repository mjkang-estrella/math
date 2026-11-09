"""Pasotti-Pellegrini near 1-factor conjecture (MathDB 344926) exhaustive check for one odd v.
For every admissible multiset L of n=(v-1)/2 lengths in [1,n] (for every divisor d>1 of v: #multiples of d in L <= (v-d)/2),
search a near 1-factor of K_v (Z_v, isolated vertex fixed to 0 by rotation) with length multiset L.
Usage: nearfactor.py v chunk_index num_chunks   (lists enumerated in lexicographic order, chunk by index mod num_chunks)
"""
import sys, itertools, time
v = int(sys.argv[1]); ci = int(sys.argv[2]); nc = int(sys.argv[3])
n = (v - 1) // 2
divs = [d for d in range(3, v + 1) if v % d == 0]
full = ((1 << v) - 1) & ~1  # vertices 1..v-1 must be matched

sys.setrecursionlimit(10000)

def solve(counts):
    memo = set()
    def dfs(mask, key):
        if mask == 0: return True
        if (mask, key) in memo: return False
        x = (mask & -mask).bit_length() - 1
        for l in range(1, n + 1):
            if counts[l] == 0: continue
            for y in ((x + l) % v, (x - l) % v):
                if y and (mask >> y) & 1:
                    counts[l] -= 1
                    ok = dfs(mask & ~(1 << x) & ~(1 << y), key - (1 << (5 * l)))
                    counts[l] += 1
                    if ok: return True
        memo.add((mask, key))
        return False
    key = sum(c << (5 * l) for l, c in enumerate(counts))
    return dfs(full, key)

t0 = time.time(); checked = 0; skipped = 0; fails = []
for idx, L in enumerate(itertools.combinations_with_replacement(range(1, n + 1), n)):
    if idx % nc != ci: continue
    ok = True
    for d in divs:
        if sum(1 for x in L if x % d == 0) > (v - d) // 2: ok = False; break
    if not ok: skipped += 1; continue
    counts = [0] * (n + 1)
    for x in L: counts[x] += 1
    if len(set(L)) <= 2:  # covered by Pasotti-Pellegrini theorem (underlying set size 1 or 2); still cheap to check
        pass
    checked += 1
    if not solve(counts):
        fails.append(L); print('FAIL', v, L, flush=True)
print('v', v, 'chunk', ci, '/', nc, 'admissible_checked', checked, 'inadmissible_skipped', skipped, 'fails', len(fails), 'secs', round(time.time() - t0, 1), flush=True)
