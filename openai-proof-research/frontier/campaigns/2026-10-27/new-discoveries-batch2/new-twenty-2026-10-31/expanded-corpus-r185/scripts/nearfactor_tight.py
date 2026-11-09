"""Tight-list mode for MathDB 344926: lists whose number of multiples of some divisor d of v is within s of the bound (v-d)/2.
Usage: nearfactor_tight.py v s [chunk nchunks]
"""
import sys, itertools, time, pathlib
sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
v = int(sys.argv[1]); s = int(sys.argv[2]); ci = int(sys.argv[3]) if len(sys.argv) > 3 else 0; nc = int(sys.argv[4]) if len(sys.argv) > 4 else 1
n = (v - 1) // 2
divs = [d for d in range(3, v + 1) if v % d == 0]
full = ((1 << v) - 1) & ~1
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
                    ok = dfs(mask & ~(1 << x) & ~(1 << y), key - (1 << (6 * l)))
                    counts[l] += 1
                    if ok: return True
        memo.add((mask, key))
        if len(memo) > 50000: raise OverflowError
        return False
    key = sum(c << (6 * l) for l, c in enumerate(counts))
    return dfs(full, key)
lists = set()
for d in divs:
    bound = (v - d) // 2
    mult = [x for x in range(1, n + 1) if x % d == 0]
    non = [x for x in range(1, n + 1) if x % d != 0]
    if not mult: continue
    for m in range(max(0, bound - s), min(bound, n) + 1):
        for A in itertools.combinations_with_replacement(mult, m):
            for B in itertools.combinations_with_replacement(non, n - m):
                L = tuple(sorted(A + B))
                if all(sum(1 for x in L if x % dd == 0) <= (v - dd) // 2 for dd in divs): lists.add(L)
lists = sorted(lists)
t0 = time.time(); fails = 0; checked = 0; hard = []
for i, L in enumerate(lists):
    if i % nc != ci: continue
    counts = [0] * (n + 1)
    for x in L: counts[x] += 1
    checked += 1
    if len(sys.argv) > 5: print("TRY", L, flush=True)
    try:
        r = solve(counts)
    except OverflowError:
        print('HARD', v, L, flush=True); hard.append(L); continue
    if not r: fails += 1; print('FAIL', v, L, flush=True)
    if time.time() - t0 > 90: print('TIMEOUT-STOP at index', i, flush=True); break
print('v', v, 'slack', s, 'chunk', ci, '/', nc, 'tight lists total', len(lists), 'checked', checked, 'fails', fails, 'hard', len(hard), 'secs', round(time.time() - t0, 1), flush=True)
