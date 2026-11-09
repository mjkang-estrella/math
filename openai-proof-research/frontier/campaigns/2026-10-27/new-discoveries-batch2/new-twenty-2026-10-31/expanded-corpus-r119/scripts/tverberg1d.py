"""360345, d=1 clause (k(1)=1): points 1..n on a line (only order matters). Tverberg r-partition: r nonempty parts whose
intervals [min,max] share a point (max of mins <= min of maxes). Edge: partitions differing by moving one point to another part
(source Def. def-TverbergGraph). Check connectivity for n >= 2r."""
import sys
def partitions(n, r):
    # restricted growth strings of length n with exactly r blocks
    a = [0] * n
    def rec(i, m):
        if i == n:
            if m == r: yield tuple(a)
            return
        if r - m > n - i: return
        for v in range(min(m + 1, r)):
            a[i] = v; yield from rec(i + 1, max(m, v + 1))
    yield from rec(0, 0)
def tverberg(p, r):
    lo = [None] * r; hi = [None] * r
    for i, v in enumerate(p):
        if lo[v] is None: lo[v] = i
        hi[v] = i
    return max(lo) <= min(hi)
def canon(p):
    m = {}; return tuple(m.setdefault(v, len(m)) for v in p)
def run(n, r):
    V = [p for p in partitions(n, r) if tverberg(p, r)]
    S = set(V); seen = {V[0]}; st = [V[0]]
    while st:
        p = st.pop()
        for i in range(n):
            for v in range(r):
                if v == p[i]: continue
                q = list(p); q[i] = v
                if len(set(q)) < r: continue
                q = canon(q)
                if q in S and q not in seen: seen.add(q); st.append(q)
    return len(V), len(seen)
if __name__ == '__main__':
    for r in range(2, 7):
        for n in range(2 * r - 1, 2 * r + 3):
            if n > 12: break
            nv, comp = run(n, r)
            print(f'r={r} n={n} vertices={nv} reached={comp} connected={nv == comp}', flush=True)
