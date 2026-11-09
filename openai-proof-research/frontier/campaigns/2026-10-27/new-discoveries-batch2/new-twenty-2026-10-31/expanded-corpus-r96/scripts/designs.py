"""368627: is (G, B_k^x) a 2-design for a finite abelian p-group G?

B_k^x = family of k-subsets of G summing to x (Definition 2.1 of arXiv:2506.00429).
Exact integer arithmetic.  For a pair {a,b}, the number of blocks containing it is
  N(a,b) = sum_{i,j>=0} (-1)^{i+j} b[k-2-i-j][x-(i+1)a-(j+1)b]
(expand t^2 z^{a+b} prod_{g != a,b}(1+t z^g) = t^2 z^{a+b} P(t,z) / ((1+t z^a)(1+t z^b))),
where b[j][y] = number of j-subsets of G with sum y, computed by a direct DP.
Usage: designs.py t1,t2,...  p   (group Z_{p^t1} + ... ) [maxn]
"""
import sys, itertools, json, resource
resource.setrlimit(resource.RLIMIT_CPU, (115, 115))

def group(p, ts):
    mods = [p ** t for t in ts]
    els = list(itertools.product(*[range(m) for m in mods]))
    idx = {e: i for i, e in enumerate(els)}
    n = len(els)
    add = [[idx[tuple((u + v) % m for u, v, m in zip(a, b, mods))] for b in els] for a in els]
    neg = [idx[tuple((-u) % m for u, m in zip(a, mods))] for a in els]
    return els, add, neg, n

def subset_table(n, add):
    # b[j][y]
    b = [[0] * n for _ in range(n + 1)]
    b[0][0] = 1
    for g in range(n):
        for j in range(g + 1, 0, -1):
            row, prev = b[j], b[j - 1]
            ag = add[g]
            for y in range(n):
                c = prev[y]
                if c:
                    row[ag[y]] += c
    return b

def run(p, ts):
    els, add, neg, n = group(p, ts)
    b = subset_table(n, add)
    sub = lambda u, v: add[u][neg[v]]
    mul = [[0] * n for _ in range(n + 1)]  # mul[i][a] = i*a
    for a in range(n):
        acc = 0
        for i in range(n + 1):
            mul[i][a] = acc
            acc = add[acc][a]
    def N(k, x, a, c):
        s = 0
        for i in range(k - 1):
            for j in range(k - 1 - i):
                y = sub(sub(x, mul[i + 1][a]), mul[j + 1][c])
                s += (-1) ** (i + j) * b[k - 2 - i - j][y]
        return s
    pairs = [(a, c) for a in range(n) for c in range(a + 1, n)]
    designs = []
    checked = 0
    for k in range(2, n - 1):
        for x in range(n):
            if b[k][x] == 0:
                continue
            checked += 1
            # quick screen on a few pairs, then all pairs
            first = N(k, x, pairs[0][0], pairs[0][1])
            ok = True
            for (a, c) in pairs[1:]:
                if N(k, x, a, c) != first:
                    ok = False
                    break
            if ok:
                designs.append({'k': k, 'x': list(els[x]), 'lambda': first, 'blocks': b[k][x]})
    return {'p': p, 't': ts, 'n': n, 'pairs_kx_checked': checked, 'k_range': [2, n - 2], 'designs': designs}

if __name__ == '__main__':
    ts = [int(t) for t in sys.argv[1].split(',')]
    p = int(sys.argv[2])
    print(json.dumps(run(p, ts)), flush=True)
