# 346465: is the two-birds formula T_k divisible by smaller two-birds formulas T_j (j<k)?
# T_k fragments: A1..A_{k-1} A_k A_{k-1}..A1  and  A_k..A2 A1 A2..A_k  (variables as ints 1..k).
# f divisible by f' iff exists nonerasing morphism h (variables of f' -> nonempty words over vars of f)
# with every h(fragment of f') a factor of some fragment of f.
import itertools, sys
def T(k):
    P = list(range(1, k)); f1 = P + [k] + P[::-1]
    Q = list(range(k, 1, -1)); f2 = Q + [1] + Q[::-1]
    return [tuple(f1), tuple(f2)]
def factors(frags):
    S = set()
    for f in frags:
        for i in range(len(f)):
            for j in range(i + 1, len(f) + 1): S.add(f[i:j])
    return S
def divisible(k, j):
    F = factors(T(k)); fr = T(j)
    words = sorted({w for w in F}, key=len)
    vars_ = list(range(1, j + 1))
    # backtracking assignment in order of first appearance in fragments, prune by prefix-factor check
    order = []
    for f in fr:
        for v in f:
            if v not in order: order.append(v)
    h = {}
    def ok_partial():
        for f in fr:
            # check longest prefix and suffix fully assigned... simple: check maximal assigned runs
            run = ()
            for v in f:
                if v in h: run += h[v]
                else:
                    if run and run not in F: return False
                    run = ()
            if run and run not in F: return False
        return True
    def rec(i):
        if i == len(order): return dict(h)
        for w in words:
            h[order[i]] = w
            if ok_partial():
                r = rec(i + 1)
                if r: return r
            del h[order[i]]
        return None
    return rec(0)
for k in range(4, int(sys.argv[1]) + 1):
    for j in range(3, k):
        print(k, j, divisible(k, j), flush=True)
