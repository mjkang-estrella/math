# Exact dd({i};n): permutations of [n] whose double-descent set is exactly {i}.
# Double descent at p (2<=p<=n-1): w_{p-1}>w_p>w_{p+1}.
import sys, itertools, json
def dd_single(n, i):
    # A[d][s]: count of standardized prefixes of length j ending with rank s (0-based), d=1 if step j-1->j was descent
    A = [[0], [0]]; A[0] = [1]; A[1] = [0]   # length 1: no previous step; treat as 'not descent'
    for j in range(1, n):          # create step at position j (between w_j and w_{j+1})
        # new rank r in 0..j; previous last rank s in 0..j-1; ascent iff r > s, descent iff r <= s
        B = [[0]*(j+1), [0]*(j+1)]
        for d in (0, 1):
            src = A[d]
            # prefix sums
            pre = [0]*(j+1)
            for s in range(j): pre[s+1] = pre[s] + src[s]
            tot = pre[j]
            for r in range(j+1):
                asc = pre[r]          # s < r
                desc = tot - pre[r]   # s >= r
                # ascent at j
                B[0][r] += asc
                # descent at j: DD at j iff d==1 (descent at j-1) and j>=2
                isdd = (d == 1)
                if j == i:
                    if isdd: B[1][r] += desc
                else:
                    if not isdd: B[1][r] += desc
        # at j == i, a DD must occur: kill non-DD paths that passed position i
        if j == i:
            B[0] = [0]*(j+1)
            # B[1] currently includes only DD descents (from d==1) — correct
        A = B
    return sum(A[0]) + sum(A[1])
def brute(n, i):
    c = 0
    for w in itertools.permutations(range(n)):
        S = {p+1 for p in range(1, n-1) if w[p-1] > w[p] > w[p+1]}
        c += (S == {i})
    return c
if __name__ == '__main__':
    mode = sys.argv[1]
    if mode == 'check':
        for n in range(3, 9):
            for i in range(2, n):
                assert dd_single(n, i) == brute(n, i), (n, i)
        print('brute check ok n<=8; dd({2};4)=', dd_single(4, 2), 'dd({6};9)=', dd_single(9, 6))
    else:
        lo, hi = int(sys.argv[2]), int(sys.argv[3])
        out = {}
        for n in range(lo, hi+1):
            vals = {i: dd_single(n, i) for i in range(2, (n+3)//2 + 1)}
            m = -(-n // 2)
            fails = []
            for i in range(2, m):
                a, b = vals[i], vals[i+1]
                ok = (a > b) if i % 2 == 0 else (a < b)
                if not ok: fails.append(i)
            out[n] = fails
            print(n, 'fails', fails, flush=True)
