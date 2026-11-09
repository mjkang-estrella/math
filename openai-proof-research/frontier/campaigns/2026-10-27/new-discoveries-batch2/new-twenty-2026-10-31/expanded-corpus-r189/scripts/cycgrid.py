"""Count cyclic permutations (single n-cycle) in the sigma-class S^sigma_n of
Archer-Lauderdale arXiv:1606.04502 (Section 2.2): permutations made of k contiguous,
possibly empty segments, the i-th increasing if sigma_i = '+', decreasing if '-'.

Each permutation is generated once, via its greedy (longest-prefix) segmentation:
a value continues the current segment whenever it is monotone in that segment's
direction, otherwise it opens the next segment.  The suffix of a coverable word is
coverable by the remaining signature, so greedy is complete, and it is canonical.
Cycles are tracked incrementally (pi(pos)=v), so premature cycles are pruned.

usage: cycgrid.py SIGMA NMAX   (also --brute SIGMA N for an independent cross-check)
"""
import sys, itertools

def count(sigma, n):
    k = len(sigma)
    used = [False] * (n + 1)
    head = list(range(n + 1))  # head[t] for a tail t of a chain
    tail = list(range(n + 1))  # tail[h] for a head h of a chain
    res = 0

    def rec(pos, seg, last, length):
        nonlocal res
        if pos > n:
            res += 1
            return
        for v in range(1, n + 1):
            if used[v]:
                continue
            # segment decision (greedy)
            if length == 0:
                nseg, nlen = seg, 1
            else:
                up = v > last
                if (sigma[seg] == '+') == up:
                    nseg, nlen = seg, length + 1
                else:
                    if seg + 1 >= k:
                        continue
                    nseg, nlen = seg + 1, 1
            # cycle constraint: set pi(pos) = v ; pos is a tail, v is a head
            h = head[pos]
            if h == v and pos < n:
                continue  # would close a cycle early (pos<n means not the last assignment)
            t = tail[v]
            used[v] = True
            oh, ot = head[t], tail[h]
            head[t] = h; tail[h] = t
            rec(pos + 1, nseg, v, nlen)
            head[t] = oh; tail[h] = ot
            used[v] = False

    rec(1, 0, None, 0)
    return res

def brute(sigma, n):
    k = len(sigma)
    def in_class(p):
        seg, i = 0, 0
        while i < n:
            if seg >= k:
                return False
            j = i + 1
            while j < n and ((p[j] > p[j-1]) == (sigma[seg] == '+')):
                j += 1
            seg += 1; i = j
            if seg > k and i < n:
                return False
        return seg <= k
    def cyclic(p):
        x, c = 0, 0
        while True:
            x = p[x] - 1; c += 1
            if x == 0:
                return c == n
    return sum(1 for p in itertools.permutations(range(1, n + 1)) if in_class(p) and cyclic(p))

if __name__ == '__main__':
    if sys.argv[1] == '--brute':
        s, n = sys.argv[2], int(sys.argv[3])
        print(s, n, brute(s, n), count(s, n))
    else:
        s, nmax = sys.argv[1], int(sys.argv[2])
        print(s, [count(s, n) for n in range(1, nmax + 1)], flush=True)
