"""Operation counts for kernel-evaluation estimates (no big numbers computed here except
label-insertion state counts).  (1) top-max recursion with range pruning for target N:
number of big-integer multiplications in the naive 4-fold loop.  (2) elementary
root-split recursion from n0 to a.  (3) label-insertion automaton: states and
transitions per level for target n (reuses the reviewer's own automaton logic)."""
import sys
from collections import defaultdict


def topmax_mults(N):
    B = lambda M: min(M, N + 1 - M)
    tot = 0
    for M in range(1, N + 1):
        Bm = B(M)
        tot += 9 * Bm * Bm  # KI
        for m2 in range(1, M):
            Ma = M - m2
            for r in range(1, Bm + 1):
                for r2 in range(1, min(r - 1, m2, B(m2)) + 1):
                    if r - r2 > min(Ma, B(Ma)):
                        continue
                    # s, s2 loops of the same shape
                    for s in range(1, Bm + 1):
                        tot += max(0, min(s - 1, m2, B(m2)) - max(1, s - min(Ma, B(Ma))) + 1)
            tot += 2 * Bm * Bm  # binomial scalings
    return tot


def elem_mults(n0, a):
    return sum(2 * (n - 2) + 1 for n in range(n0 + 1, a + 1))


MU = {0: 1, 1: 2, 2: 1}


def step(state, remaining):
    K = len(state)
    nF = sum(1 for g in state if g & 1) - 1
    nG = sum(1 for g in state if g & 2) - 1
    for q in range(K):
        if state[q] != 3:
            continue
        Fidx = [i for i in range(q) if state[i] & 1]
        Gidx = [i for i in range(q) if state[i] & 2]
        for t in (0, 1, 2):
            if t > len(Fidx):
                continue
            for u in (0, 1, 2):
                if u > len(Gidx):
                    continue
                if nF - t > remaining - 1 or nG - u > remaining - 1:
                    continue
                left = list(state[:q])
                for i in (Fidx[len(Fidx) - t + 1:] if t >= 1 else []):
                    left[i] &= ~1
                for i in (Gidx[len(Gidx) - u + 1:] if u >= 1 else []):
                    left[i] &= ~2
                qm = (1 if t == 0 else 0) | (2 if u == 0 else 0)
                yield tuple([g for g in left if g] + ([qm] if qm else []) + [3] + list(state[q + 1:])), MU[t] * MU[u]


def li_counts(n):
    cur = {(3,): 1}
    S = T = 0
    for k in range(1, n + 1):
        nxt = defaultdict(int)
        for st, c in cur.items():
            for st2, w in step(st, n - k + 1):
                nxt[st2] += c * w
                T += 1
        S += len(nxt)
        cur = nxt
    return S, T, cur.get((3, 3))


for N in (16, 20, 50, 78, 82):
    print("topmax naive mults N=%d: %d" % (N, topmax_mults(N)), flush=True)
for (n0, a) in ((16, 230), (20, 130), (16, 400)):
    print("elementary recursion mults %d->%d: %d" % (n0, a, elem_mults(n0, a)))
for n in (12, 14, 16):
    S, T, p = li_counts(n)
    print("label-insertion n=%d: total states %d, transitions %d, P=%d" % (n, S, T, p), flush=True)
