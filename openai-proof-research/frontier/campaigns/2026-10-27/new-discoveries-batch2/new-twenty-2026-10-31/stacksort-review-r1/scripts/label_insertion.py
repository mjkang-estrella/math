"""Independent method L (no hook-length formula, no closure lemma, no block recursion).

P_n counts pairs (T, T') of decreasing binary plane trees on labels 1..n with the same
postorder word (because s(sigma) = postorder of the decreasing tree of sigma).
Build both forests simultaneously by inserting labels 1, 2, ..., n in increasing order:
label k becomes a new root whose children are t (resp. u) consecutive current roots,
t, u in {0, 1, 2}, weight 2 for a single child (left or right).  The new letter is
inserted into the common postorder word at a gap q that must be a tree boundary in
both forests.  State: left-to-right list of the gaps that are boundaries in at least
one forest, flagged 1 (first forest), 2 (second) or 3 (both).  Exponential state
space, so only small n.  Restricting both forests to labels <= k gives forests whose
postorder words are the subsequences on letters <= k, so equality of the final words
is equivalent to the simultaneous insertion process."""
import sys, json
from collections import defaultdict

MU = {0: 1, 1: 2, 2: 1}


def step(state, remaining):
    K = len(state)
    nF = sum(1 for g in state if g & 1) - 1  # trees of forest 1
    nG = sum(1 for g in state if g & 2) - 1
    for q in range(K):
        if state[q] != 3:
            continue
        Fidx = [i for i in range(q) if state[i] & 1]  # F-boundaries left of q
        Gidx = [i for i in range(q) if state[i] & 2]
        for t in (0, 1, 2):
            if t > len(Fidx):
                continue
            for u in (0, 1, 2):
                if u > len(Gidx):
                    continue
                newF = nF + 1 - t
                newG = nG + 1 - u
                if newF - 1 > remaining - 1 or newG - 1 > remaining - 1:
                    continue
                left = list(state[:q])
                # boundaries strictly between p_t and q lose their flag
                for i in Fidx[len(Fidx) - t + 1:] if t >= 1 else []:
                    left[i] &= ~1
                for i in Gidx[len(Gidx) - u + 1:] if u >= 1 else []:
                    left[i] &= ~2
                qminus = (1 if t == 0 else 0) | (2 if u == 0 else 0)
                new = [g for g in left if g] + ([qminus] if qminus else []) + [3] + list(state[q + 1:])
                yield tuple(new), MU[t] * MU[u]


def P(n):
    cur = {(3,): 1}
    for k in range(1, n + 1):
        nxt = defaultdict(int)
        rem = n - k + 1
        for st, c in cur.items():
            for st2, w in step(st, rem):
                nxt[st2] += c * w
        cur = nxt
    return cur.get((3, 3), 0), len(cur)


nmax = int(sys.argv[1])
out = {}
for n in range(1, nmax + 1):
    p, _ = P(n)
    out[n] = p
    print(n, p, flush=True)
json.dump(out, open("outputs/label_insertion_P.json", "w"), indent=1)
