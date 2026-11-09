"""Generator: all multisets of extra edges completing the path 0-1-...-(m-1) to a loopless cubic
(multi)graph with edge multiplicity <= 2 (multiplicity 3 only occurs for m = 2).
Chunking: the decision nodes at recursion depth 1 (second processed vertex) are numbered in the fixed
enumeration order by a counter incremented before filtering; chunk c of nch keeps nodes with
counter % nch == c. Depth 0 is never filtered, so the numbering is identical in every chunk and the
chunks partition the full set."""
import itertools
from collections import Counter

def completions(m, multi, chunk=0, nch=1):
    need = [2] + [1] * (m - 2) + [2]
    extra = []
    counter = [0]
    def rec(i, depth):
        while i < m and need[i] == 0: i += 1
        if i == m:
            yield list(extra); return
        k = need[i]
        cands = [j for j in range(i + 1, m) if need[j] > 0]
        gen = itertools.combinations_with_replacement(cands, k) if multi else itertools.combinations(cands, k)
        for J in gen:
            cnt = Counter(J); ok = True
            for j, t in cnt.items():
                mult = t + (1 if j == i + 1 else 0)
                if need[j] < t or mult > 2 or (not multi and mult > 1): ok = False
            if not ok: continue
            if depth == 1:
                counter[0] += 1
                if (counter[0] - 1) % nch != chunk: continue
            need[i] = 0
            for j in J: need[j] -= 1; extra.append((i, j))
            yield from rec(i + 1, depth + 1)
            for j in J: need[j] += 1; extra.pop()
            need[i] = k
    yield from rec(0, 0)
