"""Independently verify a CaDiCaL model: decode colouring, test literally for colour-1 cyclic S_a and colour-2 cyclic P_b
by brute force over all injective maps (not reusing the CNF tuples). usage: check_model.py a b n solver.log"""
import sys, itertools
a, b, n, log = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), sys.argv[4]
vals = set()
for l in open(log):
    if l.startswith('v '): vals |= {int(x) for x in l.split()[1:] if x != '0'}
pairs = list(itertools.combinations(range(n), 2))
col = {}
for i, (u, v) in enumerate(pairs):
    c = 1 if (i + 1) in vals else 0   # code 1 = colour 2
    col[(u, v)] = col[(v, u)] = c
def cyclic(phi):
    k = len(phi)
    return any(all(phi[(t + j) % k] < phi[(t + j + 1) % k] for j in range(k - 1)) for t in range(k))
def contains(k, edges, code):
    for phi in itertools.permutations(range(n), k):
        if cyclic(phi) and all(col[(phi[u], phi[v])] == code for u, v in edges): return True
    return False
if n <= 9:
  s = contains(a, [(0, i) for i in range(1, a)], 0); p = contains(b, [(i, i + 1) for i in range(b - 1)], 1)
  print(f'a={a} b={b} n={n} red_star={s} blue_path={p} VALID_WITNESS={not s and not p}')
# Second, algorithmically different check (any n): red star <=> some vertex has >= a-1 colour-1 neighbours;
# blue cyclic path <=> for some start s, the longest blue path with strictly increasing clockwise offsets from s has >= b vertices.
deg1 = max(sum(1 for v in range(n) if v != u and col[(u, v)] == 0) for u in range(n))
best = 0
for s0 in range(n):
    L = [1] * n  # L[d] = longest path starting at s0 ending at offset d
    for d in range(1, n):
        for e in range(d):
            if col[((s0 + e) % n, (s0 + d) % n)] == 1:
                L[d] = max(L[d], L[e] + 1)
    best = max(best, max(L))
print(f'DP: max_colour1_degree={deg1} (star iff >= {a-1}) longest_clockwise_blue_path={best} (path iff >= {b}) VALID_WITNESS_DP={deg1 < a-1 and best < b}')
