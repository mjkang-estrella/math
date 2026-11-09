"""Definitional cross-check (tiny n): for random 2-colourings of K_n, compare
(i) literal source definition of a cyclic embedding (exists injective phi and t with
    (phi(t),...,phi(k-1),phi(0),...,phi(t-1)) increasing, every H-edge mapped to colour j)
against
(ii) the shortcut criteria: colour-1 S_a  <=>  some vertex has colour-1 degree >= a-1;
     colour-2 P_b^mon <=> clockwise path x_1..x_b (cyclic order) in colour 2.
Also checks stars with every centre position (centre irrelevance)."""
import itertools, random, sys
def star(a, c):  # star of order a with centre c
    return [(c, v) for v in range(a) if v != c]
def path(b):
    return [(i, i + 1) for i in range(b - 1)]
def contains_def(n, col, edges, k, j):
    # literal: increasing up to cyclic permutation
    for S in itertools.combinations(range(n), k):  # increasing tuple
        for t in range(k):
            # (phi(t),...,phi(k-1),phi(0),...,phi(t-1)) = S
            phi = [None] * k
            for i in range(k):
                phi[(t + i) % k] = S[i]
            if all(col[frozenset((phi[u], phi[v]))] == j for u, v in edges):
                return True
    return False
def star_short(n, col, a):
    return any(sum(1 for w in range(n) if w != v and col[frozenset((v, w))] == 1) >= a - 1 for v in range(n))
def path_short(n, col, b):
    for s in range(n):
        order = [(s + i) % n for i in range(n)]
        best = {}
        for idx, y in enumerate(order):
            L = 1
            for x in order[:idx]:
                if col[frozenset((x, y))] == 2:
                    L = max(L, best[x] + 1)
            best[y] = L
            if L >= b:
                return True
    return False
random.seed(int(sys.argv[1]) if len(sys.argv) > 1 else 1)
bad = 0; trials = 0
for n in range(3, 8):
    pairs = [frozenset(p) for p in itertools.combinations(range(n), 2)]
    for _ in range(150):
        p1 = random.random()
        col = {e: (1 if random.random() < p1 else 2) for e in pairs}
        for a in range(3, min(n, 6) + 1):
            s = star_short(n, col, a)
            for c in range(a):
                if contains_def(n, col, star(a, c), a, 1) != s:
                    bad += 1
            trials += 1
        for b in range(3, n + 1):
            if contains_def(n, col, path(b), b, 2) != path_short(n, col, b):
                bad += 1
            trials += 1
print("defcheck trials", trials, "mismatches", bad)
