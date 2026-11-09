"""335668 disposition check: characteristic polynomials (exact integer, Faddeev-LeVerrier with fractions) of
G1 = complement(K_w join 2C_3) = wK_1 ∪ K_{3,3}  and  G2 = (w-4)K_1 ∪ K_{1,9}, for w = 4..6; also confirms
complement(K_w join mC_3) is wK_1 ∪ complement(mC_3) by explicit construction."""
from fractions import Fraction


def charpoly(A):
    n = len(A)
    M = [[Fraction(0)] * n for _ in range(n)]
    coeffs = [Fraction(1)]
    I = [[Fraction(int(i == j)) for j in range(n)] for i in range(n)]
    Mk = [[Fraction(0)] * n for _ in range(n)]
    c = Fraction(1)
    cs = [Fraction(1)]
    for k in range(1, n + 1):
        # M_k = A M_{k-1} + c_{k-1} I ; c_k = -tr(A M_k)/k
        Mk = [[sum(A[i][t] * Mk[t][j] for t in range(n)) + (cs[-1] if i == j else 0) for j in range(n)] for i in range(n)]
        AM = [[sum(A[i][t] * Mk[t][j] for t in range(n)) for j in range(n)] for i in range(n)]
        c = -sum(AM[i][i] for i in range(n)) / k
        cs.append(c)
    return [int(x) for x in cs]


def graph(n, edges):
    A = [[0] * n for _ in range(n)]
    for u, v in edges:
        A[u][v] = A[v][u] = 1
    return A


def complement_join(w, m, cyc):
    n = w + m * cyc
    E = set()
    for i in range(w):
        for j in range(n):
            if j != i:
                E.add(frozenset((i, j)))
    for c in range(m):
        base = w + c * cyc
        for i in range(cyc):
            E.add(frozenset((base + i, base + (i + 1) % cyc)))
        # no edges between distinct cycles of mC_n (disjoint union)
    comp = [(u, v) for u in range(n) for v in range(u + 1, n) if frozenset((u, v)) not in E]
    return n, comp


for w in (4, 5, 6):
    n, comp = complement_join(w, 2, 3)
    G1 = graph(n, comp)
    G2 = graph(n, [(0, j) for j in range(1, 10)])
    p1, p2 = charpoly(G1), charpoly(G2)
    deg1 = sorted(sum(r) for r in G1)
    deg2 = sorted(sum(r) for r in G2)
    print('w', w, 'n', n, 'edges', len(comp), 'charpoly equal', p1 == p2, 'degree seqs', deg1, deg2)
