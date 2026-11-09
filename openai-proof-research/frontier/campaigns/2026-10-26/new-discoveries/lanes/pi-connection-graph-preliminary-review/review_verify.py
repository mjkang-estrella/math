"""Independent adversarial verification of the proposed graph-case theorem.
Different construction style from parent: build simplex lists, literal L(x,y)=1 iff
x∩y!=∅ and literal D=d+d* from signed boundary; structured + random graphs; all k=1..N;
plus independent checks of each intermediate lemma."""
import numpy as np, random, itertools

rng = random.Random(20261026)

def complex_of(edges, n):
    faces = [(i,) for i in range(n)] + edges
    return faces

def literal_matrices(faces):
    nf = len(faces)
    L = np.zeros((nf, nf))
    for i, x in enumerate(faces):
        for j, y in enumerate(faces):
            L[i, j] = 1.0 if set(x) & set(y) else 0.0
    # signed boundary d(x,y)=sign if |x|=|y|+1 and y proper subset of x
    d = np.zeros((nf, nf))
    for i, x in enumerate(faces):
        for j, y in enumerate(faces):
            if len(x) == len(y) + 1 and set(y) < set(x):
                d[i, j] = 1.0 if sorted(x).index(y[0]) == 0 else -1.0  # boundary: one +1, one -1
    D = d + d.T
    return L, D

def gap_all(L, D):
    ls = np.linalg.eigvalsh(L)[::-1]
    ds = np.linalg.eigvalsh(D)[::-1]
    return np.cumsum(ls - ds), ls, ds

def phi(t): return (t + np.sqrt(t * t + 4)) / 2

def graph_cases():
    cases = []
    # structured: complete, path, star, cycle, bipartite, disjoint unions, isolates
    def edg(P): return [tuple(sorted(p)) for p in P]
    K = lambda n: edg(itertools.combinations(range(n), 2))
    P = lambda n: edg(zip(range(n - 1), range(1, n)))
    S = lambda n: edg((0, j) for j in range(1, n))
    C = lambda n: P(n) + [(n - 1, 0)]
    cases += [("K5", K(5), 5), ("P7", P(7), 7), ("S6", S(6), 6), ("C8", C(8), 8),
              ("K33", edg((i, 3 + j) for i in range(3) for j in range(3)), 6),
              ("isolates+edge", [(0, 1)], 5),
              ("2K3 disjoint", [(0, 1), (1, 2), (0, 2), (5, 6), (6, 7), (5, 7)], 8),
              ("K4+isolates", K(4), 7),
              ("P1 single vertex", [], 1),
              ("K1,5 + isolate", S(6), 8),
              ("K_n bipartite-ish K_{3,4}", edg((i, 3 + j) for i in range(3) for j in range(4)), 7)]
    for a in range(120):
        n = rng.randint(1, 12)
        p = rng.random()
        E = [(i, j) for i in range(n) for j in range(i + 1, n) if rng.random() < p]
        cases.append((f"rand{n}_{a}", E, n))
    worst = (np.inf, None)
    for name, E, n in cases:
        E = [tuple(sorted(e)) for e in E]
        assert len(set(E)) == len(E)
        faces = complex_of(E, n)
        L, D = literal_matrices(faces)
        N = len(faces)
        g, ls, ds = gap_all(L, D)
        if g.min() < worst[0]: worst = (float(g.min()), name)
        assert g.min() > np.sqrt(2) - 1 - 1e-8, (name, g.min())
        # intermediate lemmas
        v, m = n, len(E)
        # count of positive/negative eigenvalues of L == (v, m)
        assert np.sum(ls > 1e-9) == v and np.sum(ls < -1e-9) == m, (name, "count")
        # positive spectrum of L == phi(sorted eig of Q=UU^T)
        U = np.zeros((v, m))
        for z, (i, j) in enumerate(E): U[i, z] = U[j, z] = 1
        C = np.zeros((v, m))
        for z, (i, j) in enumerate(E): C[i, z] = -1.0; C[j, z] = 1.0
        if m:
            Q = U @ U.T
            qs = np.sort(np.linalg.eigvalsh(Q))[::-1]
            pos = np.sort(ls[ls > 1e-9])[::-1]
            assert np.allclose(pos, phi(qs), atol=1e-8), (name, "phi mismatch")
            # Loewner H<=2Delta: individual eigenvalues
            Delta = np.diag(U.sum(axis=1))
            H = C @ C.T
            ell = np.sort(np.linalg.eigvalsh(H))[::-1]
            dgs = np.sort(U.sum(axis=1))[::-1]
            assert np.all(ell <= 2 * dgs + 1e-9), (name, "Loewner eig fail")
            # q1>=2
            assert qs[0] >= 2 - 1e-9
        # S_k(D) formula for k<=v
        r = min(v, m)  # rank C <= min(v,m); exact rank:
        rc = np.linalg.matrix_rank(C) if m else 0
        assert np.sum(ds > 1e-9) == rc
        assert N - 2 * rc >= v - rc
        if m:
            ells = np.sqrt(np.clip(np.sort(np.linalg.eigvalsh(C @ C.T))[::-1], 0, None))  # descending
            assert np.sum(ds > 1e-9) == np.sum(ell > 1e-7)  # same positive count (pre-sqrt threshold)
            for k in range(1, v + 1):
                # zeros at positions rc+1..v can differ by O(sqrt(eps)) after sqrt; structural claim:
                assert abs(ds[:k].sum() - ells[:k].sum()) < 1e-6, (name, 'SkD formula', k)
    return worst

w = graph_cases()
print({"cases_checked": "structured+120random", "min_gap": w, "all_pass": True})
