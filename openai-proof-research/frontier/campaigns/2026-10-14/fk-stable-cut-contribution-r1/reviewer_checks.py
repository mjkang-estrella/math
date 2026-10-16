# Reviewer-side exact finite checks for the G contribution audit.
# Myeongjin Kang campaign; reviewer code, MIT. Finite support only, not a proof.
# Independent of the candidate's checks.py (not read, not executed).
import json
import random
from fractions import Fraction as Fr
from itertools import product


def solve(A, b):
    n = len(A)
    M = [row[:] + [b[i]] for i, row in enumerate(A)]
    for c in range(n):
        p = next(r for r in range(c, n) if M[r][c] != 0)
        M[c], M[p] = M[p], M[c]
        piv = M[c][c]
        M[c] = [x / piv for x in M[c]]
        for r in range(n):
            if r != c and M[r][c] != 0:
                f = M[r][c]
                M[r] = [x - f * y for x, y in zip(M[r], M[c])]
    return [M[i][n] for i in range(n)]


def green_apply(V, edges, m, f):
    """K f for K = (-L)^{-1} on m-mean-zero functions, L f(v) = m(v)^-1 sum c (f(w)-f(v))."""
    # Solve Lap g = m f with g(0) = 0, then center in m.
    rhs = [m[v] * f[v] for v in range(V)]
    A = [[Fr(0)] * V for _ in range(V)]
    for (u, w, r) in edges:
        c = 1 / r
        A[u][u] += c
        A[w][w] += c
        A[u][w] -= c
        A[w][u] -= c
    sub = [row[1:] for row in A[1:]]
    g = [Fr(0)] + solve(sub, rhs[1:])
    M = sum(m)
    mean = sum(mv * gv for mv, gv in zip(m, g)) / M
    return [gv - mean for gv in g]


def far_side(V, edges, idx):
    u, w, _ = edges[idx]
    adj = {v: [] for v in range(V)}
    for j, (a, b, _) in enumerate(edges):
        if j != idx:
            adj[a].append(b)
            adj[b].append(a)
    seen, stack = {w}, [w]
    while stack:
        x = stack.pop()
        for y in adj[x]:
            if y not in seen:
                seen.add(y)
                stack.append(y)
    assert u not in seen
    return seen


def check_tree_linearity(trials=40, seed=7, wrong_mass=False):
    rng = random.Random(seed)
    for _ in range(trials):
        V = rng.randint(2, 8)
        edges = []
        for v in range(1, V):
            edges.append((rng.randrange(v), v, Fr(rng.randint(1, 30), rng.randint(1, 7))))
        # masses: original degree plus arbitrary extra loop darts (even), any positive integers
        deg = [0] * V
        for (a, b, _) in edges:
            deg[a] += 1
            deg[b] += 1
        m = [Fr(deg[v] + 2 * rng.randint(0, 2)) for v in range(V)]
        M = sum(m)
        us = []
        for i, (_, _, r) in enumerate(edges):
            A = far_side(V, edges, i)
            s = sum(m[v] for v in A) / M
            if wrong_mass:  # control: far-side fraction by vertex count instead of mass
                s = Fr(len(A), V)
            us.append((r, [(1 if v in A else 0) - s for v in range(V)]))
        for _ in range(3):
            f = [Fr(rng.randint(-9, 9)) for _ in range(V)]
            mu = sum(mv * fv for mv, fv in zip(m, f)) / M
            f = [fv - mu for fv in f]
            lhs = green_apply(V, edges, m, f)
            rhs = [Fr(0)] * V
            for r, u in us:
                ip = sum(mv * uv * fv for mv, uv, fv in zip(m, u, f))
                rhs = [x + r * ip * uv for x, uv in zip(rhs, u)]
            if lhs != rhs:
                return False
    return True


# --- selected-child identity (3.5), brute force over plane trees -------------
P = {0: Fr(5, 8), 2: Fr(1, 4), 4: Fr(1, 8)}  # critical: 2/4+4/8 = 1


def trees(n):
    """All plane trees with n nodes, offspring in {0,2,4}, as nested tuples."""
    if n == 1:
        return [()]
    out = []
    for k in (2, 4):
        for sizes in compositions(n - 1, k):
            for kids in product(*[trees(s) for s in sizes]):
                out.append(tuple(kids))
    return out


_comp = {}


def compositions(total, parts):
    key = (total, parts)
    if key not in _comp:
        if parts == 1:
            _comp[key] = [(total,)] if total >= 1 and total % 2 == 1 else []
        else:
            res = []
            for first in range(1, total):
                for rest in compositions(total - first, parts - 1):
                    res.append((first,) + rest)
            _comp[key] = res
    return _comp[key]


def size(t):
    return 1 + sum(size(c) for c in t)


def weight(t):
    w = P[len(t)]
    for c in t:
        w *= weight(c)
    return w


def toll(t, g, F):
    tot = g(len(t)) * sum(F(size(c)) for c in t) if t else 0
    return tot + sum(toll(c, g, F) for c in t)


def walk_law(j):
    # a_j(z) = P(sum_{i<=j}(xi_i - 1) = z)
    dist = {0: Fr(1)}
    for _ in range(j):
        nd = {}
        for z, p in dist.items():
            for k, q in P.items():
                nd[z + k - 1] = nd.get(z + k - 1, Fr(0)) + p * q
        dist = nd
    return dist


def check_selected_child(Nmax=11, shift=0):
    g = lambda k: k * k + 1
    F = lambda s: s * s + 3 * s
    laws = {j: walk_law(j) for j in range(Nmax + 1)}
    a = lambda j, z: laws[j].get(z, Fr(0))
    results = {}
    for N in range(3, Nmax + 1, 2):
        ts = trees(N)
        Z = sum(weight(t) for t in ts)
        lhs = sum(weight(t) * toll(t, g, F) for t in ts) / Z
        rhs = Fr(0)
        for s in range(1, N):
            pi_s = a(s, -1) / s
            inner = sum(k * pk * g(k) * a(N - 1 - s, 1 - k - shift) for k, pk in P.items() if k >= 1)
            rhs += F(s) * pi_s * inner
        rhs *= Fr(N) / a(N, -1)
        assert Z == a(N, -1) / N
        results[N] = (lhs == rhs, len(ts))
    return results


def check_nested_example():
    sI, sJ, inter = Fr(3, 4), Fr(1, 2), Fr(1, 2)
    rI, rJ = Fr(16, 3), Fr(4)
    nI, nJ = sI * (1 - sI), sJ * (1 - sJ)
    ip = inter - sI * sJ
    # operator rI vI(x)vI + rJ vJ(x)vJ restricted to span{vI,vJ}: matrix in that basis
    G = [[nI, ip], [ip, nJ]]
    D = [[rI, 0], [0, rJ]]
    Mx = [[sum(D[i][k] * G[k][j] for k in range(2)) for j in range(2)] for i in range(2)]
    tr = Mx[0][0] + Mx[1][1]
    det = Mx[0][0] * Mx[1][1] - Mx[0][1] * Mx[1][0]
    return {"weights": [str(rI * nI), str(rJ * nJ)], "trace": str(tr), "det": str(det),
            "normalized_ip_sq": str(ip * ip / (nI * nJ))}


def check_interval_coarea(Nmax=9, drop_self=False):
    """Exact (4.4): sum_w b_w phi(I_w) = int dt sum_{w anc-or-self of v(t)} b_w phi(I_w)/s_w."""
    phi = lambda a, b: (a + 2 * b) ** 2 + Fr(1, 3) * a + 1
    count, ok = 0, True
    for N in range(3, Nmax + 1, 2):
        for t in trees(N):
            M = N - 1
            cells = []  # (interval start, end, ancestors-or-self list) per nonroot node, preorder

            def walk(node, anc):
                for c in node:
                    idx = len(cells)
                    cells.append([idx, None, anc + [idx]])
                    walk(c, anc + [idx])
                    cells[idx][1] = len(cells)
            walk(t, [])
            assert len(cells) == M
            b = [(i * 7 + 3) % 3 != 0 for i in range(M)]
            I = [(Fr(c[0], M), Fr(c[1], M)) for c in cells]
            lhs = sum(phi(*I[w]) for w in range(M) if b[w])
            rhs = Fr(0)
            for j in range(M):
                chain = cells[j][2][:-1] if drop_self else cells[j][2]
                rhs += Fr(1, M) * sum(phi(*I[w]) / (I[w][1] - I[w][0]) for w in chain if b[w])
            ok &= (lhs == rhs)
            count += 1
    return ok, count


if __name__ == "__main__":
    out = {
        "preorder_interval_coarea_4_4": check_interval_coarea(),
        "control_drop_self_term_rejected": not check_interval_coarea(Nmax=7, drop_self=True)[0],
        "tree_green_operator_equals_sum_of_cut_rank_ones": check_tree_linearity(),
        "selected_child_identity_3_5": {str(k): v for k, v in check_selected_child().items()},
        "nested_cut_example": check_nested_example(),
        "control_vertex_count_mass_rejected": not check_tree_linearity(wrong_mass=True),
        "control_wrong_lattice_site_rejected": not all(
            v[0] for v in check_selected_child(Nmax=9, shift=2).values()),
        "scope": "finite exact support only; not a proof of any limit or contribution verdict",
    }
    print(json.dumps(out, sort_keys=True))
