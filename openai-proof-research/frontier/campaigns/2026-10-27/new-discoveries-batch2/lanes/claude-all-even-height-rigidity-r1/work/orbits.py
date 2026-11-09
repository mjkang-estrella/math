"""Structured 3-D analogue of the cyclotomic family: orbits of finite point
groups G < O(3) (T_d, T_h, O_h, I_h, dihedral D_n, D_nd, D_nh, C_nv, S_2n)
of special base points, single orbits and unions of two orbits (two radii).
Float mode (exploration only; any zero must be re-verified exactly).
Reports minimal number of odd line directions found per family."""
import sys, os, json, itertools, math
import numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from lp import odd_directions

phi = (1 + 5 ** 0.5) / 2


def closure(gens):
    G = [np.eye(3)]
    keys = {tuple(np.round(np.eye(3), 6).ravel())}
    frontier = [np.eye(3)]
    while frontier:
        nf = []
        for A in frontier:
            for g in gens:
                B = g @ A
                k = tuple(np.round(B, 6).ravel())
                if k not in keys:
                    keys.add(k); G.append(B); nf.append(B)
        frontier = nf
        if len(G) > 200:
            break
    return G


def rotz(t):
    c, s = math.cos(t), math.sin(t)
    return np.array([[c, -s, 0], [s, c, 0], [0, 0, 1]])


P = np.array([[0, 1, 0], [0, 0, 1], [1, 0, 0]], float)
signs = [np.diag(s) for s in itertools.product([1, -1], repeat=3)]
perm = [np.eye(3)[list(p)] for p in itertools.permutations(range(3))]
Rx = np.diag([1, -1, -1]).astype(float)
Mz = np.diag([1, 1, -1]).astype(float)
My = np.diag([1, -1, 1]).astype(float)
five = 0.5 * np.array([[1, -phi, 1 / phi], [phi, 1 / phi, -1], [1 / phi, 1, phi]])
groups = {
    'Td': closure(perm + [np.diag([-1, -1, 1.])]),
    'Th': closure([P] + signs),
    'Oh': closure(perm + signs),
    'O': closure([P, np.array([[0, -1, 0], [1, 0, 0], [0, 0, 1.]])]),
    'I': closure([P, np.diag([-1, -1, 1.]), five]),
    'Ih': closure([P, np.diag([-1, -1, 1.]), five, -np.eye(3)]),
}
for n in (3, 5, 7, 9):
    groups[f'D{n}'] = closure([rotz(2 * math.pi / n), Rx])
    groups[f'D{n}d'] = closure([rotz(2 * math.pi / n), Rx, My])
    groups[f'C{n}v'] = closure([rotz(2 * math.pi / n), My])
    groups[f'S{2*n}'] = closure([rotz(math.pi / n) @ Mz])
    groups[f'D{n}h'] = closure([rotz(2 * math.pi / n), Rx, Mz])
bases = [(1, 0, 0), (0, 0, 1), (1, 1, 0), (1, 1, 1), (phi, 1, 0), (1, 0, 0.5), (1, 0.3, 0),
         (1, 0, 0.7), (0.8, 0.6, 0.4), (1, 2, 0), (2, 1, 0.5), (0, 1, phi), (1, 0.5, 0.25)]


def orb(G, x):
    pts = {}
    for g in G:
        y = g @ np.array(x, float)
        pts[tuple(np.round(y, 9))] = tuple(y)
    return list(pts.values())


def score(S):
    S = [tuple(p) for p in S]
    if len(S) % 2 or len(S) < 4:
        return None
    if np.linalg.matrix_rank(np.array(S) - np.array(S[0]), tol=1e-7) < 3:
        return None
    return len(odd_directions(S, exact=False, digits=6))


out = {}
for gn, G in groups.items():
    best = None
    orbs = [orb(G, b) for b in bases]
    cands = [(f'{bi}', o) for bi, o in enumerate(orbs)]
    for (i, oi), (j, oj) in itertools.combinations(list(enumerate(orbs)), 2):
        for r in (1.0, 0.5, 2.0):
            U = {tuple(np.round(p, 9)): p for p in oi}
            for p in oj:
                q = tuple(r * np.array(p))
                U[tuple(np.round(q, 9))] = q
            cands.append((f'{i}+{r}*{j}', list(U.values())))
    for name, S in cands:
        if len(S) > 130:
            continue
        sc = score(S)
        if sc is not None and (best is None or sc < best[0]):
            best = (sc, name, len(S))
    out[gn] = {'order': len(G), 'best_odd_dirs_name_size': best}
print(json.dumps(out))
