#!/usr/bin/env python3
"""pi-wgm-parity-review: independent check, method deliberately different from the
parent's unordered-config enumeration and from the Lean proof.

Theory used (derived independently in review.md):
A config (child : n x 2 slots -> terminals m or internals n, root = internal 0) is
SOUND (Definition 3.1 semantics: forall x,t >= 0, inequality <=> exists z >= 0,
z_root = t, all constraints) iff
  (a) every terminal is reachable from root via child edges, AND
  (b) the exact-rational flow system is feasible:
        exists q >= 0 (q_i for constraint i, i in 0..n-1):
          for each terminal j:  sum_{i,b: child(i,b)=j} q_i = s_j
          for each internal j: 2*q_j - sum_{i,b: child(i,b)=m+j} q_i = S*delta_{j,root}
(a) from the 0/1 assignment argument; (b) from Farkas' lemma applied to the
finite-log reading (x_j > 0, t > 0). Soundness of Definition 3.1 implies both;
conversely (a)+(b) give a soundness certificate, so the test is exact both ways.
"""
from itertools import product, combinations as _c
import itertools
from fractions import Fraction as Q
import random, json

# ---------- exact feasibility by column-subset enumeration ----------
def _solve_exact(rows, rhs):
    """Exact Gaussian elimination on a (rows x size) system; return unique solution
    if columns independent and system consistent, else None."""
    nr = len(rows)
    k = len(rows[0])
    M = [[Q(v) for v in rows[i]] + [Q(rhs[i])] for i in range(nr)]
    pivots = []
    r = 0
    for c in range(k):
        p = next((i for i in range(r, nr) if M[i][c] != 0), None)
        if p is None:
            continue
        M[r], M[p] = M[p], M[r]
        v = M[r][c]
        M[r] = [x / v for x in M[r]]
        for i in range(nr):
            if i != r and M[i][c] != 0:
                f = M[i][c]
                M[i] = [x - f * y for x, y in zip(M[i], M[r])]
        pivots.append(c)
        r += 1
    if len(pivots) < k:
        return None  # columns dependent
    # consistency: any row with all-zero coeffs but nonzero rhs?
    for i in range(nr):
        if all(M[i][j] == 0 for j in range(k)) and M[i][k] != 0:
            return None
    sol = [Q(0)] * k
    for idx, c in enumerate(pivots):
        sol[c] = M[idx][k]
    return sol

def exact_feasible(A, b):
    """Is there q >= 0 with A q = b?  Exact rational.
    A minimal-support nonneg solution has linearly independent support columns,
    so enumerating independent column subsets of size <= rank suffices."""
    m_, n_ = len(A), len(A[0])
    cols = list(range(n_))
    for size in range(0, min(m_, n_) + 1):
        for sub in _c(cols, size):
            if size == 0:
                if all(Q(x) == 0 for x in b):
                    return True
                continue
            rowsA = [[A[i][j] for j in sub] for i in range(m_)]
            sol = _solve_exact(rowsA, b)
            if sol is None:
                continue
            if all(x >= 0 for x in sol):
                return True
    return False

# ---------- config machinery ----------
def reachable_all(child, m, n, root=0):
    seen, todo = {m + root}, [m + root]
    while todo:
        v = todo.pop()
        if v >= m:
            for c in child[v - m]:
                if c not in seen:
                    seen.add(c); todo.append(c)
    return all(j in seen for j in range(m))

def flow_feasible(child, m, n, s, root=0):
    S = sum(s)
    cols = n
    rows, b = [], []
    # terminal equations
    for j in range(m):
        row = [0] * cols
        for i in range(n):
            for bb in (0, 1):
                if child[i][bb] == j:
                    row[i] += 1
        rows.append(row); b.append(s[j])
    # internal equations
    for j in range(n):
        row = [0] * cols
        row[j] += 2
        for i in range(n):
            for bb in (0, 1):
                if child[i][bb] == m + j:
                    row[i] -= 1
        rows.append(row); b.append(S if j == root else 0)
    return exact_feasible(rows, b)

def sound(child, m, n, s):
    if not reachable_all(child, m, n):
        return False
    # pre-filter: every terminal needs an incoming slot (s_j > 0)
    targets = {c for pair in child for c in pair}
    if any(j not in targets for j in range(m)):
        return False
    return flow_feasible(child, m, n, s)

# ---------- randomized cross-check of the Farkas characterization ----------
def find_violation(child, m, n, s, iters=40000, seed=1):
    """Search for x >= 0, t >= 0, z >= 0, z_root = t, constraints hold, t^S > prod x^s."""
    rng = random.Random(seed)
    S = sum(s)
    best = None
    for _ in range(iters):
        x = [rng.random() ** 2 * 10 for _ in range(m)]
        z = [rng.random() ** 2 * 10 for _ in range(n)]
        t = z[0]  # root = internal 0
        ok = True
        for i in range(n):
            a, b_ = child[i]
            lhs = (x[a] if a < m else z[a - m]) * (x[b_] if b_ < m else z[b_ - m])
            if lhs + 1e-12 < z[i] * z[i]:
                ok = False; break
        if not ok:
            continue
        prod = 1.0
        for j in range(m):
            prod *= x[j] ** s[j]
        val = t ** S - prod
        if best is None or val > best[0]:
            best = (val, x, z)
    return best

def main():
    report = {}
    random.seed(0)
    for m in (2, 3, 4):
        for n_rel, label in ((-1, "n=m-1"), (-2, "n=m-2"), (0, "n=m")):
            n = m + n_rel
            if n < 1:
                continue
            V = m + n
            slots = list(range(V))
            # weight vectors: one odd-S, one even-S (positive)
            if m == 2: svecs = [(1, 2), (1, 1)]
            elif m == 3: svecs = [(1, 1, 1), (1, 2, 1)]
            else: svecs = [(1, 1, 1, 2), (1, 1, 2, 2)]
            counts = {}
            sound_examples = {}
            for s in svecs:
                cnt = 0; ex = None
                for child in product(product(slots, repeat=2), repeat=n):
                    if sound(child, m, n, s):
                        cnt += 1
                        if ex is None: ex = child
                counts[s] = cnt; sound_examples[s] = ex
            report[f"m{m}_{label}"] = {"counts": {str(k): v for k, v in counts.items()},
                                       "examples": {str(k): v for k, v in sound_examples.items()}}
            print(f"m={m} {label}: " + "; ".join(f"s={s} S={sum(s)} sound_configs={counts[s]}" for s in svecs))
    # cross-check: sound configs admit no violation; a sample of unsound ones do not necessarily...
    # we check: for n=m-1 configs declared sound, random search finds no violation (must hold).
    m, n = 3, 2
    s = (1, 2, 1)
    V = m + n
    tested_sound = 0
    for child in product(product(range(V), repeat=2), repeat=n):
        if sound(child, m, n, s):
            tested_sound += 1
            v = find_violation(child, m, n, s, iters=8000, seed=tested_sound)
            assert v is None or v[0] <= 1e-9, f"VIOLATION found for sound config {child}: {v[0]}"
    print(f"cross-check: {tested_sound} sound configs (m=3,n=2,s=(1,2,1)) survived random violation search")
    # and: for configs declared UNSOUND by flow-infeasibility but reach-all, find an explicit violation
    found = 0
    for child in product(product(range(V), repeat=2), repeat=n):
        if reachable_all(child, m, n) and not flow_feasible(child, m, n, s):
            v = find_violation(child, m, n, s, iters=200000, seed=777)
            if v and v[0] > 1e-9:
                found += 1
            if found >= 5:
                break
    print(f"cross-check: found explicit violations for {found} flow-infeasible reach-all configs")
    with open(__file__.replace(".py", "_out.json"), "w") as f:
        json.dump(report, f, indent=1, default=str)

if __name__ == "__main__":
    main()
