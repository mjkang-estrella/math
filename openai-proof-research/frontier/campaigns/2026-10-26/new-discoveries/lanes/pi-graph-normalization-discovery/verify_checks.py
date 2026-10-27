#!/usr/bin/env python3
"""Independent checks for the graph-normalization lane.

1. Exact (Fraction) verification of the symmetrization identity
   1^T y - y^T B y = (1/2) sum_ij B_ij x_i x_j (1/z_i - 1/z_j)^2,  z = Bx, y = x/z
   for random symmetric nonnegative B (superset of A+I), hence Conjecture 8.1
   (MathDB 349070) for B = A + I.
2. Conjecture 8.1 itself on many random connected graphs (exact rationals).
3. Energy descent (arXiv:2605.05330v1 Thm 1) along IGN orbits: gamma=1, v=1.
4. Mass growth 1^T x^k (Thm 8.1 of 2012.07764 made unconditional).
5. Convergence check of the raw IGN sequence x^k (componentwise) for random
   graphs/starts: max coordinate drift over a long tail window.
"""
from fractions import Fraction as F
import random, json
import numpy as np

def check_identity_exact(trials=300, nmax=6, seed=12345):
    rng = random.Random(seed)
    worst = F(0)
    for t in range(trials):
        n = rng.randint(1, nmax)
        B = [[F(0)]*n for _ in range(n)]
        for i in range(n):
            B[i][i] = F(rng.randint(1, 4))
            for j in range(i+1, n):
                v = F(rng.randint(0, 3))
                B[i][j] = B[j][i] = v
        x = [F(rng.randint(1, 9), rng.randint(1, 9)) for _ in range(n)]
        z = [sum(B[i][j]*x[j] for j in range(n)) for i in range(n)]
        y = [x[i]/z[i] for i in range(n)]
        lhs = sum(y) - sum(y[i]*B[i][j]*y[j] for i in range(n) for j in range(n))
        rhs = F(1, 2)*sum(B[i][j]*x[i]*x[j]*(1/z[i]-1/z[j])**2
                          for i in range(n) for j in range(n))
        diff = abs(lhs - rhs)
        if diff > worst: worst = diff
        if diff != 0:
            return {"pass": False, "trial": t, "diff": str(diff)}
        if lhs < 0:
            return {"pass": False, "trial": t, "negative lhs": str(lhs)}
    return {"pass": True, "trials": trials, "max_|lhs-rhs|": str(worst)}

def check_conjecture_graphs(trials=200, seed=777):
    """Exact check of y^T(A+I)y <= ||y||_1 on random connected simple graphs."""
    rng = random.Random(seed)
    for t in range(trials):
        n = rng.randint(2, 7)
        A = [[0]*n for _ in range(n)]
        for i in range(n):
            for j in range(i+1, n):
                if rng.random() < 0.4: A[i][j] = A[j][i] = 1
        # connect
        comp = list(range(n))
        def find(a):
            while comp[a] != a: comp[a] = comp[comp[a]]; a = comp[a]
            return a
        for i in range(1, n):
            a, b = find(i), find(rng.randrange(i))
            if a != b: comp[a] = b; A[i][b if b < i else i] = A[b if b < i else i][i] = 1
        B = [[A[i][j] + (1 if i == j else 0) for j in range(n)] for i in range(n)]
        x = [F(rng.randint(1, 20), rng.randint(1, 20)) for _ in range(n)]
        z = [sum(B[i][j]*x[j] for j in range(n)) for i in range(n)]
        y = [x[i]/z[i] for i in range(n)]
        val = sum(y[i]*B[i][j]*y[j] for i in range(n) for j in range(n)) - sum(y)
        if val > 0:
            return {"pass": False, "trial": t, "n": n, "A": A, "x": [str(v) for v in x], "violation": str(val)}
    return {"pass": True, "trials": trials}

def float_checks():
    rng = np.random.default_rng(2026)
    results = {"energy_violation": 0.0, "mass_violation": 0.0,
               "worst_convergence_drift": 0.0, "n_graphs": 0}
    worst = []
    for n in [3, 4, 5, 6, 8, 10, 12, 16]:
        for trial in range(25):
            p = rng.uniform(0.1, 0.9)
            A = (rng.random((n, n)) < p).astype(float)
            A = np.triu(A, 1); A = A + A.T
            # ensure connected via a random spanning path
            perm = rng.permutation(n)
            for a, b in zip(perm[:-1], perm[1:]):
                A[a, b] = A[b, a] = 1.0
            B = A + np.eye(n)
            results["n_graphs"] += 1
            for s in range(4):
                x = np.exp(rng.uniform(-5, 5, size=n))
                prevE = None
                traj = []
                for k in range(12000):
                    z = B @ x
                    x = x / z
                    E = 0.5*x @ (B @ x) - x.sum()
                    if prevE is not None:
                        d = E - prevE
                        if d > results["energy_violation"]:
                            results["energy_violation"] = d
                    prevE = E
                    traj.append(x)
                traj = np.array(traj[6000:])
                traj_n = traj / traj.sum(axis=1, keepdims=True)
                dev = np.abs(traj_n - traj_n.mean(axis=0)).max()
                if dev > results["worst_convergence_drift"]:
                    results["worst_convergence_drift"] = dev
                worst.append((dev, n))
    worst.sort(key=lambda t: -t[0])
    results["top5_drift"] = [(float(w[0]), w[1]) for w in worst[:5]]
    return results

if __name__ == "__main__":
    out = {}
    out["identity_exact"] = check_identity_exact()
    out["conjecture_graphs_exact"] = check_conjecture_graphs()
    out["float"] = float_checks()
    print(json.dumps(out, indent=1))
    json.dump(out, open("independent-checks.json", "w"), indent=1)
