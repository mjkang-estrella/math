# Exploration (float): Psi(A) = sum_{|J|=3} |det[1 A]_J| * f_{A^T E}(0) / (n+1), A in R^{m x 2}, n = m-3.
# f via inner eta-residues (closed form) and trapezoid in theta (xi = tan theta).
import cmath
import itertools
import math
import random
import sys


def f2(A, K=400):
    m = len(A)
    neg = [k for k in range(m) if A[k][0] < 0]
    tot = 0.0
    for s in range(K):
        th = -math.pi / 2 + math.pi * (s + 0.5) / K
        xi = math.tan(th)
        jac = 1 / math.cos(th) ** 2
        lam = [1 - 1j * a[1] * xi for a in A]
        inner = 0j
        for k in neg:
            ak = A[k][0]
            pr = 1 + 0j
            for j in range(m):
                if j != k:
                    pr *= lam[j] - A[j][0] * lam[k] / ak
            inner += (-1 / ak) / pr
        tot += (2 * math.pi * inner).real * jac
    return tot * (math.pi / K) / (4 * math.pi ** 2)


def detsum(A):
    s = 0.0
    for i, j, k in itertools.combinations(range(len(A)), 3):
        x1, y1 = A[j][0] - A[i][0], A[j][1] - A[i][1]
        x2, y2 = A[k][0] - A[i][0], A[k][1] - A[i][1]
        s += abs(x1 * y2 - x2 * y1)
    return s


def Psi(A, K=400):
    n = len(A) - 3
    return detsum(A) * f2(A, K) / (n + 1)


def search(m, seed, rounds, K):
    rng = random.Random(seed)
    A = [[rng.gauss(0, 1), rng.gauss(0, 1)] for _ in range(m)]
    best = Psi(A, K)
    step = 0.3
    for _ in range(rounds):
        B = [[x + step * rng.gauss(0, 1) for x in row] for row in A]
        if min(abs(r[0]) for r in B) < 1e-3:
            continue
        v = Psi(B, K)
        if v > best and v < 5:
            best, A = v, B
        else:
            step = max(step * 0.995, 1e-4)
    return best, A


if __name__ == "__main__":
    if sys.argv[1] == "test":
        for m in (5, 8, 11):
            T = [[-0.3, -0.2], [0.7, -0.2], [-0.3, 0.8]] + [[1e-9 * (i + 1), 0.0] for i in range(m - 3)]
            print("simplex-group m", m, Psi(T))
            a = [-1.0, 0.0, 1.0] + [0.0] * (m - 3)
            P = [[a[i] if i != 1 else 1e-9, 0.0] for i in range(m)]
        sys.exit()
    m = int(sys.argv[1])
    for s in range(int(sys.argv[2])):
        b, A = search(m, s, int(sys.argv[3]), int(sys.argv[4]))
        print(m, s, round(b, 6), "recheck K=1600", round(Psi(A, 1600), 6), flush=True)
