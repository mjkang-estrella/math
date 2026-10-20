# Exploration (float): sup_b R_k(b) = D(b) / ((k+1) (sqrt P + sqrt N)^2),
# P = E (sum b_j E_j)^+, N = P - sum b, E_j iid Exp(1). R_k > 1 <=> positive first variation off the simplex curve.
import math
import random
import sys


def Ppos(b):
    s = 0.0
    for j, bj in enumerate(b):
        if bj > 0:
            pr = bj
            for l, bl in enumerate(b):
                if l != j:
                    pr *= bj / (bj - bl)
            s += pr
    return s


def Dsum(b):
    s = sorted(b)
    k = len(s)
    return sum((2 * i - k + 1) * s[i] for i in range(k))


def R(b):
    k = len(b)
    P = Ppos(b)
    N = P - sum(b)
    if P < 0 or N < 0:
        return 0.0
    return Dsum(b) / ((k + 1) * (math.sqrt(P) + math.sqrt(N)) ** 2)


def opt(k, seed, rounds=20000):
    rng = random.Random(seed)
    x = [rng.gauss(0, 1) for _ in range(k)]
    best = R(x)
    step = 0.5
    for _ in range(rounds):
        y = [xi + step * rng.gauss(0, 1) for xi in x]
        if len(set(round(v, 12) for v in y)) < k:
            continue
        v = R(y)
        if v > best:
            best, x = v, y
        else:
            step = max(step * 0.999, 1e-6)
    sc = max(x) - min(x)
    mn = min(x)
    return best, sorted((v - mn) / sc for v in x)


if __name__ == "__main__":
    for k in range(int(sys.argv[1]), int(sys.argv[2]) + 1):
        res = sorted((opt(k, s) for s in range(int(sys.argv[3]))), reverse=True)
        print(k, round(res[0][0], 9), [round(v, 4) for v in res[0][1]], flush=True)
