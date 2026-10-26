"""Exploratory source-faithful Kahn--Saks 1-Rayleigh search; no proof claim."""
from collections import defaultdict
from fractions import Fraction
from itertools import combinations
from math import factorial
from pathlib import Path
import json
import numpy as np

rng = np.random.default_rng(20261026)


def polynomial(n, chain, edges):
    pred = [0] * n
    for a, b in edges:
        assert a < b
        pred[b] |= 1 << a
    for b in range(n):
        for a in range(b):
            if pred[b] >> a & 1:
                pred[b] |= pred[a]
    k = len(chain)
    chain_mask = sum(1 << x for x in chain)
    zero = (0,) * k
    dp = {0: {zero: 1}}
    for size in range(n):
        nxt = {}
        for mask, terms in dp.items():
            seen = (mask & chain_mask).bit_count()
            variable = 0 if seen in [0, k] else seen
            for v in range(n):
                if mask >> v & 1 or pred[v] & ~mask:
                    continue
                target = nxt.setdefault(mask | 1 << v, defaultdict(int))
                if chain_mask >> v & 1:
                    for alpha, count in terms.items():
                        target[alpha] += count
                else:
                    for alpha, count in terms.items():
                        beta = list(alpha)
                        beta[variable] += 1
                        target[tuple(beta)] += count
        dp = nxt
    return dict(dp[(1 << n) - 1]), pred


def derivative(terms, alpha, point, exact=False):
    # N(P) has coefficient F(beta)/beta!: partial^alpha has
    # coefficient F(beta)/(beta-alpha)!. All counts are exact integers.
    result = Fraction(0) if exact else 0.0
    for beta, count in terms.items():
        if any(x < y for x, y in zip(beta, alpha)):
            continue
        value = Fraction(count) if exact else float(count)
        for x, y, t in zip(beta, alpha, point):
            value *= t ** (x - y)
            value /= factorial(x - y)
        result += value
    return result


def check(terms, alpha, point):
    k = len(alpha)
    value = derivative(terms, alpha, point)
    singles = []
    for i in range(k):
        a = list(alpha)
        a[i] += 1
        singles.append(derivative(terms, a, point))
    for i, j in combinations(range(k), 2):
        a = list(alpha)
        a[i] += 1
        a[j] += 1
        lhs = value * derivative(terms, a, point)
        rhs = singles[i] * singles[j]
        if lhs > rhs + 1e-8 * max(1, abs(lhs), abs(rhs)):
            ai, aj = list(alpha), list(alpha)
            ai[i] += 1
            aj[j] += 1
            le = derivative(terms, alpha, point, True) * derivative(terms, a, point, True)
            re = derivative(terms, ai, point, True) * derivative(terms, aj, point, True)
            if le > re:
                return {"alpha": list(alpha), "point": list(map(int, point)),
                        "i": i, "j": j, "lhs": str(le), "rhs": str(re)}
    return None


def main():
    records = []
    total = 0
    for n in range(5, 14):
        for trial in range(300):
            k = min(n - 2, int(rng.integers(3, 6)))
            chain = sorted(map(int, rng.choice(n, size=k, replace=False)))
            probability = float(rng.choice([.05, .1, .2, .35, .55]))
            edges = {(a, b) for a, b in combinations(range(n), 2) if rng.random() < probability}
            edges.update(zip(chain, chain[1:]))
            terms, pred = polynomial(n, chain, edges)
            degree = n - k
            for _ in range(25):
                alpha = [0] * k
                for j in rng.integers(0, k, size=int(rng.integers(0, degree - 1))):
                    alpha[int(j)] += 1
                point = rng.choice([0, 1, 1, 1, 2, 4, 10], size=k).tolist()
                if not any(point):
                    point[0] = 1
                hit = check(terms, alpha, point)
                if hit:
                    hit.update({"n": n, "chain": chain, "edges": sorted(map(list, edges)),
                                "predecessor_masks": pred,
                                "coefficients": [{"exponent": list(a), "count": c} for a, c in sorted(terms.items())],
                                "seed": 20261026, "status": "EXACT ARITHMETIC HIT; independent/source/novelty/formal gates pending"})
                    Path('hit.json').write_text(json.dumps(hit, indent=2) + '\n')
                    print(json.dumps(hit), flush=True)
                    return
            total += 1
        records.append({"n": n, "posets": 300, "tests_per_poset": 25})
        print(json.dumps(records[-1]), flush=True)
    Path('screen.json').write_text(json.dumps({"status": "No violation found; not a proof", "seed": 20261026,
                                              "posets": total, "records": records}, indent=2) + '\n')


if __name__ == '__main__':
    main()
