"""Finite rational diagnostics only; not a universal-proof/novelty gate."""
from fractions import Fraction as F
from itertools import product


def run():
    counts = dict(normalized_random_tilts=0, exact_centered_scores=0,
                  one_coordinate_variance_and_logistic_difference=0,
                  graph_edge_counts=0, marked_replacement_budget=0)
    for m in range(1, 5):
        states = list(product((0, 1), repeat=m))
        for seed in (1, 2, 5):
            weights = [F(1 + ((i + 1) * seed) % 11) for i in range(len(states))]
            base = [w / sum(weights) for w in weights]
            annealed = [F(0)] * len(states)
            raw_annealed = [F(0)] * len(states)
            for signs in product((-1, 1), repeat=m):
                odds = [F(i + 3, i + 2) ** s for i, s in enumerate(signs)]
                raw = [p * __import__('functools').reduce(
                    lambda a, b: a * b, (u ** x for u, x in zip(odds, state)), F(1))
                    for p, state in zip(base, states)]
                law = [r / sum(raw) for r in raw]
                assert sum(law) == 1
                counts['normalized_random_tilts'] += 1
                for j in range(m):
                    mean = sum(p * x[j] for p, x in zip(law, states))
                    score_mean = sum(p * (x[j] - mean) for p, x in zip(law, states))
                    var = sum(p * (x[j] - mean) ** 2 for p, x in zip(law, states))
                    assert score_mean == 0 and var == mean * (1-mean) <= F(1, 4)
                    counts['exact_centered_scores'] += 1
                for i in range(len(states)):
                    annealed[i] += law[i] / 2 ** m
                    raw_annealed[i] += raw[i] / 2 ** m
            tilted_annealed = [p / sum(raw_annealed) for p in raw_annealed]
            assert annealed != tilted_annealed  # distinct references, exact finite witness
    for a in (F(1, 7), F(1, 3), F(1), F(4)):
        for u in (F(6, 5), F(3, 2), F(2), F(5)):
            pplus = a*u/(1+a*u)
            pminus = (a/u)/(1+a/u)
            assert pplus-pminus == a*(u-1/u)/((1+a*u)*(1+a/u))
            # Supremum over the fixed other-coordinate log odds is tanh(log(u)/2).
            assert 0 <= pplus-pminus <= (u-1)/(u+1)
            counts['one_coordinate_variance_and_logistic_difference'] += 1
    for n in range(1, 101):
        assert 2*n*(n+1)-2*n == 2*n*n
        assert F(2*n*n, 8) == F(n*n, 4)
        counts['graph_edge_counts'] += 1
    for j in range(1, 15):
        assert sum(F(1, 2**k) for k in range(1, j+1)) + F(1, 2**j) == 1
        counts['marked_replacement_budget'] += 1
    return dict(status='PASS', counts=counts,
                scope='Finite exact rational diagnostics only; no universal proof, fixed-disorder limit, or substantiality certification')


if __name__ == '__main__':
    import json
    print(json.dumps(run(), indent=2))
