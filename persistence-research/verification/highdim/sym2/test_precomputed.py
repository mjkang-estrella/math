"""Finite equivalence tests for the search-only caches (stdlib only)."""
import sys
sys.dont_write_bytecode = True
import itertools
import json
import math
import pathlib
import random
sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
from gen_sym import Generator
from gen_precomputed import PrecomputedGenerator


def main():
    rng = random.Random(14112)
    counts = {'forbidden_comparisons': 0, 'sumkill_comparisons': 0, 'orbit_comparisons': 0}
    for coefs, K, q in (([9, 9, 18], 98, 4), ([9, 18, 54], 89, 3), ([9, 9, 9], 98, 3)):
        a = Generator(coefs, K, q, seconds=90)
        b = PrecomputedGenerator(coefs, K, q, seconds=90)
        supply = [e for es in a.byperiod.values() for e in es]
        for M in (1, 2, 3, 6, 12, 18, 42, 126, 252, 1008):
            for _ in range(12):
                r = a.key(tuple(rng.randrange(M) for _ in range(len(coefs) + 1)), M)
                aa, ww = a.sig(r, M)
                for e in rng.sample(supply, 20):
                    for T in (0, 1, rng.randrange(e[0])):
                        assert a.forbidden(T, e, aa, ww) == b.forbidden(T, e, aa, ww)
                        # A repeated call specifically exercises the cached path.
                        assert a.forbidden(T, e, aa, ww) == b.forbidden(T, e, aa, ww)
                        counts['forbidden_comparisons'] += 2
                assert a.sumkill(r, M, aa, ww) == b.sumkill(r, M, aa, ww)
                counts['sumkill_comparisons'] += 1
        for p, d, _, _, _ in supply:
            if d > 126:
                continue
            for g in (math.gcd(d, M) for M in (1, 2, 3, 6, 42)):
                for residue in range(min(g, 3)):
                    for c in (1, 9, 18, 54):
                        expected = {c * pow(10, k, p) % p for k in range(residue, d, g)}
                        assert b.contribution(p, d, g, c, residue) == expected
                        counts['orbit_comparisons'] += 1
    out = {'result': 'PASS', **counts}
    (pathlib.Path(__file__).resolve().parent / 'precompute_test_results.json').write_text(json.dumps(out, indent=1) + '\n')
    print(json.dumps(out))


if __name__ == '__main__':
    main()
