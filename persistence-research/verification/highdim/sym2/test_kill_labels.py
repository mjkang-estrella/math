"""Verify witness-label order calculations against finite decimal cycles."""
import sys
sys.dont_write_bytecode = True
import json
import pathlib
sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import continue_sym2 as continuation


def main():
    primes = (11, 13, 17, 19, 31, 37, 41, 53, 73, 101, 127, 271)
    expected = {}
    for p in primes:
        v = 10 % p
        d = 1
        while v != 1:
            v = 10 * v % p
            d += 1
        expected[p] = d
    cases = 0
    for mode in ('exact', 'multiple', 'invalid', 'missing'):
        continuation.ORDERS = ({p: d for p, d in expected.items()} if mode == 'exact' else
                               {p: 6 * d for p, d in expected.items()} if mode == 'multiple' else
                               {p: 1 for p in primes} if mode == 'invalid' else {})
        continuation.decimal_order.cache_clear()
        for p, d in expected.items():
            assert continuation.decimal_order(p) == d
            for M in (1, 2, 3, 6, 12, 42, 126, 1008):
                assert (M % continuation.decimal_order(p) == 0) == (M % d == 0)
                cases += 1
    out = {'result': 'PASS', 'classification_cases': cases, 'untrusted_hint_modes': 4}
    (pathlib.Path(__file__).resolve().parent / 'kill_label_tests.json').write_text(json.dumps(out, indent=1) + '\n')
    print(json.dumps(out))


if __name__ == '__main__':
    main()
