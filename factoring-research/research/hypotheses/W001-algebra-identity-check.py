"""Bounded algebra identity check, not a factoring performance experiment.

Preregistered checks: (1) C_pq(f) = C_p(f) C_q(f) mod pq for cubics;
(2) translated x^3-x has the stated factor-separation rate on seven scoped
prime pairs; (3) t=0 is a deliberately degenerate control. Reject each lemma
at its first counterexample. Factors are used only by this mathematical checker.
Run from the project with: timeout 60s python3 research/hypotheses/W001-algebra-identity-check.py
"""

import json
import math
import random
import time


def central_coefficient(index, f, modulus):
    target = index - 1
    a = [1]
    for _ in range((index - 1) // 2):
        b = [0] * min(target + 1, len(a) + 3)
        for i, v in enumerate(a):
            for j, c in enumerate(f):
                if i + j < len(b):
                    b[i + j] = (b[i + j] + v * c) % modulus
        a = b
    return a[target] if target < len(a) else 0


def shifted_cm(t):
    return [t**3 - t, 3 * t**2 - 1, 3 * t, 1]


def main():
    start = time.monotonic()
    rng = random.Random(1001)
    primes = [3, 5, 7, 11, 13, 17, 19]
    identities = 0
    for i, p in enumerate(primes):
        for q in primes[i + 1:]:
            modulus = p * q
            for _ in range(2):
                f = [rng.randrange(modulus) for _ in range(3)] + [1]
                lhs = central_coefficient(modulus, f, modulus)
                rhs = (central_coefficient(p, f, modulus)
                       * central_coefficient(q, f, modulus)) % modulus
                assert lhs == rhs, (p, q, f, lhs, rhs)
                identities += 1

    families = []
    # The first four pairs were the initial screen. The final three check the
    # stronger q > p lemma, derived after that screen; they are not a holdout.
    for p, q in [(7, 13), (7, 17), (11, 17), (11, 29),
                 (11, 13), (23, 29), (31, 37)]:
        modulus = p * q
        values = [central_coefficient(modulus, shifted_cm(t), modulus)
                  for t in range(q)]
        gcds = [math.gcd(v, modulus) for v in values]
        assert all(g in (p, modulus) for g in gcds), (p, q, gcds)
        failures = gcds.count(modulus)
        assert failures <= (p - 1) // 2, (p, q, failures)
        assert values[0] == 0, (p, q, values[0])
        families.append({"p": p, "q": q, "N": modulus,
                         "shifts_tested": q,
                         "proper_factor_gcds": gcds.count(p),
                         "gcd_equals_N": failures,
                         "failure_bound": (p - 1) // 2,
                         "t_zero_gcd": gcds[0],
                         "first_success": next({"t": t, "coefficient": v,
                                                "gcd": gcds[t]}
                                               for t, v in enumerate(values)
                                               if gcds[t] == p)})
    print(json.dumps({"seed": 1001, "identity_checks": identities,
                      "identity_failures": 0, "families": families,
                      "elapsed_seconds": time.monotonic() - start}, indent=2))


if __name__ == "__main__":
    main()
