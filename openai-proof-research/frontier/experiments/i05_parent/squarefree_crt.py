"""Exact local-survival diagnostic, not an asymptotic/PD verification."""
from fractions import Fraction
from math import gcd, lcm
from pathlib import Path
import json

primes = (2, 3, 5)
cases = forced_zero = 0
for modulus in range(1, 25):
    extended = lcm(modulus, *(q*q for q in primes))
    for b in range(modulus):
        if gcd(b, modulus) != 1:
            continue
        lifts = [a for a in range(b, extended, modulus) if gcd(a, extended) == 1]
        observed = Fraction(sum(all((a-1) % (q*q) for q in primes) for a in lifts), len(lifts))
        predicted = Fraction(1)
        for q in primes:
            e, t = 0, modulus
            while t % q == 0:
                t //= q
                e += 1
            if e == 0:
                rho = Fraction(1, q*(q-1))
            elif e == 1:
                rho = Fraction(1, q) if (b-1) % q == 0 else Fraction(0)
            else:
                rho = Fraction(int((b-1) % (q*q) == 0))
            predicted *= 1-rho
        assert observed == predicted, (modulus, b, observed, predicted)
        cases += 1
        forced_zero += predicted == 0

result = dict(cases=cases, forced_zero=forced_zero, primes=list(primes), maximum_modulus=24,
              passed=True, scope="Finite CRT probabilities only, not asymptotic proof or novelty.")
Path(__file__).with_name("squarefree_crt.json").write_text(json.dumps(result, indent=2)+"\n")
print(json.dumps(result, indent=2))
