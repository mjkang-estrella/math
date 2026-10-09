"""Finite algebra checks for the paper; these do not prove asymptotic estimates."""
from collections import Counter
from fractions import Fraction as F
from itertools import product
from math import gcd, lcm
from pathlib import Path
import cmath
import hashlib
import json
import re

ROOT = Path(__file__).resolve().parent
counts = Counter()

for modulus in range(1, 25):
    units = [t for t in range(modulus) if gcd(t, modulus) == 1]
    for residue, value, shift in product(range(modulus), range(modulus), units):
        lhs = sum((t * value - residue) % modulus == 0
                  and (t * (value + shift) - residue - 1) % modulus == 0
                  for t in units)
        assert lhs == int((value - residue * shift) % modulus == 0)
        counts['unit_orbit_including_nonunit_residues'] += 1

for modulus in range(1, 41):
    for residue in range(modulus):
        if gcd(residue, modulus) != 1:
            continue
        for prime in (2, 3, 5, 7, 11):
            combined = lcm(modulus, prime * prime)
            lifts = [n for n in range(residue, combined, modulus)
                     if gcd(n, combined) == 1]
            actual = F(sum((n - 1) % (prime * prime) == 0 for n in lifts), len(lifts))
            if modulus % prime:
                expected = F(1, prime * (prime - 1))
            elif modulus % (prime * prime):
                expected = F(int((residue - 1) % prime == 0), prime)
            else:
                expected = F(int((residue - 1) % (prime * prime) == 0))
            assert actual == expected
            counts['square_density_reduced_lifts'] += 1

def small_part(n):
    a = 1
    omega = 0
    for p in (2, 3, 5, 7):
        while n % p == 0:
            n //= p
            a *= p
            omega += 1
    return a, omega, n

for n in range(1, 301):
    a, omega, residual = small_part(n)
    for smooth in (1, 2, 4, 6, 8, 9, 12, 25, 49, 72, 225):
        small, exponent, _ = small_part(smooth)
        aa, oo, rr = small_part(n * smooth)
        assert (aa, oo, rr) == (a * small, omega + exponent, residual)
        counts['full_small_part_covariance_with_repeated_primes'] += 1

maximum_error = 0.0
for modulus in range(1, 13):
    for residue in range(modulus):
        for omega in range(0, 3 * modulus + 1):
            value = sum(cmath.exp(2j * cmath.pi * j * (omega - residue) / modulus)
                        for j in range(modulus)) / modulus
            error = abs(value - int(omega % modulus == residue))
            maximum_error = max(maximum_error, error)
            assert error < 1e-12
            counts['root_of_unity_filter_floating_point'] += 1

for probabilities in product((F(0), F(1, 3), F(2, 5), F(1)), repeat=4):
    direct = F(0)
    expanded = F(0)
    # Retain a success in each of two disjoint group families.
    for bits in product((0, 1), repeat=4):
        if not (sum(bits[:2]) >= 1 and sum(bits[2:]) >= 1):
            continue
        term = F(1)
        for bit, probability in zip(bits, probabilities):
            term *= probability if bit else 1 - probability
        direct += term
        failures = [i for i, bit in enumerate(bits) if not bit]
        for extra in product((0, 1), repeat=len(failures)):
            selected = {i for i, bit in enumerate(bits) if bit}
            selected.update(i for i, bit in zip(failures, extra) if bit)
            term = F((-1) ** sum(extra))
            for i in selected:
                term *= probabilities[i]
            expanded += term
    assert direct == expanded and 0 <= direct <= 1
    counts['signed_coin_reconstruction_exact_rational'] += 1

for j, hits, groups in product(range(2, 8), range(1, 14), range(1, 8)):
    q = F(2, 5)
    assert j ** hits * (q / j) ** (hits - groups) == j ** groups * q ** (hits - groups)
    counts['allocation_coefficient_exact_rational'] += 1

manifest = json.loads((ROOT / 'evidence/upstream-manifest.json').read_text())
all_source = []
for row in manifest['files']:
    data = (ROOT / 'evidence/upstream' / row['path']).read_bytes()
    assert hashlib.sha256(data).hexdigest() == row['sha256']
    assert hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest() == row['git_blob']
    all_source.append(data.decode())
    counts['pinned_source_hash_pairs'] += 1
sources = '\n'.join(all_source)
for label in re.findall(r'\\texttt\{([^{}]+:[^{}]+)\}', (ROOT / 'evidence/source-dependency-ledger.tex').read_text()):
    assert '\\label{' + label + '}' in sources, label
    counts['archived_source_label_existence'] += 1

result = {
    'status': 'passed', 'checks': dict(counts),
    'maximum_fourier_floating_point_error': maximum_error,
    'limits': 'Finite identities and provenance only; no proof of asymptotic bounds, human peer review, or formal verification.',
}
(ROOT / 'evidence/finite-checks.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps(result, indent=2))
