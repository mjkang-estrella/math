#!/usr/bin/env python3
# Copyright (c) 2026 Myeongjin Kang. MIT license.
"""Deterministic formula checks. These are not proof of full target B."""
from bisect import bisect_right
from fractions import Fraction
import json
import math
import random


def cap_cdf(z):
    if z <= -1:
        return 0.0
    if z >= 1:
        return 1.0
    return 0.5 + (math.asin(z) + z * math.sqrt(1-z*z))/math.pi


def disk_kernel(s, radius):
    z = s/radius
    return 2*math.sqrt(max(0.0, 1-z*z))/(math.pi*radius)


def profile_value(s, positions, levels):
    return levels[bisect_right(positions, s)]


def average(s, radius, positions, levels):
    heights = [abs(v) for v in levels]
    return heights[0] + sum(
        (heights[i+1]-heights[i])*cap_cdf((s-z)/radius)
        for i, z in enumerate(positions))


def derivative(s, radius, positions, levels):
    heights = [abs(v) for v in levels]
    return sum((heights[i+1]-heights[i])*disk_kernel(s-z, radius)
               for i, z in enumerate(positions))


def layers():
    # Deliberately asymmetric, including a sign-crossing jump, equal
    # endpoint magnitudes, many plateaux, and an approximation to Cantor Dq.
    profiles = [
        ([-2.2, -0.19, 0.07, 1.8], [-2, -1.95, -.3, .011, 4]),
        ([.13], [-1, 3]),
        ([-2, -.1, .01, .02, 1], [-2, -1.9, -1.8, .01, .4, 2]),
        ([-1.8, .7, 2.5], [0, .03, 1.5, 3]),
    ]
    rng = random.Random(20261016)
    for _ in range(12):
        levels = sorted([-1.7, 3.4] + [rng.uniform(-1.7, 3.4) for _ in range(14)])
        positions = sorted(rng.uniform(-2, 2) for _ in range(len(levels)-1))
        profiles.append((positions, levels))
    positions = []
    for i in range(32):
        digits = [(i >> k) & 1 for k in range(5)]
        positions.append(-1 + 2*sum(2*d/3**(k+1) for k, d in enumerate(digits)))
    positions.sort()
    profiles.append((positions, [-1+3*i/32 for i in range(33)]))

    comparisons = 0
    minimum_active_derivative = 0.0
    max_variation_error = 0.0
    for positions, levels in profiles:
        assert all(a < b for a, b in zip(positions, positions[1:]))
        assert all(a <= b for a, b in zip(levels, levels[1:]))
        A, B = -levels[0], levels[-1]
        assert 0 <= A <= B
        for t in (.023, .31, 1.7, 6.0):
            radii = [t*2**(-k/8) for k in range(89)]
            extent = max(abs(z) for z in positions) + t + 1
            grid = [-extent+2*extent*i/320 for i in range(321)]
            for s in grid:
                q = profile_value(s, positions, levels)
                for radius in radii[::8]:
                    if q > A and s not in positions:
                        d = derivative(s, radius, positions, levels)
                        minimum_active_derivative = min(minimum_active_derivative, d)
                        assert d >= -1e-10
                    if q <= A:
                        assert average(s, radius, positions, levels) <= (A+B)/2+1e-12
            envelopes = [max(abs(profile_value(s, positions, levels)),
                             max(average(s, r, positions, levels) for r in radii))
                         for s in grid]
            for c in ((A+B)/2, (A+3*B)/4, B+.5):
                values = [max(c, value) for value in envelopes]
                assert all(b >= a-1e-11 for a, b in zip(values, values[1:]))
                variation = sum(abs(b-a) for a, b in zip(values, values[1:]))
                error = abs(variation-max(0, B-c))
                max_variation_error = max(max_variation_error, error)
                assert error < 1e-9
                # Reflection gives the opposite monotonicity, same variation.
                reflected_values = list(reversed(values))
                assert all(b <= a+1e-11 for a, b in zip(reflected_values, reflected_values[1:]))
                comparisons += len(values)-1
    return {'profiles': len(profiles), 'monotonicity_comparisons': comparisons,
            'minimum_active_derivative_rounded': round(minimum_active_derivative, 10),
            'max_variation_error_below': 1e-9}


def hat(x, vertex, k):
    mesh = Fraction(1, 2**k)
    return max(Fraction(0), 1-abs(x-vertex*mesh)/mesh)


def scalar_tent_mass(atoms, k):
    bound = 2**(k+1)
    return sum(abs(sum(mass*hat(x, v, k) for x, mass in atoms))
               for v in range(-bound, bound+1))


def tent_checks():
    # These are 1D hats; the 2D product identity reduces to this in
    # each coordinate. All arithmetic, including cancellation, is exact.
    test_points = [Fraction(k, 64) for k in range(-48, 49)]
    for k in range(4):
        for vertex in range(-2**k, 2**k+1):
            for x in test_points:
                rhs = sum(hat(Fraction(child, 2**(k+1)), vertex, k)*hat(x, child, k+1)
                          for child in range(2*vertex-1, 2*vertex+2))
                assert hat(x, vertex, k) == rhs
    signed_atoms = [(Fraction(-3, 4), Fraction(1)),
                    (Fraction(-1, 8), Fraction(-2)),
                    (Fraction(1, 4), Fraction(3)),
                    (Fraction(3, 4), Fraction(-1))]
    masses = [scalar_tent_mass(signed_atoms, k) for k in range(6)]
    total = sum(abs(v) for _, v in signed_atoms)
    for k in range(5):
        summed_defects = sum((masses[l+1]-masses[l])/2 for l in range(k, 5))
        assert summed_defects == (total-masses[k])/2
    # A monotone atomic staircase has no scalar cancellation budget,
    # despite singular derivative measures versus the affine limit.
    for j in (4, 8, 16, 32):
        staircase = [(Fraction(i, j), Fraction(1, j)) for i in range(j)]
        for k in range(5):
            assert scalar_tent_mass(staircase, k) == 1
    # Opposite absolute-value derivatives of a narrow valley cancel at
    # coarse mesh while their variation stays 2. Not a strict sequence.
    valley = []
    for j in (8, 16, 32, 64):
        atoms = [(Fraction(-1, j), Fraction(-1)), (Fraction(1, j), Fraction(1))]
        coarse_mass = scalar_tent_mass(atoms, 0)
        assert coarse_mass == Fraction(2, j)
        defect = (Fraction(2)-coarse_mass)/2
        valley.append({'j':j, 'coarse_absolute_mass':str(coarse_mass),
                       'fine_defect_budget':str(defect)})
    return {'positive_staircase_defect': '0 exactly',
            'signed_atomic_telescope': 'PASS, exact rational arithmetic',
            'absolute_valley_countercheck': valley}


def main():
    result = {'status':'SUPPORTING_FORMULA_CHECKS_PASS',
              'full_target_B':'UNRESOLVED', 'independent_review':False,
              'arbitrary_monotone_layers':layers(), 'tent_budgets':tent_checks(),
              'tail_polar_integral_coefficient': '8/R for bound 16/(pi*|x|^3) outside 4R',
              'limits':'Finite profiles and exact identities only; not a proof of BV continuity.'}
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == '__main__':
    main()
