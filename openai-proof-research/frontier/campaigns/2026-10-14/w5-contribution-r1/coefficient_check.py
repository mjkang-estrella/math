#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# Copyright (c) 2026 Myeongjin Kang. No affiliation.
# Original reviewer check: exact rational test of the W5 coefficient identity
#   (1+e^2)(|c/a|^2+|1-c/a|^2/e^2) = 1 + kappa|c-c0|^2,
#   c0 = a/(1+e^2), kappa = (1+e^2)^2/(a^2 e^2),
# plus a false-identity control. Supports, does not replace, the algebra.
from fractions import Fraction as Q
import itertools, sys

def n2(x, y):
    return x * x + y * y

def lhs(a, e, cr, ci):
    xr, xi = cr / a, ci / a
    return (1 + e * e) * (n2(xr, xi) + n2(1 - xr, -xi) / (e * e))

def rhs(a, e, cr, ci, c0_shift=Q(0)):
    c0 = a / (1 + e * e) + c0_shift
    kappa = (1 + e * e) ** 2 / (a * a * e * e)
    return 1 + kappa * n2(cr - c0, ci)

def main():
    vals = [Q(1, 3), Q(2), Q(5, 7)]
    cs = [Q(-3, 2), Q(0), Q(1, 5), Q(7, 4)]
    cases = 0
    for a, e, cr, ci in itertools.product(vals, vals, cs, cs):
        if lhs(a, e, cr, ci) != rhs(a, e, cr, ci):
            print('IDENTITY_FAILED', a, e, cr, ci); return 1
        cases += 1
    # control: shifting the reference coefficient must break the identity
    broken = sum(lhs(a, e, cr, ci) != rhs(a, e, cr, ci, Q(1, 11))
                 for a, e, cr, ci in itertools.product(vals, vals, cs, cs))
    if broken == 0:
        print('CONTROL_FAILED'); return 1
    print('COEFFICIENT_IDENTITY_EXACT cases=%d control_rejections=%d' % (cases, broken))
    return 0

if __name__ == '__main__':
    sys.exit(main())
