#!/usr/bin/env python3
"""Exact arithmetic support only; does not prove a theorem about klt germs.
Copyright (c) 2026 Myeongjin Kang. SPDX-License-Identifier: MIT
"""
from fractions import Fraction as F
import json

def run():
    rows = []
    for n in range(2, 101):
        epsilon = F(1, 3) if n < 4 else F(1, n - 1)
        test = 2 * (n - 1 - epsilon) ** n / (1 - epsilon)
        expected = F(4, 3) if n == 2 else F(125, 9) if n == 3 else 2 * n ** n * F(n - 2, n - 1) ** (n - 1)
        assert test == expected
        assert 0 < test < 2 * (n - 1) ** n
        assert 3 * (1 - epsilon) >= 2
        if n >= 3:
            assert 3 * (n - 2) ** n < test
        if n <= 8:
            rows.append({'n': n, 'epsilon': str(epsilon), 'bound': str(test)})
    return {'status': 'PASS', 'dimensions_checked': [2, 100], 'scope': 'finite rational formula checks only', 'sample': rows}

if __name__ == '__main__':
    print(json.dumps(run(), indent=2))
