"""New finite identities only; imported/executed only after immutable validation."""
from itertools import product
from fractions import Fraction
from math import comb

def run():
    checks = {'same_site_patterns': 0, 'centered_multi_quad': 0,
              'response_table_weight': 0, 'factorial_generating_identity': 0}
    # All pairs of Boolean functions on two bits, all baseline states, all sites.
    for f, g in product(range(16), repeat=2):
        def bit(fn, x): return (fn >> x) & 1
        for x in range(4):
            for site in range(2):
                y = x ^ (1 << site)
                indicators = [int(bit(fn, x) != bit(fn, y)) for fn in (f, g)]
                union = 0
                for pattern in range(1, 4):
                    exact = int(sum(a << j for j, a in enumerate(indicators)) == pattern)
                    inclusion = 0
                    complement = 3 ^ pattern
                    for extra in range(4):
                        if extra & ~complement: continue
                        mask = pattern | extra
                        monomial = 1
                        for j in range(2):
                            if mask >> j & 1: monomial *= indicators[j]
                        inclusion += (-1) ** extra.bit_count() * monomial
                    assert exact == inclusion
                    union += exact
                    checks['same_site_patterns'] += 1
                assert union == int(any(indicators))
            # Dedicated labels 1,2. Each site's membership can require both quads.
            for masks in product(range(1,4), repeat=2):
                actual = 0
                expected = 1
                for i, mask in enumerate(masks):
                    for j, fn in enumerate((f,g)):
                        if mask >> j & 1:
                            expected *= int(bit(fn,x) != bit(fn,x ^ (1<<i)))
                for active in range(4):
                    value = 1
                    for i, mask in enumerate(masks):
                        label = x ^ ((1<<i) if active >> i & 1 else 0)
                        for j, fn in enumerate((f,g)):
                            if mask >> j & 1: value *= int(bit(fn,x) != bit(fn,label))
                    actual += (-1)**(2-active.bit_count()) * value
                assert actual == expected
                checks['centered_multi_quad'] += 1
                # Arbitrary response test at an extra label: all four assignments.
                for toggle in range(4):
                    response = bit(f,x ^ toggle) * (1-bit(g,x ^ toggle))
                    signed = 0
                    for active in range(4):
                        value = 1
                        for i, mask in enumerate(masks):
                            label=x ^ ((1<<i) if active >> i & 1 else 0)
                            for j, fn in enumerate((f,g)):
                                if mask >> j & 1: value *= int(bit(fn,x) != bit(fn,label))
                        z=x ^ (toggle & active)
                        signed += (-1)**(2-active.bit_count()) * value * bit(f,z)*(1-bit(g,z))
                    assert signed == expected*response
                    checks['response_table_weight'] += 1
    for n in range(21):
        for t in (Fraction(0),Fraction(1,7),Fraction(2,3),Fraction(2)):
            assert (1+t)**n == sum(comb(n,k)*t**k for k in range(n+1))
            checks['factorial_generating_identity'] += 1
    return {'status':'PASS','checks':checks,'arithmetic':'exact integers and fractions',
            'scope':'finite identities only; no arm estimate, planar network, universal theorem, or semantic-read certification'}
