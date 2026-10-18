#!/usr/bin/env python3
"""MIT. Rational exponent checks and route controls; not a proof."""
from fractions import Fraction as F
import json

rows = []
for n in range(2, 41):
    s = F(n, 2*(n+1))
    # Illustrative admissible p, not the unspecified exponent of the source.
    p = 2 + F(1, 2*(n+1))
    r = 2 + F(1, 4*(n+1))
    q = r/(r-1)
    alpha = 2/q
    delta = n+2*s-2*n/q
    r_edge = F(2*(n+1), n)
    assert 2 < r < min(p, r_edge)
    assert alpha > 1 and delta > 0
    assert delta == 2*s-n+2*n/r
    # Negative controls: the geometric decay disappears at the edge,
    # and is reversed beyond it; alpha=1 has zero convexity deficit.
    assert 2*s-n+2*n/r_edge == 0
    assert 2*s-n+2*n/(r_edge+F(1,100)) < 0
    assert (F(1)+1)**1-F(1)**1-1 == 0
    assert n/(n-2*s) == F(n+1,n)
    bks_loss = F(n,2)-2*s
    assert bks_loss == F(n*(n-1),2*(n+1)) > 0
    rows.append({'n': n, 'alpha': str(alpha), 'delta': str(delta),
                 'bks_frequency_loss': str(bks_loss)})

# Exact finite Rademacher Gram controls. Columns are indexed by bits;
# rows are all sign vectors. Normalized Gram is the identity, while
# all singular values are one: no dimension-free finite Schatten bound.
for m in range(1, 9):
    for j in range(m):
        for k in range(m):
            gram = sum((1 if (v>>j)&1 else -1)*
                       (1 if (v>>k)&1 else -1) for v in range(1<<m))
            assert gram == ((1<<m) if j == k else 0)

print(json.dumps({'status': 'PASS_FINITE_DIAGNOSTIC_NOT_PROOF',
                  'rational_cases': rows,
                  'negative_controls': ['delta_zero_at_edge',
                      'delta_negative_above_edge', 'convexity_zero_at_alpha_one'],
                  'rademacher_gram_dimensions': list(range(1,9))},
                 sort_keys=True, indent=2))
