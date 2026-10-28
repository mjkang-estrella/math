#!/usr/bin/env python3
"""Monte-Carlo end-to-end falsification check of literal Conjecture 1 LT identity
and of the conditional identity (2). Correct Beta sampling: Beta(p,q)=G_p/(G_p+G_q).
(A previous version of this script sampled Beta(p,q) as G_p/G_q, i.e. beta-prime,
which produced spurious discrepancies; corrected 2026-10-28.) Diagnostics only."""
import json
import numpy as np
from pathlib import Path

rng = np.random.default_rng(20261028)
N = 1 << 23

def beta(p, q, n):
    g1 = rng.gamma(p, 1.0, n)
    g2 = rng.gamma(q, 1.0, n)
    return np.clip(g1 / (g1 + g2), 1e-300, 1 - 1e-16)

out = {'conditional_identity': [], 'end_to_end': []}
for (u, b, lam) in [(0.25, 0.2, 1.0), (0.5, 0.35, 2.0), (0.1, 0.3, 0.5)]:
    c = 2 * np.sqrt(u * (1 - u))
    lhs = float(np.mean(np.exp(-lam * (u / rng.gamma(b, 1, N)
                                       + (1 - u) / rng.gamma(b, 1, N)))))
    W = beta(b, 0.5 - b, N)
    rhs = float(np.mean(np.exp(-lam * (1 + c / np.sqrt(W)) / rng.gamma(b, 1, N))))
    out['conditional_identity'].append(
        {'u': u, 'b': b, 'lambda': lam, 'lhs': lhs, 'rhs': rhs,
         'rel_diff': abs(lhs - rhs) / lhs})

for (a, b, lam) in [(1.3, 0.2, 0.7), (0.6, 0.35, 2.0), (2.0, 0.1, 0.2),
                    (0.4, 0.45, 1.0), (0.9, 0.3, 5.0)]:
    x1 = rng.gamma(a, 1, N) / rng.gamma(b, 1, N)
    x2 = rng.gamma(a, 1, N) / rng.gamma(b, 1, N)
    lhs = float(np.mean(np.exp(-lam * (x1 + x2))))
    y = rng.gamma(2 * a, 1, N) / rng.gamma(b, 1, N)
    b1 = beta(a, 0.5, N)
    b2 = beta(b, 0.5 - b, N)
    rhs = float(np.mean(np.exp(-lam * y * (1 + np.sqrt(b1 / b2)))))
    out['end_to_end'].append({'a': a, 'b': b, 'lambda': lam, 'lhs': lhs,
                              'rhs': rhs, 'rel_diff': abs(lhs - rhs) / lhs})

Path('_mc_endtoend.json').write_text(json.dumps(out, indent=1))
print(json.dumps(out, indent=1))
