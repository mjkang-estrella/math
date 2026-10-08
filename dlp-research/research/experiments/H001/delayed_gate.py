"""Arithmetic sanity checks, NOT an EC experiment or a rho runtime theorem.
The phase-collision estimate uses an independent-stage idealization; actual
r-adding maps, long-range collisions, cycles and distinguished points need
separate analysis. No hardware timing or calibrated operation weights.
"""
import json
from math import sqrt

rows = []
for h in (2, 6):
    for t in (1, 2, 4, 8):
        d = sqrt((h + t - 1) / h)
        rows.append(dict(orbit_size=h, block_length=t,
                         heuristic_additions_ratio=t/d,
                         heuristic_break_even_C_over_A=None if t == 1 else (t-d)/(d-1)))
q = 11
canon = lambda x: min(x % q, (-x) % q)
f = lambda x: (x + 1) % q
assert canon(1) == canon(-1) == 1
assert canon(f(1)) == 2 and canon(f(-1)) == 0
# Exact two-input calculation for independent uniform maps on N points,
# with equally sized equivalence classes. This does not establish a rho
# trajectory distribution or the heuristic work ratios above.
N = 120
pairs = []
for h in (2, 6):
    for t in (1, 2, 4, 8):
        equal = 1 - (1 - 1/N)**t
        orbit_equal = equal + (1-equal)*(h-1)/(N-1)
        pairs.append(dict(N=N, h=h, t=t, endpoint_pair_collision=orbit_equal,
                          first_order_approximation=(h+t-1)/N))
print(json.dumps(dict(
    kind='analytic sanity checks only',
    independent_stage_heuristic=rows,
    independent_uniform_maps_pair_probability=pairs,
    quotient_counterexample=dict(q=11, left=1, right=10,
                                 canonical_inputs=[1,1], canonical_successors=[2,0]),
    synthetic_EC_runs=0, verified_improvement='NONE'), indent=2, sort_keys=True))
