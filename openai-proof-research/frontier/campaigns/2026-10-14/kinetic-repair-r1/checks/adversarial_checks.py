"""Exact rational checks for review.md; these do not prove W or Theorem F."""
from fractions import Fraction as F
import json
from pathlib import Path

t12, t23, t14 = F(1,5), F(2,5), F(9,20)
# Geometric normal is +e1. All incoming normal velocities are negative.
v = [-1, 0, 3, 4]
x12 = [F(0), F(-1)]
assert v[0]-v[1] == -1
v[0], v[1] = v[1], v[0]
x1_t23 = x12[0] + v[0]*(t23-t12)
x2_t23 = x12[1] + v[1]*(t23-t12)
x3_t23 = x2_t23-1
assert x1_t23 == 0 and x2_t23 == F(-6,5)
assert x3_t23 == F(-11,5) and v[1]-v[2] == -4
v[1], v[2] = v[2], v[1]
# x1 = 0; x2 = x2_t23 + 3*(t-t23). Solve x1-x2 = 1.
t_redundant = t23 + (-x2_t23-1)/v[1]
assert t_redundant == F(7,15)
assert t_redundant > t14 > t23
assert v[0]-v[1] == -3
v[0], v[1] = v[1], v[0]
formal_x1_t14 = x1_t23 + v[0]*(t14-t_redundant)
x4_t14 = formal_x1_t14-1
assert formal_x1_t14 == F(-1,20) and x4_t14 == F(-21,20)
assert v[0]-v[3] == -1
assert 0-x4_t14 == F(21,20) # true chronological pre-redundant branch misses contact
# The indicator Q rejects at the next prescribed merger, since 9/20 < 7/15.
assert not all(a < b for a,b in zip([t12,t23,t_redundant],[t23,t_redundant,t14]))
# Perturbations smaller than this strict time gap still have the same ordering.
gap = t_redundant-t14
assert gap == F(1,60)
for m in range(1,12):
    for p in range(m):
        for h in range(1,6):
            eps_exp = -2*(m-h) + 2*(m-1-p) + 2*p
            assert eps_exp == 2*(h-1)
assert -1 + F(21,20)*F(21,22) == F(1,440)
assert -1 + F(3,2)*F(1,2) == F(-1,4)
assert -F(1,2) == 1-F(3,2) # leading microscopic third-moment exponent in mu
result = {
 'method': 'exact rational arithmetic; no Monte Carlo and no proof claim',
 'counterchart': {
   'diameter': 1, 'merger_times': [str(t12),str(t23),str(t14)],
   'redundant_time': str(t_redundant), 'time_order_violation_gap': str(gap),
   'formal_x1_at_last_merger': str(formal_x1_t14),
   'chronological_x1_at_last_merger': '0',
   'x4_at_last_merger': str(x4_t14),
   'geometric_incoming_relative_velocities': [-1,-4,-3,-1],
   'Q_rejects': True,
 },
 'scaling': 'mu^(m-h)*epsilon^(2(m-1-p))*epsilon^(2p)=mu^(1-h)',
 'transfer_epsilon_exponent': '1/440',
 'dyadic_mu_exponent': '-1/4',
 'microscopic_leading_mu_exponent': '-1/2',
 'microscopic_remainder_epsilon_exponent': 'P-6',
 'second_moment_union_bound': 'T/eta^2 (does not vanish)',
 'status': 'all exact assertions passed'
}
Path(__file__).with_name('adversarial_checks.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
