"""Exact finite identities for the variable-edge reconstruction screen.

These identities check the explicit ray example, not the general theorem.
"""
from fractions import Fraction as F
import json

product = F(1)
weighted_potential = F(0)
records = []
for n in range(1, 1001):
    lam = 1 - F(1, (n + 1) ** 2)
    product *= lam
    resistance = product ** -2
    weighted_potential += (1 - lam ** 4) * resistance ** 2
    assert product == F(n + 2, 2 * (n + 1))
    assert weighted_potential == product ** -4 - 1
    if n in [1, 2, 10, 100, 1000]:
        records.append({'depth': n, 'channel_product': str(product),
                        'reconstruction_advantage': str(F(3, 4) * product),
                        'weighted_unit_flow_potential': str(weighted_potential)})

# Thermal means 1 and 3, equal mixing: exp(g(2)) divided by
# the sharp conditional-EPI output entropy power is 729/728.
epni_power = F(27, 4)
conditional_epi_power = (F(4) + F(256, 27)) / 2
assert epni_power / conditional_epi_power == F(729, 728)
result = {'exact_ray_identities_checked': 1000, 'samples': records,
          'conditional_entropy_power_ratio': '729/728',
          'scope': 'Finite algebra checks only; not a capacity sufficiency proof.'}
print(json.dumps(result, indent=2))
