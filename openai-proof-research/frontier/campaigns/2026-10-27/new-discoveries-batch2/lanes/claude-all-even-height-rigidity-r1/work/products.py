"""Product family S = Q x H subset R^3 (Q planar, H subset R), exact rationals.
Q ranges over the source's planar all-even sets (Sect. 6.2) plus perturbation
controls; H over small 1-D sets.  Reports number of odd line directions.
Support/exploration only; a zero with affine dim 3 would be a candidate to be
re-verified independently."""
import sys, os, json
from fractions import Fraction as F
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from lp import odd_directions
from selftest_data import SETS

Hs = {'012': [0, 1, 2], '013': [0, 1, 3], '0124': [0, 1, 2, 4], '01': [0, 1],
      '0123': [0, 1, 2, 3], '01-3': [0, 1, 3], '0,1,1/2*3': [0, 1, F(3, 2)],
      '01234': [0, 1, 2, 3, 4], '0135': [0, 1, 3, 5]}
res = {}
for qn, Q in SETS.items():
    for hn, H in Hs.items():
        S = [(F(x), F(y), F(h)) for (x, y) in Q for h in H]
        od = odd_directions(S)
        res[f'{qn} x {hn}'] = len(od)
print(json.dumps(res, indent=0))
