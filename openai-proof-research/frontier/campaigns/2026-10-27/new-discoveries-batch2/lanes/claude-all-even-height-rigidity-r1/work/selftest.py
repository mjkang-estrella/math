"""Control: source planar all-even sets (Section 6.2) must be all-even;
P15 minus P3 (float mode) all-even; perturbations must fail."""
import sys, os, math
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from lp import odd_directions

S8 = [(0, -1), (3, -1), (-4, 0), (0, 0), (6, 0), (-1, 1), (2, 1), (0, 2)]
S10 = S8 + [(-2, 0), (4, 0)]
S10p = [(1, 1), (7, 1), (2, 3), (4, 3), (5, 3), (6, 3), (7, 3), (4, 4), (1, 5), (7, 5)]
S14 = [(-5, -5), (5, -5), (-1, -2), (1, -2), (-2, -1), (-1, -1), (2, -1), (-2, 1),
       (-1, 1), (2, 1), (-1, 2), (1, 2), (-5, 5), (5, 5)]
S16 = S14 + [(-3, -3), (3, 3)]
S18 = S16 + [(-3, 3), (3, -3)]


def Ak(k):
    A = [(3 * i - 1, -1) for i in range(-k, k + 2)]
    A += [(2 * i - 1, 0) for i in range(-3 * k - 2, 3 * k + 4) if i != 1]
    A += [(3 * i + 1, 1) for i in range(-k - 1, k + 1)]
    A += [(-1, 2)]
    return A


for name, S in [('S8', S8), ('S10', S10), ('S10p', S10p), ('S14', S14), ('S16', S16),
                ('S18', S18), ('A1', Ak(1)), ('A2', Ak(2))]:
    print(name, len(S), 'odd dirs:', len(odd_directions(S)))
    S3 = [p + (0,) for p in S]
    print(name, 'in R3 odd dirs:', len(odd_directions(S3)))
P = [(math.cos(2 * math.pi * i / 15), math.sin(2 * math.pi * i / 15)) for i in range(15) if i % 5]
print('P15-P3 float odd dirs:', len(odd_directions(P, exact=False)))
print('S8 minus a point odd:', len(odd_directions(S8[:-1])))
print('S8 moved point odd:', len(odd_directions(S8[:-1] + [(0, 3)])))
