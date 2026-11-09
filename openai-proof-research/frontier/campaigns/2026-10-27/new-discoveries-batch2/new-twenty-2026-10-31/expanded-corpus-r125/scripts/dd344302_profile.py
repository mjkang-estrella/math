import sys
sys.path.insert(0, sys.argv[1])
from dd344302 import dd_single
n = int(sys.argv[2])
vals = {i: dd_single(n, i) for i in range(2, n)}
from fractions import Fraction
for i in range(2, n-1):
    a, b = vals[i], vals[i+1]
    rel = (b - a) / a
    print(i, '%+.3e' % rel)
