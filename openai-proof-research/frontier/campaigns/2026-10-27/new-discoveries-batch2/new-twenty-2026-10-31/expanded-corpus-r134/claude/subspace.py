import sys, os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
# Players at all points of a d-dimensional linear subspace of F_2^n, given by the multiplicity
# m_f of each nonzero coordinate functional f in F_2^d (coordinates of the profile).
import itertools
from math import lcm
from vor import scores_lowmem as scores
def profile(d, mult):
    funcs = [f for f in range(1, 1 << d)]
    cols = []
    for f, m in zip(funcs, mult): cols += [f] * m
    n = len(cols)
    pos = []
    for s in range(1 << d):
        v = 0
        for j, f in enumerate(cols):
            if bin(f & s).count('1') % 2: v |= 1 << j
        pos.append(v)
    return n, pos
def check(d, mult):
    n, pos = profile(d, mult)
    k = len(pos); L = lcm(*range(1, k + 1)); V = 1 << n
    S = scores(n, pos, 0, L)
    cur = S[0]; best = max(S)
    return n, cur, best, S.index(best), L * V // k
if __name__ == '__main__':
    d = int(sys.argv[1]); mult = list(map(int, sys.argv[2].split(',')))
    n, cur, best, arg, fair = check(d, mult)
    print('d', d, 'mult', mult, 'n', n, 'cur', cur, 'fair', fair, 'best', best, 'arg', bin(arg), 'EQ' if best <= cur else 'NOT', 'gain', (best - cur) / (fair * len(range(1 << d))))
