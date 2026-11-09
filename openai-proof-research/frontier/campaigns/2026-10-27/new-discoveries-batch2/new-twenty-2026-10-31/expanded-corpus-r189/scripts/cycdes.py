"""Check beta(D) = beta([n-1]\\D) for the descent-set distribution beta of n-cycles,
the key lemma of the Gessel-Reutenauer bridge for MathDB 333370.
Enumerates n-cycles as (1 t_2 ... t_n) over permutations t of {2..n}.
usage: cycdes.py NMIN NMAX
"""
import sys, itertools, collections
for n in range(int(sys.argv[1]), int(sys.argv[2]) + 1):
    beta = collections.Counter()
    full = (1 << (n - 1)) - 1
    for t in itertools.permutations(range(2, n + 1)):
        cyc = (1,) + t
        pi = [0] * (n + 1)
        for i in range(n):
            pi[cyc[i]] = cyc[(i + 1) % n]
        d = 0
        for i in range(1, n):
            if pi[i] > pi[i + 1]:
                d |= 1 << (i - 1)
        beta[d] += 1
    asym = sum(1 for D in range(full + 1) if beta[D] != beta[full ^ D])
    print('n', n, 'n mod 4', n % 4, 'cycles', sum(beta.values()), 'descent sets D with beta(D)!=beta(complement):', asym, flush=True)
