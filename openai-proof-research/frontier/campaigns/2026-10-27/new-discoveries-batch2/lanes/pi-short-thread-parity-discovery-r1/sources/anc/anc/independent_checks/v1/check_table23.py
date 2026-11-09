"""Check Table tab:blocked23, Lemma lem:universal, W(kappa0)=3, and g(S(2,3,z)) for z<=ZMAX."""
import sys, time
from spider import Gamma, V, rho, times, spider, MEMO

RMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 300
ZMAX = int(sys.argv[2]) if len(sys.argv) > 2 else 300

pi = lambda r: r % 2
pib = lambda r: 1 - r % 2


def pre(prefix, f):
    return lambda r: prefix[r - 1] if r <= len(prefix) else f(r)


T = {}
def put(s, K, fin, fout):
    T[(s, tuple(sorted(K)))] = {'I': fin, 'O': fout}

F, I, O = 'F', 'I', 'O'
put('n', [(2, F), (3, F)], pre([2, 6, 7, 5, 4], lambda r: r + 2), pre([2, 6, 7, 5, 4], lambda r: r + 2))
put('n', [(2, F), (1, I)], pre([2], pi), pib)
put('n', [(2, F), (1, O)], pib, pre([2], pi))
put('n', [(2, F), (2, I)], pib, pi)
put('n', [(2, F), (2, O)], pi, pib)
put('n', [(1, I), (3, F)], pre([5, 4, 5], lambda r: 2 + pib(r)), pre([1], lambda r: 2 + pi(r)))
put('n', [(1, O), (3, F)], pre([1], lambda r: 2 + pi(r)), pre([5, 4, 5], lambda r: 2 + pib(r)))
put('n', [(1, I), (1, I)], pib, pi)
put('n', [(1, O), (1, O)], pi, pib)
put('n', [(1, I), (1, O)], lambda r: r, lambda r: r)
put('n', [(1, I), (2, I)], pi, pre([2], pib))
put('n', [(1, I), (2, O)], pib, pre([2], pi))
put('n', [(1, O), (2, I)], pre([2], pi), pib)
put('n', [(1, O), (2, O)], pre([2], pib), pi)
put('i', [(2, F)], pre([3], pib), pi)
put('i', [(3, F)], lambda r: 4 + pib(r), pre([0, 4, 5, 7, 6, 7, 6], lambda r: 4 + pi(r)))
put('i', [(1, I)], pi, pib)
put('i', [(1, O)], lambda r: r ^ 1, lambda r: r ^ 1)
put('i', [(2, I)], pib, pre([3], pi))
put('i', [(2, O)], pi, pre([3], pib))
# s = o rows by reversal: V^phi_(o;K) = V^{phibar}_(i;Kbar)
bar = {'I': 'O', 'O': 'I', 'F': 'F'}
for (s, K) in list(T):
    if s == 'i':
        Kb = tuple(sorted((h, bar[p]) for (h, p) in K))
        T[('o', Kb)] = {'I': T[(s, K)]['O'], 'O': T[(s, K)]['I']}
print('table entries:', len(T))

# own reachability: successors of short moves
def successors(s, K):
    out = []
    for idx, (h, psi) in enumerate(K):
        rest = K[:idx] + K[idx + 1:]
        for j in range(1, h + 1):
            for d in 'IO':
                if j == h and psi != 'F' and d != psi:
                    continue
                if j >= 2:
                    out.append((s, tuple(sorted(rest + ((j - 1, d),)))))
                elif s == 'n':
                    out.append((times(s, d), rest))
    return out

k0 = ('n', ((2, F), (3, F)))
seen, st = {k0}, [k0]
while st:
    k = st.pop()
    for k2 in successors(*k):
        if k2 not in seen:
            seen.add(k2); st.append(k2)
print('reachable configurations:', len(seen), ' same set as table:', seen == set(T))
from collections import Counter
print('by status:', Counter(s for s, K in seen))

t0 = time.time()
bad = 0
for r in range(1, RMAX + 1):
    for (s, K), fam in T.items():
        for phi in 'IO':
            v = V(s, K, phi, r)
            if v != fam[phi](r):
                bad += 1
                if bad < 20:
                    print('MISMATCH', s, K, phi, r, v, fam[phi](r))
print('blocked families checked for r <= %d: %d mismatches (%.1fs)' % (RMAX, bad, time.time() - t0))

# direct check of reversal on all families
rb = 0
for r in range(1, RMAX + 1):
    for (s, K) in T:
        sb = {'n': 'n', 'i': 'o', 'o': 'i'}[s]
        Kb = tuple(sorted((h, bar[p]) for (h, p) in K))
        for phi in 'IO':
            if V(s, K, phi, r) != V(sb, Kb, bar[phi], r):
                rb += 1
print('reversal symmetry violations:', rb)

# W(kappa0)
print('W_IN(kappa0)=Gamma(i;{2F,3F}) =', Gamma('i', ((2, F), (3, F))), ' W_OUT =', Gamma('o', ((2, F), (3, F))))
# universal families
ub = 0
for r in range(1, RMAX + 1):
    for phi in 'IO':
        ub += V('n', [(1, 'I'), (1, 'O')], phi, r) != r
        ub += V('i', [(1, 'O')], phi, r) != r ^ 1
        ub += V('o', [(1, 'I')], phi, r) != r ^ 1
print('universal family violations:', ub)

# g(S(2,3,z))
g = [None] + [spider(2, 3, z) for z in range(1, ZMAX + 1)]
print('g(S(2,3,z)) z=1..30:', g[1:31])
badz = [z for z in range(1, ZMAX + 1) if g[z] != z % 2]
print('z<=%d with g != z mod 2:' % ZMAX, badz)
# Gamma(i;{2*,3*}) as asked
print('Gamma(i;{2*,3*}) =', Gamma('i', ((2, 'F'), (3, 'F'))))
# free families used in Lemma lem:lowerbounds
lb = {('i', ((3, F),)): 2, ('n', ((1, I), (3, F))): 2, ('i', ((2, F),)): 4, ('n', ((1, I), (2, F))): 2,
      ('n', ((2, F), (2, I))): 2}
for (s, K), b in lb.items():
    for (ss, KK) in [(s, K), ({'n': 'n', 'i': 'o'}[s], tuple(sorted((h, bar[p]) for h, p in K)))]:
        vals = [V(ss, KK, 'F', z) for z in range(14, ZMAX + 1)]
        print('lowerbound', ss, KK, '>=', b, ':', min(vals) >= b, ' min over z in [14,%d] =' % ZMAX, min(vals),
              ' values at z=1..20:', [V(ss, KK, 'F', z) for z in range(1, 21)])
print('memo size', len(MEMO))
