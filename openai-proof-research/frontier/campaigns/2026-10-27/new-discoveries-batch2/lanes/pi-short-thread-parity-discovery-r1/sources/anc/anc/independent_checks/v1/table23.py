"""Closed forms of Table tab:blocked23 (transcribed by the referee)."""
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
