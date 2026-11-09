"""Exact distributions for Burstein-Jones Conjecture 5.3 (MathDB 345654).

a_{n,k} = #{pi in D^1_{2n}(2143) : (2-31)pi = k}
b_{n,k} = #{pi in D^1_{2n}(3421) : (13-2)pi = k}

Dumont-1 (source Def.): each even entry is immediately followed by a smaller
entry; each odd entry is immediately followed by a larger entry or ends pi.

usage: dumont.py N which(a|b|both) [first_entry ...] [--brute]
Writes nothing; prints JSON {which: {k: count}} to stdout.
--brute uses naive pattern counting (cross-check, small N only).
"""
import sys, json
from itertools import combinations

def run(N, which, firsts):
    L = 2 * N
    full = (1 << (L + 1)) - 2  # bits 1..L
    dist = {}
    if which == 'a':
        # state: last, used, forb(2143), invmin, stat, seq
        def rec(seq, used, forb, invmin, stat):
            if used == full:
                if seq[-1] & 1:
                    dist[stat] = dist.get(stat, 0) + 1
                return
            y = seq[-1]
            if y & 1:
                cand = range(y + 1, L + 1)
            else:
                cand = range(1, y)
            for x in cand:
                b = 1 << x
                if used & b or forb & b:
                    continue
                # new forbidden interval for future elements: (invmin, x) with x as '4'
                nf = forb
                if invmin < x:
                    lo = invmin + 1
                    nf |= ((1 << x) - 1) & ~((1 << lo) - 1)
                # inversion-min update: earlier elements > x now have a smaller later element
                ni = invmin
                for v in seq:
                    if v > x and v < ni:
                        ni = v
                # (2-31) count: adjacent descent y->x, earlier elements (before y) in (x, y)
                ns = stat
                if y > x:
                    for v in seq[:-1]:
                        if x < v < y:
                            ns += 1
                seq.append(x)
                rec(seq, used | b, nf, ni, ns)
                seq.pop()
        for f in firsts:
            rec([f], 1 << f, 0, L + 1, 0)
    else:
        # 3421 avoidance: T = max '2'-value of a 342 occurrence; forbid x < T.
        # A = max value having a larger element after it.
        def rec(seq, used, T, A, asc, stat):
            if used == full:
                if seq[-1] & 1:
                    dist[stat] = dist.get(stat, 0) + 1
                return
            y = seq[-1]
            if y & 1:
                cand = range(y + 1, L + 1)
            else:
                cand = range(1, y)
            for x in cand:
                b = 1 << x
                if used & b or x < T:
                    continue
                nT = T
                if x < A and x > nT:
                    nT = x
                nA = A
                for v in seq:
                    if v < x and v > nA:
                        nA = v
                # (13-2): x as '2' after adjacent ascent (p,q) with p < x < q
                ns = stat
                for (p, q) in asc:
                    if p < x < q:
                        ns += 1
                nasc = asc + [(y, x)] if y < x else asc
                seq.append(x)
                rec(seq, used | b, nT, nA, nasc, ns)
                seq.pop()
        for f in firsts:
            rec([f], 1 << f, 0, 0, [], 0)
    return dist

def dumont1(L):
    from itertools import permutations
    for p in permutations(range(1, L + 1)):
        ok = p[-1] & 1
        for i in range(L - 1):
            if p[i] & 1:
                if not p[i + 1] > p[i]: ok = False; break
            else:
                if not p[i + 1] < p[i]: ok = False; break
        if ok:
            yield p

def contains(p, pat):
    k = len(pat)
    for idx in combinations(range(len(p)), k):
        vals = [p[i] for i in idx]
        order = sorted(range(k), key=lambda t: vals[t])
        rank = [0] * k
        for r, t in enumerate(order):
            rank[t] = r + 1
        if tuple(rank) == pat:
            return True
    return False

def brute(N):
    L = 2 * N
    da, db = {}, {}
    for p in dumont1(L):
        if not contains(p, (2, 1, 4, 3)):
            s = sum(1 for i in range(L) for j in range(i + 1, L - 1) if p[j + 1] < p[i] < p[j])
            da[s] = da.get(s, 0) + 1
        if not contains(p, (3, 4, 2, 1)):
            s = sum(1 for i in range(L - 1) for k in range(i + 2, L) if p[i] < p[k] < p[i + 1])
            db[s] = db.get(s, 0) + 1
    return da, db

if __name__ == '__main__':
    args = [x for x in sys.argv[1:] if not x.startswith('--')]
    N = int(args[0]); which = args[1]
    L = 2 * N
    firsts = [int(x) for x in args[2:]] or list(range(1, L + 1))
    if '--brute' in sys.argv:
        da, db = brute(N)
        print(json.dumps({'N': N, 'brute_a': dict(sorted(da.items())), 'brute_b': dict(sorted(db.items()))}))
    else:
        out = {'N': N, 'firsts': firsts}
        for w in (['a', 'b'] if which == 'both' else [which]):
            out[w] = dict(sorted(run(N, w, firsts).items()))
        print(json.dumps(out))
