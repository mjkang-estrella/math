# Agent E: independent enumeration of the full configuration space for targets 112, 14112, 111132.
# Written without reading pipeline.py.  Stdlib only.
import json, sys, itertools, collections
TARGETS = (112, 14112, 111132)
DIG = (2, 3, 4, 6, 7, 8, 9)          # 0 kills the product, 5 would put 5 | Pi
def v2(x):
    x = abs(x); c = 0
    while x % 2 == 0: x //= 2; c += 1
    return c

def multisets(T):
    """all multisets (sorted tuples) of digits from DIG with product exactly T"""
    out = []
    def rec(rem, mind, cur):
        if rem == 1: out.append(tuple(cur)); return
        for d in DIG:
            if d >= mind and rem % d == 0:
                cur.append(d); rec(rem // d, d, cur); cur.pop()
    rec(T, 2, [])
    return out

# reachable residues mod 40 (and mod 1000) of 2^i 3^j 7^k, by monoid closure
def closure(mod):
    seen = {1 % mod}; st = [1 % mod]
    while st:
        x = st.pop()
        for g in (2, 3, 7):
            y = x * g % mod
            if y not in seen: seen.add(y); st.append(y)
    return seen
R40, R1000 = closure(40), closure(1000)

def configs(T):
    """dict: (S_low, far A-tuple sorted) -> info.   Enumerates every (multiset, placement of non-1 digits at positions 0,1,2 or far)."""
    res = {}
    for M in multisets(T):
        # low pattern: (d0,d1,d2), each 1 or a digit; non-1 digits must form a sub-multiset of M
        for pat in itertools.product((1,) + tuple(sorted(set(M))), repeat=3):
            used = collections.Counter(d for d in pat if d != 1)
            cm = collections.Counter(M)
            if any(used[d] > cm[d] for d in used): continue
            far = list((cm - used).elements())
            S_low = sum((d - 1) * 10 ** p for p, d in enumerate(pat))
            farA = tuple(sorted(9 * (c - 1) for c in far))
            key = (S_low, farA)
            assert key not in res, ("duplicate config", key)
            res[key] = dict(multiset=M, low=pat, far=tuple(sorted(far)),
                            dead40=((111 + S_low) % 40 not in R40),
                            dead1000=((111 + S_low) % 1000 not in R1000))
    return res

def perms(F):
    return sorted(set(itertools.permutations(F)))

def slices(K, F, used=()):
    """Partition-cover of {free far digits F (A-values) at distinct positions >=3, L > all positions} for equation
       X = 10^L + K + sum A_i 10^q_i.  Returns list of (K', F_free_tuple, qmin, fixed_positions).  Every point is in >=1 piece."""
    out = {}
    def rec(K, F, used):
        assert K > 0
        t0 = v2(K); qmin = max(3, t0 + 1)
        out[(K, tuple(sorted(F)))] = (K, tuple(sorted(F)), qmin, tuple(sorted(used)))
        for v in sorted(set(F)):
            for q in range(3, qmin):
                if q in used: continue      # position already occupied by a fixed digit
                F2 = list(F); F2.remove(v)
                rec(K + v * 10 ** q, F2, used + (q,))
    rec(K, list(F), tuple(used))
    return list(out.values())

if __name__ == '__main__':
    allc = {}
    for T in TARGETS:
        cf = configs(T)
        allc[T] = cf
        ms = multisets(T)
        nd = sum(1 for v in cf.values() if v['dead40'])
        nd1000 = sum(1 for v in cf.values() if v['dead1000'])
        byk = collections.Counter((len(k[1]), v['dead40']) for k, v in cf.items())
        print(T, 'multisets', len(ms), 'configs', len(cf), 'dead40', nd, 'dead1000', nd1000)
        print('   by (#far, dead40):', sorted(byk.items()))
    print('R40', sorted(R40))
