# Agent E2: independent enumeration of the configuration space for B's targets t in {12,14,15,16,18,21,24,32,42,81}.
# Adapted from E's e_enum.py (which was written without reading any GLM pipeline).  Stdlib only.
import itertools, collections
TARGETS = (12, 14, 15, 16, 18, 21, 24, 32, 42, 81)
def digs(T): return (2, 3, 4, 6, 7, 8, 9) + ((5,) if T % 5 == 0 else ())   # 0 kills the product; 5 only if 5 | T
def v2(x):
    x = abs(x); c = 0
    while x % 2 == 0: x //= 2; c += 1
    return c
def multisets(T):
    out = []
    D = digs(T)
    def rec(rem, mind, cur):
        if rem == 1: out.append(tuple(cur)); return
        for d in D:
            if d >= mind and rem % d == 0:
                cur.append(d); rec(rem // d, d, cur); cur.pop()
    rec(T, 2, [])
    return out
def closure(gens, mod):
    seen = {1 % mod}; st = [1 % mod]
    while st:
        x = st.pop()
        for g in gens:
            y = x * g % mod
            if y not in seen: seen.add(y); st.append(y)
    return seen
R40 = closure((2, 3, 7), 40); R1000 = closure((2, 3, 7), 1000)       # n = 2^i 3^j 7^k, 5-free
R40o = closure((3, 7), 40); R1000o = closure((3, 7), 1000)            # n odd, 5-free (all digits odd)
R200o = closure((3, 7), 200)                                          # m = n/5 for the five-mode
def dead_flags(T, M, S_low):
    """returns (weak_dead, strong_dead).  n mod 1000 = 111 + S_low  (L >= 3, no carries)."""
    r1000 = (111 + S_low) % 1000
    if 5 in M:
        # digits {1,3,5}: n odd.  Either last digit != 5  => 5 !| n, n in <3,7>;  or last digit 5 => n = 5 m, v5(n)=1, m in <3,7>.
        if r1000 % 10 == 5:
            m200 = (r1000 // 5)       # n mod 1000 = 5 m mod 1000 => m mod 200
            strong = (m200 % 200) not in R200o
            # weak = only the mod-5 condition (v5(n)=1): n mod 25 != 0
            weak = (r1000 % 25 == 0)
            return weak, strong
        else:
            return ((r1000 % 40) not in R40o), (r1000 not in R1000o)
    weak = (r1000 % 40) not in R40
    strong = (r1000 not in R1000) or (all(d % 2 == 1 for d in M) and r1000 not in R1000o)
    return weak, strong
def configs(T):
    res = {}
    for M in multisets(T):
        for pat in itertools.product((1,) + tuple(sorted(set(M))), repeat=3):
            used = collections.Counter(d for d in pat if d != 1)
            cm = collections.Counter(M)
            if any(used[d] > cm[d] for d in used): continue
            far = list((cm - used).elements())
            S_low = sum((d - 1) * 10 ** p for p, d in enumerate(pat))
            farA = tuple(sorted(9 * (c - 1) for c in far))
            key = (S_low, farA)
            assert key not in res, ("duplicate config", key)
            w, s = dead_flags(T, M, S_low)
            res[key] = dict(multiset=M, low=pat, far=tuple(sorted(far)), dead_weak=w, dead_strong=s)
    return res
def perms(F): return sorted(set(itertools.permutations(F)))
def slices(K, F, used=()):
    """cover of {far digits F (A-values) at distinct positions >= 3, L > all}: (K', free F, qmin, fixed positions)."""
    out = {}
    def rec(K, F, used):
        t0 = v2(K); qmin = max(3, t0 + 1)
        out[(K, tuple(sorted(F)), used)] = (K, tuple(sorted(F)), qmin, tuple(sorted(used)))
        for v in sorted(set(F)):
            for q in range(3, qmin):
                if q in used: continue
                F2 = list(F); F2.remove(v)
                rec(K + v * 10 ** q, F2, used + (q,))
    rec(K, list(F), tuple(used))
    return list(out.values())
if __name__ == '__main__':
    for T in TARGETS:
        cf = configs(T); ms = multisets(T)
        nw = sum(1 for v in cf.values() if v['dead_weak']); ns = sum(1 for v in cf.values() if v['dead_strong'])
        byk = collections.Counter((len(k[1]), v['dead_weak']) for k, v in cf.items())
        print(T, 'multisets', ms, 'configs', len(cf), 'dead_weak', nw, 'dead_strong', ns, 'by(#far,dead):', sorted(byk.items()))
    print('R40', sorted(R40)); print('R40o', sorted(R40o))
