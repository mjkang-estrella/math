"""Test whether necessary multiset conditions C1 & C2 already force the conjecture.

C1(t): n_t = sum_{v<=t} m_v <= 2t                       (from alpha(H_{t+1}) >= ceil(n_t/2) <= t)
C2(t): if n_t >= t: sum_{v<=t} v*m_v >= n_t + (n_t-t)*(t-1)
       (from required matching nu >= n_t - t at level k=t+1: matched pairs sum >= k,
        unmatched singletons >= 1; sum >= nu*k + (n_t - 2*nu) = n_t + nu*(k-2))
Enumerate all profiles m_1..m_n >= 0, sum n, C1; check C2; track min sum.
"""
import sys

def min_profiles(n, cap=5_000_000):
    best = [None]; bestprof=[None]; count=[0]
    m = [0]*(n+1)
    # DFS over m_1..m_n with C1 pruning; visit small sums first? enumerate all, track min.
    def rec(v, rem, cnt_t, mass_t):
        # cnt_t = n_{v-1}, mass_t = sum_{u<v} u*m_u
        if v > n:
            if rem == 0:
                count[0]+=1
                if count[0] > cap: raise RuntimeError("cap")
                # check C2
                nt = 0; S = 0
                for t in range(1, n+1):
                    nt += m[t]; S += t*m[t]
                    if nt >= t and S < nt + (nt-t)*(t-1):
                        return
                s = mass_t
                if best[0] is None or s < best[0]:
                    best[0] = s; bestprof[0] = m[:]
            return
        # C1: partial counts already <= 2(v-1); m_v <= 2v - cnt_t
        maxmv = min(rem, 2*v - cnt_t)
        if maxmv < 0: return
        # admissible skip-to-end option handled at v==n via rem==0; also allow finishing early
        for x in range(0, maxmv+1):
            m[v] = x
            rec(v+1, rem-x, cnt_t+x, mass_t + v*x)
        m[v] = 0
    try:
        rec(1, n, 0, 0)
    except RuntimeError:
        pass
    return best[0], bestprof[0], count[0]

def conjecture(n):
    m4, r = divmod(n,4)
    if r==1: return 5*m4*m4+4*m4+1
    if r==3: return 5*m4*m4+9*m4+4
    return None

for n in range(3, 22):
    b, prof, cnt = min_profiles(n)
    c = conjecture(n)
    print("n=%2d  min(C1,C2)=%s  conjecture=%s  profiles=%d  prof=%s" % (n, b, c, cnt, prof if n<=13 else ""))
