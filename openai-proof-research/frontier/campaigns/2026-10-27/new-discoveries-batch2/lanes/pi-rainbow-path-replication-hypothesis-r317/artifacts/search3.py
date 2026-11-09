"""Exact minimum solver v3: F(state) = min completion sum, memoized exactly.

State after prefix i: (last value a_i, dp0[k], dp1[k] for k=2..n, cnt[t] for t=1..n).
F is T-independent, so each reachable state is solved exactly once.
Prunes: prefix bad-set DP (exact), count cap n_t <= 2t (necessary), a_v <= n WLOG,
C1/C2-based suffix bound, base bound g(L).  Answers min sum over ALL feasible
sequences = rho_R(P_n) under the primary-source reduction.
"""
import sys
sys.setrecursionlimit(100000)

def make_g(limit=64):
    g=[0]*(limit+1); s=0
    for L in range(1,limit+1):
        s += (L+1)//2; g[L]=s
    return g
G=make_g()

def check_seq(a):
    n=len(a)
    for k in range(2,n+1):
        d0,d1,prev = 0,-1,0
        km1=k-1
        for v in a:
            nd0 = d0 if d0>d1 else d1
            nd1 = -1
            if v<=km1:
                if d0>=0: nd1=d0+1
                if d1>=0 and prev+v<=km1 and d1+1>nd1: nd1=d1+1
            d0,d1=nd0,nd1; prev=v
        if (d0 if d0>d1 else d1)>=k: return False
    return True

def construction(n):
    m4,r=divmod(n,4); S1=[];T1=[];S2=[];T2=[]
    if r==0:
        S1=list(range(1,m4+1)); T1=[n//2]*m4; S2=list(range(m4+1,n//2+1)); T2=[n//4]*(m4-1)+[n//2]
    elif r==1:
        m=(n-1)//4; S1=list(range(1,m+2)); T1=[m+1]*m; S2=list(range(m+2,2*m+2)); T2=[2*m+1]*(m-1)+[m+1]
    elif r==2:
        m=(n-2)//4; S1=list(range(1,m+2)); T1=[n//2]*(m+1); S2=list(range(m+2,n//2+1)); T2=[m+1]*m
    else:
        m=(n-3)//4; S1=list(range(1,m+2)); T1=[m+1]*(m+1); S2=list(range(m+2,2*m+3)); T2=[2*m+2]*m
    out=[]; i=0
    while len(out)<n:
        for L in (S1,T1,S2,T2):
            if i<len(L): out.append(L[i])
        i+=1
    return out[:n]

def min_suffix_sum(cnt, L, n):
    cap=[0]*(n+1)
    for t in range(1,n+1): cap[t]=2*t-cnt[t]
    if min(cap[1:])<0: return None
    suf=[0]*(n+2); suf[n+1]=10**9
    for t in range(n,0,-1): suf[t]=min(cap[t],suf[t+1])
    total=0; placed=0; rprev=0
    for v in range(1,n+1):
        room=suf[v]-rprev
        if room<0: return None
        take=min(L-placed,room)
        total+=take*v; placed+=take; rprev+=take
        if placed==L: break
    return total if placed==L else None

def solve(n, state_cap=8_000_000):
    Ks=list(range(2,n+1))
    memo={}
    nodes=[0]
    INF=float('inf')

    def dfs(i, last, dp0, dp1, cnt):
        """min sum of positions i+1..n given prefix state; INF if impossible."""
        nodes[0]+=1
        if i==n:
            return 0
        key=(i, last, tuple(dp0[2:]), tuple(dp1[2:]), tuple(cnt))
        r=memo.get(key)
        if r is not None: return r
        if len(memo)>state_cap: raise MemoryError("state cap")
        L=n-i
        ms=min_suffix_sum(cnt,L,n)
        if ms is None:
            memo[key]=INF; return INF
        best=INF
        hi = n  # a_v <= n WLOG
        a_i = last
        for v in range(1,hi+1):
            ok=True
            ndp0=[0]*(n+1); ndp1=[0]*(n+1)
            for k in Ks:
                km1=k-1; pd0=dp0[k]; pd1=dp1[k]
                d1=-1
                if v<=km1:
                    if pd0>=0: d1=pd0+1
                    if pd1>=0 and a_i+v<=km1 and pd1+1>d1: d1=pd1+1
                d0=pd0 if pd0>pd1 else pd1
                if (d0 if d0>d1 else d1)>=k: ok=False; break
                ndp0[k]=d0; ndp1[k]=d1
            if not ok: continue
            for t in range(v,n+1): cnt[t]+=1
            if min_suffix_sum(cnt, L-1, n) is not None:
                sub=dfs(i+1, v, ndp0, ndp1, cnt)
                if sub is not INF:
                    s=v+sub
                    if s<best: best=s
            for t in range(v,n+1): cnt[t]-=1
        memo[key]=best
        return best

    dp0=[0]*(n+1); dp1=[-1]*(n+1); cnt=[0]*(n+1)
    # position 1: last=0 sentinel
    val=dfs(0,0,dp0,dp1,cnt)
    sys.stderr.write("nodes=%d states=%d\n"%(nodes[0],len(memo)))
    return val

def main():
    cmd=sys.argv[1]
    if cmd=="verify":
        n=int(sys.argv[2]); a=[int(x) for x in sys.argv[3:3+n]]
        print("n=%d sum=%d %s"%(n,sum(a),"FEASIBLE" if check_seq(a) else "INFEASIBLE"))
    elif cmd=="construction":
        n=int(sys.argv[2]); c=construction(n)
        print("n=%d seq=%s sum=%d %s"%(n,c,sum(c),"FEASIBLE" if check_seq(c) else "INFEASIBLE"))
    elif cmd=="minsum":
        n=int(sys.argv[2])
        try:
            v=solve(n)
            print("n=%d min_sum=%s"%(n,v))
        except MemoryError:
            print("n=%d STATE_CAP_EXCEEDED"%n)

main()
