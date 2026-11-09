"""Exact decision search v2 for the rho_R(P_n) sequence problem (arXiv:1201.5340).

Reduction (primary source, Thm 2.1 + Lemma 2.2): G ->_R P_n iff for every
S subseteq [n]:  |S| <= max( max_{i in S} a_i , max_{i,i+1 in S}(a_i+a_{i+1}) ).
Equivalently, for every k, the largest S with all a_i <= k-1 and no adjacent
pair (i,i+1) in S with sum >= k has size <= k-1 (exact path DP; Lemma 6.1).
Exact over ALL proper vertex colorings.

decide n T: complete DFS. Prunes:
  (a) exact bad-set DP in prefix (sound: a bad set in a prefix is a bad set);
  (b) tight suffix bound: minimal possible sum of the remaining n-i values
      subject to the exact global necessary condition n_t <= 2t for all t
      (n_t = #{i: a_i <= t}, implied by alpha(H_{t+1}) >= ceil(n_t/2) <= t),
      computed greedily with suffix-min caps on prefix counts;
  (c) a_i <= n WLOG (capping preserves feasibility and reduces sum);
  (d) reversal symmetry WLOG a_1 <= a_n;
  (e) memoized infeasible states (feasibility monotone in remaining budget).
"""
import sys

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
    """Minimal sum of L values x (1<=x) such that for all t: cnt[t] + #{x<=t} <= 2t.
    Returns None if impossible."""
    cap = [0]*(n+1)
    for t in range(1,n+1): cap[t] = 2*t - cnt[t]
    if min(cap[1:]) < 0: return None
    suf = [0]*(n+2); suf[n+1] = 10**9
    for t in range(n,0,-1): suf[t] = min(cap[t], suf[t+1])
    total=0; placed=0; rprev=0
    for v in range(1,n+1):
        room = suf[v] - rprev
        if room < 0: return None
        take = min(L-placed, room)
        total += take*v; placed += take; rprev += take
        if placed==L: break
    if placed < L: return None
    return total

def decide(n, T):
    found=[None]; nodes=[0]
    a=[0]*(n+1)
    Ks=list(range(2,n+1))
    memo={}

    def dfs(i, sumv, dp0, dp1, cnt, first):
        nodes[0]+=1
        rem = n-i
        if sumv + G[rem] > T: return False
        ms = min_suffix_sum(cnt, rem, n)
        if ms is None or sumv + ms > T: return False
        if i==n:
            found[0]=a[1:n+1][:]; return True
        key=(i, a[i], tuple(dp0[2:]), tuple(dp1[2:]), tuple(cnt))
        b=memo.get(key)
        if b is not None and b >= T-sumv: return False
        budget = T - sumv - G[rem-1]
        if budget > n: budget = n
        ai=a[i]
        res=False
        for v in range(1,budget+1):
            ok=True
            ndp0=[0]*(n+1); ndp1=[0]*(n+1)
            for k in Ks:
                km1=k-1; pd0=dp0[k]; pd1=dp1[k]
                d1=-1
                if v<=km1:
                    if pd0>=0: d1=pd0+1
                    if pd1>=0 and ai+v<=km1 and pd1+1>d1: d1=pd1+1
                d0 = pd0 if pd0>pd1 else pd1
                if (d0 if d0>d1 else d1)>=k: ok=False; break
                ndp0[k]=d0; ndp1[k]=d1
            if not ok: continue
            for t in range(v,n+1): cnt[t]+=1
            a[i+1]=v
            if dfs(i+1, sumv+v, ndp0, ndp1, cnt, first):
                res=True
            for t in range(v,n+1): cnt[t]-=1
            if res: break
        if not res:
            if len(memo) > 300000: memo.clear()
            if b is None or T-sumv > b: memo[key]=T-sumv
        return res

    dp0=[0]*(n+1); dp1=[-1]*(n+1)
    cnt=[0]*(n+1)
    ok=dfs(0,0,dp0,dp1,cnt,1)
    sys.stderr.write("nodes=%d memo=%d\n"%(nodes[0],len(memo)))
    return found[0] if ok else None

def main():
    cmd=sys.argv[1]
    if cmd=="verify":
        n=int(sys.argv[2]); a=[int(x) for x in sys.argv[3:3+n]]
        print("n=%d sum=%d %s"%(n,sum(a),"FEASIBLE" if check_seq(a) else "INFEASIBLE"))
    elif cmd=="construction":
        n=int(sys.argv[2]); c=construction(n)
        print("n=%d seq=%s sum=%d %s"%(n,c,sum(c),"FEASIBLE" if check_seq(c) else "INFEASIBLE"))
    elif cmd=="decide":
        n=int(sys.argv[2]); T=int(sys.argv[3])
        r=decide(n,T)
        print("n=%d T=%d %s"%(n,T,("FOUND "+str(r)) if r else "INFEASIBLE"))

main()
