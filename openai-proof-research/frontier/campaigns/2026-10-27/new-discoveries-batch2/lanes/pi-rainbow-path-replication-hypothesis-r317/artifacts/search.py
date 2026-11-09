"""Exact decision search for the rho_R(P_n) sequence problem (arXiv:1201.5340).

Reduction (primary source): G ->_R P_n  iff  for every S subseteq [n]:
    |S| <= max( max_{i in S} a_i , max_{i,i+1 in S} (a_i + a_{i+1}) )
(a_i = replication-clique sizes; Thm 2.1 + Lemma 2.2 (perfectness)).  Equivalently,
for every k the largest S with all a_i <= k-1 and no adjacent pair (i,i+1) in S
with a_i + a_{i+1} >= k has size <= k-1  (exact DP over the path; Lemma 6.1).
This is an exact test over ALL proper vertex colorings, not a bounded sweep.

Commands:
  verify n a1 ... an     - check one sequence
  construction n         - source Thm 3.1 construction + feasibility
  decide n T             - exhaustive DFS: exists feasible sequence with sum <= T?
"""
import sys

def make_g(limit=48):
    g = [0]*(limit+1)
    s = 0
    for L in range(1, limit+1):
        s += (L+1)//2
        g[L] = s
    return g
G = make_g()

def check_seq(a):
    n = len(a)
    for k in range(2, n+1):
        d0, d1 = 0, -1
        prev = 0
        km1 = k-1
        for i in range(n):
            v = a[i]
            nd0 = d0 if d0 > d1 else d1
            nd1 = -1
            if v <= km1:
                if d0 >= 0: nd1 = d0 + 1
                if d1 >= 0 and prev + v <= km1 and d1+1 > nd1:
                    nd1 = d1 + 1
            d0, d1 = nd0, nd1
            prev = v
        if (d0 if d0 > d1 else d1) >= k:
            return False
    return True

def construction(n):
    m4, r = divmod(n, 4)
    S1=[];T1=[];S2=[];T2=[]
    if r==0:
        S1=list(range(1,m4+1)); T1=[n//2]*m4; S2=list(range(m4+1,n//2+1))
        T2=[n//4]*(m4-1)+[n//2]
    elif r==1:
        m=(n-1)//4
        S1=list(range(1,m+2)); T1=[m+1]*m; S2=list(range(m+2,2*m+2)); T2=[2*m+1]*(m-1)+[m+1]
    elif r==2:
        m=(n-2)//4
        S1=list(range(1,m+2)); T1=[n//2]*(m+1); S2=list(range(m+2,n//2+1)); T2=[m+1]*m
    else:
        m=(n-3)//4
        S1=list(range(1,m+2)); T1=[m+1]*(m+1); S2=list(range(m+2,2*m+3)); T2=[2*m+2]*m
    out=[]; i=0
    while len(out)<n:
        for L in (S1,T1,S2,T2):
            if i < len(L): out.append(L[i])
        i += 1
        if i > max(len(S1),len(T1),len(S2),len(T2))+2: break
    return out[:n]

def decide(n, T):
    """DFS; returns feasible sequence with sum<=T or None. Complete:
    prunes are (a) suffix base bound sum_{j<=L} ceil(j/2), (b) exact bad-set DP
    in prefix, (c) count n_t <= 2t, (d) a_i <= n WLOG, (e) reversal WLOG a_1<=a_n."""
    g = G
    found = [None]
    a = [0]*(n+1)
    # dp[k] = (d0,d1) after current prefix; store as two lists indexed by k
    nodes = [0]
    K = range(2, n+1)
    Ks = list(K)

    def dfs(i, sumv, dp0, dp1, cnt, first):
        # cnt[t] = number of assigned values <= t
        nodes[0] += 1
        if sumv + g[n-i] > T:
            return False
        if i == n:
            found[0] = a[1:n+1][:]
            return True
        budget = T - sumv - g[n-i-1]
        if budget > n: budget = n
        ai = a[i]
        ndp0 = [0]*(n+1); ndp1 = [0]*(n+1)
        for v in range(1, budget+1):
            if i+1 == n and v < first:
                continue
            ok = True
            for k in Ks:
                km1 = k-1
                pd0 = dp0[k]; pd1 = dp1[k]
                d1 = -1
                if v <= km1:
                    if pd0 >= 0: d1 = pd0 + 1
                    if pd1 >= 0 and ai + v <= km1 and pd1+1 > d1:
                        d1 = pd1 + 1
                d0 = pd0 if pd0 > pd1 else pd1
                if (d0 if d0 > d1 else d1) >= k:
                    ok = False
                    break
                ndp0[k] = d0; ndp1[k] = d1
            if not ok:
                continue
            # count constraint n_t <= 2t
            okc = True
            for t in range(v, n+1):
                cnt[t] += 1
            for t in range(1, n+1):
                if cnt[t] > 2*t:
                    okc = False
                    break
            if okc:
                a[i+1] = v
                if dfs(i+1, sumv+v, ndp0, ndp1, cnt, first):
                    return True
            for t in range(v, n+1):
                cnt[t] -= 1
        return False

    dp0 = [0]*(n+1); dp1 = [-1]*(n+1)
    cnt = [0]*(n+1)
    # WLOG a_1 <= a_n handled inside; also fix a_1 range: a_1 >= 1
    ok = dfs(0, 0, dp0, dp1, cnt, 1)
    sys.stderr.write("nodes=%d\n" % nodes[0])
    return found[0] if ok else None

def main():
    cmd = sys.argv[1]
    if cmd == "verify":
        n = int(sys.argv[2]); a = [int(x) for x in sys.argv[3:3+n]]
        print("n=%d sum=%d %s" % (n, sum(a), "FEASIBLE" if check_seq(a) else "INFEASIBLE"))
    elif cmd == "construction":
        n = int(sys.argv[2]); c = construction(n)
        print("n=%d seq=%s sum=%d %s" % (n, c, sum(c), "FEASIBLE" if check_seq(c) else "INFEASIBLE"))
    elif cmd == "decide":
        n = int(sys.argv[2]); T = int(sys.argv[3])
        r = decide(n, T)
        print("n=%d T=%d %s" % (n, T, ("FOUND " + str(r)) if r else "INFEASIBLE"))

main()
