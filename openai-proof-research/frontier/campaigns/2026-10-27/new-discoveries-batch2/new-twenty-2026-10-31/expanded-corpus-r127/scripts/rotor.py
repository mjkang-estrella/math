# Count recurrent configurations of the sinkless rotor network on the bidirected cycle C_n
# (Chan-Levine, Abelian networks IV, arXiv:1804.03322v2, Sec. 8.3, Thm 7.4 cycle test).
# Config: x in N^{Z_n}, sum x = m; rotor q(v_k) in {+1 (edge v_k->v_{k+1}), -1 (edge v_k->v_{k-1}, weight 1)}.
# Recurrent iff x>=0 and every directed cycle of the rotor digraph meets supp(x).
# Directed cycles: 2-cycles {v_k,v_{k+1}} with q(v_k)=+1,q(v_{k+1})=-1; the n-cycle when all q equal.
# Weight: sum_k k x(v_k) + #{k: q(v_k)=-1} mod n.
import sys, itertools, json
def brute(n,m):
    cnt=[0]*n
    for q in itertools.product((1,-1),repeat=n):
        for x in comps(m,n):
            if not rec(n,x,q): continue
            w=(sum(k*x[k] for k in range(n))+sum(1 for t in q if t==-1))%n
            cnt[w]+=1
    return cnt
def comps(m,n):
    if n==1: yield (m,); return
    for a in range(m+1):
        for r in comps(m-a,n-1): yield (a,)+r
def rec(n,x,q):
    if all(t==1 for t in q) or all(t==-1 for t in q):
        if sum(x)==0: return False
    for k in range(n):
        k1=(k+1)%n
        if q[k]==1 and q[k1]==-1 and x[k]==0 and x[k1]==0: return False
    return True
def dp(n,m):
    # transfer over vertices 0..n-1, state: (q0, z0 (x0==0), qprev, zprev); value: dict (chips, weight)->count stored as list of lists
    # chip generating per vertex k: x=0 -> (0,0); x=a>=1 -> (a, k*a mod n)
    from collections import defaultdict
    res=[0]*n
    for q0 in (1,-1):
        for z0 in (True,False):
            # vertex 0 contributions
            arr=[[0]*n for _ in range(m+1)]
            if z0: arr[0][(1 if q0==-1 else 0)%n]+=1
            else:
                for a in range(1,m+1): arr[a][(1 if q0==-1 else 0)%n]+=1
            states={(q0,z0,True):arr}  # third: all rotors equal to q0 so far
            for k in range(1,n):
                new={}
                for (qp,zp,alleq),A in states.items():
                    for q in (1,-1):
                        for z in (True,False):
                            if qp==1 and q==-1 and zp and z: continue
                            ae=alleq and q==q0
                            key=(q,z,ae)
                            B=new.get(key)
                            if B is None: B=[[0]*n for _ in range(m+1)]; new[key]=B
                            rw=1 if q==-1 else 0
                            if z:
                                for c in range(m+1):
                                    row=A[c]; tgt=B[c]
                                    for w in range(n):
                                        if row[w]: tgt[(w+rw)%n]+=row[w]
                            else:
                                for c in range(m+1):
                                    row=A[c]
                                    if not any(row): continue
                                    for a in range(1,m-c+1):
                                        tgt=B[c+a]; sh=(k*a+rw)%n
                                        for w in range(n):
                                            if row[w]: tgt[(w+sh)%n]+=row[w]
                states=new
            for (ql,zl,alleq),A in states.items():
                # closing pair (v_{n-1}, v_0)
                if ql==1 and q0==-1 and zl and z0: continue
                for w in range(n): res[w]+=A[m][w]
                # m>=1 so the all-equal n-cycle always meets supp(x)
    return res
if __name__=='__main__':
    mode=sys.argv[1]
    if mode=='table':
        for n in range(3,9):
            print(n, dp(n,n), flush=True)
        for n,m in [(3,3),(4,4),(5,3),(4,2),(5,5)]:
            print('brute',n,m,brute(n,m),dp(n,m),flush=True)
