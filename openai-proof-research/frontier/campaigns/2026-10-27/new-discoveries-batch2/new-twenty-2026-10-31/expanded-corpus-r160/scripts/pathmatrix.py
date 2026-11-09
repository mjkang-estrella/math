import sys,os
sys.path.insert(0,os.path.dirname(os.path.abspath(__file__)))
from g6 import g6decode
def local_conn(n,adj,s,t):
    # max number of internally vertex-disjoint s-t paths (edge st counts as one path)
    # vertex split: v_in=2v, v_out=2v+1, cap 1 for v not in {s,t}
    N=2*n; cap={}
    def add(a,b,c):
        cap[(a,b)]=cap.get((a,b),0)+c; cap.setdefault((b,a),0)
    INF=n+5
    for v in range(n): add(2*v,2*v+1, INF if v in (s,t) else 1)
    for u in range(n):
        for v in range(n):
            if adj[u]>>v&1: add(2*u+1,2*v,1)
    nbr={}
    for (a,b) in cap: nbr.setdefault(a,[]).append(b)
    src=2*s+1; snk=2*t; flow=0
    while True:
        par={src:None}; st=[src]
        while st and snk not in par:
            x=st.pop()
            for y in nbr.get(x,()):
                if y not in par and cap[(x,y)]>0: par[y]=x; st.append(y)
        if snk not in par: return flow
        y=snk
        while par[y] is not None:
            x=par[y]; cap[(x,y)]-=1; cap[(y,x)]+=1; y=x
        flow+=1
def path_matrix(n,adj):
    P=[[0]*n for _ in range(n)]
    for i in range(n):
        for j in range(i+1,n):
            P[i][j]=P[j][i]=local_conn(n,adj,i,j)
    return P
def charpoly(A):
    # Berkowitz, integer, returns coeffs c0..cn of det(xI-A) highest first
    n=len(A)
    C=[1,-A[0][0]]
    for r in range(1,n):
        # build Toeplitz using submatrix A[0..r][0..r]
        R=[A[r][j] for j in range(r)]; S=[A[i][r] for i in range(r)]; a=A[r][r]
        M=[row[:r] for row in A[:r]]
        Q=[1,-a]; v=S[:]
        for k in range(r):
            Q.append(-sum(R[j]*v[j] for j in range(r)))
            v=[sum(M[i][j]*v[j] for j in range(r)) for i in range(r)]
        # multiply lower-triangular Toeplitz (first col Q, size (r+2)x(r+1)) by C
        newC=[sum(Q[i-j]*C[j] for j in range(0,min(i,len(C)-1)+1) if i-j<len(Q)) for i in range(r+2)]
        C=newC
    return C
def npos(A):
    c=charpoly(A)  # det(xI-A)=sum c[i] x^(n-i)
    sg=[x for x in c if x!=0]
    return sum(1 for a,b in zip(sg,sg[1:]) if (a>0)!=(b>0))
def blocks(n,adj):
    # biconnected components via Tarjan; returns list of vertex sets (as bitmasks) incl bridges
    disc=[-1]*n; low=[0]*n; t=[0]; stack=[]; out=[]
    def dfs(u,p):
        disc[u]=low[u]=t[0]; t[0]+=1
        for v in range(n):
            if not adj[u]>>v&1 or v==p: continue
            if disc[v]==-1:
                stack.append((u,v)); dfs(v,u); low[u]=min(low[u],low[v])
                if low[v]>=disc[u]:
                    m=0
                    while True:
                        e=stack.pop(); m|=(1<<e[0])|(1<<e[1])
                        if e==(u,v): break
                    out.append(m)
            elif disc[v]<disc[u]:
                stack.append((u,v)); low[u]=min(low[u],disc[v])
    for s in range(n):
        if disc[s]==-1: dfs(s,-1)
    return out
if __name__=='__main__':
    import json
    f=sys.argv[1]; a=int(sys.argv[2]); b=int(sys.argv[3])
    from collections import Counter
    stat=Counter(); ex={}
    with open(f) as fh:
        for i,line in enumerate(fh):
            if i<a: continue
            if i>=b: break
            n,adj=g6decode(line)
            B=blocks(n,adj)
            big=[x for x in B if bin(x).count('1')>=3]; br=len(B)-len(big)
            P=path_matrix(n,adj); k=npos(P)
            key=(n,len(big),br,k)
            stat[key]+=1
            if key not in ex: ex[key]=line.strip()
    for key in sorted(stat): print('n=%d blocks2conn=%d bridges=%d npos=%d count=%d ex=%s'%(key+(stat[key],ex[key])))
