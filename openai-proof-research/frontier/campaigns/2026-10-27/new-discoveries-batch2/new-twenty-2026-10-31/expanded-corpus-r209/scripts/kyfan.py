# all free trees on n vertices (leaf extension + canonical center-rooted AHU code); Laplacian eigenvalues by Jacobi;
# check Ky Fan k-norm of LI = L - (2m/n) I against path and star for all k.
import sys,math,json,time
def canon(adj):
    n=len(adj)
    # find centers
    deg=[len(a) for a in adj]; leaves=[i for i in range(n) if deg[i]<=1]; rem=n; d=deg[:]
    removed=[False]*n
    while rem>2:
        nl=[]
        for v in leaves:
            removed[v]=True; rem-=1
            for u in adj[v]:
                if not removed[u]:
                    d[u]-=1
                    if d[u]==1: nl.append(u)
        leaves=nl
    centers=[i for i in range(n) if not removed[i]]
    def code(v,p):
        return '('+''.join(sorted(code(u,v) for u in adj[v] if u!=p))+')'
    if len(centers)==1: return code(centers[0],-1)
    a,b=centers
    ca,cb=code(a,b),code(b,a)
    return '2'+min(ca+cb,cb+ca)
def trees(N):
    level={canon([[1],[0]]):[[1],[0]]}
    yield 2,list(level.values())
    for n in range(3,N+1):
        new={}
        for adj in level.values():
            for v in range(len(adj)):
                a=[x[:] for x in adj]+[[v]]; a[v].append(n-1)
                c=canon(a)
                if c not in new: new[c]=a
        level=new
        yield n,list(level.values())
def jacobi(A):
    n=len(A); A=[r[:] for r in A]
    for sweep in range(100):
        off=sum(A[i][j]**2 for i in range(n) for j in range(i+1,n))
        if off<1e-22: break
        for p in range(n):
            for q in range(p+1,n):
                if abs(A[p][q])<1e-14: continue
                theta=(A[q][q]-A[p][p])/(2*A[p][q])
                t=(1 if theta>=0 else -1)/(abs(theta)+math.sqrt(theta*theta+1))
                c=1/math.sqrt(t*t+1); s=t*c
                for k in range(n):
                    akp,akq=A[k][p],A[k][q]
                    A[k][p]=c*akp-s*akq; A[k][q]=s*akp+c*akq
                for k in range(n):
                    apk,aqk=A[p][k],A[q][k]
                    A[p][k]=c*apk-s*aqk; A[q][k]=s*apk+c*aqk
    return sorted(A[i][i] for i in range(n))
def kyfan(adj):
    n=len(adj); L=[[0.0]*n for _ in range(n)]
    for i in range(n):
        L[i][i]=len(adj[i])
        for j in adj[i]: L[i][j]=-1.0
    ev=jacobi(L); dbar=2*(n-1)/n
    sv=sorted((abs(x-dbar) for x in ev),reverse=True)
    out=[];s=0
    for x in sv: s+=x; out.append(s)
    return out
if __name__=='__main__':
    nmin,nmax=int(sys.argv[1]),int(sys.argv[2])
    for n,ts in trees(nmax):
        if n<nmin: continue
        t0=time.time()
        P=kyfan([[1]]+[[i-1,i+1] for i in range(1,n-1)]+[[n-2]]) if n>2 else None
        S=kyfan([list(range(1,n))]+[[0] for _ in range(n-1)])
        viol=[]; tol=1e-9
        for adj in ts:
            F=kyfan(adj)
            isP=max(len(a) for a in adj)<=2; isS=max(len(a) for a in adj)==n-1
            for k in range(n):
                if not isP and F[k]<=P[k]+tol: viol.append(('low',k+1,round(F[k]-P[k],6),canon(adj)))
                if not isS and F[k]>=S[k]-tol: viol.append(('up',k+1,round(F[k]-S[k],6),canon(adj)))
        print(json.dumps({'n':n,'trees':len(ts),'secs':round(time.time()-t0,1),'nviol':len(viol),'viol_sample':viol[:12],'viol_k':sorted(set((v[0],v[1]) for v in viol))}),flush=True)
