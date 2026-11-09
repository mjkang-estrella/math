# Guess algebraic / D-finite relations for D(x)=sum d_n x^n (d_0=1) mod a prime.
import json, sys
p=(1<<61)-1
P={int(k):int(v) for k,v in json.load(open(sys.argv[1])).items()}
N=max(P)
fact=[1]
for i in range(1,N+1): fact.append(fact[-1]*i%p)
d=[1]+[P[n]*pow(fact[n],p-2,p)%p for n in range(1,N+1)]
def mul(a,b):
    c=[0]*(N+1)
    for i,x in enumerate(a):
        if x:
            for j in range(0,N+1-i): c[i+j]=(c[i+j]+x*b[j])%p
    return c
def rank_kernel(rows_fn, nunk, neq):
    # build matrix neq x nunk, gaussian elim mod p, return nullity
    M=[rows_fn(e) for e in range(neq)]
    r=0; piv=[]
    for c in range(nunk):
        k=next((i for i in range(r,neq) if M[i][c]),None)
        if k is None: continue
        M[r],M[k]=M[k],M[r]; inv=pow(M[r][c],p-2,p)
        M[r]=[x*inv%p for x in M[r]]
        for i in range(neq):
            if i!=r and M[i][c]:
                f=M[i][c]; M[i]=[(x-f*y)%p for x,y in zip(M[i],M[r])]
        r+=1
    return nunk-r
# algebraic: sum_{k<=K} sum_{j<=m} c_{kj} x^j D^k = 0
pw=[[1]+[0]*N]
for k in range(1,7): pw.append(mul(pw[-1],d))
for K in range(1,7):
    for m in range(0,12):
        nunk=(K+1)*(m+1)
        if nunk>N-5: break
        def row(e):
            return [ (pw[k][e-j] if e-j>=0 else 0) for k in range(K+1) for j in range(m+1)]
        nl=rank_kernel(row,nunk,N+1)
        if nl>0: print('algebraic candidate K',K,'deg',m,'nullity',nl,'unknowns',nunk,'eqs',N+1); break
# D-finite recurrence: sum_{i<=r} sum_{j<=m} c_{ij} n^j d_{n+i} = 0 for n>=0
for r in range(1,8):
    for m in range(0,10):
        nunk=(r+1)*(m+1); neq=N+1-r
        if nunk>neq-5: break
        def row(e):
            return [ pow(e,j,p)*d[e+i]%p for i in range(r+1) for j in range(m+1)]
        nl=rank_kernel(row,nunk,neq)
        if nl>0: print('recurrence candidate order',r,'deg',m,'nullity',nl,'unknowns',nunk,'eqs',neq); break
print('done')
