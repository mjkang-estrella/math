# Coefficientwise positivity test of Hankel minors of (P_n(x+s)) via Kronecker substitution:
# integer Bareiss determinant of the matrix evaluated at X = 2^b, decoded in balanced base X.
import json, sys, math, itertools, pathlib
def shift(p,s):
    # coefficients of p(x+s)
    n=len(p); out=[0]*n
    for i,c in enumerate(p):
        if c:
            for j in range(i+1): out[j]+=c*math.comb(i,j)*s**(i-j)
    return out
def ev(p,X):
    v=0
    for c in reversed(p): v=v*X+c
    return v
def det(M):
    M=[r[:] for r in M]; n=len(M); sign=1; prev=1
    for k in range(n-1):
        if M[k][k]==0:
            for r in range(k+1,n):
                if M[r][k]!=0: M[k],M[r]=M[r],M[k]; sign=-sign; break
            else: return 0
        for i in range(k+1,n):
            for j in range(k+1,n):
                M[i][j]=(M[i][j]*M[k][k]-M[i][k]*M[k][j])//prev
        prev=M[k][k]
    return sign*M[n-1][n-1]
def decode(v,X):
    out=[]
    while v:
        r=v%X
        if r>X//2: r-=X
        out.append(r); v=(v-r)//X
    return out or [0]
def minor_poly(a,rows,cols,X):
    return decode(det([[a[i+j] for j in cols] for i in rows]),X)
if __name__=='__main__':
    data=json.load(open(sys.argv[1])); cls=sys.argv[2]; s=int(sys.argv[3]); mode=sys.argv[4]
    Nmax=int(sys.argv[6]) if len(sys.argv)>6 else len(data[cls])-1
    P=data[cls][:Nmax+1]; A=[shift(p,s) for p in P]; N=len(A)-1
    l1=[sum(abs(c) for c in p) for p in A]
    def X_for(rows,cols):
        k=len(rows); B=math.factorial(k)
        for i in rows: B*=max(l1[i+j] for j in cols)
        return 1<<(B.bit_length()+3)
    if mode=='contig':
        bad=[]; cnt=0
        for k in range(1,N//2+2):
            for m in range(0,N-2*k+3):
                rows=range(k); cols=range(m,m+k)
                if max(rows)+max(cols)>N: continue
                X=X_for(rows,cols); a=[ev(p,X) for p in A]
                q=minor_poly(a,list(rows),list(cols),X); cnt+=1
                neg=[i for i,c in enumerate(q) if c<0]
                if neg: bad.append((k,m,neg[:5],len(q)))
            print('k',k,'done; negatives so far',len(bad),bad[-3:],flush=True)
        print('class',cls,'shift',s,'N',N,'contiguous minors tested',cnt,'negative',len(bad)); print(bad[:20])
    elif mode=='all':
        K=int(sys.argv[5]); cnt=0; bad=[]
        kmin=int(sys.argv[7]) if len(sys.argv)>7 else 1
        kmax=int(sys.argv[8]) if len(sys.argv)>8 else K
        B=math.factorial(K)*max(l1[:2*K-1])**K
        X=1<<(B.bit_length()+3)
        a=[ev(p,X) for p in A[:2*K-1]]
        for k in range(kmin,kmax+1):
            for rows in itertools.combinations(range(K),k):
                for cols in itertools.combinations(range(K),k):
                    if rows>cols: continue  # Hankel symmetry: minor(rows,cols)=minor(cols,rows)
                    q=minor_poly(a,rows,cols,X); cnt+=1
                    if any(c<0 for c in q): bad.append((rows,cols))
            print('k',k,'tested so far',cnt,'negative',len(bad),bad[:3],flush=True)
        print('class',cls,'shift',s,'all minors of leading',K,'x',K,'sizes',kmin,kmax,'tested',cnt,'negative',len(bad)); print(bad[:10])
    elif mode=='small':
        # all minors of size <= kmax of the leading K x K Hankel matrix, with a per-minor Kronecker base
        K=int(sys.argv[5]); kmax=int(sys.argv[7]); cnt=0; bad=[]; import time; t0=time.time()
        for k in range(1,kmax+1):
            for rows in itertools.combinations(range(K),k):
                for cols in itertools.combinations(range(K),k):
                    if rows>cols: continue
                    X=X_for(rows,cols); a={}
                    idxs={i+j for i in rows for j in cols}
                    for t in idxs: a[t]=ev(A[t],X)
                    q=decode(det([[a[i+j] for j in cols] for i in rows]),X); cnt+=1
                    if any(c<0 for c in q): bad.append((rows,cols))
            print('k',k,'tested so far',cnt,'negative',len(bad),bad[:3],round(time.time()-t0,1),flush=True)
        print('class',cls,'shift',s,'minors of size <=',kmax,'of leading',K,'x',K,'tested',cnt,'negative',len(bad))
