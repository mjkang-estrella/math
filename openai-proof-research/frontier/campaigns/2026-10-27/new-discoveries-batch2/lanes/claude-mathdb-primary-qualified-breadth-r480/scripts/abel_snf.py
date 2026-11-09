# Independent check for MathDB 339564: Smith normal form over Z of the n x n relation matrix of
# Gamma_n(1,n/2-1) = <x_i | x_i x_{i+1} x_{i+n/2-1}>, row i = e_i + e_{i+1} + e_{i+n/2-1}.
# d(G^ab) = number of invariant factors != 1 (group finite here). Also compare |G^ab| with
# printed Theorem 4.2: 3(L_m - 1 - (-1)^m) and with 3(L_m + 1 + (-1)^m).
import sys,json
def snf_diag(M):
    A=[r[:] for r in M]; n=len(A); m=len(A[0]); diag=[]
    r=0
    for c in range(m):
        if r>=n: break
        while True:
            piv=None
            for i in range(r,n):
                for j in range(c,m):
                    if A[i][j] and (piv is None or abs(A[i][j])<abs(A[piv[0]][piv[1]])): piv=(i,j)
            if piv is None: return diag+[0]*(min(n,m)-len(diag))
            i,j=piv; A[r],A[i]=A[i],A[r]
            for row in A: row[c],row[j]=row[j],row[c]
            p=A[r][c]; done=True
            for i in range(r+1,n):
                q=A[i][c]//p
                if q:
                    A[i]=[a-q*b for a,b in zip(A[i],A[r])]
                if A[i][c]: done=False
            for j in range(c+1,m):
                q=A[r][j]//p
                if q:
                    for row in A: row[j]-=q*row[c]
                if A[r][j]: done=False
            if done:
                # ensure divisibility
                bad=None
                for i in range(r+1,n):
                    for j in range(c+1,m):
                        if A[i][j]%p: bad=i;break
                    if bad is not None: break
                if bad is None:
                    diag.append(abs(p)); r+=1; break
                A[r]=[a+b for a,b in zip(A[r],A[bad])]
    return diag
def lucas(k):
    a,b=2,1
    for _ in range(k): a,b=b,a+b
    return a
lo,hi=int(sys.argv[1]),int(sys.argv[2]); out=[]
for n in range(lo,hi+1):
    if n%2 or n%3==0 or n<8: continue
    m=n//2; M=[[0]*n for _ in range(n)]
    for i in range(n):
        for s in (0,1,m-1): M[i][(i+s)%n]+=1
    D=snf_diag(M); nonunit=[x for x in D if x!=1]; order=1
    for x in D: order*=x
    v=n%16; pred={2:1,4:2,16:0,8:3}
    pred = 1 if n%4==2 else (2 if n%16 in (4,12,0) else 3) if n%8 else 2
    pred = {2:1,4:2,8:3,16:2}[__import__('math').gcd(n,16)]
    rec=dict(n=n,gcd16=__import__('math').gcd(n,16),d=len(nonunit),pred=pred,ok=len(nonunit)==pred,order=order,
             thm42_printed=3*(lucas(m)-1-(-1)**m),thm42_alt=3*(lucas(m)+1+(-1)**m),invariants=nonunit)
    out.append(rec); print(json.dumps(rec),flush=True)
print('ALL_OK',all(r['ok'] for r in out),'printed_matches',sum(r['order']==r['thm42_printed'] for r in out),'alt_matches',sum(r['order']==r['thm42_alt'] for r in out),'count',len(out))
