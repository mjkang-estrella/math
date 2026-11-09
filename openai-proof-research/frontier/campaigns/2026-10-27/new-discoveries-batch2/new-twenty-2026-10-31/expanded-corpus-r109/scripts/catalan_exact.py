# Exact det(CG_n) by Bareiss (diagnostic exploration for MathDB 338260).
import sys
N=int(sys.argv[1])
W=N+3; T=[[0]*W for _ in range(W)]
T[0][0]=1
for m in range(W-1):
    for j in range(1,W-1):
        T[m][j]=(T[m][j-1]+(T[m-1][j+1] if m>0 else 0))&1
def A(n):
    M=[[0]*n for _ in range(n)]
    for i in range(1,n+1):
        for j in range(1,i):
            v=T[i-1-j][j]; M[i-1][j-1]=v; M[j-1][i-1]=v
    return M
def det(M):
    n=len(M); M=[r[:] for r in M]; sign=1; prev=1
    for k in range(n-1):
        if M[k][k]==0:
            for i in range(k+1,n):
                if M[i][k]: M[k],M[i]=M[i],M[k]; sign=-sign; break
            else: return 0
        for i in range(k+1,n):
            for j in range(k+1,n):
                M[i][j]=(M[i][j]*M[k][k]-M[i][k]*M[k][j])//prev
        prev=M[k][k]
    return sign*M[n-1][n-1]
for n in range(1,N+1,2):
    d=det(A(n)); 
    f=[];x=abs(d)
    for p in [2,3,5,7]:
        e=0
        while x and x%p==0: x//=p;e+=1
        f.append(e)
    print(n,d,'v2,v3,v5,v7=',f,'rest',x)
