# Exact operator T on Z[y], y=x/(1-x), w=(1+x)/(1-x)=1+2y.
# Sum_n c_m(2n) x^n = C^m(x) * T(1);  U_2(C^m F) = C^m T(F),  T(F)=U_2[w^m F].
# Rules: w^m y^(2e) -> y^e T_{m+e}(1+2y);  w^m y^(2e+1) -> y^e (T_{m+e+1}-T_{m+e})(1+2y)/2.
import sys, json
from functools import lru_cache
@lru_cache(None)
def cheb(k):
    if k==0: return (1,)
    if k==1: return (1,2)
    a=list(cheb(k-1)); b=cheb(k-2)
    r=[0]*(k+1)
    for i,c in enumerate(a):
        r[i]+=2*c; r[i+1]+=4*c
    for i,c in enumerate(b): r[i]-=c
    return tuple(r)
def add(a,b,s=1):
    n=max(len(a),len(b)); r=[0]*n
    for i,c in enumerate(a): r[i]+=c
    for i,c in enumerate(b): r[i]+=s*c
    while len(r)>1 and r[-1]==0: r.pop()
    return r
def T(F,m):
    out=[0]
    for E,c in enumerate(F):
        if c==0: continue
        e=E//2
        if E%2==0: g=list(cheb(m+e))
        else:
            g=add(cheb(m+e+1),cheb(m+e),-1); assert all(x%2==0 for x in g); g=[x//2 for x in g]
        term=[0]*e+[c*x for x in g]
        out=add(out,term)
    return out
def v2(x): return (x&-x).bit_length()-1 if x else 10**9
def minval(F): return min(v2(c) for c in F)
if __name__=='__main__':
    m=int(sys.argv[1]); J=int(sys.argv[2])
    A=[[1]]
    for j in range(J+2): A.append(T(A[-1],m))
    res=[]
    for j in range(J):
        d=add(A[j+2],A[j],-1)
        vals=[v2(c) for c in d]
        res.append(dict(j=j,deg=len(d)-1,minval=min(vals),val_by_degree=vals[:12]))
    print(json.dumps(dict(m=m,rows=res)))
