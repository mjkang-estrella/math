# Checks the structural identities used in the 342364 proof, for m=1..MAX:
#  even m=2k:  T(1)-1 = y(1+y)*rho, rho = 8*U_{k-1}(1+2y)^2 ;  r0 = rho + Tt(rho)
#  odd  m=2h+1: T(1)+1 = 2(1+y)*W_h(1+2y)^2 ; T(2(1+y)H) = 2(1+y) T'(H) ; r0 = 2*((T'-1)G)/y, G=W_h^2
#  crude bound (odd m): nu2(r0_F) >= 2F+3 for all F
import sys, json
from math import comb
sys.path.insert(0, __import__('os').path.dirname(__file__))
from tcheb import T, add, v2
from reduced import Tt, divyy, mul
def U(N): return [4**i*comb(N+i+1,2*i+1) for i in range(N+1)] if N>=0 else [0]
def W(N): return [4**i*comb(N+i,2*i) for i in range(N+1)]
def Tp(H,m):
    out=[0]
    for E,c in enumerate(H):
        if not c: continue
        e=E//2
        g=[0]*e+W(m+e) if E%2==0 else [0]*(e+1)+[2*x for x in U(m+e)]
        out=add(out,[c*x for x in g])
    return out
MAX=int(sys.argv[1]); res=[]
for m in range(1,MAX+1):
    A1=T([1],m); A2=T(A1,m); r0=divyy(add(A2,[1],-1))
    if m%2==0:
        k=m//2; Uk=U(k-1); rho=[8*x for x in mul(Uk,Uk)]
        ok1=add(add(A1,[1],-1),mul([0,1,1],rho),-1)==[0]
        ok2=add(r0,add(rho,Tt(rho,m)),-1)==[0]
        res.append(dict(m=m,ok=ok1 and ok2))
    else:
        h=(m-1)//2; G=mul(W(h),W(h))
        ok1=add(add(A1,[1]),mul([2,2],G),-1)==[0]
        H=[3,-5,7,1]  # random test polynomial
        ok2=add(T(mul([2,2],H),m),mul([2,2],Tp(H,m)),-1)==[0]
        g=add(Tp(G,m),G,-1); assert g[0]==0
        ok3=add(r0,[2*x for x in g[1:]],-1)==[0]
        crude=all(v2(c)>=2*F+3 for F,c in enumerate(r0) if c)
        res.append(dict(m=m,ok=ok1 and ok2 and ok3,crude=crude))
print(json.dumps(dict(all_ok=all(r['ok'] and r.get('crude',True) for r in res),rows=res)))
