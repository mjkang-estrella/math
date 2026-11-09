# MathDB 342364: reduced-operator certificate.
# Notation: y=x/(1-x), w=1+2y=(1+x)/(1-x).  A_j := T^j(1) in Z[y] with sum_n c_m(2^j n)x^n = C(x)^m A_j.
# d_j := A_{j+2}-A_j = y(1+y) r_j.  Claimed: r_{j+1} = Tt(r_j) with
#   Tt(y^{2e})   = 2 y^e U_{m+e}(1+2y)  = 2 y^e sum_i 4^i binom(m+e+i+1,2i+1) y^i
#   Tt(y^{2e+1}) =   y^e (U_{m+e+1}-U_{m+e})(1+2y) = y^e sum_i 4^i binom(m+e+i+1,2i) y^i
# weight omega(R)=min_E nu2(R_E)-bitlen(E);  omega(Tt R) >= omega(R)+1.
import sys, json
from math import comb
sys.path.insert(0, __import__('os').path.dirname(__file__))
from tcheb import T, add, v2
def Tt(R,m):
    out=[0]
    for E,c in enumerate(R):
        if c==0: continue
        e=E//2; K=m+e
        if E%2==0: g=[2*4**i*comb(K+i+1,2*i+1) for i in range(K+1)]
        else: g=[4**i*comb(K+i+1,2*i) for i in range(K+2)]
        out=add(out,[0]*e+[c*x for x in g])
    return out
def mul(a,b):
    r=[0]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,z in enumerate(b): r[i+j]+=x*z
    return r
def divyy(d):
    # divide by y(1+y)=y+y^2 exactly
    d=list(d); assert d[0]==0; d=d[1:]  # now divide by (1+y)
    q=[0]*(len(d)-1); rem=d[:]
    for k in range(len(d)-1,0,-1):
        q[k-1]=rem[k]; rem[k]-=q[k-1]; rem[k-1]-=q[k-1]
    assert all(x==0 for x in rem), 'not divisible'
    while len(q)>1 and q[-1]==0: q.pop()
    return q
def omega(R): return min(v2(c)-(E.bit_length()) for E,c in enumerate(R) if c)
def lead(R,w):
    return {E:(c>>(w+E.bit_length()))&1 for E,c in enumerate(R) if c and v2(c)-E.bit_length()==w}
if __name__=='__main__':
    mlo,mhi,J=map(int,sys.argv[1:4])
    for m in range(mlo,mhi+1):
        A=[[1]]
        for j in range(J+2): A.append(T(A[-1],m))
        r=[divyy(add(A[j+2],A[j],-1)) for j in range(J)]
        ok_op=all(add(Tt(r[j],m),r[j+1],-1)==[0] for j in range(J-1))
        om=[omega(x) for x in r]
        mono=all(om[j+1]>=om[j]+1 for j in range(J-1))
        L0=lead(r[0],om[0])
        print(json.dumps(dict(m=m,operator_identity_ok=ok_op,omega_r0=om[0],omega_seq=om,weight_increase_ok=mono,leading_r0={str(k):v for k,v in sorted(L0.items())},coeffval_min=[min(v2(c) for c in x if c) for x in r])),flush=True)
