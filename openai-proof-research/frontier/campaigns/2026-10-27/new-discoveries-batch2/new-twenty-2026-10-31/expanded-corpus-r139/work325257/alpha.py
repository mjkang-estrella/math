# (b) monotonicity: for odd n, unique negative root alpha_n (Descartes on P(-x) = 1, P(x)>0 for x>0).
# Float bisection estimate, then EXACT separation: rational r with P_n(r) < 0 < P_{n+2}(r) certifies
# alpha_{n+2} < r < alpha_n (P_n<0 left of alpha_n, >0 right of it on (-1,0)).
import sys, json, pathlib
from fractions import Fraction
sys.path.insert(0,str(pathlib.Path(__file__).resolve().parent)); from tatami import P
def fval(p,x):
    acc=0.0
    for c in reversed(p): acc=acc*x+float(c)
    return acc
def root(p):
    lo,hi=-1.0,-0.5
    assert fval(p,lo)<0 and fval(p,hi)>=0
    for _ in range(70):
        mid=(lo+hi)/2
        if fval(p,mid)<0: lo=mid
        else: hi=mid
    return (lo+hi)/2
def sign_exact(p,xn,xd):
    D=len(p)-1; acc=p[D]; pw=1
    for k in range(D-1,-1,-1):
        pw*=xd; acc=acc*xn+p[k]*pw
    return (acc>0)-(acc<0)
a,b=int(sys.argv[1]),int(sys.argv[2])
prev=None
for n in range(a if a%2 else a+1,b+1,2):
    p=P(n); al=root(p)
    rec={'n':n,'alpha_float':al}
    if prev is not None:
        pn,pa,pp=prev
        rec['gap_float']=pa-al
        # choose dyadic r between al and pa
        k=10
        while True:
            den=2**k; num=round((al+pa)/2*den)
            if al < num/den < pa: break
            k+=4
            if k>200: break
        rec['r']=f'{num}/{den}'
        rec['cert']=(sign_exact(pp,num,den)<0 and sign_exact(p,num,den)>0)
    print(json.dumps(rec),flush=True)
    prev=(n,al,p)
