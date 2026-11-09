# Finite certificate for the uniform proof (see outputs/342364-proof.md).
# All facts are exact; polynomial-in-t facts use exact Newton interpolation with a proved degree bound
# deg_m r_{0,F} <= 4F+4 and check on extra points.
import sys, json
from math import comb
from fractions import Fraction
sys.path.insert(0, __import__('os').path.dirname(__file__))
from tcheb import T, add, v2
from reduced import divyy
def r0(m): return divyy(add(T(T([1],m),m),[1],-1))
def newton(vals):
    b=[]; cur=list(vals)
    while cur: b.append(cur[0]); cur=[cur[i+1]-cur[i] for i in range(len(cur)-1)]
    return b
out={}
# (1) r_{0,0} = (2/3) m^2 (m+1)(m+5), m=1..80
out['r00_formula_m1_80']=all(3*r0(m)[0]==2*m*m*(m+1)*(m+5) for m in range(1,81))
def cls(q,s,F,extra=8):
    D=4*F+4; npts=D+1+extra
    vals=[r0(q*t+s)[F] for t in range(npts)]
    b=newton(vals[:D+1])
    pred=[sum(b[i]*comb(t,i) for i in range(D+1)) for t in range(npts)]
    return dict(cls=f'{q}t+{s}',F=F,deg_bound=D,points=npts,consistent=pred==vals,nu2_b=[v2(x) if x else None for x in b])
facts=[cls(4,3,1),cls(4,3,2),cls(16,15,1),cls(16,15,2),cls(16,11,1)]
out['class_facts']=facts
def minv(f): return min(x for x in f['nu2_b'] if x is not None)
out['m3mod4_r01_ge7']=facts[0]['consistent'] and minv(facts[0])>=7
out['m3mod4_r02_ge7']=facts[1]['consistent'] and minv(facts[1])>=7
out['m15mod16_r01_ge8']=facts[2]['consistent'] and minv(facts[2])>=8
out['m15mod16_r02_ge8']=facts[3]['consistent'] and minv(facts[3])>=8
f=facts[4]; out['m11mod16_r01_exactly7']=f['consistent'] and f['nu2_b'][0]==7 and all(x is None or x>=8 for x in f['nu2_b'][1:])
# (5) binomial identity C(k+a,2a+1)(2a+1)C(2a,a) = k C(k+a,a) C(k-1,a)
out['binom_identity_k1_60_a0_40']=all(comb(k+a,2*a+1)*(2*a+1)*comb(2*a,a)==k*comb(k+a,a)*comb(k-1,a) for k in range(1,61) for a in range(0,41))
# (6) Kummer nu2(C(2a,a)) = s2(a)
out['kummer_a0_300']=all(v2(comb(2*a,a))==bin(a).count('1') for a in range(0,301))
out['ALL_OK']=all(v for k,v in out.items() if isinstance(v,bool))
print(json.dumps(out,indent=1))
