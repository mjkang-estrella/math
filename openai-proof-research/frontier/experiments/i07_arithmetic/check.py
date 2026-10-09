"""Exact bookkeeping/certificate checks only; no asymptotic numerical tests."""
import json, math
from fractions import Fraction as F
from pathlib import Path
root=Path(__file__).resolve().parents[3]

def upper(x,e):
    lo,hi=0,100000
    assert F(hi,100000)**e>x
    while hi-lo>1:
        mid=(lo+hi)//2
        if F(mid,100000)**e>x:hi=mid
        else:lo=mid
    return F(hi,100000)

epsilon=F(1,10**6); etaL,etaH=1-epsilon,F(3001,3000)
bL,bH=4-2*etaH,2+2*epsilon
t,w=F(1,2),F(24809,100000); m=3*w
u,v=(etaH-m)/4,(bH-m)/4; tau=F(1,50000)
assert 0<m<1 and m<min(etaL,bL)
cut1=w**3*10-(F(5,16)*(etaH+bH*t))**4
cut2=w**2*5-((etaH+bH*t)/3)**3
assert cut1>0 and cut2>0
assert min(u,v)>0 and F(3,20)<=v/u<=5

def delta(h,D): return upper((u*v)**h/((2*u+v)**(h-1)*D),h)
P=[delta(4,u+v),delta(3,v),max(delta(2,min(3*u,2*v,u+v)),upper(u*u/3,2)),max(u/2,min(u,v/4))]
assert P==[F(4729,100000),F(5097,100000),F(6899,100000),F(76819,1200000)]
gap=1-m-sum(max(P[:i]) for i in range(1,5))-4*tau
fiber=1-m-2*u-2*tau
assert gap==F(1941,100000) and fiber==F(15319,120000)
phase_cases=0
for order in range(2,20):
 for J in range(1,9):
  for s in range(1,9):
   for c in range(J*s+1):
    for h in range(12):
     assert (J*s-c+h)%order == (J*s+(-c)%order+h)%order
     phase_cases+=1
assert (4-1)%3 != (4+1)%3

def mobius(n):
    ans=1;p=2
    while p*p<=n:
        if n%p==0:
            n//=p;ans=-ans
            if n%p==0:return 0
            while n%p==0:n//=p
        p+=1
    return -ans if n>1 else ans

def ramanujan(k,h):
    g=math.gcd(k,h)
    return sum(d*mobius(k//d) for d in range(1,g+1) if g%d==0)
residue_cases=0
for k in range(1,70):
 for h in range(k):
  for a in range(k):
   if math.gcd(a,k)==1:
    assert ramanujan(k,h*a)==ramanujan(k,h)
    residue_cases+=1
results={'scope':'Exact finite algebra and fixed parameter inequalities, not asymptotic validation.',
'quartic':{'epsilon':str(epsilon),'m':str(m),'u':str(u),'v':str(v),'cut_margin_1':str(cut1),'cut_margin_2':str(cut2),'threshold_upper_bounds':list(map(str,P)),'lattice_gap':str(gap),'fiber_gap':str(fiber)},
'phase_cases':phase_cases,'incorrect_positive_phase_counterexample':{'root_order':3,'Js':4,'c':1,'correct_exponent_mod3':0,'incorrect_exponent_mod3':2},'ramanujan_unit_invariance_cases':residue_cases,'failures':0}
p=root/'frontier/experiments/i07_arithmetic/results.json';p.write_text(json.dumps(results,indent=2)+'\n');print(json.dumps(results,indent=2))
