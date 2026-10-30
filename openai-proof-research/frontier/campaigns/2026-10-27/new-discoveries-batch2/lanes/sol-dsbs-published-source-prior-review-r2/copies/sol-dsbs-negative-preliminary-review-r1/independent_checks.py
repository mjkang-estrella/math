from pathlib import Path
from fractions import Fraction as F
import itertools, json, mpmath as mp
mp.mp.dps=75
out=Path(__file__).resolve().parent
log=lambda x:mp.log(x,2)
h=lambda x: -x*log(x)-(1-x)*log(1-x) if 0<x<1 else mp.mpf(0)
def entropy(ps):return -sum(mp.mpf(p.numerator)/p.denominator*log(mp.mpf(p.numerator)/p.denominator) for p in ps if p)
def KL(a,b):return sum(mp.mpf(x.numerator)/x.denominator*log((mp.mpf(x.numerator)/x.denominator)/(mp.mpf(y.numerator)/y.denominator)) for x,y in zip(a,b) if x)
rows=[]
# Exact rational joint laws, with a processor containing zeros and correlated bits.
for k in range(1,13):
 A=[[F(k,2*k+3),F(1,2*k+3),F(2,2*k+3),F(k,2*k+3)], [F(1,2),0,0,F(1,2)]]
 B=[[F(1,10),F(2,10),F(3,10),F(4,10)],[0,F(1,3),F(2,3),0]]
 A=[[F(x) for x in v] for v in A];B=[[F(x) for x in v] for v in B]
 e=F(1,7); r=F(k,40)
 base=lambda x,y,z: ((1-z) if x==y else z)/2
 Q={};P={};Pjoint={};qhat={}
 for x,y in itertools.product(range(4),repeat=2):
  u=(x//2,x%2,y//2,y%2)
  P[u]=sum(A[m][x]*B[m][y]/2 for m in range(2))
  Q[u]=base(u[0],u[2],r)*base(u[1],u[3],r)
  for m in range(2):
   Pjoint[(m,)+u]=A[m][x]*B[m][y]/2
   qhat[(m,)+u]=Q[u]*Pjoint[(m,)+u]/P[u]
 assert sum(qhat.values())==1
 assert all(sum(qhat[(m,)+u] for m in range(2))==Q[u] for u in Q)
 def marg(ids):
  d={}
  for u,p in qhat.items():
   key=tuple(u[i] for i in ids);d[key]=d.get(key,F(0))+p
  return d
 def H(ids):return entropy(marg(ids).values())
 def I(a,b,c=()):return H(a+c)+H(b+c)-H(c)-H(a+b+c)
 block=I((1,2),(3,4),(0,)); single=I((1,),(3,),(0,))+I((2,),(4,),(0,1,3))
 jointkl=KL(list(qhat.values()),list(Pjoint.values())); kl=KL(list(Q.values()),list(P.values()))
 assert abs(jointkl-kl)<mp.mpf('1e-70')
 qm=marg((0,));rest=KL(list(qm.values()),[F(1,2)]*2)+block
 for m in range(2):
  qx=[sum(qhat[(m,x//2,x%2,y//2,y%2)] for y in range(4))/qm[(m,)] for x in range(4)]
  qy=[sum(qhat[(m,x//2,x%2,y//2,y%2)] for x in range(4))/qm[(m,)] for y in range(4)]
  rest+=mp.mpf(qm[(m,)].numerator)/qm[(m,)].denominator*(KL(qx,A[m])+KL(qy,B[m]))
 assert abs(rest-kl)<mp.mpf('1e-70')
 assert single<=block+mp.mpf('1e-70')
 assert abs(I((1,3),(0,))+I((2,4),(0,1,3))-I((1,2,3,4),(0,)))<mp.mpf('1e-70')
 rows.append({'k':k,'KL':str(kl),'block_CMI':str(block),'single_CMI':str(single),'exact_posterior_marginal':True})
slopes=[]
for j in [10,12,20,40]:
 e=mp.mpf(2)**(-j);s=mp.sqrt(1-2*e);a=(1-s)/2;b=a*a/(1-e)
 L=log((1-a)/a);A=L/s-log((1-e)/e);B=L*mp.sqrt(e/((1-e)*(1-2*e)))
 fun=lambda q:2*h((1-e)*q+e/2)-(1-e)*h(q)-e-h(e)
 assert abs(fun(b))<mp.mpf('1e-65')
 assert abs(mp.diff(fun,b))<mp.mpf('1e-60')
 assert abs(mp.diff(fun,b,2)/(4*(1-e)**2*(1-2*e)/(e*e*mp.log(2)))-1)<mp.mpf('1e-50')
 assert A-mp.sqrt(2)*B>mp.mpf(1)/16
 slopes.append({'j':j,'worst_beta_1_slope':str(A-mp.sqrt(2)*B)})
# Exact rational portions of analytic bounds; logarithmic bound follows by fourth power.
assert F(3969,2048)>F(7,4) and F(7,4)**4>8
assert F(3,4)-F(3,2)*F(11,24)==F(1,16)
(out/'independent-checks.json').write_text(json.dumps({'status':'PASS; diagnostics, not proof certificates','rational_probability_high_precision_entropy_cases':rows,'slope_checks':slopes,'exact_rational_bounds':True},indent=2))
print('PASS 12 rational posterior/zero-support cases; exact marginals; 75-digit KL decomposition and tensorization; four derivative/slope controls; exact rational bound arithmetic')
