"""Bounded diagnostics; no universal theorem follows from this grid."""
import json,hashlib,datetime,sys
from pathlib import Path
from fractions import Fraction as Q
import mpmath as m
L=Path(__file__).resolve().parent;m.mp.dps=60
def phi(t):return t*t/(1+t)-m.mpf('0.001')*t*t/(1+t)**2/(1+10000*(t-2)**2)
def dp(t):return m.diff(phi,t)
def inv(s):
 lo=m.mpf(0);hi=max(1,2*s+2)
 for _ in range(230):
  z=(lo+hi)/2
  if phi(z)<s:lo=z
  else:hi=z
 return (lo+hi)/2
a=m.mpf('0.1');grid=list(map(m.mpf,['0.001','0.01','0.1','0.5','1','1.9','1.99','2','2.01','2.1','3','10','100','10000']))
rows=[];worst=None
for u in grid:
 for v in grid:
  f=inv(a*(phi(u)+phi(v)))
  grad=[a*dp(u)/dp(f),a*dp(v)/dp(f)]
  gap=a-sum(z*z for z in grad)
  rec=[str(u),str(v),str(gap)]
  if worst is None or gap<m.mpf(worst[2]):worst=rec
  assert gap>0
  rows.append(rec)
# Exact second derivative at 201/100, independently computed by rational jets.
import sympy as S
t=S.symbols('t');p=t*t/(1+t)-S.Rational(1,1000)*t*t/(1+t)**2/(1+10000*(t-2)**2)
dd=S.diff(p,t,2).subs(t,S.Rational(201,100))
assert dd==-S.Rational(17578551005,8208541201) and dd<0
# Base-generator failure of the tempting convexity route: F(1,0)=1/4,
# F(2,0)=(1+sqrt(31))/15 < 1/2.
assert Q(31)<Q(13,2)**2
assert Q(1,10)*Q(1,2)==Q(1,20)
assert Q(1,4)**2/(1+Q(1,4))==Q(1,20)
out=dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),precision=60,grid_points=len(rows),worst_gradient_margin=worst,phi_second_derivative=str(dd),base_convexity_route='exactly false',scope='necessary gradient diagnostic only, not subadditivity proof',rows=rows)
if '--replay' not in sys.argv:(L/'checks.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:v for k,v in out.items() if k!='rows'},indent=2))
