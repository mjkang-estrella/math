"""Exact method checks only: these do not resolve the entropy conjecture."""
import json,hashlib,sys
from fractions import Fraction as Q
from pathlib import Path
import sympy as s
L=Path(__file__).resolve().parent
if '--verify' in sys.argv:
 for n in ['scientific-freeze.json','finalmanifest.json']:
  j=json.loads((L/n).read_bytes())
  for item in j['files']:
   b=(L/item['path']).read_bytes()
   assert len(b)==item['bytes'] and hashlib.sha256(b).hexdigest()==item['sha256'],item['path']
  print(n,'PASS',len(j['files']))
records=[]
for m in range(1,41):
 # sqrt(H)=1+epsilon*x^m on [0,1]; lower-bound area divided by 8*pi.
 # I0=(2/3)x^(3/2), dI=-x^(m+3/2)/(m+3/2).
 coefficient=3/Q(2*m+3)*2-1
 area_derivative_over_8pi=coefficient/Q(m+2)
 assert area_derivative_over_8pi==Q(3-2*m,(2*m+3)*(m+2))
 records.append(dict(m=m,area_derivative_over_8pi=str(area_derivative_over_8pi)))
assert records[1]['area_derivative_over_8pi']=='-1/28'
# Uniform elementary remainder for m=2, 0<=epsilon<=1/100.
# I=I0(1-a*epsilon*x^2+rho), a=3/7, 0<=rho<=(3/11)epsilon^2*x^4.
# Direct rational bracketing of (1+epsilon*x^2)^-1*(I0/I)^2
# at x^2=z, with no floating root search. Finite checks are just controls.
controls=0
for den in [10,100,1000]:
 e=Q(1,den)
 for k in range(101):
  z=Q(k,100);lo=1-Q(3,7)*e*z;hi=lo+Q(3,11)*e*e*z*z
  assert lo>0
  lower=1/((1+e*z)*hi*hi);upper=1/((1+e*z)*lo*lo)
  tangent=1-Q(1,7)*e*z
  assert abs(lower-tangent)<=20*e*e*z*z
  assert abs(upper-tangent)<=20*e*e*z*z
  controls+=1
r=s.symbols('r',positive=True);F=s.Function('F')(r);H=s.Function('H')(r)
A=1-F;B=H*A
E=s.simplify(B*s.diff(A,r,2)/(2*A)+s.diff(A,r)*s.diff(B,r)/(4*A)-B*s.diff(A,r)**2/(4*A*A))
assert s.simplify(E+H*s.diff(F,r,2)/2+s.diff(H,r)*s.diff(F,r)/4)==0
K=(H*s.diff(F,r,2)+s.diff(H,r)*s.diff(F,r)/2)**2+2*H**2*s.diff(F,r)**2/r**2+2*(s.diff(H,r)*(1-F)-H*s.diff(F,r))**2/r**2+4*(1-H+H*F)**2/r**4
K1=s.simplify(K.subs(H,1).doit())
assert s.simplify(K1-(s.diff(F,r,2)**2+4*s.diff(F,r)**2/r**2+4*F**2/r**4))==0
f=r*r/(r+1)**3;k=s.factor(K1.subs(F,f).doit())
assert s.simplify(k-12*(r**4-2*r**3+7*r*r+2)/(r+1)**10)==0
# Local core scaling: theta(0)=theta0>0 -> J~theta0*r^3/3,
# source B=r^4/J^2~9/theta0^2/r^2. An improper integral from 0 diverges.
z=s.symbols('z',positive=True);theta0=s.symbols('theta0',positive=True)
assert s.limit(r**2*(r**4/(theta0*r**3/3)**2),r,0)==9/theta0**2
out=dict(status='PASS supporting diagnostics only',exact_variations=records,rational_controls=controls,symbolic_identities=4,source_resolution=False)
print(json.dumps(out,indent=2))
