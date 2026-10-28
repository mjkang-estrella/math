"""Exact exploratory checks of the proposed interval proof. Not a Lean proof."""
import json
from pathlib import Path
import sympy as s
from fractions import Fraction as Q
from interval_probe import narrow

a,b=s.symbols('a b')
c=a+b;d=a+2*b;e=2*a+3*b;f=3*a+5*b
L=2*a+b;J=a+3*b;K=3*a+4*b
rel=b*b-a*b-a*a+1
identities=[
 ('c3-ad2', c**3-a*d*d,-b),
 ('c2d-bd2',c*c*d-b*d*d,d),
 ('L2c-aJ2',L*L*c-a*J*J,3*a-b),
 ('Ld-Jc',L*d-J*c,1),
 ('Lc-a(K-1)',L*c-a*(K-1),a-1),
 ('Kc2-Ld2',K*c*c-L*d*d,a),
 ('J2c-a(K-1)2',J*J*c-a*(K-1)**2,6*a*a+8*a*b-9*a-9*b),
 ('Kc-Jd',K*c-J*d,2),
 ('c2-ae',c*c-a*e,-1),
 ('cd-be',c*d-b*e,1),
 ('d2c-ae2',d*d*c-a*e*e,-K),
 ('d3-be2',d**3-b*e*e,c),
 ('de-cf',d*e-c*f,-1),
 ('e2-df',e*e-d*f,1),
 ('lower-final',(e-1)**2*e-c*(f-2)**2,6*a*a+10*a*b-3*a-3*b-2),
 ('upper-final',d*(f-1)-(e-1)*e,c-1),
 ('invariant',d*d-c*d-c*c,-1),
]
checks=[]
for label,lhs,rhs in identities:
 rem=s.reduced(s.expand(lhs-rhs),[rel],b,a)[1]
 assert rem==0,(label,rem)
 checks.append({'identity':label,'remainder':str(rem)})
iv=[(Q(1),Q(4))]
for n in (1,2,3):iv=narrow(iv,n)
assert iv==[(Q(5,2),Q(8,3))],iv
ai,bi=2,3
steps=[]
for i in range(12):
 ci,di=ai+bi,ai+2*bi
 ei,fi=2*ai+3*bi,3*ai+5*bi
 assert bi*bi-ai*bi-ai*ai==-1
 assert 2*bi>=3*ai and bi<2*ai
 old=[(Q(ci,ai),Q(di,bi))]
 for n in (ci,2*ai+bi,di):old=narrow(old,n)
 assert old==[(Q(ei,ci),Q(fi,di))],(i,old)
 steps.append({'i':i,'a':ai,'b':bi,'inputs':[ci,2*ai+bi,di],
   'new_squared_interval':[str(Q(ei,ci)),str(Q(fi,di))]})
 ai,bi=ci,di
result={'status':'PASS','symbolic_identities':checks,'exact_base_interval':['5/2','8/3'],
        'finite_validation_only':steps,
        'scope':'Symbolic polynomial identities and finite exact interval checks; not the all-order theorem or a formal certificate.'}
Path('algebra-checks.json').write_text(json.dumps(result,indent=2)+'\n')
print('PASS:',len(checks),'symbolic identities, exact base,',len(steps),'interval induction instances')
