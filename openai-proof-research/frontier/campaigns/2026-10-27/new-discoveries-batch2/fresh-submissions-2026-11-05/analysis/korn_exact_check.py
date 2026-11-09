from fractions import Fraction as F
from pathlib import Path
import json
# Polynomials in independent formal z,w, restricted on the circle by w=z^-1.
def add(*ps):
 r={}
 for p in ps:
  for k,v in p.items():r[k]=r.get(k,F(0))+v
 return {k:v for k,v in r.items() if v}
def diff(p,j):return {(a-(j==0),b-(j==1)):v*(a if j==0 else b) for (a,b),v in p.items() if (a if j==0 else b)}
def circle(p):
 r={}
 for (a,b),v in p.items():r[a-b]=r.get(a-b,F(0))+v
 return {k:v for k,v in r.items() if v}
def norm(p):return sum((v*v for v in p.values()),F(0))
rows=[]
for k in range(1,65):
 U={(k+1,0):F(3,4),(k+2,1):F(-1,4),(1,k):F(2*k+3,4),(2,k+1):F(-2*k-1,4)}
 uz=circle(diff(U,0));uw=circle(diff(U,1));realuz={j:(uz.get(j,F(0))+uz.get(-j,F(0)))/2 for j in set(uz)|{-j for j in uz}}
 # Means are integral/(2*pi). Gradient=2(|Uz|²+|Uw|²).
 vals=[norm(circle(U)),2*(norm(uz)+norm(uw)),2*(norm(realuz)+norm(uw))]
 expected=[F(1,2),F(2*k*k+1,2),F(1,2)]
 assert vals==expected,(k,vals,expected)
 rows.append({'k':k,'norm_squared_over_pi':[str(2*v) for v in vals]})
p=Path(__file__).parent;(p/'korn-exact-diagnostic.json').write_text(json.dumps({'arithmetic':'Python fractions.Fraction, exact Laurent coefficients and constant-term Parseval identities','checked_k':[1,64],'pass':True,'rows':rows},indent=2));print('PASS: 64 exact polynomial derivative and circle integral checks; ordinary all-k proof separate')
