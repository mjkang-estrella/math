import json,sys,math
from fractions import Fraction
from pathlib import Path
import sympy as S
L=Path(__file__).resolve().parent
rows=json.loads((L/'checks.json').read_text())['rows'];out=[]
def vp(a,p):
 k=0
 while a%p==0:a//=p;k+=1
 return k
def subsets(parts):
 r={0}
 for a in parts:r|={x+a for x in r}
 return r
def polygon(co,p):
 h=[]
 for i,a in enumerate(reversed(co)):
  if not a:continue
  q=(i,vp(abs(a),p))
  while len(h)>1 and (h[-1][0]-h[-2][0])*(q[1]-h[-1][1]) <= (h[-1][1]-h[-2][1])*(q[0]-h[-1][0]):h.pop()
  h.append(q)
 return h
for row in rows:
 d=row['degree'];co=row['F_coefficients'];allowed=set(range(1,d//2+1));records=[]
 for p in S.primerange(2,2*row['n']+2):
  h=polygon(co,p);parts=[]
  assert h[0][0]==0 and h[-1][0]==d
  slopes=[Fraction(b[1]-a[1],b[0]-a[0]) for a,b in zip(h,h[1:])]
  assert all(a<b for a,b in zip(slopes,slopes[1:]))
  for a,b in zip(h,h[1:]):
   for i in range(a[0],b[0]+1):
    c=co[d-i]
    if c:assert Fraction(vp(abs(c),p)-a[1]) >= Fraction((i-a[0])*(b[1]-a[1]),b[0]-a[0])
  for a,b in zip(h,h[1:]):
   dx=b[0]-a[0];dy=b[1]-a[1];den=Fraction(dy,dx).denominator;parts.extend([den]*(dx//den))
  poss=subsets(parts);allowed &= poss
  if h!=[(0,0),(d,0)]:records.append({'p':p,'vertices':h,'allowable_small_degrees':sorted(poss & set(range(1,d//2+1)))})
 out.append({'n':row['n'],'degree':d,'remaining_factor_degrees':sorted(allowed),'polygons':records})
result={'scope':'unshifted Newton degree restrictions only, n3..48; not factor existence','rows':out}
if len(sys.argv)>1 and sys.argv[1]=='verify':assert json.loads((L/'newton.json').read_text())==json.loads(json.dumps(result));print('Newton controls reproduce')
else:
 (L/'newton.json').write_text(json.dumps(result,indent=2)+'\n')
 for r in out:print(r['n'],r['degree'],r['remaining_factor_degrees'])
