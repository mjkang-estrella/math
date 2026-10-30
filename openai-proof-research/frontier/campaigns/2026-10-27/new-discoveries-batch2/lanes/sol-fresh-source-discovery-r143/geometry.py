from fractions import Fraction as F
from pathlib import Path
import json
L=Path(__file__).resolve().parent
def cross(a,b):return a[0]*b[1]-a[1]*b[0]
def sub(a,b):return (a[0]-b[0],a[1]-b[1])
def area(p):return abs(sum(cross(a,b) for a,b in zip(p,p[1:]+p[:1])))/2 if p else F(0)
def clip(poly,a,b):
 out=[];e=sub(b,a)
 for u,v in zip(poly,poly[1:]+poly[:1]):
  du=cross(e,sub(u,a));dv=cross(e,sub(v,a))
  if du>=0:out.append(u)
  if (du<0<dv) or (dv<0<du):
   t=du/(du-dv);out.append((u[0]+t*(v[0]-u[0]),u[1]+t*(v[1]-u[1])))
 return out
def cov(poly,z):
 out=poly[:];shift=[(x+z[0],y+z[1]) for x,y in poly]
 for a,b in zip(shift,shift[1:]+shift[:1]):
  out=clip(out,a,b)
  if not out:break
 return area(out)
D=[(F(0),F(0)),(F(1),F(0)),(F(0),F(1))]
V=[(1,0),(0,1),(-1,1),(-1,0),(0,-1),(1,-1)]
rows=[]
for eps in [F(1,100),F(1,1000)]:
 K=[(eps,F(0)),(F(1),F(0)),(F(0),F(1)),(F(0),eps)]
 assert area(K)==(1-eps*eps)/2
 for r in [F(1,3),F(1,2),F(2,3)]:
  for sector,(a,b) in enumerate(zip(V,V[1:]+V[:1])):
   for j in range(1,6):
    t=F(j,6);z=(r*((1-t)*a[0]+t*b[0]),r*((1-t)*a[1]+t*b[1]))
    g0=cov(D,z);g=cov(K,z)
    assert g0==(1-r)**2/2
    loss=eps*eps/2 if sector in [0,3] else F(0)
    assert g0-g==loss
    rows.append(dict(eps=str(eps),r=str(r),sector=sector,t=str(t),g0=str(g0),g=str(g),loss=str(loss)))
(L/'geometry-checks.json').write_text(json.dumps(dict(status='PASS',cases=len(rows),rows=rows,limit='Exact isolated covariogram samples only. No continuum sector rule, shape derivative, volume integration, or all-body inequality certified.'),indent=2)+'\n')
print('PASS',len(rows),'rational clipped covariogram values')
