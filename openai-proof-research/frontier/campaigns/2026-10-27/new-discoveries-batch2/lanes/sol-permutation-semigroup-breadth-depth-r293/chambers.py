from fractions import Fraction as Q
from itertools import combinations,permutations
from math import gcd
from pathlib import Path
import json,sys
L=Path(__file__).resolve().parent
# a=1,b=x,c=y; complete list of values <=4a, plus the endpoint 4a.
H=int(sys.argv[1]) if len(sys.argv)>1 else 4
forms=[(u,v,w) for u in range(H) for v in range(H-u) for w in range(H-u-v) if u+v+w>0]+[(H,0,0)]
def val(f,p):return f[0]+f[1]*p[0]+f[2]*p[1]
lines=set()
for f,g in combinations(forms,2):
 t=tuple(x-y for x,y in zip(f,g));d=gcd(gcd(abs(t[0]),abs(t[1])),abs(t[2]));t=tuple(x//d for x in t)
 if next(x for x in t if x)!=abs(next(x for x in t if x)):t=tuple(-x for x in t)
 if t[1:]!=(0,0):lines.add(t)
def clip(poly,f,sign):
 out=[]
 for p,r in zip(poly,poly[1:]+poly[:1]):
  vp=sign*val(f,p);vr=sign*val(f,r)
  if vp>=0:out.append(p)
  if (vp>0 and vr<0) or (vp<0 and vr>0):
   t=vp/(vp-vr);out.append(tuple(p[j]+t*(r[j]-p[j]) for j in range(2)))
 out=list(dict.fromkeys(out))
 if len(out)<3:return []
 return out
polys=[[(Q(1),Q(1)),(Q(1),Q(2)),(Q(2),Q(2))]]
for f in sorted(lines):
 new=[]
 for p in polys:
  vs=[val(f,v) for v in p]
  if min(vs)<0<max(vs):new.extend([clip(p,f,1),clip(p,f,-1)])
  else:new.append(p)
 polys=[p for p in new if p]
survive=[];residues=list(permutations(range(3)))
for p in polys:
 center=tuple(sum(v[j] for v in p)/len(p) for j in range(2));ordered=sorted(forms,key=lambda f:val(f,center));ordered=[f for f in ordered if val(f,center)<=H]
 good=[]
 for R in residues:
  s=[sum(x*y for x,y in zip(f,R))%3 for f in ordered]
  if all(len(set(s[i:i+3]))==3 for i in range(0,len(s)-2,3)):good.append(R)
 if good:survive.append(dict(vertices=[[str(z) for z in v] for v in p],center=list(map(str,center)),residues=good,order=ordered))
out=dict(horizon=H,forms=forms,hyperplanes=sorted(lines),open_chambers=len(polys),polygons=[[[str(z) for z in v] for v in p] for p in polys],surviving_open_chambers=survive,limitation='Boundary hyperplanes not classified; sums above H*a untested. This is a necessary prefix screen only.')
(L/('chambers-result-'+str(H)+'.json')).write_text(json.dumps(out,indent=2));print('hyperplanes',len(lines),'chambers',len(polys),'survive',len(survive));print(survive[:2])
if H==8:
 edges=set();vertices=set()
 for p in polys:
  vertices.update(p)
  for x,y in zip(p,p[1:]+p[:1]):edges.add(tuple(sorted((x,y))))
 def boundary_test(p):
  if not 1<p[0]<p[1]<2:return []
  groups={}
  for f in forms:
   v=val(f,p)
   if v<=H:groups.setdefault(v,[]).append(f)
  good=[]
  for R in residues:
   s=[];ok=True
   for v,fs in sorted(groups.items()):
    rs={sum(x*y for x,y in zip(f,R))%3 for f in fs}
    if len(rs)>1:ok=False;break
    s.append(next(iter(rs)))
   if ok and all(len(set(s[i:i+3]))==3 for i in range(0,len(s)-2,3)):good.append(R)
  return good
 E=[];V=[]
 for x,y in sorted(edges):
  p=tuple((x[j]+y[j])/2 for j in range(2));rs=boundary_test(p)
  if rs:E.append(dict(endpoints=[list(map(str,x)),list(map(str,y))],residues=rs,lines=[f for f in sorted(lines) if val(f,p)==0]))
 for p in sorted(vertices):
  rs=boundary_test(p)
  if rs:V.append(dict(point=list(map(str,p)),residues=rs))
 (L/'boundary-result.json').write_text(json.dumps(dict(edges=E,vertices=V,edge_count=len(edges),vertex_count=len(vertices)),indent=2))
 print('surviving edges',len(E),'vertices',len(V),'line supports',sorted({tuple(f) for e in E for f in e['lines']}))
