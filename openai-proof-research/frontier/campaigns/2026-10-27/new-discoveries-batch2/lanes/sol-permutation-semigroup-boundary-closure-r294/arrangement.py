from fractions import Fraction as F
from itertools import combinations,permutations
from math import gcd
from pathlib import Path
import json
L=Path(__file__).resolve().parent
old=json.loads((L/'frozen/0021-chambers-result-8.json').read_text())
H=8
forms=[(u,v,w) for u in range(9) for v in range(9-u) for w in range(9-u-v) if 0<u+v+w<=8]
def ev(f,p):return f[0]+f[1]*p[0]+f[2]*p[1]
def norm(t):
 g=gcd(*t);t=tuple(x//g for x in t)
 return t if next(x for x in t if x)>0 else tuple(-x for x in t)
triangle=[(F(1),F(1)),(F(1),F(2)),(F(2),F(2))]
# Includes all degree-eight forms, unlike predecessor's economical list.
orderforms=[f for f in forms if sum(f)<8 or f==(8,0,0)]
lines=sorted({norm(tuple(x-y for x,y in zip(f,g))) for f,g in combinations(orderforms,2) if f[1:]!=g[1:]})
lines=[f for f in lines if min(ev(f,p) for p in triangle)<0<max(ev(f,p) for p in triangle)]
borders=[(-1,1,0),(0,-1,1),(-2,0,1)]
alllines=lines+borders
def meet(f,g):
 z=f[1]*g[2]-g[1]*f[2]
 if not z:return None
 return (F(f[2]*g[0]-g[2]*f[0],z),F(f[0]*g[1]-g[0]*f[1],z))
def closed(p):return p and 1<=p[0]<=p[1]<=2
def interior(p):return 1<p[0]<p[1]<2
points={p for f,g in combinations(alllines,2) if closed(p:=meet(f,g))}
xs=sorted({p[0] for p in points}|{F(1),F(2)})
res=list(permutations(range(3)))
def test(p):
 groups={}
 for f in forms:
  v=ev(f,p)
  if v<=8:groups.setdefault(v,[]).append(f)
 good=[];bad=[]
 for R in res:
  seq=[];compatible=True
  for v,fs in sorted(groups.items()):
   rr={sum(a*b for a,b in zip(f,R))%3 for f in fs}
   if len(rr)!=1:compatible=False;break
   seq.append((v,next(iter(rr))))
  if not compatible:bad.append('incompatible');continue
  fail=next((i for i in range(0,len(seq)-2,3) if len({s[1] for s in seq[i:i+3]})!=3),None)
  if fail is None:good.append(R);bad.append(None)
  else:bad.append([fail+1,[str(s[0]) for s in seq[fail:fail+3]],[s[1] for s in seq[fail:fail+3]]])
 return good,bad
faces={}
for left,right in zip(xs,xs[1:]):
 x=(left+right)/2
 ys=sorted({x,F(2)}|{F(-f[0]-f[1]*x,f[2]) for f in lines if f[2] and x<F(-f[0]-f[1]*x,f[2])<2})
 for low,high in zip(ys,ys[1:]):
  p=(x,(low+high)/2);key=tuple(1 if ev(f,p)>0 else -1 for f in lines)
  if key not in faces:
   good,bad=test(p);assert not good
   faces[key]=dict(point=list(map(str,p)),failures=bad)
oldsigns=set()
for poly in old['polygons']:
 p=tuple(sum(F(v[i]) for v in poly)/len(poly) for i in range(2))
 oldsigns.add(tuple(1 if ev(f,p)>0 else -1 for f in lines))
assert set(faces)==oldsigns
edges=[];all_edges=0
for f in lines:
 pp=sorted(p for p in points if ev(f,p)==0)
 for p,q in zip(pp,pp[1:]):
  mid=tuple((x+y)/2 for x,y in zip(p,q))
  if not interior(mid):continue
  all_edges+=1;good,bad=test(mid)
  if good:edges.append(dict(line=f,endpoints=[list(map(str,p)),list(map(str,q))],residues=good))
vertices=[]
for p in sorted(points):
 if interior(p):
  good,bad=test(p)
  if good:vertices.append(dict(point=list(map(str,p)),residues=good))
prior=json.loads((L/'frozen/0018-boundary-result.json').read_text())
def eset(es):return {(tuple(tuple(v) for v in e['endpoints']),tuple(tuple(r) for r in e['residues'])) for e in es}
def vset(vs):return {(tuple(v['point']),tuple(tuple(r) for r in v['residues'])) for v in vs}
assert eset(edges)==eset(prior['edges']);assert vset(vertices)==vset(prior['vertices'])
out=dict(method='independent vertical slabs; pairwise intersections; all degree<=8 forms',lines=lines,x_events=len(xs),open_faces=len(faces),face_certificates=list(faces.values()),interior_edges=all_edges,surviving_edges=edges,surviving_vertices=vertices,prior_face_sign_sets_equal=True,prior_boundary_sets_equal=True)
(L/'arrangement-result.json').write_text(json.dumps(out,indent=2)+'\n')
print({k:v for k,v in out.items() if k not in ['lines','face_certificates','surviving_edges','surviving_vertices']});print('retained',len(edges),len(vertices))
