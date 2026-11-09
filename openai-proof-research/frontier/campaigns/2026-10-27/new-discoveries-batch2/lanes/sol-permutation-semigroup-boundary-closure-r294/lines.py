from pathlib import Path
from fractions import Fraction as F
from itertools import combinations,permutations
from math import gcd
import json,sys
L=Path(__file__).resolve().parent;H=int(sys.argv[1]) if len(sys.argv)>1 else 12
prior=json.loads((L/'arrangement-result.json').read_text());supports=sorted({tuple(e['line']) for e in prior['surviving_edges']})
forms=[(u,v,w) for u in range(H) for v in range(H-u) for w in range(H-u-v) if u+v+w]+[(H,0,0)]
def val(f,p):return f[0]+f[1]*p[0]+f[2]*p[1]
def test(p):
 groups={}
 for f in forms:
  z=val(f,p)
  if z<=H:groups.setdefault(z,[]).append(f)
 good=[]
 for R in permutations(range(3)):
  s=[]
  for z,fs in sorted(groups.items()):
   rr={sum(x*y for x,y in zip(f,R))%3 for f in fs}
   if len(rr)!=1:break
   s.append(next(iter(rr)))
  else:
   if all(len(set(s[i:i+3]))==3 for i in range(0,len(s)-2,3)):good.append(R)
 return good
out=[]
for A,B,C in supports:
 # parameter t=x unless vertical; p=p0+t*p1
 if C:p0=(F(0),F(-A,C));p1=(F(1),F(-B,C))
 else:p0=(F(-A,B),F(0));p1=(F(0),F(1))
 def point(t):return tuple(x+t*y for x,y in zip(p0,p1))
 ff=[(val(f,p0),f[1]*p1[0]+f[2]*p1[1]) for f in forms]
 breaks=set()
 for (a,b),(c,d) in combinations(ff,2):
  if b!=d:
   t=(c-a)/(b-d);x,y=point(t)
   if 1<=x<=y<=2:breaks.add(t)
 for a,b in [(-1+p0[0],p1[0]),(p0[1]-p0[0],p1[1]-p1[0]),(p0[1]-2,p1[1])]:
  if b:
   t=-a/b;x,y=point(t)
   if 1<=x<=y<=2:breaks.add(t)
 breaks=sorted(breaks);segs=[];verts=[]
 for l,r in zip(breaks,breaks[1:]):
  p=point((l+r)/2)
  if 1<p[0]<p[1]<2 and (rs:=test(p)):segs.append(dict(parameter=[str(l),str(r)],endpoints=[list(map(str,point(l))),list(map(str,point(r)))],residues=rs))
 for t in breaks:
  p=point(t)
  if 1<p[0]<p[1]<2 and (rs:=test(p)):verts.append(dict(point=list(map(str,p)),residues=rs))
 out.append(dict(support=[A,B,C],parameter_origin=list(map(str,p0)),parameter_direction=list(map(str,p1)),events=len(breaks),segments=segs,vertices=verts))
 print((A,B,C),'segments',len(segs),'vertices',len(verts),flush=True)
(L/('lines-result-%s.json'%H)).write_text(json.dumps(dict(horizon=H,supports=out),indent=2)+'\n')
