"""Small exact arithmetic cross-check of displayed constructions; not proof certification."""
from pathlib import Path
import json

def conv(a,b):
 out=[0]*(len(a)+len(b)-1)
 for i,x in enumerate(a):
  for j,y in enumerate(b):out[i+j]+=x*y
 return out

def profile(bfree,a,q):
 c=[1,1];e=[1,6,1]
 cp,cq=conv(c,a),conv(c,q);ep,eq=conv(e,a),conv(e,q)
 lc=2*bfree+4*sum(map(max,zip(cp,cq)))
 lm=8*bfree+4*sum(map(max,zip(ep,eq)))
 return {'free':bfree,'A':sum(a),'Q':sum(q),'fixed':4*lc,'stable':lm,'cyclic':8*bfree+32*max(sum(a),sum(q)),'gap':lm-4*lc}

out=[]
for a,b in [(0,0),(0,1),(1,0),(1,2),(1,3),(2,6),(2,7),(3,10),(10,30)]:
 v=profile(12+32*a+24*b,[2*a,4*a,2*a],[b,b,b]);v.update(a=a,b=b)
 assert (v['fixed']==v['cyclic'])==(b<=2*a or b>=3*a)
 if a>=1 and 3*a<=b<7*a/2:
  assert v['fixed']==96+256*a+288*b
  assert v['stable']==96+368*a+256*b
  assert v['gap']==112*a-32*b>0
 if b>=3*a and 2*b>=7*a:assert v['gap']==0
 out.append(v)
L=6
def fr(r):return [sum(k+l==j for k in range(1,L-r+1) for l in range(r+1)) for j in range(1,L+1)]
x,y,z=fr(0),fr(1),fr(2)
v=profile(506,[4*k for k in y],[3*k+2*l for k,l in zip(x,z)])
assert v['fixed']==5392 and v['stable']==5424 and v['cyclic']==5392
out.append({'cp9_seven_center_m1':v})
r=Path(__file__).parent
(r/'private/arithmetic-results.json').write_text(json.dumps(out,indent=2)+'\n')
print('Exact convolution checks completed for nine boundary/interior parameter choices and the seven-center CP9 construction.')
