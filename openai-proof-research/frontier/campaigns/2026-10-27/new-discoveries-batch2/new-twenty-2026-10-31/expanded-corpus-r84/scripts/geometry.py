import itertools,json,time
from fractions import Fraction
from pathlib import Path
D=Path(__file__).resolve().parents[1];t=time.time()
def cross(a,b,c):return (b[0]-a[0])*(c[1]-a[1])-(b[1]-a[1])*(c[0]-a[0])
def hull(ps):
 ps=sorted(ps)
 if len(ps)<2:return ps
 lo=[];hi=[]
 for a in ps:
  while len(lo)>1 and cross(lo[-2],lo[-1],a)<=0:lo.pop()
  lo.append(a)
 for a in ps[::-1]:
  while len(hi)>1 and cross(hi[-2],hi[-1],a)<=0:hi.pop()
  hi.append(a)
 return lo[:-1]+hi[:-1]
def on(a,b,c):return cross(a,b,c)==0 and min(a[0],b[0])<=c[0]<=max(a[0],b[0]) and min(a[1],b[1])<=c[1]<=max(a[1],b[1])
def inside(p,H):
 if len(H)==1:return H[0]==p
 if len(H)==2:return on(*H,p)
 return all(cross(a,b,p)>=0 for a,b in zip(H,H[1:]+H[:1]))
def meet(A,B):
 if any(inside(p,B) for p in A) or any(inside(p,A) for p in B):return True
 for a,b in zip(A,A[1:]+A[:1]):
  for c,d in zip(B,B[1:]+B[:1]):
   x,y=cross(a,b,c),cross(a,b,d);z,w=cross(c,d,a),cross(c,d,b)
   if x*y<0 and z*w<0:return True
   if on(a,b,c) or on(a,b,d) or on(c,d,a) or on(c,d,b):return True
 return False
def partitions(n,r):
 def rec(a):
  if len(a)==n:
   if max(a)==r-1:yield a
  else:
   for k in range(min(max(a)+1,r-1)+1):yield from rec(a+[k])
 yield from rec([0])
out={}
for n in [5,6,7]:
 pats=list(partitions(n,3));yes=0;no=[]
 for ps in itertools.combinations(list(itertools.product(range(3),repeat=2)),n):
  good=False
  for pat in pats:
   hs=[hull([p for p,c in zip(ps,pat) if c==k])for k in range(3)]
   if all(meet(A,B) for A,B in itertools.combinations(hs,2)):good=True;break
  if good:yes+=1
  else:no.append(ps)
 out[n]={'pointsets':yes+len(no),'admitting_pairwise_intersecting_3_partition':yes,'failures':no,'partitions_per_set_cap':len(pats)}
(D/'outputs/reay.json').write_text(json.dumps({'scope':'All n-subsets of 3x3 integer grid, n=5,6,7; r=3,k=2,d=2; all set partitions until witness or exhaustion; exact integer convex hull tests','cases':out,'wall_seconds':time.time()-t},indent=2)+'\n');print(out)
