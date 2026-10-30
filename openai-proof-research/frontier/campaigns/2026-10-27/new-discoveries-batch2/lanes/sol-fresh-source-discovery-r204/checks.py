from fractions import Fraction as Q
import json,itertools

def rank(a):
 a=[list(map(Q,row)) for row in a];r=0
 for j in range(len(a[0])):
  p=next((i for i in range(r,len(a)) if a[i][j]),None)
  if p is None:continue
  a[r],a[p]=a[p],a[r];v=a[r][j];a[r]=[x/v for x in a[r]]
  for i in range(len(a)):
   if i!=r:
    v=a[i][j];a[i]=[x-v*y for x,y in zip(a[i],a[r])]
  r+=1
  if r==len(a):break
 return r

def arank(a):return rank([[x-y for x,y in zip(row,a[0])] for row in a[1:]])
count=0
# Rational points on t^2+s^2=1, in the source's cutoff-one chart.
for z in range(2,32):
 t=Q(2*z,z*z+1);s=Q(z*z-1,z*z+1);t0=Q(3,5);s0=Q(4,5)
 for eta in [Q(1,1000),Q(-1,1000)]:
  P=[[t,0,-s],[-t,0,-s],[0,t,-s+eta*t],[0,-t,-s+eta*t]]
  J=[[t,0,-s],[-t,0,-s],[0,t+eta*s,-s],[0,-t-eta*s,-s]]
  E=[[t0,0,-s0],[-t0,0,-s0],[0,t0,-s0+eta*t0],[0,-t0,-s0+eta*t0]]
  c=[0,0,t0*s/t-s0]
  assert t*t+s*s==1 and arank(P)==3 and arank(J)==2
  for p,j,e in zip(P,J,E):
   assert sum(x*y for x,y in zip(p,j))==1
   assert p==[t/t0*(x-y) for x,y in zip(e,c)]
  count+=1
# Higher-dimensional affine-rank controls on the actual source construction.
higher=0
for n in range(3,13):
 for k in range(4,n+2):
  m=k-2;t=Q(3,5);s=Q(4,5);eta=Q(1,1000)
  directions=[]
  for j in range(m):directions.append([Q(int(i==j)) for i in range(m)])
  directions += [[-Q(int(i==j)) for i in range(m)] for j in [0,1]]
  P=[];J=[]
  for a in directions:
   P.append([t*x for x in a]+[Q(0)]*(n-m-1)+[-s+eta*t*a[1]*a[1]])
   J.append([t*x+(eta*s*x if i==1 else 0) for i,x in enumerate(a)]+[Q(0)]*(n-m-1)+[-s])
  assert arank(P)==k-1 and arank(J)==k-2
  higher+=1
# Degenerate derivative model: F=(x_1,...,x_r,sum_{j>r}x_j^2).
model=0
for n in range(3,7):
 for k in range(4,n+2):
  r=k-2
  for x in itertools.product([-1,0,1],repeat=n):
   F=list(x[:r])+[sum(v*v for v in x[r:])]
   assert (not any(F))==(not any(x));model+=1
print(json.dumps(dict(status='PASS',source_3d_controls=count,source_higher_rank_controls=higher,degenerate_fiber_controls=model,scope='Exact finite diagnostics only. No universal medial-axis converse proof; no fixed eta certified globally convex.'),indent=2))
