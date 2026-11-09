"""Exact finite checks of the regular-case certificate; not the universal proof."""
import itertools,json,resource,time
from pathlib import Path
resource.setrlimit(resource.RLIMIT_CPU,(35,35));resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,512*1024**2))
t=time.monotonic();counts={};witnesses=0;checks=0
for n in range(2,6):
 pairs=list(itertools.combinations(range(n),2));regular=0;nonconstant=0
 for vals in itertools.product(range(3),repeat=len(pairs)):
  C=[[0]*n for _ in range(n)]
  for (i,j),a in zip(pairs,vals):C[i][j]=C[j][i]=a
  sums=list(map(sum,C))
  if len(set(sums))!=1:continue
  regular+=1
  if len(set(vals))==1:continue
  nonconstant+=1;found=False
  for i,j in pairs:
   v=[0 if k in (i,j) else C[k][i]-C[k][j] for k in range(n)]
   if not any(v):continue
   found=True;s=sum(x*x for x in v)
   assert sum(v)==0 and s>=2
   w=[int(k==i)-int(k==j) for k in range(n)]
   cw=[sum(C[k][l]*w[l] for l in range(n)) for k in range(n)]
   assert cw==[v[k]-C[i][j]*w[k] for k in range(n)]
   assert sum(cw[k]*v[k] for k in range(n))==s
   checks+=1
  assert found
  witnesses+=1
 counts[n]={'all_symmetric_inputs':3**len(pairs),'regular':regular,'nonconstant_regular':nonconstant}
r={'counts':counts,'certified_nonconstant_inputs':witnesses,'pair_identity_checks':checks,'seconds':time.monotonic()-t,'arithmetic':'integer only','scope':'symmetric zero-diagonal matrices with entries 0,1,2 through order 5, including odd row sums; not exhaustive digraph validation'}
Path(__file__).with_name('gap-diagnostic.json').write_text(json.dumps(r,indent=2));print(json.dumps(r))
