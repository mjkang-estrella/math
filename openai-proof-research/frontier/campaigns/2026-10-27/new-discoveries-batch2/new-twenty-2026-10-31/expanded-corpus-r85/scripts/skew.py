from poly import test,D
from collections import defaultdict
import itertools,json
parts=[a for a in itertools.product(range(8),repeat=3) if a[0]>=a[1]>=a[2] and sum(a)<=7];count=0;bad=[]
for lam in parts:
 for mu in parts:
  if any(a<b for a,b in zip(lam,mu)):continue
  cells=[(i,j) for i in range(3) for j in range(mu[i],lam[i])];fill={};p=defaultdict(int)
  def walk(k,alpha):
   if k==len(cells):p[alpha]+=1;return
   i,j=cells[k]
   for v in range(3):
    if (i,j-1) in fill and fill[i,j-1]>v:continue
    if (i-1,j) in fill and fill[i-1,j]>=v:continue
    fill[i,j]=v;a=list(alpha);a[v]+=1;walk(k+1,tuple(a));del fill[i,j]
  walk(0,(0,0,0));count+=1
  err=test(p,3,len(cells))
  if err:bad.append([lam,mu,err])
print(count,bad)
(D/'outputs/343052-search.json').write_text(json.dumps(dict(variable_count=3,outer_partition_size_at_most=7,all_contained_inner_partitions=True,skew_shapes=count,violations=bad,method='exact tableau enumeration; normalized derivative Hessian inertia by characteristic polynomials; full M-convex exchange'),indent=2)+'\n')
