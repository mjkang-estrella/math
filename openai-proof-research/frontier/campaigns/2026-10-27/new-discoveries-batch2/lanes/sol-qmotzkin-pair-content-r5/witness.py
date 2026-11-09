#!/usr/bin/env python3
import os,resource
for k in ('OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS','NUMEXPR_NUM_THREADS'):os.environ[k]='1'
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,)*2);resource.setrlimit(resource.RLIMIT_CPU,(50,50))
import json,math
from pathlib import Path
from itertools import combinations_with_replacement,permutations,product
n,r=3,6;target=(3,5,2,5,2,1)
parts=[tuple(reversed(t)) for t in combinations_with_replacement(range(n+1),r)]
chains=[]
def layer(mu,nu):
 cells=[(i,j) for i in range(r) for j in range(mu[i],nu[i])];a={};counts=[0]*3
 def rec(k,res):
  if k==len(cells):counts[res]+=1;return
  i,j=cells[k]
  for v in (1,2):
   if (i-1,j) in a and a[i-1,j]>=v:continue
   if (i,j-1) in a and a[i,j-1]>v:continue
   a[i,j]=v;rec(k+1,(res+v)%3);del a[i,j]
 rec(0,0);assert counts[1]==counts[2]
 return counts

def visit(l,mu,chain,counts):
 if l==r:
  if mu==(n,)*r:chains.append({'chain':chain,'residues':counts,'sign':counts[0]-counts[1]})
  return
 for nu in parts:
  if nu[l]!=n or sum(nu)-sum(mu)!=target[l] or any(a>b for a,b in zip(mu,nu)):continue
  c=layer(mu,nu)
  if not sum(c):continue
  nxt=[sum(counts[a]*c[b] for a in range(3) for b in range(3) if (a+b)%3==s) for s in range(3)]
  visit(l+1,nu,chain+[nu],nxt)
visit(0,(0,)*r,[],[1,0,0]);total=[sum(c['residues'][i] for c in chains) for i in range(3)]
assert total[0]-total[1]==-1
# Entire determinant's single target coefficient, independently via permutations.
# H_d(prefix m)=sum_{|e|=d} product f(e_i) a^e; f=1,-1,0 periodically.
f=lambda d: (1,-1,0)[d%3]
contributions=[]
for perm in permutations(range(r)):
 deg=[n-i+perm[i] for i in range(r)]
 if min(deg)<0:continue
 from functools import lru_cache
 @lru_cache(None)
 def rec(i,rem):
  if i==r:return int(not any(rem))
  if sum(rem)!=sum(deg[i:]):return 0
  ans=0
  for e in product(*(range(min(rem[j],deg[i])+1) for j in range(i+1))):
   if sum(e)!=deg[i] or any(x%3==2 for x in e):continue
   nr=tuple(rem[j]-(e[j] if j<=i else 0) for j in range(r))
   ans+=math.prod(f(x) for x in e)*rec(i+1,nr)
  return ans
 c=rec(0,target);sgn=(-1)**sum(perm[i]>perm[j] for i in range(r) for j in range(i+1,r))
 if c:contributions.append({'permutation_zero_based':perm,'signed_coefficient':sgn*c})
assert sum(c['signed_coefficient'] for c in contributions)==-1
out={'shape':[n]*r,'flags':list(range(2,2*r+1,2)),'content':target,'total_residues':total,'coefficient':-1,'chains':chains,'determinant_contributions':contributions,'status':'PASS'}
Path(__file__).with_name('witness.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))

# Supplementary geometric-degree aggregation, kept separate from the proof.
import runpy
poly=runpy.run_path(str(Path(__file__).with_name('check.py')))['polynomial'](n,r)
for chain in out['chains']:
 mu=(0,)*r;info=[]
 for nu in chain['chain']:
  free=[0]*r;v=0
  for j in range(n):
   rows=[i for i in range(r) if mu[i]<=j<nu[i]]
   if len(rows)==2:v+=1
   elif rows:free[rows[0]]+=1
  info.append({'V':v,'free':free});mu=nu
 chain['layer_data']=info
out['geometric_degree']=sum(i*e for i,e in enumerate(target))
out['full_geometric_coefficient_at_degree']=sum(c for e,c in poly.items() if sum(i*v for i,v in enumerate(e))==out['geometric_degree'])
assert out['geometric_degree']==37 and out['full_geometric_coefficient_at_degree']==29
Path(__file__).with_name('witness-extended.json').write_text(json.dumps(out,indent=2)+'\n')
