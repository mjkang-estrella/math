from itertools import permutations,combinations
from collections import Counter
from math import factorial
from pathlib import Path
import json
L=Path(__file__).parent
def boxes(p):
 out=[]
 for i,j,k,l in combinations(range(len(p)),4):
  a,b,c,d=p[i],p[j],p[k],p[l]
  if not b<a<d<c:continue
  if all(t in (j,k) or not b<p[t]<c for t in range(i+1,l)):out.append((i,j,k,l))
 return out
def inter(p,r):
 a=[]
 for i,x in enumerate(p):
  a.append(2*x-1)
  if i<len(r):a.append(2*r[i])
 return tuple(a)
def b12(p):
 return sum(p[i]<p[j] and all(not p[i]<p[k]<p[j] for k in range(i+1,j)) for i in range(len(p)) for j in range(i+1,len(p)))
def mult(p):
 out=Counter()
 for j in range(len(p)+1):
  hi=0;r=0
  for x in reversed(p[:j]):
   if x>hi:r+=1;hi=x
  out[r]+=1
 return tuple(sorted(out.items()))
res={'completion':[],'rule_failures':{},'inherited_blocking_not_sufficient':None,'scalar_closure_failure':None,'D':[]};identities=0
for m in range(1,6):
 count=0;minimum=factorial(m-1)
 for p in permutations(range(1,m+1)):
  oc=boxes(p);good=0
  rules={'increasing':tuple(range(1,m)),'decreasing':tuple(range(m-1,0,-1))}
  for name,r in rules.items():
   if name not in res['rule_failures'] and boxes(inter(p,r)):res['rule_failures'][name]={'pi':p,'rho':r,'output':inter(p,r),'occurrences':boxes(inter(p,r))}
  for r in permutations(range(1,m)):
   q=inter(p,r);out=boxes(q)
   cond=all(any(p[j]<=r[t]<p[k] for t in range(i,l)) for i,j,k,l in oc)
   assert all(any(p[j]<=r[t]<p[k] for t in range(i,l)) == ((2*i,2*j,2*k,2*l) not in out) for i,j,k,l in oc)
   identities+=len(oc)
   if oc and cond and out and res['inherited_blocking_not_sufficient'] is None:res['inherited_blocking_not_sufficient']={'pi':p,'rho':r,'output':q,'source_occurrences':oc,'new_occurrences':out}
   if not out:good+=1
  assert good>0
  count+=1;minimum=min(minimum,good)
 res['completion'].append({'m':m,'inputs':count,'minimum_good_completions':minimum})
for n in range(9):
 hist=Counter();by={}
 for p in permutations(range(1,n+1)):
  b=b12(p);hist[b]+=1;u=mult(p)
  if b in by and by[b][1]!=u and res['scalar_closure_failure'] is None:res['scalar_closure_failure']={'n':n,'b':b,'p':by[b][0],'p_multiplier':by[b][1],'q':p,'q_multiplier':u}
  by[b]=(p,u)
  if n<=6:
   for j in range(n+1):assert b12(p[:j]+(n+1,)+p[j:]) == b+sum(p[k]>max(p[k+1:j],default=0) for k in range(j))
 vals=[hist[i] for i in range(max(hist,default=0)+1)];assert sum(vals)==factorial(n)
 peaked=False;unimodal=True
 for a,c in zip(vals,vals[1:]):
  if c<a:peaked=True
  if peaked and c>a:unimodal=False
 res['D'].append({'n':n,'coefficients':vals,'unimodal':unimodal})
res['inherited_occurrence_identities']=identities
(L/'check-results.json').write_text(json.dumps(res,indent=2));print(json.dumps(res,indent=2))
