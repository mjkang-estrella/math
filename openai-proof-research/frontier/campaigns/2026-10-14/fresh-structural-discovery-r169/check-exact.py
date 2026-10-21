from fractions import Fraction as Q
from itertools import product
from pathlib import Path
import json
R=Path('frontier/campaigns/2026-10-14/fresh-structural-discovery-r169')
def walsh(t):
 a=list(t);h=1
 while h<len(a):
  for i in range(0,len(a),2*h):
   for j in range(i,i+h):a[j],a[j+h]=a[j]+a[j+h],a[j]-a[j+h]
  h*=2
 return a
def deg(t):return max((s.bit_count() for s,c in enumerate(walsh(t)) if c),default=0)
def lin(t):
 w=walsh(t);n=len(t).bit_length()-1
 return [Q(w[1<<i],len(t)) for i in range(n)]
def influences(t):
 n=len(t).bit_length()-1
 return [Q(sum(t[x]!=t[x^(1<<i)] for x in range(len(t))),len(t)) for i in range(n)]
def compose(f,g):
 m=len(f).bit_length()-1;n=len(g).bit_length()-1
 return [f[sum((g[(x>>(i*n))&((1<<n)-1)]==-1)<<i for i in range(m))] for x in range(1<<(m*n))]
counts={'all_truth_tables_normalized':0,'balanced_compositions':0,'compression_examples':0,'noise_recursions':0}
for n in [1,2,3]:
 for t in product([-1,1],repeat=1<<n):
  if len(set(t))==1:continue
  w=walsh(t);flip=sum(1<<i for i in range(n) if w[1<<i]<0);f=[t[x^flip] for x in range(1<<n)];mu=Q(sum(f),len(f))
  g=[]
  for x in range(1<<(n+1)):
   y=-1 if x>>n else 1;z=(x&((1<<n)-1))^(((1<<n)-1) if y==-1 else 0);g.append(y*f[z])
  if mu<0:g=[g[x^(1<<n)] for x in range(len(g))]
  assert sum(g)==0 and all(g[x]==-g[x^(len(g)-1)] for x in range(len(g)))
  assert lin(g)[:-1]==lin(f) and lin(g)[-1]==abs(mu)
  d=deg(f);assert deg(g)==d+(d%2==0)
  if sum(lin(g))>1:assert max(influences(g))<1
  counts['all_truth_tables_normalized']+=1
for f in product([-1,1],repeat=4):
 if len(set(f))==1:continue
 for g in product([-1,1],repeat=4):
  if sum(g):continue
  h=compose(f,g)
  assert deg(h)==deg(f)*deg(g)
  assert lin(h)==[a*b for a in lin(f) for b in lin(g)]
  assert influences(h)==[a*b for a in influences(f) for b in influences(g)]
  counts['balanced_compositions']+=1
# Exact degree-raising compression in the text.
f=[];sorted_f=[]
for mask in range(8):
 x=[1-2*((mask>>i)&1) for i in range(3)]
 f.append((x[1]-x[2]+x[0]*x[1]+x[0]*x[2])//2)
 sorted_f.append((x[1]-x[2]+x[0]+x[0]*x[1]*x[2])//2)
assert set(f)=={-1,1} and deg(f)==2 and deg(sorted_f)==3
for mask in range(0,8,2):assert (sorted_f[mask],sorted_f[mask+1])==(max(f[mask],f[mask+1]),min(f[mask],f[mask+1]))
counts['compression_examples']=1
majority=[1 if sum(1-2*((mask>>i)&1) for i in range(3))>0 else -1 for mask in range(8)]
h=compose(majority,majority)
def stab(f,t):return sum(Q(c*c,len(f)**2)*t**s.bit_count() for s,c in enumerate(walsh(f)))
for rho in [Q(1,4),Q(1,2),Q(3,4)]:
 assert stab(h,rho)==stab(majority,stab(majority,rho));counts['noise_recursions']+=1
out=dict(checks=counts,scope='finite exact identities only; no numerical source seed, independent review, formalization, contribution or acceptance',passed=True)
(R/'private/exact-diagnostic.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
