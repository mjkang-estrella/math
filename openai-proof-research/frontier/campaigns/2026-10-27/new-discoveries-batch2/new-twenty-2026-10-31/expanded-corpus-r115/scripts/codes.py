from itertools import product
from collections import Counter
from pathlib import Path
import json
D=Path(__file__).resolve().parents[1];N=28

def rank(a):
 piv={}
 for v in a:
  while v:
   b=v.bit_length()
   if b in piv:v^=piv[b]
   else:piv[b]=v;break
 return len(piv)
gram={v:sum((((v>>i)&1)*((v>>j)&1))<<b for b,(i,j) in enumerate([(0,0),(0,1),(0,2),(1,1),(1,2),(2,2)])) for v in range(1,8)}
sr=[rank([i for i in range(1,8) if s>>(i-1)&1]) for s in range(128)]
gr=[]
for g in range(64):
 a=[0,0,0]
 for b,(i,j) in enumerate([(0,0),(0,1),(0,2),(1,1),(1,2),(2,2)]):
  if g>>b&1:a[i]|=1<<j;a[j]|=1<<i
 gr.append(rank(a))
classes={}
for a,b,c in product(range(1,8),repeat=3):
 if rank([a,b,c])!=3:continue
 p={i:(a if i&1 else 0)^(b if i&2 else 0)^(c if i&4 else 0) for i in range(1,8)};seen=set();cy=[]
 for i in range(1,8):
  if i in seen:continue
  members=[];t=i
  while t not in seen:seen.add(t);members.append(t);t=p[t]
  cy.append((len(members),sum(1<<(t-1) for t in members),__import__('functools').reduce(int.__xor__,(gram[t] for t in members),0)))
 key=tuple(sorted(x[0] for x in cy))
 if key not in classes:classes[key]=[0,cy]
 classes[key][0]+=1
counts=[[0]*4 for _ in range(N+1)];coverage=[]
for key,(mult,cy) in classes.items():
 fixed=[[0]*4 for _ in range(N+1)];leaves=[0]
 def rec(j,s,g,sup):
  if j==len(cy):
   leaves[0]+=1
   if sr[sup]==3:fixed[s][3-gr[g]]+=1
   return
  ln,mask,delta=cy[j]
  for t in range((N-s)//ln+1):rec(j+1,s+t*ln,g^(delta if t&1 else 0),sup|(mask if t else 0))
 rec(0,0,0,0)
 for n in range(N+1):
  for h in range(4):counts[n][h]+=mult*fixed[n][h]
 coverage.append(dict(cycle_type=key,multiplicity=mult,histograms=leaves[0]));print(coverage[-1],flush=True)
for n in range(1,N+1):
 for h in range(4):counts[n][h]+=counts[n-1][h]
rows=[]
for n in range(6,N+1):
 assert all(x%168==0 for x in counts[n]);v=[x//168 for x in counts[n]]
 rows.append(dict(n=n,k=3,q=2,B=v,holds=min(v[:2])>v[2]>v[3]))
print(json.dumps(rows,indent=2),flush=True)
(D/'outputs/codes.json').write_text(json.dumps(dict(method='Burnside on binary column multisets under GL(3,2), zero columns included by cumulative sum',coverage=coverage,rows=rows),indent=2)+'\n')
