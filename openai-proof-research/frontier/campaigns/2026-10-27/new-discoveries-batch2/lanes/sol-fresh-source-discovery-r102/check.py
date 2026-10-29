from pathlib import Path
from itertools import combinations
import json,random
P=Path(__file__).resolve().parent
checks=0
def graph(n,edges):
 a=[0]*n
 for x,y in edges:a[x]|=1<<y;a[y]|=1<<x
 return a
def path(a,mask,k):
 if k==0:return True
 def walk(v,seen,left):
  if left==1:return True
  avail=a[v]&mask&~seen
  while avail:
   t=avail&-avail;avail-=t
   if walk(t.bit_length()-1,seen|t,left-1):return True
  return False
 return any(walk(v,1<<v,k) for v in range(len(a)) if mask>>v&1)
def contains(a,s,k):
 full=(1<<len(a))-1
 for C in combinations(range(len(a)),s):
  if not all(a[x]>>y&1 for x,y in combinations(C,2)):continue
  mask=full
  for v in C:mask&=a[v]
  if path(a,mask,k):return True
 return False
def add(a,x,y):
 b=a.copy();b[x]|=1<<y;b[y]|=1<<x;return b
def sat(a,s,k):
 return not contains(a,s,k) and all(contains(add(a,x,y),s,k) for x,y in combinations(range(len(a)),2) if not a[x]>>y&1)
def edges(a):return sum(x.bit_count() for x in a)//2
out={}
# Exact family defeating the necessary-local-condition-only route.
family=[]
for s in range(2,6):
 for k in range(3,8):
  n=s+k+2;a=graph(n,[(x,y) for x,y in combinations(range(n),2) if x<s])
  assert not contains(a,s,k)
  assert all(not contains(add(a,x,y),s,k) for x,y in combinations(range(s,n),2))
  family.append(dict(s=s,k=k,n=n,edges=edges(a),nonedges=(n-s)*(n-s-1)//2));checks+=2
out['local_insufficiency']=family
# Genuine saturated graphs without any universal vertex.
family=[]
for s in range(2,5):
 for k in range(3,6):
  t=(k+1)//2;parts=[t]*(s+1);n=sum(parts);labels=[i for i,z in enumerate(parts) for _ in range(z)]
  a=graph(n,[(x,y) for x,y in combinations(range(n),2) if labels[x]!=labels[y]])
  assert sat(a,s,k);assert max(v.bit_count() for v in a)<n-1;checks+=2
  family.append(dict(s=s,k=k,parts=parts,edges=edges(a)))
out['nonuniversal_saturated']=family
# Exhaustive small cases verify deletion equivalence and basic source endpoint data.
counts={};deletion=0
for n in range(3,7):
 E=list(combinations(range(n),2));best=None;number=0
 for code in range(1<<len(E)):
  a=graph(n,[e for i,e in enumerate(E) if code>>i&1])
  # H_1,3=diamond; universal deletion must preserve saturation in BOTH directions for cones.
  if n<=5:
   base=sat(a,1,3);cone=graph(n+1,[(x,y) for x,y in E if a[x]>>y&1]+[(x,n) for x in range(n)])
   assert base==sat(cone,2,3);deletion+=1
  if n==6 and sat(a,3,3):
   z=edges(a)
   if best is None or z<best:best=z;number=1
   elif z==best:number+=1
 counts[str(n)]={'minimum_H33':best,'number_labeled_minimum':number} if n==6 else {}
assert counts['6']['minimum_H33']==13
out['all_6vertex_H33']=counts['6'];out['deletion_identities']=deletion
# A tempting classification 'every minimum has all three universal center vertices' fails.
a=graph(6,[(x,y) for x,y in combinations(range(6),2) if (x,y) not in [(0,1),(2,3)]])
assert sat(a,3,3) and edges(a)==13 and sum(v.bit_count()==5 for v in a)==2
out['three_universal_classification_obstruction']={'n':6,'missing_edges':[[0,1],[2,3]],'edges':13,'universal_vertices':[4,5]}
out['assertions_at_least']=checks+deletion+2;out['status']='PASS; route diagnostics only, neither full conjecture nor classification proved'
(P/'check-results.json').write_text(json.dumps(out,indent=2));print(json.dumps(out))
# Exact accounting identity at a minimum-degree vertex for genuine saturated multipartite hosts.
identities=[]
for row in out['nonuniversal_saturated']:
 s=row['s'];k=row['k'];parts=row['parts'];labels=[i for i,z in enumerate(parts) for _ in range(z)];n=len(labels)
 a=graph(n,[(x,y) for x,y in combinations(range(n),2) if labels[x]!=labels[y]])
 v=min(range(n),key=lambda x:a[x].bit_count());A=[x for x in range(n) if a[v]>>x&1];B=[x for x in range(n) if x!=v and x not in A];d=len(A);r=d-s
 ea=sum(a[x]>>y&1 for x,y in combinations(A,2));eb=sum(a[x]>>y&1 for x,y in combinations(B,2));ex=sum(sum(a[b]>>x&1 for x in A)-s for b in B)
 charge=ea-s*(s-1)//2+eb+ex
 assert edges(a)==s*n-s*(s+1)//2-(s-1)*r+charge
 assert all(any(all(a[x]>>y&1 for x,y in combinations(C,2)) for C in combinations([x for x in A if a[b]>>x&1],s)) for b in B)
 identities.append(dict(s=s,k=k,n=n,delta=d,r=r,charge=charge));checks+=2
out['charge_identities']=identities;out['assertions_at_least']=checks+deletion+2
(P/'check-results.json').write_text(json.dumps(out,indent=2))
