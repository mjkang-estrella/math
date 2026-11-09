from pathlib import Path
import json
out=[]
for t in range(1,7):
 m=2*t+1;tests=0;ind=0
 for mask in range(1,1<<m):
  A={i for i in range(m) if mask>>i&1};a=min(A)
  def p(x):
   d=(x-a)%m
   return (a+(d+1 if d%2 else d-1))%m if d else a
  def q(x):return x if x in A or p(x) in A else p(x)
  assert all(p(p(x))==x for x in range(m))
  U=set(range(m))-A
  assert all(q(x) in U and q(q(x))==x and (q(x)==x or (q(x)-x)%m in (1,m-1)) for x in U)
  assert sum(q(x)==x for x in U)<=len(A)-1
  if all((x+1)%m not in A for x in A):
   ind+=1;S=sorted(A);odds=sum(((S[(i+1)%len(S)]-x-1)%m)%2 for i,x in enumerate(S));assert odds<=len(A)-1
  tests+=1
 out.append(dict(t=t,nonempty_deletion_sets=tests,independent_deletion_sets=ind))
Path('receipts/pairing-check.json').write_text(json.dumps(out,indent=2));print(out)
