import json,itertools,hashlib
from pathlib import Path
L=Path(__file__).resolve().parent
def neigh(v,d):return {v^(1<<i) for i in range(d)}
rows=[]
for d in [5,9,17]:
 ns=[1<<i for i in range(d)];total=0
 # Every active class is a subset of some open neighborhood; cube
 # translation sends that center to zero. Thus these are all local types.
 for mask in range(1,1<<d):
  c=[ns[i] for i in range(d) if mask>>i&1]
  cn=neigh(c[0],d)
  for v in c[1:]:cn.intersection_update(neigh(v,d))
  assert len(c)+len(cn)<=d+1
  total+=1
 rows.append(dict(d=d,nonempty_neighborhood_subsets=total))
constructions=[]
for n in [2,3,4]:
 m=(1<<n)-1;d=m+2
 # Binary Hamming code; last two bits free. No optimizer or solver.
 code=[]
 for x in range(1<<m):
  syndrome=0
  for i in range(m):
   if x>>i&1:syndrome^=i+1
  if syndrome==0:code.append(x)
 D={x|(b<<m) for x in code for b in range(4)}
 assert len(D)==1<<(d-n)
 classes=[{x} for x in sorted(D)]
 classes += [{x for x in range(1<<d) if x not in D and x.bit_count()%2==p} for p in [0,1]]
 assert all(classes)
 color={x:i for i,c in enumerate(classes) for x in c}
 for v in range(1<<d):
  N=neigh(v,d)
  assert any(w in D for w in N)
  assert all(color[v]!=color[w] for w in N)
 assert len(classes)==(1<<(d-n))+2
 constructions.append(dict(n=n,d=d,vertices=1<<d,TD_size=len(D),colors=len(classes)))
gaps=[]
for n in range(2,13):
 d=(1<<n)+1;V=1<<d;g=V//(d-1)
 gap0=2*V-(d+1)*(g+1);gap1=3*V//2+1-(d+1)*g
 assert gap0>0 and gap1>0
 gaps.append(dict(n=n,d=d,gap0_bits=gap0.bit_length(),gap1_bits=gap1.bit_length()))
sources={n:hashlib.sha256((L/'sources'/n).read_bytes()).hexdigest() for n in ['kazemi.pdf','prisms.pdf']}
out=dict(local_types=rows,explicit_colorings=constructions,integer_gap_controls=gaps,primary_hashes=sources,scope='Exact finite diagnostics only; universal argument is in PROOF.md; no novelty inference.')
(L/'checks.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
