from pathlib import Path
from itertools import permutations
from collections import deque
import random,json
D=Path(__file__).resolve().parents[1]
def red(p):return tuple(sorted(p).index(x) for x in p)
base=[tuple(map(int,s)) for s in '1234 2341 3412 4231 3421 4321 4312 4123'.split()]
ps=list(permutations(range(1,5)));rest=set(ps)-set(base);r=random.Random(2009)
def bad(t):
 L=len(t);g=[set() for _ in t]
 for i,p in enumerate(t):
  for a in range(4):
   for b in range(4):
    if p[a]<p[b]:g[(i+a)%L].add((i+b)%L)
 d=[0]*L
 for es in g:
  for v in es:d[v]+=1
 q=deque(i for i in range(L) if not d[i]);c=0
 while q:
  u=q.popleft();c+=1
  for v in g[u]:
   d[v]-=1
   if not d[v]:q.append(v)
 return c<L
assert bad(base)
found=None;tested=0
for trial in range(20000):
 k=r.randrange(8);start=red(base[k][:-1]);adj={red(p[:-1]):[] for p in ps}
 for p in sorted(rest):adj[red(p[:-1])].append(p)
 for v in adj:r.shuffle(adj[v])
 st=[(start,None)];back=[]
 while st:
  v,p=st[-1]
  if adj[v]:
   e=adj[v].pop();st.append((red(e[1:]),e))
  else:
   _,e=st.pop()
   if e:back.append(e)
 if len(back)!=16:continue
 t=base[:k]+back[::-1]+base[k:];tested+=1
 assert len(set(t))==24 and all(red(p[1:])==red(t[(i+1)%24][:-1]) for i,p in enumerate(t))
 if bad(t):found={'trial':trial,'splice_before_base_index':k,'tour':[''.join(map(str,p)) for p in t]};break
out={'base_nonrealizable':True,'method':'single 16-edge residual Euler excursion spliced into printed 8-edge tour','tested':tested,'found':found,'note':'No discovery scripts imported. A new obstruction is evidence of easy augmentation, not proof of historical publication.'}
(D/'albert-west-augmentation.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
