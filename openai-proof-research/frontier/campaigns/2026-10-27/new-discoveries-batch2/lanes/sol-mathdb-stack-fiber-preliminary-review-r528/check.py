from pathlib import Path
from itertools import permutations,combinations
from collections import Counter,defaultdict
from math import factorial
import json
D=Path(__file__).resolve().parent
# Top at index 0. Previously legal stack: only a newly pushed x can be
# first in a new 1_23 occurrence, so inspect adjacent increasing pairs below x.
def run(p,trace=False):
 s=[];o=[];t=[]
 for x in p:
  while any(x<s[j]<s[j+1] for j in range(len(s)-1)):
   y=s.pop(0);o.append(y)
   if trace:t.append(dict(action='pop/retry',next=x,element=y,stack=s[:],output=o[:]))
  s.insert(0,x)
  if trace:t.append(dict(action='push',element=x,stack=s[:],output=o[:]))
 while s:
  y=s.pop(0);o.append(y)
  if trace:t.append(dict(action='drain',element=y,stack=s[:],output=o[:]))
 return (tuple(o),t) if trace else tuple(o)
# Independent whole-stack legality implementation: bottom at index 0,
# test every triple in proposed stack, with explicit adjacency selector.
def generic(p,adj='last',pat=(1,2,3),reverse=False):
 s=[];o=[]
 for x in p:
  while True:
   v=s+[x];v=v if reverse else v[::-1]
   bad=False
   for i,j,k in combinations(range(len(v)),3):
    if adj=='last' and k!=j+1:continue
    if adj=='first' and j!=i+1:continue
    if adj=='all' and (j!=i+1 or k!=j+1):continue
    a=[v[i],v[j],v[k]];rank=tuple(1+sum(z<y for z in a) for y in a)
    if rank==pat:bad=True;break
   if not bad:s.append(x);break
   o.append(s.pop())
 return tuple(o+s[::-1])
def recperm(xs):
 if not xs:yield ()
 for i,x in enumerate(xs):
  for q in recperm(xs[:i]+xs[i+1:]):yield (x,)+q
example=(5,1,4,3,6,2);assert run(example)==(6,3,2,4,1,5)
controls={}
for adj,want in [('none',(4,6,3,2,1,5)),('all',(2,6,3,4,1,5)),('first',(4,2,6,3,1,5)),('last',(6,3,2,4,1,5))]:
 got=generic(example,adj);assert got==want;controls[adj]=''.join(map(str,got))
assert generic(example,reverse=True)!=run(example)
assert generic(example,pat=(1,3,2))!=run(example)
summary={};traces={};witness={}
for n in [2,3,4,5,8]:
 fib=defaultdict(list);seen=set();lines=[]
 for p in permutations(range(1,n+1)):
  assert len(set(p))==n and set(p)==set(range(1,n+1));assert p not in seen;seen.add(p)
  q=run(p);assert q==generic(p);assert sorted(q)==list(range(1,n+1)) and q[-1]==p[0]
  a=''.join(map(str,p));b=''.join(map(str,q));fib[b].append(a);lines.append(a+' '+b+'\n')
 assert len(seen)==factorial(n)
 if n==5:assert seen==set(recperm(tuple(range(1,6))))
 (D/f'io-n{n}.txt').write_text(''.join(lines))
 hist=Counter(map(len,fib.values()));hist[0]=factorial(n)-len(fib)
 if hist[0]==0:del hist[0]
 sizes=sorted(hist);summary[n]=dict(inputs=len(seen),fiber_histogram=dict(sorted(hist.items())),largest=sizes[-1],second_distinct=(sizes[-2] if len(sizes)>1 else None),maximizers=sorted(q for q,v in fib.items() if len(v)==sizes[-1]),second_outputs=sorted(q for q,v in fib.items() if len(sizes)>1 and len(v)==sizes[-2]))
 if n==5:
  for q in ['32514','32415','43215']:witness[q]=fib[q]
  assert fib['32514']==['41523','41532','42315','43152','43215']
  for p in fib['32514']:traces[p]=run(tuple(map(int,p)),True)[1]
  assert sizes[-2]==5 and len(fib['43215'])==8
 if n==8:
  for q in ['65432817','76543218']:witness[q]=fib[q];assert len(fib[q])==64
(D/'math-results.json').write_text(json.dumps(dict(summary=summary,controls=controls,witnesses=witness),indent=2)+'\n')
(D/'n5-hand-traces.json').write_text(json.dumps(traces,indent=2)+'\n')
print(json.dumps({n:{k:v for k,v in s.items() if k not in ['maximizers','second_outputs']} for n,s in summary.items()}))
