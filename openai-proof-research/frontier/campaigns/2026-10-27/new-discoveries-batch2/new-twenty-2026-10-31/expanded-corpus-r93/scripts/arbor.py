import itertools,math,json,time
from pathlib import Path
D=Path(__file__).resolve().parents[1]
def partitions(n):
 def rec(a):
  if len(a)==n:yield a;return
  for x in range(max(a,default=-1)+2):yield from rec(a+[x])
 yield from rec([])
def comp(total,n):
 if n==1:yield (total,);return
 for i in range(total+1):
  for c in comp(total-i,n-1):yield (i,)+c
out=[]
for n in range(1,6):
 spaces=set()
 for a in partitions(n):
  k=max(a)+1
  for par in itertools.product(range(k),repeat=k-1):
   parents=[-1]+list(par)
   ok=True
   for i in range(1,k):
    seen=set();v=i
    while v!=0:
     if v in seen:ok=False;break
     seen.add(v);v=parents[v]
    if not ok:break
   if not ok:continue
   sets=[]
   for v in range(k):
    desc=[]
    for j in range(k):
     u=j
     while u not in [-1,v]:u=parents[u]
     if u==v:desc.extend(i for i,b in enumerate(a) if b==j)
    sets.append(tuple(desc))
   spaces.add(tuple(sorted(sets)))
 # Quotient variable relabeling to avoid repeating equivalent tests.
 canonical={}
 for ss in spaces:
  sig=min(tuple(sorted(tuple(sorted(p[i] for i in s)) for s in ss)) for p in itertools.permutations(range(n)))
  canonical[sig]=sig
 for ss in canonical:
  L=[]
  for t in range(n+1):
   L.append(sum(all(sum(c[i] for i in s)<=t*len(s) for s in ss) for total in range(t*n+1) for c in comp(total,n)))
  h=[sum((-1)**j*math.comb(n+1,j)*L[i-j] for j in range(i+1)) for i in range(n+1)]
  words=[0]*(n+1)
  for w in itertools.product(range(n),repeat=n):
   if all(sum(w.count(i) for i in s)>=len(s) for s in ss):words[n-1-sum(w[i]>w[i+1] for i in range(n-1))]+=1
  if h!=words:print('COUNTEREXAMPLE',n,ss,h,words,flush=True)
 print(n,len(spaces),len(canonical),'passed',flush=True);out.append([n,len(spaces),len(canonical)])
(D/'outputs/arbor.json').write_text(json.dumps(out))
