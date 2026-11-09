import numpy as np,random,json,itertools
random.seed(346405)
def tree(edges,n):
 L=np.zeros((n,n))
 for a,b in edges:L[a,a]+=1;L[b,b]+=1;L[a,b]-=1;L[b,a]-=1
 return round(np.linalg.det(L[:-1,:-1]))
def match(v):
 if not v:yield [];return
 a=v[0]
 for b in v[1:]:
  if (a-b)%n in [1,n-1]:continue
  for rest in match([x for x in v if x not in [a,b]]):yield [(a,b)]+rest
out=[]
for n in [8,10,12,14,16,18,20]:
 cyc=[(i,(i+1)%n) for i in range(n)];base=cyc+[(i,i+n//2) for i in range(n//2)];t=tree(base,n);best=t;win=None;cnt=0
 it=match(list(range(n))) if n<=12 else None
 for k in range(20000 if n>=14 else 200000):
  if it is not None:
   try:M=next(it)
   except StopIteration:break
  else:
   v=list(range(n));random.shuffle(v);M=list(zip(v[::2],v[1::2]))
   if any((a-b)%n in [1,n-1] for a,b in M):continue
  cnt+=1;s=tree(cyc+M,n)
  if s>best:best=s;win=M
 row=dict(n=n,FCG_trees=t,best_trees=best,matchings_tested=cnt,matching=win,mode='all perfect matchings avoiding cycle edges' if it is not None else '20000 shuffled trials before adjacency rejection')
 out.append(row);print(row,flush=True)
json.dump(out,open('outputs/reliability.json','w'),indent=2)
