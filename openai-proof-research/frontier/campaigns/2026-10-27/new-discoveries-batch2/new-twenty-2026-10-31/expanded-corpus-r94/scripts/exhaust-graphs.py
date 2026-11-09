from graphlib import dist,GP,D,rng
import itertools as it,json,time
out=[]
for n in range(1,7):
 edges=list(it.combinations(range(n),2));count=conn=tfree=0;no_terminal=[];no_label=[];hist={}
 for mask in range(1<<len(edges)):
  a=[set()for _ in range(n)]
  for b,(i,j) in enumerate(edges):
   if mask>>b&1:a[i].add(j);a[j].add(i)
  count+=1;d=dist(a)
  if max(d[0])<999:
   conn+=1;g=GP(d);terminal=False
   for s in range(1,1<<n):
    if g.check([v for v in range(n)if s>>v&1])[1]:terminal=True;break
   if not terminal:no_terminal.append(mask)
  if len({tuple(sorted(s))for s in a})==n:
   tfree+=1;ok=False
   for p in it.permutations(range(1,n+1)):
    if len({sum(p[v]for v in s)for s in a})==n:ok=True;break
   if not ok:no_label.append(mask)
 r=dict(n=n,labelled_graphs=count,connected=conn,twin_free=tfree,no_terminal=no_terminal,no_antimagic=no_label);out.append(r);print(r,flush=True)
 (D/'outputs/exhaust-graphs.json').write_text(json.dumps(out,indent=2)+'\n')
