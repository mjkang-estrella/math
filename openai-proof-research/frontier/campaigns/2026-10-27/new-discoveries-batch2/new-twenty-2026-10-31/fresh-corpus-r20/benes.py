import os,resource,pathlib,itertools,random,json,time
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]);resource.setrlimit(resource.RLIMIT_CPU,(20,20));resource.setrlimit(resource.RLIMIT_AS,(1024**3,1024**3))
p=pathlib.Path(__file__).resolve().parent;edges=set()
def build(n,key):
 ins=[key+':i'+str(i) for i in range(n)];outs=[key+':o'+str(i) for i in range(n)]
 if n==2:
  edges.update(itertools.product(ins,outs));return ins,outs,None
 subs=[build(n//2,key+str(c)) for c in [0,1]]
 for i in range(n):
  for c in [0,1]:edges.add((ins[i],subs[c][0][i//2]));edges.add((subs[c][1][i//2],outs[i]))
 return ins,outs,subs
def route(net,perm):
 ins,outs,subs=net;n=len(ins)
 if n==2:return [[ins[i],outs[perm[i]]] for i in range(n)]
 adj={}
 for i in range(n):
  for v in [('a',i//2),('b',perm[i]//2)]:adj.setdefault(v,[]).append(i)
 col={}
 for first in range(n):
  if first in col:continue
  stack=[(first,0)]
  while stack:
   i,c=stack.pop()
   if i in col:assert col[i]==c;continue
   col[i]=c
   for v in [('a',i//2),('b',perm[i]//2)]:
    for j in adj[v]:
     if i!=j:stack.append((j,1-c))
 subperm=[[None]*(n//2) for _ in [0,1]]
 for i in range(n):subperm[col[i]][i//2]=perm[i]//2
 paths=[route(subs[c],subperm[c]) for c in [0,1]]
 return [[ins[i]]+paths[col[i]][i//2]+[outs[perm[i]]] for i in range(n)]
rng=random.Random(339710);out=[]
for n in [4,16]:
 edges=set();net=build(n,str(n));es=set(edges);cases=list(itertools.permutations(range(n))) if n==4 else [rng.sample(range(n),n) for _ in range(256)]
 records=[]
 for perm in cases:
  paths=route(net,perm);seen=set()
  for i,path in enumerate(paths):
   assert path[0]==net[0][i] and path[-1]==net[1][perm[i]]
   assert len(path)==len(set(path)) and not seen.intersection(path);seen.update(path)
   assert all((u,v) in es for u,v in zip(path,path[1:]))
  records.append({'permutation':perm,'paths':paths})
 out.append({'n':n,'vertices':len(set(v for e in es for v in e)),'arc_count':len(es),'arcs':sorted(es),'cases':records})
(p/'benes.json').write_text(json.dumps(out,indent=2)+'\n');print([(d['n'],d['vertices'],d['arc_count'],len(d['cases'])) for d in out])
