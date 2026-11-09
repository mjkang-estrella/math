"""Exact bounded diagnostic for the one-Kempe-change repair proposal; no universal certificate."""
import itertools,json,pathlib,time,collections
L=pathlib.Path(__file__).parent;start=time.monotonic();out=[]
graphs={'K4':[(a,b) for a in range(4) for b in range(a+1,4)],'K33':[(a,b) for a in range(3) for b in range(3,6)],'cube':[(a,a^(1<<j)) for a in range(8) for j in range(3) if a<(a^(1<<j))],'Petersen':[(i,(i+1)%5) for i in range(5)]+[(i,i+5) for i in range(5)]+[(i+5,((i+2)%5)+5) for i in range(5)]}
for name,edges in graphs.items():
 edges=sorted(tuple(sorted(e)) for e in edges);n=1+max(max(e) for e in edges);inc=[[i for i,e in enumerate(edges) if v in e] for v in range(n)];assert all(len(t)==3 for t in inc)
 def bad(c):
  palettes=[set(c[i] for i in es) for es in inc]
  return [i for i,(a,b) in enumerate(edges) if len(palettes[a]|palettes[b])==4]
 def moves(c):
  for a,b in itertools.combinations(range(5),2):
   rem={i for i,x in enumerate(c) if x in (a,b)}
   while rem:
    comp={rem.pop()};todo=list(comp)
    while todo:
     i=todo.pop()
     for v in edges[i]:
      for j in inc[v]:
       if j in rem:rem.remove(j);comp.add(j);todo.append(j)
    d=list(c)
    for i in comp:d[i]=a+b-c[i]
    yield tuple(d)
 stats={'name':name,'edges':edges,'nodes':0,'proper':0,'two_defect':0,'one_step_fail':None,'bounded':False};c=[-1]*len(edges);used=[set() for _ in range(n)]
 def visit(k,mx):
  stats['nodes']+=1
  if stats['nodes']>2000000 or time.monotonic()-start>70:stats['bounded']=True;return True
  if k==len(edges):
   stats['proper']+=1
   if len(bad(c))!=2:return False
   stats['two_defect']+=1
   if any(not bad(d) for d in moves(tuple(c))):return False
   witness=tuple(c);q=collections.deque([(witness,0)]);seen={witness};depth=None
   while q and len(seen)<30000:
    d,t=q.popleft()
    if not bad(d):depth=t;break
    if t<3:
     for e in moves(d):
      if e not in seen:seen.add(e);q.append((e,t+1))
   stats['one_step_fail']={'colors':witness,'abnormal_edges':bad(c),'distance_if_found':depth,'bfs_states':len(seen)};return True
  a,b=edges[k]
  for x in range(min(4,mx+1)+1):
   if x in used[a] or x in used[b]:continue
   c[k]=x;used[a].add(x);used[b].add(x)
   stop=visit(k+1,max(mx,x))
   used[a].remove(x);used[b].remove(x);c[k]=-1
   if stop:return True
  return False
 visit(0,-1);out.append(stats)
(L/'repair-results.json').write_text(json.dumps(out,indent=2));print(json.dumps(out,indent=2));print('seconds',time.monotonic()-start)
