"""Exact integer diagnostic on Putman's public graph; not an UNSAT replay."""
import pathlib,json,hashlib,random,time
L=pathlib.Path(__file__).parent
F=[(0,1),(0,5),(1,2),(1,6),(2,7),(3,5),(3,6),(4,6),(4,7),(5,7)];C=[(0,1),(0,2),(0,3)]
FE=(0,2,3,4);CE=(3,1,1,2,2,3)
joins=[((0,0),(3,2)),((0,2),(4,0)),((0,3),(4,1)),((1,1),(4,2)),((1,0),(4,3)),((2,0),(4,4)),((3,0),(4,5)),((1,2),(2,1)),((2,2),(3,1))]
def build(parts,joins,ports):
 edges=[];ends=[];offset=0
 for es,ps,n in parts:
  edges.extend((a+offset,b+offset) for a,b in es);ends.append([p+offset for p in ps]);offset+=n
 edges.extend((ends[a][i],ends[b][j]) for (a,i),(b,j) in joins)
 return edges,[ends[a][i] for a,i in ports],offset
le,lp,ln=build([(F,FE,8)]*4+[(C,CE,4)],joins,[(0,1),(1,3),(2,3),(3,3)])
gj=[((0,0),(2,2)),((0,1),(1,1)),((0,2),(3,0)),((0,3),(3,1)),((1,0),(3,2)),((1,2),(3,4)),((2,1),(3,3)),((2,0),(3,5)),((1,3),(2,3))]
es,ps,n=build([(le,lp,ln)]*3+[(C,CE,4)],gj,[]);edges=sorted(tuple(sorted(e)) for e in es);assert len(set(edges))==168 and n==112
def perm(x):
 for lo,hi,k in [(0,7,0),(8,31,4),(32,35,-24),(36,43,4),(44,67,8),(68,71,-20),(72,79,4),(80,103,8),(104,107,-20),(108,111,-72)]:
  if lo<=x<=hi:return x+k
ref=sorted(tuple(sorted((perm(a),perm(b)))) for a,b in edges);digest=hashlib.sha256(json.dumps(ref,separators=(',',':')).encode()).hexdigest();assert digest=='dc16cc18600cf77c8661b7baf89c7019f265299308541961ff884ea7187b4e8b'
inc=[[i for i,e in enumerate(edges) if v in e] for v in range(n)];assert all(len(x)==3 for x in inc)
def connected(skip=-1):
 seen={0};todo=[0]
 while todo:
  v=todo.pop()
  for i in inc[v]:
   if i==skip:continue
   a,b=edges[i];w=a+b-v
   if w not in seen:seen.add(w);todo.append(w)
 return len(seen)==n
assert connected() and all(connected(i) for i in range(168))
r=random.Random(253);c=[-1]*168
# Cubic greedy with five colors always succeeds: at most four forbidden colors.
for i,(a,b) in enumerate(edges):c[i]=r.choice(sorted(set(range(5))-{c[j] for v in (a,b) for j in inc[v]}))
def bad(c):
 palettes=[set(c[i] for i in t) for t in inc]
 return sum(len(palettes[a]|palettes[b])==4 for a,b in edges)
best=c[:];score=bestscore=bad(c);start=time.monotonic();steps=0;milestones=[]
for step in range(120000):
 if time.monotonic()-start>65:break
 a,b=r.sample(range(5),2);seed=r.randrange(168)
 if c[seed] not in (a,b):continue
 comp={seed};todo=[seed]
 while todo:
  i=todo.pop()
  for v in edges[i]:
   for j in inc[v]:
    if j not in comp and c[j] in (a,b):comp.add(j);todo.append(j)
 for i in comp:c[i]=a+b-c[i]
 new=bad(c);steps+=1
 if new<=score or r.randrange(200)==0:score=new
 else:
  for i in comp:c[i]=a+b-c[i]
 if score<bestscore:
  best=c[:];bestscore=score;milestones.append([step,bestscore])
 if bestscore<=2:break
assert all(len({best[i] for i in t})==3 for t in inc)
out={'reference_sha256':digest,'simple_connected_bridgeless_cubic':True,'best_abnormal_count':bestscore,'steps':steps,'milestones':milestones,'edges':edges,'colors':best,'seconds':time.monotonic()-start,'meaning':'bounded diagnostic; public noncolorability certificates not replayed; no universal conclusion'}
(L/'construction-results.json').write_text(json.dumps(out,indent=2));print({k:v for k,v in out.items() if k not in ['edges','colors']})
