"""Fresh source-definition checker. Standard library only; no prior checker imported."""
from pathlib import Path
import json,itertools as it,collections as co,hashlib,zipfile,stat,shutil,sys
O=Path(__file__).resolve().parents[1]; B=O.parent if '--offline' not in sys.argv and (O.parent/'expanded-corpus-r153').exists() else O/'sources'
E=[(0,3),(0,6),(0,14),(1,2),(1,9),(1,16),(2,5),(2,16),(3,7),(3,14),(4,6),(4,12),(4,15),(5,9),(5,13),(6,11),(7,8),(7,11),(8,10),(8,17),(9,12),(10,11),(10,14),(12,15),(13,16),(13,17),(15,17)]
def frozen(g):return tuple(map(tuple,g))
def valid(g):
 n=len(g);assert all(len(r)==n and sum(r)==6 for r in g)
 assert all(g[i][i]==0 and all(isinstance(g[i][j],int) and g[i][j]>=0 and g[i][j]==g[j][i] for j in range(n)) for i in range(n))
def centres(g):return [i for i,r in enumerate(g) if sorted(x for x in r if x)==[2,2,2]]
def reduce(g,v):
 assert v in centres(g);K=[i for i in range(len(g)) if i!=v]
 h=frozen([[g[i][j]+int(i!=j and g[v][i]==2 and g[v][j]==2) for j in K] for i in K]);valid(h);return h
def expand(g,T):
 assert len(set(T))==3 and all(g[i][j]>0 for i,j in it.combinations(T,2))
 n=len(g);h=[list(r)+[0] for r in g]+[[0]*(n+1)]
 for i,j in it.combinations(T,2):h[i][j]-=1;h[j][i]-=1
 for i in T:h[i][n]=h[n][i]=2
 h=frozen(h);valid(h);return h
G=[[0]*18 for _ in range(18)]
assert len(set(E))==27
for i,j in E:G[i][j]=G[j][i]=2
G=frozen(G);valid(G);assert all(sum(x>0 for x in r)==3 for r in G)
seen={G};todo=[G];arcs=0
while todo:
 g=todo.pop()
 for v in centres(g):
  h=reduce(g,v);arcs+=1
  if h not in seen:seen.add(h);todo.append(h)
counts=co.Counter(map(len,seen));minimum=min(counts);mins=sorted(g for g in seen if len(g)==minimum)
D=json.loads((B/'expanded-corpus-r153/outputs/pure-dag.json').read_text());nodes=D['nodes'];N=[frozen(n['graph']) for n in nodes]
assert len(N)==len(set(N)) and set(N)==seen and N[D['root']]==G
for k,node in enumerate(nodes):
 actual={reduce(N[k],v) for v in centres(N[k])}
 assert sorted(v for v,x in node['children'])==centres(N[k])
 assert all(reduce(N[k],v)==N[x] for v,x in node['children'])
 # Arc census counts legal centres even when target matrices coincide.
 supplied={N[x] for v,x in node['children']}
 assert actual==supplied and all(len(N[x])==len(N[k])-1 for v,x in node['children'])
assert sum(len(centres(g)) for g in N)==arcs
pure=[G];g=G
for v in [0,0,3,4,6,7,11]:g=reduce(g,v);pure.append(g)
H=g;ops=[('expand',[1,6,8]),('reduce',6),('expand',[4,7,10]),('expand',[3,7,10]),('reduce',10),('reduce',7),('reduce',9)];trace=[H]
for op,arg in ops:g=expand(g,arg) if op=='expand' else reduce(g,arg);trace.append(g)
def ends(g):return [i for i,r in enumerate(g) if sorted(x for x in r if x)==[1,1,2,2]]
def haschain(g):
 n=len(g);end=ends(g)
 def take(cap,edges):
  a=[list(r) for r in cap]
  for i,j,m in edges:
   if i==j or a[i][j]<m:return None
   a[i][j]-=m;a[j][i]-=m
  return a
 def attachments(v):return [(v,j,2) for j in range(n) if g[v][j]==2]
 def step(v,bases,cap):
  for w in range(n):
   if w in bases:continue
   for a in range(n):
    if len({v,w,a})<3:continue
    c=take(cap,[(v,w,1),(v,a,1),(w,a,1)])
    if c is None:continue
    if w in end and take(c,attachments(w)) is not None:return True
    for z in range(n):
     d=take(c,[(w,z,2)])
     if d is not None and step(w,bases|{w},d):return True
  return False
 return any(step(v,{v},take(g,attachments(v))) for v in end)
assert not any(haschain(h) for h in mins)
# Positive chain controls, including an internal attachment sharing a triple pair.
control=[[0]*9 for _ in range(9)]
for tri in [(0,1,3),(1,2,4)]:
 for i,j in it.combinations(tri,2):control[i][j]+=1;control[j][i]+=1
for i,j in [(0,5),(0,6),(1,3),(2,7),(2,8)]:control[i][j]+=2;control[j][i]+=2
assert haschain(control) and control[1][3]==3
assert all(sum(control[i])==6 for i in [0,1,2])
# Known non-chain Figure 14 templates; coincidences allowed, edges consume capacity.
def template(tris,att):
 c=co.Counter(tuple(sorted(e)) for t in tris for e in it.combinations(t,2))
 for e in att:c[tuple(sorted(e))]+=2
 return c
patterns={'c':template([(0,1,2),(0,1,3)],[(0,4),(1,5),(3,6),(3,7)]),'e':template([(0,1,2),(0,3,4),(0,5,6)],[(1,7),(1,8),(4,9),(4,10),(6,11),(6,12)]),'f':template([(0,1,2),(0,1,3),(1,4,5)],[(0,6),(3,7),(3,8),(4,9),(4,10)]),'g':template([(0,1,2),(0,1,3),(3,4,5)],[(0,6),(1,7),(5,8),(5,9)])}
def match(p,g):
 V={x for e in p for x in e};deg={v:sum(m for e,m in p.items() if v in e) for v in V};order=sorted(V,key=lambda v:(-deg[v],v));f={};used=co.Counter()
 def go(k):
  if k==len(order):return dict(f)
  v=order[k]
  for w in range(len(g)):
   if deg[v]+sum(deg[u] for u,z in f.items() if z==w)>6:continue
   add=co.Counter()
   for u,z in f.items():add[tuple(sorted((w,z)))]+=p[tuple(sorted((u,v)))]
   if any(m and (i==j or used[i,j]+m>g[i][j]) for (i,j),m in add.items()):continue
   f[v]=w;used.update(add);r=go(k+1)
   if r is not None:return r
   used.subtract(add);del f[v]
  return None
 return go(0)
fig0={k:match(p,H) for k,p in patterns.items()};fig1={k:match(p,trace[1]) for k,p in patterns.items()}
print('figure checks',fig0,fig1)
assert all(v is None for v in fig0.values()) and fig1['c'] is not None
nine1=expand(H,[0,5,7]);nine2=expand(nine1,[1,6,8]);fig9={k:match(p,nine2) for k,p in patterns.items()};assert fig9['c'] is not None and fig9['g'] is not None
assert (len(seen),arcs,minimum,len(mins),len(g))==(2328,9846,11,25,10)
# Snapshot packet, safe extraction without executing any content.
zsrc=B/'delta-formal-r3/source.zip'
if not zsrc.exists():zsrc=O/'lean-source.zip'
sha=hashlib.sha256(zsrc.read_bytes()).hexdigest();assert sha=='c0dba5dc4f6738531b09750bd5e6f46ba565ba952f50fbe927e4f9cfe4a0e08c'
if zsrc.resolve()!=(O/'lean-source.zip').resolve():shutil.copyfile(zsrc,O/'lean-source.zip')
target=O/'packet-safe-test';serial=0
while target.exists():serial+=1;target=O/f'packet-safe-test-{serial}'
target.mkdir()
with zipfile.ZipFile(zsrc) as z:
 names=z.namelist();assert len(names)==len(set(names))
 for info in z.infolist():
  p=Path(info.filename);assert not p.is_absolute() and '..' not in p.parts and not stat.S_ISLNK(info.external_attr>>16)
  assert (target/p).resolve().is_relative_to(target.resolve())
  if not info.is_dir():
   (target/p).parent.mkdir(parents=True,exist_ok=True);(target/p).write_bytes(z.read(info))
 manifest_checks=0
 for line in (target/'source-files.sha256').read_text().splitlines():
  digest,name=line.split(maxsplit=1);name=name.lstrip('*');p=(target/name).resolve();assert p.is_relative_to(target.resolve()) and hashlib.sha256(p.read_bytes()).hexdigest()==digest;manifest_checks+=1
 modules=sorted(target.rglob('*.lean'));chunks=[p for p in modules if p.stem.startswith('Closure') and p.stem[7:].isdigit()]
 assert len(modules)==634 and len(chunks)==582
 extraction={str(p.relative_to(target)):hashlib.sha256(p.read_bytes()).hexdigest() for p in target.rglob('*') if p.is_file()}
(O/'receipts/safe-extraction.json').write_text(json.dumps({'archive_sha256':sha,'members':len(names),'modules':len(modules),'closure_chunks':len(chunks),'executed':False,'internal_manifest_checked_files':manifest_checks,'files':extraction},indent=2)+'\n')
r={'base_edges':E,'states':len(seen),'legal_move_arcs':arcs,'states_by_order':dict(sorted(counts.items())),'minimum_order':minimum,'labelled_minima':len(mins),'chain_free_minima':len(mins),'end_bases':ends(H),'pure_centres':[0,0,3,4,6,7,11],'pure_orders':list(map(len,pure)),'pure_matrices':pure,'witness_operations':ops,'witness_orders':list(map(len,trace)),'witness_matrices':trace,'figure14_initial':fig0,'figure14_after_first_expansion':fig1,'figure14_nine_trace_after_two_expansions':fig9,'packet_modules':len(modules),'closure_chunks':len(chunks),'safe_members':len(names),'positive_alias_control_pass':True,'all_checks_pass':True}
(O/'recomputation.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps({k:v for k,v in r.items() if 'matrices' not in k},indent=2))
