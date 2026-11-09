# Independently written from Definition 2.1; no discovery code imported.
import json,itertools,collections,pathlib
P=pathlib.Path(__file__).resolve().parents[1]
D=P.parent/'expanded-corpus-r153'
edges=[(0,3),(0,6),(0,14),(1,2),(1,9),(1,16),(2,5),(2,16),(3,7),(3,14),(4,6),(4,12),(4,15),(5,9),(5,13),(6,11),(7,8),(7,11),(8,10),(8,17),(9,12),(10,11),(10,14),(12,15),(13,16),(13,17),(15,17)]
a=[[0]*18 for _ in range(18)]
for i,j in edges:a[i][j]=a[j][i]=2
def freeze(a):return tuple(map(tuple,a))
def valid(a):
 n=len(a)
 assert all(len(r)==n and sum(r)==6 for r in a)
 assert all(a[i][i]==0 and all(a[i][j]==a[j][i]>=0 for j in range(n)) for i in range(n))
def wyes(a):return [i for i,r in enumerate(a) if sorted(x for x in r if x)==[2,2,2]]
def down(a,x):
 assert x in wyes(a)
 keep=[i for i in range(len(a)) if i!=x]
 r=[[a[i][j]+int(i!=j and a[x][i]==2 and a[x][j]==2) for j in keep] for i in keep]
 valid(r);return freeze(r)
def up(a,t):
 assert len(set(t))==3 and all(a[i][j]>0 for i,j in itertools.combinations(t,2))
 n=len(a);r=[list(row)+[0] for row in a]+[[0]*(n+1)]
 for i,j in itertools.combinations(t,2):r[i][j]-=1;r[j][i]-=1
 for i in t:r[i][n]=r[n][i]=2
 valid(r);return freeze(r)
def triangles(a):return [t for t in itertools.combinations(range(len(a)),3) if all(a[i][j]>0 for i,j in itertools.combinations(t,2))]
def endpoint(a,i):return sorted(x for x in a[i] if x)==[1,1,2,2]
def internal(a,i):return sorted(x for x in a[i] if x)==[1,1,1,1,2]
def chain(a):
 # Restricted diagnostic only; NOT sound for the source's vertex-coincidence convention.
 ends=[i for i in range(len(a)) if endpoint(a,i)]
 elig=[i for i in range(len(a)) if endpoint(a,i) or internal(a,i)]
 first=[(i,j,k) for i in ends for j in elig for k in range(len(a)) if len({i,j,k})==3 and a[i][j]==a[i][k]==a[j][k]==1]
 return {'endpoints':ends,'internal':[i for i in elig if i not in ends],'possible_first_triangles':first}
a=freeze(a);valid(a)
assert a==freeze(json.loads((D/'outputs/delta-trace-checked.json').read_text())['original'])
seen={a};todo=[a];arcs=0;counts=collections.Counter()
while todo:
 g=todo.pop();counts[len(g)]+=1
 for x in wyes(g):
  h=down(g,x);arcs+=1
  if h not in seen:seen.add(h);todo.append(h)
b=min(map(len,seen));mins=sorted(g for g in seen if len(g)==b)
g=a;pure=[]
for x in [0,0,3,4,6,7,11]:g=down(g,x);pure.append(g)
G=g;assert g in seen
ops=[('up',(0,5,7)),('up',(1,6,8)),('down',6),('down',10),('up',(4,7,10)),('up',(3,7,10)),('down',10),('down',7),('down',9)]
trace=[]
for op,arg in ops:
 g=up(g,arg) if op=='up' else down(g,arg)
 trace.append({'op':op,'arg':arg,'order':len(g),'graph':g})
# Map reindexing back to persistent original Gprime names for every move.
names=list(range(11));nextname=11;provenance=[]
for op,arg in ops:
 provenance.append([op,[names[i] for i in arg] if op=='up' else names[arg]])
 if op=='up':names.append(nextname);nextname+=1
 else:names.pop(arg)
r={'states':len(seen),'arcs':arcs,'orders':dict(sorted(counts.items())),'min_order':b,'minimum_states':len(mins),'Gprime':G,'chain_obstruction':chain(G),'minimum_chain_obstructions':[chain(h) for h in mins],'all_minima_first_step_blocked':all(not chain(h)['possible_first_triangles'] for h in mins),'triangles':triangles(G),'pure_trace':pure,'nine_move_trace':trace,'persistent_label_operations':provenance}
assert (len(seen),arcs,b,len(g))==(2328,9846,11,10)
(P/'recomputation.json').write_text(json.dumps(r,indent=2)+'\n')
print(json.dumps({k:v for k,v in r.items() if k not in ['pure_trace','nine_move_trace','minimum_chain_obstructions','Gprime']},indent=2))
def findchain(a):
 ends=[i for i in range(len(a)) if endpoint(a,i)]
 middle=[i for i in range(len(a)) if internal(a,i)]
 def walk(i,visited,used):
  for j in ends+middle:
   if j==i or j in visited:continue
   for k in range(len(a)):
    if len({i,j,k})<3 or not a[i][j]==a[i][k]==a[j][k]==1:continue
    ed={tuple(sorted(e)) for e in [(i,j),(i,k),(j,k)]}
    if ed&used:continue
    if j in ends:return [(i,j,k)]
    res=walk(j,visited|{j},used|ed)
    if res:return [(i,j,k)]+res
  return None
 for i in ends:
  res=walk(i,{i},set())
  if res:return res
 return None
# Literal source Figure 14 graph templates, digit names are schematic vertices.
def template(core,doubles):
 E=collections.Counter(tuple(sorted(e)) for t in core for e in itertools.combinations(t,2))
 for i,j in doubles:E[tuple(sorted((i,j)))]+=2
 return E
patterns={
 'c':template([(0,1,2),(0,1,3)],[(0,4),(1,5),(3,6),(3,7)]),
 'e':template([(0,1,2),(0,3,4),(0,5,6)],[(1,7),(1,8),(4,9),(4,10),(6,11),(6,12)]),
 'f':template([(0,1,2),(0,1,3),(1,4,5)],[(0,6),(3,7),(3,8),(4,9),(4,10)]),
 'g':template([(0,1,2),(0,1,3),(3,4,5)],[(0,6),(1,7),(5,8),(5,9)])}
def match(pattern,a):
 # Non-induced edge-injective homomorphisms: vertex coincidences permitted.
 verts=sorted({v for e in pattern for v in e});deg={v:sum(m for e,m in pattern.items() if v in e) for v in verts}
 order=sorted(verts,key=lambda v:(-deg[v],v));assigned={};used=collections.Counter()
 def go(k):
  if k==len(order):return dict(assigned)
  v=order[k]
  for w in range(len(a)):
   updates=collections.Counter();ok=True
   for u,z in assigned.items():
    m=pattern[tuple(sorted((u,v)))]
    if not m:continue
    e=tuple(sorted((w,z)))
    updates[e]+=m
    if w==z or used[e]+updates[e]>a[w][z]:ok=False;break
   if not ok:continue
   # Incident degree required at any merged image cannot exceed six.
   if deg[v]+sum(deg[u] for u,z in assigned.items() if z==w)>6:continue
   assigned[v]=w
   for e,m in updates.items():used[e]+=m
   res=go(k+1)
   if res:return res
   for e,m in updates.items():used[e]-=m
   del assigned[v]
  return None
 return go(0)
chains=[findchain(h) for h in mins]
r['minimum_chains']=chains;r['chain_free_minima']=sum(c is None for c in chains)
r['figure14_matches']={name:match(pat,G) for name,pat in patterns.items()}
# Remove the commuting inverse pair up(0,5,7), down(new11) from the supplied trace.
# Persistent name operations make a seven-move witness without this detour.
h=G;names=list(range(11));new=12;seven=[]
for op,arg in provenance[1:3]+provenance[4:]:
 arg0=tuple(names.index(i) for i in arg) if op=='up' else names.index(arg)
 h=up(h,arg0) if op=='up' else down(h,arg0)
 seven.append([op,arg0,len(h)])
 if op=='up':names.append(new);new+=1
 else:names.pop(arg0)
assert len(h)==10
r['seven_move_witness']=seven
(P/'recomputation.json').write_text(json.dumps(r,indent=2)+'\n')
print('chains',sum(c is not None for c in chains),'chain_free',r['chain_free_minima'])
print('figure_matches',r['figure14_matches'])
print('seven_move_witness',seven)
r['figure_matches_along_trace']=[{name:match(pat,freeze(step['graph'])) for name,pat in patterns.items()} for step in trace]
# Diagnostic only: independence number is not used as a substitute for DAG closure.
indsets=[]
for mask in range(1<<18):
 if all(not(mask>>i&1 and mask>>j&1) for i,j in edges):indsets.append(mask)
r['independence_number']=max(m.bit_count() for m in indsets)
r['maximum_independent_sets']=sum(m.bit_count()==r['independence_number'] for m in indsets)
(P/'recomputation.json').write_text(json.dumps(r,indent=2)+'\n')
print('gadget_matches_along_trace',r['figure_matches_along_trace'])
print('independence',r['independence_number'],r['maximum_independent_sets'])
def faithful_chain(a):
 n=len(a);ends={i for i in range(n) if endpoint(a,i)}
 def reserve(used,items):
  out=used.copy()
  for i,j,m in items:
   if i==j:return None
   e=tuple(sorted((i,j)));out[e]+=m
   if out[e]>a[i][j]:return None
  return out
 def endattachments(i):return [(i,j,2) for j in range(n) if a[i][j]==2]
 def walk(i,cores,used,tri,attachments):
  for j in range(n):
   if j in cores:continue
   for k in range(n):
    if len({i,j,k})!=3:continue
    nxt=reserve(used,[(i,j,1),(i,k,1),(j,k,1)])
    if nxt is None:continue
    if j in ends:
     if reserve(nxt,endattachments(j)) is not None:
      return {'triangles':tri+[(i,j,k)],'double_attachments':attachments+endattachments(j)}
    # j can be internal even when also an actual endpoint: no artificial incidence type.
    for z in range(n):
     more=reserve(nxt,[(j,z,2)])
     if more is not None:
      res=walk(j,cores|{j},more,tri+[(i,j,k)],attachments+[(j,z,2)])
      if res:return res
  return None
 for i in ends:
  res=walk(i,{i},reserve(collections.Counter(),endattachments(i)),[],endattachments(i))
  if res:return res
 return None
r['faithful_chain_Gprime']=faithful_chain(G)
r['faithful_chains_all_minima']=[faithful_chain(h) for h in mins]
r['faithful_chain_free_minima']=sum(x is None for x in r['faithful_chains_all_minima'])
(P/'recomputation.json').write_text(json.dumps(r,indent=2)+'\n')
print('faithful_chain_Gprime',r['faithful_chain_Gprime'])
print('faithful_chain_free_minima',r['faithful_chain_free_minima'])
control=template([(0,1,3),(1,2,4)],[(0,5),(0,6),(1,3),(2,7),(2,8)])
ct=[[0]*9 for _ in range(9)]
for (i,j),m in control.items():ct[i][j]=ct[j][i]=m
assert faithful_chain(ct) is not None
assert internal(ct,1)==False
r['alias_control']={'matrix':ct,'chain':faithful_chain(ct),'lane_internal_test_on_middle':internal(ct,1)}
(P/'recomputation.json').write_text(json.dumps(r,indent=2)+'\n')
print('alias_control_pass',r['alias_control']['chain'])
assert all(sum(v==2 for v in row)==3 and set(row)<={0,2} for row in a)
colours={0:0};stack=[0];bipartite=True
while stack:
 v=stack.pop()
 for w in range(18):
  if not a[v][w]:continue
  if w not in colours:colours[w]=1-colours[v];stack.append(w)
  elif colours[w]==colours[v]:bipartite=False
assert len(colours)==18 and not bipartite
r['initial_hypotheses']={'doubled_simple_cubic':True,'connected':True,'bipartite':bipartite}
(P/'recomputation.json').write_text(json.dumps(r,indent=2)+'\n')
print('initial_hypotheses',r['initial_hypotheses'])
