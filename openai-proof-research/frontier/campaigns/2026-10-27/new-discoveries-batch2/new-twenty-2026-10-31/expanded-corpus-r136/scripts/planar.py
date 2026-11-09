import sys,pathlib,json,random,itertools,time
D=pathlib.Path(__file__).resolve().parents[1];sys.path.insert(0,str(D/'sources/vendor/networkx-networkx-3.4.2'));import networkx as nx
rng=random.Random(136)
def colorcount(g,limit=2):
 n=len(g);col={};count=0
 def rec():
  nonlocal count
  if len(col)==n:count+=1;return
  u=max((u for u in g if u not in col),key=lambda u:(len({col[v] for v in g[u] if v in col}),g.degree(u)))
  used={col[v] for v in g[u] if v in col};mx=max(col.values(),default=-1)
  for c in range(min(mx+2,3)):
   if c not in used:
    col[u]=c;rec();del col[u]
    if count>=limit:return
 rec();return count

def test(g):
 ok,e=nx.check_planarity(g)
 if not ok:return 'nonplanar'
 seen=set();faces=[];emap={}
 for u,v in e.edges():
  if (u,v) not in seen:
   f=e.traverse_face(u,v,seen);fi=len(faces);faces.append(f)
   for a,b in zip(f,f[1:]+f[:1]):emap[a,b]=fi
 bad=any(len(faces[emap[v,u]])<=4 for f in faces if len(f)==3 for u,v in zip(f,f[1:]+f[:1]))
 if bad:return 'has_small_pair'
 if colorcount(g)==1:
  o={'n':len(g),'edges':list(g.edges()),'faces':faces};print('CANDIDATE',json.dumps(o),flush=True);(D/'outputs/planar-candidate.json').write_text(json.dumps(o));return 'candidate'
 return 'multiple_or_no_colorings'
counts={};atlas=[]
for g in nx.graph_atlas_g():
 if len(g)>=4 and min(dict(g.degree()).values())>=3 and nx.node_connectivity(g)>=3:
  result=test(g);counts[result]=counts.get(result,0)+1;atlas.append(len(g))
print('ATLAS',json.dumps({'counts':counts,'orders':{n:atlas.count(n) for n in set(atlas)}}),flush=True)
# Generate stacked triangulations then remove edges, preserving 3-connectivity.
counts={};steps=0
for n in [8,10,12,15,20,25,30]:
 for rep in range(80):
  g=nx.complete_graph(4);faces=[(0,1,2),(0,1,3),(0,2,3),(1,2,3)]
  for v in range(4,n):
   f=faces.pop(rng.randrange(len(faces)));g.add_edges_from((v,u) for u in f);faces.extend((v,f[i],f[(i+1)%3]) for i in range(3))
  # Random flips create nonstacked triangulations, verified by planarity.
  for it in range(3*n):
   a,b=rng.choice(list(g.edges()));common=list(set(g[a])&set(g[b]))
   if len(common)==2 and not g.has_edge(*common):
    g.remove_edge(a,b);g.add_edge(*common)
    if not nx.check_planarity(g)[0]:g.remove_edge(*common);g.add_edge(a,b)
  for a,b in rng.sample(list(g.edges()),g.number_of_edges()):
   if min(g.degree(a),g.degree(b))<=3:continue
   g.remove_edge(a,b)
   if nx.node_connectivity(g)<3:g.add_edge(a,b)
   else:
    result=test(g);steps+=1;counts[result]=counts.get(result,0)+1
  result=test(g);counts[result]=counts.get(result,0)+1
 print('RANDOM',n,steps,json.dumps(counts),flush=True)
(D/'outputs/planar.json').write_text(json.dumps({'atlas_count':len(atlas),'random_steps':steps,'random_counts':counts},indent=2)+'\n')
