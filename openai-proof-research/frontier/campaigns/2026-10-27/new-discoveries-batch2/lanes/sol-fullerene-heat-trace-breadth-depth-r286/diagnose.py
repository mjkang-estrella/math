from pathlib import Path
import sys,json,random,itertools,time
L=Path(__file__).resolve().parent
sys.path.insert(0,str(Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/experiments/i25_matching_entropy_improvement/vendor')))
import networkx as nx
try:import numpy as np
except ImportError as e:print(e);raise
I=nx.icosahedral_graph();_,emb=nx.check_planarity(I);seen=set();faces=[]
for a,b in emb.edges():
 if (a,b) not in seen:faces.append(emb.traverse_face(a,b,seen))
G=nx.Graph();G.add_nodes_from(range(32))
for i,f in enumerate(faces):
 for v in f:G.add_edge(v,12+i)
for i,f in enumerate(faces):
 for j,g in enumerate(faces[:i]):
  if len(set(f)&set(g))==2:G.add_edge(12+i,12+j)
def valid(H):
 ok,em=nx.check_planarity(H)
 if not ok or not nx.is_connected(H) or nx.node_connectivity(H)<3:return False
 se=set();fs=[]
 for a,b in em.edges():
  if (a,b) not in se:fs.append(em.traverse_face(a,b,se))
 return all(len(f)==3 for f in fs) and sorted(dict(H.degree()).values())==[5]*12+[6]*20
assert valid(G)
rng=random.Random(286);graphs=[];keys=set();start=time.monotonic()
for it in range(14000):
 if it%300==0:H=G.copy()
 choices=[]
 for a,b in H.edges():
  if H.degree(a)==H.degree(b)==6:
   cs=list(set(H[a])&set(H[b]))
   if len(cs)==2 and all(H.degree(c)==5 for c in cs) and not H.has_edge(*cs):choices.append((a,b,*cs))
 if not choices:continue
 a,b,c,d=rng.choice(choices);H.remove_edge(a,b);H.add_edge(c,d)
 key=nx.weisfeiler_lehman_graph_hash(H,iterations=5)
 if key in keys:continue
 keys.add(key);graphs.append(H.copy())
 if len(graphs)>=600:break
print('graphs',len(graphs),flush=True)
params=[(.02,.02),(.9,.02),(.02,.9),(.9,.9),(.5,.25)]
values=[]
fingerprints={};pencil_hits=[]
for H in graphs:
 A=nx.to_numpy_array(H,nodelist=range(32));D=np.diag(A.sum(axis=1));values.append([float(np.exp(np.linalg.eigvalsh(a*A+b*D)).sum()) for a,b in params])
 A=A.astype('int64');D=D.astype('int64');fp=[]
 for t in [0,1,2]:
  M=A+t*D;P=np.eye(32,dtype='int64')
  for k in range(1,9):P=P@M;fp.append(int(np.trace(P)))
 key=tuple(fp)
 if key in fingerprints:pencil_hits.append([fingerprints[key],len(values)-1])
 fingerprints[key]=len(values)-1
pair=None
for i in range(len(graphs)):
 for j in range(i):
  dif=[values[i][k]-values[j][k] for k in range(len(params))]
  if min(dif)<-1e-7 and max(dif)>1e-7:pair=(i,j,dif);break
 if pair:break
out=dict(status='finite floating screening only',graphs=len(graphs),iterations=it,params=params,pair=pair,seconds=time.monotonic()-start)
out['pencil_filter']=dict(exact_integer_moments='k=1..8, t=0,1,2 for A+tD',possible_pairs=pencil_hits,overflow_bound='32*18^8 < 2^63',scope='WL-deduplicated random walk, not exhaustive enumeration; polynomial identity would imply these equalities')
resolved=[]
for i,j in pencil_hits:
 mismatch=None
 for t in range(33):
  mats=[]
  for h in [graphs[i],graphs[j]]:
   A=nx.to_numpy_array(h,nodelist=range(32),dtype=int).astype(object);mats.append(A+t*np.diag(A.sum(axis=1)))
  powers=[np.eye(32,dtype=object),np.eye(32,dtype=object)]
  for k in range(1,33):
   powers=[p@m for p,m in zip(powers,mats)];tr=[int(np.trace(p)) for p in powers]
   if tr[0]!=tr[1]:mismatch=dict(t=t,k=k,traces=list(map(str,tr)));break
  if mismatch:break
 resolved.append(dict(pair=[i,j],mismatch=mismatch,nonisomorphic=not nx.is_isomorphic(graphs[i],graphs[j])))
out['pencil_filter']['full_followup']=resolved
if pair:
 i,j,_=pair
 out['valid']=[valid(graphs[k]) for k in [i,j]];out['nonisomorphic']=not nx.is_isomorphic(graphs[i],graphs[j])
 for label,k in [('G',i),('H',j)]: (L/(label+'-edges.json')).write_text(json.dumps(sorted(map(list,graphs[k].edges()))))
(L/'floating-screen.json').write_text(json.dumps(out,indent=2));print(json.dumps(out))
