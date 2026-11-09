import os
os.environ['OPENBLAS_NUM_THREADS']='1';os.environ['OMP_NUM_THREADS']='1'
import resource,itertools,json,pathlib,math,time
resource.setrlimit(resource.RLIMIT_AS,(2*1024**3,2*1024**3));resource.setrlimit(resource.RLIMIT_CPU,(80,80))
o=pathlib.Path(__file__).resolve().parent
# Exact squared lengths in triangular lattice (x+y/2,sqrt(3)y/2).
def search(points,triangular):
 def sq(p,q):
  x,y=p[0]-q[0],p[1]-q[1];return x*x+x*y+y*y if triangular else x*x+y*y
 sig={t:tuple(sorted(sq(points[i],points[j]) for i,j in itertools.combinations(t,2))) for t in itertools.combinations(range(len(points)),3)}
 hits=[];count=0;best=100
 for s in itertools.combinations(range(len(points)),7):
  count+=1;seen=set()
  for t in itertools.combinations(s,3):
   seen.add(sig[t])
   if len(seen)>4:break
  if len(seen)<=4:hits.append({'points':[points[i] for i in s],'squared_triangle_signatures':sorted(seen)})
 return {'points':points,'sets_checked':count,'at_most_four_hits':hits,'includes_degenerate_triples':True}
tri=[(x,y) for x in range(-2,3) for y in range(-2,3) if max(abs(x),abs(y),abs(x+y))<=2]
ans={'triangular_radius2':search(tri,True),'square4x4':search(list(itertools.product(range(4),repeat=2)),False)}
hexpts=[(0,0),(1,0),(0,1),(-1,1),(-1,0),(0,-1),(1,-1)];ans['hexagon_center']=search(hexpts,True)
print(json.dumps(ans,indent=2));(o/'geometry-diagnostics.json').write_text(json.dumps(ans,indent=2)+'\n')
# All connected regular graph-atlas graphs; this is a bounded diagnostic, not complete for n>7.
import networkx as nx,numpy as np
by={}
for g in nx.graph_atlas_g():
 n=len(g)
 if n<3 or not nx.is_connected(g):continue
 ds=set(dict(g.degree()).values())
 if len(ds)!=1 or min(ds)<2:continue
 d=next(iter(ds));basis=nx.minimum_cycle_basis(g);girth=min(map(len,basis));a=nx.to_numpy_array(g);ac=float(np.linalg.eigvalsh(d*np.eye(n)-a)[1]);key=f'{d},{n}'
 by.setdefault(key,{});v=by[key].setdefault(str(girth),{'max_ac':-1,'graphs':0});v['graphs']+=1;v['max_ac']=max(v['max_ac'],ac)
print('ATLAS',json.dumps(by,indent=2));(o/'atlas-diagnostics.json').write_text(json.dumps(by,indent=2)+'\n')
