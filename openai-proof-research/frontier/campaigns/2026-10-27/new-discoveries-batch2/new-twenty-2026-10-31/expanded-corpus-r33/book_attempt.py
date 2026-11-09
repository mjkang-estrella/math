import os
os.environ['OPENBLAS_NUM_THREADS']='1';os.environ['OMP_NUM_THREADS']='1'
import networkx as nx,random,json,pathlib,resource,time
from fractions import Fraction as F
resource.setrlimit(resource.RLIMIT_AS,(2*1024**3,2*1024**3));resource.setrlimit(resource.RLIMIT_CPU,(80,80))
o=pathlib.Path(__file__).resolve().parent; rng=random.Random(341706)
def greedy(x):
 b=F(1);rs=[]
 for _ in range(30):
  if x==1:return b,rs
  r=(F(1,1)/(1-x)).__ceil__();rs.append(r);x/=F(r-1,r);b*=F(r-2,r)
 return None,rs
out={'templates':0,'weighted_cases':0,'min_degree_violations':[],'density_violations':[],'greedy_failures':0};start=time.monotonic()
with (o/'book-weighted.jsonl').open('w') as f:
 for idx,g in enumerate(nx.graph_atlas_g()):
  v=len(g)
  if v<3 or not g.number_of_edges():continue
  out['templates']+=1;edges=list(g.edges());neigh=[set(g[i]) for i in range(v)]
  for it in range(32):
   w=[1]*v if it==0 else [rng.randint(1,9) for _ in range(v)];N=sum(w);e=sum(w[i]*w[j] for i,j in edges);deg=min(sum(w[j] for j in neigh[i]) for i in range(v));bk=max(sum(w[k] for k in neigh[i]&neigh[j]) for i,j in edges);rec={'atlas':idx,'weights':w,'N':N,'e':e,'mindeg':deg,'book':bk,'tests':{}}
   for key,x in [('min_degree',F(deg,N)),('density',F(2*e,N*N))]:
    if not F(1,2)<x<1:continue
    b,rs=greedy(x)
    if b is None:out['greedy_failures']+=1;continue
    rec['tests'][key]={'x':str(x),'greedy':rs,'b':str(b),'gap':str(F(bk,N)-b)}
    if F(bk,N)<b:out[key+'_violations'].append(rec)
   out['weighted_cases']+=1;f.write(json.dumps(rec)+'\n')
out['wall_seconds']=time.monotonic()-start;out['scope']='Finite exact integer blow-ups of atlas graphs <=7, 32 weights per template, seeded; no universal theorem and no Lean semantics';(o/'book-attempt-results.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out),flush=True)
