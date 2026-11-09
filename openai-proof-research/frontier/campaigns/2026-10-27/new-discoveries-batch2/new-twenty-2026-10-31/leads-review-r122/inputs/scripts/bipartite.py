import sys
sys.path.append('/home/mj-kang/.local/lib/python3.14/site-packages')
import numpy as np,itertools,json,pathlib,random,math
D=pathlib.Path(__file__).resolve().parents[1];rows=[];bad=[]
def test(p,q,bits):
 n=p+q;deg=[0]*n;edges=[]
 for i in range(p):
  for j in range(q):
   if bits>>(i*q+j)&1:deg[i]+=1;deg[p+j]+=1;edges.append((i,p+j))
 if min(deg)==0:return None
 seen={0}
 for _ in range(n):
  for i,j in edges:
   if i in seen or j in seen:seen.update([i,j])
 if len(seen)!=n:return None
 A=np.zeros((n,n))
 for i,j in edges:A[i,j]=A[j,i]=(deg[i]/deg[j]+deg[j]/deg[i])/2
 val=np.linalg.eigvalsh(A)[-1];bound=((n-1)**2+1)/(2*math.sqrt(n-1))
 if val>bound+1e-8:bad.append({'p':p,'q':q,'bits':bits,'rho':val,'star_rho':bound});print('FAIL',bad[-1],flush=True)
 return val/bound
for p in range(1,5):
 for q in range(p,5):
  if p+q<5:continue
  vals=[v for b in range(1<<(p*q)) if (v:=test(p,q,b)) is not None]
  row={'p':p,'q':q,'labeled_edge_subsets':1<<(p*q),'connected':len(vals),'max_ratio_to_actual_star':max(vals)};rows.append(row);print(row,flush=True)
rng=random.Random(122)
for n in [10,15,20,30,50]:
 vals=[]
 for _ in range(1200):
  p=rng.randrange(1,n//2+1);q=n-p;density=rng.random();bits=sum(1<<i for i in range(p*q) if rng.random()<density)
  v=test(p,q,bits)
  if v is not None:vals.append(v)
 row={'n':n,'random_draws':1200,'connected':len(vals),'max_ratio_to_actual_star':max(vals)};rows.append(row);print(row,flush=True)
(D/'outputs/bipartite.json').write_text(json.dumps({'coverage':rows,'failures':bad},indent=2))
