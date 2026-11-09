import pathlib,sys,itertools,json,random
D=pathlib.Path(__file__).resolve().parents[1]
sys.path.insert(0,str(D/'scripts'))
# Import definitions without executing the atlas driver.
ns={'__file__':str(D/'scripts/eip.py')};exec((D/'scripts/eip.py').read_text().split('out=[];total=0')[0],ns)
test=ns['test'];random.seed(196);out=[]
for n in range(8,13):
 graphs=[]
 # All labelled threshold construction strings: adding isolated or dominating vertices.
 for bits in range(1<<(n-1)):
  adj=[0]*n
  for v in range(1,n):
   if bits>>(v-1)&1:
    for u in range(v):adj[u]|=1<<v;adj[v]|=1<<u
  graphs.append(('threshold-'+str(bits),adj))
 # 300 dense and 300 general random graphs per order, with fixed seed.
 for j in range(600):
  prob=random.choice([.15,.25,.5,.75,.9,.95]);adj=[0]*n
  for u in range(n):
   for v in range(u+1,n):
    if random.random()<prob:adj[u]|=1<<v;adj[v]|=1<<u
  graphs.append(('random-'+str(j),adj))
 nested=nonreg=0;success=[]
 for label,adj in graphs:
  if len(set(x.bit_count() for x in adj))==1:continue
  nonreg+=1;e=[0]*(1<<n);best=[0]*(n+1)
  for s in range(1,1<<n):
   v=(s&-s).bit_length()-1;t=s^(1<<v);e[s]=e[t]+(adj[v]&t).bit_count();best[s.bit_count()]=max(best[s.bit_count()],e[s])
  reach={0}
  for k in range(1,n+1):
   reach={s for s in range(1<<n) if s.bit_count()==k and e[s]==best[k] and any(s^(1<<v) in reach for v in range(n) if s>>v&1)}
   if not reach:break
  if not reach:continue
  nested+=1;seq=tuple(best[k]-best[k-1] for k in range(1,n+1));ok,nt,w=test(seq)
  if ok:success.append({'label':label,'adj':adj,'delta':seq})
 out.append({'n':n,'generated':len(graphs),'nonregular':nonreg,'nested':nested,'survivors':success});print(out[-1],flush=True)
 (D/'outputs/eip-structured.json').write_text(json.dumps(out,indent=2))
