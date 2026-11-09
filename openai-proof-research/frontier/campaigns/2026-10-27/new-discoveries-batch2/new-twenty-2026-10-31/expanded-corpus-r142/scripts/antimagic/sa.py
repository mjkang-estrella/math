# Simulated annealing search for local antimagic labelings of complete full t-ary trees
# with exactly l+1 colours. Usage: sa.py t n seconds seed
import sys,random,math,time,json
t,n,secs,seed=map(int,sys.argv[1:5]); random.seed(seed)
# build tree: vertices by BFS, edges child->parent
par=[-1]; depth=[0]; 
for d in range(n):
  for v in [v for v in range(len(par)) if depth[v]==d]:
    for _ in range(t): par.append(v); depth.append(d+1)
V=len(par); E=V-1  # edge i joins vertex i+1 and par[i+1]
inc=[[] for _ in range(V)]
for i in range(E): inc[i+1].append(i); inc[par[i+1]].append(i)
leaves=[v for v in range(V) if depth[v]==n]; l=len(leaves)
adj=[(i+1,par[i+1]) for i in range(E)]
def cost(lab):
  w=[sum(lab[e] for e in inc[v]) for v in range(V)]
  conf=sum(1 for a,b in adj if w[a]==w[b])
  return 10*conf+max(0,len(set(w))-(l+1)),w
lab=list(range(1,E+1)); random.shuffle(lab)
c,w=cost(lab); best=c; T0=2.0; start=time.time(); it=0
while time.time()-start<secs:
  it+=1
  i,j=random.randrange(E),random.randrange(E)
  lab[i],lab[j]=lab[j],lab[i]
  c2,w2=cost(lab)
  temp=T0*max(0.01,1-(time.time()-start)/secs)
  if c2<=c or random.random()<math.exp((c-c2)/temp): c=c2
  else: lab[i],lab[j]=lab[j],lab[i]
  if c<best: best=c
  if c==0: break
c,w=cost(lab)
print(json.dumps(dict(t=t,n=n,edges=E,leaves=l,found=(c==0),cost=c,iters=it,colours=len(set(w)),labels=lab if c==0 else None,parent=par if c==0 else None)))
