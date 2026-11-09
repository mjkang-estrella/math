import itertools,math,json,pathlib,random,sys
D=pathlib.Path(__file__).resolve().parents[1]
# Diagnostic floating point metric checker; no exact-certificate claims.
raw=[x for x in itertools.product([-1,0,1],repeat=3) if any(x)]
pts=[tuple(a/math.sqrt(sum(t*t for t in x)) for a in x) for x in raw]
if len(sys.argv)>1:
 m=int(sys.argv[1]);pts=[]
 for zero in range(3):
  for k in range(m):
   v=[math.cos(2*math.pi*k/m),math.sin(2*math.pi*k/m)];v.insert(zero,0)
   if not any(sum((a-b)**2 for a,b in zip(v,w))<1e-16 for w in pts):pts.append(tuple(v))
 raw=pts
N=len(pts);dist=[[math.acos(max(-1,min(1,sum(a*b for a,b in zip(x,y))))) for y in pts] for x in pts]
trip=[]
for i in range(N):
 for j in range(N):
  for k in range(i+1,N):
   if abs(dist[i][j]-dist[j][k])<1e-9 and abs(dist[i][k]-2*dist[i][j])<1e-9:trip.append((1<<i|1<<j|1<<k,2))
def val(mask):return mask.bit_count()+sum(c for m,c in trip if mask&m==m)
def bound(n):return (n*n+[4*n-8,5*n-16,6*n-12,5*n-14][n%4])//2
out=[]
# Exhaust all subsets of the 14 axes/cube vertices, then deterministic hill climbing on 26 points.
inds=[] if len(sys.argv)>1 else [i for i,x in enumerate(raw) if sum(t!=0 for t in x) in [1,3]];best={}
for mask0 in range(1<<len(inds)):
 mask=sum(1<<inds[j] for j in range(len(inds)) if mask0>>j&1);n=mask.bit_count()
 if n<2:continue
 v=val(mask)
 if v>best.get(n,(-1,0))[0]:best[n]=(v,mask)
out.append({'mode':'all 16384 subsets of 14 axes/cube directions','best':{n:[v,bound(n),m] for n,(v,m) in best.items()}})
rng=random.Random(184);best={};trials=0
for n in range(2,min(N,32)+1):
 for restart in range(100):
  s=set(rng.sample(range(N),n));mask=sum(1<<i for i in s);v=val(mask)
  for step in range(50):
   if n==N:break
   a=rng.choice(sorted(s));b=rng.choice([i for i in range(N) if i not in s]);m=mask^(1<<a)^(1<<b);w=val(m);trials+=1
   if w>=v:s.remove(a);s.add(b);mask=m;v=w
  if v>best.get(n,(-1,0))[0]:best[n]=(v,mask)
out.append({'mode':'100 restarts per size, at most 50 proposed swaps each','proposals':trials,'best':{n:[v,bound(n),m] for n,(v,m) in best.items()}})
(D/'outputs'/('sphere-results.json' if len(sys.argv)==1 else 'sphere-circles-results.json')).write_text(json.dumps({'points':raw,'nonconstant_unoriented_triples':len(trip),'runs':out,'violations':[(n,v,bound(n)) for n,(v,m) in best.items() if v>bound(n)],'warning':'Floating metric diagnostic only; restricted configurations do not exhaust the sphere.'},indent=2));print('sphere completed',N,trials)
