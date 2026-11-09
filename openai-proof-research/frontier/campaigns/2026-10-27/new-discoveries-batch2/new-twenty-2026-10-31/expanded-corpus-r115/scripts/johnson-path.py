import itertools,math,random,time,json
from pathlib import Path
D=Path(__file__).resolve().parents[1];rng=random.Random(115);out=[]
def upper(n,k):
 C=lambda a,b:math.comb(a,b) if a>=b>=0 else 0
 def f(t):return t*C(n-t,k-1)+t*sum(C((k-i)*t,k-i) for i in range(2,k+1))-sum(C((k-i-1)*t+1,k-i) for i in range(1,k))
 return max(f((n+1)//k),f((n+k-1)//k))-1
for n,k in [(8,4),(9,4),(10,5)]:
 V=[sum(1<<i for i in s) for s in itertools.combinations(range(n),k)];N=len(V);adj=[sum(1<<j for j,w in enumerate(V) if (v^w).bit_count()==2) for v in V];powers=[1.2**i for i in range(N+1)]
 def score(p):
  seen=0;boundary=0;mx=0;cost=0
  for v in p:
   seen|=1<<v;boundary=(boundary|adj[v])&~seen;c=boundary.bit_count();mx=max(mx,c);cost+=powers[c]
  return mx,cost
 p=list(range(N));best,cur=score(p);bestp=p[:];initial=best;start=time.monotonic();steps=0
 while time.monotonic()-start<35:
  steps+=1;i=rng.randrange(N);j=max(0,min(N-1,i+rng.randint(-max(3,N//5),max(3,N//5))));p[i],p[j]=p[j],p[i];width,c=score(p);temp=.0001+0.03*((steps%20000)/20000)
  if c<=cur or rng.random()<math.exp(max(-700,(cur-c)/(temp*cur))):cur=c
  else:p[i],p[j]=p[j],p[i]
  if width<best:best=width;bestp=p[:]
  if steps%30000==0:p=bestp[:];cur=score(p)[1]
 row=dict(n=n,k=k,N=N,source_bound=upper(n,k),initial_lex_vertex_separation=initial,best_vertex_separation=best,steps=steps,order=bestp);out.append(row);print({k:v for k,v in row.items() if k!='order'},flush=True);(D/'outputs/johnson-path.json').write_text(json.dumps(out,indent=2)+'\n')
