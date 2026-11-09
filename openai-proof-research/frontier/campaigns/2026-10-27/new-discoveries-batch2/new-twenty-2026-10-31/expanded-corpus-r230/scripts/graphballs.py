import itertools,math,json,sys
N=int(sys.argv[1])
for n in range(3,N+1):
 es=list(itertools.combinations(range(n),2));cuts=set()
 for c in itertools.product(range(3),repeat=n):
  if c[0]!=0 or set(c)!={0,1,2}:continue
  cuts.add(sum(1<<i for i,(u,v) in enumerate(es) if c[u]!=c[v]))
 best=(0,1,None);hits=[]
 for h in range(1<<len(es)):
  lam=min((h&c).bit_count() for c in cuts);s=(lam-1)//2
  if s<0:continue
  e=h.bit_count();num=sum(math.comb(e,j) for j in range(s+1));den=1<<e
  if num*best[1]>best[0]*den:best=(num,den,dict(h=h,edges=e,s=s,threecut=lam))
  if num*(1<<n)>(n+1)*den:hits.append(dict(h=h,num=num,den=den,s=s))
 print(json.dumps(dict(n=n,supports=1<<len(es),tripartitions=len(cuts),best=best,exceeding=len(hits),examples=hits[:5])),flush=True)
