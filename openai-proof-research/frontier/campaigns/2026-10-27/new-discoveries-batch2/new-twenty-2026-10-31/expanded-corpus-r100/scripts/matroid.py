import random,itertools,math,json,time
random.seed(352596)
def span(v):
 s={0}
 for a in v:s|={x^a for x in s.copy()}
 return s
def calc(cols):
 n=len(cols);flats={}
 for mask in range(1<<n):
  sp=span([cols[i] for i in range(n) if mask>>i&1]);cl=sum(1<<i for i,c in enumerate(cols) if c in sp);flats[cl]=len(sp).bit_length()-1
 fs=sorted(flats,key=lambda f:(flats[f],f));rank=[flats[f] for f in fs];r=rank[-1];L=len(fs);pi={}
 for i in range(L):
  mu={i:1}
  for j in range(i,L):
   if fs[i]&fs[j]!=fs[i]:continue
   if j!=i:mu[j]=-sum(v for k,v in mu.items() if k!=j and fs[k]&fs[j]==fs[k])
   pi[i,j]=sum(v*(-1)**(rank[k]-rank[i]) for k,v in mu.items() if fs[k]&fs[j]==fs[k])
 # weight sums over all flags of each cardinality
 dp={(0,0):1};W=[0]*r
 for j in range(1,L):
  for ell in range(1,r+1):
   v=sum(dp.get((i,ell-1),0)*pi[i,j] for i in range(j) if (i,j) in pi)
   dp[j,ell]=v
   if j==L-1:W[ell-1]=v
 num=[sum(W[l]*math.comb(r-1-l,k-l)*(-1)**(k-l) for l in range(k+1)) for k in range(r)]
 # type B Eulerian degree r-1 in source indexing
 E=[1]
 for d in range(1,r):
  E=[(2*k+1)*(E[k] if k<len(E) else 0)+(2*d-2*k+1)*(E[k-1] if k else 0) for k in range(d+1)]
 lower=[math.comb(r-1,k)*pi[0,L-1] for k in range(r)];upper=[x*pi[0,L-1] for x in E]
 assert all(a<=b<=c for a,b,c in zip(lower,num,upper)),(cols,r,num,lower,upper)
 assert num!=lower and num!=upper,(cols,r,num)
 return dict(columns=cols,rank=r,flats=L,pi_at_1=pi[0,L-1],numerator=num)
out=[]
for n in range(3,8):
 for cols in itertools.combinations(range(1,8),n):
  if len(span(cols))<8:continue
  out.append(calc(list(cols)))
for r in [4,5]:
 for j in range(50):
  cols=random.sample(range(1,1<<r),random.randrange(r+1,11))
  if len(span(cols))!=1<<r:continue
  out.append(calc(cols))
print('tested',len(out),'binary represented matroids; no coefficient violation',flush=True)
json.dump(out,open('outputs/matroid.json','w'),indent=2)
