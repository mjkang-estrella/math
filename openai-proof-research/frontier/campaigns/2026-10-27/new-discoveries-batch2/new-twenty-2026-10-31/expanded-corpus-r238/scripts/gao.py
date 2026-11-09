import itertools,functools,time,json,pathlib,sys,math
D=pathlib.Path(__file__).resolve().parents[1]
@functools.lru_cache(None)
def nu(w):
 r=next((i for i in range(len(w)-2,-1,-1) if w[i]>w[i+1]),None)
 if r is None:return 1
 s=max(j for j in range(r+1,len(w)) if w[j]<w[r]);v=list(w);v[r],v[s]=v[s],v[r];ans=nu(tuple(v))
 for i in range(r):
  if v[i]<v[r] and not any(v[i]<v[k]<v[r] for k in range(i+1,r)):
   u=v.copy();u[i],u[r]=u[r],u[i];ans+=nu(tuple(u))
 return ans
def standard(w):return tuple(sorted(w).index(x)+1 for x in w)
def mac(w):
 @functools.lru_cache(None)
 def f(v):
  ds=[i for i in range(len(v)-1) if v[i]>v[i+1]]
  if not ds:return (1,0)
  val=0;l=None
  for i in ds:
   z=list(v);z[i],z[i+1]=z[i+1],z[i];a,l=f(tuple(z));val+=(i+1)*a
  return val,l+1
 a,l=f(w);assert a%math.factorial(l)==0;return a//math.factorial(l)
# Independent Macdonald reduced-word check, all permutations through S5.
for n in range(6):
 for w in itertools.permutations(range(1,n+1)):assert nu(w)==mac(w),(w,nu(w),mac(w))
print('transition/Macdonald validation all S0..S5 passed',flush=True)
cs={():1};summary=[]
for n in range(1,int(sys.argv[1])+1):
 hist={};mn=10**30;mx=0;t=time.monotonic();neg=[]
 for w in itertools.permutations(range(1,n+1)):
  c=nu(w)-sum(cs[standard(z)] for k in range(n) for z in itertools.combinations(w,k));cs[w]=c;mn=min(mn,c);mx=max(mx,c);hist[c]=hist.get(c,0)+1
  if c<0:neg.append((w,c))
 row=dict(n=n,count=math.factorial(n),min=mn,max=mx,negative=neg,seconds=time.monotonic()-t,histogram=hist);summary.append(row);print(json.dumps(row),flush=True)
 (D/'gao-coverage.json').write_text(json.dumps(summary,indent=2)+'\n')
