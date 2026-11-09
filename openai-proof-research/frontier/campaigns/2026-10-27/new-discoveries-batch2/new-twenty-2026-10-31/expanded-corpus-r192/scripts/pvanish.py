import pathlib,json,functools,math,sys
D=pathlib.Path(__file__).resolve().parents[1]
@functools.lru_cache(None)
def parts(n,m=1000):
 if n==0:return ((),)
 return tuple((i,)+q for i in range(min(n,m),1-1,-1) for q in parts(n-i,i))
@functools.lru_cache(None)
def char(lam,mu):
 if not mu:return int(not lam)
 k=mu[0];l=len(lam);B=[x+l-i-1 for i,x in enumerate(lam)];S=set(B);out=0
 for b in B:
  if b>=k and b-k not in S:
   C=sorted((S-{b})|{b-k},reverse=True);nu=tuple(x-l+i+1 for i,x in enumerate(C) if x-l+i+1>0)
   out+=(-1)**sum(b-k<x<b for x in B)*char(nu,mu[1:])
 return out

def deg(lam):
 N=sum(lam);d=1
 for r,a in enumerate(lam):
  for c in range(a):d*=a-c+sum(x>c for x in lam[r+1:])
 return math.factorial(N)//d
rows=[]
for n in range(int(sys.argv[1]),int(sys.argv[2])+1):
 P=parts(n);degrees={la:deg(la) for la in P};primes=[p for p in range(5,n+2) if all(p%d for d in range(2,math.isqrt(p)+1))];tested=0;survive=[]
 for p in primes:
  a0=n%p;sing=[la for la in P if degrees[la]%p==0]
  for mu in P:
   if sum(x for x in mu if x<a0)<=a0:continue
   tested+=1
   if all(char(la,mu)==0 for la in sing):survive.append({'p':p,'mu':mu})
 z={'n':n,'partitions':len(P),'primes':primes,'violating_classes_tested':tested,'counterexamples':survive,'character_cache':char.cache_info()._asdict()};rows.append(z);print(json.dumps(z),flush=True);(D/f'outputs/pvanish-{sys.argv[1]}-{sys.argv[2]}.json').write_text(json.dumps(rows,indent=2));char.cache_clear()
