import resource,json,math
resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
def prime(n):return n>=2 and all(n%d for d in range(2,math.isqrt(n)+1))
def seeds(k):
 a=list(range(1,k+1));s=[('identity',a)]
 if prime(k+1):s.append(('inversion',a[1:]+[1]))
 p=k//2
 if p>=3 and prime(p) and prime(p+2):
  b=a[:];b[1],b[2*p-1]=b[2*p-1],b[1];b[p-1],b[p+1]=b[p+1],b[p-1];s.append(('twice-twin',b))
 if k%2 and prime((k+1)//2) and prime(k+2) and prime((k+1)//2+2):
  p=(k+1)//2;b=a[2:]+[2,1];b[p-1],b[p-3]=b[p-3],b[p-1];s.append(('Sophie',b))
 return s
for k in range(501,1001):
 # exact one-transposition neighbors: all divisor sets for d <=k/2 must agree.
 divs=[tuple(d for d in range(2,k//2+1) if v%d==0) for v in range(k+1)]
 groups={}
 for v in range(1,k+1):groups.setdefault(divs[v],[]).append(v)
 swaps=[];checked=0
 for name,s in seeds(k):
  pos={v:i+1 for i,v in enumerate(s)}
  for g in groups.values():
   for i,a in enumerate(g):
    for b in g[i+1:]:
     checked+=1
     # exact remaining divisor conditions, if unique multiple >k/2 moves
     if all(k-v<pos[u]<=v for v,u in [(a,b),(b,a)] if v>k//2):swaps.append([name,a,b])
 print(json.dumps({'k':k,'seeds':[name for name,s in seeds(k)],'signature_pair_tests':checked,'valid_transpositions':swaps,'scope':'one-transposition neighborhoods of printed starting sequences only, not all WCS or uniqueness'}),flush=True)
