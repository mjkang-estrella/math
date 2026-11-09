import pathlib,json,itertools,sys,time,functools
D=pathlib.Path(__file__).resolve().parents[1]
def key(a):
 def f(v,p):return '('+''.join(sorted(f(w,v) for w in range(len(a)) if a[v]>>w&1 and w!=p))+')'
 return min(f(v,-1) for v in range(len(a)))
def trees(N):
 ts={2:[(2,1)]}
 for n in range(3,N+1):
  out={}
  for a in ts[n-1]:
   for v in range(n-1):
    b=list(a)+[1<<v];b[v]|=1<<(n-1);out[key(b)]=tuple(b)
  ts[n]=list(out.values())
 return [a for n in ts for a in ts[n]]
def rho(a):
 n=len(a);far=[]
 for v in range(n):
  reach=1<<v
  for _ in range(3):
   reach|=sum(0 for _ in []) # OR below
   z=reach
   while z:
    b=z&-z;z-=b;reach|=a[b.bit_length()-1]
  far.append(((1<<n)-1)^reach)
 @functools.lru_cache(None)
 def go(s):
  if not s:return 0
  b=s&-s;v=b.bit_length()-1
  return max(go(s^b),1+go(s&far[v]))
 return go((1<<n)-1)
def feasible(a,k):
 n=len(a);allm=(1<<n)-1
 edges=[(1<<u|1<<v,(1<<u|1<<v)|a[u]|a[v]) for u in range(n) for v in range(u+1,n) if a[u]>>v&1]
 choices=[[e for e in edges if e[1]>>v&1] for v in range(n)]
 states=0
 @functools.lru_cache(None)
 def go(used,covered,left):
  nonlocal states
  states+=1
  if covered==allm:return ()
  if not left:return None
  possible=[[(e,c) for e,c in choices[v] if not e&used] for v in range(n) if not covered>>v&1]
  opts=min(possible,key=len)
  if not opts:return None
  opts.sort(key=lambda x:(x[1]&~covered).bit_count(),reverse=True)
  for e,c in opts:
   ans=go(used|e,covered|c,left-1)
   if ans is not None:return (e,)+ans
  return None
 ans=go(0,0,k)
 return ans,states
ts=trees(int(sys.argv[1])); start=int(sys.argv[2]);stop=int(sys.argv[3])
pairs=list(itertools.combinations_with_replacement(range(len(ts)),2))
print(json.dumps(dict(tree_counts={n:sum(len(a)==n for a in ts) for n in range(2,int(sys.argv[1])+1)},pairs=len(pairs),start=start,stop=stop)),flush=True)
for index in range(start,min(stop,len(pairs))):
 i,j=pairs[index];a,b=ts[i],ts[j];n,m=len(a),len(b);x,y=rho(a),rho(b)
 prod=[sum(1<<(v*m+w) for v in range(n) for w in range(m) if a[u]>>v&1 and b[t]>>w&1) for u in range(n) for t in range(m)]
 ans,states=feasible(prod,x*y)
 print(json.dumps(dict(index=index,n=n,m=m,rho=[x,y],a=a,b=b,witness=ans,states=states)),flush=True)
