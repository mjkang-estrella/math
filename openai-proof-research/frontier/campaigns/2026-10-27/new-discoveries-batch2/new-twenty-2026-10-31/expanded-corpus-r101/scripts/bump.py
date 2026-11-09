import functools,itertools,sys,json,time
m=int(sys.argv[1]);L=int(sys.argv[2]);t0=time.monotonic()
@functools.lru_cache(maxsize=300000)
def evalword(w):
 p=list(range(max(w,default=0)+3))
 for s in w:
  # right multiply swaps p[s],p[s+1]; left swaps values s,s+1
  if p[s]==s+1 or (p[s]==s and p[s+1]==s+1):p[s],p[s+1]=p[s+1],p[s]
  else:
   p[s],p[s+1]=p[s+1],p[s]
   for i in range(len(p)):
    if p[i]==s:p[i]=s+1
    elif p[i]==s+1:p[i]=s
 inv=sum(p[i]>p[j] for i in range(len(p)) for j in range(i+1,len(p)));cycles=sum(p[i]>i for i in range(len(p)))
 if (inv+cycles)//2!=len(w):return None
 while len(p)>1 and p[-1]==len(p)-1:p.pop()
 return tuple(p)
counts={};bumps=0;longest=0
# valid eval using ordinary involution action may return valid final rank despite intermediate down? rank changes ±1, max final rank length guarantees all up.
for length in range(1,L+1):
 num=0
 for w in itertools.product(range(1,m+1),repeat=length):
  if evalword(w) is None:continue
  num+=1
  for i in range(length):
   pi=evalword(w[:i]+w[i+1:])
   if pi is None:continue
   v=list(w);j=i;steps=0
   while True:
    v[j]+=1;steps+=1
    if evalword(tuple(v)) is not None:break
    others=[h for h in range(length) if h!=j and evalword(tuple(v[:h]+v[h+1:]))==pi]
    if len(others)!=1:raise RuntimeError(('mark error',w,i,v,j,others))
    j=others[0]
    if steps>1000:raise RuntimeError('termination')
   bumps+=1;longest=max(longest,steps)
   if any(b-a not in [0,1] for a,b in zip(w,v)):
    print('COUNTEREXAMPLE',w,i,pi,v,flush=True);sys.exit(2)
 counts[length]=num;print('length',length,'words',num,'bumps',bumps,'maxsteps',longest,flush=True)
print(json.dumps({'m':m,'L':L,'counts':counts,'bumps':bumps,'maxsteps':longest,'wall':time.monotonic()-t0}))
