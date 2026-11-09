import pathlib,json,functools,itertools,sys
D=pathlib.Path(__file__).resolve().parents[1]
@functools.lru_cache(None)
def size(t):return 1 if not t else sum(map(size,t))
@functools.lru_cache(None)
def even(d,n):
 if n==1:return ()
 if n<=d:return ((),)*n
 s,b=divmod(n,d);return tuple(sorted([even(d,s)]*(d-b)+[even(d,s+1)]*b))
@functools.lru_cache(None)
def copies(s,t):
 if not s:return size(t)
 if not t or size(s)>size(t):return 0
 ans=sum(copies(s,c) for c in t)
 # each target branch occupies one distinct host branch; divide duplicate permutations
 if len(s)<=len(t):
  for inds in itertools.combinations(range(len(t)),len(s)):
   for perm in set(itertools.permutations(s)):
    z=1
    for a,i in zip(perm,inds):z*=copies(a,t[i])
    ans+=z
 return ans
@functools.lru_cache(None)
def alltrees(d,n):
 if n==1:return ((),)
 pool=sorted(t for k in range(1,n) for t in alltrees(d,k))
 out=[]
 def rec(start,remain,parts):
  if remain==0:
   if len(parts)>=2:out.append(tuple(parts))
   return
  if len(parts)>=d:return
  for i in range(start,len(pool)):
   s=size(pool[i])
   if s<=remain:rec(i,remain-s,parts+[pool[i]])
 rec(0,n,[]);return tuple(out)
rows=[];hits=[]
for d in (2,3,4):
 for n in range(2,12):
  ts=alltrees(d,n);row={'d':d,'n':n,'trees':len(ts),'maxima':{}}
  for k in range(2,n+1):
   s=even(d,k);baseline=copies(s,even(d,n));val,t=max((copies(s,t),t) for t in ts);row['maxima'][k]=val
   if val>baseline:
    h={'d':d,'n':n,'k':k,'baseline':baseline,'value':val,'target':s,'witness':t};hits.append(h);print('HIT',h,flush=True)
  rows.append(row);print(d,n,len(ts),flush=True)
(D/'outputs/trees.json').write_text(json.dumps({'rows':rows,'hits':hits},indent=2))
