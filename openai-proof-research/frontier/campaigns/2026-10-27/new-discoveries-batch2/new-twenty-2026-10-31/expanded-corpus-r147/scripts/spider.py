import itertools,functools,pathlib,json,time,sys
D=pathlib.Path(__file__).resolve().parents[1];k=int(sys.argv[1]);start=time.monotonic();out=[]
@functools.lru_cache(None)
def forest(q,r):
 if not q:return True
 if r<0:return False
 if sum(q)>(r+1)**2:return False
 cap=2*r+1
 for i,a in enumerate(q):
  qq=list(q);qq[i]=max(0,a-cap);qq=tuple(sorted(v for v in qq if v))
  if forest(qq,r-1):return True
 return False
def cover(L,k):
 vertices=[(-1,0)]+[(i,s) for i,l in enumerate(L) for s in range(1,l+1)];n=len(vertices);full=(1<<n)-1
 def dist(x,y):
  i,s=x;j,t=y
  return abs(s-t) if i==j else s+t
 balls=[[sum(1<<j for j,y in enumerate(vertices) if dist(x,y)<=r) for x in vertices] for r in range(k)]
 @functools.lru_cache(None)
 def rec(mask,r):
  if time.monotonic()-start>100:raise TimeoutError
  if mask==full:return ()
  if r<0:return None
  missing=full^mask
  opts=sorted(set(b&missing for b in balls[r]),key=int.bit_count,reverse=True)
  if sum(sorted((max((b&missing).bit_count() for b in balls[j]) for j in range(r+1)),reverse=True))<missing.bit_count():return None
  for b in opts:
   if not b:continue
   result=rec(mask|b,r-1)
   if result is not None:return (balls[r].index(next(v for v in balls[r] if (v&missing)==b)),)+result
  return None
 return rec(0,k-1),len(rec.cache_info().__str__())
# symmetric minimal core plus asymmetric core (d1=k-1,d2=d3=k+1)
for d in [(k,k,k),(k-1,k+1,k+1)]:
 for q in itertools.combinations_with_replacement(range(1,2*k+4),3):
  if forest(q,k-2):continue
  L=tuple(di+qi-1 for di,qi in zip(d,q))
  if sum(L)+1>k*k+2*k:continue
  try:ans,_=cover(L,k)
  except TimeoutError:break
  out.append({'d':d,'q':q,'L':L,'burnable_in_k':ans is not None,'centers_descending_radius':ans})
  if ans is not None:print('COUNTEREXAMPLE',out[-1],flush=True);break
  if time.monotonic()-start>100:break
 if time.monotonic()-start>100 or (out and out[-1]['burnable_in_k']):break
(D/f'outputs/spider{k}.json').write_text(json.dumps({'k':k,'cases':out,'seconds':time.monotonic()-start},indent=2)+'\n');print('k',k,'cases',len(out),'seconds',time.monotonic()-start,flush=True)
