"""Bounded exact subset diagnostics for Celoria Section 5. Python stdlib only."""
import collections,hashlib,json,random,resource,time
from pathlib import Path
resource.setrlimit(resource.RLIMIT_AS,(800*1024**2,800*1024**2))
resource.setrlimit(resource.RLIMIT_CPU,(110,110))
OUT=Path(__file__).resolve().parent
rng=random.Random(381600)
def sig(a):
 n=len(a);allv=(1<<n)-1;edges=sum(x.bit_count() for x in a)//2
 C=collections.Counter();J=collections.Counter()
 for S in range(1<<n):
  W=allv^S;k=S.bit_count();seen=0;c=0;e=0;cross=0;z=0
  for v in range(n):
   if S>>v&1:e+=(a[v]&S).bit_count();cross+=(a[v]&W).bit_count()
   elif not a[v]&S:z+=1
  e//=2
  todo=S
  while todo:
   c+=1;front=todo&-todo
   while front:
    todo &= ~front;seen |=front;new=0
    while front:
     v=(front&-front).bit_length()-1;front&=front-1;new|=a[v]
    front=new&todo
  ranks=(c,e-k+c,z,cross-(n-k)+z,edges-e-cross)
  assert min(ranks)>=0
  J[(k,)+ranks]+=1
  for p,r in enumerate(ranks):
   if r:C[k,p,r]+=1
 return tuple(sorted(C.items())),tuple(sorted(J.items()))
def iso(a,b):
 n=len(a);mapping={};used=set();order=sorted(range(n),key=lambda i:-a[i].bit_count())
 def rec(t):
  if t==n:return True
  v=order[t]
  for w in range(n):
   if w in used or a[v].bit_count()!=b[w].bit_count():continue
   if any(bool(a[v]>>u&1)!=bool(b[w]>>z&1) for u,z in mapping.items()):continue
   mapping[v]=w;used.add(w)
   if rec(t+1):return True
   used.remove(w);del mapping[v]
  return False
 return rec(0)
def regular(n,d):
 for _ in range(100):
  stubs=list(range(n))*d;rng.shuffle(stubs);a=[0]*n;ok=True
  for v,w in zip(stubs[::2],stubs[1::2]):
   if v==w or a[v]>>w&1:ok=False;break
   a[v]|=1<<w;a[w]|=1<<v
  if ok:
   reached=1
   while True:
    nex=reached
    for v in range(n):
     if reached>>v&1:nex|=a[v]
    if nex==reached:break
    reached=nex
   if reached==(1<<n)-1:return a
 return None
def edges(a):return [[i,j] for i in range(len(a)) for j in range(i+1,len(a)) if a[i]>>j&1]
if __name__=='__main__':
 start=time.monotonic();seen={};counts=collections.Counter();collisions=[];attempts=0
 while time.monotonic()-start<75 and attempts<1800:
  n,d=[(10,3),(12,3),(10,4),(12,4)][attempts%4];attempts+=1;a=regular(n,d)
  if a is None:continue
  ss,j=sig(a);key=(n,d,ss);counts[str((n,d))]+=1
  if key in seen:
   b=seen[key]
   if not iso(a,b):
    collisions.append({'a':edges(a),'b':edges(b),'n':n,'d':d,'joint_equal':j==sig(b)[1]});break
  else:seen[key]=a
 out={'seed':381600,'elapsed_seconds':time.monotonic()-start,'attempts':attempts,'evaluated':dict(counts),'distinct_signatures':len(seen),'counterexamples':collisions,'scope':'Sampled connected regular graphs only; all 2^n subsets evaluated with integer arithmetic; no completeness claim.'}
 (OUT/'metric-diagnostics.json').write_text(json.dumps(out,indent=2));print(json.dumps(out))
