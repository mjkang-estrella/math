import pathlib,json,itertools,sys,time
D=pathlib.Path(__file__).resolve().parents[1];start=time.monotonic()
def good(w,cyc):
 n=len(w)
 for k in range(2,n+1):
  best=-1
  for f in (0,1):
   if f and w[0]>=k:continue
   a,b=(0,-999) if f==0 else (-999,1)
   for i in range(1,n):
    nb=max(a,b if w[i]+w[i-1]<k else -999)+1 if w[i]<k else -999
    a,b=max(a,b),nb
   z=a if cyc and f and w[-1]+w[0]>=k else max(a,b)
   best=max(best,z)
  if best>=k:return False
 return True
def brute(w,cyc):
 n=len(w);e=[(i,i+1) for i in range(n-1)]+([(n-1,0)] if cyc else [])
 for m in range(1,1<<n):
  s=[i for i in range(n) if m>>i&1];v=max([w[i] for i in s]+[w[i]+w[j] for i,j in e if m>>i&1 and m>>j&1])
  if v<len(s):return False
 return True
checks=0
for n in range(2,7):
 for w in itertools.product(range(1,4),repeat=n):
  for cyc in ([False,True] if n%2==0 and n>=4 else [False]):
   assert good(w,cyc)==brute(w,cyc);checks+=1
print('checker crosschecks',checks,flush=True)
def compositions(n,total,prefix=()):
 if n==1:
  if total>=1:yield prefix+(total,)
 else:
  for x in range(1,total-n+2):yield from compositions(n-1,total-x,prefix+(x,))
out={'crosschecks':checks,'cases':[]}
for n,target in [(6,14),(8,23)]:
 for cyc in [False,True]:
  tested=0;valid=None
  for total in range(n,target+1):
   for w in compositions(n,total):
    if cyc and w[0]!=min(w):continue
    if w>w[::-1]:continue
    tested+=1
    if good(w,cyc):valid=w;break
   if valid:break
  o={'n':n,'cycle':cyc,'minimum':sum(valid) if valid else None,'witness':valid,'tested':tested,'domain':'all positive integer weight vectors through first feasible total, with reflection and cycle-minimum symmetry'};out['cases'].append(o);print(o,flush=True)
out['seconds']=time.monotonic()-start;(D/'outputs/replication-exhaustive.json').write_text(json.dumps(out,indent=2))
