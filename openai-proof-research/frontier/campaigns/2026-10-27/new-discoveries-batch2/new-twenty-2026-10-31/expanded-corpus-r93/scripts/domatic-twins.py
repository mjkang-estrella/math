import itertools,functools,json
from pathlib import Path
D=Path(__file__).resolve().parents[1]
def parts(n,lo=1):
 if n==0:yield ();return
 for x in range(lo,n+1):
  for y in parts(n-x,x):yield (x,)+y
def solve(sizes,k,first):
 m=len(sizes)
 @functools.lru_cache(None)
 def go(cols,turn):
  empty=tuple(sizes[i]-sum(c[i] for c in cols) for i in range(m))
  for i in range(m):
   ext_empty=sum(empty[j] for j in range(m) if i!=j)
   for c in cols:
    if sum(c[j] for j in range(m) if i!=j)==0 and ext_empty==0:
     if c[i]+empty[i]<sizes[i]:return False
  if not any(empty):return True
  for i in range(m):
   if not empty[i]:continue
   seen=set()
   for j,c in enumerate(cols):
    if c in seen:continue
    seen.add(c);cc=list(c);cc[i]+=1;new=list(cols);new[j]=tuple(cc);new=tuple(sorted(new))
    val=go(new,1-turn)
    if val==(turn==0):return val
  return bool(turn)
 return go(((0,)*m,)*k,first)
out=[]
for n in range(3,15):
 count=0;hist={}
 for sizes in parts(n):
  if len(sizes)<2:continue
  bound=(n-max(sizes)+3)//2
  if bound<3:continue
  vals=[1,1]
  for k in range(2,bound+1):
   for t in range(2):
    if solve(sizes,k,t):vals[t]=k
  count+=1;hist[str(vals)]=hist.get(str(vals),0)+1
  print('tested',sizes,vals,flush=True)
  if abs(vals[0]-vals[1])>1:print('WITNESS',sizes,vals,flush=True)
 print('COMPLETE',n,count,hist,flush=True);out.append([n,count,hist]);(D/'outputs/domatic-twins.json').write_text(json.dumps(out))
