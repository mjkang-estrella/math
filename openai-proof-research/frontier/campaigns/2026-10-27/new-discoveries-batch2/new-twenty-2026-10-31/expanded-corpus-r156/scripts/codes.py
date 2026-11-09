import itertools,random,json,time
from pathlib import Path
random.seed(156); terms=[]
for s in range(2,5):
 for S in itertools.combinations(range(1,8),s):
  v=0
  for t in S:v^=t
  minimal=True
  for j in range(1,len(S)):
   for T in itertools.combinations(S,j):
    z=0
    for t in T:z^=t
    if z&~v==0:minimal=False
  if minimal:terms.append(S)
def val(a):
 s=sum(a)+sum(x*(x-1)//2 for x in a[1:])
 for T in terms:
  v=1
  for t in T:v*=a[t]
  s+=v
 return s
def pred(k):
 a=[0]*8
 if k%4:
  for t,v in zip([4,2,5,3],[(k+i)//4 for i in range(4)]):a[t]=v
 else:a[4],a[2],a[5],a[3]=k//4,k//4-1,k//4+1,k//4
 return a
rows=[];moves=0;start=time.monotonic()
for k in list(range(151,181))+[200,250,500,1000,10000,1000000]:
 target=val(pred(k));best=0;arg=None
 for trial in range(12):
  if trial==0:a=pred(k)
  elif trial<5:
   a=pred(k)
   for j in range(trial):
    i=random.choice([i for i in range(8) if a[i]]);a[i]-=1;a[random.randrange(8)]+=1
  else:
   cut=sorted([0,k]+[random.randrange(k+1) for _ in range(6)]);a=[0]+[cut[j+1]-cut[j] for j in range(7)];random.shuffle(a)
  v=val(a)
  for it in range(100):
   bv=v;ba=None
   for i in range(8):
    if a[i]==0:continue
    for j in range(8):
     if i==j:continue
     b=a.copy();b[i]-=1;b[j]+=1;w=val(b);moves+=1
     if w>bv:bv=w;ba=b
   if ba is None:break
   a=ba;v=bv
  if v>best:best=v;arg=a
 rows.append({'k':k,'claimed':target,'best_local':best,'multiplicities':arg,'trials':12})
 if best>target:print('VIOLATION',rows[-1],flush=True)
Path('outputs/codes-search.json').write_text(json.dumps({'terms':terms,'rows':rows,'unit_transfers_evaluated':moves,'elapsed':time.monotonic()-start,'scope':'Local search only; not global optimization. Beyond authors k<=150.'},indent=2));print('completed',len(rows),'parameters;',moves,'transfers',flush=True)
