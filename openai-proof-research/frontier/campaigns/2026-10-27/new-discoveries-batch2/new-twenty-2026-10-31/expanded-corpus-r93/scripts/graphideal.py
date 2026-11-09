import itertools,json,random,sys
from pathlib import Path
D=Path(__file__).resolve().parents[1]
def rank(cols):
 piv={}
 for x in cols:
  while x:
   b=x.bit_length()
   if b in piv:x^=piv[b]
   else:piv[b]=x;break
 return len(piv)
def invariants(nb):
 n=len(nb);full=(1<<n)-1
 # squarefree monomial colon: all residual generators must be divisible by a singleton residual
 best=n
 for a in range(1<<n):
  if a.bit_count()>=best:continue
  residual=[b&~a for b in nb]
  if 0 in residual:continue
  singles=0
  for b in residual:
   if b.bit_count()==1:singles|=b
  if all(b&singles for b in residual):best=a.bit_count()
 faces=[a for a in range(1<<n) if not any(a&b==b for b in nb)]
 reg=0
 for w in range(1<<n):
  by={}
  for a in faces:
   if a&~w==0:by.setdefault(a.bit_count(),[]).append(a)
  ranks={}
  for dim,fs in by.items():
   if not dim:continue
   lower={a:i for i,a in enumerate(by.get(dim-1,[]))}
   cols=[]
   for a in fs:
    col=0
    for v in range(n):
     if a>>v&1:col^=1<<lower[a^(1<<v)]
    cols.append(col)
   ranks[dim]=rank(cols)
  for dim,fs in by.items():
   if len(fs)-ranks.get(dim,0)-ranks.get(dim+1,0)>0:reg=max(reg,dim)
 return best,reg
rng=random.Random(930928);res=[]
mode=sys.argv[1] if len(sys.argv)>1 else 'all'
for n in (range(1,6) if mode=='all' else range(6,10)):
 es=list(itertools.combinations(range(n),2));hist={};cnt=0
 gs=range(1<<len(es)) if mode=='all' else (rng.getrandbits(len(es)) for _ in range(1000))
 for g in gs:
  nb=[1<<i for i in range(n)]
  for j,(a,b) in enumerate(es):
   if g>>j&1:nb[a]|=1<<b;nb[b]|=1<<a
  seen=1
  while True:
   new=seen
   for i in range(n):
    if seen>>i&1:new|=nb[i]
   if new==seen:break
   seen=new
  if seen!=(1<<n)-1:continue
  v,r=invariants(nb);cnt+=1;key=str((v,r));hist[key]=hist.get(key,0)+1
  if v>r:print('WITNESS',n,g,v,r,nb,flush=True)
  if cnt%100==0:print('progress',n,cnt,flush=True)
 print('COMPLETE',n,cnt,hist,flush=True);res.append([n,cnt,hist]);(D/f'outputs/graphideal-{mode}.json').write_text(json.dumps(res,indent=2))
