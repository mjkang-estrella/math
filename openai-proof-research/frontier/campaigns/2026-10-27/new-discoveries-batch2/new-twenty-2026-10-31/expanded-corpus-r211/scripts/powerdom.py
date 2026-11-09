import pathlib,json,random,itertools
D=pathlib.Path(__file__).resolve().parents[1];rng=random.Random(211)
def components_ok(a):
 unseen=(1<<len(a))-1
 while unseen:
  todo=unseen&-unseen;s=0
  while todo:
   s|=todo;temp=todo;todo=0
   while temp:
    b=temp&-temp;temp-=b;todo|=a[b.bit_length()-1]
   todo&=~s
  if s.bit_count()<3:return False
  unseen&=~s
 return True
def gamma(a):
 n=len(a);allv=(1<<n)-1
 def dominates(s):
  seen=0
  for i in s:seen|=a[i]|1<<i
  while True:
   old=seen;temp=seen
   while temp:
    b=temp&-temp;temp-=b;u=a[b.bit_length()-1]&~seen
    if u and u&(u-1)==0:seen|=u
   if seen==allv:return True
   if old==seen:return False
 for k in range(1,n+1):
  for s in itertools.combinations(range(n),k):
   if dominates(s):return k
out=[]
for n in [13,14,16,17,20]:
 checked=0;mx=0;hist={}
 for j in range(1000):
  p=[.12,.2,.3,.4,.5][j%5];a=[0]*n
  for u in range(n):
   for v in range(u):
    if rng.random()<p:a[u]|=1<<v;a[v]|=1<<u
  b=[((1<<n)-1)^a[u]^(1<<u) for u in range(n)]
  if not components_ok(a) or not components_ok(b):continue
  g=gamma(a);h=gamma(b);checked+=1;mx=max(mx,g+h);key=str((g,h));hist[key]=hist.get(key,0)+1
  if g+h>n//3+2:print('FAIL',n,a,g,h,flush=True)
 row={'n':n,'generated':1000,'eligible_checked':checked,'max_sum':mx,'gamma_pair_histogram':hist,'bound':n//3+2};out.append(row);print(row,flush=True);(D/'outputs/powerdom.json').write_text(json.dumps(out,indent=2)+'\n')
