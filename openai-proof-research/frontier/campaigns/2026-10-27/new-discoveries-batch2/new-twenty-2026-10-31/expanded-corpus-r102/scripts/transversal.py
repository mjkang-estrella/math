import random,json,time,pathlib,math
random.seed(102);D=pathlib.Path(__file__).resolve().parents[1]
for p in [3,5,7,11,13,17]:
 n=p*p; best=n*n;bt=None;moves=0;start=time.monotonic()
 for run in range(6):
  t=[(x+p*(0 if run%2==0 else random.randrange(p)),y+p*(0 if run%2==0 else random.randrange(p))) for x in range(p) for y in range(p)]
  cnt=[0]*(n*n)
  def diff(a,b):return ((a[0]-b[0])%n)*n+(a[1]-b[1])%n
  for a in t:
   for b in t:cnt[diff(a,b)]+=1
  val=sum(c>0 for c in cnt)
  def change(i,nt):
   global val
   old=t[i]
   for j,b in enumerate(t):
    if j==i:continue
    for d in [diff(old,b),diff(b,old)]:
     cnt[d]-=1
     if cnt[d]==0:val-=1
    for d in [diff(nt,b),diff(b,nt)]:
     if cnt[d]==0:val+=1
     cnt[d]+=1
   t[i]=nt
  if val<best:best=val;bt=t[:]
  for k in range(1500):
   i=random.randrange(1,n);old=t[i];ov=val
   nt=(i//p+p*random.randrange(p),i%p+p*random.randrange(p));change(i,nt);moves+=1
   temp=.2+2*(1-k%500/500)
   if val>ov and random.random()>math.exp((ov-val)/temp):change(i,old)
   if val<best:best=val;bt=t[:]
  if time.monotonic()-start>16:break
 result={'p':p,'moves':moves,'best':best,'box':(2*p-1)**2,'witness':bt,'seconds':time.monotonic()-start,'independent_support':len({diff(a,b) for a in bt for b in bt})}
 print(json.dumps(result),flush=True)
