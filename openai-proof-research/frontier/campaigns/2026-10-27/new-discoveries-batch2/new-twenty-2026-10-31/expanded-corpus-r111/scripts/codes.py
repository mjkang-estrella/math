import itertools,json,pathlib,collections,math
L=pathlib.Path(__file__).resolve().parents[1];out=[]
for n in range(1,5):
 q=1<<n;poly={1:3,2:7,3:11,4:19}[n]
 def mult(a,b):
  r=0
  while b:
   if b&1:r^=a
   b>>=1;a<<=1
   if a&q:a^=poly
  return r
 for m in [2,3]:
  subsets=range(1,(1<<m)-1)
  configs=0;fail=[]
  for Ms in itertools.product(subsets,repeat=n):
   if __import__('functools').reduce(int.__or__,Ms)==(1<<m)-1:continue
   configs+=1;ss=sum(x.bit_count()for x in Ms);D=set()
   positions=[(j,k)for j,M in enumerate(Ms)for k in range(m)if M>>k&1]
   for bits in range(1<<len(positions)):
    v=[0]*m
    for idx,(j,k)in enumerate(positions):
     if bits>>idx&1:v[k]^=1<<j
    D.add(tuple(v))
   wD=[];wC=[]
   for x in itertools.product(range(q),repeat=m):
    if not any(x):continue
    w=0
    for v in D:
     y=0
     for a,b in zip(x,v):y^=mult(a,b)
     w+=bool(y)
    wD.append(w);wC.append((q-1)*q**(m-1)-w)
   t=len(set(wD)-{0});distance=(q-1)*(q**(m-1)-(1<<(ss-n)));length=q**m-(1<<ss);gr=sum((distance+q**i-1)//q**i for i in range(m))
   if min(wC)!=distance or len(set(wC))!=t+1 or gr!=length:fail.append({'Ms':Ms,'weights_D':sorted(set(wD)),'weights_C':sorted(set(wC)),'expected_d':distance,'griesmer':gr,'length':length})
  row={'n':n,'q':q,'m':m,'configurations':configs,'failures':fail};out.append(row);print(row,flush=True);(L/'outputs/codes.json').write_text(json.dumps(out,indent=2))
