import sys,pathlib,json,math
sys.dont_write_bytecode=True
D=pathlib.Path(__file__).resolve().parents[1];sys.path.insert(0,str(D.parent/'fresh-corpus-r10/pydeps'))
import numpy as np
out=[]
for n,pol in [(9,0x211),(11,0x805),(13,0x201b)]:
 q=1<<n;X=np.arange(q,dtype=np.int32)
 # Field operations vectorized without q by q multiplication storage.
 def mul(a,b):
  a,b=np.broadcast_arrays(a,b);a=a.copy();b=b.copy();r=np.zeros_like(a)
  for _ in range(n):r^=a*(b&1);b>>=1;a<<=1;a^=(a>>n)*pol
  return r
 def pw(x,e):
  y=np.ones_like(x)
  while e:
   if e&1:y=mul(y,x)
   x=mul(x,x);e>>=1
  return y
 assert np.all(mul(X[1:],pw(X[1:],q-2))==1)
 factors=[p for p in range(2,q) if (q-1)%p==0 and all(p%d for d in range(2,math.isqrt(p)+1))]
 g=next(g for g in range(2,q) if all(int(pw(np.array(g), (q-1)//p))!=1 for p in factors))
 gi=int(pw(np.array(g),q-2));perms=[X^(1<<j) for j in range(n)]+[mul(gi,X)]
 for i in range(1,(n+1)//2):
  if math.gcd(i,n)!=1:continue
  s=2**(2*i)-2**i+1;inv=pow(2**i+1,-1,q-1);omit=np.unique(pw(pw(X,s)^pw(X^1,s)^1,inv));block=(~np.isin(X,omit)).astype(np.uint8)
  piv={};queue=[];ops=0
  def add(v):
   while v:
    k=v.bit_length()-1
    if k not in piv:piv[k]=v;queue.append(v);return
    v^=piv[k]
  add(int.from_bytes(np.packbits(block,bitorder='little').tobytes(),'little'))
  for v in queue:
   row=np.unpackbits(np.frombuffer(v.to_bytes(q//8,'little'),dtype=np.uint8),bitorder='little')
   for perm in perms:
    add(int.from_bytes(np.packbits(row[perm],bitorder='little').tobytes(),'little'));ops+=1
  o=dict(n=n,i=i,modulus=pol,primitive=g,rank=len(piv),generator_images=ops);out.append(o);print(o,flush=True)
  (D/'outputs/kassami-closure.json').write_text(json.dumps(out,indent=2))
