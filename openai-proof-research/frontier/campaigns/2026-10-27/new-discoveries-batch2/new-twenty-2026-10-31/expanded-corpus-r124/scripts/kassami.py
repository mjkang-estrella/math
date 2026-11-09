import sys,pathlib,json,math
sys.dont_write_bytecode=True
D=pathlib.Path(__file__).resolve().parents[1];sys.path.insert(0,str(D.parent/'fresh-corpus-r10/pydeps'))
import numpy as np
out=[]
for n,pol in [(5,0x25),(7,0x83),(9,0x211)]:
 q=1<<n;X=np.arange(q,dtype=np.int32);M=np.zeros((q,q),dtype=np.int32);a=X.copy()
 for j in range(n):M^=a[:,None]*((X>>j)&1)[None,:];a<<=1;a^=(a>>n)*pol
 def pw(x,e):
  y=np.ones_like(x)
  while e:
   if e&1:y=M[y,x]
   x=M[x,x];e>>=1
  return y
 assert np.all(M[X[1:],pw(X[1:],q-2)]==1)
 for i in range(1,(n+1)//2):
  if math.gcd(i,n)!=1:continue
  s=2**(2*i)-2**i+1;inv=pow(2**i+1,-1,q-1);omit=np.unique(pw(pw(X,s)^pw(X^1,s)^1,inv));B=X[~np.isin(X,omit)]
  piv={};processed=0
  for a in range(1,q):
   block=np.zeros(q,dtype=np.uint8);block[M[a,B]]=1
   rows=block[np.bitwise_xor(X[:,None],X[None,:])]
   for bs in np.packbits(rows,axis=1,bitorder='little'):
    v=int.from_bytes(bs.tobytes(),'little');processed+=1
    while v:
     k=v.bit_length()-1
     if k not in piv:piv[k]=v;break
     v^=piv[k]
  o=dict(n=n,i=i,block_size=len(B),affine_images_with_multiplicity=processed,binary_incidence_rank=len(piv));out.append(o);print(o,flush=True)
(D/'outputs/kassami.json').write_text(json.dumps(out,indent=2))
