import sys,pathlib,json
D=pathlib.Path(__file__).resolve().parents[1];sys.path.insert(0,str(D.parent/'fresh-corpus-r10/pydeps'))
import numpy as np
out=[]
for n,pol in [(5,0x25),(7,0x83),(9,0x211),(11,0x805)]:
 q=1<<n;X=np.arange(q,dtype=np.int32);M=np.zeros((q,q),dtype=np.int32);a=X.copy()
 for i in range(n):
  M^=a[:,None]*((X>>i)&1)[None,:];a<<=1;a^=(a>>n)*pol
 def pw(x,e):
  y=np.ones_like(x)
  while e:
   if e&1:y=M[y,x]
   x=M[x,x];e>>=1
  return y
 s=2**((n-1)//2)+2**(((n-1)//4) if n%4==1 else ((3*n-1)//4))-1
 B=np.unique(pw(X,s)^pw(X^1,s));inB=np.zeros(q,dtype=bool);inB[B]=True
 counts=np.zeros(q,dtype=np.int64);stab=0
 for a in range(1,q):
  # Every affine transform a*B+b containing 0 and 1. Inverse representation counts b,b+a,y in B.
  bs=X[inB & inB[X^a]];inv=int(pw(np.array(a),q-2))
  ts=M[inv,np.bitwise_xor(bs[:,None],B[None,:])].ravel();counts+=np.bincount(ts,minlength=q)
  # Count translations identifying aB with B by candidate image of first member.
  A=M[a,B];cands=A[0]^B
  stab+=sum(bool(np.all(inB[A^b])) for b in cands)
 o=dict(n=n,modulus=pol,s=s,block_size=len(B),stabilizer=stab,triple_min=int(min(counts[2:])),triple_max=int(max(counts[2:])),expected=q*(q-4)//8);out.append(o);print(o,flush=True)
(D/'outputs/apn.json').write_text(json.dumps(out,indent=2))
