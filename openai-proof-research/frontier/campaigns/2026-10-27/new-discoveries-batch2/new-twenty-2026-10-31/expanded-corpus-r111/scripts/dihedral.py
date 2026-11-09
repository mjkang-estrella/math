import numpy as np,json,pathlib
L=pathlib.Path(__file__).resolve().parents[1];out=[]
for n in range(3,13):
 N=2*n
 def mul(a,b):return ((a%n+(1 if a<n else -1)*(b%n))%n)+n*((a//n)^(b//n))
 def inv(a):return (-a)%n if a<n else a
 S=np.zeros(1,dtype=np.uint32);D=S.copy()
 for x in range(N):
  ind=np.arange(1<<x,dtype=np.uint32);ss=S.copy()|(1<<mul(x,x));dd=D.copy()|1
  for y in range(x):
   yes=((ind>>y)&1).astype(bool)
   ss[yes]|=(1<<mul(x,y))|(1<<mul(y,x));dd[yes]|=(1<<mul(x,inv(y)))|(1<<mul(y,inv(x)))
  S=np.concatenate([S,ss]);D=np.concatenate([D,dd])
 delta=np.bitwise_count(S).astype(int)-np.bitwise_count(D).astype(int)
 row={'n':n,'subsets':1<<N,'MSTD':int((delta>0).sum()),'MDTS':int((delta<0).sum()),'balanced':int((delta==0).sum())};out.append(row);print(row,flush=True);(L/'outputs/dihedral.json').write_text(json.dumps(out,indent=2))
