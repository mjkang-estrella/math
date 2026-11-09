import numpy as np,json,pathlib,sys,time
D=pathlib.Path(__file__).resolve().parents[1];out=[]
for n,p,k in [(n,3,3) for n in range(16,25)]+[(n,4,3) for n in range(21,25)]:
 M=1<<n;a=np.zeros(M,dtype=np.uint8)
 for i in range(n):
  L=1<<i;nb=sum(1<<j for j in range(i) if min((i-j)%n,(j-i)%n)<=p);idx=np.arange(L,dtype=np.uint32);a[L:2*L]=np.maximum(a[:L],1+a[idx&np.uint32((M-1)^nb)])
 fs={}
 for x in np.flatnonzero(a<k):
  x=int(x);fs.setdefault(x.bit_count(),[]).append(x)
 ranks={0:0};dims=sorted(fs)
 for size in dims[1:]:
  rows={x:i for i,x in enumerate(fs[size-1])};piv={}
  for s in fs[size]:
   col=0;t=s
   while t:
    b=t&-t;t^=b;col^=1<<rows[s^b]
   while col:
    lead=col.bit_length()-1
    if lead not in piv:piv[lead]=col;break
    col^=piv[lead]
  ranks[size]=len(piv)
 betti={str(size-1):len(fs[size])-ranks[size]-ranks.get(size+1,0) for size in dims}
 row={'n':n,'p':p,'k':k,'face_counts':{str(s-1):len(v) for s,v in fs.items()},'reduced_mod2_betti':betti};out.append(row);(D/'outputs/cut-homology.json').write_text(json.dumps(out,indent=2)+'\n');print(row,flush=True)
