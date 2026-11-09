from pathlib import Path
import numpy as np,json
D=Path(__file__).resolve().parents[1];N=600;out=[]
# Product over d: ((1+q^d)/(1-q^d))^r for even d, power s for odd d.
for k in range(1,7):
 for i in range(4):
  for j in range(4):
   r=2**(k+1)*j+2**k-1;s=2**k*i+1;mod=2**(k+2)
   a=np.zeros(N+1,dtype=np.int64);a[0]=1
   for d in range(1,N+1):
    c=r if d%2==0 else s
    # exponentiate truncated overpartition factor by squaring
    f=np.zeros(N//d+1,dtype=np.int64);f[0]=1;f[1:]=2
    g=np.zeros_like(f);g[0]=1
    while c:
     if c&1:g=np.convolve(g,f)[:len(f)]%mod
     f=np.convolve(f,f)[:len(f)]%mod;c//=2
    new=a.copy()
    for t in range(1,len(g)):new[t*d:]=(new[t*d:]+g[t]*a[:-t*d])%mod
    a=new
   bad=[(int(v),int(a[v]),2**(k+1) if v%3==2 else mod) for v in range(N+1) if (v%3==2 and a[v]%(2**(k+1))) or (v%9 in [3,6] and a[v]%mod)]
   out.append(dict(k=k,i=i,j=j,N=N,bad=bad));print(out[-1],flush=True)
   (D/'outputs/partitions.json').write_text(json.dumps(out,indent=2))
