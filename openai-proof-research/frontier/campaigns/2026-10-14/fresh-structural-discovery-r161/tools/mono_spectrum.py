from fractions import Fraction as F
from math import comb,prod,log2
from pathlib import Path
import json
R=Path("frontier/campaigns/2026-10-14/fresh-structural-discovery-r161")
def fall(n,k):return prod(range(n-k+1,n+1)) if 0<=k<=n else 0
out=[]
for q,N in [(2,24),(3,24),(3,36),(3,60),(4,32),(4,64)]:
 h=N//q;w=N//2;D=comb(h,h//2)
 distribution=[(q*j,F(comb(h//2,j)**2,D)) for j in range(h//2+1)]
 assert sum(p for j,p in distribution)==1
 eigen=[]
 for l in range(w+1):
  value=sum(p*sum((-1)**(l-u)*comb(l,u)*F(fall(j,u),fall(w,u))*F(fall(w-j,l-u),fall(N-w,l-u)) for u in range(l+1)) for j,p in distribution)
  assert 0<=value<=1
  eigen.append(value)
 traces={str(power):sum((comb(N,l)-(comb(N,l-1) if l else 0))*eigen[l]**power for l in range(w+1)) for power in [2,q,q+1]}
 item={"q":q,"N":N,"diagonal_trace2_lower":str(F(comb(N,w),D**2)),"moments":{k:float(v) for k,v in traces.items()},"eigenvalues":[str(x) for x in eigen],"max_level_ge_6":float(max(eigen[6:]))}
 out.append(item);print(q,N,item["moments"],item["max_level_ge_6"])
(R/"private/mono-spectrum.json").write_text(json.dumps({"purpose":"Exact finite diagnostic, not a proof of uniform smoothing or a contribution gate", "results":out},indent=2)+"\n")
