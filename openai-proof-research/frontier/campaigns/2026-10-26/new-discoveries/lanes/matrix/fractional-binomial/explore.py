import math,random,json
from pathlib import Path
import numpy as np
root=Path(__file__).resolve().parent
rng=random.Random(352508)
def ratio(a,n,p):
 if p==0 or p==1:return math.exp((a-1)*math.log(2))
 j=np.arange(n+1,dtype=float)
 lg=np.array([math.lgamma(a*n+1)-math.lgamma(a*t+1)-math.lgamma(a*(n-t)+1) for t in j])
 terms=lg+a*j*math.log(p)+a*(n-j)*math.log1p(-p)
 m=float(np.max(terms));return (a-1)*math.log(2)+m+math.log(float(np.exp(terms-m).sum()))
rows=[]
for a in [2.000001,2.001,2.01,2.1,2.25,2.5,2.9,3.001,3.5,4.1,4.5,5.5,6.5,8.5,12.5,20.5,40.5]:
 best=(float('inf'),None,None)
 for n in range(2,151):
  for p in np.r_[np.geomspace(.000001,.05,45),np.linspace(.05,.5,91)]:
   v=ratio(a,n,float(p))
   if v<best[0]:best=(v,n,float(p))
 rows.append({'alpha':a,'minimum_log_ratio':best[0],'k':best[1],'p':best[2]})
print(json.dumps(rows,indent=2));(root/'grid-results.json').write_text(json.dumps(rows,indent=2)+'\n')
