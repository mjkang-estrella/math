"""Exploratory floating-point falsification only, never a certificate."""
import numpy as np, random,json
from pathlib import Path
rng=random.Random(473)
def deriv(roots,q):
 a=np.polynomial.polynomial.polyfromroots([-x for x in roots])
 b=np.array([a[k]*(q**k-1)/(q-1) for k in range(1,len(a))])
 return np.sort(-np.roots(b[::-1]).real)
for it in range(100000):
 n=rng.randrange(3,9);q=1+rng.random()*2
 f=[1.]
 for i in range(n-1):f.append(f[-1]*q*(1+3*rng.random()))
 g=[rng.uniform(f[i],f[i+1]) for i in range(n-1)]
 if any(g[i+1]<q*g[i] for i in range(n-2)):continue
 df=deriv(f,q);dg=deriv(g,q)
 if any(not (df[i]<=dg[i]+1e-7<=df[i+1]+1e-7) for i in range(n-2)):
  r=dict(status='candidate failure',iteration=it,q=q,f=f,g=g,df=df.tolist(),dg=dg.tolist());break
else:r=dict(status='no exploratory failure in 100000 attempts')
print(r);Path(__file__).with_suffix('.json').write_text(json.dumps(r,indent=2))
