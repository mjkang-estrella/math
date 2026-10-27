"""Finite numerical probe only; never a proof or exclusion."""
import json
from pathlib import Path
import numpy as np

rng = np.random.default_rng(290393)

def power(a, t):
    d, q = np.linalg.eigh(a)
    return (q * d**t) @ q.T

def geometric(a, b):
    h, j = power(a, .5), power(a, -.5)
    return h @ power(j @ b @ j, .5) @ h

def sample(n, h):
    q, _ = np.linalg.qr(rng.normal(size=(n,n)))
    # Endpoint-biased spectra, including exact endpoint projections.
    d = np.where(rng.random(n)<.7, rng.integers(0,2,n), rng.random(n))
    return (q * (1+(h-1)*d)) @ q.T

best = {'polya': [1., None], 'diaz': [1., None]}
count = 0
for n in [2,3,4]:
  for h in [1.1, 2, 4, 10, 30, 100, 1000]:
    for j in range(800):
      a1,b1,a2,b2 = [sample(n,h) for _ in range(4)]
      a,b = (a1+a2)/2,(b1+b2)/2
      c = (geometric(a1,b1)+geometric(a2,b2))/2
      d = geometric(a,b)
      alpha=(h+1)/(2*np.sqrt(h))
      for key,lhs,constant in [('polya',d,alpha),('diaz',(a+b)/2,alpha)]:
        ratio=float(np.linalg.norm(lhs @ np.linalg.inv(c),2)/constant)
        if ratio>best[key][0]:
          best[key]=[ratio, {'n':n,'h':h,'a1':a1.tolist(),'b1':b1.tolist(),'a2':a2.tolist(),'b2':b2.tolist()}]
      count+=1
Path('numerical-squared.json').write_text(json.dumps({'trials':count,'best':best,'scope':'finite numerical evidence only'},indent=2))
print(json.dumps({'trials':count,'best_ratios':{k:v[0] for k,v in best.items()}}))
