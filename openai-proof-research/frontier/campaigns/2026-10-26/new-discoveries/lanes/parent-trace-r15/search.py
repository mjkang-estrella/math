#!/usr/bin/env python3
"""Source Lemma2.2.3 exact coefficient polynomial, then bounded numeric search."""
from itertools import product
from collections import defaultdict, Counter
from pathlib import Path
import json
import numpy as np
import sympy as s
from scipy.optimize import minimize

K = 6
nodes = [-2, -1, 1]
edges = [(i,j) for i in range(3) for j in range(i,3)]
lookup = {e:i for i,e in enumerate(edges)}
z=s.Symbol('z')
dd={}
coeff=defaultdict(lambda:s.Rational(0))
for word in product(range(3),repeat=K):
    cnt=tuple(word.count(i) for i in range(3))
    if cnt not in dd:
        if cnt[2]==0:
            dd[cnt]=s.Rational(0)
        else:
            expr=K-1
            expr=expr*z**(K-2)
            for i in range(2):
                expr/= (z-nodes[i])**cnt[i]
            dd[cnt]=s.diff(expr,z,cnt[2]-1).subs(z,nodes[2])/s.factorial(cnt[2]-1)
    exp=[0]*6
    for i in range(K):
        edge=tuple(sorted([word[i],word[(i+1)%K]]))
        exp[lookup[edge]]+=1
    coeff[tuple(exp)] += dd[cnt]/K
coeff={e:s.factor(v) for e,v in coeff.items() if v}
xs=s.symbols('x:6')
expr=sum(v*s.prod(x**j for x,j in zip(xs,e)) for e,v in coeff.items())
evaluate=s.lambdify([xs],expr,'numpy',cse=True)
rng=np.random.default_rng(20261027)
best=(float('inf'),None)
for batch in range(40):
    X=rng.normal(size=(6,2000)); X/=np.linalg.norm(X,axis=0)
    vals=evaluate(X)
    j=np.argmin(vals)
    if vals[j]<best[0]:best=(vals[j],X[:,j])
for i in range(12):
    x=best[1] if i==0 else rng.normal(size=6)
    r=minimize(lambda x:evaluate(x/np.linalg.norm(x)),x,method='BFGS',options={'maxiter':700})
    v=evaluate(r.x/np.linalg.norm(r.x))
    if v<best[0]:best=(v,r.x/np.linalg.norm(r.x))
result={'status':'finite numerical evidence, not a proof','order':K,'nodes':nodes,
        'function':'max(x,0)^(K-1)','polynomial_terms':len(coeff),
        'coefficient_exact':str(expr),'min_numeric':float(best[0]),
        'best_edge_coordinates':best[1].tolist(),'samples':80000}
Path(__file__).with_name('search-result.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
