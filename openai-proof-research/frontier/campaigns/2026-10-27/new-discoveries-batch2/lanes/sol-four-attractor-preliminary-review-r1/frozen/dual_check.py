import json,pathlib
from fractions import Fraction
import numpy as np
from scipy.optimize import linprog
L=pathlib.Path(__file__).resolve().parent;c=json.loads((L/'attractor-certificate.json').read_text());ss=c['essential_constraints']
A=np.array([[int(i in row['positions']) for row in ss] for i in range(c['length'])])
r=linprog(-np.ones(len(ss)),A_ub=A,b_ub=np.ones(c['length']),bounds=(0,None),method='highs',options={'threads':1})
w=[Fraction(float(x)).limit_denominator(1000) for x in r.x]
assert all(sum(w[j] for j,s in enumerate(ss) if i in s['positions'])<=1 for i in range(c['length']))
out=dict(total=str(sum(w)),weights=[dict(factor=s['factor'],weight=str(x)) for s,x in zip(ss,w) if x]);(L/'dual-results.json').write_text(json.dumps(out,indent=2));print(json.dumps(out,indent=2))
