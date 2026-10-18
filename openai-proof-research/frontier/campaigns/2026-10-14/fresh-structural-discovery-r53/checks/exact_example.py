#!/usr/bin/env python3
"""MIT. Exact finite support calculation, not a general theorem checker."""
from fractions import Fraction as Q
from itertools import product
import json
U=((Q(-1),Q(3,4)),(Q(3,4),Q(-1,4)))
E=((0,1),(0,2),(0,3),(3,4))
def density(edges,kernel,n):
 N=len(kernel)
 return sum((prod(kernel[x[a]][x[b]] for a,b in edges) for x in product(range(N),repeat=n)),Q())/N**n
def prod(xs):
 r=Q(1)
 for x in xs:r*=x
 return r
V=tuple(tuple(Q(s+t,2)*U[x][y] for y in range(2) for t in (-1,1)) for x in range(2) for s in (-1,1))
W=tuple(tuple((1+z)/2 for z in row) for row in V)
Wc=tuple(tuple(1-z for z in row) for row in W)
f=density(E,U,5);p=density(((0,1),(1,2)),U,3)
normalized=8*(density(E,W,5)+density(E,Wc,5))
assert f==Q(-5,4096) and p==Q(5,128)
assert normalized==1+p+f/16 and normalized>1
print(json.dumps({'full_term':str(f),'path_term':str(p),'normalized_two_color_sum':str(normalized),'scope':'one explicit rational example; not BUC proof or refutation'},indent=2))
