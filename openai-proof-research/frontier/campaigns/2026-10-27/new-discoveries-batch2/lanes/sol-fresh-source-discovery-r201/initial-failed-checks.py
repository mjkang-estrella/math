"""Exact pointwise linear algebra only; no universal rigidity claim."""
import itertools, json
from pathlib import Path
import sympy as S

def matrix(d, coefficients):
    triples=list(itertools.combinations_with_replacement(range(d),3))
    lookup={t:i for i,t in enumerate(triples)}
    h=S.symbols('h:'+str(d)); z=S.symbols('z:'+str(d*len(triples)))
    def k(v,w):
        return S.Matrix([sum(coefficients[lookup[tuple(sorted((a,b,c)))]]*v[b]*w[c]
            for b in range(d) for c in range(d)) for a in range(d)])
    def dk(v,w,t):
        return S.Matrix([sum(v[j]*z[j*len(triples)+lookup[tuple(sorted((a,b,c)))]]*w[b]*t[c]
            for j in range(d) for b in range(d) for c in range(d)) for a in range(d)])
    hh=S.Matrix(h); q=k(hh,hh)
    e=2*k(hh,dk(hh,hh,hh))+5*dk(q,hh,hh)-4*dk(hh,hh,q)
    equations=[]
    for a in e: equations.extend(S.Poly(S.expand(a),*h).coeffs())
    return S.linear_eq_to_matrix(equations,z)[0]

rows=[]
for d,cs in [(2,[1,0,0,0]),(2,[1,0,0,1]),(2,[1,2,3,5]),(2,[0,1,1,0]),
             (3,[1,0,0,0,0,0,1,0,0,1]),(3,[1,2,3,5,7,11,13,17,19,23])]:
    m=matrix(d,cs); r=m.rank(); rows.append(dict(d=d,cubic=cs,columns=m.cols,rank=r,nullity=m.cols-r))
    if d==2 and cs==[1,0,0,0]:
        rows[-1]['kernel']=[[str(v) for v in x] for x in m.nullspace()]
print(json.dumps(dict(scope=__doc__,rows=rows),indent=2))
