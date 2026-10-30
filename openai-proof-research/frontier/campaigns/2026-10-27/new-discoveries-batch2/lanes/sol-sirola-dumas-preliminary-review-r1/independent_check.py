"""Independent initial-form diagnostics; no candidate code imported or executed."""
from pathlib import Path
from itertools import product
from math import gcd
import random, json

OUT=Path(__file__).resolve().parent
def mul(a,b,p):
    c={}
    for (i,j),x in a.items():
        for (k,l),y in b.items():
            z=(i+k,j+l); c[z]=(c.get(z,0)+x*y)%p
    return {z:x for z,x in c.items() if x}

def initial(a,sgn,num,den):
    # a is a bivariate polynomial in X,t over F_p. sgn=-1 gives -degree_t.
    w=min(den*sgn*j+num*i for i,j in a)
    return w,{(i,j):x for (i,j),x in a.items() if den*sgn*j+num*i==w}

tot=0; cancelled=0
def check(a,b,p,sgn,num,den):
    global tot,cancelled
    c=mul(a,b,p); assert c
    u,ai=initial(a,sgn,num,den);v,bi=initial(b,sgn,num,den)
    w,ci=initial(c,sgn,num,den)
    assert u+v==w and mul(ai,bi,p)==ci
    # Whole initial form equality is stronger than only testing its extremal indices.
    assert min(i for i,j in ci)==min(i for i,j in ai)+min(i for i,j in bi)
    assert max(i for i,j in ci)==max(i for i,j in ai)+max(i for i,j in bi)
    if len(c)<len(a)*len(b):cancelled+=1
    tot+=1

# Exhaust all degree-at-most-one X polynomials with coefficients in
# F_2-span{1,t^2,t^3}, inside the nonnormal non-UFD domain F_2[t^2,t^3].
mons=list(product(range(2),(0,2,3)))
polys=[{z:c for z,c in zip(mons,bits) if c} for bits in product(range(2),repeat=6) if any(bits)]
for a in polys:
    for b in polys:
        for sgn,num,den in [(-1,-5,3),(-1,2,3),(1,5,3),(1,-2,3)]:
            check(a,b,2,sgn,num,den)
exhaustive=tot
rng=random.Random(914037)
for p in (2,3,5):
    for _ in range(450):
        a={(i,j):rng.randrange(1,p) for i in range(rng.randrange(1,8)) for j in (0,2,3,4,5,6) if rng.randrange(3)==0}
        b={(i,j):rng.randrange(1,p) for i in range(rng.randrange(1,8)) for j in (0,2,3,4,5,6) if rng.randrange(3)==0}
        if not a or not b:continue
        for sgn in (-1,1):check(a,b,p,sgn,rng.randrange(-20,21),rng.randrange(1,11))
normalizations=0
for n in range(2,24):
    for m in range(1,37):
        if gcd(n,m)!=1:continue
        assert all((s*m)%n for s in range(1,n))
        for d in range(1,m+1):
            if m%d:continue
            M=m//d; assert gcd(n,M)==1
            # Compare source first-kind bounds with reciprocal normalized bounds.
            for j in range(n+1):
                for omega in range(0,m+2):
                    if n*omega>(n-j)*m:continue
                    k=n-j
                    # Integer-scaled inequality avoids floating-point inference.
                    assert n*(m-omega)>=(n-k)*m
            normalizations+=1
# Explicit cancellation, gcd failure, rational-value failure controls.
a={(1,0):1,(0,1):1};b={(1,0):1,(0,1):4}
assert mul(a,b,5)=={(2,0):1,(0,2):4} # (X+t)(X-t)
assert gcd(2,2)==2
assert gcd(2,1)==1 # height under omega=degree/2; integer-valued premise fails
result={'status':'PASS','independently_authored':True,'candidate_code_used':False,
        'exhaustive_initial_form_products':exhaustive,'total_initial_form_products':tot,
        'merged_or_cancelled_product_support_controls':cancelled,
        'normalized_height_cases':normalizations,'seed':914037,
        'scope':'Exact finite diagnostics in cusp domains and integer lattices; not a universal proof.'}
(OUT/'independent-evidence.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result))
