import os
for name in ('OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS'):
    os.environ[name]='1'
import resource
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,512*1024**2))
resource.setrlimit(resource.RLIMIT_CPU,(40,40))
import json
from functools import lru_cache
from pathlib import Path

def mul(a,b):
    c=0
    while b:
        low=b&-b
        c ^= a << (low.bit_length()-1)
        b ^= low
    return c

def square(a):
    c=0
    while a:
        low=a&-a
        c |= 1 << (2*(low.bit_length()-1))
        a ^= low
    return c

@lru_cache(None)
def trees(n):
    if n==1: return (None,)
    return tuple((a,b) for k in range(1,n) for a in trees(k) for b in trees(n-k))

@lru_cache(None)
def data(t):
    if t is None: return 2,((0,1),)
    a,wa=data(t[0]); b,wb=data(t[1]); b2=square(b)
    p=square(a)^mul(b2,b)
    assert p
    return p,tuple((l+1,mul(a,w)) for l,w in wa)+tuple((l,mul(b2,w)) for l,w in wb)

def relation(vs):
    piv={}
    for j,v in enumerate(vs):
        mask=1<<j
        while v:
            d=v.bit_length()-1
            if d not in piv:
                piv[d]=(v,mask); break
            w,m=piv[d]; v^=w; mask^=m
        if not v: return mask
    return None

def fmt(t):
    return 'x' if t is None else 'F('+fmt(t[0])+','+fmt(t[1])+')'

def main():
    checked=0; failure=None; counts=[]; repeated_degree=None
    for n in range(1,12):
        count=0
        for t in trees(n):
            p,ws=data(t); count+=1; checked+=1
            for l in sorted(set(l for l,w in ws)):
                positions=[i for i,(ll,w) in enumerate(ws) if ll==l]
                vs=[ws[i][1] for i in positions]
                degrees=[v.bit_length()-1 for v in vs]
                if repeated_degree is None and len(set(degrees))<len(degrees):
                    repeated_degree={'tree':fmt(t),'left_depth':l,
                                     'positions':positions,'degrees':degrees,
                                     'polynomials_hex':[hex(v) for v in vs]}
                rel=relation(vs)
                if rel is not None:
                    failure={'leaves':n,'tree':fmt(t),'left_depth':l,
                             'positions_zero_based':[positions[j] for j in range(len(vs)) if rel>>j&1],
                             'mod2_polynomial_bitsets':[hex(v) for v in vs]}
                    break
            if failure: break
        counts.append({'leaves':n,'trees_checked':count})
        if failure: break
    result={'checked':checked,'counts':counts,'fixed_left_depth_independence_obstruction':failure,
            'distinct_leading_degree_shortcut_counterexample':repeated_degree,
            'scope':'Bounded diagnostic only. No full isolation or source theorem.'}
    Path(__file__).with_name('checks.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__=='__main__': main()
