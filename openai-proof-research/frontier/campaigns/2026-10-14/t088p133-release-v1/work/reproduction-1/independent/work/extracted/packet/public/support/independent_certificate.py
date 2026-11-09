#!/usr/bin/env python3
"""MIT. Round3 independent certificate, using competing exponential phases.
No author/round2 imports, interpolation, partial fractions or polynomial division.
For U=sum u_i E_i, V=sum v_j E'_j, race their first unfinished phases.
The U phase wins with probability v_j/(u_i+v_j), the V phase with u_i/(u_i+v_j).
After either win the other's residual phase is independent with its original law.
p_ij=P(U_remaining>V_remaining), R_ij=E(U_remaining-V_remaining)^+.
At V completion p=1,R=sum remaining u; at U completion p=R=0.
Clear the rectangular denominator prod_{a>=i,b>=j}(u_a+v_b).
This gives the polynomial recurrence in build(), valid also for repeated rates.
"""
import json
import sys
from functools import lru_cache
from itertools import combinations
from pathlib import Path
sys.dont_write_bytecode = True

def add(*ps):
    q={}
    for p in ps:
        for e,c in p.items(): q[e]=q.get(e,0)+c
    return {e:c for e,c in q.items() if c}
def scale(p,c): return {e:c*v for e,v in p.items() if c*v}
def mul(p,q):
    out={}
    for a,c in p.items():
        for b,d in q.items():
            e=tuple(a[i]+b[i] for i in range(len(a)))
            out[e]=out.get(e,0)+c*d
    return {e:c for e,c in out.items() if c}
def prod(ps,one):
    out=one
    for p in ps: out=mul(out,p)
    return out

def build(k,l,z):
    nv=k+l; one={(0,)*nv:1}; zero={}
    variables=[]
    for i in range(nv):
        e=[0]*nv; e[i]=1; variables.append({tuple(e):1})
    u=[add(*variables[i:k]) for i in range(k)]
    v=[add(*variables[k+j:]) for j in range(l)]
    cross=[[add(a,b) for b in v] for a in u]
    @lru_cache(None)
    def race(i,j):
        if i==k: return zero,zero
        if j==l: return one,add(*u[i:])
        pa,ra=race(i+1,j); pb,rb=race(i,j+1)
        first=mul(v[j],prod(cross[i][j+1:],one))
        second=mul(u[i],prod([cross[a][j] for a in range(i+1,k)],one))
        return add(mul(first,pa),mul(second,pb)),add(mul(first,ra),mul(second,rb))
    p,r=race(0,0)
    den=prod([cross[i][j] for i in range(k) for j in range(l)],one)
    # Direct pair distances in sorted order; no use of the author's rank formula.
    ordered=[scale(t,-1) for t in v]+[zero]*z+list(reversed(u))
    D=add(*(add(ordered[j],scale(ordered[i],-1)) for i,j in combinations(range(k+l+z),2)))
    T=add(scale(mul(r,den),k+l+z+1),scale(mul(D,mul(p,p)),-1))
    return p,r,den,D,T

def serial(p): return [[list(e),c] for e,c in sorted(p.items())]

def main():
    witnesses=[]
    for k in range(1,5):
        for l in range(5-k):
            z=4-k-l
            p,r,den,D,T=build(k,l,z)
            assert T and min(T.values())>0
            endpoints={k-1} | ({k+l-1} if l else set())
            strict={e:c for e,c in T.items() if all(not a or i in endpoints for i,a in enumerate(e))}
            assert strict
            witnesses.append(dict(pattern=[k,l,z],variables=[f'x{i+1}' for i in range(k)]+[f'y{j+1}' for j in range(l)],
                                  Np=serial(p),NP=serial(r),Den=serial(den),D=serial(D),T=serial(T),strict=serial(strict)))
            print((k,l,z),'terms',len(T),'degree',max(map(sum,T)),'min',min(T.values()),'endpoint witness',serial(strict),flush=True)
    out=Path(sys.argv[1]) if len(sys.argv)>1 else Path(__file__).with_name('certificate-witness.json')
    out.write_text(json.dumps(witnesses,indent=2)+'\n')
    print('PASS: ten complete exact coefficient witnesses; repeated rates allowed by derivation.')
if __name__=='__main__': main()
