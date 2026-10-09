"""Exact algebra checks for arithmetic bridge round 2; no asymptotic numerics."""
from fractions import Fraction as F
from itertools import product, combinations
from pathlib import Path
import importlib.util
import json
import sys

sys.dont_write_bytecode = True


def local_prime(p, d, e, band, A=3, h=1):
    beta=F(1, A+1) if band=='C' else F(1,2)
    theta=F(1,4)
    vertices=[0,2*h*d,2*h*(d+e),2*h*e]
    labels=[d,e,d,e]
    out=F(0)
    for x in range(p):
        val=F(1)
        for offset,label in zip(vertices,labels):
            lit=(x+offset)%p==0
            val*=beta**int(lit)
            if label%p==0:
                val*= A*int(lit) if band=='C' else F(int(lit))-theta/p
        out+=abs(val)/p
    return out


def local_checks():
    rows=[]
    for p in [5,7,11,17,31]:
        for h in [1,2]:
            # both labels divisible by p
            common_c=local_prime(p,p,2*p,'C',h=h)
            assert common_c==F(3,4)**4/p
            common_z=local_prime(p,p,2*p,'Z',h=h)
            formula=F(1,16)*(1-F(1,4*p))**4/p+(1-F(1,p))*F(1,4*p)**4
            assert common_z==formula
            assert common_z<=F(1,16*p)+F(1,256*p**4)
            # exactly one label divisible by p, nonzero difference mod p
            assert local_prime(p,p,p+1,'C',h=h)==0
            only_z=local_prime(p,p,p+1,'Z',h=h)
            theta=F(1,4)
            formula=3*theta**2/p**2-(2*theta**3+2*theta**2)/p**3
            assert only_z==formula
            assert only_z<=3*theta**2/p**2
            rows.append({'p':p,'h':h,'unique_center_exact':str(only_z),'common_center_exact':str(common_z)})
    return rows


def subset_product(xs):
    value=1
    for x in xs:value*=x
    return value


def euler_sum():
    core=[5];center=[7,11];primes=core+center
    subsets=[set(p for p,bit in zip(primes,bits) if bit) for bits in product([0,1],repeat=len(primes))]
    total=F(0);nonnested=F(0)
    for ds,es in product(subsets,repeat=2):
        if ds==es:continue
        d,e=subset_product(ds),subset_product(es)
        factor=F(1)
        for p in ds|es:
            factor*=local_prime(p,d,e,'C' if p in core else 'Z')
        total+=factor
        if ds-es and es-ds:nonnested+=factor
    c={p:local_prime(p,p,2*p,'C' if p in core else 'Z') for p in primes}
    u={p:local_prime(p,p,p+1,'Z') for p in center}
    expected=subset_product([1+c[p] for p in core])*(subset_product([1+c[p]+2*u[p] for p in center])-subset_product([1+c[p] for p in center]))
    assert total==expected
    cross=subset_product([1+c[p] for p in core])*(subset_product([1+c[p]+2*u[p] for p in center])-2*subset_product([1+c[p]+u[p] for p in center])+subset_product([1+c[p] for p in center]))
    assert nonnested==cross
    return {'direct_sum':str(total),'euler_difference':str(expected),'nonnested_sum':str(nonnested),'nonnested_euler_difference':str(cross)}


def rank(rows):
    a=[[F(v) for v in row] for row in rows];r=0
    for c in range(len(a[0])):
        pivot=next((i for i in range(r,len(a)) if a[i][c]),None)
        if pivot is None:continue
        a[r],a[pivot]=a[pivot],a[r];z=a[r][c];a[r]=[v/z for v in a[r]]
        for i in range(len(a)):
            if i!=r:
                z=a[i][c];a[i]=[v-z*w for v,w in zip(a[i],a[r])]
        r+=1
    return r


def trace_geometry():
    sym=[[1,1,0],[1,2,1],[1,1,2],[1,0,1]]
    direct=[[1,1,0,0],[1,0,1,0],[1,0,2,-1],[1,1,1,-1]]
    assert rank(sym)==rank(direct)==3
    assert all(sum(c*v for c,v in zip(row,[1,-1,-1,-1]))==0 for row in direct)
    # Directed cycles require a+c=b+d. Two different labels only yield retracing.
    count=0
    for a,b,c,d in product([11,13],repeat=4):
        if a+c!=b+d:continue
        x1=0;y0=2*a;y1=2*b;x2=2*(b-c)
        assert x1==x2 or y0==y1
        mids=[a,b,2*b-c,a+b-c]
        assert all(mids.count(t)%2==0 for t in set(mids))
        count+=1
    return {'symmetric_rank':3,'directed_rank':3,'directed_midpoint_null_vector':[1,-1,-1,-1],'two_label_directed_cycles_checked':count}


def cubic_signs():
    for ku,kw in product(range(7),repeat=2):
        lhs=(-1)**(ku+kw)*(-1)**(3*ku)*(-F(1,4))**kw
        assert lhs==F(1,4)**kw
    return 'lambda(uw) lambda(u)^3 (-theta)^omega(w) = theta^omega(w)'


def scout_checks():
    path=Path(__file__).with_name('arithmetic_obstructions.py')
    spec=importlib.util.spec_from_file_location('scout_obstructions',path)
    mod=importlib.util.module_from_spec(spec);spec.loader.exec_module(mod)
    return {'characters':[mod.check_character(q) for q in [5,7,11,17,31,101]],'renewal':mod.check_blocks(),'dilation':mod.check_dilation()}


if __name__=='__main__':
    result={'local_factors':local_checks(),'euler_sum':euler_sum(),'trace_geometry':trace_geometry(),'cubic_sign':cubic_signs(),'scout_rechecks':scout_checks()}
    print(json.dumps(result,indent=2))
