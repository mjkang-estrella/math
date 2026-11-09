#!/usr/bin/env python3
"""Exact integer diagnostics for the crossed factorization; no theorem gate."""
import itertools
import json

def matmul(a,b):
    return [[sum(x*y for x,y in zip(row,col)) for col in zip(*b)] for row in a]
def tr(a):
    return list(map(list,zip(*a)))
def require_equal(a,b,label):
    if a!=b:
        raise RuntimeError('Exact identity failed: '+label)

def run(n,perm):
    ix=list(itertools.product(range(n),repeat=2))
    def aa(i,j,a,b):
        return ((i+1)*7+(j+1)*11+(a+1)*13+(b+1)*17+i*j*3-a*b*5)%19-9
    def ff(k,l,a,b):
        z=(k,l,a,b)
        return aa(*(z[p] for p in perm))
    q=[[sum(aa(i,j,a,b)*ff(k,l,a,b) for a,b in ix) for j,l in ix] for i,k in ix]
    # Intermediate coordinates (a,b,j,k).
    mid=list(itertools.product(range(n),repeat=4))
    rr=[[aa(i,j,a,b) if k==h else 0 for a,b,j,h in mid] for i,k in ix]
    cc=[[ff(k,l,a,b) if j==h else 0 for h,l in ix] for a,b,j,k in mid]
    require_equal(matmul(rr,cc),q,'Q=RC')
    ga=[[sum(aa(i,j,a,b)*aa(ip,j,a,b) for j in range(n) for a,b in ix) for ip in range(n)] for i in range(n)]
    gf=[[sum(ff(k,l,a,b)*ff(k,lp,a,b) for k in range(n) for a,b in ix) for lp in range(n)] for l in range(n)]
    require_equal(matmul(rr,tr(rr)),[[ga[i][ip] if k==kp else 0 for ip,kp in ix] for i,k in ix],'RR*=Gram_singleton_i tensor I')
    require_equal(matmul(tr(cc),cc),[[gf[l][lp] if j==jp else 0 for jp,lp in ix] for j,l in ix],'C*C=I tensor Gram_singleton_l')
    return {'dimension':n,'second_tensor_permutation':list(perm),'exact_integer_identities':3}

if __name__=='__main__':
    cases=[run(n,p) for n in (2,3) for p in ((0,1,2,3),(2,0,3,1),(3,2,1,0))]
    print(json.dumps({'status':'PASS_EXACT_FACTORIZATION_DIAGNOSTICS_ONLY','cases':cases},indent=2))
