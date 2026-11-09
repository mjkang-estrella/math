#!/usr/bin/env python3
"""MIT. Exact cross-checks on copies, not a substitute for the analytic review."""
from pathlib import Path
import importlib.util,json,sys
from fractions import Fraction as F
sys.dont_write_bytecode=True

def load(name,path):
    s=importlib.util.spec_from_file_location(name,path);m=importlib.util.module_from_spec(s);s.loader.exec_module(m);return m
r=Path(__file__).resolve().parents[2]
ours=load('race',r/'packet/public/independent_certificate.py')
a=load('author',r/'packet/public/checks/author-certificate.py')
r2=load('r2',r/'packet/public/checks/r2-independent-certificate.py')
# No interpolation rerun: identity of the explicit cleared M and the independently
# produced T is the final algebraic condition used by that checker.
for k in range(1,5):
 for l in range(5-k):
    z=4-k-l
    p,R,den,D,T=ours.build(k,l,z)
    author=a.build(k,l,z)
    for key,got in [('Np',p),('NP',R),('Den',den),('D',D),('T',T)]:
        assert got==author[key].t,(k,l,z,key)
    M,V,*_=r2.build_M(k,l,z)
    exact=ours.add(ours.mul(ours.mul(T,V.t),V.t),ours.scale(M.t,-1))
    assert not exact,(k,l,z)
    print((k,l,z),'all five author polynomials identical; R2 T*V^2=M verified')
# Independent universal two-bracket algebra, polynomial in a,b,A,B,p,d;
# clear denominators and use P=pA,N=(1-p)B before cancellation.
nv=6;one={(0,)*nv:1};vs=[]
for i in range(nv):
 e=[0]*nv;e[i]=1;vs.append({tuple(e):1})
a,b,A,B,p,d=vs
add,mul,scale=ours.add,ours.mul,ours.scale
q=add(mul(add(a,A),add(b,B)),scale(mul(add(one,d),add(mul(mul(p,a),add(b,B)),mul(mul(add(one,scale(p,-1)),b),add(a,A)))),-1))
rhs=add(mul(mul(p,A),b),mul(mul(add(one,scale(p,-1)),B),a),scale(mul(mul(d,a),b),-1),mul(A,B),scale(mul(d,add(mul(mul(p,a),B),mul(mul(add(one,scale(p,-1)),b),A))),-1))
assert not add(q,scale(rhs,-1))
print('universal two-bracket identity: zero polynomial in six independent variables')
print('PASS')
