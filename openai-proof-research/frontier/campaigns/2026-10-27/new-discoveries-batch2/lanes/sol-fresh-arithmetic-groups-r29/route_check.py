#!/usr/bin/env python3
import os,resource,signal,itertools,json
for v in ['OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS']:os.environ[v]='1'
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,512*1024**2));resource.setrlimit(resource.RLIMIT_CPU,(15,15));signal.alarm(20)
from fractions import Fraction as Q
# A5 classes 1,2A,3A,5A,5B. Standard degree-four character is fixed points minus one.
sizes=[1,15,20,12,12];chi=[4,0,1,-1,-1];reg=[60,0,0,0,0];triv=[1]*5
F=[reg[i]-5*chi[i]+5 for i in range(5)]
assert F==[45,5,0,10,10] and min(F)>=0
inner=sum(Q(s*a*b,60) for s,a,b in zip(sizes,F,chi));assert inner==-1
# Independent permutation evaluation of standard character / conjugacy class counts.
G=[p for p in itertools.permutations(range(5)) if sum(p[i]>p[j] for i in range(5) for j in range(i+1,5))%2==0]
def order(p):
 q=tuple(range(5))
 for k in range(1,61):
  q=tuple(p[q[i]] for i in range(5))
  if q==tuple(range(5)):return k
counts={}
for p in G:
 o=order(p);counts[o]=counts.get(o,0)+1
 expected={1:4,2:0,3:1,5:-1}[o];assert sum(p[i]==i for i in range(5))-1==expected
assert counts=={1:1,2:15,3:20,5:24}
# Restriction decompositions of F on the three maximal-subgroup types.
# A4 irreducibles 1,1',1'',3; D10 irreducibles 1,sign,2a,2b; S3 irreducibles 1,sign,2.
restrictions={}
for name,index,degrees,chi_mult in [('A4',5,[1,1,1,3],[1,0,0,1]),('D10',6,[1,1,2,2],[0,0,1,1]),('S3',10,[1,1,2],[1,1,1])]:
 m=[index*d-5*c+5*(j==0) for j,(d,c) in enumerate(zip(degrees,chi_mult))]
 assert min(m)>=0 and sum(x*d for x,d in zip(m,degrees))==45
 restrictions[name]=m
# Divisor-closed/rational power-closed subset counterexample in C6: orders 1,2,3 but not 6.
# Sum of a faithful character on the selected elements is 1-1+(zeta3+zeta3^2)=-1.
assert 1-1-1==-1
print(json.dumps(dict(F_values=F,negative_irreducible_multiplicity=str(inner),proper_maximal_restrictions=restrictions,A5_order_counts=counts,warning='method falsifiers only, not source counterexamples'),indent=2))
