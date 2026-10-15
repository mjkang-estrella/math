#!/usr/bin/env python3
"""Specified exact symbolic checks, not a parameter scan or infinite proof."""
from fractions import Fraction as Q
from pathlib import Path
import json
N=7
zero=[Q(0)]*N
def mul(a,b):
    return [sum((a[j]*b[i-j] for j in range(i+1)),Q(0)) for i in range(N)]
def add(a,b):return [x+y for x,y in zip(a,b)]
def scale(a,c):return [x*c for x in a]
def log1(c):return [Q(0)]+[Q((-1)**(i+1),i)*c**i for i in range(1,N)]
def const(a,b=Q(0)):return [Q(a),Q(b)]+[Q(0)]*(N-2)
L=add(log1(Q(2)),scale(log1(Q(-1)),-1))
i=scale(add(mul(const(1,2),log1(Q(2))),scale(mul(const(1,-1),log1(Q(-1))),2)),Q(1,3))
j=scale(mul(const(0,1),L),Q(1,3))
b=scale(mul(const(1,1),mul(L,L)),Q(1,9))
V=add(b,scale(mul(j,j),-2))
assert i[2:4]==[1,Q(-1,3)]
assert j[2:4]==[1,Q(-1,2)]
assert b[2:4]==[1,0]
assert V[2:5]==[1,0,Q(-3,4)]
# (1+t)-2t^2=(1-t)(1+2t), coefficient identity for exact V.
assert add(const(1,1),scale(mul(const(0,1),const(0,1)),-2))==mul(const(1,-1),const(1,2))
# Expand abstract product statistics in basis H, j_mu*j_nu.
product_coefficients={'I':[-1,0],'J':[0,0],'B':[0,4],'J_squared':[0,2]}
assert [3*product_coefficients['I'][i]-2*product_coefficients['J'][i]+Q(4,5)*product_coefficients['B'][i] for i in range(2)]==[-3,Q(16,5)]
assert Q(4,5)*4-Q(8,5)*2==0
out={'status':'specified exact algebra checks passed; capacity necessity unresolved','series':{k:[str(x) for x in v] for k,v in {'I':i,'J':j,'B':b,'V=B-2J^2':V}.items()},'product_defect_coefficients':product_coefficients,'checks':['single-channel Taylor coefficients','log-variance factorization','source mixed coefficient 16/5','quadratic correction cancellation'],'scan':False,'simulation':False,'infinite_proof':'candidate.md, not inferred from these checks'}
p=Path(__file__).resolve().parent
(p/'checks.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
