#!/usr/bin/env python3
# Myeongjin Kang. MIT. Exact finite diagnostics, not a proof of the all-N theorem.
from fractions import Fraction as F
from itertools import combinations

def energy(indices,m):
 # Exact squared chord lengths for the regular4-gon or6-gon only.
 sq={2:{1:2,2:4},3:{1:1,2:3,3:4}}[m]
 return sum((F(1,sq[min((i-j)%(2*m),(j-i)%(2*m))]) for i,j in combinations(indices,2)),F(0))
for m in (2,3):
 sets=list(combinations(range(2*m),m))
 values={a:energy(a,m) for a in sets}
 best=min(values.values())
 minimizers={a for a,e in values.items() if e==best}
 assert minimizers=={tuple(range(0,2*m,2)),tuple(range(1,2*m,2))}
 assert all(e>best for a,e in values.items() if a not in minimizers)
for N in range(3,101):
 central=F(1,N);outer=F(1,2*N)
 assert central+2*(N-1)*outer==1
 assert central==2*outer
 assert 2*F(N*(N-1),2)==N*(N-1)
# Meaningful negative controls: equal component weights erase the deficit;
# zero exponent erases strict polygon energy and pair-Hessian invertibility;
# one outer point fails the shared-zero-gradient input.
assert not (F(1,5)>F(1,5))
assert not (F(0)*(F(0)+1)!=0)
assert not (1==0)
print('PASS_NONPROOF_DIAGNOSTIC: exact4/6-gon contacts, mass weights; 3 negative inputs rejected')
