"""Exact method-obstruction checks. No source theorem is certified."""
from fractions import Fraction as F
from pathlib import Path
import json,hashlib
L=Path(__file__).resolve().parent
# Source Conj.1: square-moment bound alone does not imply cube-moment bound.
y=[F(6,5),F(6,5),F(1,10)]
assert sum(v*v for v in y)<3<sum(v**3 for v in y)
# Conj.3, A=(1,1),B=(0,0),C=(1,0): a=b=1,c=sqrt(2).
# Classical side-linear relaxation: r=(0,0,1/sqrt(2)),
# R=(1/sqrt(2),1/sqrt(2),0) satisfies all three inequalities
# a*R1>=b*r3+c*r2, and cyclically, but has ratio exactly 2.
# Required K=2*(sqrt(5)+sqrt(2))/sqrt(13)>2,
# since 10>9 implies sqrt(10)>3.
assert 10>9
# Positive strict relaxation, r3=1, r1=r2=epsilon=1/1000:
# R1=R2=1+sqrt(2)*epsilon, R3=sqrt(2)*epsilon.
# Ratio=(2+3sqrt(2)*epsilon)/(1+2epsilon)<201/100<K.
# Use sqrt(2)<3/2 to bound first numerator by 2+9epsilon/2.
e=F(1,1000)
assert (2+F(9,2)*e)/(1+2*e)<F(201,100)
# K^2=(28+8sqrt(10))/13 > (28+8*(31/10))/13 > (201/100)^2.
assert F(31,10)**2<10
assert (28+8*F(31,10))/13>F(201,100)**2
# Exact reciprocal cubic identity with arbitrary rational median stand-ins.
count=0
for m in [(F(a),F(b),F(c)) for a in range(1,8) for b in range(1,8) for c in range(1,8)]:
 p=sum(m);q=m[0]*m[1]+m[1]*m[2]+m[2]*m[0];t=m[0]*m[1]*m[2]
 D=p*q-t;A=p*p+q
 assert sum(1/(p-v)**3 for v in m)==(A**3-6*p*A*D+3*D*D)/D**3
 count+=1
out=dict(status='PASS',source_resolution=False,square_to_cube_countermodel=[str(v) for v in y],square_sum=str(sum(v*v for v in y)),cube_sum=str(sum(v**3 for v in y)),positive_linear_EM_relaxation_countermodel=True,reciprocal_identity_controls=count,limits='Exact rational algebra/method falsifiers only. No finite diagnostic elevated to universal geometry.')
(L/'checks.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
