#!/usr/bin/env python3
"""MIT, Myeongjin Kang. Exact diagnostic for the explicit comparison, not T117Q."""
from fractions import Fraction
import json

A = [(2,1,0),(0,1,0),(0,1,1)]
B = [(1,0,1),(1,0,0),(1,2,0)]
points = A+B
weights = [1,1,1,-1,-1,-1]
def dist(x,y): return max(abs(a-b) for a,b in zip(x,y))
D = [[dist(x,y) for y in points] for x in points]
assert sum(weights)==0
assert all(dist(x,y)==1 for x in A for y in B)
q = sum(weights[i]*weights[j]*D[i][j] for i in range(6) for j in range(6))
assert q==2
for k in range(1,101):
    average=Fraction(sum(abs(u-v) for u in range(k+1) for v in range(k+1)),(k+1)**2)
    assert average==Fraction(k*(k+2),3*(k+1)) and average>=Fraction(k,3)
print(json.dumps({'status':'PASS_EXACT_COMPARISON_DIAGNOSTIC','distance_matrix':D,
 'weights':weights,'cnd_quadratic_form':q,'tested_average_formula_k':100,
 'scope':'Explicit six-point certificate and finite formula checks only; universal average formula proved in response.md'},indent=2))
