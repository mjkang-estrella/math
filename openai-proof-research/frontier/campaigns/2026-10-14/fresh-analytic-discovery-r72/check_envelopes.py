#!/usr/bin/env python3
# Copyright 2026 Myeongjin Kang. MIT.
"""Exact finite illustration; not a proof of the general classification."""
from fractions import Fraction as F
from itertools import combinations,product
import json

def check(M,p,c,a,e):
 d=a*p-e
 # Each triple (beta coefficient, h coefficient, constant).
 planes=[(F(0),F(0),F(0))]+[(p*(a*p*m*m-e*m*(m-1))/2,p*m,-p*c*(m-1)) for m in range(1,M+1)]
 corners=set()
 for i,j,k in combinations(range(M+1),3):
  x,y,z=planes[i],planes[j],planes[k]
  A,B,C=(y[t]-x[t] for t in range(3));D,E,G=(z[t]-x[t] for t in range(3));det=A*E-B*D
  if not det:continue
  beta=(B*G-C*E)/det;h=(C*D-A*G)/det
  if beta<=0:continue
  vals=[v[0]*beta+v[1]*h+v[2] for v in planes]
  if vals[i]==max(vals):corners.add((beta,h))
 expected={(2*c/(M*d),-c*a*p/(M*d))} if d>0 else set()
 assert corners==expected,(M,p,c,a,e,corners,expected)
 return len(corners)

if __name__=='__main__':
 cases=vertices=0
 for M,p,c,a,e in product(range(2,10),[F(1,2),F(1),F(2)],[F(1),F(3)],[F(1,2),F(2)], [F(-1),F(0),F(1,4),F(1),F(4)]):
  vertices+=check(M,p,c,a,e);cases+=1
 print(json.dumps({'status':'PASS_FINITE_ILLUSTRATIONS_ONLY','rational_parameter_cases':cases,'noncollinear_active_triples_located_as_vertices':vertices},indent=2))
