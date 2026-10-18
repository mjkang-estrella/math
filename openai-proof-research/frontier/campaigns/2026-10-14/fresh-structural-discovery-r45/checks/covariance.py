#!/usr/bin/env python3
"""Exact rational first-moment diagnostic; pre-collision sampling only."""
from fractions import Fraction as Q
import json
n=8;d=3;k=d-2
C=[(i,(i+1)%n)for i in range(n)]
F=[(i,i+4)for i in range(4)]
def orient(E):return E+[(b,a)for a,b in E]
Co=orient(C);Fo=orient(F);G=Co+Fo

def law_ind(E,w=Q(1)):
 return [(g,j,w/Q(len(E)**2))for g in E for j in E]
full=law_ind(G);off=law_ind(Fo)
mix=law_ind(Fo,Q(k,d))
for direction in (C,[(b,a)for a,b in C]):
 for g in direction:
  for a,b in direction:mix.append((g,(b,a),Q(1,d*n*n)))
assert sum(w for _,_,w in mix)==1

def mean(law):
 # Coefficients of s and sigma; test on contrast basis e_i-e_(n-1).
 result=[[[Q(0)for _ in range(n-1)]for _ in range(n-1)]for _ in range(2)]
 def value(i,p):return int(i==p)-int(p==n-1)
 for (u,v),(x,y),prob in law:
  a=[value(i,u)-value(i,x)for i in range(n-1)]
  b=[value(i,v)-value(i,y)for i in range(n-1)]
  for i in range(n-1):
   for j in range(n-1):
    result[0][i][j]-=prob*(a[i]*a[j]+b[i]*b[j])/k
    result[1][i][j]+=prob*d*(a[i]*b[j]+b[i]*a[j])/k
 return result
A=mean(full);B=mean(mix);D=mean(off)
assert A==B and D!=A
witness=next((c,i,j,str(A[c][i][j]),str(D[c][i][j]))for c in range(2)for i in range(n-1)for j in range(n-1)if A[c][i][j]!=D[c][i][j])
print(json.dumps({'status':'PASS','n':n,'d':d,'same_type_equals_full_mean_on_1_perp':True,'off_cycle_mismatch_witness':witness,'scope':'First moments before validity conditioning; not spectral bias, global Hamiltonicity, or the full proposed repair.'},indent=2))
