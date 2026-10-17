#!/usr/bin/env python3
"""Exact affine-branch/support calculation, not a continuum phase proof. MIT."""
from fractions import Fraction as Q
import json
M=(0,1,4,16); b={0:0,1:0,4:9,16:225}
v={m:(Q(3*m*m,4),Q(m)) for m in M}
def dot(x,y):return sum(a*b for a,b in zip(x,y))
def sub(x,y):return tuple(a-b for a,b in zip(x,y))
def cross(x,y):return x[0]*y[1]-x[1]*y[0]
def val(m,point):return dot(v[m],point)-b[m]
points=[(Q(1),Q(-3,4)),(Q(21,16),Q(-27,16))]
triples=[(0,1,4),(0,4,16)]
weights=[(Q(1,4),Q(1,3),Q(5,12)),(Q(11,16),Q(1,4),Q(1,16))]
centers=[(Q(21,4),Q(2)),(Q(15),Q(2))]
r=Q(1,10);eps=Q(1,1000)
rows=[]
for point,triple,lam,g in zip(points,triples,weights,centers):
 assert sum(lam)==1 and min(lam)>0
 assert tuple(sum(a*v[m][j] for a,m in zip(lam,triple)) for j in range(2))==g
 assert all(val(m,point)==0 for m in triple)
 inactive=next(m for m in M if m not in triple)
 inactive_upper=val(inactive,point)+eps*sum(abs(a) for a in v[inactive])
 assert inactive_upper<0
 distances=[]
 for i in range(3):
  a,c=v[triple[i]],v[triple[(i+1)%3]]
  edge=sub(c,a); d2=cross(edge,sub(g,a))**2/dot(edge,edge)
  assert d2>r*r
  distances.append(str(d2))
 rows.append({'parameter_point':list(map(str,point)),'active':triple,'inactive_value':str(val(inactive,point)),'inactive_rectangle_upper':str(inactive_upper),'support_center':list(map(str,g)),'edge_distance_squares':distances})
# Every free-component exponent is a convex combination of the four
# extreme (slope,intercept) points. The fourth is dominated by (4,-9).
# For k fixed, interpolate between M=k and M=4k, then k=1 and k=4.
for k in range(1,5):
 for m in range(k,4*k+1):
  theta=Q(m-k,3*k)
  coeff=Q(k-1,3)
  reconstructed_slope=(1-theta)*((1-coeff)*1+coeff*4)+theta*((1-coeff)*4+coeff*16)
  reconstructed_intercept=(1-theta)*((1-coeff)*0+coeff*(-9))+theta*((1-coeff)*(-54)+coeff*(-225))
  assert reconstructed_slope==m
  assert reconstructed_intercept==-3*(k-1)-18*(m-k)
print(json.dumps({'passed':True,'normalization':'all pressures/slopes divided by p','parameter_rectangle_radius':str(eps),'support_ball_radius':str(r),'common_density_interval_divided_by_p':['19/10','21/10'],'two_triples':rows,'limits':'Does not verify cluster integrals, thermodynamic limits, iteration, or exact phase transitions.'},indent=2))
