from fetch import D
from fractions import Fraction as F
from itertools import combinations
import json
rows=[]
for n in range(1,6):
 worst=None;example=None;count=0
 for v in combinations(range(1,13),n):
  # Every interior maximum of the lower envelope of triangle waves occurs
  # at a peak of one wave or an intersection of oppositely sloping waves.
  times={F(k,a+b) for a in v for b in v for k in range(a+b+1)}
  def dist(t):return min(min((a*t)%1,1-(a*t)%1) for a in v)
  value=max(map(dist,times));count+=1
  if worst is None or value<worst:worst=value;example=v
  assert value>=F(1,n+1)
 rows.append(dict(n=n,tuples=count,min_of_max=str(worst),example=example))
(D/'outputs/lonely.json').write_text(json.dumps({'space':'all strictly increasing distinct positive speed tuples of lengths 1..5 from 1..12; exact rational envelope extrema in [0,1]','rows':rows,'warning':'finite speed box only; does not establish global kappa or obstruction parameter'},indent=2));print(rows)
