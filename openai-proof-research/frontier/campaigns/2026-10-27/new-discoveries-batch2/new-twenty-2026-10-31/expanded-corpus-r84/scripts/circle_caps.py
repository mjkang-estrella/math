from fractions import Fraction as Q
from itertools import combinations_with_replacement
from pathlib import Path
import json
rows=[]
for rad in range(1,9):
 best=0;tested=0
 for centers in combinations_with_replacement(range(8),3):
  tested+=1;arcs=[]
  for c in centers:
   lo=Q(c-rad,4);hi=Q(c+rad,4)
   for shift in [-2,0,2]:
    a=max(Q(0),lo+shift);b=min(Q(2),hi+shift)
    if a<b:arcs.append((a,b))
  arcs.sort();total=0;end=Q(0)
  for a,b in arcs:
   total+=max(Q(0),b-max(end,a));end=max(end,b)
  best=max(best,total);assert total<=min(Q(2),Q(6*rad,4))
 rows.append({'radius_over_pi':str(Q(rad,4)),'configurations':tested,'maximum_over_pi':str(best),'simplex_union_over_pi':str(min(Q(2),Q(6*rad,4)))})
Path(__file__).resolve().parents[1].joinpath('outputs/circle-caps.json').write_text(json.dumps({'scope':'S1, three centers at angles c*pi/4 c=0..7 with repetitions allowed; cap geodesic radii rad*pi/4 rad=1..8; exact rational arc lengths','cases':rows,'limitation':'Only known dimension n=2; no higher-dimensional spherical area search.'},indent=2)+'\n')
