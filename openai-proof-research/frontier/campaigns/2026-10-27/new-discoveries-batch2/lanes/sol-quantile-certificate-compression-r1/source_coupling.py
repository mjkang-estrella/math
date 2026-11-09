from fractions import Fraction as F
from pathlib import Path
import json
import numpy as np
from scipy.optimize import linear_sum_assignment
L=Path(__file__).parent
exec((L/'try_continuous.py').read_text().split('rows=[]')[0])
ss=[[F(x,10) for x in row] for row in [[10,13,22,28,29],[5,9,9,16,18]]]
def q(k,u):
 j=min(int(5*u),4);return sum(ss[k][:j],F(0))/5+ss[k][j]*(u-F(j,5))
def integrate_piece(a,b,offset):
 pts={a,b}
 for k in range(1,5):
  for x in [F(k,5),F(k,5)-offset]:
   if a<x<b:pts.add(x)
 base=sorted(pts)
 for l,r in zip(base,base[1:]):
  yl=q(0,l)+q(1,l+offset);yr=q(0,r)+q(1,r+offset)
  for t in hx[1:-1]:
   if yl<t<yr:pts.add(l+(r-l)*(t-yl)/(yr-yl))
 pts=sorted(pts)
 return sum(((r-l)*(h(q(0,l)+q(1,l+offset))+h(q(0,r)+q(1,r+offset)))/2 for l,r in zip(pts,pts[1:])),F(0))
# One prescribed coarse grid, exact integral costs, rather than midpoint optimization.
N=20
cost=[[integrate_piece(F(i,N),F(i+1,N),F(j-i,N)) for j in range(N)] for i in range(N)]
_,p=linear_sum_assignment(np.array([[float(x) for x in row] for row in cost]),maximize=True)
A=sum((cost[i][j] for i,j in enumerate(p)),F(0))
ubreaks={F(i,5) for i in range(6)}
for t in knots[1:-1]:
 for i in range(5):
  l=F(i,5);r=F(i+1,5);yl=(q(0,l)+q(1,l))/2;yr=(q(0,r)+q(1,r))/2
  if yl<t<yr:ubreaks.add(l+(r-l)*(t-yl)/(yr-yl))
ubreaks=sorted(ubreaks)
B=sum(((r-l)*(d((q(0,l)+q(1,l))/2)+d((q(0,r)+q(1,r))/2)) for l,r in zip(ubreaks,ubreaks[1:])),F(0))
out={'N':N,'permutation':p.tolist(),'source_integral':str(A),'target_upper':str(B),'gap':str(A-B),'per_interval_integrals':[str(cost[i][j]) for i,j in enumerate(p)],'target_u_breakpoints':list(map(str,ubreaks))}
print(out);(L/'coupling20.json').write_text(json.dumps(out,indent=2)+'\n')
