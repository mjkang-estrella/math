from fractions import Fraction as F
from pathlib import Path
import json
L=Path(__file__).parent
hx=[F(0),F(318,1000),F(795,1000),F(1590,1000),F(1908,1000),F(3021,1000),F(3180,1000)]
hs=[-1,1,-1,1,-1,1];hy=[F(0)]
for a,b,s in zip(hx,hx[1:],hs):hy.append(hy[-1]+s*(b-a))
def h(x):
 for i in range(6):
  if x<=hx[i+1]:return hy[i]+hs[i]*(x-hx[i])
 raise ValueError(x)
knots=list(map(F,['0','477/2000','1113/2000','2703/2000','159/100']))
def d(x):return F(159,1000)-x+2*max(x-knots[1],0)-2*max(x-knots[2],0)+2*max(x-knots[3],0)
rows=[]
for a,b in zip(knots,knots[1:]):
 for c,e in zip(knots,knots[1:]):
  pts={(a,c),(a,e),(b,c),(b,e)}
  for t in hx[1:-1]:
   for x in [a,b]:
    if c<=t-x<=e:pts.add((x,t-x))
   for y in [c,e]:
    if a<=t-y<=b:pts.add((t-y,y))
  rows += [(d(x)+d(y)-h(x+y),x,y) for x,y in pts]
print('min slack',min(rows),'knots',[(str(x),str(d(x))) for x in knots])
(L/'continuous-attempt.json').write_text(json.dumps({'minimum_slack':str(min(rows)[0]),'minimizer':list(map(str,min(rows)[1:])),'vertices':len(rows)},indent=2)+'\n')
