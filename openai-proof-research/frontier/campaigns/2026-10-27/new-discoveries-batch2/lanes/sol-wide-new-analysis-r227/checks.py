from fractions import Fraction as F
from math import comb
import pathlib,json
L=pathlib.Path(__file__).resolve().parent
out={'scope':'exact finite evidence only; no universal wavelet classification'}
out['hh']=[]
for n in [2,8,32,128,512]:
 c=F(comb(n,n//2),2**(n+1));I=F(n+2,4*(n+1));r=(I-c)/(1-2*c)
 assert r<=F(1,4)
 out['hh'].append({'n':n,'midpoint':str(c),'integral':str(I),'ratio':str(r)})
def data(x,b):
 # j bounds adequate for x in this finite experiment, asserted below
 vals=[]
 for j in range(-35,36):
  q=F(2)**j;y=abs(x)/q
  if b<y<1:vals.append((j,q,y))
 assert not vals or min(t[0] for t in vals)>-35 and max(t[0] for t in vals)<35
 neighbors=[x-(1 if x>0 else -1)*q for j,q,y in vals if y<1-b]
 anchor=len(vals)-len(neighbors)
 return len(vals),neighbors,anchor
out['wavelet']=[]
for b in [F(13,100),F(1,7),F(1,6)]:
 # generic non-endpoint seed; graph ball, exact residual for sign-alternating trial vector
 V={F(17,53),-F(17,53)};front=set(V)
 for depth in range(7):
  new={y for x in front for y in data(x,b)[1]}-V
  if len(V|new)>3000:break
  V|=new;front=new
  boundary=sum(sum(y not in V for y in data(x,b)[1]) for x in V)
  anchors=sum(data(x,b)[2] for x in V)
  # internal graph edges must be symmetric and connect opposite signs
  for x in V:
   for y in data(x,b)[1]:
    assert x*y<0
    if y in V:assert x in data(y,b)[1]
  out['wavelet'].append({'b':str(b),'depth':depth+1,'vertices':len(V),'anchor_mass':anchors,'boundary_edges':boundary,'formal_graph_Rayleigh':str(F(anchors+boundary,len(V)))})
(L/'checks.json').write_text(json.dumps(out,indent=2));print(json.dumps(out,indent=2))
