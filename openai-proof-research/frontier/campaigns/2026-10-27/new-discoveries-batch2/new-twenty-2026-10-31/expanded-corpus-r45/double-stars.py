from diagnostics import *
from math import comb
count=0;maxgap=0
for r in range(1,81):
 for s in range(1,81):
  # Both hubs; exactly one hub; neither hub. Leaves in the opposite side are forced.
  p=add([0,0]+[comb(r+s,j) for j in range(r+s+1)],add([0]*(r+1)+[comb(s,j) for j in range(s+1)],add([0]*(s+1)+[comb(r,j) for j in range(r+1)],[0]*(r+s)+[1])))
  def formula(r,s):
   return add([0,0]+[comb(r+s,j) for j in range(r+s+1)],add([0]*(r+1)+[comb(s,j) for j in range(s+1)],add([0]*(s+1)+[comb(r,j) for j in range(r+1)],[0]*(r+s)+[1])))
  # boundary r=0 remains valid only if s>0: the no-hub case fails because the leafless hub is undominated.
  if r==1:q=add([0,0]+[comb(s,j) for j in range(s+1)],add([0]+[comb(s,j) for j in range(s+1)],[0]*(s+1)+[1]))
  else:q=formula(r-1,s)
  if r<=4 and s<=4:
   E=[(0,1)]+[(0,i+2) for i in range(r)]+[(1,i+r+2) for i in range(s)]
   assert p==poly(E,r+s+2)
   assert q==poly(E,r+s+2,2)
  if unimodal(p) and unimodal(q):
   count+=1;gap=abs(mode(p)-mode(q));maxgap=max(maxgap,gap)
   if gap>1:print(json.dumps({'r':r,'s':s,'p':p,'q':q}));raise SystemExit
print(json.dumps({'parameter_grid':'1<=r,s<=80','unimodal_pairs':count,'max_gap':maxgap,'diagnostic':True}))
