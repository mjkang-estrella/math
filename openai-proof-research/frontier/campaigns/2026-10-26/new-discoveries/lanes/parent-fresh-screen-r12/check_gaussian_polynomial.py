"""Exact finite-field product checks of the uncredited elementary corollary."""
import math,json
from pathlib import Path
out=[]
for p in [3,5,7,11,13,17,19,23,29,31]:
 coeff=[(1,0)]
 for a in range(1,p):
  for b in range(1,p):
   if (a*a+b*b)%p==0:continue
   nxt=[(0,0)]*(len(coeff)+1)
   for k,(r,s) in enumerate(coeff):
    x,y=nxt[k];nxt[k]=((x-a*r+b*s)%p,(y-a*s-b*r)%p)
    x,y=nxt[k+1];nxt[k+1]=((x+r)%p,(y+s)%p)
   coeff=nxt
 assert all(y==0 for x,y in coeff)
 if p%4==3:
  pred=[0]*((p-1)**2+1)
  for j in range((p-1)//2+1):pred[2*j*(p-1)]=1
 else:
  pred=[0]*((p-1)*(p-3)+1)
  for j in range(p-2):pred[j*(p-1)]=math.comb(j+2,2)%p
 assert [x for x,y in coeff]==pred
 out.append({'prime':p,'degree':len(coeff)-1,'PASS':True})
res={'status':'PASS','cases':out,'credit':0,'scope':'Finite checks of direct classical finite-field product corollary, not a novelty claim.'}
Path(__file__).with_name('gaussian-polynomial-check.json').write_text(json.dumps(res,indent=2)+'\n');print(json.dumps(res))
