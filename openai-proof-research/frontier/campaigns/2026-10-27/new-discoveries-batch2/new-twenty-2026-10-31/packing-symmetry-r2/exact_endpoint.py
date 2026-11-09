"""Exact exhaustive endpoint calculation. NOT a Lean/geometric certificate."""
import json,hashlib
from pathlib import Path
from fractions import Fraction
p=Path(__file__).resolve().parent
D=10**10
X=[0,3574916299,4902203394,6699528833,7172681767,8786594106,D]
Y=[0,3574916299,4984072088,6490568711,7292468328,8682676509,D]
pts=[(0,0),(1,4),(2,2),(3,5),(4,1),(5,3)]
opts=[]
for i,j in pts:
 opts.append([(i,j,r,t) for r in range(i+1,7) for t in range(j+1,7) if not any(i<a<r and j<b<t for a,b in pts)]+[(i,j,i,j)])
def compatible(r,s):
 return r[0]==r[2] or s[0]==s[2] or r[2]<=s[0] or s[2]<=r[0] or r[3]<=s[1] or s[3]<=r[1]
best=-1; witness=None; counts=[0]*7; hist={};positive_best=-1
# Keep zero rectangles; integer arithmetic, all compatible selections, no pruning.
def go(k,rs,area):
 global best,witness,positive_best
 counts[k]+=1
 if k==6:
  z=sum(a==c for a,b,c,d in rs); hist[z]=hist.get(z,0)+1
  if area>best: best=area; witness=rs
  if z==0: positive_best=max(positive_best,area)
  return
 for r in opts[k]:
  if all(compatible(r,s) for s in rs):
   i,j,a,b=r;go(k+1,rs+[r],area+(X[a]-X[i])*(Y[b]-Y[j]))
go(0,[],0)
f=Fraction(best,D*D);gap=Fraction(6471,10000)-f
out=dict(denominator=D,x=X,y=Y,permutation=[4,2,5,1,3],option_counts=list(map(len,opts)),dfs_counts=counts,zero_histogram=hist,maximum_numerator=best,maximum_denominator=D*D,reduced_maximum=str(f),decimal_diagnostic=float(f),separator='6471/10000',strict_gap=str(gap),strict_gap_positive=gap>0,maximizing_selection=witness,positive_only_maximum_numerator=positive_best,kernel_checked=False,scope='endpoint enumeration only; geometric completeness argued in SUMMARY, not formalized')
(p/'exact-endpoint.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
