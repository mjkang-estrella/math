from fractions import Fraction as F
from pathlib import Path
import json,itertools,math
D=Path(__file__).resolve().parents[1]
def cyl(k,h):
 out=[(F(k-1,k*(k-1)-1),F(1))]
 for _ in range(h):out=[(F(1,d)+l/(d*(d-1)),F(1,d)+r/(d*(d-1))) for l,r in out for d in range(2,k+1)]
 return out
def merge(xs):
 out=[]
 for l,r in sorted(xs):
  if out and l<=out[-1][1]:out[-1]=(out[-1][0],max(out[-1][1],r))
  else:out.append((l,r))
 return out
luroth=[]
for h in range(1,7):
 a,b=cyl(3,h),cyl(4,h); sums=merge([(l+x,r+y) for l,r in a for x,y in b]); mods=merge([(max(F(0),l-t),min(F(1),r-t)) for l,r in sums for t in [0,1] if l-t<=1 and r-t>=0]);gaps=[(str(r),str(s)) for (_,r),(s,_) in zip(mods,mods[1:]) if r<s];luroth.append(dict(depth=h,pairs=len(a)*len(b),components=len(sums),mod_components=len(mods),gaps=gaps[:10],measure=str(sum(r-l for l,r in mods))))
 print('Luroth',luroth[-1],flush=True)
# Binary-code obstruction to a naive Davenport extraction proof.
# A length r+2 sequence of vectors in F2^r has nullity >=2. Choose independent
# dependencies a,b. wt(a)+wt(b)+wt(a+b)<=2*(r+2).
binary=[dict(rank=r,D=r+1,length=r+2,short=r-1,code_bound=(2*(r+2))//3,bound_suffices=(2*(r+2))//3<=r-1) for r in range(5,17)]
# Source Section5 edge-budget relaxation: continuous clique count upper bound
# using only sum(e_c)=binom(n,2) has asymptotic coefficient larger than conjecture.
relax=[dict(k=k,relax_to_target_ratio=(k/(k-1))**(k/2)*(1-k**(1-k))) for k in [4,5,6,7]]
# local recoloring source method: source alpha=(1-((k-1)/k)^(k/(k-2)))
# missing edge has crude loss coefficient alpha^((k-2)/2)*(k/(k-3))^(k-2).
for o in relax:
 k=o['k'];alpha=1-((k-1)/k)**(k/(k-2));o.update(alpha=alpha,crude_loss=alpha**((k-2)/2)*(k/(k-3))**(k-2))
(D/'outputs/diagnostics.json').write_text(json.dumps(dict(luroth=luroth,binary_code=binary,clique_relaxation=relax),indent=2)+'\n')
print('binary code',binary);print('clique relaxation',relax)
