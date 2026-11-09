import pathlib,json,math
from fractions import Fraction
P=pathlib.Path(__file__).resolve().parent
out=[]
for n in range(1,5):
 m=1<<n
 for ell in range(n+1):
  neighbors=[sum(1<<b for b in range(m) if (a&b).bit_count()==ell) for a in range(m)]
  best=0;witness=None
  common=[(1<<m)-1]*(1<<m)
  for a in range(1,1<<m):
   low=a&-a;common[a]=common[a^low]&neighbors[low.bit_length()-1]
   value=a.bit_count()*common[a].bit_count()
   if value>best:best=value;witness=[a,common[a]]
  bound=Fraction(math.comb(2*ell,ell))*Fraction(2)**(n-2*ell)
  out.append({'n':n,'ell':ell,'maximum':best,'bound':str(bound),'holds':best<=bound,'maximizing_family_masks':witness,'families_A_examined':(1<<m)-1})
assert all(e['holds'] for e in out)
(P/'bounded-checks.json').write_text(json.dumps({'executed':True,'scope':'All pairs of Boolean set families for 1<=n<=4, 0<=ell<=n; optimize B as common neighbors for each nonempty A; exact intersection size ell. No all-n proof, no credit.','results':out},indent=2)+'\n')
print('exact checks',len(out),'PASS')
