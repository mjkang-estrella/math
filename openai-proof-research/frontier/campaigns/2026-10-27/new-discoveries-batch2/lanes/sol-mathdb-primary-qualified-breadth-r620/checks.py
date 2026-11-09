from pathlib import Path
import json
P=Path(__file__).parent;out=[]
for n in range(1,5):
 neigh=[sum(1<<(a*n+b) for a in range(n) for b in range(n) if (a,b)!=(i,j) and abs(a-i)<=1 and abs(b-j)<=1) for i in range(n) for j in range(n)]
 best=-1;w=None
 for s in range(1<<(n*n)):
  if s.bit_count()<=best:continue
  if all(not(s>>i&1) or 2*(s&v).bit_count()<=v.bit_count() for i,v in enumerate(neigh)):
   best=s.bit_count();w=s
 out.append({'n':n,'maximum_half_dependent_size':best,'witness_bitmask':w,'all_subsets_examined':1<<(n*n),'five_times_deficit':3*n*n-5*best})
(P/'bounded-checks.json').write_text(json.dumps({'executed':True,'method':'Exhaustive subset enumeration, actual boundary degree; only n<=4, not a limit or uniform deficit proof','kings':out,'scalar_identity':'Exact symbolic: alpha(z)=conj(z), theta(z)=z; theta(z)+conj(theta(alpha(z)))=2z. Norm theta=1. Wording-only exclusion.'},indent=2)+'\n')
print(out)
