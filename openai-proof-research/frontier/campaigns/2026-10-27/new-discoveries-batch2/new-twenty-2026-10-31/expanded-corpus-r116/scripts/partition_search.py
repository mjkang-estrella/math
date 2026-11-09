from collections import Counter
from itertools import combinations_with_replacement
from math import comb,prod
import json,sys
from pathlib import Path
D=Path(__file__).resolve().parents[1]
def parts(n,lo=1,odd=False,distinct=False):
 if not n:yield ();return
 for x in range(lo,n+1):
  if odd and x%2==0:continue
  for p in parts(n-x,x+int(distinct),odd,distinct):yield (x,)+p
def shortparts(n,k,lo=1):
 if n==0:yield ();return
 if k==0:return
 for x in range(lo,n+1):
  for q in shortparts(n-x,k-1,x):yield (x,)+q
def image(p,j):
 c=Counter(p);K=sorted(c);o=Counter()
 for q in combinations_with_replacement(K,j):
  a=prod(comb(c[x],v) if v<=c[x] else 0 for x,v in Counter(q).items())
  if a:o[prod(q)]+=a
 return tuple(sorted(o.items()))
out=[]
for n in range(int(sys.argv[1]),int(sys.argv[2])+1):
 row={'n':n}
 for j in [2,3]:
  O={image(p,j) for p in parts(n,odd=True) if len(p)>=j}
  # length <=j maps to empty or a singleton; include all regardless of input parts
  Dd=set()
  for p in parts(n,distinct=True):
   if len(p)<=j:continue
   im=image(p,j)
   if all(c==1 for x,c in im):Dd.add(im)
  for p in shortparts(n,j):
   if len(p)>j:continue
   im=image(p,j);Dd.add(im)
   if all(x%2 for x,c in im):O.add(im)
  row[str(j)]={'odd':len(O),'distinct':len(Dd),'difference':len(O)-len(Dd)}
 print(row,flush=True);out.append(row)
 (D/f'outputs/partition-{sys.argv[1]}-{sys.argv[2]}.json').write_text(json.dumps(out,indent=2)+'\n')
