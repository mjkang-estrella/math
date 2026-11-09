from pathlib import Path
from math import comb,isqrt,gcd
from collections import Counter
import json,itertools
D=Path(__file__).resolve().parents[1];out={}
# Source (1.1); integer arithmetic, all valid windows n=1..100-2r, r=1..8.
a=[sum(2*comb(n+1,k-1)*comb(n+1,k)*comb(n+1,k+1) for k in range(1,n+1))//(n*(n+1)**2) for n in range(1,101)]
rows=[]
for r in range(1,9):
 a=[a[i]*a[i+2]-a[i+1]**2 for i in range(len(a)-2)];rows.append({'iteration':r,'start_indices':[1,len(a)],'negative_indices':[i+1 for i,x in enumerate(a) if x<0],'minimum':str(min(a))})
out['368344']={'definition':'L(a)_i=a_i*a_(i+2)-a_(i+1)^2; Baxter source (1.1)','coverage':rows}
# Q recursion source (1); completed values certified diagnostically by both monotone slow branches leaving each level.
N=2**20;q=[0,1,1]
for n in range(3,N+1):
 x,y=n-q[-1],n-q[-2];assert 0<x<n and 0<y<n;q.append(q[x]+q[y]+(-1 if n%2 else 1))
f=Counter((x+1)//2 for x in q[1:]);limit=min((q[-1]+1)//2,(q[-2]+1)//2)-1;rows=[]
for k in range(15):
 if 2**(k+1)-1>limit:break
 c=Counter(f[s] for s in range(2**k,2**(k+1)));rows.append({'k':k,'counts':dict(c),'current_source_match':c==Counter(3+((j&-j).bit_length()-1) for j in range(1,2**k+1)), 'raw_mathdb_match':all(c[r]==2**(k-r+2) for r in range(3,k+2)) and c[k+2]==1 and c[k+3]==1})
out['373645']={'generated_indices':[1,N],'complete_frequency_levels_using_source_slow_branch_lemma':[1,limit],'blocks':rows,'note':'MathDB formula agrees with current theorem for k>=1; k=0 endpoint not discovery credit'}
# Source Q primes, exhaustive x,y primitive representations; search equivalent obstruction bounded primes.
ps=[p for p in range(3,2001,2) if all(p%d for d in range(2,isqrt(p)+1))];qs=[];bad=[]
for p in ps:
 cert=[]
 for j in [1,4,8]:
  for y in range(isqrt(j*p//27)+1):
   z=j*p-27*y*y
   if z%8:continue
   x=isqrt(z//8)
   if 8*x*x==z and gcd(x,y)==1:cert.append([j,x,y])
 if not cert:continue
 qs.append({'p':p,'certificates':cert})
 for y in range(isqrt(11*p*p//27)+1):
  z=11*p*p-27*y*y
  if z%8==0 and isqrt(z//8)**2==z//8:bad.append([p,isqrt(z//8),y])
out['357344']={'primes_range':[3,2000],'Q_primes':qs,'integral_obstruction_solutions':bad,'note':'Checks source final sufficient Diophantine obstruction; not direct partition coefficients or all primes'}
# Ordinary square-free permutations: all permutations lengths 1..8, all insertions for qualifying inputs.
def sf(p):
 for l in range(2,len(p)//2+1):
  for i in range(len(p)-2*l+1):
   a,b=p[i:i+l],p[i+l:i+2*l]
   if all((a[x]<a[y])==(b[x]<b[y]) for x in range(l) for y in range(x)):return False
 return True
rows=[]
for n in range(1,9):
 s=b=e=st=0
 for p in itertools.permutations(range(n)):
  st+=1
  if not sf(p):continue
  s+=1;inserts=[]
  for pos in range(n+1):
   can=False
   for val in range(n+1):
    pp=[v+(v>=val) for v in p];pp.insert(pos,val)
    if sf(pp):can=True;break
   inserts.append(can)
  b+=not inserts[0] and not inserts[-1];e+=not any(inserts)
 rows.append({'n':n,'all_permutations':st,'square_free':s,'bicrucial':b,'extremal':e})
out['351805']=out['351806']={'coverage':rows,'note':'Finite existence census cannot refute unbounded existence'}
(D/'outputs/sequence-search.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
