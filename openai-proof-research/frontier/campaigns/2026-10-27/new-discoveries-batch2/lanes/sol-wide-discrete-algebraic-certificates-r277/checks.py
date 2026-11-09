"""Exact bounded falsifiers/searches; no claim of universal coverage."""
from pathlib import Path
from itertools import product
import json,random
L=Path(__file__).resolve().parent
def lifting(a,p):
 n=len(a);r=len(a[0]);basis={}; sums=[(0,)*r]; equations=0
 for mask in range(1,1<<n):
  j=(mask&-mask).bit_length()-1
  s=tuple(x+y for x,y in zip(sums[mask^(1<<j)],a[j]));sums.append(s)
  if any(x%p for x in s):continue
  equations+=1
  row=[(mask>>i)&1 for i in range(n)]+[(-x//p)%p for x in s]
  for k,b in sorted(basis.items()):
   c=row[k]
   if c:row=[(x-c*y)%p for x,y in zip(row,b)]
  k=next((i for i in range(n) if row[i]),None)
  if k is None:
   if any(row[n:]):return None,equations
  else:
   inv=pow(row[k],-1,p);basis[k]=[(x*inv)%p for x in row]
 b=[[0]*r for _ in a]
 for k,row in sorted(basis.items(),reverse=True):
  b[k]=[(row[n+t]-sum(row[j]*b[j][t] for j in range(k+1,n)))%p for t in range(r)]
 return [tuple(a[i][t]+p*b[i][t] for t in range(r)) for i in range(n)],equations
def wbad(a,n):
 sums={(0,)*len(a[0])}
 for v in a:
  sums|={tuple((x+y)%(n*n) for x,y in zip(s,v)) for s in list(sums)}
 return all(not all(x%n==0 for x in s) or all(x==0 for x in s) for s in sums)
def reduced(a,p):
 def ss(xs):
  s={(0,)*len(a[0])}
  for v in xs:s|={tuple((x+y)%p for x,y in zip(t,v)) for t in list(s)}
  return s
 s=ss(a);return all(ss(a[:i]+a[i+1:])!=s for i in range(len(a)))
out={}
base=[(1,0,0)]*2+[(-1,0,0)]*2+[(0,1,0)]*2+[(0,-1,0)]*2+[(0,0,1)]*2+[(0,0,-1)]*2
assert wbad(base,3)
out['known_lower_witness']={'n':3,'r':3,'length':12,'vectors':base,'wbad':True,'not_new':'source Lemma3.1'}
assert reduced([(1,),(-1,)],3)
out['zero_free_shortcut_falsifier']={'group':'Z/3','sequence':[1,-1],'reduced':True,'contains_zero_sum':True}
assert lifting([(1,)]*4,3)[0] is None
out['same_residue_lift_obstruction']={'p':3,'residues':[[1]]*4,'inconsistent':True}
rng=random.Random(277);vectors=[x for x in product(range(3),repeat=3) if any(x)]
counts={'tested':0,'inconsistent':0,'consistent':0};found=[]
for trial in range(240):
 a=([tuple(x%3 for x in v) for v in base]+[rng.choice(vectors)]) if trial<26 else [rng.choice(vectors) for _ in range(13)]
 if trial<26:a[-1]=vectors[trial]
 lift,eq=lifting(a,3);counts['tested']+=1
 if lift is None:counts['inconsistent']+=1
 else:
  assert wbad(lift,3);counts['consistent']+=1;found.append({'residues':a,'lift':lift})
out['lift_search']={**counts,'seed':277,'scope':'all 26 single additions to fixed signed basis witness, plus 214 random residue lists; NOT exhaustive','witnesses':found}
(L/'exact-checks.json').write_text(json.dumps(out,indent=2));print(json.dumps(out))
