"""Independent finite coefficient checks; no author code/data imports.
Counts the original four geometric-sum indices, then complement-pair residues.
"""
from collections import Counter
from itertools import product
from math import gcd
from pathlib import Path
import json,hashlib
checked=[]
for m in range(2,16):
 for n in range(1,m):
  if gcd(m,n)>1:continue
  k=m-n;original=Counter();paired=Counter()
  for p1,p2,q1,q2 in product(range(m),repeat=4):
   if (q1+q2-n*(p1+p2)-(n-1))%m:continue
   num=k*(p1+p2)+q1+q2-n+1
   assert num%m==0 and 0<=num//m<=2*k
   original[num//m]+=1
   pprime,qprime=m-1-p2,m-1-q2
   r1=(q1-n*p1)%m;r2=(qprime-n*pprime)%m
   assert r1==r2
   e1=p1-(n*p1+r1)//m;e2=pprime-(n*pprime+r1)//m
   assert q1==n*p1+r1-m*((n*p1+r1)//m)
   assert qprime==n*pprime+r1-m*((n*pprime+r1)//m)
   assert num//m==k+e1-e2
   paired[k+e1-e2]+=1
  assert original==paired
  residues=[[p-(n*p+r)//m for p in range(m)] for r in range(m)]
  sos=Counter(k+a-b for exps in residues for a in exps for b in exps)
  assert original==sos
  A0,A1=Counter(residues[0]),Counter(residues[1])
  pstar=next(p for p in range(1,m) if n*p%m==m-1)
  qstar=n*pstar//m;d=pstar-qstar-1
  diff=Counter({e:A1[e]-A0[e] for e in range(k+1)})
  assert all(diff[e]==(int(e==d)-int(e==d+1)) for e in range(k+1))
  assert original[0]>0 and original[2*k]>0
  assert all(original[e]==original[2*k-e] for e in range(2*k+1))
  checked.append([m,n])
out={'status':'PASS','pairs':checked,'pair_count':len(checked),'m_max':15,'method':'original four geometric indices counted as integers; explicit complement-pair bijection; no author polynomial code imported','checks':['source filtered exponent equals complement-pair exponent','same-residue grouping exactly equals finiteSOS','A1 minus A0 exact monomial*(1-z)','positive constant and leading coefficients, reciprocity']}
p=Path(__file__).resolve().parent/'independent-bijection-check.json';p.write_text(json.dumps(out,indent=2)+'\n');print(len(checked),hashlib.sha256(p.read_bytes()).hexdigest())
