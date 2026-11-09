from pathlib import Path
import json,itertools,hashlib
D=Path(__file__).parent;I=D.parent/'root-mathdb-breadth-intake-r583'
j=lambda p:json.loads(p.read_text())
c=j(I/'coverage-delta.json');rs=j(I/'active-breadth-reservations.json'); own=j(I/'reserved-ids.json');sets=[set(x['ids']) for x in rs];assert len(c)==5533; assert len(sets)==3
for s in sets:assert len(s)==50 and not s.intersection(map(int,c)) and not s.intersection(own['protected_ids'])
for x,y in itertools.combinations(sets,2):assert not x&y
assert set(own['ids']) in sets; assert set(own['other_active_reservations'])==set.union(*[s for s in sets if s!=set(own['ids'])])
assert {344924,386396,387650}<=set(map(int,c))
A=[[1,0],[0,1]]; even=A[0][0]+A[1][1];odd=A[0][1]+A[1][0]
# Exact rational polynomial multiplication, no approximate algebra.
from fractions import Fraction as F
def mul(a,b):
 r=[F(0)]*(len(a)+len(b)-1)
 for i,x in enumerate(a):
  for k,y in enumerate(b):r[i+k]+=x*y
 return r
P=[F(1),F(0),F(1)];Q=[F(0),F(3,2),F(0),F(1)];p3=mul(mul(P,P),P);q2=mul(Q,Q);diff=[x-y for x,y in zip(p3,q2)]
(D/'bounded-checks.json').write_text(json.dumps({'reservation_integrity':'PASS','covered_record_baseline':5533,'active_sets':[{'lane':x['lane'],'count':len(x['ids'])} for x in rs],'parity_example':{'matrix':A,'even_max':even,'odd_max':odd,'meaning':'executed decision instance only; not a refutation of a decision problem'},'polynomial_instance':{'P':'x^2+1','Q':'x^3+3x/2','P^3-Q^2':[str(z) for z in diff],'meaning':'executed exact rational instance of reported classical bound, no discovery credit'},'restoration_ids_preserved':[344924,386396,387650]},indent=2)+'\n');print('DISJOINT PASS; examples',even,odd,[str(z) for z in diff])
