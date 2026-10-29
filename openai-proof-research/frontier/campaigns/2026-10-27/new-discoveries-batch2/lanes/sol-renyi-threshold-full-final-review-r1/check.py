from pathlib import Path
from fractions import Fraction as F
import math,json,hashlib,re
O=Path(__file__).resolve().parent
# Independent exact overlap computation by endpoint cell subdivision.
k=0
for ai in range(1,18):
 a=F(ai,7)
 for si in range(-4,40):
  s=F(si,7);ends=sorted(set([F(0),a,s-a,s]));length=F(0)
  for l,r in zip(ends,ends[1:]):
   t=(l+r)/2
   if 0<=t<=a and 0<=s-t<=a:length+=r-l
  expected=s if 0<=s<=a else 2*a-s if a<=s<=2*a else F(0)
  assert length==expected;k+=1
# Exact universal cofinal certificate, using exp(t)>=t^4/24.
worst=F(1,24)+F(1,18432**2)
assert worst<F(1,6)
# Independent stable diagnostic: integrate derivative representation of bracket.
# B=integral_(a-u)^(a+u) p*t^(p-1)dt when u<a.
def simpson(f,l,r,n):
 h=(r-l)/n
 return h/3*sum((1 if i in (0,n) else 4 if i%2 else 2)*f(l+i*h) for i in range(n+1))
rows=[]
for p,a in [(0.2,1000),(0.5,100),(0.8,100000),(0.9,1e10)]:
 def bracket(u):
  if u==0:return 0.
  return simpson(lambda t:p*t**(p-1),a-u,a+u,8)
 # scaled variable v=p*u, exponential tail cut at v=40; diagnostic only
 K=simpson(lambda v: math.exp(-v)*bracket(v/p)/p,0,40,2000)
 J=math.gamma(p+1)/p**(p+1)
 assert 0<K<J
 rows.append(dict(p=p,a=a,K=K,J=J,K_over_J=K/J))
r=json.loads((O/'rebuild/replay/replay-receipt.json').read_text());ds=r['declarations'];assert len(ds)==104
seen=set();aud=[]
for d in ds:
 assert d['name'] not in seen;seen.add(d['name'])
 assert d['actual_type'] and set(d['axioms'])<={'propext','Classical.choice','Quot.sound'}
 assert not any(d[x] for x in ['unsafe','partial','axiom'])
 aud.append(dict(name=d['name'],origin=d['origin'],actual_type_sha256=hashlib.sha256(d['actual_type'].encode()).hexdigest(),type_chars=len(d['actual_type']),axioms=d['axioms'],safety='PASS'))
(O/'row-audit.json').write_text(json.dumps(aud,indent=2))
(O/'checker-evidence.json').write_text(json.dumps(dict(exact_overlap_checks=k,cofinal_universal_bound=str(worst),numerics=rows,numerical_scope='Derivative quadrature over v in [0,40], unvalidated floating diagnostics only; no rigorous error bound and no proof role.',all_actual_rows_checked=len(ds)),indent=2))
print('exact overlap',k,'cofinal',worst,'audits',len(ds));print(rows)
