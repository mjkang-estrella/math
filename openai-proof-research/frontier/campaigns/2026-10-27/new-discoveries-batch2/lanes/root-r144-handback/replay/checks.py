"""Exact bounded controls, not a quasipolynomial proof. Stdlib only."""
from pathlib import Path
from math import gcd,prod
import json,datetime
L=Path(__file__).resolve().parent
def props(gaps):
 c=max(gaps,default=-1)+1
 m=next(n for n in range(1,c+2) if n not in gaps)
 left=[n for n in range(1,c) if n not in gaps]
 return c,m,gcd(*left) if left else 0
def apery(gaps,m):
 return [next(n for n in range(i,2*max(gaps,default=0)+2*m,m) if n not in gaps) for i in range(1,m)]
records=[];tested=trunc=0
for m in [2,3,4,5,6,7,8,9,10,12]:
 layer={frozenset(range(1,m))};counts=[];cap=None;local=0
 primes=[p for p in range(2,m+1) if m%p==0 and all(p%q for q in range(2,p))]
 divisors=[d for d in range(2,m+1) if m%d==0 and all(d%(p*p) for p in primes)]
 for g in range(m-1,41):
  counts.append([g,len(layer)])
  nxt=set()
  for gaps in sorted(layer,key=lambda s:tuple(sorted(s))):
   c,mm,dd=props(gaps);assert mm==m and len(gaps)==g
   assert dd!=1
   w=apery(gaps,m);assert sum((v-i)//m for i,v in enumerate(w,1))==g
   assert max(w)-m+1==c
   # Direct gcd and Apéry top-band formulations agree, including ordinary c=m.
   direct=any(dd%p==0 for p in primes)
   band=any(all(v>=c for i,v in enumerate(w,1) if i%p) for p in primes)
   assert direct==band
   # Inclusion-exclusion over distinct primes, including gcd(empty)=0.
   ie=0
   for d in divisors:
    k=sum(d%p==0 for p in primes)
    valid=all(v>=c for i,v in enumerate(w,1) if i%d)
    ie+=(-1)**(k+1)*valid
   assert ie==1
   tested+=1
   if local<500 and c>m:
    for d in divisors:
     if not all(n%d==0 for n in range(1,c) if n not in gaps):continue
     n=(c+d-1)//d
     tg={t for t in range(n) if d*t in gaps}
     h=len(tg)
     assert g==c-n+h
     assert next(t for t in range(1,n+2) if t not in tg)==m//d
     assert all(a+b not in tg for a in range(n) if a not in tg for b in range(n-a) if b not in tg)
     rebuilt={v for v in range(c) if v%d or v//d in tg}
     assert rebuilt==set(gaps)
     trunc+=1
    local+=1
   if g==40:continue
   for x in [c,c+1]:
    if x==m or x in gaps:continue
    if any(a not in gaps and x-a not in gaps for a in range(1,x)):continue
    child=gaps|{x};cc,mc,dc=props(child)
    if mc==m and dc!=1:nxt.add(child)
   if len(nxt)>50000:
    cap={'at_genus':g+1,'reason':'50000 next-layer state cap','incomplete_layer_discarded':True};break
  if cap:break
  layer=nxt
  if tested>300000:
   cap={'reason':'300000 total-state cap checked between complete layers'};break
 records.append(dict(m=m,counts=counts,cap=cap))
 # Known source controls.
 if m in [2,3,5,7]:assert all(n==1 for g,n in counts)
 if m==4:assert all(n==(g+1)//3 for g,n in counts)
 if m==6:assert all(n==(2*g*g+g-16)//9-((g-1)**2)//5 for g,n in counts)
def kunz(x):
 m=len(x)+1
 return all(v>=1 for v in x) and all(x[i-1]+x[j-1]+(i+j>=m)>=x[(i+j)%m-1] for i in range(1,m) for j in range(i,m) if (i+j)%m)
def comps(total,n):
 if n==1:
  if total>=1:yield (total,)
 else:
  for a in range(1,total-n+2):
   for tail in comps(total-a,n-1):yield (a,)+tail
independent=[];compositions=0
for m in range(2,9):
 rec=next(r for r in records if r['m']==m)
 for g in range(m-1,15):
  count=0
  for x in comps(g,m-1):
   compositions+=1
   if not kunz(x):continue
   w=[m*t+i for i,t in enumerate(x,1)];c=max(w)-m+1
   dd=0
   for n in range(1,c):
    if n%m==0 or n>=w[n%m-1]:dd=gcd(dd,n)
   if dd!=1:count+=1
  assert count==dict(rec['counts'])[g]
  independent.append([m,g,count])
x=(6,2,6,4,6,6,6);shift=tuple(t-1 for t in x)
assert kunz(x) and not kunz(shift)
w=[8*t+i for i,t in enumerate(x,1)];c=max(w)-8+1
assert c==48 and sum(x)==36 and all(v>=c for i,v in enumerate(w,1) if i%2)
out=dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),tested_states=tested,truncation_checks=trunc,records=records,independent_compositions=compositions,independent_counts=independent,shift_obstruction=dict(m=8,x=x,genus=36,conductor=48,subtracted=shift,failed_inequality='2*x_2=2 < x_4=3'),limits='m fixed list, genus <=40, next-layer50000, total-state300000 between layers; independent all positive compositions m2..8,g<=14; finite controls only',proof=False)
(L/'checks.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:v for k,v in out.items() if k!='records'}))
