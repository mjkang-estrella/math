"""Find extra small-period primes by complete sieve and cyclotomic factoring."""
import sys
sys.dont_write_bytecode=True
import os,json,math,time,collections
HERE=os.path.dirname(os.path.abspath(__file__));sys.path.insert(0,HERE)
from hnt import order,factorint,is_prime,factor_partial,cyclotomic_value
start=time.monotonic()
baseline=json.load(open(os.path.join(HERE,'supply_B.json')))
existing={x[0]:x for x in baseline}
# C is an existing generator search cache, never a trusted proof premise.
cpath=os.path.join(HERE,'..','supply_C.json')
cs=json.load(open(cpath)) if os.path.exists(cpath) else []
for e in cs:existing[e[0]]=e
B=3000000
sv=bytearray(b'\1')*(B+1);sv[0]=sv[1]=0
for p in range(2,math.isqrt(B)+1):
 if sv[p]:sv[p*p::p]=b'\0'*len(sv[p*p::p])
found=[]
for p in range(11,B+1,2):
 if not sv[p] or p in existing:continue
 fac=factorint(p-1);d=order(10,p,fac)
 if d>2000:continue
 o3,o7=order(3,p,fac),order(7,p,fac);index=(p-1)//math.lcm(o3,o7)
 # Keep all short-period primes and coset-useful modest periods.
 if d<=160 or index>=2:
  e=[p,d,o3,o7];existing[p]=e;found.append(e)
print('sieve additions',len(found),time.monotonic()-start,flush=True)
# Factor modest cyclotomic values for missing decimal periods. Each can yield
# primes beyond the direct sieve, capped so the direct trial-division checker is feasible.
for d in [11,13,17,19,22,26,34,38,44,52,68,76,88,104,136,152]:
 fs,rest=factor_partial(cyclotomic_value(d),budget=100000,small=10000)
 for p in sorted(set(fs)):
  if p<=7 or p>10**12 or p in existing:continue
  fac=factorint(p-1)
  dd=order(10,p,fac)
  if dd!=d:continue
  e=[p,d,order(3,p,fac),order(7,p,fac)];existing[p]=e;found.append(e)
 print('period',d,'unfactored_digits',len(str(rest)),'additions',len(found),flush=True)
json.dump(sorted(existing.values()),open(os.path.join(HERE,'supply_extended.json'),'w'),indent=1)
report={'baseline_count':len(baseline),'merged_C_count':len(cs),'new_search_primes':found,'total':len(existing),'elapsed_s':time.monotonic()-start}
json.dump(report,open(os.path.join(HERE,'supply_search.json'),'w'),indent=1)
print('DONE',len(existing),'new',len(found),flush=True)
