from fractions import Fraction as F
import json,datetime
# Diagnostic truncated square roots only. The report proves existence by recurrence.
def root(N,mod=None):
 s=[F(1)] if mod is None else [1]
 for m in range(1,N+1):
  rhs=(1 if m==1 else 0)-sum(s[i]*s[m-i] for i in range(1,m))
  s.append(rhs/F(2) if mod is None else rhs*pow(2,-1,mod)%mod)
 for m in range(N+1):
  z=sum(s[i]*s[m-i] for i in range(m+1))-(1 if m in [0,1] else 0)
  assert z==0 if mod is None else z%mod==0
 return N+1
count=root(64)
for p in [3,5,7,11,13,17,19]:count+=root(32,p)
norms=0
for p in [3,5,7,11,13,17,19]:
 squares={x*x%p for x in range(p)};d=next(a for a in range(1,p) if a not in squares)
 values={(x*x-d*y*y)%p for x in range(p) for y in range(p)}
 assert values==set(range(p))
 assert [(x,y) for x in range(p) for y in range(p) if (x*x-d*y*y)%p==0]==[(0,0)]
 norms+=1
print(json.dumps(dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),status='PASS',square_series_coefficients=count,finite_norm_forms=norms,limit='Exact diagnostic checks, not a proof of UUD, valuation detection, or any universal source resolution.'),indent=2))
