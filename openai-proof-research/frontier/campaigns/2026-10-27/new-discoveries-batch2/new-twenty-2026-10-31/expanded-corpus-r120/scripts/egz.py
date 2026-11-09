import math,itertools,json

def comps(n,q):
 if q==1:yield (n,);return
 for k in range(n+1):
  for r in comps(n-k,q-1):yield (k,)+r

def e(c,q):
 f=[1]+[0]*q
 for a,n in enumerate(c):
  for _ in range(n):
   for j in range(q,0,-1):f[j]=(f[j]+a*f[j-1])%q
 return f[q]
for q,t in [(2,4),(2,5),(2,8),(2,9),(2,12),(2,13),(3,9),(3,10),(3,11),(4,16)]:
 assert math.comb(t,q)%q==0
 n=t+q*q-q;subs=[c for c in comps(t,q) if e(c,q)==0];checked=0
 for c in comps(n,q):
  if not any(all(a<=b for a,b in zip(d,c)) for d in subs):print('COUNTEREXAMPLE',q,t,c);raise SystemExit(2)
  checked+=1
 print(json.dumps(dict(q=q,t=t,length=n,multisets_exhausted=checked,zero_submultisets=len(subs),finding='every multiset contains a zero e_q subsequence of length t')),flush=True)
