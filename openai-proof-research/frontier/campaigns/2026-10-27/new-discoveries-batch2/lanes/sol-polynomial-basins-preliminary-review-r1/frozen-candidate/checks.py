import json,pathlib
L=pathlib.Path(__file__).parent
def prime(n):return n>=2 and all(n%d for d in range(2,int(n**.5)+1))
ps=[p for p in range(2,150) if prime(p)]
traps=[]
for p in ps:
 for x in range(p):
  for y in range(p):
   a,b=x,y
   for t in range(p):a,b=a*a*b%p,(a*a*b+a*b*b)%p
   assert (a,b)==(0,0)
 traps.append(p)
ratios=[]
for k in range(1,13):
 q=next(q for q in ps if q>2 and k%q)
 p=next(p for p in ps if (p-1)%q==0)
 z=next(z for z in range(2,p) if pow(z,q,p)==1)
 for c in [1,p-1]:
  a,b=1,z
  for t in range(2*p):
   assert a!=b and a and b and b*pow(a,-1,p)%p==pow(z,pow(k,t),p)
   a,b=c*pow(a,k,p)%p,c*pow(b,k,p)%p
 ratios.append(dict(k=k,q=q,p=p,z=z))
# C3 altitude-one transfer: four horizontal steps at each level, one vertical.
walks=[]
for k in range(1,21):
 a,b=1,0
 for _ in range(k):a,b=4*a+b,a+4*b
 assert 2*(a-4**k)==3**k-2*4**k+5**k
 walks.append(dict(k=k,count=a-4**k))
(L/'exact-checks.json').write_text(json.dumps(dict(status='PASS',scope='finite diagnostics only; proofs in prose',trap_primes=traps,ratio_examples=ratios,cube_altitude=walks),indent=2))
print('PASS exact diagnostics')
