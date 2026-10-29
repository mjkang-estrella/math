import math,json,pathlib,time
P=pathlib.Path(__file__).resolve().parent
start=time.monotonic()
def prime(n):
 return next((p for p in range(2,n+1) if n%p==0 and all(p%d for d in range(2,math.isqrt(p)+1))),None)
def conjectured(s):
 p=prime(2*s+1)
 return 2*s*s if p==2*s+1 else 2*s*s+2*s-(p*p-1)//2
def diamond(s):return [(x,y) for x in range(-s,s+1) for y in range(-s+abs(x),s-abs(x)+1)]
rows=[];sample=None;total=0
for s in range(3,19):
 D=diamond(s);bound=conjectured(s);tested=0;passers=[]
 for N in range(bound+1,len(D)+1):
  for a in range(2,N+1):
   if N%a:continue
   d=N//a
   for b in range(a):
    c=math.gcd(a,math.gcd(b,d))
    if c==1:continue
    tested+=1
    # Exact quotient by HNF columns (a,0), (b,d).
    image={((x-b*(y//d))%a,y%d) for x,y in D}
    if len(image)==N:passers.append([a,b,d,N])
 rows.append({'s':s,'bound':bound,'lattices_above_bound_tested':tested,'counterexamples':passers});total+=tested
 # Full F_p^2 fiber counts are necessary for every noncyclic quotient with p|c.
 for p in [3,5,7]:
  counts=[sum(x%p==i and y%p==j for x,y in D) for i in range(p) for j in range(p)]
  cap=p*p*min(counts)
  N=((bound//(p*p))+1)*p*p
  if sample is None and N<=cap and N<=len(D):sample={'s':s,'p':p,'candidate_order':N,'claimed_bound':bound,'prime_fiber_cap':cap}
assert all(not r['counterexamples'] for r in rows)
# Independently compare floor-quotient reduction with bounded membership search.
transport=0
for a in range(2,9):
 for d in range(2,9):
  for b in range(a):
   for x,y in diamond(3):
    q=y//d;u=(x-b*q)%a;v=y%d
    assert (y-v)%d==0 and (x-u-b*((y-v)//d))%a==0
    transport+=1
out={'scope':'bounded diagnostics only, no universal theorem','rows':rows,'tested':total,'transport_checks':transport,'fiber_shortcut_survivor':sample}
(P/'checks.json').write_text(json.dumps(out,indent=2));print(json.dumps(out,indent=2))
