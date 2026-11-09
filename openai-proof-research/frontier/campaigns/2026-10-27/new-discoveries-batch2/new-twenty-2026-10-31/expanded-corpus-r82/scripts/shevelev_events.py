from fetch import D
import math,json,sympy as s
LIMIT=10**12
# At processed n, c(n)=n+d. Until the next increment>1, d remains fixed.
# For even k gcd(k,c(k-1))=gcd(k,d-1); for odd k gcd(k-2,c(k-1))=gcd(k-2,d+1).
n=2;c=4;fund=[2];last=2;rows=[];events=0
while n<LIMIT:
 d=c-n;poss=[]
 for parity,z,shift in [(0,d-1,0),(1,d+1,2)]:
  if z==0:
   k=n+1
   while k%2!=parity or abs(k-shift)<=1:k+=1
   poss.append(k);continue
  for p in s.factorint(abs(z)):
   if parity==1 and p==2:continue
   k=((n-shift)//p+1)*p+shift
   if k%2!=parity:k+=p
   if k%2==parity:poss.append(k)
 k=min(poss) if poss else LIMIT+1;end=min(k-1,LIMIT)
 # Fundamental indices inside the run c(j)=j+d occur only at j=d.
 if n<d<=end:
  i=len(fund)+1;prev=fund[-1]
  rows.append(dict(i=i,m=d,previous_m=prev,rho=last,denominator=prev+3,fails=i>=6 and 4*last>5*(prev+3)))
  fund.append(d)
 if k>LIMIT:break
 c=c+(k-n-1);inc=math.gcd(k if k%2==0 else k-2,c);assert inc>1;c+=inc;n=k;before=last;last=k;events+=1
 if c==2*n and n>fund[-1]:
  i=len(fund)+1;prev=fund[-1];rows.append(dict(i=i,m=n,previous_m=prev,rho=before,denominator=prev+3,fails=i>=6 and 4*before>5*(prev+3)));fund.append(n)
ref=json.loads((D/'outputs/shevelev.json').read_text())['rows']
assert [(r['m'],r['rho']) for r in rows if r['m']<=10**7]==[(r['m'],r['rho']) for r in ref]
o={'space':'all recurrence indices 1..10^12 by exact event skipping; only completed fundamental intervals','events':events,'rows':rows,'direct_comparison_through':10**7,'violations':[r for r in rows if r['fails']]}
(D/'outputs/shevelev-events.json').write_text(json.dumps(o,indent=2));print(json.dumps(o,indent=2))
