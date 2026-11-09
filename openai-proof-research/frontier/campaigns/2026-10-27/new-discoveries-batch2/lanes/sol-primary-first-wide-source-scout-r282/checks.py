from fractions import Fraction
from math import gcd
from pathlib import Path
import json
L=Path(__file__).resolve().parent
H=Fraction(0);rows=[];mixed=[]
for n in range(1,201):
 u,v=H.numerator,H.denominator;h=gcd(n,v);r=n//h;s=v//h;g=gcd(r*u+s,h)
 new=H+Fraction(1,n);w=new.denominator
 assert w==h*r*s//g
 assert (n%1==0) and ((w%n!=0)==(g>1))
 assert ((w<v)==(g>r))
 if g>1:rows.append({'n':n,'r':r,'g':g,'v':v,'w':w})
 if r>1 and g>1:mixed.append(n)
 H=new
def mob(n):
 k=0;p=2
 while p*p<=n:
  if n%p==0:
   n//=p;k+=1
   if n%p==0:return 0
  p+=1
 if n>1:k+=1
 return (-1)**k
field=[]
for q in [2,3,4,5,7,8,9,11,13,16,17,19,23,25,27,29,31]:
 M=[0];tot=0
 for n in range(1,43):
  z=sum(mob(d)*q**(n//d) for d in range(1,n+1) if n%d==0)
  assert z%n==0;tot+=z//n;M.append(tot)
 bad=[[],[],[]]
 for n in range(1,41):
  if not M[n+1]**2<M[n]*M[n+2] and not(q<5 and n in [2,4,6,8,10,12]):bad[0].append(n)
  if n>2 and not M[n]**(n+1)<M[n+1]**n and not(q<7 and n in [3,5]):bad[1].append(n)
  if n>3 and not M[n+1]**(2*n*(n+2))>M[n]**((n+1)*(n+2))*M[n+2]**(n*(n+1)) and not((q<8 and n in [5,7,9,11,13])or(9<q<14 and n==4)):bad[2].append(n)
 field.append({'q':q,'outside_exception_failures':bad})
(L/'exact-checks.json').write_text(json.dumps({'arithmetic':'exact integers/Fraction; no floats','harmonic_n_cap':200,'harmonic_cancellations':rows,'mixed_cancellation_indices':mixed,'finitefield_n_cap':40,'finitefield':field,'artificial_nonharmonic_obstruction':{'n':6,'u':1,'v':2,'r':3,'g':2,'w':3}},indent=2))
print('checks passed; finite-field failures',[(r['q'],r['outside_exception_failures'])for r in field if any(r['outside_exception_failures'])])
