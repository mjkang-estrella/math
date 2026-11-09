from pathlib import Path
import numpy as np,math,json,random,time
from fractions import Fraction
L=Path(__file__).resolve().parent;rng=random.Random(287);start=time.monotonic();rows=[];suspects=[]
def mul(a,b):
 c=[0]*(len(a)+len(b)-1)
 for i,x in enumerate(a):
  for j,y in enumerate(b):c[i+j]+=x*y
 return c
for deg in [4,5,6,8,10,12,16,20,24,32]:
 best=0;trials=1500
 for trial in range(trials):
  # All but two roots real; the irreducible quadratic has discriminant <0.
  b=rng.randint(-15,15);c=b*b//4+rng.randint(1,40);a=[c,b,1]
  roots=[rng.choice([-1,1])*rng.randint(1,24) for _ in range(deg-2)]
  for r in roots:a=mul(a,[-r,1])
  # Positive input scaling changes no root counts and improves coefficient scale.
  z=[float(Fraction(v*(k*k+k+1),math.factorial(k))) for k,v in enumerate(a)]
  rr=np.polynomial.polynomial.polyroots(np.array(z)/max(abs(x) for x in z))
  nonreal=int(sum(abs(x.imag)>1e-5*(1+abs(x.real)) for x in rr));best=max(best,nonreal)
  if nonreal>2:
   import sympy as s
   x=s.Symbol('x');P=s.Poly(sum(s.Rational(v*(k*k+k+1),math.factorial(k))*x**k for k,v in enumerate(a)),x)
   real=P.count_roots(-s.oo,s.oo);exact_nonreal=deg-real
   rec=dict(degree=deg,b=b,c=c,real_roots=roots,input_coefficients=a,exact_output_nonreal=exact_nonreal,numeric_output_nonreal=nonreal)
   suspects.append(rec)
   if exact_nonreal>2:
    (L/'witness.json').write_text(json.dumps(rec,indent=2));print('WITNESS',rec);break
  if len(suspects)>15:break
 rows.append(dict(degree=deg,trials=trial+1,max_numeric_nonreal=best))
 if (suspects and suspects[-1]['exact_output_nonreal']>2) or len(suspects)>15:break
(L/'cappedchecks.json').write_text(json.dumps(dict(seed=287,route='real factors times irreducible quadratic; factorial diagonal; numerical screening with exact Sturm confirmation of suspects',rows=rows,suspects=suspects,elapsed=time.monotonic()-start,universal_conclusion=False),indent=2));print(rows)
