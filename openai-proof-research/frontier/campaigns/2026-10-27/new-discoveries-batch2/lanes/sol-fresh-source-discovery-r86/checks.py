from fractions import Fraction as Q
import json,pathlib
P=pathlib.Path(__file__).parent; count=0
# Exact independent quotient derivatives via polynomial quotient rule at rational points.
for T in range(1,17):
 for q in [Q(0),Q(1,3),Q(4,5)]:
  c=(1-q)**T
  for s in [Q(1,9),Q(1,2),Q(9,10)]:
   for j in range(1,20):
    x=Q(j,20);m=1-c*x**T;d=-c*T*x**(T-1);dd=-c*T*(T-1)*x**(T-2)
    den=1+s*m;w=m/den;wp=d/den**2;wpp=(dd*den-2*s*d*d)/den**3
    assert m>0 and w>0 and wp<0 and wpp<=0
    for b in [Q(-2),Q(0),Q(1,4),Q(3,4),Q(1),Q(2)]:
     # h=(x-b)m / (1+sm), raw numerator n and denominator g.
     n=(x-b)*m;nd=m+(x-b)*d;ndd=2*d+(x-b)*dd;gd=s*d;gdd=s*dd
     rawfirst=(nd*den-n*gd)/den**2
     rawsecond=ndd/den-2*nd*gd/den**2-n*gdd/den**2+2*n*gd*gd/den**3
     assert rawfirst==w+(x-b)*wp
     assert rawsecond==2*wp+(x-b)*wpp
     if x<b:assert rawfirst>0
     if x>=b:assert rawsecond<0
     count+=1
out={'status':'PASS','exact_rational_cases':count,'T_range':[1,16],'scope':'quotient identities and sign checks only; universal proof is the calculus argument in discovery.md; no novelty claim'}
(P/'checks.json').write_text(json.dumps(out,indent=2));print(json.dumps(out))
