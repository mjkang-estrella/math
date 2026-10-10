"""Independent finite exact diagnostics. Standard library only; no writes."""
from fractions import Fraction as Q
import json
count=0
for r in [Q(1,2),Q(1),Q(3,2),Q(7,4)]:
 for t in [Q(1,100),Q(1,17),Q(2,3)]:
  for A in [Q(1,3),Q(2,5),Q(3,7)]:
   for B in [Q(1),Q(4,3),Q(8,9)]:
    At=2/(A-B)+(B-3*A)/(3*t);Bt=1/(A-B)
    P3=r*(r*r-B);P6=6*t*(r*r-A)-P3**2
    P3r=3*r*r-B;P3t=-r*Bt;P6r=12*t*r-2*P3*P3r;P6t=6*(r*r-A)-6*t*At-2*P3*P3t
    assert P6r+P3*P6t-2*P3t*P6==0
    assert P3r+P3*P3t+P6t/2-P3/r+3*(A+t*At)-5*r*r==0
    count+=1
for z in [Q(1,100),Q(1,32),Q(1,2),Q(3)]:
 # (I-Rminus)(I/2-J/(2z)); complex number representation J=i
 ar=2*z*z/(1+z*z);ai=2*z/(1+z*z)
 assert ar/2+ai/(2*z)==1 and ai/2-ar/(2*z)==0
rho=Q(1,100);assert rho*Q(44,3)<Q(1,2) and rho*22<1
support=Q(1,16)+Q(1,4096);assert support<Q(1,4)
exponents=0
for k in range(65):
 for n in range(max(k,4),130):
  assert n+8-k>=8 and 2*n+19-k>=19 and n+7<=2**n
  exponents+=1
print(json.dumps({'status':'PASS_FINITE_DIAGNOSTICS_NOT_PROOF','CLV_compatibility_and_Grad_Shafranov_cases':count,'Picard_radius':str(rho),'Picard_self_map_increment':str(rho*Q(44,3)),'Picard_contraction':str(rho*22),'moving_template_support_over_h':str(support),'two_rotation_inverse_cases':4,'exponent_cases':exponents},sort_keys=True,indent=2))
