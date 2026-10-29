from fractions import Fraction as F
import json
# Checks of the rational certificates in PROOF.md; the universal steps are proved there.
for n in range(2,33):
 p=F(n-1,n);a=2*(48*n)**n
 first=2/p/F(48*n)
 tail=F(1152,a*a)
 assert a>=8192 and first<=F(1,24) and tail<F(1,24)
 assert first+tail<F(1,12)<F(1,6)
 print(json.dumps({'n':n,'p':str(p),'a':str(a),'first_bound':str(first),'tail_bound':str(tail),'sum_lt_one_twelfth':True}))
count=0
for a in [F(1,2),F(1),F(3),F(11)]:
 for k in range(-5,46):
  s=a*F(k,20)
  overlap=max(F(0),min(a,s)-max(F(0),s-a))
  claimed=min(s,2*a-s) if 0<=s<=2*a else 0
  assert overlap==claimed;count+=1
print(json.dumps({'exact_convolution_overlap_checks':count,'status':'PASS','limits':'finite arithmetic sanity checks; not the universal analytic proof'}))
