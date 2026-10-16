from fractions import Fraction as F
import json
# Represent coefficients of sqrt(5),sqrt(15).
kA=(F(3,5),F(0)); kB=(F(0),F(4,15)); kC=(F(0),F(19,60))
gap=tuple(kC[i]-(kA[i]+kB[i])/2 for i in range(2))
assert gap==(-F(3,10),F(11,60))
assert (F(11,60)**2)*15 > (F(3,10)**2)*5
nuA=(F(1),F(0)); nuB=(F(0),F(1,5)); nuC=(F(0),F(2,5))
ngap=tuple(nuC[i]-(nuA[i]+nuB[i])/2 for i in range(2))
assert ngap==(-F(1,2),F(3,10))
assert F(3,10)**2*15 > F(1,2)**2*5
assert all(x>F(1,4) for x in [F(5),F(3,5),F(12,5)])
uA=F(3,5);uB=F(3,2);uC=(uA+uB)/2;phi=F(17,8)
second=(1-phi**2)*(1/uC-F(1,2)/uA-F(1,2)/uB)
assert second==F(675,896)
print(json.dumps({'status':'PASS_FINITE_ARITHMETIC_ONLY','rate_gap_coefficients':list(map(str,gap)),'photon_gap_coefficients':list(map(str,ngap)),'physical_covariances':True,'second_derivative':str(second)},indent=2))
