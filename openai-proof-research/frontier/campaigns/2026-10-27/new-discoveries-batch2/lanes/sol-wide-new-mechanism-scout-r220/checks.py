from fractions import Fraction as F
import json
def a(k):return {1:F(2,3),2:F(1,3)}.get(k,F(1,k))
assert a(1)==2*a(2) and a(2)>=a(3)
# Beyond k=3 these are identities/monotonicity of 1/k, rather than finite evidence.
for j in range(1,9):assert a(2*j-1)>=F(2*j,2*j-1)*a(2*j)
assert F(1,640)<F(7,12*5**3)
assert F(8111*433,221184*250)>F(1,16)+F(1,1200)
# Ratio of U_(m+1)*(2m+5)^3 to U_m*(2m+3)^3 is
# (2m+5)^2/[4*(2m+4)*(2m+3)^3] <1 for m>=1:
# (2m+5)<2*(2m+3), so numerator <4*(2m+3)^2 < denominator.
assert 433**2<3*250**2
assert F(7,13360)<F(1,1800)
print(json.dumps({'status':'PASS','scope':'exact rational constants and coefficient boundary; universal inequalities proved in PROOF.md','credit':0}))
