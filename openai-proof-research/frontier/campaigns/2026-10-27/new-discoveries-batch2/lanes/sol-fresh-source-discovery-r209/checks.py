from fractions import Fraction as F
import json

# Unit-covolume packing radii, compared by exact sixth powers.
t=F(11,20)
assert F(27,1024) < t**6 < F(1,32)

# Exact layer-cake/stop-loss identity for finite rational controls.
def moment(dist,p): return sum(w*x**p for x,w in dist)
def stoploss_integral(dist,p):
    # integral_0^x t^(p-2)(x-t)dt = x^p/(p(p-1)).
    return sum(w*x**p/F(p*(p-1)) for x,w in dist)
controls=[[(F(0),F(2,3)),(F(2),F(1,3))],[(F(1),F(1))],[(F(1,3),F(1,2)),(F(7,3),F(1,2))]]
for d in controls:
    for p in range(2,13):
        assert moment(d,p)==p*(p-1)*stoploss_integral(d,p)
a,b=controls[:2]
assert moment(a,1)<moment(b,1)
assert moment(a,2)>moment(b,2)
assert max(x for x,w in a)>max(x for x,w in b)
assert moment(a,3)>moment(b,3)
print(json.dumps({'status':'PASS','rational_packing_witness':'27/1024 < (11/20)^6 < 1/32','layer_cake_controls':33,'abstract_endpoint_control':'p=2 and maximum-radius ordering do not imply p=1','limits':'No lattice optimization, source resolution, or universal stop-loss inequality certified.'},sort_keys=True))
