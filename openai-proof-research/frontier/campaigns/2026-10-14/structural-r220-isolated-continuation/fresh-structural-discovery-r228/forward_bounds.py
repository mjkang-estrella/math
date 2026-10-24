"""Exact rational bounds for the explicitly stated forward local/tail maps.
No finite-interval matching, global expander, or compact flow is certified.
"""
from fractions import Fraction as F
import json
from pathlib import Path
R=Path(__file__).resolve().parent
S=F(100); Z=F(600); seed=F(75); dmax=F(401,1000)
K=F(1,3)/(F(1,2)-3/S)
L=30/S+F(751,4)/S**2+F(1215,4)/S**3
a=3*Z/S**3
image=seed+K*(3*L*Z+F(1215,4)*dmax+18*Z**2/S**3)
lip=K*(3*L+3*a*(2+a)/(1-a)**2)
K6=F(1,3)/(F(1,2)-6/S)
remainder_lip=K6*(3*L+3*a*(2+a)/(1-a)**2)
assert remainder_lip<1
r=F(1,10)
origin_image=F(1,20)+(dmax+r/(1-r))/264
origin_lip=1/(264*(1-r)**2)
assert a<F(1,2) and image<600 and lip<F(69,100)
assert origin_image<r and origin_lip<F(1,200)
rows={k:str(v) for k,v in dict(S=S,Z=Z,seed=seed,dmax=dmax,K=K,L=L,p_bound=a,tail_image=image,tail_lipschitz=lip,K6=K6,tail_remainder_lipschitz=remainder_lip,origin_image=origin_image,origin_lipschitz=origin_lip).items()}
out={'domain':'0<d<=401/1000; conjugate stable tail coordinates at S=100 of modulus <=75/100^3; origin slope |a|<=1/20 on complex disk |y|<=1','arithmetic':'exact fractions; the exponential kernel bounds are proved in notes/04-forward-construction.md','values':rows,'coverage':'origin and tail fixed points only; no global matching or geometric continuation'}
(R/'private/forward-rational-bounds.json').write_text(json.dumps(out,indent=2))
print(json.dumps(out,indent=2))
