from fractions import Fraction as F
from pathlib import Path
import json
L=Path(__file__).parent
r,s=100000,225985;n=3*r+s
def bounds(t):
 lo=sum((2*t**(2*j+1)/F(2*j+1) for j in range(20)),F(0));return lo,lo+2*t**41/(41*(1-t*t))
u,v=bounds(F(3,7)),bounds(F(1,5))
for (lo,hi),d in [(u,9162907318741),(v,4054651081081)]:assert F(d,10**13)<lo<hi<F(d+1,10**13)
loglo=r*u[0]-s*v[1];loghi=r*u[1]-s*v[0]
assert 0<loglo<loghi<F(1,10)
# Independent direct integer mass test, without constructing polynomials.
aa=5**r*2**(s-r);bb=3**s
assert bb<aa<2*bb
assert F(2,5)**6<F(1,100) and F(2,3)**12<F(1,100)
mu=[F(2*r+s,2)+F(4*r,5),F(3*r,2)+F(2*s,3)]
var=[F(2*r+s,4)+F(4*r,25),F(3*r,4)+F(2*s,9)]
assert mu==[F(585985,2),F(901970,3)] and var==[F(489985,4),F(1126970,9)]
assert all(t<126000 for t in var)
windows=[(291993,293993),(295825,297825),(299657,301657)]
assert all(b-a+1==2001 for a,b in windows)
outer=[]
for m,(a,b) in zip(mu,[windows[0],windows[2]]):
 d=min(m-(a-1),(b+1)-m);assert d>1000;outer.append(str(d))
middle=[windows[1][0]-mu[0],mu[1]-windows[1][1]]
assert all(d>2800 for d in middle)
assert 1-F(126000,1000**2)-F(1,100)>F(86,100)
assert F(126000,2800**2)<F(17,1000)
assert F(51,1000)<F(86,100)
assert n==525985 and 2*n==1051970
out={'status':'PASS','r':r,'s':s,'degree':n,'vertices_corona':2*n,'means':list(map(str,mu)),'variances':list(map(str,var)),'outer_min_distances':outer,'middle_min_distances':list(map(str,middle)),'log_ratio_bounds_exact':list(map(str,[loglo,loghi])),'small_control':{'note':'No graph or high-degree polynomial expansion; proof identity checked symbolically in review.'}}
(L/'own-checks.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:v for k,v in out.items() if k!='log_ratio_bounds_exact'}))
