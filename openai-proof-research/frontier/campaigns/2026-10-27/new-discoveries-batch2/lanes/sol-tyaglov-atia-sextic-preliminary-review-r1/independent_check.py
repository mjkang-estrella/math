"""Independent exact rational arithmetic; no candidate code or CAS imported."""
from fractions import Fraction as F
from pathlib import Path
import json

def add(a,b):
    return [(a[i] if i<len(a) else 0)+(b[i] if i<len(b) else 0) for i in range(max(len(a),len(b)))]
def mul(a,b):
    c=[0]*(len(a)+len(b)-1)
    for i,u in enumerate(a):
        for j,v in enumerate(b): c[i+j]+=u*v
    return c
def scale(a,c): return [c*v for v in a]
def deriv(a): return [i*a[i] for i in range(1,len(a))]
def val(a,x):
    y=0
    for c in reversed(a): y=y*x+c
    return y
roots=[-13,-2,-1,3,13]
dp=[300]
for r in roots: dp=mul(dp,[-r,1])
# Reconstruct the polynomial by integration, independently of displayed coefficients.
p=[F(108312103)]+[F(c,i+1) for i,c in enumerate(dp)]
assert p==[108312103,304200,177450,-600,-13200,0,50]
assert deriv(p)==dp
ddp=deriv(dp)
critical=[val(p,r) for r in roots]
assert critical==[3,108210303,108172803,109772803,5272803]
assert all(v>0 for v in critical) and p[-1]>0 and (len(p)-1)%2==0
num=add(scale(mul(p,ddp),4),scale(mul(dp,dp),-3))
j=[v/F(1200) for v in num]
assert j==[127901873749,-1479679536,-57294664659,-79953900,525944015,1064700,414050,-900,-13200,0,25]
intervals=[(-20,-19),(-14,-13),(-13,-12),(-2,-1),(1,2),(12,13),(14,15),(19,20)]
rows=[]
for a,b in intervals:
    u,v=val(j,a),val(j,b)
    assert a<b and u*v<0
    rows.append([a,b,int(u),int(v)])
assert all(intervals[i][1]<=intervals[i+1][0] for i in range(7))
assert F(1,2)<F(3,4)<F(5,6)
assert all(val(ddp,r)!=0 and val(num,r)!=0 for r in roots)
# Actual 2024 Example 16.2, independently expanded.
e=[F(1,10),0,20,-28,7,1]
assert deriv(e)==[0,40,-84,28,5]
ed,edd=deriv(e),deriv(deriv(e))
samples=[]
for x in [F(-27,20),F(-11,40)]:
    m=val(e,x)*val(edd,x)/val(ed,x)**2
    samples.append({'x':str(x),'M':str(m),'M_minus_two_thirds':str(m-F(2,3))})
assert F(samples[0]['M'])>F(2,3)>F(samples[1]['M'])
assert val(e,F(3,2))==F(-1019,160)<0
# Complete lower-degree bridge from the actual 2024 Section 16 mechanism.
w=[2,0,-2,0,1]  # (x^2-1)^2+1 > 0
wd=deriv(w)
assert wd==[0,-4,0,4]
wn=add(scale(mul(w,deriv(wd)),50),scale(mul(wd,wd),-37))
k=[-50,0,126,0,-27,0,1]
assert wn==scale(k,8)
assert F(1,2)<F(37,50)<F(3,4)
bridge_intervals=[(-6,-3),(-3,-1),(-1,0),(0,1),(1,3),(3,6)]
bridge_rows=[]
for a,b in bridge_intervals:
    u,v=val(k,a),val(k,b)
    assert u*v<0
    bridge_rows.append([a,b,u,v])
# Three real roots of e: signs around -10, 1, 2; exactly two nonreal roots
# follows by derivative extrema plus the positive min at zero and positive max
# on (-8,-7). We only need its odd degree and negative value here.
out={'status':'PASS','ascending_P':[int(v) for v in p],
     'ascending_derivative':dp,'critical_values':[int(v) for v in critical],
     'critical_second_derivatives':[int(val(ddp,r)) for r in roots],
     'ascending_J':[int(v) for v in j],'intervals_and_exact_J_values':rows,
     'example16_2_exact_samples':samples,'example16_2_at_3_over_2':str(val(e,F(3,2))),
     'complete_positive_quartic_bridge':{'P':w,'kappa':'37/50','50PPdd_minus_37Pd_squared':wn,'equals':'8*(x^6-27*x^4+126*x^2-50)','six_intervals_and_K_values':bridge_rows},
     'analytic_bridges':'Coercive continuous P has an attained minimum, derivative zero there. All critical values >=3. IVT on eight disjoint open intervals. Thus P>=3 and >=8 distinct numerator roots; source denominator P^2 is positive.'}
Path(__file__).with_name('independent-evidence.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
