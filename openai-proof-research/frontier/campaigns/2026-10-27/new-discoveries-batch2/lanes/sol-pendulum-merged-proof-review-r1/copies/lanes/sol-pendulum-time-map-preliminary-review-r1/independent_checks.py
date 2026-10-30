"""Finite diagnostics only; run through the designated unchanged helper_guard.py."""
from pathlib import Path
import json, math
import mpmath as m
m.mp.dps = 40
O = Path(__file__).resolve().parent
def T(a,z):
    if z == 0:
        return m.quad(lambda u: 1/m.sqrt(2-a*m.sin(u)**2), [0,m.pi/2])
    phi,b=m.acos(1-a)/2,m.acos(1-z)/2
    return sum(c*m.quad(lambda u: 1/m.sqrt(a+z-2*m.sin(c*u)**2),[0,1]) for c in [phi,b])
def moment(a,z,n):
    s=a+z
    return 2*s**n*sum(m.quad(lambda u:m.sin(u)**(2*n),[0,m.asin(m.sqrt(v/s))]) for v in [a,z])
rows=[]
for aa,zz in [('0.0001','0.0002'),('0.1','1.9'),('1','1'),('1.9','0.1'),('1.999','1.999'),('0.7','0.43')]:
    a,z=map(m.mpf,[aa,zz]);s=a+z
    assert abs(moment(a,z,0)-m.pi)<m.mpf('1e-32')
    assert abs(moment(a,z,1)-(m.pi*s/2-2*m.sqrt(a*z)))<m.mpf('1e-32')
    for n in [2,3,7]:
        p=m.mpf(n)-m.mpf('.5')
        A=m.quad(lambda t:t**p/m.sqrt(s-t),[0,a])
        B=m.quad(lambda y:(z-y)**p/m.sqrt(a+y),[0,z])
        assert abs(A+B-moment(a,z,n))<m.mpf('1e-28')
    curv=m.diff(lambda w:T(a,w),z,2)
    I=sum(c*m.quad(lambda u:(s-2*m.sin(c*u)**2)**(-m.mpf('2.5')),[0,1]) for c in [m.acos(1-a)/2,m.acos(1-z)/2])
    g=z*z-2*(1-a)*z-2*a
    direct=(3*I+g/(z*(2-z)*a)**m.mpf('1.5'))/4
    assert abs(curv-direct)<m.mpf('1e-20')*max(1,abs(curv))
    lower=m.sqrt(a)/(16*m.sqrt(2)*z**m.mpf('1.5'))
    assert curv>=lower
    partial=sum(m.mpf(math.comb(2*n,n))/8**n*moment(a,z,n) for n in range(16))/(2*m.sqrt(2))
    q=max(a,z)/2
    tail=m.pi/(2*m.sqrt(2))*q**16/(1-q)
    assert -m.mpf('1e-30')<=T(a,z)-partial<=tail+m.mpf('1e-30')
    rows.append({'a':aa,'z':zz,'curvature':str(curv),'lower_bound':str(lower),'series_gap':str(T(a,z)-partial),'tail_bound':str(tail)})
endpoint=[]
for a in map(m.mpf,['0.001','0.7','1.999']):
    vals=[T(a,m.mpf(z)) for z in ['0','.4','1.2','2']]
    for x,y in [(0,2),(0,m.mpf('1.2')),(m.mpf('.4'),2)]:
        assert T(a,(x+y)/2)<(T(a,x)+T(a,y))/2
    endpoint.append({'a':str(a),'T0':str(vals[0]),'T2':str(vals[-1])})
a=z=m.mpf(1)
B0=lambda w:2*m.asin(m.sqrt(w/(a+w)))
assert m.diff(B0,z,2)<0
out={'status':'PASS','curvature_series_cases':rows,'moment_convolution_controls':18,'endpoint_Jensen_controls':9,'endpoint_values':endpoint,'M0_separate_moving_piece_curvature':str(m.diff(B0,z,2)),'qualification':'Finite arbitrary-precision diagnostics, not interval certificates or universal proof.'}
(O/'independent-checks.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
