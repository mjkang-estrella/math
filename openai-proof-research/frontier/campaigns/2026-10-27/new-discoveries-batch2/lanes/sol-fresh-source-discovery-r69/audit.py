import json,mpmath as m
from pathlib import Path
m.mp.dps=65
j=json.load(open('scan.json'));x=m.mpf(str(j['best'][1][0]));pars=list(map(lambda z:m.mpf(str(z)),j['best'][1][1]))
def conv(x,a,b,u,c,d,v):
 pts=sorted([-m.inf,-u,u,x-v,x+v,m.inf]);out=m.mpf(0)
 for l,h in zip(pts,pts[1:]):
  z=(l+h)/2 if m.isfinite(l) and m.isfinite(h) else (h-1 if l==-m.inf else l+1)
  A,C=(a,0) if abs(z)<u else (b,-(a-b)*u*u)
  B,D=(c,0) if abs(x-z)<v else (d,-(c-d)*v*v)
  k=A+B;mu=B*x/k
  out+=m.exp(C+D-A*B*x*x/k)*m.sqrt(m.pi/k)/2*(m.erf(m.sqrt(k)*(h-mu))-m.erf(m.sqrt(k)*(l-mu)))
 return out
L=lambda z:m.log(conv(z,*pars))
score=x*m.diff(L,x,2)-m.diff(L,x)
# independent direct quadrature, split at all discontinuous derivative points
p=lambda z,a,b,u:m.exp(-a*z*z) if abs(z)<u else m.exp(-(a-b)*u*u-b*z*z)
f=lambda z:p(z,*pars[:3])*p(x-z,*pars[3:])
scale=conv(x,*pars)
quad=scale*m.quad(lambda z:f(z)/scale,sorted([-m.inf,-pars[2],pars[2],x-pars[5],x+pars[5],m.inf]))
rel=abs(quad-conv(x,*pars))/quad
assert rel<m.mpf('1e-55')
# This value may be very small; sign is numerical, never a certificate.
assert score>0
out={'precision_digits':65,'best_float_score_was':j['best'][0],'recomputed_xLpp_minus_Lp':m.nstr(score,60),'quadrature_relative_error':m.nstr(rel,8),'interpretation':'floating near-negative discarded as cancellation; no counterexample or universal claim'}
open('audit.json','w').write(json.dumps(out,indent=2));print(json.dumps(out))
