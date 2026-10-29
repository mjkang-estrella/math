import mpmath as m,json,pathlib
from fractions import Fraction as F
m.mp.dps=40
rows=[]
for r in [m.mpf('.5'),m.mpf(1),m.mpf(3)]:
 for t in [m.mpf('.4'),m.mpf('1.7'),m.pi]:
  z=m.exp(1j*t)
  def I(k):
   if k==0:return m.quad(lambda x:m.cos(r*m.log(x))*z/(1-z*x),[0,.01,.1,1])
   if k==1:return m.quad(lambda x:m.cos(r*m.log(x))*z/(1-z*x)**2,[0,.01,.1,1])
   return m.quad(lambda x:m.cos(r*m.log(x))*z*(1+z*x)/(1-z*x)**3,[0,.01,.1,1])
  g,dg,d2g=[I(k) for k in range(3)]
  v=m.pi/2*m.sinh(r*(m.pi-t))/m.sinh(m.pi*r)
  vp=-m.pi*r/2*m.cosh(r*(m.pi-t))/m.sinh(m.pi*r)
  err=max(abs(g.imag-v),abs(dg.real-vp),abs((-d2g-r*r*g).real-1/(4*m.sin(t/2)**2)))
  # dg.real = boundary imaginary-part derivative
  assert err<m.mpf('1e-30'),err
  W=(dg*g.conjugate()).real
  assert W>0
  rows.append({'r':str(r),'theta':str(t),'max_identity_error':str(err),'W':str(W)})
# r=1+2i: a2=(14+12i)/17, |a2|^2=20/17.
a2abs2=F(14*14+12*12,17*17)
assert a2abs2==F(20,17)>1
out={'status':'PASS','diagnostics_only':True,'boundary_integral_probes':rows,'complex_a2_abs_squared':str(a2abs2),'complex_S_a2_abs':str(2*a2abs2)}
pathlib.Path(__file__).with_name('checks.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
