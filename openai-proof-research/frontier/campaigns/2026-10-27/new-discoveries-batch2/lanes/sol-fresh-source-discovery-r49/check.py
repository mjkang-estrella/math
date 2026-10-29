import mpmath as m, json, time
from pathlib import Path
m.mp.dps=45
start=time.monotonic()
def U(a,t):
 return m.sin((1-a)*t)*m.sin(a*t)**(a/(1-a))/m.sin(t)**(1/(1-a))
def w(a,b,x):
 total=m.mpf(0);small=0
 for k in range(3000):
  z=(-x)**k*m.rgamma(b-a*k)/m.factorial(k);total+=z
  small=small+1 if abs(z)<m.mpf('1e-38') else 0
  if small>40:return total
 raise RuntimeError('series truncation not reached')
rows=[]
for a in [m.mpf(1)/2,m.mpf(2)/3,m.mpf(4)/5,m.mpf(9)/10]:
 p=1/(1-a)
 for x in [m.mpf('0.5'),m.mpf(1)]:
  y=x**p
  J=[m.quad(lambda t: U(a,t)**k*m.exp(-y*U(a,t)),[0,m.pi/2,3*m.pi/4,m.pi]) for k in [1,2,3]]
  C=m.gamma(1+a)*p/m.pi
  f=C*x**p*J[0];mean=J[1]/J[0];var=J[2]/J[0]-mean**2
  fs=m.gamma(a)*w(a,0,x)
  first=-m.gamma(a)*w(a,-a,x)
  second=m.gamma(a)*w(a,-2*a,x)
  ds=p/x-p*x**(p-1)*mean
  curvature=(-p-p*(p-1)*y*mean+p**2*y**2*var)/x**2
  errs=[abs(f-fs),abs(first/fs-ds),abs((second/fs-(first/fs)**2)-curvature)]
  assert max(errs)<m.mpf('1e-30'),(a,x,errs)
  rows.append({'alpha':str(a),'x':str(x),'errors':[str(z) for z in errs],'curvature':str(curvature)})
# An exact non-source mixture obstruction, p=6, U=1/5 with equal tilted weights at x=1.
# Original weights 1 and exp(4)/5 make U*weight*exp(-U) equal.
assert -6-6*5*3+6**2*4==48
# Exact logU Taylor coefficient: U(theta)=c(1+a theta^2/2+O(theta^4)).
# This gives w(u) ~ C*(u-c)^(-1/2) and H=(u-c)*(log w)' -> -1/2.
# At infinity U~sin(pi*a)^(1/(1-a))*(pi-theta)^(-p), w~C*u^(-1/p).
for a in [m.mpf('0.6'),m.mpf('0.8'),m.mpf('0.9')]:
 c=(1-a)*a**(a/(1-a));t=m.mpf('1e-5')
 assert abs((U(a,t)/c-1)/t**2-a/2)<m.mpf('1e-10')
result={'status':'PASS identities/route obstructions only','integral_series_checks':rows,'generic_mixture_logcurvature':48,'Kanter_small_angle_checks':3,'seconds':time.monotonic()-start}
Path(__file__).with_name('checks.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result))
