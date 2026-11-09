#!/usr/bin/env python3
# Independent reviewer checker. Does not read/import root checker/results.
import resource
CAP=512*1024*1024
resource.setrlimit(resource.RLIMIT_AS,(CAP,CAP))
import mpmath as m, json, datetime, time
from pathlib import Path
m.mp.dps=32
start=time.monotonic(); rows=[]
def check(name,x,y,tol='1e-22'):
 e=abs(x-y)/max(1,abs(x),abs(y)); ok=e<m.mpf(tol)
 rows.append(dict(name=name,error=str(e),pass_check=bool(ok)))
 assert ok,(name,x,y,e)
def E(a,z):
 return m.nsum(lambda k:z**k/m.gamma(1+a*k),[0,m.inf])
def halfcf(a,q): # precision a in density 2 sqrt(a/pi) exp(-a x^2)
 return m.exp(-q*q/(4*a))*(1+1j*m.erfi(q/(2*m.sqrt(a))))
def conv(a,b,x): # density V-W; direct convolution, no erfc input
 return 4*m.sqrt(a*b)/m.pi*m.quad(lambda y:m.exp(-a*(y+x)**2-b*y*y),[max(0,-x),m.inf])
def mix(a,b,t,k=0): # compact angular coordinate, not root's infinite u quadrature
 C=m.sqrt(a*b/(m.pi*(a+b)));c=a*b/(a+b)
 out=0
 for d in [a/m.sqrt(a+b),b/m.sqrt(a+b)]:
  def f(th):
   cs=m.cos(th); B=c*cs*cs+d*d; rate=cs*cs/(4*B)
   return cs/m.sqrt(B)*rate**k*m.exp(-t*rate)
  out+=m.quad(f,[0,m.pi/4,m.pi/2])
 return 2*C/m.sqrt(m.pi)*out
def skewcdf(x,w,lam): # direct definition [3], never uses Owen T
 return m.quad(lambda z:2*m.exp(-z*z/2)/m.sqrt(2*m.pi)*(1+m.erf(lam*z/m.sqrt(2)))/2,[-m.inf,0,x/w]) if x>=0 else m.quad(lambda z:2*m.exp(-z*z/2)/m.sqrt(2*m.pi)*(1+m.erf(lam*z/m.sqrt(2)))/2,[-m.inf,x/w])
def pap(s0,s1,s2,x):
 s=m.sqrt(s0*s0+s1*s1+s2*s2);h=s1/s0;j=s2/s0
 w1=s*m.sqrt(1+j*j)/h;w2=s*m.sqrt(1+h*h)/j
 l1=j/h*s/s0;l2=h/j*s/s0
 return 2/s*m.exp(-x*x/(2*s*s))/m.sqrt(2*m.pi)*(skewcdf(x,w1,-l1)-skewcdf(x,w2,l2))
def noisy_from_erfc(s0,s1,s2,x):
 a=1/(2*s1*s1);b=1/(2*s2*s2);c=a*b/(a+b);C=2*m.sqrt(a*b/(m.pi*(a+b)))
 def f(y):
  d=a if y>=0 else b
  return C*m.exp(-c*y*y)*m.erfc(d*abs(y)/m.sqrt(a+b))*m.exp(-(x-y)**2/(2*s0*s0))/(s0*m.sqrt(2*m.pi))
 return m.quad(f,[-m.inf,0,m.inf])
for aa,bb in [('0.03','7'),('1','1'),('4','0.2'),('0.4','2')]:
 a=m.mpf(aa);b=m.mpf(bb)
 for x in [m.mpf('0'),m.mpf('.3'),m.mpf('1.2')]:
  C=m.sqrt(a*b/(m.pi*(a+b)));c=a*b/(a+b)
  formula=C*m.exp(-c*x*x)*(m.erfc(a*x/m.sqrt(a+b))+m.erfc(b*x/m.sqrt(a+b)))
  check('convolution-sym '+str((aa,bb,str(x))),(conv(a,b,x)+conv(a,b,-x))/2,formula)
 check('mass '+aa+','+bb,mix(a,b,0),1)
 for t in [m.mpf('.07'),m.mpf('1.3')]:
  f=lambda z:m.re(halfcf(a,m.sqrt(z))*m.conj(halfcf(b,m.sqrt(z))))
  for k in range(5):check('literal-CF derivative '+str((aa,bb,str(t),k)),(-1)**k*m.diff(f,t,k),mix(a,b,t,k))
for s0,s1,s2 in [(1,2,3),(.7,.3,2)]:
 s0,s1,s2=map(lambda v:m.mpf(str(v)),(s0,s1,s2))
 for x in [-m.mpf('.8'),m.mpf('.4')]:check('noisy density skewCDF vs convolution '+str((s0,s1,s2,x)),pap(s0,s1,s2,x),noisy_from_erfc(s0,s1,s2,x),'1e-20')
# Genuine half-normal mixing example alpha=1/4: M_(2alpha)=M_1/2 is explicit.
for q in [m.mpf('.2'),m.mpf('.7')]:
 got=m.quad(lambda r:halfcf(1/(4*r),q)*m.exp(-r*r/4)/m.sqrt(m.pi),[0,1,m.inf])
 check('M1/4 characteristic mixture '+str(q),got,E(m.mpf('.25'),1j*q),'1e-20')
# General subordination Mellin moments, noninteger orders and nu including >1/2.
for a in map(m.mpf,['.07','.25','.413']):
 for p in map(m.mpf,['0','.3','1','2.7','7']):
  # moment half-normal of variance 2tau, then M_(2a) moment p/2
  h=2**p*m.gamma((p+1)/2)/m.sqrt(m.pi)
  sub=h*m.gamma(1+p/2)/m.gamma(1+a*p)
  check('subordination moment '+str((a,p)),sub,m.gamma(1+p)/m.gamma(1+a*p))
res=dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),hard_address_space_cap_bytes=CAP,checks=len(rows),passed=all(r['pass_check'] for r in rows),max_error=max(float(r['error']) for r in rows),wall_seconds=time.monotonic()-start,maxrss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,rows=rows,proof=False)
Path(__file__).with_name('own-check-results.json').write_text(json.dumps(res,indent=2));print(json.dumps({k:v for k,v in res.items() if k!='rows'}))
