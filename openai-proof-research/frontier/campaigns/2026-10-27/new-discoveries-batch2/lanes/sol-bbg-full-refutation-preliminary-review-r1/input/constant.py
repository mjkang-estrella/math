import os,resource,signal
for k in ['OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS']:os.environ[k]='1'
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,)*2);resource.setrlimit(resource.RLIMIT_CPU,(20,20));signal.alarm(25)
from fractions import Fraction as F
from math import factorial
from pathlib import Path
import json,datetime
D=10**30;cd=lambda a,b:-((-a)//b)
def log_interval(x,K):
 z=(x-1)/(x+1);assert 0<z<1
 s=2*sum((z**(2*j+1)/F(2*j+1) for j in range(K)),F(0));e=2*z**(2*K+1)/((2*K+1)*(1-z*z))
 return s,s+e
tlo,thi=log_interval(F(3),70);tlo=F(tlo.numerator*D//tlo.denominator,D);thi=F(cd(thi.numerator*D,thi.denominator),D)
_,l10hi=log_interval(F(10),220);l10hi=F(cd(l10hi.numerator*D,l10hi.denominator),D)
h=F(sum(D//n for n in range(1,10001)),D);glo=h-4*l10hi-F(1,10000)
lllo,_=log_interval(tlo,25);lllo=F(lllo.numerator*D//lllo.denominator,D)
ei=glo+lllo+sum((tlo**k/(k*factorial(k)) for k in range(1,40)),F(0));assert ei>F(21635,10000)
out={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'status':'PASS','scope':'rigorous Ei(log3)>2.1635 via Euler gamma lower bound and positive series','Ei_lower':str(ei),'gamma_lower':str(glo),'Ei_lower_decimal_diagnostic':float(ei),'AS':512*1024**2,'CPU':20,'wall_alarm':25,'BLAS_threads':1}
Path(__file__).with_name('constant.json').write_text(json.dumps(out,indent=2));print(out['status'],float(ei))
