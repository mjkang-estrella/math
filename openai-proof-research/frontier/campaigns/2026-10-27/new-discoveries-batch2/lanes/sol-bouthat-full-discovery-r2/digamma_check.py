import os
os.environ.update(OPENBLAS_NUM_THREADS='1',OMP_NUM_THREADS='1',MKL_NUM_THREADS='1')
import resource
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,512*1024**2));resource.setrlimit(resource.RLIMIT_CPU,(80,80))
import mpmath as mp,json
from pathlib import Path
mp.mp.dps=50
rows=[];ident=[]
for et in ['0.348','0.3','0.1','0.01','0.0001','0.000001']:
 e=mp.mpf(et);a=mp.sqrt(e-e*e/4);z=e/2+1j*a
 def rr(x):return mp.im(mp.digamma(x*(1-z))-mp.digamma(-x*z))/a
 def dr(x):return mp.im((1-z)*mp.polygamma(1,x*(1-z))+z*mp.polygamma(1,-x*z))/a
 for n in [1,2,5,20]:
  direct=mp.fsum(n/(j*j+e*n*(n-j)) for j in range(n))
  ident.append({'epsilon':et,'n':n,'error':str(abs(rr(n)-direct))})
 fails=[]
 for j in range(41):
  x=mp.power(10,mp.mpf(j)/10)
  d=dr(x);dl=d+(1/e-1)/(x*x)
  if d>0 or dl<0:fails.append({'x':str(x),'R_derivative':str(d),'L_derivative':str(dl)})
 rows.append({'epsilon':et,'x_grid':'10^(j/10), j=0..40','failures':fails})
Path(__file__).with_name('digamma-checks.json').write_text(json.dumps({'proof':False,'precision':50,'identities':ident,'derivatives':rows},indent=2))
print(json.dumps({'max_identity_error':str(max(mp.mpf(v['error']) for v in ident)),'failures':[len(r['failures']) for r in rows]}))
