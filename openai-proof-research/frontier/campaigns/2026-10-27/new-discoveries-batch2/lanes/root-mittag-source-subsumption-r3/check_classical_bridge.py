"""Independent diagnostics, not proof. Reproduce with python3 check_classical_bridge.py."""
import os
os.environ['OPENBLAS_NUM_THREADS'] = '1'
os.environ['OMP_NUM_THREADS'] = '1'
import resource
resource.setrlimit(resource.RLIMIT_AS, (512*1024**2,512*1024**2))
import math, json, random
from scipy.integrate import quad
from scipy.special import ndtr, owens_t, erfc, erfi, gammaln

rows=[]
def check(label,left,right,tol=3e-10):
    error=abs(left-right)/max(1,abs(left),abs(right))
    rows.append(dict(label=label,left=float(left),right=float(right),error=float(error),passed=bool(error<tol)))
    assert error<tol,(label,left,right,error)

def diff_density(x,a,b):
    if x<0:return diff_density(-x,b,a)
    return 2*math.sqrt(a*b/(math.pi*(a+b)))*math.exp(-a*b*x*x/(a+b))*erfc(a*x/math.sqrt(a+b))

def papad(x,noise,s1,s2):
    th1,th2=s1/noise,s2/noise
    s=math.sqrt(noise**2+s1**2+s2**2)
    w1=s*math.sqrt(1+th2**2)/th1
    w2=s*math.sqrt(1+th1**2)/th2
    l1=th2/th1*math.sqrt(1+th1**2+th2**2)
    l2=th1/th2*math.sqrt(1+th1**2+th2**2)
    G=lambda z,l:ndtr(z)-2*owens_t(z,l)
    p=2/s*math.exp(-(x/s)**2/2)/math.sqrt(2*math.pi)*(G(x/w1,-l1)-G(x/w2,l2))
    sym=4/s*math.exp(-(x/s)**2/2)/math.sqrt(2*math.pi)*(owens_t(x/w1,l1)+owens_t(x/w2,l2))
    return p,sym

for noise,s1,s2 in [(1,1,1),(.3,1,2),(2,.4,1),(.2,3,.7)]:
    a,b=1/(2*s1*s1),1/(2*s2*s2)
    for x in [-2,-.3,0,.3,2]:
        conv=lambda z:diff_density(z,a,b)*math.exp(-((x-z)/noise)**2/2)/(noise*math.sqrt(2*math.pi))
        direct=quad(conv,-math.inf,0,epsabs=1e-11)[0]+quad(conv,0,math.inf,epsabs=1e-11)[0]
        p,sym=papad(x,noise,s1,s2)
        check('Papad Eq2 vs independent convolution',p,direct)
        check('Papad symmetrization',sym,(p+papad(-x,noise,s1,s2)[0])/2)

def mixture_cf(a,b,t):
    C=math.sqrt(a*b/(math.pi*(a+b)))
    c=a*b/(a+b)
    ans=0
    for d in [a/math.sqrt(a+b),b/math.sqrt(a+b)]:
        def integrand(theta):
            A=c+(d/math.cos(theta))**2
            return math.exp(-t/(4*A))/math.sqrt(A)
        ans+=quad(integrand,0,math.pi/2,epsabs=1e-12)[0]
    return 2*C/math.sqrt(math.pi)*ans

rng=random.Random(20261029)
for i in range(48):
    v,w=10**rng.uniform(-1,1),10**rng.uniform(-1,1)
    t=rng.uniform(0,2)
    a,b=1/(4*v),1/(4*w)
    literal=math.exp(-(v+w)*t)*(1+erfi(math.sqrt(v*t))*erfi(math.sqrt(w*t)))
    check('Gaussian mixture vs literal Ehalf product',mixture_cf(a,b,t),literal)
    check('mixture probability normalization',mixture_cf(a,b,0),1)

for alpha in [.1,.2,1/3,.49]:
    for n in range(11):
        log_product=(gammaln(1+n/2)-gammaln(1+alpha*n))+(gammaln(1+n)-gammaln(1+n/2))
        check('subordination moment cancellation',log_product,gammaln(1+n)-gammaln(1+alpha*n))

out=dict(status='PASS',checks=len(rows),max_error=max(r['error'] for r in rows),proof_claim=False,rows=rows)
open('check-results.json','w').write(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:v for k,v in out.items() if k!='rows'},indent=2))
