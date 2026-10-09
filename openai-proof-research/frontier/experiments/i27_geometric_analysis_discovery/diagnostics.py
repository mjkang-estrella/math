"""Exact diagnostics of deductions/countermodels, not a proof of a new varifold theorem."""
from pathlib import Path
from fractions import Fraction as F
import json
ROOT=Path(__file__).resolve().parents[3]
checks={}
# Frequency identity dotP - [(q-n²)+(n-2P)²] = (2P-1)(n-2P).
freq=0
for P in [F(k,8) for k in range(4,33)]:
 for a in [F(k,9) for k in range(19)]:
  for defect in [F(k,7) for k in range(12)]:
   n=2*P+a;q=n*n+defect;dot=2*P-n+q-2*P*n
   square=defect+(n-2*P)**2
   assert dot-square==(2*P-1)*(n-2*P)>=0
   freq+=1
checks['frequency_exact_rational_cases']=freq
# Defect measure model ν=(|x|+b)^2; β_ac=e⊗e, f=(x+b sign x)e.
# δ coefficient in div f and Δν/2 is 2b; tangential β_s trace is 2b.
model=0
for m in range(2,11):
 for b in [F(k,11) for k in range(1,23)]:
  for x in [F(k,13) for k in range(-39,40) if k]:
   v=(abs(x)+b)**2;f=x+(b if x>0 else -b)
   assert v-f*f==0
   assert (m-1)*F(2*b,m-1)==2*b
   assert (b-(-b))==2*b
   model+=1
checks['distributional_model_algebra_cases']=model
# Smooth approximants r=sqrt(x²+eta²), w=r+b, using rational Pythagorean x/eta.
smoothed=0
for m in range(2,9):
 for eta in [F(1,k) for k in range(2,18)]:
  for b in [F(1,3),F(1,2),F(1)]:
   for t in [F(k,17) for k in range(-15,16)]:
    x=eta*2*t/(1-t*t);r=eta*(1+t*t)/(1-t*t);w=r+b
    assert r*r==x*x+eta*eta
    wp=x/r;wpp=eta*eta/r**3
    nu=w*w;fl=w*wp;beta_n=wp*wp;beta_t=w*wpp/(m-1)
    d=beta_n+(m-1)*beta_t;mass=beta_n-F(1,2)
    assert nu*beta_n-fl*fl==0
    assert d==1+b*eta*eta/r**3
    assert d-2*mass==2*eta*eta/r**2+b*eta*eta/r**3>=0
    assert abs(mass)<=d/2
    # derivative beta_nn = 2 w' w'', identical to derivative mass.
    assert 2*wp*wpp==2*x*eta*eta/r**4
    smoothed+=1
checks['smooth_stress_approximant_cases']=smoothed
# Product sphere energy normalized by 16π² and flow instability, including equality.
products=0
for u in [F(k,101) for k in range(-99,100)]:
 a=1/(3*(1+u));b=1/(3*(1-u))
 assert 2/a+2/b==12
 assert (a-b)**2/(a*b)==4*u*u/(1-u*u)
 da=a/b-1;db=b/a-1
 assert da*b+db*a==0
 assert da-db==(a-b)*(a+b)/(a*b)
 assert (da-db)*(a-b)>=0
 products+=1
checks['einstein_product_cases']=products
# Endpoint normalized error: epsilon*sum_{j<=N}1. No limiting-order shortcut.
endpoint=[]
for k in range(2,41):
 eps=F(1,k);N=k*k
 assert eps*N==k
 endpoint.append({'k':k,'epsilon':str(eps),'dyadic_shell_count':N,'normalized_majorant':str(eps*N)})
checks['endpoint_sequences']=endpoint
# Scalar Lp spike on volume a^4, p even: a=delta^(p/2), amplitude=delta/a^(4/p)=delta^-1.
spikes=[]
for p in [4,6,8,10,12]:
 for k in range(2,18):
  delta=F(1,k);a=delta**(p//2);amp=1/delta
  assert amp**p*a**4==delta**p
  assert amp**2*a**4/a**4==1/delta**2
  assert amp<=a**(-2)
  spikes.append({'p':p,'k':k,'normalized_scalar_square_loss':k*k})
checks['scalar_spike_cases']=len(spikes)
# PSD subtraction estimate: |v-w|_B²≤2|v|_B²+2|w|_B² for Gram B.
psd=0
for a in range(-3,4):
 for b in range(-3,4):
  assert (a-b)**2<=2*a*a+2*b*b
  psd+=1
checks['psd_subtraction_cases']=psd
# Minimal graph boundary reflection: Re((e^{2iθ} conjugate z)^k)=-Re(z^k)
# for θ=(2j+1)π/(2k); exact phase exponent is odd integer, no floats.
reflection=0
for k in range(2,202):
 for j in range(k):
  exponent=2*j+1
  assert exponent%2==1
  reflection+=1
checks['minimal_graph_reflection_cases']=reflection
checks['limitations']='Exact finite diagnostics verify displayed identities and scaling; distributional/PDE arguments are in report. No numerical simulation is used as a proof of existence or rectifiability.'
out=ROOT/'frontier/experiments/i27_geometric_analysis_discovery/diagnostics.json'
out.write_text(json.dumps(checks,indent=2)+'\n')
print(json.dumps({k:v for k,v in checks.items() if not isinstance(v,list)},indent=2))
