"""Deterministic exact identities and three diagnostics; no theorem certificate."""
import resource
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,512*1024**2))
import sympy as S, mpmath as m, json, time
from pathlib import Path
P=Path(__file__).resolve().parent
z,s,y,t,a,c=S.symbols('z s y t a c')
q=[S.Integer(1)]
for n in range(1,9):q.append(S.expand(sum((a*S.Rational(k,k+1)+c)*q[n-k] for k in range(1,n+1))/n))
G=S.exp(a*(-S.log(1-z)/z-1)-c*S.log(1-z))
assert S.expand(S.series(G,z,0,9).removeO()-sum(q[n]*z**n for n in range(9)))==0
checks={
'partial_fraction_U':S.factor(1-y*y/((y+1)*(y+s))-(1/(1-s)/(y+1)-s*s/(1-s)/(y+s)))==0,
'partial_fraction_V':S.factor(-y/((y+1)*(y+s))-(s/(1-s)/(y+s)-1/(1-s)/(y+1)))==0,
'filtered_U':S.simplify(((S.exp(-t)-s*s*S.exp(-s*t)) +(-S.exp(-t)+s**3*S.exp(-s*t)))/(1-s)+s*s*S.exp(-s*t))==0,
'filtered_V':S.simplify(((s*S.exp(-s*t)-S.exp(-t))+(-s*s*S.exp(-s*t)+S.exp(-t)))/(1-s)-s*S.exp(-s*t))==0,
'generating_function_coefficients_through_8':True}
assert all(checks.values())
m.mp.dps=70
# q-series for Phi and Phi_t: finite truncation, cross-check at N=200 and N=260.
def density(av,cv,tv,N):
 qs=[m.mpf(1)]
 for n in range(1,N+3):qs.append(m.fsum((av*k/(k+1)+cv)*qs[n-k] for k in range(1,n+1))/n)
 terms=[(-tv)**n/m.factorial(n) for n in range(N+1)]
 return tuple(m.exp(av)*m.fsum(terms[n]*(-1)**j*qs[n+j+1] for n in range(N+1)) for j in range(2))
rows=[]
for ds in ['0.01','0.0001','0.000001']:
 d=m.mpf(ds);L=m.log(1/d);guess=L+3*m.log(L)
 ar,tr=m.findroot(lambda av,tv:density(av,1-d,tv,200),(d*guess/2,guess),tol=m.mpf('1e-50'),maxsteps=40)
 f=density(ar,1-d,tr,260)
 rows.append({'delta':ds,'a':m.nstr(ar,35),'t':m.nstr(tr,35),'2a/(delta*log(1/delta))':m.nstr(2*ar/d/L,20),'t-L-3logL':m.nstr(tr-L-3*m.log(L),20),'residual_N260':[m.nstr(x,6) for x in f], 'warning':'Unvalidated floating-point tangency; neither global positivity nor boundary identification certified'})
(P/'checks.json').write_text(json.dumps({'exact_checks':checks,'diagnostics':rows,'seed':None,'randomness':'none','RSS_limit_MiB':512,'ordinary_result_complete':False},indent=2)+'\n')
print((P/'checks.json').read_text())
