"""Independent-algorithm diagnostics, never substituted for the written proof."""
from pathlib import Path
import json
import sympy as S
import mpmath as mp

ROOT = Path(__file__).resolve().parent
mp.mp.dps = 55
t,p=S.symbols('t p',positive=True)
u=t/(1-t*t)
H=S.log(u)-(u*t+S.log(1-t*t)/2)/p
expected=(1+t*t)*(p-(p+1)*t*t)/(p*t*(1-t*t)**2)
assert S.simplify(S.diff(H,t)-expected)==0


def psi(u):
    tt=2*u/(1+mp.sqrt(1+4*u*u))
    return u*tt+mp.log1p(-tt*tt)/2


def logZ(n,r):
    if r==0:
        return mp.mpf(0)
    v=mp.mpf(n)/2
    return mp.loggamma(v+1)+v*mp.log(2/r)+mp.log(mp.besseli(v,r))


out={'symbolic_derivative_identity':'PASS','uniform_bounds':[], 'asymptotic_diagnostics':[]}
for n in [3,6,21,51]:
    d=n-1
    c=mp.gamma(mp.mpf(n)/2+1)/(mp.sqrt(mp.pi)*mp.gamma(mp.mpf(n+1)/2))
    assert mp.mpf(1)/2<=c<=d
    for uu in ['0','0.01','0.1','1','3','10','100']:
        uu=mp.mpf(uu)
        zz=logZ(n,d*uu)
        lower=mp.log(c)-mp.log(4*d*(1+uu))+d*psi(uu)
        upper=mp.log(2*c)+d*psi(uu)
        assert lower<=zz<=upper
        out['uniform_bounds'].append(dict(n=n,u=str(uu),lower_margin=str(zz-lower),upper_margin=str(upper-zz)))

for pp in ['0.5','1','2','5']:
    pp=mp.mpf(pp)
    star=mp.sqrt(pp*(1+pp))
    hp=mp.log(pp)/2+(1+1/pp)*mp.log1p(pp)/2-1
    assert abs(psi(star)-(pp-mp.log1p(pp)/2))<mp.mpf('1e-50')
    for n in [10,30,80]:
        d=n-1
        integrand=lambda u:mp.exp(d*mp.log(u)-logZ(n,d*u)/pp-d*hp) if u else mp.mpf(0)
        q=mp.quad(integrand,[0,star/2,star,2*star,4*star,mp.inf])
        logF=(mp.loggamma(mp.mpf(n)/2+1)+mp.mpf(n)/2*mp.log(2))/pp+n*mp.log(d)+d*hp+mp.log(q)
        headline=n*((1+1/(2*pp))*mp.log(n)-1/(2*pp)+hp)
        out['asymptotic_diagnostics'].append(dict(p=str(pp),n=n,log_error=str(logF-headline),
            error_over_log_n=str((logF-headline)/mp.log(n)),per_dimension_log_error=str((logF-headline)/n)))
(ROOT/'checks.json').write_text(json.dumps(out,indent=2)+'\n')
print('symbolic identity PASS;',len(out['uniform_bounds']),'uniform checks;',len(out['asymptotic_diagnostics']),'asymptotic diagnostics')
for row in out['asymptotic_diagnostics']:
    print(row['p'],row['n'],row['per_dimension_log_error'][:16])
