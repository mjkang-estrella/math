#!/usr/bin/env python3
"""Independent transcription diagnostics; no numerical output is a proof."""
from pathlib import Path
import json
import math
import mpmath as mp
import sympy as S
from scipy.integrate import quad
from scipy.special import beta, gamma, kv

mp.mp.dps = 55
here = Path(__file__).resolve().parent
b, m, t, c = S.symbols('b m t c', positive=True)
g = t**(2*b+m-1)*(1-t*t)**(-b-S.Rational(1,2))*(t+c)**(-m)
H = t**(2*b+m)*(1-t*t)**(S.Rational(1,2)-b)*(t+c)**(-m-1)
operator_over_g = c*(1-c*c)*m*(m+1)/(t+c)**2-(1-2*b-2*(m+1)*c*c)*m/(t+c)-m*(m+1)*c
H_over_g=t*(1-t*t)/(t+c)
log_g_t=(2*b+m-1)/t+(2*b+1)*t/(1-t*t)-m/(t+c)
ibp = S.factor(operator_over_g-m*(S.diff(H_over_g,t)+H_over_g*log_g_t))
assert ibp == 0, ibp

z = S.symbols('z')
Y = S.Function('Y')
# Independent chain-rule comparison of the c-ODE with the z Gauss equation.
yp = -2*c*Y(z).diff(z)
ypp = -2*Y(z).diff(z)+4*c*c*Y(z).diff(z,2)
ode = c*(1-c*c)*ypp+(1-2*b-2*(m+1)*c*c)*yp-m*(m+1)*c*Y(z)
gauss = z*(1-z)*Y(z).diff(z,2)+(b+m+S.Rational(1,2)-(m+S.Rational(3,2))*z)*Y(z).diff(z)-m*(m+1)*Y(z)/4
ode_res = S.expand(ode/(4*c)-gauss).subs(c*c,1-z).expand()
assert ode_res == 0, ode_res

def beta_expect(f, a, q):
    """Split at 1/2 and remove endpoint powers analytically."""
    a,q = mp.mpf(a),mp.mpf(q)
    half = mp.mpf('.5')
    lo = half**a/a*mp.quad(lambda r: f(half*r**(1/a))*(1-half*r**(1/a))**(q-1),[0,1])
    hi = half**q/q*mp.quad(lambda r: f(1-half*r**(1/q))*(1-half*r**(1/q))**(a-1),[0,1])
    return (lo+hi)/mp.beta(a,q)

moments=[]
for bs in ['.1','.25','.4']:
    bb=mp.mpf(bs)
    for us in ['.1','.25','.5']:
        u=mp.mpf(us); cc=2*mp.sqrt(u*(1-u))
        for mm in [1,2,3,7,20]:
            lhs=mp.rf(2*bb,mm)*beta_expect(lambda v: (v*(1-v)/(u+(1-2*u)*v))**mm,bb,bb)
            rhs=mp.rf(bb,mm)*beta_expect(lambda w: (mp.sqrt(w)/(mp.sqrt(w)+cc))**mm,bb,mp.mpf('.5')-bb)
            series=mp.rf(2*bb,mm)*mp.rf(bb,mm)/(2**mm*mp.rf(bb+mp.mpf('.5'),mm))*mp.hyp2f1(mp.mpf(mm)/2,mp.mpf(mm+1)/2,bb+mm+mp.mpf('.5'),1-cc*cc)
            err=max(abs(lhs-rhs),abs(lhs-series))/max(abs(lhs),abs(rhs))
            assert err < mp.mpf('1e-45'), (bs,us,mm,err)
            moments.append({'b':bs,'u':us,'m':mm,'relative_error':str(err)})

def beta_expect_float(f,a,q):
    lo=.5**a/a*quad(lambda r:f(.5*r**(1/a))*(1-.5*r**(1/a))**(q-1),0,1,epsabs=2e-12,epsrel=2e-12,limit=200)[0]
    hi=.5**q/q*quad(lambda r:f(1-.5*r**(1/q))*(1-.5*r**(1/q))**(a-1),0,1,epsabs=2e-12,epsrel=2e-12,limit=200)[0]
    return (lo+hi)/beta(a,q)

laplace=[]
for bb in [.1,.25,.4]:
    def f(s):
        return 2*s**(bb/2)*kv(bb,2*math.sqrt(s))/gamma(bb) if s>0 else 1.
    for u in [.1,.25,.5]:
        cc=2*math.sqrt(u*(1-u))
        for lam in [.1,1.,10.]:
            lhs=f(lam*u)*f(lam*(1-u))
            rhs=beta_expect_float(lambda w:f(lam*(1+cc/math.sqrt(w))) if w else 0.,bb,.5-bb)
            rel=abs(lhs-rhs)/lhs
            assert rel < 2e-9,(bb,u,lam,rel)
            laplace.append({'b':bb,'u':u,'lambda':lam,'relative_error':rel})

result={'status':'PASS diagnostics only','symbolic':{'IBP_identity':str(ibp),'Gauss_ODE_transform':str(ode_res)},'inverse_moments':moments,'Laplace_Bessel_diagnostics':laplace,'credit':0,'full_lean_endpoint':False}
(here/'checks.json').write_text(json.dumps(result,indent=2)+'\n')
print('PASS: 2 exact symbolic identities,',len(moments),'high-precision inverse moments,',len(laplace),'independent Laplace checks')
