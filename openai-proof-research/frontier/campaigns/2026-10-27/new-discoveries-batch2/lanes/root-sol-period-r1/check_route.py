#!/usr/bin/env python3
"""Diagnostics only: independent real period quadrature vs Gamma transform inversion."""
import json
from pathlib import Path
import mpmath as m

m.mp.dps = 45

def U(a,t):
    return m.log((a*m.exp(2*t)+m.exp(-2*a*t))/(a+1))

def Up(a,t):
    return 2*a*(m.exp(2*t)-m.exp(-2*a*t))/(a*m.exp(2*t)+m.exp(-2*a*t))

def turning(a,h,sgn):
    lo,hi=m.mpf(0),m.mpf(1)
    while U(a,sgn*hi)<h: hi*=2
    for _ in range(220):
        mid=(lo+hi)/2
        if U(a,sgn*mid)<h:lo=mid
        else:hi=mid
    return sgn*(lo+hi)/2

def period(a,h):
    left,right=turning(a,h,-1),turning(a,h,1)
    r,mid=(right-left)/2,(right+left)/2
    def f(theta):
        if abs(theta+m.pi/2)<m.mpf('1e-18'):
            return 2*m.sqrt(2*r/(-Up(a,left)))
        if abs(theta-m.pi/2)<m.mpf('1e-18'):
            return 2*m.sqrt(2*r/Up(a,right))
        t=mid+r*m.sin(theta)
        return 2*r*m.cos(theta)/m.sqrt(-m.expm1(U(a,t)-h))
    return m.quad(f,[-m.pi/2,0,m.pi/2])

def lap(a,s):
    q=a/(1+a);r=1/(1+a);c=(1+a)/a**q
    return m.sqrt(m.pi)/(1+a)*c**s*m.gamma(q*s)*m.gamma(r*s)/m.gamma(s+m.mpf('.5'))

def kernel(t):
    if abs(t)<m.mpf('1e-5'):
        return t/12-t**3/720+t**5/30240-t**7/1209600
    return 1/m.expm1(t)-1/t+m.mpf('.5')

rows=[]
for astr in ['.1','.37','1','2.5']:
    a=m.mpf(astr);q=a/(1+a);r=1/(1+a)
    for hstr in ['.3','1','3']:
        h=m.mpf(hstr)
        p=period(a,h)
        inv=m.invertlaplace(lambda s:lap(a,s),h,method='dehoog')
        err=abs(p-inv)
        assert err<m.mpf('1e-22'),(a,h,p,inv,err)
        rows.append({'alpha':astr,'h':hstr,'period':m.nstr(p,32),'transform_inverse':m.nstr(inv,32),'error':m.nstr(err,8)})
    for sstr in ['.2','1','5']:
        s=m.mpf(sstr)
        nu=lambda t:(kernel(t/q)+kernel(t/r)+kernel(t)-kernel(t/2))/t
        logrep=m.quad(lambda t:m.exp(-s*t)*nu(t),[0,1,m.inf])
        target=m.log(s*lap(a,s)/(m.pi*m.sqrt(2/a)))
        assert abs(logrep-target)<m.mpf('1e-30'),(a,s,logrep,target)
    assert min((kernel(t/q)+kernel(t/r)+kernel(t)-kernel(t/2))/t
        for t in map(m.mpf,['.0001','.01','.1','1','10','100']))>0

out={'status':'PASS diagnostics only; no interval certificates or Lean claim',
     'period_and_inverse_transform_cases':rows,
     'binet_identity_cases':12,'positive_kernel_grid_cases':24}
Path(__file__).with_name('checks.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({'status':out['status'],'period_cases':len(rows),'binet_cases':12}))
