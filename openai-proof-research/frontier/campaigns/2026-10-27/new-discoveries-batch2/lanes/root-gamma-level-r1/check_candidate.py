#!/usr/bin/env python3
"""Own symbolic checks and high-precision diagnostics, never a proof certificate."""
import json
from pathlib import Path
import mpmath as mp
import sympy as sp

u, s, x, m = sp.symbols('u s x m', positive=True)
g = -sp.log(1-u**-2)
assert sp.simplify(sp.diff(g,u) + 2/(u*(u**2-1))) == 0
assert sp.simplify(sp.diff(g,u,2) - 2*(3*u**2-1)/(u**2*(u**2-1)**2)) == 0
# Algebraic factor underlying Euler's cancelled product.
assert sp.simplify((s+m)**2/((s-x+m)*(s+x+m)) - 1/(1-x**2/(s+m)**2)) == 0

mp.mp.dps = 70
def F(x, s):
    return mp.loggamma(s-x)+mp.loggamma(s+x)-2*mp.loggamma(s)
def rho(s, c):
    lo, hi = mp.mpf(0), s
    for _ in range(300):
        mid = (lo+hi)/2
        if F(mid,s) < mp.log(c): lo = mid
        else: hi = mid
    return (lo+hi)/2

pairs = [('0.0001','0.001'),('0.01','0.7'),('0.2','2'),('1','30'),('10','200')]
rows=[]
lam=mp.mpf('0.37')
for cs in ['1.01','1.2','2','5','100']:
    c=mp.mpf(cs)
    for aa,bb in pairs:
        a,b=mp.mpf(aa),mp.mpf(bb)
        ra,rb=rho(a,c),rho(b,c)
        margin=rho(lam*a+(1-lam)*b,c)-lam*ra-(1-lam)*rb
        assert margin>0
        rows.append({'c':cs,'s0':aa,'s1':bb,'concavity_margin':mp.nstr(margin,55)})

result={'symbolic_checks':3,'diagnostic_checks':len(rows),'precision_decimal_digits':mp.mp.dps,
        'status':'PASS diagnostics; no interval certification or formal proof', 'rows':rows}
Path(__file__).with_name('reproducible-checks.json').write_text(json.dumps(result,indent=2)+'\n')
print('PASS: 3 exact symbolic checks; 25 numerical diagnostics (not a proof)')
