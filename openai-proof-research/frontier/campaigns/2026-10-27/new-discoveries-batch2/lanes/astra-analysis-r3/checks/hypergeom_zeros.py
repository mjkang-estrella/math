"""Exploratory zeros only; corrected primary rho=(n-2)/2."""
import mpmath as m,json
from pathlib import Path
m.mp.dps=40
out=[]
for n in [3,5,7,9,13,21]:
 rho=m.mpf(n-2)/2
 for z in [m.mpf('.2'),m.mpf('.8'),m.mpf('.99')]:
  f=lambda s:m.hyp2f1(s-rho-1,-rho,s,z)
  roots=[]
  for t in [0.5,2,5,10,20,40]:
   try:
    r=m.findroot(f,(-.2+t*1j,-.1+(t+.1)*1j),maxsteps=40,tol=m.mpf('1e-30'))
    if abs(f(r))<m.mpf('1e-25') and not any(abs(r-v)<m.mpf('1e-20') for v in roots):roots.append(r)
   except (ValueError,ZeroDivisionError):pass
  row=dict(n=n,z=str(z),roots=[str(r) for r in roots],counterexample=any(m.re(r)>0 for r in roots));out.append(row);print(row,flush=True)
Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2))
