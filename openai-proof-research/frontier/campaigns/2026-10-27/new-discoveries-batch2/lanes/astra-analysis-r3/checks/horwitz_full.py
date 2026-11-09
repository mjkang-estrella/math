"""Exploration, not proof. Independent divided differences vs gap formulas."""
import mpmath as m, json, random
from pathlib import Path
m.mp.dps=110

def dd(v,f):
 return sum(f(x)/m.fprod(x-y for j,y in enumerate(v) if j!=i) for i,x in enumerate(v))
def calc(p,q):
 a,b,c=m.exp(-p),m.mpf(1),m.exp(q)
 x=-m.expm1(-p)/p;z=m.expm1(q)/q;s=p+q;y=(p*x+q*z)/s;d=z-x
 old0=d/(x*z*s*y);old1=1/y-old0
 j0=s*m.log(y)-p*m.log(x)-q*m.log(z)
 j1=p*x*m.log(x)+q*z*m.log(z)-s*y*m.log(y)
 new0=s*j0/(p*q*d*d);new1=s*j1/(p*q*d*d)
 vals=(old0,new0,old1,new1)
 direct=(-dd((a,b,c),m.log),-dd((x,y,z),m.log),dd((a,b,c),lambda t:t*m.log(t)),dd((x,y,z),lambda t:t*m.log(t)))
 err=max(abs(u/v-1) for u,v in zip(vals,direct))
 return (old0-new0)/old0,(new1-old1)/old1,err

ps=[m.mpf(10)**k for k in range(-8,4)] + [m.mpf(2),m.mpf(3),m.mpf(30),m.mpf(300)]
res=[];worsterr=m.mpf(0)
for p in ps:
 for q in ps:
  d0,d1,e=calc(p,q);worsterr=max(e,worsterr)
  res.append(dict(p=str(p),q=str(q),relative_residual0=str(d0),relative_residual1=str(d1)))
out=dict(label='NONRIGOROUS high-precision exploration only',precision=m.mp.dps,count=len(res),max_formula_relative_error=str(worsterr),negative=[r for r in res if m.mpf(r['relative_residual0'])<0 or m.mpf(r['relative_residual1'])<0],minima=[min(res,key=lambda r:m.mpf(r[k])) for k in ['relative_residual0','relative_residual1']])
Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2));print(json.dumps(out,indent=2))
