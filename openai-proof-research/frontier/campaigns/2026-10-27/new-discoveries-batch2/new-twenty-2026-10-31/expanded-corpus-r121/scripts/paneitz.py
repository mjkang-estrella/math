from decimal import Decimal,localcontext
import json
with localcontext() as ctx:
 ctx.prec=1100
 def cs(t):e=t.exp();f=(-t).exp();return (e+f)/2,(e-f)/2
 for al in ['0.01','0.1','0.5']:
  alpha=Decimal(al);beta=alpha*(1-alpha)
  for ts in ['0.0001','0.001','0.01','0.1','0.5','1','2','5','10']:
   t=Decimal(ts);c0,s0=cs(2*t);last=None;bad=[]
   for l in range(1,101):
    C,S=cs((2*l+2)*t);a=-2*l*(l+2)+2*(l+1)**2*c0-2*C
    b=4*l*(l+1)*(l+2)*((l+1)*s0+S)/beta
    c=-8*l*l*(l+1)**2*(l+2)**2*(C-c0)/beta
    disc=b*b-4*a*c
    v=-2*c/(b+disc.sqrt())
    if last is not None and v<=last:bad.append(l)
    last=v
   print(json.dumps(dict(alpha=al,tau=ts,ell_range=[1,100],decimal_precision=1100,nonincreasing_steps=bad,certified=False)),flush=True)
