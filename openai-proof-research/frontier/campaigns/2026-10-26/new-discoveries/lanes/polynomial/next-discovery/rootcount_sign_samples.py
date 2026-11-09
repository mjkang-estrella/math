from pathlib import Path
import sys,json
sys.path.insert(0,str(Path(__file__).resolve().parent))
import rootcount_scan as r
from flint import arb,arb_poly,ctx
ctx.prec=600
for k in map(int,sys.argv[1:]):
 u,v=r.polys(k); a=arb(str(r.alpha(k)));u=arb_poly(u);v=arb_poly(v)
 last=None;changes=[];indeterminate=[]
 points=sorted(set([i/2000 for i in range(1,2000)]+[1-10**(-j/20) for j in range(1,241)]+[10**(-j/20)for j in range(1,241)]))
 for x in points:
  xx=arb(str(x));f=a*u(xx)-v(xx)
  s=1 if f>0 else -1 if f<0 else 0
  if not s:indeterminate.append(x)
  elif s!=last:changes.append((x,s));last=s
 print(json.dumps({'k':k,'samples':len(points),'changes':changes,'indeterminate':indeterminate}),flush=True)
