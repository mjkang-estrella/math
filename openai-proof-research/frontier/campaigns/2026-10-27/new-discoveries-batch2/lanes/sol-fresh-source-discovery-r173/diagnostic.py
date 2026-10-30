import math,json
from pathlib import Path
from scipy.optimize import differential_evolution
L=Path(__file__).resolve().parent
def data(v):
 x,h,t,u=v;h=math.exp(h)
 # B=(0,0), C=(1,0), A=(x,h); P=t*A+(1-t)*(u*B+(1-u)*C)
 a=1.;b=math.hypot(x-1,h);c=math.hypot(x,h)
 ma=math.hypot(x-.5,h);mb=math.hypot((x+1)/2,h/2);mc=math.hypot(x/2-1,h/2)
 px=t*x+(1-t)*(1-u);py=t*h
 ds=[math.hypot(px-x,py-h),math.hypot(px,py),math.hypot(px-1,py)]
 rs=[py,((1-px)*h+(x-1)*py)/b,(px*h-x*py)/c]
 ratio=sum(ds)/sum(rs)
 rhs3=4*(mb+mc)/math.sqrt(9+4*h*h)
 rhs4=4*(ma*mb+mb*mc+mc*ma)/ (ma*ma+mb*mb+mc*mc+h*h+(h/b)**2+(h/c)**2)
 R=b*c/(2*h);r=h/(1+b+c)
 T=1/R+1/(2*r)
 c1=1-72*sum((T*(z+w))**-3 for z,w in [(ma,mb),(mb,mc),(mc,ma)])
 return [c1,ratio/rhs3-1,ratio/rhs4-1]
out=[]
for k in range(3):
 z=differential_evolution(lambda v:data(v)[k],[(-2,3),(-5,3),(.00001,.99999),(.00001,.99999)],seed=173+k,popsize=14,maxiter=180,tol=1e-9,polish=True,workers=1)
 out.append(dict(conjecture=[1,3,4][k],parameters=z.x.tolist(),normalized_margin=float(z.fun),diagnostic_only=True,iterations=z.nit))
(L/'diagnostics.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
