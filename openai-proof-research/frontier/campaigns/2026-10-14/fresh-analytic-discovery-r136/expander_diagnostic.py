"""Bounded floating-point ODE exploration; no certified intervals or existence proof."""
from pathlib import Path
import json,math,time
R=Path(__file__).resolve().parent
d=.400682721856639
B=751/4;C=-1215/4

def origin(k):
 a=[d,k];inv=[1/(1+d),-k/(1+d)**2]
 for i in range(2,40):
  a.append(-(inv[i-2]-(1 if i==2 else 0))/((27/8)*(i-1)*(i+9)*(i+10)))
  inv.append(-sum(a[j]*inv[i-j] for j in range(1,i+1))/(1+d))
 # start s=1; the source's majorant is not asserted for these expanding coefficients.
 return [sum(a),sum(1.5*i*a[i] for i in range(1,len(a))),sum(1.5*i*(1.5*i-1)*a[i] for i in range(1,len(a)))]
def rhs(s,y):
 p,v,w=y
 return [v,w,-30/s*w-B/s**2*v-C/s**3*(p-d)+p/(1+p)]
def run(k,step=.005,end=20):
 y=origin(k);s=1.;mn=y[0];mx=y[0]
 steps=round((end-1)/step);h=(end-1)/steps
 for _ in range(steps):
  if y[0]<=-.95 or y[0]>=5 or not all(math.isfinite(q) for q in y):
   return {'k':k,'terminal':s,'p':y[0],'score':-1e8 if y[0]<0 else 1e8,'min_p':mn,'max_p':mx,'complete':False}
  a=rhs(s,y);b=rhs(s+h/2,[y[i]+h*a[i]/2 for i in range(3)]);cc=rhs(s+h/2,[y[i]+h*b[i]/2 for i in range(3)]);dd=rhs(s+h,[y[i]+h*cc[i] for i in range(3)])
  y=[y[i]+h*(a[i]+2*b[i]+2*cc[i]+dd[i])/6 for i in range(3)];s+=h;mn=min(mn,y[0]);mx=max(mx,y[0])
 # asymptotic particular p~(1215/4)*d/s^3; projected unstable jet
 t=(1215/4)*d
 target=t*(s**-3-3*s**-4+12*s**-5)
 return dict(k=k,terminal=s,p=y[0],dp=y[1],ddp=y[2],score=sum(y)-target,min_p=mn,max_p=mx,complete=True)
start=time.monotonic()
scan=[run(-.04*i) for i in range(11)]
roots=[]
for l,r in zip(scan,scan[1:]):
 if l['score']*r['score']>=0:continue
 lo=l['k'];hi=r['k'];sl=l['score']
 for i in range(42):
  mid=(lo+hi)/2;z=run(mid)
  if z['score']*sl>0:lo=mid
  else:hi=mid
 k=(lo+hi)/2
 roots=[run(k,step=.005),run(k,step=.0025),run(k,step=.0025,end=30)]
 break
out=dict(status='FLOATING_POINT_DIAGNOSTIC_NOT_PROOF',d_central=d,c_central=1/(1+d),origin_terms=40,start_s=1,end_s=20,step=.005,scan=scan,refinements=roots,elapsed_seconds=time.monotonic()-start,limits='central cone only; truncated origin series; approximate terminal projection; no interval enclosure, positivity proof, infinite tail, inverse or compact continuation')
(R/'expander-diagnostic.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
