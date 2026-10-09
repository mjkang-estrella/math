"""Floating, deterministic three-site test; explicitly not a certified counterexample search."""
from pathlib import Path
import json, math

ROOT=Path(__file__).resolve().parents[3]
OUT=ROOT/'frontier/experiments/i33_density_robust_brenier'

def solve(a,t,n):
 kap=.5
 ys=[-1+2*i/n for i in range(n+1)]
 ws=[(1 if i in (0,n) else 4 if i%2 else 2)*2/(3*n) for i in range(n+1)]
 def primitive(x,y):return (x+kap*y*a*math.log(a*a+x*x))/4
 def f(x,y):return (1+kap*y*2*a*x/(a*a+x*x))/4
 def masses(A,z,deriv=False):
  vals=[0.]*6
  for y,w in zip(ys,ws):
   width=max(A+t*y,0.);l=max(-1.,min(1.,z-width));r=max(-1.,min(1.,z+width))
   vals[0]+=w*(primitive(l,y)-primitive(-1,y));vals[1]+=w*(primitive(1,y)-primitive(r,y))
   if deriv:
    fl=f(l,y) if -1<l<1 else 0.;fr=f(r,y) if -1<r<1 else 0.;active=width>0
    vals[2]-=w*fl*active;vals[3]+=w*fl;vals[4]-=w*fr*active;vals[5]-=w*fr
  return vals
 A,z=a,0.
 target=(1-a)/2
 for it in range(80):
  ml,mr,aa,az,ra,rz=masses(A,z,True);e1,e2=ml-target,mr-target
  err=max(abs(e1),abs(e2))
  if err<2e-13:break
  det=aa*rz-az*ra
  assert abs(det)>1e-16
  dA=(-e1*rz+az*e2)/det;dz=(-aa*e2+e1*ra)/det
  rate=1.
  for _ in range(30):
   vals=masses(A+rate*dA,z+rate*dz)
   if max(abs(vals[0]-target),abs(vals[1]-target))<err:break
   rate/=2
  A+=rate*dA;z+=rate*dz
 else:raise AssertionError('Newton did not converge')
 E=0.
 oldvals=[(-1.,0.),(0.,0.),(1.,0.)];newvals=[(-1.,0.),(0.,t),(1.,0.)]
 for y,w in zip(ys,ws):
  width=max(A+t*y,0.);l=max(-1.,min(1.,z-width));r=max(-1.,min(1.,z+width))
  old=[(-1.,-a),(-a,a),(a,1.)];new=[(-1.,l),(l,r),(r,1.)]
  for i,(lo,hi) in enumerate(old):
   for j,(ll,rr) in enumerate(new):
    low,high=max(lo,ll),min(hi,rr)
    if high>low:
     dist=sum((u-v)**2 for u,v in zip(oldvals[i],newvals[j]))
     E+=w*dist*(primitive(high,y)-primitive(low,y))
 return {'a':a,'t':t,'grid':n,'A':A,'z':z,'mass_residual':err,'squared_map_error':E,'W2_squared':a*t*t,'D6_over_W2_squared':E**3/(a*t*t),'iterations':it+1}

def run():
 rows=[]
 for a in (1/16,1/64,1/256):
  for ratio in (1/16,1/4,1,4,16):
   t=min(a*ratio,.5)
   low,high=solve(a,t,256),solve(a,t,512)
   high['coarse_grid_error_difference']=abs(low['squared_map_error']-high['squared_map_error'])
   rows.append(high)
 result={'scope':'floating Simpson quadrature and Newton solves; no rigorous error certificate; law masses approximated','cases':rows,'summary':{'cases':len(rows),'max_residual':max(r['mass_residual'] for r in rows),'max_grid_difference':max(r['coarse_grid_error_difference'] for r in rows),'max_ratio':max(r['D6_over_W2_squared'] for r in rows)}}
 (OUT/'fixed-mass-search.json').write_text(json.dumps(result,indent=2)+'\n')
 print(json.dumps(result['summary'],sort_keys=True))
if __name__=='__main__':run()
