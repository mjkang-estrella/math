#!/usr/bin/env python3
"""Independent diagnostics for the ordinary proof; never a proof by scanning."""
from pathlib import Path
import json
import sympy as sp
import numpy as np
from scipy.integrate import quad
from scipy.special import kv, kve

out={"role":"diagnostics only; full ordinary proof in PROOF.md", "credit":0}
v,n,d=sp.symbols("nu n delta", real=True)
mu=v+n
out["exact"]={
 "radicand":str(sp.expand((mu-1)**2-2*(1-n)-(mu**2-2*v-1))),
 "order_gap":str(sp.expand(v**2-(mu**2-2*v-1)-(1-n)*(2*v+n+1))),
 "chord_coefficient":str(sp.factor(((d*d+2*v+1)-(d-1)**2)/((d+1)**2-(d-1)**2)-(v+d)/(2*d))),
 "sharp_coefficient":str(sp.expand((4*mu**2-1)/8-v-sp.Rational(1,2)-(4*(mu**2-2*v-1)-1)/8)),
}
assert all(z=="0" for z in out["exact"].values())

# Choose exact zero-order boundary cases explicitly; others include negative n.
params=[(.5,1.5,0.),(-1.,4.,0.),(.875,.625,0.),(0.,2.5,.5),
        (-2.,7.,None),(.2,3.,None),(.9,2.,None),(0.,10.,None)]
rows=[]
for nn,vv,dd in params:
 mm=vv+nn
 dd=np.sqrt(mm*mm-2*vv-1) if dd is None else dd
 assert vv>dd and mm*mm>(dd+1)**2
 for x in [.2,1.,5.,20.]:
  # Exponential scaling avoids ordinary underflow; exact integration variable x+s.
  tail_scaled,err=quad(lambda s:np.exp(-s)*(x/(x+s))**vv*kve(mm,x+s),0,np.inf,
                       epsabs=1e-11,epsrel=3e-11,limit=150)
  rhs_scaled=kve(dd,x)
  deriv_gap=kve(mm,x)-kve(dd-1,x)-(vv+dd)*kve(dd,x)/x
  gap=tail_scaled-rhs_scaled
  assert gap>0 and deriv_gap>0,(nn,vv,dd,x,gap,deriv_gap)
  rows.append({"n":nn,"nu":vv,"delta":float(dd),"x":x,
               "tail_scaled_gap":float(gap),"derivative_scaled_gap":float(deriv_gap),
               "quadrature_error":float(err)})
out["source_checks"]=rows

# Three-order extrapolation with the classical recurrence, not source quadrature.
three=[]
for dd in [0.,.1,.5,1.,2.,5.]:
 for vv in [dd+.1,dd+1.,dd+4.]:
  mm=np.sqrt(dd*dd+2*vv+1)
  for x in [.3,2.,15.]:
   gap=kve(mm,x)-kve(dd-1,x)-(vv+dd)*kve(dd,x)/x
   assert gap>0
   three.append(float(gap))
out["three_order_count"]=len(three)
out["minimum_three_order_scaled_gap"]=min(three)

# Check the tangent identity by direct integration at the delicate delta=0 case.
tangent=[]
for x in [.2,1.,4.]:
 f=lambda u: np.exp(-x*(np.cosh(u)-1))*u*np.sinh(u)
 val,err=quad(f,0,12,epsabs=1e-11,epsrel=1e-11)
 residual=val-kve(0,x)/x
 assert abs(residual)<1e-8*(1+abs(val))
 tangent.append({"x":x,"scaled_residual":float(residual)})
out["tangent"]=tangent
out["status"]="PASS"
Path(__file__).with_name("checks.json").write_text(json.dumps(out,indent=2)+"\n")
print(json.dumps({"status":"PASS","exact":len(out['exact']),
                  "tail_checks":len(rows),"three_order_checks":len(three),
                  "zero_order_tangent_checks":len(tangent)}))
