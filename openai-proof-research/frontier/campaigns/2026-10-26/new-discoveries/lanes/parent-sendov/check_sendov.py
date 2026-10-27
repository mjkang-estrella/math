#!/usr/bin/env python3
from pathlib import Path
import json
import sympy as S
import mpmath as m
m.mp.dps=70
rho=S.Rational(9,10);s=S.Rational(3,4);z,u,q=S.symbols('z u q')
P=(z-rho)*(z-rho*s*u)*(z+rho*s*u)
D=S.diff(P,z)
assert S.expand(D-(3*z*z-2*rho*z-rho*rho*s*s*u*u))==0
B=[rho*(1+q)/3,rho*(1-q)/3]
assert S.rem(S.expand(D-3*(z-B[0])*(z-B[1])),q*q-1-S.Rational(27,16)*u*u,q)==0
assert S.Rational(43,16)<4
assert S.Rational(43,16)>S.Rational(3,2)**2
R=m.mpf(9)/10;ss=m.mpf(3)/4
mxroots=m.mpf(0);mxcrit=m.mpf(0);mxalg=m.mpf(0);mxweights=m.mpf(0);minweight=m.inf
ends=[]
for k in range(401):
 t=m.mpf(k)/400;U=m.exp(m.pi*1j*t)
 H=1+m.mpf(16)/27*m.conj(U)**2
 assert H.real>=m.mpf(11)/27-m.mpf('1e-65')
 Q=3*m.sqrt(3)/4*U*m.sqrt(H)
 roots=[R,R*ss*U,-R*ss*U]
 bs=[R/3*(1+Q),R/3*(1-Q)]
 mxroots=max(mxroots,*map(abs,roots));mxcrit=max(mxcrit,*map(abs,bs))
 mxalg=max(mxalg,abs(Q**2-(1+m.mpf(27)/16*U**2)))
 for b in bs:
  deleted=sum((b-roots[(j+1)%3])*(b-roots[(j+2)%3]) for j in range(3))
  mxalg=max(mxalg,abs(deleted))
  weights=[1/abs(b-a)**2 for a in roots];total=sum(weights);weights=[w/total for w in weights]
  mxweights=max(mxweights,abs(b-sum(w*a for w,a in zip(weights,roots))))
  minweight=min(minweight,*weights)
 if k in [0,400]:ends.append([str(abs(R-b)) for b in bs])
assert mxroots<1 and mxcrit<1 and mxalg<m.mpf('1e-60') and mxweights<m.mpf('1e-60')
assert m.mpf(ends[0][1])>m.mpf(21)/20 and m.mpf(ends[1][0])>m.mpf(21)/20
out={'status':'PASS','qualification':'Exact symbolic identities plus high-precision path checks; connectedness proof is in PROOF.md, not replaced by samples','samples':401,'precision_digits':70,'max_root_norm':str(mxroots),'max_critical_norm':str(mxcrit),'max_algebra_residual':str(mxalg),'max_convex_weight_residual':str(mxweights),'min_positive_weight':str(minweight),'critical_distances_from_a0_at_endpoints':ends,'symbolic_derivative':str(D),'exact_bad_endpoint_distance':'3/5+3*sqrt(43)/40','strict_verified_rational_lower_bound':'21/20'}
Path('check-result.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
