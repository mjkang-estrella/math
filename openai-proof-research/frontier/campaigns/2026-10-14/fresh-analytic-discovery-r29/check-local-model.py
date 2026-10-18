#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
"""Exact local diagnostic only; not a global Coulomb theorem."""
import json
import sympy as S
x,z,k,d,eps=S.symbols("x z k d eps", positive=True)
s=S.sqrt(2*d)
g=eps*S.exp(-k*x)*S.cosh(s*z)
h=z*S.exp(-k*x)
v=k*k/2+d
lap=lambda f:S.diff(f,x,2)+S.diff(f,z,2)
rg=S.simplify(-lap(g)/2+v*g)
rh=S.simplify(-lap(h)/2+v*h-d*h)
assert rg==0 and rh==0
n=g*g+h*h
root=S.sqrt(n)
curv=S.simplify((lap(root)/(2*root)).subs(z,0))
theta=S.atan(h/g)
tz=S.simplify(S.diff(theta,z).subs(z,0))
assert tz==1/eps
assert S.simplify(curv-v-1/(2*eps**2))==0
assert S.simplify(curv-tz**2/2-v)==0
assert S.simplify(n.subs(z,0)-eps**2*S.exp(-2*k*x))==0
assert S.simplify(n-z*z*S.exp(-2*k*x)-eps**2*S.exp(-2*k*x)*S.cosh(s*z)**2)==0
# Two controls must FAIL the corresponding desired zero residual.
assert S.simplify(-lap(g)/2+(v-d)*g)==-d*g
assert S.simplify(curv-v)==1/(2*eps**2)
print(json.dumps({"orbital_residuals":[str(rg),str(rh)],"plane_curvature":str(curv),"plane_angle_derivative":str(tz),"positive_gap":True,"wrong_potential_detected":True,"omitted_angle_detected":True,"scope":"local exact model only; nonnormalizable"},sort_keys=True,indent=2))
