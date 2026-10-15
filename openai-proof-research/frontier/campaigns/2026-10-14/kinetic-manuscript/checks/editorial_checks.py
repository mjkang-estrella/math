"""Exact finite controls for editorial interfaces; not the analytic theorem.
Copyright (c) 2026 Myeongjin Kang. MIT License; see ../LICENSE-code.txt.
"""
from fractions import Fraction as F
from pathlib import Path
import json
checks={}
def ck(name,truth):
    if not truth: raise AssertionError(name)
    checks[name]=True
# A redundant O-update leaves r(t)=d+u*t unchanged. Its next entering root
# is a structural tie, including after any common rational time shift.
d,u,diam=F(3),F(-2),F(1)
t=(diam-d)/u
ck('O_root_is_entering',t==1 and u<0)
for shift in (F(-7),F(-1,3),F(0),F(5,2)):
    ds=d-shift*u
    root=(diam-ds)/u
    repeated=(diam-ds)/u
    assert root==t+shift==repeated
    assert repeated>=root # forward ray permits equality
    assert not repeated>root # strict global chronology rejects it
ck('structural_O_tie_rejected_by_strict_Q',True)
ck('structural_O_tie_shift_invariant',True)
# Compare coefficients of x^3 = (x)_3 + 3(x)_2 + x, in Q[x].
f3=[F(0),F(2),F(-3),F(1)]
f2=[F(0),F(-1),F(1),F(0)]
f1=[F(0),F(1),F(0),F(0)]
ck('Count_cubic_polynomial_coefficients',[f3[i]+3*f2[i]+f1[i] for i in range(4)]==[0,0,0,1])
for k in range(1,25):
    mu=F(k*k); alpha=F(1,k**3); err=F(1,k**17)
    lhs=F(1,1)/alpha*(mu*alpha+err)/(k**3)
    assert lhs==F(1,k)+err
ck('aligned_actual_Count_error_union',True)
# The weaker convention in the old proof remains a transparent upper bound.
ck('aligned_error_implies_old_upper_bound',all(F(1,k**17)<=F(k**6,k**17) for k in range(1,25)))
for P in (F(1),F(3),F(8),F(32)):
    for E in (P/2,F(3,4)*P,P):
        assert F(3,4)*E>=E/4+P/4
ck('fixed_Gaussian_reserve_exponent',True)
ck('common_error_power_six_suffices',F(7)-6>0)
result={'status':'PASS','count':len(checks),'arithmetic':'exact rational arithmetic and polynomial coefficient identities','checks':checks,'scope':'Finite support only: O structural tie, Count diagonals, aligned errors, Gaussian and exponent arithmetic; not a proof of W or path convergence.'}
Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
