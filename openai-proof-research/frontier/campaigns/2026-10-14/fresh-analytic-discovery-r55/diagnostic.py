#!/usr/bin/env python3
# MIT. Exact scalar diagnostics only; no Ricci-flow existence or extension proof.
from fractions import Fraction as Q
# With q=|x|^2 and u=a^2+t, v_t/v=-2/u+q/(4u^2),
# while (4q v_qq+2n v_q)/v=-n/(2u)+q/(4u^2).
for u in [Q(1,7),Q(1),Q(13,2)]:
    temporal=(-2/u,1/(4*u*u))
    lap4=(-Q(4)/(2*u),1/(4*u*u))
    lap3=(-Q(3)/(2*u),1/(4*u*u))
    assert temporal==lap4
    assert temporal!=lap3 # wrong-dimension control
for m in range(2,51):
    ell=Q(1,m*m);H=Q(m**3);clock=ell**2
    l1=H*clock;l2=H*H*clock/Q(3)
    assert l1==Q(1,m) and l2==Q(m*m,3)
    assert H<=ell**-2
    assert H/clock<=ell**-4
    assert l2>=Q(4,3) # rejects purported vanishing-L2 inference
# D=1-J/2 has D'=-S_v/2. Extra reaction =v S_v/(2 D^2).
for D,V,S in [(Q(3,4),Q(2),Q(3)),(Q(1,2),Q(1,7),Q(1,2))]:
    reaction=V*S/(2*D**2)
    assert reaction==(V/D)*(S/D)/2
    assert -reaction!=(V/D)*(S/D)/2 # wrong denominator sign
print('PASS_SCALAR_DIAGNOSTICS_ONLY: heat coefficients; wrong dimension/sign controls; 49 rational scales')
