# Exact check in Q(zeta)[t]: Tr prod_{k<e} [[1+z,-z(1-t z^k)],[1-t z^k,0]] == 2 + q_e t^e  (mod Phi_e(z)),
# and det of the period product == (1-t^e)^2 (mod Phi_e(z)).
import sympy as sp, json, sys
z,t=sp.symbols('z t')
out=[]
for e in range(1,int(sys.argv[1])+1):
    Phi=sp.cyclotomic_poly(e,z)
    red=lambda ex: sp.expand(sp.rem(sp.expand(ex),Phi,z))
    P=sp.eye(2)
    for k in range(e):
        g=1-t*z**k
        P=(P*sp.Matrix([[1+z,-z*g],[g,0]])).applyfunc(red)
    tr=red(P.trace()); dt=red(P.det())
    qe=0 if e%2 else (2 if e%4==0 else -2)
    out.append({'e':e,'trace_ok':sp.simplify(tr-(2+qe*t**e))==0,'det_ok':sp.simplify(red(dt-(1-t**e)**2))==0,'trace':str(tr)})
print(json.dumps(out))
