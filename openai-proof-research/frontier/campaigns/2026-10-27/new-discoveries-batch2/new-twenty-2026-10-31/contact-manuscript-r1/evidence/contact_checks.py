import sympy as s,pathlib,json
D=pathlib.Path(__file__).resolve().parents[1];z,w,t=s.symbols('z w t');N=(w*z-w-1)*(w*z+w-1);Q=-w*w*z**3+2*w*w*z+4*w*z*z+2*w*z-w-3*z
print('gcd=',s.gcd(N,Q))
for e in [-1,1]:print('Q at N branch',e,s.factor(Q.subs(w,1/(z+e))))
# Independent exact coefficients of the level roots via quadratic radicals at L=1,2.
rows={}
for L in [1,2,3]:
 A=L*(1-2*t*t)+t-t**3;B=-4*L-2*L*t+L*t*t-2*t;C=3*L+t;delta=s.expand(B*B-4*A*C)
 roots=[t*(-B+sg*s.sqrt(delta))/(2*A) for sg in [-1,1]]
 rows[L]=[str(s.series(r,t,0,8)) for r in roots];print(L,rows[L],flush=True)
(D/'outputs/contact-radical-checks.json').write_text(json.dumps(rows,indent=2))
