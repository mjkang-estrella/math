import sympy as s,json
from pathlib import Path
P=Path(__file__).parent
z,c=s.symbols('z c',positive=True)
D=s.sqrt(1+z-z*c*c); u=s.sqrt(1-c*c); A=s.atan(s.sqrt(1+z)*u/c)
f=z*c+D-1;g=2*s.sqrt(z*(1+z))*c+s.sqrt(z)*u*A
fz=s.diff(f,z); fc=s.diff(f,c); fcc=s.diff(f,c,2)
gz=s.diff(g,z);gc=s.diff(g,c);gcc=s.diff(g,c,2)
expr={k:s.simplify(v) for k,v in {'f_z':fz,'f_c':fc,'f_cc':fcc,'g_z':gz,'g_c':gc,'g_cc':gcc,'asymmetry_H':gcc-gz*fcc/fz,'stationarity_J':gc*fz-gz*fc}.items()}
(P/'drum-identities.txt').write_text('\n\n'.join(k+' = '+str(v) for k,v in expr.items()))
# Rational geometry beta=pi/4 has sqrt(1+z)*sqrt(1-c²)/c=1.
# c=4/5 => z=7/9, both are interior. H may obstruct symmetrization.
vals={k:str(v.subs({z:s.Rational(7,9),c:s.Rational(4,5)}).simplify()) for k,v in expr.items()}
(P/'drum-exact.json').write_text(json.dumps(vals,indent=2));print(json.dumps(vals,indent=2))
# exact symbolic consistency of asymmetric area-preserving second variation
# F=f(z,c+e)+f(z,c-e), F''=2 fcc; z''=-fcc/fz.
assert s.simplify(fcc+z*(1+z)/D**3)==0
assert s.simplify(expr['asymmetry_H']-(s.diff(g,c,2)-s.diff(g,z)*s.diff(f,c,2)/s.diff(f,z)))==0
print('PASS exact cap curvature and constrained second variation identities')
