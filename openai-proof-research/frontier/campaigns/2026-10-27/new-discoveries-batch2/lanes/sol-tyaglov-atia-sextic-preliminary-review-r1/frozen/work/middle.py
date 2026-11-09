from pathlib import Path
import sympy as S,random,json,time
L=Path(__file__).resolve().parents[1];x=S.Symbol('x');rng=random.Random(21901);out=[];start=time.monotonic()
for n in [6,8]:
 for trial in range(90):
  roots=sorted(rng.sample(range(-20,21),n-1));g=S.prod(x-r for r in roots);base=S.integrate(g,x);c=S.Rational(1,10**(trial%4))-min(base.subs(x,r) for r in roots);p=base+c
  for k in [S.Rational(2,3),S.Rational(3,4),S.Rational(4,5)]:
   f=S.Poly(S.expand(p*S.diff(p,x,2)-k*S.diff(p,x)**2),x)
   z=sum(m*S.Poly(q,x).count_roots(-S.oo,S.oo) for q,m in S.sqf_list(f)[1]);ok=n-2<=z<=n
   row={'n':n,'derivative_roots':roots,'p':str(p),'k':str(k),'real_zeros_with_multiplicity':int(z),'conjecture_agrees':bool(ok)};out.append(row)
   if not ok:
    (L/'middle-results.json').write_text(json.dumps({'cases':out,'counterexample':row,'seconds':time.monotonic()-start},indent=2));print(row);raise SystemExit()
(L/'middle-results.json').write_text(json.dumps({'cases':out,'counterexample':None,'seconds':time.monotonic()-start},indent=2));print(len(out),'no counterexample',time.monotonic()-start)
