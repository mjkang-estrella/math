from pathlib import Path
import sympy as S,json,random,time
L=Path(__file__).resolve().parents[1];x=S.Symbol('x');rng=random.Random(219);out=[];start=time.monotonic()
for n in [2,4,6,8]:
 for trial in range(6):
  roots=sorted(rng.choices(range(-3,4),k=n-1));g=S.prod(x-r for r in roots);base=S.integrate(g,x);c=1-min(base.subs(x,r) for r in roots);p=base+c
  ks=[-1,0,S.Rational(1,4),S.Rational(1,2),S.Rational(n-1,n),S.Rational(n-1,n)+S.Rational(1,20),1,2]
  for k in ks:
   f=S.Poly(S.expand(p*S.diff(p,x,2)-k*S.diff(p,x)**2),x)
   z=sum(m*S.Poly(q,x).count_roots(-S.oo,S.oo) for q,m in S.sqf_list(f)[1])
   ok=(z==n if k>S.Rational(n-1,n) else (n-2<=z<=n if k>S.Rational(1,2) else z==n-2))
   out.append({'n':n,'derivative_roots':roots,'p':str(p),'k':str(k),'real_zeros_with_multiplicity':int(z),'conjecture_agrees':bool(ok)})
(L/'check-results.json').write_text(json.dumps({'cases':out,'all_agree':all(r['conjecture_agrees'] for r in out),'seconds':time.monotonic()-start,'scope':'Finite exact Sturm checks only; no universal proof.'},indent=2))
print(len(out),all(r['conjecture_agrees'] for r in out),time.monotonic()-start)
