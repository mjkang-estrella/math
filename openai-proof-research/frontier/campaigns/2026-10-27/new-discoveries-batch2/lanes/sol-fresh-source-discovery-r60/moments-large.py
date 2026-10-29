from pathlib import Path
import sympy as S,json
P=Path(__file__).resolve().parent;d={'__file__':str(P/'check.py')};exec((P/'check.py').read_text().split('records=[]')[0],d)
ehr=d['ehr'];heights=d['heights'];size=d['size'];x=d['x'];randtree=d['randtree']
def interp(v):
 f=S.Poly(0,x,domain=S.QQ);b=S.Poly(1,x,domain=S.QQ)
 for k in range(len(v)):
  f+=b.mul_ground(v[0]);v=[v[i+1]-v[i] for i in range(len(v)-1)];b=b*S.Poly(x-k,x,domain=S.QQ).mul_ground(S.Rational(1,k+1))
 return f
out=[]
for n in range(13,25):
 for z in range(3):
  t=randtree(n);e=ehr(t);m=interp([sum(i*a for i,a in enumerate(heights(t,k))) for k in range(n+2)])
  # Reduce common polynomial factors; assess residues at each remaining real pole.
  g=S.gcd(e,m);a=m.exquo(g);b=e.exquo(g);assert b.gcd(b.diff()).degree()==0
  vals=[];bad=False
  for (lo,hi),mult in b.intervals(eps=S.Rational(1,10**14)):
   # signs stable if no zero of a*b' on bracket; endpoints rational exact.
   h=a*b.diff()
   if lo==hi:sg=S.sign(h.eval(lo))
   else:
    assert h.count_roots(lo,hi)==0
    sg=S.sign(h.eval(lo))
   vals.append(int(sg));bad|=sg<0
  row=dict(tree=t,dimension=n,E=str(e.as_expr()),M=str(m.as_expr()),residue_signs=vals,bad=bool(bad));out.append(row)
  (P/'moments-large-replay.json').write_text(json.dumps(out,indent=2))
  if bad:print('NEGATIVE_RESIDUE',json.dumps(row));raise SystemExit(0)
print('ALL_NONNEGATIVE',len(out))
