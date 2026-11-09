from pathlib import Path
import sympy as s
import importlib.util
H=Path(__file__).resolve().parent
x=s.symbols('x');roots=[s.Rational(-9,10),s.Rational(1,10),s.Rational(3,10),s.Rational(1,2)]
q=s.prod(x-a for a in roots).expand();cs=s.symbols('c:5');sol=s.solve(s.Poly(sum(cs[k]*s.legendre(k,x) for k in range(5))-q,x).coeffs(),cs)
print('Spherical coefficient obstruction (not a realizable code certificate)');print('roots',roots,'sum',sum(roots));print('annihilator',q);print('Legendre coefficients',sol);print('positive harmonic dimension sum',sum(2*k+1 for k in range(5) if sol[cs[k]]>0));print('target binomial',s.binomial(6,4))
# independent recurrence challenge: only small compositions, already bounded.
spec=importlib.util.spec_from_file_location('sorting',H/'sorting_diagnostic.py');m=importlib.util.module_from_spec(spec)
# Load definitions only: do not repeat full diagnostic.
exec((H/'sorting_diagnostic.py').read_text().split('out=[]\nfor n in range')[0],m.__dict__)
print('Sorting endpoint-peeling recurrence counterexamples')
found=0
for n in range(5,10):
 for a in m.parts(n):
  if len(a)==1 or len(a)==n:continue
  p=m.perm(a);v=sorted(p[1:-1]);r=[v.index(z)+1 for z in p[1:-1]]
  if m.cost(p)!=m.cost(r)+2:
   print({'composition':a,'cost':m.cost(p),'peeled':r,'peeled_cost':m.cost(r)});found+=1
   if found>=6:break
 if found>=6:break
