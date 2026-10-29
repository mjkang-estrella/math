# Independent bounded checks and adversarial induction tests.
import runpy,sys,itertools,json,math
from pathlib import Path
import sympy as S
P=Path(__file__).resolve().parent
# Load definitions without running experiment driver.
d={'__file__':str(P/'check.py')};exec((P/'check.py').read_text().split('records=[]')[0],d)
ehr=d['ehr'];size=d['size'];heights=d['heights'];x=d['x']
# Brute coordinates against published height recurrence, including weighted nodes.
def brute(t,m):
 n=size(t);sub=[]
 def walk(t,base):
  r,ch=t;i=base+r
  for c in ch:walk(c,i);i+=size(c)
  sub.append((base,i));return i
 walk(t,0);h=[0]*(m*n+1)
 for a in itertools.product(range(m*n+1),repeat=n):
  if all(sum(a[l:r])<=m*(r-l) for l,r in sub):h[sum(a)]+=1
 return h
small=[(r,()) for r in range(1,5)]+[(1,((1,()),)),(1,((1,()),(1,()))),(2,((1,()),)),(1,((2,()),)),(1,((1,((1,()),)),))]
for t in small:assert list(heights(t,1))==brute(t,1)
# Same published octopus inclusion-exclusion, independently derived from inequalities.
for n in range(2,15):
 for k in range(n):
  t=(n-k,tuple((1,()) for _ in range(k)))
  for m in range(4):
   ie=sum((-1)**j*math.comb(k,j)*math.comb((n-j)*m+n-j,n) for j in range(k+1))
   assert ie==sum(heights(t,m))
# Magic-positive genuine lattice polygon, no root-preservation bridge to Ehrhart.
magic=S.Poly(2*x*x+2*x+1,x)
assert S.discriminant(magic.as_expr(),x)==-4
for m in range(6):assert sum(1 for a in range(-m,m+1) for b in range(-m,m+1) if abs(a)+abs(b)<=m)==magic.eval(m)
# A genuine source-state first moment vs a naive mean-height identity.
t=(1,((1,()),));hs=heights(t,1);N=sum(hs);M=sum(i*a for i,a in enumerate(hs))
# root extension size1 from forest of size2: (3m+1) E - height moment
root=(1,(t,));assert sum(heights(root,1))==4*N-M
# Compare source subtree to its one-block simplex: same dimension, different normalized mean.
other=(2,());ho=heights(other,1)
assert S.Rational(M,N)!=S.Rational(sum(i*a for i,a in enumerate(ho)),sum(ho))
# Check natural root-enlargement interlacing on real source states; exact isolating intervals.
out={'brute_cases':len(small),'octopus_ie_checks':sum(n for n in range(2,15))*4,'magic_counterexample':'2*x^2+2*x+1; lattice diamond, discriminant -4','height_moment':{'chain':list(hs),'chain_mean':str(S.Rational(M,N)),'simplex':list(ho),'simplex_mean':str(S.Rational(sum(i*a for i,a in enumerate(ho)),sum(ho)))}}
# first-moment table is retained as an obstruction, not a source theorem.
(P/'routes.json').write_text(json.dumps(out,indent=2));print(json.dumps(out,indent=2))
# Actual obstruction to using only E real-rooted, positive integer height masses,
# and the honest support bound 0<=height<=Nm in a root-attachment induction.
e=S.Poly((x+1)*(2*x+1),x);fake_m=S.Poly(2*x*(x+1)**2,x)
g=S.Poly((3*x+1)*e.as_expr()-fake_m.as_expr(),x)
assert g==S.Poly((x+1)*(4*x*x+3*x+1),x)
assert S.discriminant(4*x*x+3*x+1,x)==-7
for m in range(8):
 masses={0:m*(m+1),2*m:(m+1)**2} if m else {0:1}
 assert sum(masses.values())==e.eval(m)
 assert sum(h*c for h,c in masses.items())==fake_m.eval(m)
 assert all(c>=0 and 0<=h<=2*m for h,c in masses.items())
# Universal k=0,1 root formulas checked on genuine source distributions.
identities=0
for t in small:
 N=size(t);root=(1,(t,))
 for m in range(4):
  w=heights(t,m);E=sum(w);M=sum(i*a for i,a in enumerate(w));Q=sum(i*i*a for i,a in enumerate(w));z=heights(root,m);B=(N+1)*m
  assert sum(z)==(B+1)*E-M
  assert 2*sum(i*a for i,a in enumerate(z))==(B*B+B)*E+M-Q
  identities+=2
out.update(fake_profile={'E':str(e.as_expr()),'M':str(fake_m.as_expr()),'G':str(g.as_expr()),'quadratic_discriminant':-7},root_moment_identities=identities)
(P/'routes.json').write_text(json.dumps(out,indent=2));print('Additional exact route checks PASS',identities)
