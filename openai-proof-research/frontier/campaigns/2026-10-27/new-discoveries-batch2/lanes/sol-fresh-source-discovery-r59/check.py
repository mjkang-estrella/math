import itertools,json,math,random
from pathlib import Path
import sympy as s
P=Path(__file__).resolve().parent;x=s.Symbol('x')
def add(a,b):
 c=[0]*max(len(a),len(b))
 for i,v in enumerate(a):c[i]+=v
 for i,v in enumerate(b):c[i]+=v
 while len(c)>1 and c[-1]==0:c.pop()
 return tuple(c)
def poly(a):return s.Poly.from_list(list(reversed(a)),x)
def dp(lam):
 c=max(lam,default=0);D=[(0,)]*(c+1)+[(1,)]
 for w in lam:
  E=D[:];tail=(0,)
  for j in range(c,0,-1):
   tail=add(tail,D[j+1]);
   if j<=w:E[j]=add(E[j],(0,)+tail)
  D=E
 a=(0,)
 for v in D:a=add(a,v)
 return a
def column(lam):
 n=len(lam);F=[(1,)]*(n+1)
 for j in range(max(lam,default=0),0,-1):
  h=sum(w>=j for w in lam);G=F[:];tail=(0,)
  for i in range(1,h+1):
   tail=add(tail,F[i-1]);G[i]=add(F[i],(0,)+tail)
  for i in range(h+1,n+1):G[i]=G[h]
  F=G
 return F[-1]
def brute(lam):
 a=[0]*(len(lam)+1)
 def go(i,last,k):
  if i==len(lam):a[k]+=1;return
  go(i+1,last,k)
  for j in range(1,min(last-1,lam[i])+1):go(i+1,j,k+1)
 go(0,max(lam,default=0)+1,0)
 while len(a)>1 and a[-1]==0:a.pop()
 return tuple(a)
def real(p):return sum(m for ab,m in p.intervals())==p.degree()
def nonneg(p):
 if p.is_zero:return True
 if p.LC()<0 or p.degree()%2:return False
 return all(m%2==0 or q.count_roots(-s.oo,s.oo)==0 for q,m in p.sqf_list()[1])
def parts(r,c):
 for a in itertools.combinations_with_replacement(range(c+1),r):
  b=tuple(v for v in reversed(a) if v)
  if b:yield b
shapes=list(parts(5,5));counts={'shapes':len(shapes),'dp_column_equal':0,'brute_equal':0,'rr':0,'corrected_direction_Wronskians':0}
for lam in shapes:
 a=dp(lam);assert a==column(lam);counts['dp_column_equal']+=1
 if len(lam)<=4 and max(lam)<=4:assert a==brute(lam);counts['brute_equal']+=1
 f=poly(a);assert real(f);counts['rr']+=1
 small=tuple(v-1 for v in lam if v>1);g=poly(dp(small));h=poly((0,))
 for i in range(len(lam)):h+=poly(dp(lam[:i]))
 assert real(g) and real(h)
 # Intended smaller << larger under Branden convention, opposite printed v2 arrows.
 assert nonneg(f.diff()*g-f*g.diff()),lam
 assert nonneg(f.diff()*h-f*h.diff()),lam
 counts['corrected_direction_Wronskians']+=2
# Source skew counterexample independent reconstruction.
# The general skew DP is obtained by restricting row j to mu_i<col<=lambda_i.
def skew(lam,mu):
 c=max(lam);D=[(0,)]*(c+1)+[(1,)]
 for i,w in enumerate(lam):
  E=D[:];tail=(0,)
  for j in range(c,0,-1):
   tail=add(tail,D[j+1])
   if mu[i]<j<=w:E[j]=add(E[j],(0,)+tail)
  D=E
 a=(0,)
 for v in D:a=add(a,v)
 return a
known=(1,32,336,1420,2534,1946,658,86,3)
assert skew((8,8,8,8,8,8,7,6,5),(7,6,6,5,4,3,2,1,0))==known
assert not real(poly(known));counts['source_skew_counterexample']=True
# Adjacent interlacing alone is not an invariant preserved by the column update.
F=[s.Poly((1+x)**i,x) for i in range(4)]
G=[F[i]+s.Poly(x,x)*sum(F[:i],s.Poly(0,x)) for i in range(4)]
assert G[3].as_expr()==2*x**3+6*x**2+6*x+1
assert s.discriminant(G[3].as_expr(),x)==-108 and not real(G[3])
counts['false_general_adjacent_closure']={'G3':str(G[3].as_expr()),'discriminant':-108}
# Printed arrow already has wrong direction on the one-row interior example.
counts['printed_arrow_obstruction']={'lambda':[2],'M':[1,2],'Mminus1':[1,1],'roots':['-1/2','-1'],'credit':0}
# Classical Catalan HPP obstruction from v3 theorem4.3; not the same polynomial M_lambda.
f=s.Poly(x**3+36*x**2+225*x+400,x);assert not real(f)
counts['HPP_cubic_discriminant']=int(s.discriminant(f.as_expr(),x))
center=(1,1);leaves=[(2,4),(3,3),(4,2)]
def conflict(a,b):return (a[0]-b[0])*(a[1]-b[1])>=0
assert all(conflict(center,b) for b in leaves)
assert all(not conflict(a,b) for a,b in itertools.combinations(leaves,2))
counts['actual_square4_conflict_claw']=True
z=s.Symbol('z');omega=s.expand(z*(z+1)*(z-1)/3)
e2=omega.subs(z,2);e3=omega.subs(z,3)-3*e2
assert e2==e3==2 and dp((2,1))==(1,3,1)
counts['classical_Ferrers_E_mismatch']={'E':[0,0,2,2],'M':[1,3,1]}
(P/'checks.json').write_text(json.dumps(counts,indent=2)+'\n');print(json.dumps(counts))
