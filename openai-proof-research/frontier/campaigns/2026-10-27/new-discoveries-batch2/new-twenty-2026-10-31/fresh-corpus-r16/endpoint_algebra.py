import os,resource
os.sched_setaffinity(0,{0,1});resource.setrlimit(resource.RLIMIT_AS,(1024**3,1024**3))
import sympy as s
m=s.symbols('m',integer=True,positive=True)
def ratio(lam):
 l=len(lam);num=s.factorial(m)*s.factorial(m+1)
 for i in range(l):
  num/=s.factorial(lam[i]+l-i-1)
  for j in range(i+1,l):num*=lam[i]-lam[j]+j-i
 return s.factor(s.combsimp(num))
a=ratio([m-1,m-1,1,1]);b=ratio([m-2,m-2,2,2]);c=ratio([m-2,m-2,1,1,1,1]);g=s.factor(a**4-b**2-c**2)
P=s.cancel(g*576*(m+2)**4*(m+3)**2/(m-1)**2)
print('ratios:',a,b,c);print('gap:',g);print('P(5+t):',s.Poly(s.expand(P.subs(m,m+5)),m))
assert all(v>0 for v in s.Poly(s.expand(P.subs(m,m+5)),m).all_coeffs())
print('Symbolic diagnostic only, not a literal full-scope Lean certificate.')
