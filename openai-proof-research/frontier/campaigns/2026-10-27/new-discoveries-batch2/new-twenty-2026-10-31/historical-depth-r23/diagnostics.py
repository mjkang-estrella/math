"""Finite diagnostics only; no theorem or semantic certificate."""
from fractions import Fraction as Q
import math,resource,os,json,pathlib
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,)*2);resource.setrlimit(resource.RLIMIT_CPU,(15,)*2);os.sched_setaffinity(0,set(sorted(os.sched_getaffinity(0))[:2]))
c=[Q(1)]
for n in range(1,33):
 c.append(-(2*n+1)*sum((c[k]/(n+k+1) for k in range(n)),Q(0)))
 assert sum((c[k]/(n+k+1) for k in range(n+1)),Q(0))==0
print('orthorecursive exact initial coefficients',list(map(str,c[:6])))
print('sign changes N>0 through31',[n for n in range(1,32) if c[n]*c[n+1]<0])
# Falsify tempting transfer constructions, not the conjecture.
for n in [7,9,11,15,21,25]:
 v=list(range(1,n+1));u=list(range(n+1,2*n+1))
 bad=[('spoke',i+1,v[i],u[i],math.gcd(v[i],u[i])) for i in range(n) if math.gcd(v[i],u[i])>1]
 bad += [('inner',i+1,u[i],u[(i+3)%n],math.gcd(u[i],u[(i+3)%n])) for i in range(n) if math.gcd(u[i],u[(i+3)%n])>1]
 print('GP shifted rails',n,'first failures',bad[:4])
# Source GP(n,2) period-five template moved literally to k=3.
for n in [15,25]:
 v=[12*k+x for k in range(n//5) for x in [2,3,5,8,9]]
 u=[12*k+x for k in range(n//5) for x in [1,4,10,7,11]]
 print('wrong-k template',n,'inner failures',[(i+1,u[i],u[(i+3)%n],math.gcd(u[i],u[(i+3)%n])) for i in range(n) if math.gcd(u[i],u[(i+3)%n])>1][:4])
print('sandpile symbolic filters: K_m S=(m-1)^2 mod m=1; odd C_m S=m+1 mod m=1; even C_m S=m mod m=0. These are restricted families, not a proof for arbitrary graphs.')
