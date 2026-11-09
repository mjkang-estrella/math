# OBSOLETE EXPLORATORY MODEL: incorrect actual-record normalization; see ATTEMPTS.md.
from math import comb
# coefficients of m^a j^b
N={(0,4):1,(1,3):-2,(0,3):-6,(0,2):-1,(3,1):2,(2,1):12,(1,1):24,(0,1):18,(4,0):1,(3,0):6,(2,0):11,(1,0):6}
def subst(p,mode,c):
 # j=m+d+c, or m=j+d+c
 out={}
 for (a,b),v in p.items():
  power=b if mode=='j' else a
  for i in range(power+1):
   for k in range(power-i+1):
    z=power-i-k;coef=v*comb(power,i)*comb(power-i,k)*c**z
    key=(a+i,k) if mode=='j' else (b+i,k)
    out[key]=out.get(key,0)+coef
 return {x:v for x,v in out.items() if v}
for mode in ['j','m']:
 print(mode,sorted(subst(N,mode,0).items()))
# Substitute m=d+e,j=2d+e into N, then translate d,e.
def cone():
 out={}
 for (a,b),v in N.items():
  for i in range(a+1):
   for j in range(b+1):
    key=(i+j,a+b-i-j);out[key]=out.get(key,0)+v*comb(a,i)*comb(b,j)*2**j
 return {k:v for k,v in out.items() if v}
def shift(p,A,B):
 out={}
 for (a,b),v in p.items():
  for i in range(a+1):
   for j in range(b+1):
    key=(i,j);out[key]=out.get(key,0)+v*comb(a,i)*comb(b,j)*A**(a-i)*B**(b-j)
 return {k:v for k,v in out.items() if v}
# other cone d>=m: m=e,j=2e+d
p=cone(); print('cone m<=j<=2m',p)
for A,B in [(0,6),(1,5),(2,4),(3,3),(4,2),(5,1),(6,0)]:print(A,B,min(shift(p,A,B).values()))
def linearcone(M,J):
 out={}
 for (a,b),v in N.items():
  for i in range(a+1):
   for j in range(b+1):
    key=(i+j,a+b-i-j);out[key]=out.get(key,0)+v*comb(a,i)*comb(b,j)*M[0]**i*M[1]**(a-i)*J[0]**j*J[1]**(b-j)
 return {k:v for k,v in out.items() if v}
for M,J in [((1,1),(2,1)),((0,1),(1,2))]:
 p=linearcone(M,J)
 for T in range(30):
  if all(min(shift(p,A,T-A).values())>=0 for A in range(T+1)):
   print('certificate',M,J,'threshold',T);break
 print(p)
