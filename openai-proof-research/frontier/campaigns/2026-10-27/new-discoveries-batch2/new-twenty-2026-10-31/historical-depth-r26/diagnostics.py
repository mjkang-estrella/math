# Diagnostic calculations only. No MathDB endpoint certified.
from fractions import Fraction as F
from itertools import product
import resource,os
resource.setrlimit(resource.RLIMIT_AS,(256*1024**2,256*1024**2));resource.setrlimit(resource.RLIMIT_CPU,(10,10));os.sched_setaffinity(0,{0,1})
A=((0,1,1),(1,0,-2),(1,-2,0))
loops=[(p,A[p[0]][p[1]]*A[p[1]][p[2]]*A[p[2]][p[0]]) for p in product(range(3),repeat=3) if len(set(p))==3]
print('BMV A=',A,'B=diag(0,2,1); oriented three-cycle weights',loops)
print('Sum three-cycle weights',sum(v for _,v in loops))
# HH n=2 exact integrals at rational h,d, squared sloping-face factor.
for d in [F(1,2),F(1,10),F(1,100)]:
 h=d*d; V=h/2; I=h*d*d/2*(1-d/3)
 # S=1+h+q, J=d^2(1+q)/2+hd, q=sqrt(1+h^2)
 print('HH planar d,h,V,I, J constant, J q coefficient, q^2:',d,h,V,I,d*d/2+h*d,d*d/2,1+h*h)
print('No interval arithmetic / formal integration / sharp-constant theorem claimed.')
