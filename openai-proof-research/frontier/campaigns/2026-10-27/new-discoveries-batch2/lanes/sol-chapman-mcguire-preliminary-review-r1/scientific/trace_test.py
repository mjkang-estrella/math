from retrieve import *
import sympy as S
a=S.symbols('a')
for q in [2,3,4,5]:
 T=sum(a**i for i in range(q+1));P=T**(q+1)-a
 print(q,S.factor(P,modulus=2 if q==4 else q))
