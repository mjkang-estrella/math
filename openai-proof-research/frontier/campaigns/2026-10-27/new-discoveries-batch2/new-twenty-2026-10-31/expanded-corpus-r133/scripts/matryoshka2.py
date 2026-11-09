from fractions import Fraction as F
import math, sys
N=int(sys.argv[1])
m=[0,1]
for n in range(2,N+1): m.append(sum((k+1)*m[k]*m[n-k] for k in range(1,n)))
p=lambda n: n**4+18*n**3+107*n**2+242*n+168
fact=[1]
for i in range(1,N+1): fact.append(fact[-1]*i)
a=[None]+[F(m[n],fact[n]) for n in range(1,N+1)]
b=[None]+[a[n]/p(n) for n in range(1,N+1)]
for n in [5,10,20,50,100,200,400,800,N]:
    R = a[n]-(1+F(2,n))*a[n-1]-F(2,n)*a[n-2]
    rho=R/p(n)
    print(n, float(b[n]), 'rho_n',float(rho), 'n^2 rho', float(rho*n*n), 'R/(n^2 b)', float(R/(n*n*b[n])), flush=True)
mono=all(b[n]>=b[n-1] for n in range(6,N+1)); print('b increasing from 6:',mono, [float(x) for x in b[1:8]])
