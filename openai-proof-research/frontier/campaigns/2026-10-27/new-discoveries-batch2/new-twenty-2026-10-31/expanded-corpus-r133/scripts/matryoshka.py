# m_1=1, m_n = sum_{k=1}^{n-1} (k+1) m_k m_{n-k}; examine m_n/(n! n^4)
from fractions import Fraction
import math, sys
N=int(sys.argv[1])
m=[0,1]
for n in range(2,N+1):
    m.append(sum((k+1)*m[k]*m[n-k] for k in range(1,n)))
print('first',m[1:10])
for n in [10,20,50,100,200,400,800,N]:
    if n<=N:
        b=Fraction(m[n],math.factorial(n)*n**4)
        print(n, float(b))
