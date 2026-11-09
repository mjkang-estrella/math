# Lower-bound sequence e_n: e_n = d_n (exact) for n<=a, e_n = (1/n) sum_{i} e_i e_{n-1-i} for n>a (d_0=1)
from fractions import Fraction
import math
P=[1,1,4,26,224,2356,29064,411172,6573624,117448188,2322885008,50429847572,1192782788192]
for a in range(3,13):
    E=[Fraction(P[n],math.factorial(n)) for n in range(a+1)]
    N=400
    for n in range(a+1,N+1):
        E.append(sum(E[i]*E[n-1-i] for i in range(n))/n)
    r=[float(E[n]/E[n-1]) for n in (100,200,400)]
    best=max(((float(E[n-1])/(4*n))**(1/n),n) for n in range(10,N+1))
    print(a, 'ratios',r, 'doubling bound best',best, flush=True)
