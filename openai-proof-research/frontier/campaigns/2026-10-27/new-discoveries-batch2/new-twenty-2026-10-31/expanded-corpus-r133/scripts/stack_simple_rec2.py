# Lower-bound recursion g_n = (4 g_{n-1} + sum_{i=1}^{n-2} g_i g_{n-1-i})/n, seeds g_n=d_n (n<=a).
from fractions import Fraction
import math, json
P={int(k):int(v) for k,v in json.load(open('outputs/stack_pairs_P_1_82.json')).items()}
for a in [1,2,3,4,5,6,7,8,10,12,14,16,20]:
    g=[Fraction(1)]+[Fraction(P[n],math.factorial(n)) for n in range(1,a+1)]
    N=300
    for n in range(a+1,N+1):
        g.append((4*g[n-1]+sum(g[i]*g[n-1-i] for i in range(1,n-1)))/n)
    best=max(((float(g[n])/(4*(n+1)))**(1/(n+1)),n) for n in range(5,N+1))
    print(a, 'ratio@300', float(g[300]/g[299]), 'best doubling bound', best, flush=True)
