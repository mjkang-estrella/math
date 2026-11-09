from math import comb

def v2(x):
    assert x
    return (abs(x)&-abs(x)).bit_length()-1

def mul(a,b):
    c=[0]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b): c[i+j]+=x*y
    return c

checks=0
for k in range(1,65):
    u=[4**E*comb(k+E,2*E+1) for E in range(k)]
    r=[8*x for x in mul(u,u)]
    a=3+2*v2(k)
    assert r[0]==8*k*k and v2(r[0])==a
    for E,x in enumerate(u): assert v2(x)>=v2(k)+E
    for E,x in enumerate(r): assert v2(x)>=a+E
    for i in range(1,8):
        E=2**i-1
        if E<len(r): assert v2(r[E])>=a+i+1
    checks+=len(r)
for k in range(1,17):
    N=128
    c=[1]+[0]*N
    for _ in range(2*k):
        for step in [1]+[2**i for i in range(N.bit_length())]:
            for j in range(step,N+1):c[j]+=c[j-step]
    for n in range(1,33):
        assert v2(c[4*n]-c[n])==v2(n)+2*v2(k)+3
print('PASS:',checks,'rho coefficients; 512 literal even differences')
