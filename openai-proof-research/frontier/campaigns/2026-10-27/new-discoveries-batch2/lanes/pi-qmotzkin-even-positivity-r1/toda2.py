import sys, re
src = open('compute.py').read().replace('NMAX = 26','NMAX = 30').replace('for n in range(13):','for n in range(0):')
exec(src)
def kappa(n): return 0 if n%3==2 else (-1)**(n//3)
beta = lambda n: n*(n-1)*(2*n-1)//6
ok1 = ok2 = True
for n in range(1,15):
    D1 = hankel_det(1,n)
    E = n*(n*n-1)//3
    expect1 = {E: kappa(n)} if kappa(n) else {}
    ok1 &= (D1 == expect1)
    D2 = hankel_det(2,n)
    # closed form: q^{beta_{n+1}-1}(1+q) + sum_{2<=j<=n, j%3!=2} q^{beta_{n+1}-j}
    ex = {beta(n+1)-1: 1, beta(n+1): 1}
    for j in range(2,n+1):
        if j%3 != 2: ex[beta(n+1)-j] = 1
    ok2 &= (D2 == ex)
    if not ok2: print("FAIL n=",n, pstr(D2))
print("Delta^1 = kappa_n q^{n(n^2-1)/3}, n<=14:", ok1)
print("Delta^2 explicit monomial closed form, n<=14:", ok2)
# sample
n=7; ex = {beta(n+1)-1:1, beta(n+1):1}
for j in range(2,n+1):
    if j%3!=2: ex[beta(n+1)-j]=1
print("Delta_7^(2) = ", pstr(hankel_det(2,7)))
print("closed form  = ", pstr(ex))
