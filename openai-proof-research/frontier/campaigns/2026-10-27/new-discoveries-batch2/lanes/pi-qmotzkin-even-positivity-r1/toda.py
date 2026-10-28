# Toda-recursion proof of the k=1 case: Delta_n^{(2)} = q^{n^2} Delta_{n-1}^{(2)} + kappa_n^2 q^{n(n-1)(2n+5)/6}
import sys; sys.path.insert(0,'.')
from compute import M, hankel_det, padd, pmul, pstr

def kappa(n):
    if n % 3 == 2: return 0
    return (-1)**(n//3)

beta = lambda n: n*(n-1)*(2*n-1)//6
ok_all = True
prev2 = None
print("n | Delta_n^(2) | rec-match | explicit-formula-match | coefficients")
for n in range(1, 14):
    D = hankel_det(2, n)
    if n >= 2:
        rhs = pmul({n*n: 1}, prev2)
        e = n*(n-1)*(2*n+5)//6
        rhs = padd(rhs, {e: kappa(n)**2})
    else:
        rhs = {0:1, 1:1}
    prev2 = D
    # explicit formula
    ex = {}
    s2 = sum(j*j for j in range(2,n+1))
    ex[s2] = 1; ex[s2+1] = 1
    for j in range(2,n+1):
        if kappa(j) != 0:
            e2 = j*(j-1)*(2*j+5)//6 + sum(i*i for i in range(j+1,n+1))
            ex[e2] = ex.get(e2,0)+1
    m1 = (D == rhs); m2 = (D == ex)
    ok_all &= m1 and m2
    print(n, "rec:", m1, "expl:", m2, pstr(D) if n<=6 else "")
print("ALL OK (k=1 case, n<=13):", ok_all)

# also verify Delta^{(0)} monomial & Delta^{(1)} = kappa_n q^{n(n^2-1)/3} up to n=12
ok0 = all(hankel_det(0,n) == {beta(n):1} for n in range(1,13))
ok1 = all(hankel_det(1,n) == ({kappa(n)} and {n*(n*n-1)//3: kappa(n)} if kappa(n) else {}) for n in range(1,13))
print("Delta^0 monomial (n<=12):", ok0, " Delta^1 = kappa q^E (n<=12):", ok1)
