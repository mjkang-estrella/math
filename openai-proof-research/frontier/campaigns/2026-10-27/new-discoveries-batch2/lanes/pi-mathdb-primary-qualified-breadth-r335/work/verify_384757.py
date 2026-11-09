from fractions import Fraction
# Eulerian polynomials (standard): A_0=1, A_1=1, A_2=1+x, A_3=1+4x+x^2, A_4=1+11x+11x^2+x^3
def eul(n):
    import itertools, fractions
    # Eulerian numbers via recurrence A(n,k)=(n-k)A(n-1,k-1)+(k+1)A(n-1,k)
    A=[[0]*(n) for _ in range(n+1)]
    A[0][0]=1
    for m in range(1,n+1):
        for k in range(m):
            A[m][k]=(m-k)*(A[m-1][k-1] if k>=1 else 0)+(k+1)*A[m-1][k]
    return A[n]  # coefficients of A_n(x), degree n-1
# build A_0..A_4
polys={0:[1]}
for n in range(1,5):
    polys[n]=eul(n)
print("Eulerian polys:", {k:v for k,v in polys.items()})
# f(z)=(z+5)^3 -> b=(125,75,15,1)
b=[125,75,15,1]
Q=[Fraction(0)]*3
for i,bi in enumerate(b):
    for j,c in enumerate(polys[i]):
        Q[j]+=bi*c
print("Q coeffs:",Q)  # expect [216,19,1]
def disc(Q):
    a,b,c=Q[2],Q[1],Q[0]
    return b*b-4*a*c
print("disc:",disc(Q))
# variant without A_0 (sum from i=1)
Q2=[Fraction(0)]*3
for i in range(1,4):
    for j,c in enumerate(polys[i]):
        Q2[j]+=b[i]*c
print("Q2 (no A_0):",Q2, "disc:",disc(Q2))
# variant with shifted convention A'_i = standard A_{i+1}, i=0..3
polysS={i:polys[i+1] for i in range(4)}
Q3=[Fraction(0)]*4
for i,bi in enumerate(b):
    for j,c in enumerate(polysS[i]):
        Q3[j]+=bi*c
print("Q3 (shifted):",Q3)
# cubic discriminant
a3,b3,c3,d3=Q3
Delta = 18*a3*b3*c3*d3 - 4*b3**3*d3 + b3**2*c3**2 - 4*a3*c3**3 - 27*a3**2*d3**2
print("cubic disc:",Delta)
# distinct-root variant f=(z+49/10)(z+5)(z+51/10)
from fractions import Fraction as F
def polymul(p,q):
    r=[F(0)]*(len(p)+len(q)-1)
    for i,a in enumerate(p):
        for j,c in enumerate(q):
            r[i+j]+=a*c
    return r
f=polymul([F(49,10),1],polymul([F(5),1],[F(51,10),1]))
print("f coeffs:",f)
Q4=[F(0)]*3
for i,bi in enumerate(f):
    for j,c in enumerate(polys[i]):
        Q4[j]+=bi*c
print("Q4 coeffs:",Q4,"disc:",disc(Q4))
# brute sanity: Q real-rootedness via exact Sturm for Q, Q4
def sturm_count_real(coeffs):
    # coeffs low->high; return number of distinct real roots
    p=[c for c in coeffs]
    while len(p)>1 and p[-1]==0: p.pop()
    def deriv(poly):
        return [i*poly[i] for i in range(1,len(poly))]
    def rem(a,b):
        a=a[:]; 
        while len(a)>=len(b) and any(a):
            while len(a)>=len(b) and a[-1]==0 and len(a)>len(b): a.pop()
            if len(a)<len(b): break
            f=a[-1]/b[-1]; sh=len(a)-len(b)
            for i in range(len(b)): a[i+sh]-=f*b[i]
            a.pop()
        while a and a[-1]==0: a.pop()
        return a
    def sgn_at(poly,x):
        s=0
        for c in reversed(poly):
            s=s*x+c
        return (s>0)-(s<0)
    p1=p[:]; p2=deriv(p)
    chain=[p1,p2]
    while len(chain[-1])>1:
        r=rem(chain[-2],chain[-1])
        if not r: break
        chain.append([-c for c in r])
    def V(x):
        last=None; cnt=0
        for poly in chain:
            s=sgn_at(poly,x)
            if s!=0:
                if last is not None and s!=last: cnt+=1
                last=s
        return cnt
    return V(F(10)**9)-V(-F(10)**9)
print("real roots of Q:",sturm_count_real(Q))
print("real roots of Q4:",sturm_count_real(Q4))
