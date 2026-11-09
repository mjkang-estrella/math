# independent GF(5^8) check with polynomial arithmetic mod f = X^8+X^7+2X^6+2
p=5; f=[2,0,0,0,0,0,2,1,1]  # coeffs low->high
def mul(a,b):
    r=[0]*15
    for i,x in enumerate(a):
        if x:
            for j,y in enumerate(b): r[i+j]=(r[i+j]+x*y)%p
    for k in range(14,7,-1):
        c=r[k]
        if c:
            for i in range(9): r[k-8+i]=(r[k-8+i]-c*f[i])%p
    return r[:8]
def pw(a,e):
    r=[1]+[0]*7
    while e:
        if e&1: r=mul(r,a)
        a=mul(a,a); e>>=1
    return r
one=[1]+[0]*7; X=[0,1]+[0]*6
q=p**8
# irreducibility: X^(5^8)=X and X^(5^k)!=X for k|8,k<8 (k=1,2,4)
assert pw(X,q)==X
for k in (1,2,4): assert pw(X,p**k)!=X
x=[0,2,4,1,0,0,0,0]
e=(q-1)//3
for a in range(5):
    d=x[:]; d[0]=(d[0]-a)%p
    assert any(d) and pw(d,e)==one, a
# F5 clique: nonzero elements of F5 are cubes in F_q (since every element of F5* satisfies c^e = c^((q-1)/3); q-1)/3 divisible by 4)
for c in range(1,5): assert pw([c]+[0]*7,e)==one
print('ROOT GF CHECK PASS: f irreducible, x-a cubes for all a in F5, F5* cubes')
