import sys
N=int(sys.argv[1]); M=int(sys.argv[2])  # modulus for series arithmetic
def f(r):
    # Euler pentagonal: prod (1-q^{rk}) = sum (-1)^k q^{r k(3k-1)/2}
    s=[0]*(N+1); k=0
    while True:
        done=True
        for kk in ([0] if k==0 else [k,-k]):
            e=r*kk*(3*kk-1)//2
            if e<=N: s[e]+=(-1)**(abs(kk)%2); done=False
        if done and k>0: break
        k+=1
    return s
def mul(a,b):
    c=[0]*(N+1)
    nz=[(i,x) for i,x in enumerate(b) if x]
    for i,x in enumerate(a):
        if x:
            for j,y in nz:
                if i+j>N: break
                c[i+j]=(c[i+j]+x*y)%M
    return c
def inv(a):
    # a[0]=1
    b=[0]*(N+1); b[0]=1
    nz=[(i,x) for i,x in enumerate(a) if x and i>0]
    for n in range(1,N+1):
        s=0
        for i,x in nz:
            if i>n: break
            s+=x*b[n-i]
        b[n]=(-s)%M
    return b
num=mul(mul(f(4),f(6)),f(6))
den=mul(mul(f(1),f(3)),f(12))
g=mul(num,inv(den))
print('first',g[:12])
bad=[n for n in range(5,N+1,25) if g[n]%4]
print('checked 25n+5 up to',N,'count',len(range(5,N+1,25)),'failures',bad[:20])
for a,b in [(16,12),(24,20),(32,24),(48,26)]:
    print(a,b,[n for n in range(b,N+1,a) if g[n]%4][:5])
print('PD2(5+25n) mod 8 for n<20:',[g[n]%8 for n in range(5,min(N,500)+1,25)])
