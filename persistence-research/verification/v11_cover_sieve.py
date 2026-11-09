# Independent covering sieve for 10^L + K = 2^t0 * 3^a * 7^w  (L > L0), proving no solution
# beyond brute force.  Node = class L ≡ rho (mod M).  All kills are necessary conditions.
import sys, math
sys.setrecursionlimit(100000)
K=int(sys.argv[1]); L0=int(sys.argv[2]) if len(sys.argv)>2 else 3000
t0=(K & -K).bit_length()-1
def v(x,p):
    c=0
    while x%p==0 and x: x//=p; c+=1
    return c
def ordmod(g,q):
    o=q-1
    for p in set(f for f in range(2,int(o**.5)+2) if o%f==0 and all(f%k for k in range(2,int(f**.5)+1))) | ({o} if all(o%k for k in range(2,int(o**.5)+1)) else set()):
        pass
    # simple: factor o
    n=o; fs=[]; f=2
    while f*f<=n:
        while n%f==0: fs.append(f); n//=f
        f+=1
    if n>1: fs.append(n)
    for p in set(fs):
        while o%p==0 and pow(g,o//p,q)==1: o//=p
    return o
# brute force small L
sols=[]
for L in range(1,L0+1):
    x=10**L+K
    if v(x,2)==t0 or L<=t0+2:
        y=x
        for p in (2,3,7):
            while y%p==0: y//=p
        if y==1: sols.append(L)
print("K",K,"t0",t0,"brute-force solutions L<=%d:"%L0, sols)
# auxiliary primes
def isprime(n): return n>1 and all(n%k for k in range(2,int(n**.5)+1))
Q=[]
for q in range(11,60000):
    if not isprime(q): continue
    d=ordmod(10,q)
    m=d
    for p in (2,3,5,7,11,13):
        while m%p==0: m//=p
    if m!=1 or d>1500: continue   # d_q must be 13-smooth
    o3,o7=ordmod(3,q),ordmod(7,q)
    H=set(); x=1
    for _ in range(o3): H.add(x); x=x*3%q
    G=set(); 
    for h in H:
        y=h
        for _ in range(o7): G.add(y); y=y*7%q
    Q.append((len(G)/(q-1),q,d,o3,o7))
Q.sort()
Q=[x for x in Q if x[0]<1][:400]
print("aux primes:",len(Q))
inv2=lambda q: pow(pow(2,t0,q),-1,q)
nodes=[0]; fails=[]
def sig(rho,M):
    j=v(M,3) if M%3==0 else 0
    if M%3==0 or j>0:
        r=(pow(10,rho,3**(j+2))+K)%3**(j+2)
        a=('exact',v(r,3)) if r else ('ge',j+2)
    else: a=('ge',2) if (pow(10,rho,9)+K)%9==0 else ('exact',v((pow(10,rho,9)+K)%9,3))
    if M%6==0:
        i=v(M,7); r=(pow(10,rho,7**(i+1))+K)%7**(i+1)
        w=('exact',v(r,7)) if r else ('ge',i+1)
    else: w=('ge',0)
    return a,w
def killed_by(q,d,o3,o7,rho,a,w):
    T=(pow(10,rho%d,q)+K)*inv2(q)%q
    if T==0: return False   # q | 10^L+K would contradict smoothness -> actually kills
    A=[pow(3,a[1],q)] if a[0]=='exact' else [pow(3,k,q) for k in range(o3)]
    W=[pow(7,w[1],q)] if w[0]=='exact' else [pow(7,k,q) for k in range(o7)]
    Ws=set(W)
    return not any((T*pow(x,-1,q))%q in Ws for x in A)
def solve(rho,M,depth):
    nodes[0]+=1
    if nodes[0]>3_000_000: raise SystemExit("node cap")
    a,w=sig(rho,M)
    for _,q,d,o3,o7 in Q:
        if M%d==0:
            T=(pow(10,rho%d,q)+K)%q
            if T==0: return           # q divides 10^L+K for all L in class -> not 7-smooth
            if killed_by(q,d,o3,o7,rho,a,w): return
    if a[0]=='exact' and w[0]=='exact':
        N=2**t0*3**a[1]*7**w[1]-K
        if N>0 and str(N)=='1'+'0'*(len(str(N))-1):
            L=len(str(N))-1
            if L%M==rho%M and L>L0: fails.append(('SOLUTION',L))
        return
    if depth>60: fails.append((rho,M,a,w)); return
    # refine: next aux prime whose d does not divide M, else deepen 3/7
    for _,q,d,o3,o7 in Q:
        if M%d:
            f=d//math.gcd(M,d); break
    else: f=None
    if M%6: f=6//math.gcd(M,6)
    elif a[0]=='ge' and (w[0]=='exact' or v(M,3)<=v(M,7)): f=3 if f is None or depth%2==0 else f
    elif w[0]=='ge': f=7 if f is None or depth%2==1 else f
    M2=M*f
    for k in range(f): solve(rho+k*M,M2,depth+1)
solve(0,1,0)
print("nodes",nodes[0],"unresolved/failed:",fails[:5], "COMPLETE" if not fails else "INCOMPLETE")
