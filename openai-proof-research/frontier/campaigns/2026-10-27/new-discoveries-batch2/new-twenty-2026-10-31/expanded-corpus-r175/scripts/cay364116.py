# Verify the 364116 identities for small n by brute force; Prim[n] = Cayley perms with no flat steps (w_i != w_{i+1}); |Prim'[n]| = |Prim[n+1]|.
import itertools
def cay(n):
    for w in itertools.product(range(1,n+1),repeat=n):
        s=set(w)
        if s==set(range(1,len(s)+1)): yield w
for n in range(1,8):
    C=list(cay(n)); P=[w for w in cay(n+1) if all(w[i]!=w[i+1] for i in range(n))]
    a=len(P); b=sum(sum(w) for w in C); c=sum(i for w in C for i in range(1,n+1) if w[i-1]==i); d=sum(w[0] for w in C)
    print(n,'|Prim[n+1]|=',a,'half=',a/2,'(1/n)sum=',b/n,'fixsum=',c,'sum w1=',d, 'OK' if a==2*d and b==n*d and c==d else 'FAIL')
