# Control: Paley conference matrices give MDS codes (matches source's verification up to n=23) and the
# polynomial (doubly-extended RS) identification. Usage: python3 -I paley_control.py
import itertools
def leg(a,p):
    a%=p
    return 0 if a==0 else (1 if pow(a,(p-1)//2,p)==1 else -1)
def paley(p):
    n=p+1; eps=1 if p%4==1 else -1
    W=[[0]*n for _ in range(n)]
    for j in range(1,n): W[0][j]=1; W[j][0]=eps
    for i in range(p):
        for j in range(p): W[i+1][j+1]=leg(j-i,p)
    return W
def rank_mod(M,p):
    M=[[x%p for x in r] for r in M]; r=0
    for c in range(len(M[0])):
        pr=next((i for i in range(r,len(M)) if M[i][c]),None)
        if pr is None: continue
        M[r],M[pr]=M[pr],M[r]; iv=pow(M[r][c],p-2,p); M[r]=[x*iv%p for x in M[r]]
        for i in range(len(M)):
            if i!=r and M[i][c]:
                f=M[i][c]; M[i]=[(x-f*y)%p for x,y in zip(M[i],M[r])]
        r+=1
    return r
for p in [3,5,7,11,13,17,19,23]:
    W=paley(p); n=p+1; k=(p+1)//2
    assert all(sum(W[i][t]*W[j][t] for t in range(n))==(p if i==j else 0) for i in range(n) for j in range(n))
    rk=rank_mod(W,p)
    # RS identification: row i+1 at column j+1 is (j-i)^((p-1)/2) mod p, a polynomial of degree k-1 in j;
    # column 0 scaled by eps carries leading coefficient (=1); row 0 = constant 1 with 0 at infinity.
    for i in range(p):
        assert all((W[i+1][j+1]-pow(j-i,(p-1)//2,p))%p==0 for j in range(p))
    # MDS check: every k-subset of columns of W has rank k  (n<=24 -> C(24,12)=2.7M too big for 23; sample full for p<=19)
    if p<=19:
        cols=list(zip(*W)); ok=all(rank_mod([list(cols[c]) for c in S],p)==k for S in itertools.combinations(range(n),k))
    else: ok='skipped(by RS argument)'
    print('paley p',p,'rank',rk,'k',k,'all k-column subsets independent:',ok)
