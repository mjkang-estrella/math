# Independent exact check: (a) brute-force Dyck enumeration for n<=11, (b) exact big-int
# continued-fraction series for n<=N, compared with the mod 2^64 DP of catalan_scan.py.
import sys,itertools,importlib.util,math
N=int(sys.argv[1]); K=int(sys.argv[2])
def brute(n,b):
    tot=0
    def rec(h,steps,w):
        nonlocal tot
        if steps==2*n:
            if h==0: tot+=w
            return
        if h+1<=2*n-steps-1: rec(h+1,steps+1,w*b(h))
        if h>0: rec(h-1,steps+1,w)
    rec(0,0,1); return tot
def series_cf(b,N):
    # F_h = 1/(1 - b(h) x F_{h+1}); truncate at depth N (paths of semilength<=N never reach height>N)
    F=[1]+[0]*N
    for h in range(N,-1,-1):
        # G = 1 - b(h) x F
        G=[1]+[-b(h)*F[i] for i in range(N)]
        # invert G
        inv=[0]*(N+1); inv[0]=1
        for i in range(1,N+1):
            inv[i]=-sum(G[j]*inv[i-j] for j in range(1,i+1))
        F=inv
    return F
def v2(x):
    return (x&-x).bit_length()-1
def s2(n): return bin(n).count('1')
for k in range(1,K+1):
    b=lambda h,k=k:(2*h+1)**(2*k)
    S=series_cf(b,N); C=[math.comb(2*n,n)//(n+1) for n in range(N+1)]
    for n in range(0,12):
        assert brute(n,b)==S[n],(k,n)
    print(k,[v2(S[n]-C[n])-s2(n) for n in range(2,N+1)])
