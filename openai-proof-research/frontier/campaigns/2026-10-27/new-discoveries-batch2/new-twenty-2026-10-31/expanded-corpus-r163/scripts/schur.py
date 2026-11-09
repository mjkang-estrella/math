# 340618: Long-Wagner Conjecture 1.7. ST(A)=#{(x,y,z) in A^3: x+y=z mod 2^n}.
import sys, itertools, random
def layers(n):
    N=1<<n; L=[]
    for i in range(1,n+1): L.append([x for x in range(N) if x%(1<<i)==(1<<(i-1))])
    L.append([0]); return L
def ST(A,N):
    s=set(A); return sum(1 for x in A for y in A if (x+y)%N in s)
def centred_min(n,M):
    N=1<<n; L=layers(n); best=None; arg=None
    pre=[]
    for i in range(len(L)):
        base=sum(len(L[j]) for j in range(i))
        if base<=M<=base+len(L[i]):
            r=M-base
            fixed=[x for j in range(i) for x in L[j]]
            for c in itertools.combinations(L[i],r):
                v=ST(fixed+list(c),N)
                if best is None or v<best: best=v; arg=fixed+list(c)
    return best,arg
mode=sys.argv[1]; n=int(sys.argv[2]); N=1<<n
if mode=='exh':
    mins={}
    for mask in range(1<<N):
        A=[x for x in range(N) if mask>>x&1]
        v=ST(A,N); M=len(A)
        if M not in mins or v<mins[M][0]: mins[M]=(v,A)
    for M in range(N+1):
        c=centred_min(n,M)[0]
        print(M,'global',mins[M][0],'centred',c,'OK' if c==mins[M][0] else 'VIOLATION '+str(mins[M][1]),flush=True)
else:
    seed=int(sys.argv[3]); random.seed(seed); iters=int(sys.argv[4])
    Ms=range(N//2+1,N+1) if len(sys.argv)<6 else [int(x) for x in sys.argv[5].split(',')]
    for M in Ms:
        c,ca=centred_min(n,M)
        best=None
        for rep in range(3):
            A=set(random.sample(range(N),M)); v=ST(list(A),N)
            for it in range(iters):
                x=random.choice(list(A)); y=random.choice([z for z in range(N) if z not in A])
                B=(A-{x})|{y}; w=ST(list(B),N)
                if w<=v: A,v=B,w
            if best is None or v<best[0]: best=(v,sorted(A))
        flag='VIOLATION' if best[0]<c else ''
        print(M,'local',best[0],'centred',c,flag,best[1] if flag else '',flush=True)
