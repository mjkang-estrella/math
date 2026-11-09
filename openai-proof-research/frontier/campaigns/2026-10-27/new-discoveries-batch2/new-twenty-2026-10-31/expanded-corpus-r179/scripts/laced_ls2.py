# Reduced local search for Baek conj:interweaved (s(0,.)=B, s(.,N-1)=A WLOG) with a forward-checking generator. Not exhaustive.
import sys, random, time
n,k,seed,secs=int(sys.argv[1]),int(sys.argv[2]),int(sys.argv[3]),float(sys.argv[4]); N=(n-1)*(n-2)//2+k; m=n-1
rnd=random.Random(seed)
def stats(S):
    end=[[0]*N for _ in range(N)]; Ein=[1]*N
    for p in range(N):
        for x in range(p):
            b=2
            for w in range(x):
                if (S[w][x]==0 or S[x][p]==1) and end[w][x]+1>b: b=end[w][x]+1
            end[x][p]=b
            if b>Ein[p]: Ein[p]=b
    return Ein
def objective(S,Ein):
    st=[[0]*N for _ in range(N)]
    for p in range(N-1,-1,-1):
        for y in range(N-1,p,-1):
            b=2
            for z in range(y+1,N):
                if (S[p][y]==0 or S[y][z]==1) and st[y][z]+1>b: b=st[y][z]+1
            st[p][y]=b
    Sout=[max([1]+[st[p][y] for y in range(p+1,N)]) for p in range(N)]
    reach={(b,c):{b} for b in range(N) for c in range(b+1,N)}
    for l in range(3,m+1):
        new={}
        for b in range(N):
            for c in range(b+1,N):
                acc=set()
                for a in range(b):
                    if S[a][b]==0 or S[b][c]==1: acc|=reach[(a,b)]
                new[(b,c)]=acc
        reach=new
    pairs=set((f,c) for (b,c),fs in reach.items() for f in fs if Ein[f]+Sout[c]>=m)
    best=0
    for t in range(N):
        P=sorted(x for x in pairs if x[0]<=t<=x[1]); L=[]
        for i,(a,b) in enumerate(P):
            L.append(1+max([L[j] for j in range(i) if P[j][0]<a and P[j][1]<b]+[0]))
        if L: best=max(best,max(L))
    return best
def gen():
    S=[[0]*N for _ in range(N)]; Ein=[1]*N; EinA=[1]*N
    for p in range(N):
        for attempt in range(50):
            e=1; ea=1; ok=True
            for x in range(p):
                o=[]
                if EinA[x]+1<=m and (p==N-1 or EinA[x]+1<=m-1): o.append((0,EinA[x]+1))
                if Ein[x]+1<=m: o.append((1,Ein[x]+1))
                if x==0 and p!=N-1: o=[t for t in o if t[0]==1]
                elif p==N-1: o=[t for t in o if t[0]==0]
                if not o: return None
                lab,v=rnd.choice(o); S[x][p]=lab; e=max(e,v)
                if lab==0: ea=max(ea,v)
            if p==N-1 or not (e>=m and ea>=m-1): break
        else: return None
        Ein[p]=e; EinA[p]=ea
    return S
free=[(x,y) for x in range(1,N) for y in range(x+1,N-1)]
t0=time.time(); gens=0; valid=0; bestall=99
while time.time()-t0<secs:
    S=gen(); gens+=1
    if S is None: continue
    Ein=stats(S)
    if max(Ein)>m: continue
    valid+=1; f=objective(S,Ein)
    for it in range(300):
        x,y=rnd.choice(free); S[x][y]^=1; Ein2=stats(S)
        if max(Ein2)>m: S[x][y]^=1; continue
        f2=objective(S,Ein2)
        if f2<=f: f=f2
        else: S[x][y]^=1
        if f<k or time.time()-t0>secs: break
    bestall=min(bestall,f)
    if f<k: print('COUNTEREXAMPLE n',n,'k',k,'B-pairs',[(a,b) for a in range(N) for b in range(a+1,N) if S[a][b]==1],flush=True); break
print('n',n,'k',k,'N',N,'seed',seed,'generated',gens,'valid starts',valid,'best objective',bestall,'time',round(time.time()-t0,1))
