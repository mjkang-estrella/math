# Local search over valid (n-cup-free) pair labellings (same reduction as laced_exh.py) minimising the maximum number of
# mutually interweaved laced (n-1)-cups; target < k. Not exhaustive.
import sys, random, time, itertools
n,k,seed,secs=int(sys.argv[1]),int(sys.argv[2]),int(sys.argv[3]),float(sys.argv[4]); N=(n-1)*(n-2)//2+k
rnd=random.Random(seed); m=n-1
pairs_all=[(x,y) for x in range(N) for y in range(x+1,N)]
RED=len(sys.argv)>5 and sys.argv[5]=='red'
free=[(x,y) for (x,y) in pairs_all if not (RED and (x==0 or y==N-1))]
def stats(S):
    end=[[0]*N for _ in range(N)]; Ein=[1]*N
    for p in range(N):
        for x in range(p):
            b=2
            for w in range(x):
                if S[w][x]==0 or S[x][p]==1:
                    if end[w][x]+1>b: b=end[w][x]+1
            end[x][p]=b
            if b>Ein[p]: Ein[p]=b
    return end,Ein
def valid(S):
    end,Ein=stats(S); return max(Ein)<=m, Ein
def objective(S,Ein):
    st=[[0]*N for _ in range(N)]
    for p in range(N-1,-1,-1):
        for y in range(N-1,p,-1):
            b=2
            for z in range(y+1,N):
                if S[p][y]==0 or S[y][z]==1:
                    if st[y][z]+1>b: b=st[y][z]+1
            st[p][y]=b
    Sout=[max([1]+[st[p][y] for y in range(p+1,N)]) for p in range(N)]
    # (n-1)-cups via DP on (edge, length) reachability from first point: cupstart[a][b][l] set of first points
    reach={}  # (b,c,l)->set of first points of cups of length l ending with edge bc
    for b in range(N):
        for c in range(b+1,N): reach[(b,c,2)]={b}
    pairs=set()
    for l in range(3,m+1):
        for b in range(N):
            for c in range(b+1,N):
                acc=set()
                for a in range(b):
                    if S[a][b]==0 or S[b][c]==1: acc|=reach[(a,b,l-1)]
                reach[(b,c,l)]=acc
    for b in range(N):
        for c in range(b+1,N):
            for f in reach[(b,c,m)]:
                if Ein[f]+Sout[c]>=m: pairs.add((f,c))
    best=0
    for t in range(N):
        P=sorted(x for x in pairs if x[0]<=t<=x[1]); L=[]
        for i,(a,b) in enumerate(P):
            L.append(1+max([L[j] for j in range(i) if P[j][0]<a and P[j][1]<b]+[0]))
        if L: best=max(best,max(L))
    return best
def random_valid():
    S=[[0]*N for _ in range(N)]; Ein=[1]*N; EinA=[1]*N
    for p in range(N):
        e=1; ea=1
        for x in range(p):
            o=[]
            if EinA[x]+1<=m: o.append((0,EinA[x]+1))
            if Ein[x]+1<=m: o.append((1,Ein[x]+1))
            if not o: return None
            if RED and x==0 and p!=N-1: o=[t for t in o if t[0]==1]
            elif RED and p==N-1: o=[t for t in o if t[0]==0]
            if not o: return None
            lab,v=rnd.choice(o); S[x][p]=lab; e=max(e,v)
            if lab==0: ea=max(ea,v)
        Ein[p]=e; EinA[p]=ea
    return S
t0=time.time(); bestall=99; tries=0
while time.time()-t0<secs:
    S=random_valid(); tries+=1
    if S is None: continue
    ok,Ein=valid(S); f=objective(S,Ein)
    for it in range(400):
        x,y=rnd.choice(free); S[x][y]^=1
        ok,Ein2=valid(S)
        if not ok: S[x][y]^=1; continue
        f2=objective(S,Ein2)
        if f2<=f: f=f2
        else: S[x][y]^=1
        if f<k: break
        if time.time()-t0>secs: break
    bestall=min(bestall,f)
    if f<k:
        print('COUNTEREXAMPLE n',n,'k',k,'B-pairs',[(a,b) for a,b in pairs_all if S[a][b]==1],flush=True); break
print('n',n,'k',k,'N',N,'seed',seed,'starts',tries,'best objective',bestall,'time',round(time.time()-t0,1))
