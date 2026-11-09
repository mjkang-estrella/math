# Faster version of laced_exh.py (same reduction). Per new point p and earlier x:
#  s(x,p)=B(1): end(x,p)=1+Ein[x]  (all w give cups; Ein[x]=longest cup ending at x, >=1)
#  s(x,p)=A(0): end(x,p)=1+EinA[x] (EinA[x]=max end(w,x) over w with s(w,x)=A, or 1 if none)
# n-cup-free iff every end<=n-1. REDUCTION (monotone, cup sets only shrink): s(0,y)=B and s(x,N-1)=A WLOG. Optional prefix split: argv[4]=modulus, argv[5]=residue on the top-level branch counter at depth argv[6].
import sys, time
n,k=int(sys.argv[1]),int(sys.argv[2]); N=(n-1)*(n-2)//2+k; mode=sys.argv[3]
RED=mode.endswith('-red'); mode=mode.replace('-red','')
mod=int(sys.argv[4]) if len(sys.argv)>4 else 1; res=int(sys.argv[5]) if len(sys.argv)>5 else 0; SD=int(sys.argv[6]) if len(sys.argv)>6 else 0
S=[[0]*N for _ in range(N)]; END=[[0]*N for _ in range(N)]
Ein=[1]*N; EinA=[1]*N
cnt=[0]; hist={}; bad=[]; branch=[0]; t0=time.time()
def check_full():
    st=[[0]*N for _ in range(N)]
    for p in range(N-1,-1,-1):
        for y in range(N-1,p,-1):
            b=2
            spy=S[p][y]
            for z in range(y+1,N):
                if spy==0 or S[y][z]==1:
                    if st[y][z]+1>b: b=st[y][z]+1
            st[p][y]=b
    Sout=[max([1]+[st[p][y] for y in range(p+1,N)]) for p in range(N)]
    pairs=set(); m=n-1
    def ext(a,b,l,first):
        if l==m:
            if Ein[first]+Sout[b]>=m: pairs.add((first,b))
            return
        sab=S[a][b]
        for z in range(b+1,N):
            if sab==0 or S[b][z]==1: ext(b,z,l+1,first)
    for a in range(N):
        for b in range(a+1,N): ext(a,b,2,a)
    best=0
    for t in range(N):
        P=sorted(x for x in pairs if x[0]<=t<=x[1]); L=[]
        for i,(a,b) in enumerate(P):
            L.append(1+max([L[j] for j in range(i) if P[j][0]<a and P[j][1]<b]+[0]))
        if L and max(L)>best: best=max(L)
        if best>=k: return best
    return best
def dfs(p):
    if p==N:
        cnt[0]+=1
        if mode=='count': return
        b=check_full(); hist[b]=hist.get(b,0)+1
        if b<k and len(bad)<5: bad.append([(x,y) for x in range(N) for y in range(x+1,N) if S[x][y]==1])
        return
    opts=[]
    for x in range(p):
        o=[]
        if EinA[x]+1<=n-1 and (not RED or p==N-1 or EinA[x]+1<=n-2): o.append((0,EinA[x]+1))
        if Ein[x]+1<=n-1: o.append((1,Ein[x]+1))
        if RED:
            if x==0 and p!=N-1: o=[t for t in o if t[0]==1]
            elif p==N-1: o=[t for t in o if t[0]==0]
            elif False: pass
        if not o: return
        opts.append(o)
    # iterate over product
    idx=[0]*p
    while True:
        if p==SD:
            branch[0]+=1
            go = (branch[0]%mod==res)
        else: go=True
        if go:
            e=1; ea=1
            for x in range(p):
                lab,v=opts[x][idx[x]]; S[x][p]=lab; END[x][p]=v
                if v>e: e=v
                if lab==0 and v>ea: ea=v
            Ein[p]=e; EinA[p]=ea
            # forward check (exact necessary condition): a point with Ein=n-1 and EinA=n-2 forces EinA=n-1 on every later
            # point, which is only allowed for the last point; so such p must satisfy p>=N-2.
            if not (RED and p<N-2 and e>=n-1 and ea>=n-2): dfs(p+1)
        j=0
        while j<p:
            idx[j]+=1
            if idx[j]<len(opts[j]): break
            idx[j]=0; j+=1
        if j==p: break
dfs(0)
print('n',n,'k',k,'N',N,'mode',mode,'split',mod,res,SD,'labellings',cnt[0],'hist',sorted(hist.items()),'counterexamples',len(bad),'time',round(time.time()-t0,1),flush=True)
for b in bad: print('BAD B-pairs',b)
