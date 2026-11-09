# Exhaustive search for counterexamples to Baek Conj. conj:interweaved via pair labellings s:(x<y)->{A=0,B=1}.
# Cap-maximal reduction: cap(xyz) iff s(xy)=B and s(yz)=A; cup otherwise (cup iff s(xy)=A or s(yz)=B).
# Any 4-cap-free configuration has cup set containing that of some labelling configuration; such labelling configurations
# are 4-cap free, inherit n-cup-freeness, and have fewer laced cups (all notions monotone in the cup set). Hence the
# conjecture holds for (n,k) iff it holds for all n-cup-free labelling configurations of size N=C(n-1,2)+k.
import sys, itertools, time
n,k=int(sys.argv[1]),int(sys.argv[2]); N=(n-1)*(n-2)//2+k
mode=sys.argv[3] if len(sys.argv)>3 else 'check'
s={}           # s[(x,y)]
end={}         # end[(x,y)] longest cup ending with edge xy
cnt=[0]; bad=[]; t0=time.time()
def cup(x,y,z): return s[(x,y)]==0 or s[(y,z)]==1
def check_full():
    # longest cup starting at each point, ending at each point
    Ein=[1]*N
    for (x,y),v in end.items(): Ein[y]=max(Ein[y],v)
    st={}
    for p in range(N-1,-1,-1):
        for y in range(N-1,p,-1):
            b=2
            for z in range(y+1,N):
                if cup(p,y,z): b=max(b,st[(y,z)]+1)
            st[(p,y)]=b
    Sout=[1]*N
    for (x,y),v in st.items(): Sout[x]=max(Sout[x],v)
    # (n-1)-cups: enumerate via DFS on edges
    pairs=set()
    def ext(seq):
        if len(seq)==n-1:
            p,q=seq[0],seq[-1]
            if Ein[p]+Sout[q]>=n-1: pairs.add((p,q))
            return
        for z in range(seq[-1]+1,N):
            if len(seq)<2 or cup(seq[-2],seq[-1],z): ext(seq+[z])
    for a in range(N): ext([a])
    best=0
    for t in range(N):
        P=sorted(x for x in pairs if x[0]<=t<=x[1]); L=[]
        for i,(a,b) in enumerate(P):
            L.append(1+max([L[j] for j in range(i) if P[j][0]<a and P[j][1]<b]+[0]))
        best=max(best,max(L+[0]))
    return best
hist={}
def dfs(p):
    if p==N:
        cnt[0]+=1
        if mode=='count': return
        b=check_full(); hist[b]=hist.get(b,0)+1
        if b<k and len(bad)<5: bad.append(dict(s))
        return
    for mask in range(1<<p):
        ok=True; newend=[]
        for x in range(p):
            s[(x,p)]=(mask>>x)&1
        for x in range(p):
            b=2
            for w in range(x):
                if cup(w,x,p): b=max(b,end[(w,x)]+1)
            if b>n-1: ok=False; break
            newend.append((x,b))
        if not ok: continue
        for x,b in newend: end[(x,p)]=b
        dfs(p+1)
    for x in range(p):
        s.pop((x,p),None); end.pop((x,p),None)
dfs(0)
print('n',n,'k',k,'N',N,'labellings (n-cup free)',cnt[0],'hist max-interweaved-laced',sorted(hist.items()),'counterexamples',len(bad),'time',round(time.time()-t0,1))
for b in bad: print('BAD',sorted(e for e,v in b.items() if v==1))
