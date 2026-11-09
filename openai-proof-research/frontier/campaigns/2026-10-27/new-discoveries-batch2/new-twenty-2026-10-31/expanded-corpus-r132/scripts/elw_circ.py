# Screen circulant graphs Cay(Z_n, S) for ELW violations: s_l/m - 2(1-1/w), l=min(n+,w).
import sys,math,itertools,json
sys.path.insert(0,__file__.rsplit('/',1)[0])
def omega_circ(n,S):
    Sset=set(S)|{(-s)%n for s in S}
    adj=[set((v+s)%n for s in Sset) for v in range(n)]
    best=[0]
    def ext(R,P):
        if len(R)+len(P)<=best[0]: return
        if not P: best[0]=max(best[0],len(R)); return
        for v in sorted(P):
            if len(R)+len(P)<=best[0]: return
            ext(R+[v],P&adj[v]); P=P-{v}
    ext([0],adj[0]); return best[0]
N0=int(sys.argv[1]); N1=int(sys.argv[2]); top=[]
for n in range(N0,N1+1):
    half=list(range(1,n//2+1))
    for r in range(1,len(half)+1):
        for S in itertools.combinations(half,r):
            Sset=set(S)|{(-s)%n for s in S}
            deg=len(Sset); m=n*deg/2
            ev=sorted((sum(math.cos(2*math.pi*j*s/n) for s in Sset) for j in range(n)),reverse=True)
            npos=sum(1 for e in ev if e>1e-9)
            if npos<2: continue
            w=omega_circ(n,S); l=min(npos,w)
            val=sum(e*e for e in ev[:l])/m-2*(1-1/w)
            top.append((val,n,S,w,npos))
    top.sort(reverse=True); top=top[:10]
    print(n,json.dumps(top[:3]),flush=True)
