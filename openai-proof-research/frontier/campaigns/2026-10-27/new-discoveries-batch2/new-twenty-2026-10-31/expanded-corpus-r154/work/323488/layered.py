# Decide whether a k-crossing-free antichain of size T exists in {0..R}^w whose coordinate-0 values are exactly {0..R}
# (all layers nonempty). Method: DFS over transversals (one vector per layer, minimum-remaining-values layer order),
# then a clique of size T-(R+1) in the common neighbourhood.
import sys,itertools,time,json
k=int(sys.argv[1]); w=int(sys.argv[2]); R=int(sys.argv[3]); T=int(sys.argv[4]); tlim=float(sys.argv[5])
V=list(itertools.product(range(R+1),repeat=w)); N=len(V)
def compat(A,B):
    pos=neg=bigp=bign=False
    for a,b in zip(A,B):
        d=a-b
        if d>0:
            pos=True
            if d>=k: bigp=True
        elif d<0:
            neg=True
            if d<=-k: bign=True
    return pos and neg and not(bigp and bign)
nb=[0]*N
for i in range(N):
    Ai=V[i]
    for j in range(i+1,N):
        if compat(Ai,V[j]): nb[i]|=1<<j; nb[j]|=1<<i
VAL=[0]*(R+1)
for i in range(N): VAL[V[i][0]]|=1<<i
start=time.time(); nodes=0; found=None; timed_out=False; ntrans=0
def clique_in(P,s):
    # return a clique of size s inside bitset P, or None
    if s==0: return []
    while P:
        if P.bit_count()<s: return None
        v=(P&-P).bit_length()-1; P&=~(1<<v)
        r=clique_in(P&nb[v],s-1)
        if r is not None: return [v]+r
    return None
def dfs(C,P,L):
    global nodes,found,timed_out,ntrans
    nodes+=1
    if nodes%5000==0 and time.time()-start>tlim: timed_out=True; return
    if not L:
        ntrans+=1
        r=clique_in(P,T-len(C))
        if r is not None: found=C+r
        return
    if P.bit_count()<T-len(C): return
    best=None;bc=10**9
    for c in L:
        x=(VAL[c]&P).bit_count()
        if x<bc: bc=x;best=c
        if x==0: return
    c=best; L2=[x for x in L if x!=c]; Q=VAL[c]&P
    while Q:
        v=(Q&-Q).bit_length()-1; Q&=~(1<<v)
        dfs(C+[v],P&nb[v],L2)
        if found or timed_out: return
dfs([],(1<<N)-1,list(range(R+1)))
print(json.dumps({'k':k,'w':w,'R':R,'T':T,'N':N,'found':[V[i] for i in found] if found else None,'transversals':ntrans,'nodes':nodes,'timed_out':timed_out,'secs':round(time.time()-start,1)}))
