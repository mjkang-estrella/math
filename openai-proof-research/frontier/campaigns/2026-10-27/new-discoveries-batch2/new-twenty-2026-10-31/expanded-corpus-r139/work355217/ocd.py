# 355217 (Kazemnejad-Pahlavsay-Palezzato-Torielli Conjecture 7.1): gamma~_c(G) < gamma~_c(M(G)).
# Outer-connected dominating set S: dominating and G-S connected (empty graph G-S counted as connected,
# following Cyman 2007 where S=V is allowed; we record both conventions).
import sys, itertools, json, pathlib
sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[1]/'scripts'))
from graphgen import connected
def conn_mask(adj, mask):
    if mask==0: return True
    s=mask & -mask; seen=s; fr=s
    while fr:
        nf=0; m=fr
        while m:
            b=m&-m; v=b.bit_length()-1; nf|=adj[v]; m^=b
        nf&=mask&~seen; seen|=nf; fr=nf
    return seen==mask
def ocd_number(adj, upto=None):
    n=len(adj); full=(1<<n)-1; cl=[adj[v]|(1<<v) for v in range(n)]
    top=n if upto is None else min(upto,n)
    for k in range(1,top+1):
        for S in itertools.combinations(range(n),k):
            m=0; sm=0
            for v in S: m|=cl[v]; sm|=1<<v
            if m==full and conn_mask(adj, full&~sm): return k
    return None
def middle(adj):
    n=len(adj); E=[(u,v) for u in range(n) for v in range(u+1,n) if adj[u]>>v&1]
    N=n+len(E); M=[0]*N
    def e(a,b): M[a]|=1<<b; M[b]|=1<<a
    for i,(u,v) in enumerate(E):
        e(u,n+i); e(v,n+i)
        for j in range(i):
            if set(E[j])&{u,v}: e(n+i,n+j)
    return M
if __name__=='__main__':
    nmax=int(sys.argv[1]); stats={}; bad=[]
    for n in range(2,nmax+1):
        gs=[tuple(map(int,l.split())) for l in open(f'graphs/g{n}.txt') if l.strip()]
        c=0; skipped=0; eq=[]
        for g in gs:
            if not connected(g): continue
            c+=1
            a=ocd_number(list(g))
            if a < (n+1)//2: skipped+=1; continue   # Theorem 4.1: gamma~c(M(G)) >= ceil(n/2)
            b=ocd_number(middle(list(g)), upto=a)
            if b is not None:  # b <= a: violation
                bad.append({'n':n,'adj':g,'ocd_G':a,'ocd_M_le':b})
        stats[n]={'connected':c,'decided_by_lower_bound':skipped}
        print(n,stats[n],len(bad),flush=True)
    print(json.dumps(bad[:20]))
