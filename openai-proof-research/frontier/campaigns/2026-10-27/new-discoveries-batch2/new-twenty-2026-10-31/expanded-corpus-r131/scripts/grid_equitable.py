# Exhaustive enumeration of equitable partitions of P_m x P_n (restricted-growth colourings in
# row-major order with exact pruning), compared with orbit partitions of subgroups of the
# explicit group A0 (Z2xZ2, or D4 when m=n; Z2 for paths).
import sys, itertools, json
def grid(m,n):
    V=[(i,j) for i in range(m) for j in range(n)]
    idx={v:k for k,v in enumerate(V)}
    N=[[idx[(i+di,j+dj)] for di,dj in ((1,0),(-1,0),(0,1),(0,-1)) if (i+di,j+dj) in idx] for (i,j) in V]
    return V,idx,N
def A0(m,n):
    V,idx,N=grid(m,n)
    maps=[lambda i,j:(i,j),lambda i,j:(m-1-i,j),lambda i,j:(i,n-1-j),lambda i,j:(m-1-i,n-1-j)]
    if m==n: maps+= [lambda i,j:(j,i),lambda i,j:(n-1-j,i),lambda i,j:(j,n-1-i),lambda i,j:(n-1-j,m-1-i)]
    G=set()
    for f in maps: G.add(tuple(idx[f(i,j)] for (i,j) in V))
    return sorted(G)
def subgroups(G):
    G=[tuple(g) for g in G]; e=tuple(range(len(G[0])))
    comp=lambda a,b: tuple(a[b[k]] for k in range(len(a)))
    subs=set()
    for r in range(len(G)+1):
        for S in itertools.combinations(G,r):
            H=set(S)|{e}; ch=True
            while ch:
                ch=False
                for a in list(H):
                    for b in list(H):
                        c=comp(a,b)
                        if c not in H: H.add(c); ch=True
            subs.add(frozenset(H))
    return subs
def orbit_partition(H,nv):
    lab=[None]*nv; c=0; out=[0]*nv
    for v in range(nv):
        if lab[v] is None:
            for h in H: lab[h[v]]=c
            c+=1
    return tuple(lab)
def canon(col):
    m={}; return tuple(m.setdefault(x,len(m)) for x in col)
def equitable_partitions(m,n):
    V,idx,N=grid(m,n); nv=len(V)
    # vertex k becomes "complete" when all its neighbours (indices <= k+n) are coloured
    lastnb=[max(N[k]+[k]) for k in range(nv)]
    complete_at={}
    for k in range(nv): complete_at.setdefault(lastnb[k],[]).append(k)
    col=[None]*nv; res=[]
    sig={}  # colour -> neighbour-colour multiset of a complete vertex
    def nbsig(k): return tuple(sorted(col[x] for x in N[k]))
    def rec(k,ncol,sigs):
        if k==nv:
            # all complete; verify equitable fully
            s={}
            for v in range(nv):
                t=nbsig(v)
                if s.setdefault(col[v],t)!=t: return
            res.append(tuple(col)); return
        for c in range(ncol+1):
            if len(N[k])!=len(N[k]) : pass
            col[k]=c
            ok=True; added=[]
            for v in complete_at.get(k,[]):
                t=nbsig(v)
                if col[v] in sigs:
                    if sigs[col[v]]!=t: ok=False; break
                else:
                    sigs[col[v]]=t; added.append(col[v])
            # degree pruning: same colour needs same degree
            if ok:
                for v in range(k):
                    if col[v]==c and len(N[v])!=len(N[k]): ok=False; break
            if ok: rec(k+1,max(ncol,c+1),sigs)
            for a in added: del sigs[a]
            col[k]=None
    rec(0,0,{})
    return set(res)
if __name__=='__main__':
    maxv=int(sys.argv[1]); report={}
    minv=int(sys.argv[3]) if len(sys.argv)>3 else 0
    for m in range(1,8):
        for n in range(m,21):
            if m*n>maxv or m*n<minv: continue
            # enumerate on the isomorphic n x m grid (short rows => small completion lag)
            E=equitable_partitions(n,m)
            G=A0(n,m); S=subgroups(G)
            O={canon(orbit_partition(H,m*n)) for H in S}
            E={canon(e) for e in E}
            triv=any(len({g[v] for g in G})==len(G) for v in range(m*n))
            report[f'{m}x{n}']=dict(equitable=len(E),orbit_partitions=len(O),equal=(E==O),subgroups_of_A0=len(S),trivial_stabilizer_vertex=triv)
            print(m,n,report[f'{m}x{n}'],flush=True)
    json.dump(report,open(sys.argv[2],'w'),indent=1)
