# Count components of FS(K_{2,n-2}, Y) for connected bipartite Y with no non-trivial cut edge, Y != C_n.
import sys,os,itertools,time
sys.path.insert(0,os.path.dirname(os.path.abspath(__file__)))
from g6 import g6decode
def is_bip(n,adj):
    col=[-1]*n; col[0]=0; st=[0]
    while st:
        u=st.pop()
        for v in range(n):
            if adj[u]>>v&1:
                if col[v]==-1: col[v]=1-col[u]; st.append(v)
                elif col[v]==col[u]: return False
    return True
def connected_without(n,adj,u,v):
    seen=1; st=[0]
    while st:
        x=st.pop()
        for y in range(n):
            if adj[x]>>y&1 and not ((x,y)==(u,v) or (x,y)==(v,u)) and not seen>>y&1:
                seen|=1<<y; st.append(y)
    return seen==(1<<n)-1
def nontrivial_cut_edge(n,adj):
    deg=[bin(a).count('1') for a in adj]
    for u in range(n):
        for v in range(u+1,n):
            if adj[u]>>v&1 and deg[u]>1 and deg[v]>1 and not connected_without(n,adj,u,v): return True
    return False
def is_cycle(n,adj):
    return all(bin(a).count('1')==2 for a in adj)
def fs_components(n,Xedges,adj):
    perms=list(itertools.permutations(range(n)))
    idx={p:i for i,p in enumerate(perms)}
    par=list(range(len(perms)))
    def find(x):
        while par[x]!=x: par[x]=par[par[x]]; x=par[x]
        return x
    comps=len(perms)
    for i,p in enumerate(perms):
        for (a,b) in Xedges:
            if adj[p[a]]>>p[b]&1:
                q=list(p); q[a],q[b]=q[b],q[a]; j=idx[tuple(q)]
                if j>i:
                    ri,rj=find(i),find(j)
                    if ri!=rj: par[ri]=rj; comps-=1
    return comps
if __name__=='__main__':
    f=sys.argv[1]; a=int(sys.argv[2]); b=int(sys.argv[3])
    t0=time.time()
    for li,line in enumerate(open(f)):
        if li<a: continue
        if li>=b: break
        n,adj=g6decode(line)
        if not is_bip(n,adj) or nontrivial_cut_edge(n,adj) or is_cycle(n,adj): continue
        Xedges=[(i,j) for i in range(2) for j in range(2,n)]
        c=fs_components(n,Xedges,adj)
        print(li,line.strip(),'components',c,('***' if c!=2 else ''),flush=True)
    print('done',a,b,round(time.time()-t0,1))
