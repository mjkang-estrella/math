# Pure-python generation of all graphs on n vertices up to isomorphism by vertex augmentation
# with canonical forms via colour refinement + individualisation (no pruning). Graph = tuple of
# adjacency bitmasks. Output: one line per graph, adjacency masks as ints (canonical labelling).
import sys, itertools
def refine(adj, colors):
    n=len(adj)
    while True:
        sig=[(colors[v], tuple(sorted(colors[w] for w in range(n) if adj[v]>>w&1))) for v in range(n)]
        keys=sorted(set(sig)); idx={k:i for i,k in enumerate(keys)}
        new=[idx[s] for s in sig]
        if len(keys)==len(set(colors)): return new
        colors=new
def canon(adj):
    n=len(adj); best=[None]
    def leaf(colors):
        perm=sorted(range(n),key=lambda v:colors[v])  # position i -> vertex perm[i]
        pos=[0]*n
        for i,v in enumerate(perm): pos[v]=i
        code=tuple(sum(1<<pos[w] for w in range(n) if adj[v]>>w&1) for v in perm)
        if best[0] is None or code<best[0]: best[0]=code
    def rec(colors):
        colors=refine(adj,colors)
        if len(set(colors))==n: leaf(colors); return
        cnt={}
        for c in colors: cnt[c]=cnt.get(c,0)+1
        tc=min(c for c in cnt if cnt[c]>1)
        for v in range(n):
            if colors[v]==tc:
                nc=[2*c for c in colors]; nc[v]=2*tc-1
                rec(nc)
    rec([bin(a).count('1') for a in adj])
    return best[0]
def extend(graphs, n):
    out=set()
    for g in graphs:
        for S in range(1<<(n-1)):
            adj=list(g)+[S]
            for w in range(n-1):
                if S>>w&1: adj[w]|=1<<(n-1)
            out.add(canon(adj))
    return out
def connected(adj):
    n=len(adj); seen=1; fr=1
    while fr:
        nf=0
        for v in range(n):
            if fr>>v&1: nf|=adj[v]
        nf&=~seen; seen|=nf; fr=nf
    return seen==(1<<n)-1
if __name__=='__main__':
    import pathlib, time
    N=int(sys.argv[1]); out=pathlib.Path(sys.argv[2])
    prev=out/f'g{N-1}.txt'
    gs=[tuple(map(int,l.split())) for l in prev.read_text().split('\n') if l.strip()] if N>1 else [()]
    if N==1: res={(0,)}
    else: res=extend(gs,N)
    (out/f'g{N}.txt').write_text('\n'.join(' '.join(map(str,g)) for g in sorted(res))+'\n')
    print(N,len(res),sum(1 for g in res if connected(g)))
