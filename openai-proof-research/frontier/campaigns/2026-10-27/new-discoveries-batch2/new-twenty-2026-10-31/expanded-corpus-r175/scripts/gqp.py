# Longest induced path in G_{q,p} (Goedgebeur et al. arXiv:2404.11704 Sec. 6): vertices Z_{qp-2}, N(i) = {i-1,i+1} u {i+qj-1 : j in [p-1]} (mod qp-2), symmetrized.
import sys,time
def graph(q,p):
    n=q*p-2; S={1,n-1}|{(q*j-1)%n for j in range(1,p)}|{(-(q*j-1))%n for j in range(1,p)}
    S.discard(0)
    nb=[0]*n
    for i in range(n):
        for s in S: nb[i]|=1<<((i+s)%n)
    return n,nb
def check_def(q,p):
    # verify edge relation agrees with the printed N(i) (union over both endpoints) for this n
    n=q*p-2; E=set()
    for i in range(n):
        for j in [i-1,i+1]+[i+q*t-1 for t in range(1,p)]:
            j%=n
            if j!=i: E.add(frozenset((i,j)))
    n2,nb=graph(q,p)
    E2={frozenset((i,j)) for i in range(n) for j in range(n) if nb[i]>>j&1}
    return E==E2
def longest(q,p,target,deadline):
    n,nb=graph(q,p); best=[0,None]; nodes=[0]
    closed=[nb[i]|1<<i for i in range(n)]
    def dfs(path,blocked):
        nodes[0]+=1
        k=len(path)
        if k>best[0]: best[0]=k; best[1]=list(path)
        if best[0]>=target or time.time()>deadline: return
        last=path[-1]
        cand=nb[last]&~blocked
        while cand:
            b=cand&-cand; v=b.bit_length()-1; cand^=b
            path.append(v); dfs(path,blocked|closed[last]); path.pop()
            if best[0]>=target or time.time()>deadline: return
    dfs([0],0)
    return best,nodes[0],time.time()>deadline
if __name__=='__main__':
    q=int(sys.argv[1]); p0,p1=int(sys.argv[2]),int(sys.argv[3]); target=int(sys.argv[4]); budget=float(sys.argv[5])
    t0=time.time()
    for p in range(p0,p1+1):
        assert check_def(q,p)
        best,nodes,to=longest(q,p,target,time.time()+budget)
        print('q',q,'p',p,'n',q*p-2,'longest induced path found',best[0],'nodes',nodes,'TIMEOUT' if to else 'complete','path',best[1] if best[0]>=target else '',flush=True)
