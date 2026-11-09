# Induced paths in the infinite graph Lambda_q on Z: i<j adjacent iff j-i=1 or j-i = -1 (mod q).
# A finite induced subgraph = residue word r_1..r_L (positions increasing) + 'tight' flags (x_{k+1}=x_k+1, needs r_{k+1}=r_k+1).
# Edges k<l: r_l = r_k - 1 (mod q), or (l=k+1 and tight). Equivalent to induced subgraphs of G_{q,p} for p large (see notes).
import sys,time
q=int(sys.argv[1]); target=int(sys.argv[2]); budget=float(sys.argv[3])
deadline=time.time()+budget
best=[0,None]; nodes=[0]
L=target
res=[0]*L; tight=[0]*L; deg=[0]*L; par=list(range(L)); adj=[[] for _ in range(L)]
def find(x):
    while par[x]!=x: x=par[x]
    return x
def dfs(k,ncomp):
    # k vertices placed; ncomp components
    nodes[0]+=1
    if ncomp==1 and k>best[0]:
        best[0]=k; best[1]=(res[:k],tight[:k])
        if k>=target: return True
    if k==L or time.time()>deadline: return False
    # pruning: need to merge ncomp components into 1 using remaining L-k vertices; each new vertex reduces components by at most 1
    # (a new vertex joining two components reduces by 1, net). Only prune for target attempt:
    if (ncomp-1) > (L-k): return False
    for r in (range(q) if k>0 else [0]):
        for t in ((0,1) if (k>0 and (res[k-1]+1)%q==r) else (0,)):
            nbrs=[i for i in range(k) if res[i]==(r+1)%q]
            if t: nbrs.append(k-1)
            if len(nbrs)>2: continue
            if any(deg[i]>=2 for i in nbrs): continue
            roots=[find(i) for i in nbrs]
            if len(set(roots))<len(roots): continue   # cycle
            # also: future vertices with residue r-1 will be adjacent to ALL earlier residue-r vertices; fine (checked then)
            res[k]=r; tight[k]=t
            saved=[(i,par[i]) for i in roots]
            for i in nbrs: deg[i]+=1
            deg[k]=len(nbrs)
            for rt in roots: par[rt]=k
            if dfs(k+1,ncomp+1-len(nbrs)): return True
            for i in nbrs: deg[i]-=1
            for i,pv in saved: par[i]=pv
            par[k]=k; deg[k]=0
    return False
found=dfs(0,0)
print('q',q,'target',target,'FOUND' if found else 'not found','longest connected (path) found',best[0],'nodes',nodes[0],'TIMEOUT' if time.time()>deadline else 'complete')
if best[1]: print('word',best[1][0],'tight',best[1][1])
