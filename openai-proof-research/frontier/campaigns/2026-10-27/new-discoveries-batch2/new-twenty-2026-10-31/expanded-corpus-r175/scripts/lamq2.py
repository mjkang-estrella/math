# Induced paths in Lambda_q (i<j adjacent iff j-i=1 or j-i = -1 mod q), word search with forced-future pruning.
import sys,time
q=int(sys.argv[1]); target=int(sys.argv[2]); budget=float(sys.argv[3])
deadline=time.time()+budget
L=target; best=[0,None]; nodes=[0]; timed=[False]
res=[0]*L; tight=[0]*L; deg=[0]*L; comp=[0]*L
def forbidden_next(k):
    # residue s is forbidden for any future vertex if class s+1 has a deg-2 vertex, >=3 vertices, or two vertices in one component
    fb=[False]*q
    for s in range(q):
        c=(s+1)%q; idx=[i for i in range(k) if res[i]==c]
        if len(idx)>=3 or any(deg[i]>=2 for i in idx) or len({comp[i] for i in idx})<len(idx): fb[s]=True
    return fb
def ok_state(k):
    fb=forbidden_next(k)
    comps={}
    perm_end=0
    for i in range(k):
        live = deg[i]<2 and ((not fb[(res[i]-1)%q]) or i==k-1)
        comps.setdefault(comp[i],[False])
        if live: comps[comp[i]][0]=True
        if not live and deg[i]<2: perm_end += (2-deg[i]) if deg[i]==0 else 1
    if perm_end>2: return False,fb
    dead=[c for c,v in comps.items() if not v[0]]
    if dead and (len(comps)>1): return False,fb
    return True,fb
def dfs(k):
    nodes[0]+=1
    if time.time()>deadline: timed[0]=True; return False
    ncomp=len(set(comp[:k]))
    if ncomp==1 and k>best[0]:
        best[0]=k; best[1]=(res[:k],tight[:k])
        if k>=target: return True
    if k==L: return False
    ok,fb=ok_state(k)
    if not ok: return False
    if ncomp-1 > L-k: return False
    for r in (range(q) if k>0 else [0]):
        if k>0 and fb[r] and not ((res[k-1]+1)%q==r and False): 
            continue
        for t in ((0,1) if (k>0 and (res[k-1]+1)%q==r) else (0,)):
            nbrs=[i for i in range(k) if res[i]==(r+1)%q]
            if t: nbrs.append(k-1)
            if len(nbrs)>2 or any(deg[i]>=2 for i in nbrs): continue
            cs={comp[i] for i in nbrs}
            if len(cs)<len(nbrs): continue
            res[k]=r; tight[k]=t; deg[k]=len(nbrs)
            for i in nbrs: deg[i]+=1
            old=comp[:k]
            for i in range(k):
                if comp[i] in cs: comp[i]=k
            comp[k]=k
            if dfs(k+1): return True
            comp[:k]=old
            for i in nbrs: deg[i]-=1
            deg[k]=0
    return False
found=dfs(0)
print('q',q,'target',target,'FOUND' if found else 'not found','longest path found',best[0],'nodes',nodes[0],'TIMEOUT' if timed[0] else 'complete',flush=True)
if best[1]: print('word',best[1][0],'tight',best[1][1])
