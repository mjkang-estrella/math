# Chunked exhaustive search for induced P_target in Lambda_q. Usage: lamq3.py q target depth lo hi budget
# Enumerates all pruned-feasible prefixes of length 'depth' (deterministic order), searches prefixes [lo,hi).
import sys,time,pathlib
q,target,D,lo,hi,budget=int(sys.argv[1]),int(sys.argv[2]),int(sys.argv[3]),int(sys.argv[4]),int(sys.argv[5]),float(sys.argv[6])
L=target
res=[0]*L; tight=[0]*L; deg=[0]*L; comp=[0]*L
stats={'nodes':0}
def forbidden_next(k):
    fb=[False]*q
    for s in range(q):
        c=(s+1)%q; idx=[i for i in range(k) if res[i]==c]
        if len(idx)>=3 or any(deg[i]>=2 for i in idx) or len({comp[i] for i in idx})<len(idx): fb[s]=True
    return fb
def ok_state(k):
    fb=forbidden_next(k); comps={}; perm_end=0
    for i in range(k):
        live = deg[i]<2 and ((not fb[(res[i]-1)%q]) or i==k-1)
        comps.setdefault(comp[i],[False])
        if live: comps[comp[i]][0]=True
        if not live and deg[i]<2: perm_end += 2 if deg[i]==0 else 1
    if perm_end>2: return False,fb
    if any(not v[0] for v in comps.values()) and len(comps)>1: return False,fb
    return True,fb
def children(k,fb):
    for r in (range(q) if k>0 else [0]):
        if k>0 and fb[r]: continue
        for t in ((0,1) if (k>0 and (res[k-1]+1)%q==r) else (0,)):
            nbrs=[i for i in range(k) if res[i]==(r+1)%q]
            if t: nbrs.append(k-1)
            if len(nbrs)>2 or any(deg[i]>=2 for i in nbrs): continue
            cs={comp[i] for i in nbrs}
            if len(cs)<len(nbrs): continue
            yield r,t,nbrs,cs
def push(k,r,t,nbrs,cs):
    res[k]=r; tight[k]=t; deg[k]=len(nbrs)
    for i in nbrs: deg[i]+=1
    old=comp[:k]
    for i in range(k):
        if comp[i] in cs: comp[i]=k
    comp[k]=k
    return old
def pop(k,nbrs,old):
    comp[:k]=old
    for i in nbrs: deg[i]-=1
    deg[k]=0
found=[None]; deadline=[0]
class Timeout(Exception): pass
def dfs(k):
    stats['nodes']+=1
    if stats['nodes']&4095==0 and time.time()>deadline[0]: raise Timeout
    ncomp=len(set(comp[:k]))
    if k==L:
        if ncomp==1: found[0]=(res[:],tight[:]); return True
        return False
    ok,fb=ok_state(k)
    if not ok or ncomp-1>L-k: return False
    for r,t,nbrs,cs in list(children(k,fb)):
        old=push(k,r,t,nbrs,cs)
        if dfs(k+1): return True
        pop(k,nbrs,old)
    return False
# enumerate prefixes
prefixes=[]
def gen(k):
    if k==D: prefixes.append((res[:D],tight[:D])); return
    ok,fb=ok_state(k)
    if not ok: return
    for r,t,nbrs,cs in list(children(k,fb)):
        old=push(k,r,t,nbrs,cs); gen(k+1); pop(k,nbrs,old)
gen(0)
print('q',q,'target',target,'depth',D,'prefixes',len(prefixes),flush=True)
def load(pr):
    for i in range(L): res[i]=0;tight[i]=0;deg[i]=0;comp[i]=i
    k=0
    for r,t in zip(*pr):
        ok,fb=ok_state(k)
        for rr,tt,nbrs,cs in children(k,fb):
            if (rr,tt)==(r,t): push(k,rr,tt,nbrs,cs); break
        else: raise RuntimeError('bad prefix')
        k+=1
t0=time.time(); deadline[0]=t0+budget; done=lo
try:
    for idx in range(lo,min(hi,len(prefixes))):
        load(prefixes[idx])
        if dfs(D): print('FOUND',found[0],flush=True); break
        done=idx+1
except Timeout:
    pass
print('completed prefixes [%d,%d) of %d; nodes %d; %.1fs; found=%s'%(lo,done,len(prefixes),stats['nodes'],time.time()-t0,found[0] is not None),flush=True)
