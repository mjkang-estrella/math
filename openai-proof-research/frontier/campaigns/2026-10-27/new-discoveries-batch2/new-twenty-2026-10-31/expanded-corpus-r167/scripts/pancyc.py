# 368246: search strong digraphs on n vertices containing Hamiltonian cycle 0->1->...->n-1->0,
# with no cycle of length L, satisfying the BJGL-type condition of Conjecture 1 (Zhang-Wu-He arXiv:2504.21628),
# that are not LSD and not balanced complete bipartite. Hamiltonicity is WLOG by Theorem 1.1 (BJGL 1996)
# for strong digraphs satisfying the condition (condition implies Thm 1.1 hypothesis).
import sys,json,time
n=int(sys.argv[1]); L=int(sys.argv[2]); limit=float(sys.argv[3]) if len(sys.argv)>3 else 1e18
out=[0]*n; inn=[0]*n
def add(u,v): out[u]|=1<<v; inn[v]|=1<<u
def rem(u,v): out[u]&=~(1<<v); inn[v]&=~(1<<u)
for i in range(n): add(i,(i+1)%n)
arcs=[(u,v) for u in range(n) for v in range(n) if u!=v and v!=(u+1)%n]
arcs.sort(key=lambda a:(max(a),min(a),a))
und=[0]*n
for (u,v) in arcs: und[u]+=1; und[v]+=1
decided=[[False]*n for _ in range(n)]
for i in range(n): decided[i][(i+1)%n]=True
def prune_ok(u,v):
    # after deciding arc u->v (present or absent): check vertices u,v and pairs touching them
    for x in (u,v):
        ub=popc(out[x])+popc(inn[x])+und[x]
        if ub>=n: continue
        for y in range(n):
            if y==x or not (decided[x][y] and decided[y][x]): continue
            if (out[x]>>y)&1 or (out[y]>>x)&1: continue
            # common in-neighbour z with decided arcs z->x,z->y present; or common out
            if (inn[x]&inn[y]) or (out[x]&out[y]): return False
    return True
def haspath(a,b,k,used):
    # simple path a->...->b with exactly k arcs, avoiding used
    if k==1: return (out[a]>>b)&1==1
    m=out[a]&~used&~(1<<b)
    while m:
        w=(m&-m).bit_length()-1; m&=m-1
        if haspath(w,b,k-1,used|(1<<w)): return True
    return False
def creates(u,v):
    # L-cycle through new arc u->v: path v->..->u with L-1 arcs
    return haspath(v,u,L-1,(1<<u)|(1<<v)) if L>2 else False
def popc(x): return bin(x).count('1')
def check():
    deg=[popc(out[i])+popc(inn[i]) for i in range(n)]
    bad=False
    for x in range(n):
        for y in range(x+1,n):
            if (out[x]>>y)&1 or (out[y]>>x)&1: continue
            if (inn[x]&inn[y]) or (out[x]&out[y]):
                bad=True
                if deg[x]<n or deg[y]<n: return None
    if not bad: return 'LSD'
    return 'CAND'
def cycles_lengths():
    s=set()
    for k in range(2,n+1):
        for a in range(n):
            if haspath_cycle(a,k): s.add(k); break
    return s
def haspath_cycle(a,k):
    # cycle of length k through a with a minimal vertex
    def rec(c,k,used):
        if k==1: return (out[c]>>a)&1==1
        m=out[c]&~used & ~((1<<(a+1))-1)
        while m:
            w=(m&-m).bit_length()-1; m&=m-1
            if rec(w,k-1,used|(1<<w)): return True
        return False
    return rec(a,k,1<<a)
leaves=0; lsd=0; cands=[]; t0=time.time(); stopped=False
def rec(i):
    global leaves,lsd,stopped
    if stopped: return
    if i==len(arcs):
        leaves+=1
        r=check()
        if r=='LSD': lsd+=1
        elif r=='CAND':
            cl=cycles_lengths()
            cands.append({'arcs':[(u,v) for u in range(n) for v in range(n) if (out[u]>>v)&1],'cycle_lengths':sorted(cl)})
        if leaves%200000==0 and time.time()-t0>limit: stopped=True
        return
    u,v=arcs[i]
    und[u]-=1; und[v]-=1; decided[u][v]=True
    if prune_ok(u,v): rec(i+1)
    if not creates(u,v):
        add(u,v)
        if prune_ok(u,v): rec(i+1)
        rem(u,v)
    und[u]+=1; und[v]+=1; decided[u][v]=False
rec(0)
print(json.dumps({'n':n,'L':L,'leaves':leaves,'lsd_leaves':lsd,'candidates':len(cands),'complete':not stopped,'secs':round(time.time()-t0,1),'first':cands[:5]}))
