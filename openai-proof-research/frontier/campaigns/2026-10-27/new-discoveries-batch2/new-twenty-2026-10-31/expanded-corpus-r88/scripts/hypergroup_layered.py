# Generate all connected r-regular graphs on n vertices in BFS-layered form rooted at v0=0 whose distance partition from
# v0 is equitable (each vertex at distance k has c_k / a_k / b_k neighbours at distance k-1 / k / k+1, constant on the layer).
# This is (S2) with i=1, a necessary condition. Then test full (S1),(S2) and the hypergroup axioms exactly
# (check() of hypergroup_search.py). Duplicated isomorphic outputs are harmless. Exhaustive for the given (n, r).
import sys, json, time
exec(open(sys.path[0]+'/hypergroup_search.py').read().split('t=time.time(); tot=0')[0])
n=int(sys.argv[1]); r=int(sys.argv[2]); BUDGET=float(sys.argv[3])
# optional sharding: when the BFS processing reaches vertex SPLITV, the k-th arrival continues only if k % SHARDS == SHARD
SPLITV=int(sys.argv[4]) if len(sys.argv)>4 else -1; SHARDS=int(sys.argv[5]) if len(sys.argv)>5 else 1; SHARD=int(sys.argv[6]) if len(sys.argv)>6 else 0
arrivals=[0]
t0=time.time(); stats={'complete_graphs':0,'S1S2':0}; bad=[]; nondrg=[]; seen=set(); timed=False
adj=[set() for _ in range(n)]; layer=[-1]*n; layer[0]=0
for i in range(1,r+1): adj[0].add(i); adj[i].add(0); layer[i]=1
created=r+1
def layer_ok(L):
    # all vertices of layer L completely processed: equitable counts constant
    vs=[v for v in range(created) if layer[v]==L]
    sig={(sum(1 for w in adj[v] if layer[w]==L-1),sum(1 for w in adj[v] if layer[w]==L),sum(1 for w in adj[v] if layer[w]==L+1)) for v in vs}
    return len(sig)==1
def canon_key():
    return tuple(sorted(tuple(sorted(a)) for a in adj))
def finish():
    global bad
    stats['complete_graphs']+=1
    A=[sorted(a) for a in adj]
    D=dist_all(n,A)
    if any(D[0][v]!=layer[v] for v in range(n)): return
    res=check(n,A,0,D)
    if res is None: return
    stats['S1S2']+=1
    # distance-regular test: |S_i(x) ∩ S_j(y)| depends only on d(x,y)
    tab={}; drg=True
    for x in range(n):
        for y in range(n):
            for i in range(n):
                pass
    for x in range(n):
        for y in range(x,n):
            key=D[x][y]
            prof=tuple(sorted(((D[x][w],D[y][w]) for w in range(n))))
            if tab.setdefault(key,prof)!=prof: drg=False; break
        if not drg: break
    if not drg:
        stats['S1S2_nonDRG']=stats.get('S1S2_nonDRG',0)+1
        if len(nondrg)<3: nondrg.append(A)
    if not (res[0] and res[1]):
        bad.append({'adj':A,'commutative':res[0],'associative':res[1]})
def rec(v):
    # process vertex v (in BFS order): give it remaining neighbours
    global created, timed
    if time.time()-t0>BUDGET: timed=True; return
    if v==SPLITV:
        arrivals[0]+=1
        if (arrivals[0]-1)%SHARDS!=SHARD: return
    if v==n:
        if created==n: finish()
        return
    if v>=created: return   # disconnected
    # layer completion check when moving to a new layer
    if v>0 and layer[v]!=layer[v-1]:
        if not layer_ok(layer[v-1]): return
    need=r-len(adj[v])
    if need<0: return
    L=layer[v]
    # candidates: existing vertices w>v in layer L or L+1 with free degree, not adjacent; or new vertex (layer L+1)
    cands=[w for w in range(v+1,created) if layer[w] in (L,L+1) and len(adj[w])<r and w not in adj[v]]
    def choose(start,k,newcount):
        global created
        if k==0:
            rec(v+1); return
        for idx in range(start,len(cands)):
            w=cands[idx]
            if len(adj[w])>=r: continue
            adj[v].add(w); adj[w].add(v)
            choose(idx+1,k-1,newcount)
            adj[v].discard(w); adj[w].discard(v)
        # new vertices (canonical: always the next label)
        if created<n:
            w=created; created+=1; layer[w]=L+1
            adj[v].add(w); adj[w].add(v)
            cands_backup=list(cands)
            # after creating, further choices may only be new vertices (to keep order canonical)
            choose_new(k-1)
            adj[v].discard(w); adj[w].discard(v); layer[w]=-1; created-=1
    def choose_new(k):
        global created
        if k==0:
            rec(v+1); return
        if created>=n: return
        w=created; created+=1; layer[w]=L+1
        adj[v].add(w); adj[w].add(v)
        choose_new(k-1)
        adj[v].discard(w); adj[w].discard(v); layer[w]=-1; created-=1
    choose(0,need,0)
sys.setrecursionlimit(100000)
rec(1)
print(json.dumps({'n':n,'r':r,'splitv':SPLITV,'shards':SHARDS,'shard':SHARD,'arrivals_at_split':arrivals[0],'complete':not timed,**stats,'num_counterexamples':len(bad),'counterexamples':bad[:3],'nonDRG_examples':nondrg[:2],'secs':round(time.time()-t0,1)}))
