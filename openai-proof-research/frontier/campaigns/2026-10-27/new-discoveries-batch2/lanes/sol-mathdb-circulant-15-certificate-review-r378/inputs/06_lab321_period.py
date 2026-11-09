# Transfer-matrix certificate for L(3,2,1)-labelings of C_n(1,t) with labels 0..K-1.
# For n > 2*3t, labelings of C_n(1,t) <-> cyclic words of length n all of whose cyclic windows of
# length W+1 satisfy the distance-graph G(1,t) constraints <-> closed walks of length n in the graph
# on valid W-windows. Every closed walk lies in one SCC; in an SCC of period p, every closed-walk
# length is 0 mod p. Certificate: potential phi with phi(v)=phi(u)+1 mod p on every intra-SCC edge.
import sys, json, math, collections
from collections import deque
t,K=int(sys.argv[1]),int(sys.argv[2]); out=sys.argv[3] if len(sys.argv)>3 else None
dist={0:0}; q=deque([0])
while q:
    u=q.popleft()
    if dist[u]==3: continue
    for s in (1,-1,t,-t):
        v=u+s
        if v not in dist: dist[v]=dist[u]+1; q.append(v)
need={d:4-dist[d] for d in range(1,3*t+1) if d in dist and dist[d]<=3}; W=max(need)
states=[]
def dfs(seq):
    if len(seq)==W: states.append(tuple(seq)); return
    for x in range(K):
        if all(abs(x-seq[-d])>=need[d] for d in need if d<=len(seq)): dfs(seq+[x])
dfs([])
idx={s:i for i,s in enumerate(states)}; N=len(states)
adj=[[] for _ in range(N)]
for i,s in enumerate(states):
    for x in range(K):
        if all(abs(x-s[-d])>=need[d] for d in need):
            adj[i].append(idx[s[1:]+(x,)])
# iterative Tarjan
index=[-1]*N; low=[0]*N; on=[False]*N; st=[]; comp=[-1]*N; c=0; nxt=0
for r in range(N):
    if index[r]!=-1: continue
    stack=[(r,0)]; index[r]=low[r]=nxt; nxt+=1; st.append(r); on[r]=True
    while stack:
        u,k=stack[-1]
        if k<len(adj[u]):
            stack[-1]=(u,k+1); v=adj[u][k]
            if index[v]==-1:
                index[v]=low[v]=nxt; nxt+=1; st.append(v); on[v]=True; stack.append((v,0))
            elif on[v]: low[u]=min(low[u],index[v])
        else:
            stack.pop()
            if stack: low[stack[-1][0]]=min(low[stack[-1][0]],low[u])
            if low[u]==index[u]:
                while True:
                    w=st.pop(); on[w]=False; comp[w]=c
                    if w==u: break
                c+=1
members={}
for i in range(N): members.setdefault(comp[i],[]).append(i)
report=[]; phi=[None]*N; per={}
for cc,mem in members.items():
    inner=[(u,v) for u in mem for v in adj[u] if comp[v]==cc]
    if not inner: continue
    lev={mem[0]:0}; dq=deque([mem[0]])
    while dq:
        u=dq.popleft()
        for v in adj[u]:
            if comp[v]==cc and v not in lev: lev[v]=lev[u]+1; dq.append(v)
    p=0
    for u,v in inner: p=math.gcd(p,lev[u]+1-lev[v])
    per[cc]=p
    for u in mem: phi[u]=lev[u]%p
    report.append({'scc':cc,'size':len(mem),'inner_edges':len(inner),'period':p,'example_state':list(states[mem[0]])})
# Local, edge-by-edge certificate (independent of Tarjan correctness): Tarjan emits SCCs in reverse
# topological order, so every edge must satisfy comp[v]<comp[u], or comp[v]==comp[u] with
# phi[v]==phi[u]+1 mod p. Then any closed walk stays in one comp level and has length 0 mod p.
for u in range(N):
    for v in adj[u]:
        if comp[u]==comp[v]: assert (phi[u]+1-phi[v])%per[comp[u]]==0
        else: assert comp[v]<comp[u]
import hashlib
cert=json.dumps({'states':states,'comp':comp,'phi':phi,'period':{str(k):v for k,v in sorted(per.items())}},separators=(',',':'))
res={'certificate_sha256':hashlib.sha256(cert.encode()).hexdigest(),'local_edge_certificate_checked':True,'t':t,'labels':K,'window':W,'constraints':need,'states':N,'edges':sum(map(len,adj)),'nontrivial_sccs':report}
summ=collections.Counter((x["period"],x["size"]) for x in report); res["period_size_histogram"]={f"p{a}_s{b}":v for (a,b),v in sorted(summ.items())}; res["all_periods_even"]=all(x["period"]%2==0 for x in report); res["all_periods_div12"]=all(x["period"]%12==0 for x in report)
print(json.dumps({k:v for k,v in res.items() if k!="nontrivial_sccs"}))
print(json.dumps(res["nontrivial_sccs"]))
if out: open(out,'w').write(cert)
