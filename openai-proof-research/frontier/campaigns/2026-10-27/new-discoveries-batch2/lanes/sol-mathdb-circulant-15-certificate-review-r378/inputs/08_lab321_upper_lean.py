# Memory-lean variant of lab321_upper.py: frontier-only reachability from s0, states packed as ints
# (base K). Reports the closed-walk lengths through s0 among the targets; no witness reconstruction.
import sys,json
from collections import deque
t,K,n0,parity,p=map(int,sys.argv[1:6]); s0=tuple(map(int,sys.argv[6].split(',')))
dist={0:0}; q=deque([0])
while q:
    u=q.popleft()
    if dist[u]==3: continue
    for s in (1,-1,t,-t):
        v=u+s
        if v not in dist: dist[v]=dist[u]+1; q.append(v)
need={d:4-dist[d] for d in range(1,3*t+1) if d in dist and dist[d]<=3}; W=max(need)
P=[K**i for i in range(W)]  # digit i = position i (0 = oldest)
def enc(s): return sum(x*P[i] for i,x in enumerate(s))
def dec(c): return [(c//P[i])%K for i in range(W)]
items=sorted(need.items())
def succ(c):
    s=dec(c); base=c//K
    for x in range(K):
        if all(abs(x-s[W-d])>=r for d,r in items): yield base+x*P[W-1]
assert all(all(abs(s0[i]-s0[i-d])>=r for d,r in items if d<=i) for i in range(W))
targets=[n for n in range(n0,n0+2*p) if n%2==parity]; Lmax=max(targets+[p])
start=enc(s0); cur={start}; L=[]; peak=1
for k in range(1,Lmax+1):
    cur={v for c in cur for v in succ(c)}; peak=max(peak,len(cur))
    if start in cur: L.append(k)
res={'t':t,'labels':K,'p_in_L':p in L,'targets':targets,'targets_in_L':[n for n in targets if n in L],'all_targets_in_L':all(n in L for n in targets),'peak_frontier':peak}
print(json.dumps(res)); sys.exit(0 if res['p_in_L'] and res['all_targets_in_L'] else 1)
