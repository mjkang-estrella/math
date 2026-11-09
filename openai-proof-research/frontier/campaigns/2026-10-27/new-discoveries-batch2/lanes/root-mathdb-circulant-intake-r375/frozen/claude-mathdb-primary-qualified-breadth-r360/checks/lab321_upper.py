# Independent upper-bound check: with K labels, let L be the set of lengths of closed walks through a
# fixed state s0 of the window graph. L is closed under addition. If p in L and every n in a full
# residue window [n0, n0+p) of the required parity is in L, then every such n >= n0 is in L, giving
# an L(3,2,1)-labeling of C_n(1,t) with span <= K-1 for all those n (n > 6t so windows = distances).
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
assert len(s0)==W
def ok(seq,x): return all(abs(x-seq[-d])>=need[d] for d in need if d<=len(seq))
assert all(ok(s0[:i],s0[i]) for i in range(W))
targets=[n for n in range(n0,n0+2*p) if n%2==parity]
Lmax=max(targets+[p]); cur={s0}; L=[]; witness={}
parent=[{s0:None}]
for k in range(1,Lmax+1):
    nxt={}
    for s in cur:
        for x in range(K):
            if ok(s,x):
                ns=s[1:]+(x,)
                if ns not in nxt: nxt[ns]=s
    parent.append(nxt); cur=set(nxt)
    if s0 in cur: L.append(k)
# reconstruct and independently re-validate one cyclic word per target length
def word(k):
    s=s0; seq=[]
    for j in range(k,0,-1):
        seq.append(s[-1]); s=parent[j][s]
    return seq[::-1]
def valid_cyclic(w):
    n=len(w)
    return all(abs(w[i]-w[(i+d)%n])>=r for i in range(n) for d,r in need.items())
res={'t':t,'labels':K,'p_in_L':p in L,'targets':targets,'all_targets_in_L':all(n in L for n in targets)}
res['witness_words_valid']=all(valid_cyclic(word(n)) for n in targets+[p] if n in L)
print(json.dumps(res)); sys.exit(0 if res['p_in_L'] and res['all_targets_in_L'] and res['witness_words_valid'] else 1)
