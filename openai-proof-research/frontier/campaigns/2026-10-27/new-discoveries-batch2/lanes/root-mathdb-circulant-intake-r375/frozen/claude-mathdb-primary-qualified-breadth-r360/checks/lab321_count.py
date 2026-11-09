import sys
from collections import deque
t,K=int(sys.argv[1]),int(sys.argv[2])  # steps {1,t}, labels 0..K-1
D=3*t  # max displacement within distance 3
dist={0:0}; q=deque([0])
while q:
    u=q.popleft()
    if dist[u]==3: continue
    for s in (1,-1,t,-t):
        v=u+s
        if v not in dist: dist[v]=dist[u]+1; q.append(v)
need={d:4-dist[d] for d in range(1,D+1) if d in dist and dist[d]<=3}  # |f diff| >= 4-dist
print('constraints',need)
W=max(need)  # window length of state
cnt=[0]*(W+1)
def dfs(seq):
    cnt[len(seq)]+=1
    if len(seq)==W: return
    for x in range(K):
        if all(abs(x-seq[-d])>=need[d] for d in need if d<=len(seq)): dfs(seq+[x])
dfs([])
print('states by length',cnt)
