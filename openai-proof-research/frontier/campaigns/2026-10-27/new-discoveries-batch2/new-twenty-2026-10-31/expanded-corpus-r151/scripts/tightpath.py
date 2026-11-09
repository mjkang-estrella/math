# Exact check: does there exist a red/blue colouring of K_N^(k) with no red tight path of r edges and no blue tight path of s edges?
# Tight path with t edges: vertex sequence v1..v_{t+k-1}, edges {v_i..v_{i+k-1}}. Backtracking over edges with pruning.
import sys,itertools
k,r,s,N=map(int,sys.argv[1:5])
E=list(itertools.combinations(range(N),k)); eid={e:i for i,e in enumerate(E)}
def paths(t):
    out=set()
    for seq in itertools.permutations(range(N),t+k-1):
        if seq[0]>seq[-1]: continue
        es=frozenset(eid[tuple(sorted(seq[i:i+k]))] for i in range(t))
        out.add(es)
    return list(out)
PR=paths(r); PS=paths(s)
byR=[[] for _ in E]; byS=[[] for _ in E]
for p in PR:
    for e in p: byR[e].append(p)
for p in PS:
    for e in p: byS[e].append(p)
col=[None]*len(E)
# fix colour of edge 0 by symmetry (red/blue not symmetric unless r==s, so no fix)
nodes=0
def ok(e):
    c=col[e]
    L=byR[e] if c==0 else byS[e]
    for p in L:
        if all(col[f]==c for f in p): return False
    return True
def bt(i):
    global nodes
    nodes+=1
    if i==len(E): return True
    for c in (0,1):
        col[i]=c
        if ok(i) and bt(i+1): return True
    col[i]=None
    return False
res=bt(0)
print('k',k,'r',r,'s',s,'N',N,'avoiding colouring exists' if res else 'NO avoiding colouring (R<=N)','nodes',nodes)
if res: print('red edges',[E[i] for i in range(len(E)) if col[i]==0])
