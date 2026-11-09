import sys, itertools; sys.path.insert(0, sys.argv[1]); from trees import _nx, adj_of, gamma_tree
def brute(adj):
    n=len(adj); cl=[(1<<v)|sum(1<<w for w in adj[v]) for v in range(n)]; full=(1<<n)-1
    for k in range(1,n+1):
        for S in itertools.combinations(range(n),k):
            m=0
            for v in S: m|=cl[v]
            if m==full: return k
tot=0
for n in range(2,14):
    for par in _nx(n):
        adj=adj_of(par); assert gamma_tree(adj)==brute(adj),(n,par); tot+=1
print('validated gamma DP against brute force on all free trees n=2..13:',tot)
