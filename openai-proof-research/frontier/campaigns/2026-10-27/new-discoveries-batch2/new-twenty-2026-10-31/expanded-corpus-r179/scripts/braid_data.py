import sys, itertools
n=int(sys.argv[1])
def act(p,k):
    q=list(p); q[k],q[k+1]=q[k+1],q[k]; return tuple(q)
inv=lambda p: sum(1 for a in range(n) for b in range(a+1,n) if p[a]>p[b])
perms=sorted(itertools.permutations(range(n)), key=inv)
N={};B={}; idp=tuple(range(n)); N[idp]=1;B[idp]=0
for p in perms:
    if p==idp: continue
    D=[k for k in range(n-1) if p[k]>p[k+1]]
    N[p]=sum(N[act(p,k)] for k in D)
    B[p]=sum(B[act(p,k)] for k in D)+2*sum(N[act(act(act(p,k),k+1),k)] for k in D if k+1 in D)
for p in perms:
    print(''.join(str(x+1) for x in p),'len',inv(p),'N',N[p],'B',B[p],'A',N[p]-B[p])
