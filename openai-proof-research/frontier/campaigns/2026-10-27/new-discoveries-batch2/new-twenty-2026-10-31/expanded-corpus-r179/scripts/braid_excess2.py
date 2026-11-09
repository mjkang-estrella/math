# Same DP as braid_excess.py; reports the top ratios B/N among sigma that are not longest elements of an interval parabolic.
import sys, itertools, heapq
n=int(sys.argv[1])
def act(p,k):
    q=list(p); q[k],q[k+1]=q[k+1],q[k]; return tuple(q)
inv=lambda p: sum(1 for a in range(n) for b in range(a+1,n) if p[a]>p[b])
perms=sorted(itertools.permutations(range(n)), key=inv)
N={};B={}; idp=tuple(range(n)); N[idp]=1;B[idp]=0
def is_interval_w0(p):
    moved=[i for i in range(n) if p[i]!=i]
    if not moved: return True
    a,b=moved[0],moved[-1]
    return all(p[i]==a+b-i for i in range(a,b+1)) and b-a>=2
top=[]
for p in perms:
    if p==idp: continue
    D=[k for k in range(n-1) if p[k]>p[k+1]]
    N[p]=sum(N[act(p,k)] for k in D)
    B[p]=sum(B[act(p,k)] for k in D)+2*sum(N[act(act(act(p,k),k+1),k)] for k in D if k+1 in D)
    if not is_interval_w0(p):
        heapq.heappush(top,(B[p]/N[p],p)); 
        if len(top)>6: heapq.heappop(top)
for r,p in sorted(top,reverse=True): print(n,round(r,6),p,N[p],B[p])
