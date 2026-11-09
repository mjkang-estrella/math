# Simulated annealing over r-regular graphs on n vertices using 2-switch moves,
# minimising the number of unordered vertex pairs with equal K3-degree.
# usage: sa.py n seed seconds [r] [T0] [Tmin]
import sys,random,math,time,json
n=int(sys.argv[1]); seed=int(sys.argv[2]); secs=float(sys.argv[3])
r=int(sys.argv[4]) if len(sys.argv)>4 else 8
T0=float(sys.argv[5]) if len(sys.argv)>5 else 1.5
Tmin=float(sys.argv[6]) if len(sys.argv)>6 else 0.15
W1=float(sys.argv[7]) if len(sys.argv)>7 else 0.0
rng=random.Random(seed)
adj=[0]*n
for v in range(n):
    for o in range(1,r//2+1):
        adj[v]|=1<<((v+o)%n); adj[v]|=1<<((v-o)%n)
    if r%2: adj[v]|=1<<((v+n//2)%n)
assert all(a.bit_count()==r for a in adj)
edges=[(v,w) for v in range(n) for w in range(v+1,n) if adj[v]>>w&1]; E=len(edges)
M=r*(r-1)//2
t=[0]*n
for v in range(n):
    s=0;x=adj[v]
    while x:
        u=(x&-x).bit_length()-1;x&=x-1;s+=(adj[u]&adj[v]).bit_count()
    t[v]=s//2
cnt=[0]*(M+3)
for x in t: cnt[x+1]+=1
eq=sum(c*(c-1)//2 for c in cnt)
cost=eq+W1*sum(cnt[i]*cnt[i+1] for i in range(len(cnt)-1))
def setv(v,y):
    global cost,eq
    x=t[v]+1; y1=y+1
    cnt[x]-=1; eq-=cnt[x]; cost-=cnt[x]+W1*(cnt[x-1]+cnt[x+1])
    eq+=cnt[y1]; cost+=cnt[y1]+W1*(cnt[y1-1]+cnt[y1+1]); cnt[y1]+=1; t[v]=y
def tog(a,b,s):
    c=adj[a]&adj[b]; k=c.bit_count()*s
    if k: setv(a,t[a]+k); setv(b,t[b]+k)
    while c:
        w=(c&-c).bit_length()-1;c&=c-1;setv(w,t[w]+s)
    adj[a]^=1<<b; adj[b]^=1<<a
def try_switch():
    i=rng.randrange(E); j=rng.randrange(E)
    a,b=edges[i]; c,d=edges[j]
    if rng.random()<.5: c,d=d,c
    if a==c or a==d or b==c or b==d or adj[a]>>c&1 or adj[b]>>d&1: return None
    tog(a,b,-1); tog(c,d,-1); tog(a,c,1); tog(b,d,1)
    edges[i]=(a,c); edges[j]=(b,d)
    return (i,j,a,b,c,d)
def undo(m):
    i,j,a,b,c,d=m
    tog(a,c,-1); tog(b,d,-1); tog(a,b,1); tog(c,d,1); edges[i]=(a,b); edges[j]=(c,d)
for _ in range(3000):
    try_switch()
best=eq; bestadj=list(adj); start=time.time(); it=0; acc=0
period=200000
stall=int(sys.argv[8]) if len(sys.argv)>8 else 0
lastimp=0
while True:
    el=time.time()-start
    if el>secs or best==0: break
    # cyclic annealing schedule
    ph=(it%period)/period
    T=T0*(Tmin/T0)**ph
    it+=1
    old=cost
    m=try_switch()
    if m is None: continue
    dc=cost-old
    if dc<=0 or rng.random()<math.exp(-dc/T):
        acc+=1
        if eq<best: best=eq; bestadj=list(adj); lastimp=it
    else:
        undo(m)
# verify best independently
def tri(adjl):
    return [sum(1 for u in range(n) for w in range(u+1,n) if adjl[v]>>u&1 and adjl[v]>>w&1 and adjl[u]>>w&1) for v in range(n)]
tb=tri(bestadj)
assert all(a.bit_count()==r for a in bestadj) and all(not(a>>v&1) for v,a in enumerate(bestadj))
assert all((bestadj[u]>>v&1)==(bestadj[v]>>u&1) for u in range(n) for v in range(n))
from collections import Counter
cb=Counter(tb); pairs=sum(c*(c-1)//2 for c in cb.values())
print(json.dumps({'n':n,'r':r,'seed':seed,'iters':it,'accepted':acc,'secs':round(time.time()-start,1),'best_pairs':pairs,'tri':sorted(tb),'adj':bestadj}))
