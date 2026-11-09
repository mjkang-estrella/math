# D3b for G = I_a v H, H random maximal triangle-free on h vertices (n=a+h), plus general random maximal K4-free
import sys,random,itertools,time,json
n=int(sys.argv[1]); seed=int(sys.argv[2]); budget=float(sys.argv[3]); random.seed(seed); t=n//3
subs=[sum(1<<i for i in c) for c in itertools.combinations(range(n),t)]
sid={s:i for i,s in enumerate(subs)}; full=(1<<n)-1; parts=[]
for s1 in subs:
    if not s1&1: continue
    rest=full^s1; low=rest&-rest
    for s2 in subs:
        if s2&rest==s2 and s2&low: parts.append((sid[s1],sid[s2],sid[rest^s2]))
def D(adj):
    e=[]
    for s in subs:
        c=0;x=s
        while x:
            b=x&-x;i=b.bit_length()-1;c+=bin(adj[i]&s).count('1');x^=b
        e.append(c//2)
    return min(e[a]+e[b]+e[c] for a,b,c in parts)
best={}; start=time.time(); cnt=0
while time.time()-start<budget:
    h=random.randint(5,n); a=n-h
    adj=[0]*n
    pairs=[(i,j) for i in range(a,n) for j in range(i+1,n)]; random.shuffle(pairs)
    for i,j in pairs:
        if not (adj[i]&adj[j]): adj[i]|=1<<j; adj[j]|=1<<i
    if h>0:
        Hmask=sum(1<<i for i in range(a,n))
        for i in range(a): adj[i]|=Hmask
        for j in range(a,n): adj[j]|=(1<<a)-1
    v=D(adj); cnt+=1
    if v>best.get(h,(-1,))[0]: best[h]=(v,adj[:])
print(json.dumps({'n':n,'seed':seed,'samples':cnt,'bound':4*n*n/81,'best_by_h':{h:[v,ad] for h,(v,ad) in sorted(best.items())}}))
