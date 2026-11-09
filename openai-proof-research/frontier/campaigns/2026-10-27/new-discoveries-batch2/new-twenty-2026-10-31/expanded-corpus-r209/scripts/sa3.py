# simulated annealing over K4-free graphs on n vertices maximizing D3b (min class-edges over balanced 3-partitions)
import sys,random,itertools,math,time,json
n=int(sys.argv[1]); seed=int(sys.argv[2]); T=float(sys.argv[3]); budget=float(sys.argv[4])
random.seed(seed); t=n//3
subs=[sum(1<<i for i in c) for c in itertools.combinations(range(n),t)]
sid={s:i for i,s in enumerate(subs)}
full=(1<<n)-1
parts=[]
for s1 in subs:
    if not s1&1: continue
    rest=full^s1; low=rest&-rest
    for s2 in subs:
        if s2&rest==s2 and s2&low:
            parts.append((sid[s1],sid[s2],sid[rest^s2]))
pairs=[(i,j) for i in range(n) for j in range(i+1,n)]
def esub(adj,s):
    c=0; x=s
    while x:
        b=x&-x; i=b.bit_length()-1; c+=bin(adj[i]&s).count('1'); x^=b
    return c//2
def D(adj):
    e=[esub(adj,s) for s in subs]
    return min(e[a]+e[b]+e[c] for a,b,c in parts)
def k4ok(adj,i,j):
    common=adj[i]&adj[j]
    x=common
    while x:
        b=x&-x; k=b.bit_length()-1
        if adj[k]&common&~b: return False
        x^=b
    return True
adj=[0]*n
order=pairs[:]; random.shuffle(order)
for i,j in order:
    if k4ok(adj,i,j): adj[i]|=1<<j; adj[j]|=1<<i
cur=D(adj); best=cur; bestadj=adj[:]; start=time.time(); it=0
while time.time()-start<budget:
    it+=1
    new=adj[:]
    # remove 1-2 edges, then greedily add random edges keeping K4-free
    edges=[(i,j) for i,j in pairs if new[i]>>j&1]
    for _ in range(random.randint(1,3)):
        i,j=random.choice(edges); new[i]&=~(1<<j); new[j]&=~(1<<i)
    random.shuffle(order)
    for i,j in order:
        if not new[i]>>j&1 and k4ok(new,i,j) and random.random()<0.9: new[i]|=1<<j; new[j]|=1<<i
    v=D(new)
    temp=T*(1-(time.time()-start)/budget)+1e-3
    if v>=cur or random.random()<math.exp((v-cur)/temp):
        adj=new; cur=v
        if v>best: best=v; bestadj=new[:]
print(json.dumps({'n':n,'seed':seed,'iters':it,'best':best,'bound':4*n*n/81,'adj':bestadj,'edges':sum(bin(a).count('1') for a in bestadj)//2}))
