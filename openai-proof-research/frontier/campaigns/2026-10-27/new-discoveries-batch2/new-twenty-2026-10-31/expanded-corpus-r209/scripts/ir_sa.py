# Simulated annealing over complements (edge toggles) on n vertices to make the IR-graph a long path or a cycle.
# score: penalty = sum(max(0,deg-2)) + 2*(components-1); target = 'path' or 'cycle'.
import sys,random,json,time,math
n=int(sys.argv[1]); target=sys.argv[2]; seed=int(sys.argv[3]); budget=float(sys.argv[4]); init=sys.argv[5] if len(sys.argv)>5 else 'tri'
random.seed(seed)
POP=[bin(i).count('1') for i in range(1<<n)]
BYSIZE=sorted(range(1,1<<n),key=lambda D:-POP[D])
def irsets(adj,cap=60):
    N=[adj[v]|(1<<v) for v in range(n)]; best=0; sets=[]
    for D in BYSIZE:
        k=POP[D]
        if k<best: break
        ok=True;x=D
        while x:
            b=x&-x;v=b.bit_length()-1;others=0;y=D^b
            while y:
                c=y&-y;others|=N[c.bit_length()-1];y^=c
            if not N[v]&~others: ok=False;break
            x^=b
        if ok:
            best=k;sets.append(D)
            if len(sets)>cap: return best,None
    return best,sets
def evaluate(adj):
    b,sets=irsets(adj)
    if sets is None: return 1000,None
    S=set(sets); m=len(sets); nb={}; pen=0; E=0
    for A in sets:
        l=[];x=A
        while x:
            bb=x&-x;a=bb.bit_length()-1;x^=bb
            y=adj[a]&~A
            while y:
                c=y&-y;y^=c;B=(A^bb)|c
                if B in S: l.append(B)
        nb[A]=l; pen+=max(0,len(l)-2); E+=len(l)
    E//=2; comps=0; seen=set()
    for A in sets:
        if A in seen: continue
        comps+=1; st=[A]; seen.add(A)
        while st:
            X=st.pop()
            for B in nb[X]:
                if B not in seen: seen.add(B); st.append(B)
    pen+=2*(comps-1)
    shape=None
    if pen==0:
        if E==m-1 and m>=3: shape='P%d'%m
        elif E==m and m>=5: shape='C%d'%m
    if target=='cycle' and pen==0 and E==m-1: pen+=1  # want to close
    if target=='path' and pen==0 and E==m: pen+=1
    return pen - 0.05*min(m,30), shape
pairs=[(i,j) for i in range(n) for j in range(i+1,n)]
comp=set()
if init=='tri':
    for t in range(n//3): a,b,c=3*t,3*t+1,3*t+2; comp|={(a,b),(a,c),(b,c)}
    for e in pairs:
        if e[0]//3!=e[1]//3 and random.random()<0.25: comp.add(e)
else:
    comp={e for e in pairs if random.random()<0.4}
def adjof(comp):
    adj=[0]*n
    for i,j in pairs:
        if (i,j) not in comp: adj[i]|=1<<j; adj[j]|=1<<i
    return adj
cur,_=evaluate(adjof(comp)); found={}; t0=time.time(); it=0
while time.time()-t0<budget:
    it+=1; new=set(comp)
    for _ in range(random.randint(1,2)):
        e=random.choice(pairs)
        if e in new: new.remove(e)
        else: new.add(e)
    v,sh=evaluate(adjof(new))
    T=0.5*(1-(time.time()-t0)/budget)+0.02
    if v<=cur or random.random()<math.exp((cur-v)/T):
        comp=new;cur=v
        if sh and sh not in found:
            found[sh]=sorted(comp); print(json.dumps({'shape':sh,'complement':sorted(comp)}),flush=True)
print(json.dumps({'n':n,'target':target,'seed':seed,'iters':it,'shapes':sorted(found)}))
