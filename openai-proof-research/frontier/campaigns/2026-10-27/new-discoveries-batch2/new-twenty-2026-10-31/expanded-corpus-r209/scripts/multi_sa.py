# Explore G = complement of (t disjoint triangles + cross edges X) and random graphs on n vertices;
# record IR-graphs that are paths P_m (m>=3) or cycles C_m (m>=5). Fast IR-graph routine.
import sys,random,json,time,itertools
n=int(sys.argv[1]); mode=sys.argv[2]; seed=int(sys.argv[3]); budget=float(sys.argv[4]); p=float(sys.argv[5])
random.seed(seed)
POP=[bin(i).count('1') for i in range(1<<n)]
BYSIZE=sorted(range(1,1<<n),key=lambda D:-POP[D])
def irfast(adj):
    N=[adj[v]|(1<<v) for v in range(n)]
    best=0;sets=[]
    for D in BYSIZE:
        k=POP[D]
        if k<best: break
        if len(sets)>200: return best,None
        ok=True;x=D
        while x:
            b=x&-x;v=b.bit_length()-1
            others=0;y=D^b
            while y:
                c=y&-y;others|=N[c.bit_length()-1];y^=c
            if not N[v]&~others: ok=False;break
            x^=b
        if ok:
            best=k;sets.append(D)
    return best,sets
def shape(adj,sets):
    S=set(sets);m=len(sets);E=0;nb={}
    for A in sets:
        l=[];x=A
        while x:
            b=x&-x;a=b.bit_length()-1;x^=b
            y=adj[a]&~A
            while y:
                c=y&-y;y^=c;B=(A^b)|c
                if B in S: l.append(B)
        if len(l)>2: return None
        nb[A]=l;E+=len(l)
    E//=2
    seen={sets[0]};st=[sets[0]]
    while st:
        A=st.pop()
        for B in nb[A]:
            if B not in seen: seen.add(B);st.append(B)
    if len(seen)<m: return None
    if E==m-1 and m>=3: return 'P%d'%m
    if E==m and m>=5: return 'C%d'%m
    return None
found={}; cnt=0; t0=time.time()
pairs=[(i,j) for i in range(n) for j in range(i+1,n)]
base=set()
if mode=='tri':
    for t in range(n//3):
        a,b,c=3*t,3*t+1,3*t+2; base|={(a,b),(a,c),(b,c)}
cross=[e for e in pairs if e not in base and (mode!='tri' or e[0]//3!=e[1]//3)]
while time.time()-t0<budget:
    comp=set(base)|{e for e in cross if random.random()<p}
    adj=[0]*n
    for i,j in pairs:
        if (i,j) not in comp: adj[i]|=1<<j; adj[j]|=1<<i
    cnt+=1
    b,sets=irfast(adj)
    if sets is None or len(sets)<3: continue
    sh=shape(adj,sets)
    if sh and sh not in found:
        found[sh]=sorted(comp); print(json.dumps({'shape':sh,'IR':b,'complement':sorted(comp)}),flush=True)
print(json.dumps({'n':n,'mode':mode,'p':p,'samples':cnt,'shapes':sorted(found)}))
