# Iterated one-vertex extension: start from graphs in an input JSON list (adjacency bitmasks on n vertices);
# try every neighbourhood of a new vertex; keep extensions whose IR-graph is a path P_m (m>=3) or cycle C_m (m>=5).
import sys,json,random,time
inp,outp,maxkeep,budget=sys.argv[1],sys.argv[2],int(sys.argv[3]),float(sys.argv[4])
graphs=json.load(open(inp)); n=len(graphs[0])+1
POP=[bin(i).count('1') for i in range(1<<n)]
BYSIZE=sorted(range(1,1<<n),key=lambda D:-POP[D])
def irsets(adj,cap=80):
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
def shape(adj):
    b,sets=irsets(adj)
    if not sets or len(sets)<3: return None
    S=set(sets); nb={}; E=0
    for A in sets:
        l=[];x=A
        while x:
            bb=x&-x;a=bb.bit_length()-1;x^=bb
            y=adj[a]&~A
            while y:
                c=y&-y;y^=c;B=(A^bb)|c
                if B in S: l.append(B)
        if len(l)>2: return None
        nb[A]=l;E+=len(l)
    E//=2; m=len(sets); seen={sets[0]}; st=[sets[0]]
    while st:
        X=st.pop()
        for B in nb[X]:
            if B not in seen: seen.add(B); st.append(B)
    if len(seen)<m: return None
    if E==m-1: return ('P',m,b)
    if E==m and m>=5: return ('C',m,b)
    return None
t0=time.time(); keep=[]; tally={}
random.seed(1); random.shuffle(graphs)
for g in graphs:
    if time.time()-t0>budget: break
    for nb in range(1,1<<(n-1)):
        adj=list(g)+[nb]
        for u in range(n-1):
            if nb>>u&1: adj[u]|=1<<(n-1)
        sh=shape(adj)
        if sh:
            key=sh[0]+str(sh[1]); tally[key]=tally.get(key,0)+1
            if len(keep)<maxkeep or sh[0]=='C': keep.append((key,adj))
done=graphs.index(g)+1 if graphs else 0
best={}
for key,adj in keep: best.setdefault(key,adj)
json.dump([adj for key,adj in keep],open(outp,'w'))
print(json.dumps({'n':n,'inputs':len(graphs),'processed':done,'secs':round(time.time()-t0,1),'tally':tally,'examples':best}))
