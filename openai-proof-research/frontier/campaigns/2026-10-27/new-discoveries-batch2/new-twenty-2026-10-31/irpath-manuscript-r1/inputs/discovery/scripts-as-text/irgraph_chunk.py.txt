# chunked extension search: base = nonisomorphic graphs on N-1 vertices (cached), extend by every neighbourhood.
import sys,json,time,importlib.util
from collections import Counter
L=sys.argv[1]; N=int(sys.argv[2]); lo=int(sys.argv[3]); hi=int(sys.argv[4])
s=importlib.util.spec_from_file_location('ir',L+'/scripts/irgraph.py'); ir=importlib.util.module_from_spec(s); s.loader.exec_module(ir)
cache=L+f'/outputs/noniso-{N-1}.json'
try: base=json.load(open(cache))
except FileNotFoundError:
    base=ir.graphs(N-1)[N-1]; json.dump(base,open(cache,'w'))
    print('cached',len(base)); sys.exit(0)
POP=[bin(i).count('1') for i in range(1<<N)]
BYSIZE={N:sorted(range(1,1<<N),key=lambda D:-POP[D])}
def irfast(n,adj):
    N=[adj[v]|(1<<v) for v in range(n)]
    best=0;sets=[]
    for D in BYSIZE[n]:
        k=POP[D]
        if k<best: break
        ok=True;x=D
        while x:
            b=x&-x;v=b.bit_length()-1
            others=0;y=D^b
            while y:
                c=y&-y;others|=N[c.bit_length()-1];y^=c
            if not N[v]&~others: ok=False;break
            x^=b
        if ok:
            if k>best: best=k;sets=[D]
            else: sets.append(D)
    S=set(sets); m=len(sets); deg={}; E=0
    for A in sets:
        d=0;x=A
        while x:
            b=x&-x;a=b.bit_length()-1;x^=b
            y=adj[a]&~A
            while y:
                c=y&-y;y^=c
                if (A^b)|c in S: d+=1
        deg[A]=d;E+=d
        if d>2: return best,m,None
    return best,m,(deg,E//2,sets,S)
def shape2(n,adj,m,info):
    if info is None: return 'other'
    deg,E,sets,S=info
    if m<2: return 'K1'
    # connectivity via BFS on sets
    seen={sets[0]};st=[sets[0]]
    while st:
        A=st.pop();x=A
        while x:
            b=x&-x;a=b.bit_length()-1;x^=b
            y=adj[a]&~A
            while y:
                c=y&-y;y^=c;B=(A^b)|c
                if B in S and B not in seen: seen.add(B);st.append(B)
    if len(seen)<m: return 'disconnected'
    if E==m-1: return 'path%d'%m
    if E==m: return 'cycle%d'%m
    return 'other'
t0=time.time(); tally=Counter(); hits=[]; treehits=0; treeshapes=Counter()
for g in base[lo:hi]:
    for nb in range(1<<(N-1)):
        adj=g[:]+[nb]
        for u in range(N-1):
            if nb>>u&1: adj[u]|=1<<(N-1)
        if not ir.connected(N,adj): continue
        b,m,info=irfast(N,adj); sh=shape2(N,adj,m,info)
        key=sh if not sh.startswith(('tree','path','cycle')) or sh in('path2','cycle3','cycle4') else sh
        tally[key]+=1
        if (sh.startswith('path') and m>=3) or (sh.startswith('cycle') and m>=5): hits.append((adj,sh,b))
print(json.dumps({'N':N,'lo':lo,'hi':min(hi,len(base)),'nbase':len(base),'secs':round(time.time()-t0,1),'tally':dict(tally),'path_cycle_hits':hits}))
