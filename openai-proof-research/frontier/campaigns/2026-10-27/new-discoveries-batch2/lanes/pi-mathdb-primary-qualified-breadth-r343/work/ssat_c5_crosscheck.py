# Cross-validation: path-checker vs literal C5-count definition. Plus re-verify n=6 m=7 exhaustively.
import itertools

def c5_count(n, es):
    es=set(es); cnt=0
    for p in itertools.permutations(range(n),5):
        a,b,c,d,e = p
        if a!=min(p): continue  # canonical: smallest first, fix rotation/reflection
        # cycle a-b-c-d-e-a
        E={(a,b),(b,c),(c,d),(d,e),(e,a)}
        if E <= es: cnt+=1
    return cnt

def semisat_count(n, es):
    base=c5_count(n,es)
    alles=set(itertools.combinations(range(n),2))
    for e in set(alles)-set(es):
        if c5_count(n, set(es)|{e}) <= base: return False
    return True

def semisat_path(n, es):
    adj=[0]*n
    for a,b in es: adj[a]|=1<<b; adj[b]|=1<<a
    for u in range(n):
        for v in range(u+1,n):
            if (adj[u]>>v)&1: continue
            ok=False
            for x in range(n):
                if x in (u,v) or not (adj[u]>>x)&1: continue
                for y in range(n):
                    if y in (u,v,x) or not (adj[x]>>y)&1: continue
                    for z in range(n):
                        if z in (u,v,x,y): continue
                        if (adj[y]>>z)&1 and (adj[z]>>v)&1: ok=True;break
                    if ok:break
                if ok:break
            if not ok: return False
    return True

# 1) agreement on all graphs n=6, m<=7
import random
bad=0
for n in [5,6]:
    edges=list(itertools.combinations(range(n),2))
    for m in range(0,8):
        for es in itertools.combinations(edges,m):
            if semisat_count(n,es)!=semisat_path(n,es):
                bad+=1; print("MISMATCH",n,es); break
print("checker agreement over n=5,6 m<=7: mismatches =",bad)

# 2) exhaustive n=6, m=7 with the count definition
es6=list(itertools.combinations(range(6),2))
hits=[es for es in itertools.combinations(es6,7) if semisat_count(6,es)]
print("n=6 m=7 semisaturated graphs (count-def):",len(hits), hits[:1])

# 3) verify witnesses from the first run
w5=[(0,1),(0,2),(0,3),(0,4),(1,2),(3,4)]
w6=[(0,1),(0,2),(0,3),(0,4),(0,5),(1,2),(1,3),(2,4)]
w7=[(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,2),(3,4),(5,6)]
for n,w in [(5,w5),(6,w6),(7,w7)]:
    print(f"n={n} witness semisat(path)={semisat_path(n,w)} semisat(count)={semisat_count(n,w)}")
