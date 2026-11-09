# Check consistency with Mynhardt-Roux Lemma Lem_Not_Path on the P9 example, and with Brewster's closed-neighbourhood definition.
import itertools,json
E=[(0,3),(0,4),(0,6),(0,7),(1,3),(1,5),(1,6),(1,7),(1,8),(2,4),(2,5),(2,7),(2,8),(3,6),(3,8),(4,6),(4,7),(4,8),(5,7),(5,8)]
n=9; nbr={v:set() for v in range(n)}
for a,b in E: nbr[a].add(b); nbr[b].add(a)
cl=lambda v: nbr[v]|{v}
def irr1(D): return all(cl(v)-set().union(*[cl(u) for u in D if u!=v]) for v in D)
def irr2(D): return all(not cl(v)<=set().union(*[cl(u) for u in D if u!=v]) for v in D)
subs=[D for k in range(n+1) for D in itertools.combinations(range(n),k)]
assert all(irr1(D)==irr2(D) for D in subs)
S=[frozenset(D) for D in subs if len(D)==3 and irr1(D)]
assert not any(irr1(D) for D in subs if len(D)>=4)
adj={A:{B for B in S if len(A-B)==1 and next(iter(B-A)) in nbr[next(iter(A-B))]} for A in S}
# distances
def dist(A,B):
    fr={A};seen={A};d=0
    while B not in fr:
        fr={C for X in fr for C in adj[X]}-seen; seen|=fr; d+=1
        if not fr: return None
    return d
def EPN(v,X): return {w for w in nbr[v] if w not in X and not any(w in cl(u) for u in X if u!=v)}
report=[]
for X in S:
    pos=[x for x in X if any(y in nbr[x] for y in X if y!=x)]
    if len(pos)!=3: continue
    xs=sorted(X)
    for choice in itertools.product(*[sorted(EPN(x,X)) for x in xs]):
        Xp=frozenset(choice)
        isIR=Xp in S
        report.append((xs,list(choice),isIR,dist(X,Xp) if isIR else None))
print(json.dumps({'IRsets':[sorted(A) for A in S],'flip_checks':report}))
