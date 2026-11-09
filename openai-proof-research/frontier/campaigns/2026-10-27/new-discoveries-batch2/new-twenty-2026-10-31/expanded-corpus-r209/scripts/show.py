import sys,json,itertools
adj=json.loads(sys.argv[1]); n=len(adj)
E=[(i,j) for i in range(n) for j in range(i+1,n) if adj[i]>>j&1]
C=[(i,j) for i in range(n) for j in range(i+1,n) if not adj[i]>>j&1]
nbr={v:{u for u in range(n) if adj[v]>>u&1} for v in range(n)}
def priv(v,D):
    o=set()
    for u in D:
        if u!=v: o|=nbr[u]|{u}
    return (nbr[v]|{v})-o
irr=[D for k in range(n+1) for D in itertools.combinations(range(n),k) if all(priv(v,D) for v in D)]
IR=max(map(len,irr)); S=[frozenset(D) for D in irr if len(D)==IR]
adjS={A:[B for B in S if len(A-B)==1 and next(iter(B-A)) in nbr[next(iter(A-B))]] for A in S}
end=[A for A in S if len(adjS[A])==1][0]; walk=[end]; prev=None
while True:
    nx=[B for B in adjS[walk[-1]] if B!=prev]
    if not nx: break
    prev=walk[-1]; walk.append(nx[0])
print('n',n,'|E|',len(E),'IR',IR,'#IRsets',len(S),'path?',len(walk)==len(S))
print('complement',C)
print('walk',[sorted(A) for A in walk])
print('indep IR-sets',[sorted(A) for A in walk if not any(b in nbr[a] for a in A for b in A)])
print('triangles in complement',[t for t in itertools.combinations(range(n),3) if all(t[j] not in nbr[t[i]] for i in range(3) for j in range(i+1,3))])
