# All connected regular graphs on n<=6 vertices (up to iso): compute D'(G) by brute force.
import itertools
def canon(n,E):
    best=None
    for p in itertools.permutations(range(n)):
        f=tuple(sorted(tuple(sorted((p[u],p[v]))) for u,v in E))
        if best is None or f<best: best=f
    return best
def connected(n,E):
    adj={i:set() for i in range(n)}
    for u,v in E: adj[u].add(v); adj[v].add(u)
    seen={0}; st=[0]
    while st:
        x=st.pop()
        for y in adj[x]:
            if y not in seen: seen.add(y); st.append(y)
    return len(seen)==n
res=[]
for n in range(3,7):
    pairs=list(itertools.combinations(range(n),2)); seen=set()
    for mask in range(1,1<<len(pairs)):
        E=[pairs[i] for i in range(len(pairs)) if mask>>i&1]
        deg=[0]*n
        for u,v in E: deg[u]+=1; deg[v]+=1
        if len(set(deg))!=1 or not connected(n,E): continue
        c=canon(n,E)
        if c in seen: continue
        seen.add(c)
        Es=[tuple(e) for e in c]; eidx={e:i for i,e in enumerate(Es)}
        auts=[]
        for p in itertools.permutations(range(n)):
            img=[eidx.get(tuple(sorted((p[u],p[v])))) for u,v in Es]
            if None not in img and p!=tuple(range(n)): auts.append(img)
        def dist(col):
            return all(any(col[img[i]]!=col[i] for i in range(len(Es))) for img in auts)
        D=None
        for d in (1,2,3,4):
            if any(dist(col) for col in itertools.product(range(d),repeat=len(Es))): D=d; break
        res.append((n,deg[0],len(Es),len(auts)+1,D))
        print('n',n,'k',deg[0],'edges',Es,'|Aut|',len(auts)+1,"D'",D,flush=True)
