import itertools,sys
def run(n,maxedges):
    pairs=list(itertools.combinations(range(n),2))
    checked=0;lemma_cases=0;bad=0;gap=0
    for mask in range(1<<len(pairs)):
        E=[pairs[i] for i in range(len(pairs)) if mask>>i&1]
        if len(E)>maxedges: continue
        valid=[]
        for o in range(1<<len(E)):
            arcs=[(a,b) if not (o>>i&1) else (b,a) for i,(a,b) in enumerate(E)]
            indeg=[0]*n
            for a,b in arcs: indeg[b]+=1
            if min(indeg)>0: valid.append(frozenset(arcs))
        if not valid: continue
        def tdsets(D):
            out=[]
            for S in range(1<<n):
                if all(any((u,v) in D and S>>u&1 for u in range(n)) for v in range(n)): out.append(S)
            return out
        TD={D:tdsets(D) for D in valid}
        spec=sorted({min(bin(s).count('1') for s in TD[D]) for D in valid})
        if spec!=list(range(spec[0],spec[-1]+1)): gap+=1
        for D in valid:
            for F in valid:
                delta=[(a,b) for (a,b) in D if (b,a) in F]
                if all(sum(1 for (x,y) in D if y==b)==1 for (a,b) in delta):
                    lemma_cases+=1
                    tf=set(TD[F])
                    if any(s not in tf for s in TD[D]): bad+=1
        checked+=1
    return checked,lemma_cases,bad,gap
for n,me in [(3,3),(4,6),(5,7)]:
    print(n,me,run(n,me),flush=True)
