import itertools, math, collections, json
from pathlib import Path
R=Path(__file__).resolve().parent.parent

def s(w):
    if not w: return ()
    m=max(w); k=w.index(m)
    return s(w[:k])+s(w[k+1:])+(m,)

def pairs(labels):
    d=collections.defaultdict(list)
    for w in itertools.permutations(labels): d[s(w)].append(w)
    return [(u,v) for g in d.values() for u in g for v in g]

P=[len(pairs(range(n))) for n in range(8)]
assert P == [1,1,4,26,224,2356,29064,411172]
checks=0
for n in range(7):
    interior=set(); ends=set()
    for i in range(n+1):
        images=set()
        for A in itertools.combinations(range(n),i):
            B=tuple(x for x in range(n) if x not in A)
            def label(x): return A[x] if x<i else max(A,default=0)+1+x-i
            assert all(label(x)<label(x+1) for x in range(n+3))
            for w in itertools.permutations(range(i)):
                assert s(tuple(label(x) for x in w)) == tuple(label(x) for x in s(w))
            for (L,Lp),(T,Tp) in itertools.product(pairs(A),pairs(B)):
                u=L+(n,)+T; v=Lp+(n,)+Tp
                assert sorted(u)==list(range(n+1)) and s(u)==s(v)
                assert (u,v) not in images
                images.add((u,v)); checks+=1
        assert len(images)==math.comb(n,i)*P[i]*P[n-i]
        if 0<i<n:
            assert interior.isdisjoint(images)
            interior |= images
    if n:
        for u,v in pairs(range(n)):
            for b,c in itertools.product((False,True),repeat=2):
                p=((n,)+u if b else u+(n,), (n,)+v if c else v+(n,))
                assert s(p[0])==s(p[1])
                assert p not in ends
                ends.add(p)
        assert len(ends)==4*P[n]
        assert interior.isdisjoint(ends)
        assert len(interior|ends)<=P[n+1]
for a in range(4): assert math.comb(2*a,a)*P[a]**2<=P[2*a+1]

def tuples(n):
    for w in itertools.permutations(range(n)):
        if n==0: yield (); continue
        for mask in range(1<<(n-1)):
            cuts=[0]+[k for k in range(1,n) if mask>>(k-1)&1]+[n]
            yield tuple(w[a:b] for a,b in zip(cuts,cuts[1:]))

def output(F): return sum((s(w) for w in F),())
def boundaries(F): return set(itertools.accumulate((len(w) for w in F),initial=0))
def irr(F,G): return not ((boundaries(F)&boundaries(G))-{0,len(output(F))})
for n in range(1,5):
    fam=list(tuples(n)); phi=lambda x:2*x+1
    image=lambda F:tuple(tuple(phi(x) for x in w) for w in F)
    for F in fam:
        assert output(image(F))==tuple(phi(x) for x in output(F))
        assert boundaries(F)==boundaries(image(F))
    for F,G in itertools.product(fam,repeat=2):
        assert (output(F)==output(G))==(output(image(F))==output(image(G)))
        assert irr(F,G)==irr(image(F),image(G))
result={'literal_P_0_7':P,'root_image_checks':checks,'label_subset_max_n':6,'tuple_invariance_max_n':4,'doubling_max_a':3,'all_passed':True,'is_combinatorial_proof':False}
(R/'regression.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
