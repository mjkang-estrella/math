# Finite exact checks of new counts and trace normalization, not mathematical gates.
from pathlib import Path
from itertools import combinations, product
from collections import defaultdict, Counter
from math import factorial, prod, comb
from fractions import Fraction
import json
R=Path('frontier/campaigns/2026-10-14/fresh-structural-discovery-r161')
def parts(vertices,q):
    if not vertices:
        yield ();return
    first=vertices[0]
    for rest in combinations(vertices[1:],q-1):
        block=(first,)+rest; chosen=set(block)
        for tail in parts(tuple(x for x in vertices if x not in chosen),q):yield (block,)+tail
def comps(n,r):
    if r==1:yield (n,);return
    for j in range(n+1):
        for tail in comps(n-j,r-1):yield (j,)+tail
def colorings(s):
    n=sum(s)
    def rec(avail,remaining,prefix):
        if len(remaining)==1:
            out=dict(prefix);out.update((v,len(s)-1) for v in avail)
            yield tuple(out[v] for v in range(n));return
        color=len(s)-len(remaining)
        for chosen in combinations(avail,remaining[0]):
            taken=set(chosen)
            yield from rec(tuple(v for v in avail if v not in taken),remaining[1:],prefix+tuple((v,color) for v in chosen))
    yield from rec(tuple(range(n)),s,())
def fall(n,k):return factorial(n)//factorial(n-k) if k<=n else 0
results=[]
for q,N,ell,sizes in [(3,6,2,None),(3,9,2,None),(3,6,3,[(1,2,3),(2,2,2)]),(4,8,2,None)]:
    Ms=list(parts(tuple(range(N)),q));types=list(comps(q,ell));ti={a:i for i,a in enumerate(types)}
    for s in (sizes or [(w,N-w) for w in range(1,N)]):
        Zs=list(colorings(s));groups=defaultdict(list)
        for i,z in enumerate(Zs):
            for j,M in enumerate(Ms):
                cnt=[0]*len(types)
                for e in M:cnt[ti[tuple(sum(z[v]==u for v in e) for u in range(ell))]]+=1
                groups[tuple(cnt)].append((i,j))
        for t,inc in groups.items():
            B=[set() for _ in Zs]
            for i,j in inc:B[i].add(j)
            a=len(B[0]);D=sum(0 in row for row in B);h=N//q
            formulaD=Fraction(factorial(h),prod(factorial(x) for x in t))*prod(Fraction(factorial(q),prod(factorial(x) for x in alpha))**count for alpha,count in zip(types,t))
            assert formulaD==D and all(len(row)==a for row in B) and all(sum(j in row for row in B)==D for j in range(len(Ms)))
            assert a*len(Zs)==D*len(Ms)
            G=[[len(ri & rj) for rj in B] for ri in B]
            row2=[sum(G[0][j]*G[j][i] for j in range(len(B))) for i in range(len(B))]
            diagonal=sum(row2[i]*G[i][0] for i in range(len(B))) if q==3 else sum(x*x for x in row2)
            # Equivariance makes every diagonal entry of G^q equal.
            trace=Fraction(len(Zs)*diagonal,(a*D)**q)
            assert 1<=trace<=len(Zs)
            # Check degree1 and degree2 containment against exact conditional enumeration.
            z=Zs[0];matching_indices=[j for j in range(len(Ms)) if j in B[0]]
            for E in [Ms[0][:1],Ms[0][:2]]:
                ma=Counter(tuple(sum(z[v]==u for v in e) for u in range(ell)) for e in E)
                au=[sum(z[v]==u for e in E for v in e) for u in range(ell)]
                predicted=Fraction(prod(fall(t[ti[alpha]],count)*prod(factorial(x) for x in alpha)**count for alpha,count in ma.items()),prod(fall(s[u],au[u]) for u in range(ell)))
                actual=Fraction(sum(all(e in Ms[j] for e in E) for j in matching_indices),a)
                assert predicted==actual
            results.append({'q':q,'N':N,'ell':ell,'s':s,'types':types,'table':t,'row_degree':a,'column_degree':D,'trace_q':str(trace)})
print('Exact finite checks:',len(results),'table/size cases; all incidence marginals, D formula, trace normalization and selected degree1/2 containment agree.')
(R/'private/table-diagnostic.json').write_text(json.dumps({'purpose':'Finite author diagnostics, not independent correctness/contribution gates; full proof is symbolic','cases':results},indent=2)+'\n')
