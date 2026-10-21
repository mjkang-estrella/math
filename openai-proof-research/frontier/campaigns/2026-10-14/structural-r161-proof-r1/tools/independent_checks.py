#!/usr/bin/env python3
"""Small independent exact checks. Evidence only; never a proof premise."""
from collections import Counter, defaultdict
from fractions import Fraction as F
from itertools import combinations, combinations_with_replacement, permutations, product
from math import factorial, prod
from pathlib import Path
import json
ROOT = Path(__file__).resolve().parents[1]

def compositions(n, r):
    if r == 1:
        yield (n,)
    else:
        for i in range(n+1):
            for c in compositions(n-i, r-1):
                yield (i,)+c

def partitions(vertices, q):
    if not vertices:
        yield ()
        return
    for tail in combinations(vertices[1:], q-1):
        edge = (vertices[0],)+tail
        left = tuple(x for x in vertices if x not in edge)
        for rest in partitions(left,q):
            yield (edge,)+rest

def falling(n,k):
    return prod(n-i for i in range(k))

def table(M,z,ell):
    return Counter(tuple(sum(z[v]==u for v in e) for u in range(ell)) for e in M)

def key(t):
    return tuple(sorted((a,c) for a,c in t.items() if c))

cases = []
containment_checks = 0
# Includes ell=1, h=1, all cells singletons, unbalanced positive sizes and zero types.
for q,N in [(3,3),(3,6),(4,4),(5,5)]:
    Ms = list(partitions(tuple(range(N)),q))
    partials = {tuple(E) for M in Ms for k in range(N//q+1) for E in combinations(M,k)}
    for ell in range(1,N+1):
        types=list(compositions(q,ell))
        admissible=defaultdict(set)
        for alpha_list in combinations_with_replacement(types,N//q):
            s=tuple(sum(a[u] for a in alpha_list) for u in range(ell))
            if min(s)>0:admissible[s].add(key(Counter(alpha_list)))
        for s in compositions(N,ell):
            if min(s)==0:continue
            z=tuple(u for u,n in enumerate(s) for _ in range(n))
            groups=defaultdict(list)
            for M in Ms:groups[key(table(M,z,ell))].append(M)
            assert set(groups)==admissible[s]
            Z=factorial(N)//prod(factorial(n) for n in s)
            for tk,fiber in groups.items():
                t=dict(tk)
                D=F(factorial(N//q),prod(factorial(c) for c in t.values()))
                D*=prod((factorial(q)//prod(factorial(x) for x in a))**c for a,c in t.items())
                assert F(len(fiber),len(Ms))==D/Z
                for E in partials:
                    m=table(E,z,ell)
                    au=tuple(sum(a[u]*c for a,c in m.items()) for u in range(ell))
                    num=prod(falling(t.get(a,0),c)*prod(factorial(x) for x in a)**c for a,c in m.items())
                    den=prod(falling(s[u],au[u]) for u in range(ell))
                    assert den>0
                    actual=F(sum(all(e in M for e in E) for M in fiber),len(fiber))
                    assert actual==F(num,den)
                    containment_checks+=1
                cases.append({'q':q,'N':N,'ell':ell,'s':s,'table':tk,'fiber_size':len(fiber)})

# Independently sum the ordered-word law of every two-block joint table on four colors.
# Check that collapse commutes with P_v, including zero color counts.
q=3;h=2;r=4
joint_count=0;equal_tuple_marginal_count=0
for beta_list in combinations_with_replacement(list(compositions(q,r)),h):
    law=defaultdict(F)
    for beta in beta_list:
        word=tuple(j for j,c in enumerate(beta) for _ in range(c))
        words=set(permutations(word))
        for w in words:law[w]+=F(1,h*len(words))
    assert sum(law.values())==1
    marg_a=defaultdict(F);marg_b=defaultdict(F);coord=defaultdict(F)
    for w,p in law.items():
        marg_a[tuple(j//2 for j in w)]+=p
        marg_b[tuple(j%2 for j in w)]+=p
        coord[w[0]]+=p
    for side,marg in [(0,marg_a),(1,marg_b)]:
        collapsed=Counter()
        for beta in beta_list:
            alpha=tuple(sum(beta[j] for j in range(r) if (j//2 if side==0 else j%2)==u) for u in range(2))
            collapsed[alpha]+=1
        for w in product(range(2),repeat=q):
            alpha=tuple(w.count(u) for u in range(2))
            expected=F(collapsed[alpha],h)*F(prod(factorial(c) for c in alpha),factorial(q))
            assert marg[w]==expected
    for j in range(r):assert coord[j]==F(sum(beta[j] for beta in beta_list),q*h)
    joint_count+=1
    equal_tuple_marginal_count+=marg_a==marg_b

result={'purpose':'Independent finite counterchecks only, not proof gates','feasible_table_cases':len(cases),'containment_checks':containment_checks,'joint_tables':joint_count,'joint_tables_with_equal_collapsed_tables':equal_tuple_marginal_count,'cases':cases}
(ROOT/'private/independent-results.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k!='cases'}))
