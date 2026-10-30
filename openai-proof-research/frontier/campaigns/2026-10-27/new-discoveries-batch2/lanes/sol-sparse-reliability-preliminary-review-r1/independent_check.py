"""Independent diagnostic: BFS couplings and integer terminal-mask integration.
Run through the specified helper_guard.py; no third-party packages.
Finite checks are not an all-order proof.
"""
from itertools import combinations, product
from fractions import Fraction
from pathlib import Path
import json

D = Path(__file__).resolve().parent
counts = dict(coupled_outcomes=0, cores=0, ordered_pair_bounds=0, replacements=0,
              principal_association=0, budget_states=0)

def success(edges):
    frontier, seen = {0}, {0}
    for _ in range(3):
        frontier = {v if u in frontier else u for u,v in edges
                    if u in frontier or v in frontier} - seen
        seen |= frontier
    return 1 in seen

# Every present/failed/absent assignment of the ten possible edges on five
# vertices. The survival-bit bijection tests path preservation, not probabilities.
universe = list(combinations(range(5),2))
for status in product(range(3), repeat=len(universe)):
    host = {e for e,s in zip(universe,status) if s}
    live = {e for e,s in zip(universe,status) if s==2}
    if not success(live):
        continue
    if (0,1) not in host:
        for e in host:
            target = live-{e}
            if e in live: target.add((0,1))
            assert success(target), ('direct',status,e)
            counts['coupled_outcomes'] += 1
    for x in range(2,5):
        terminals = [t for t in (0,1) if (t,x) in host]
        if len(terminals)!=1: continue
        missing = (1-terminals[0],x)
        for e in host:
            if min(e)<2 or x not in e: continue
            target=live-{e}
            if e in live: target.add(missing)
            assert success(target), ('single',status,x,e)
            counts['coupled_outcomes'] += 1

def measure(a, edges, num, den):
    # Enumerate 2a terminal-edge bits directly; integrate failed interior edges.
    # Only masks with no fully surviving terminal path are admitted.
    entries=[]; Znum=0
    for mask in range(1<<(2*a)):
        if any((mask>>(2*i)&3)==3 for i in range(a)): continue
        states=tuple((mask>>(2*i))&3 for i in range(a)) # 0 neither, 1 s, 2 t
        bad=sum({states[i],states[j]}=={1,2} for i,j in edges)
        alive=mask.bit_count()
        weight=num**alive*(den-num)**(2*a-alive+bad)*den**(len(edges)-bad)
        entries.append((states,weight));Znum+=weight
    Z=Fraction(Znum,(den*den-num*num)**a*den**len(edges))
    return Z,entries,Znum

for a in range(5):
    possible=list(combinations(range(a),2))
    for mask in range(1<<len(possible)):
        edges=[e for i,e in enumerate(possible) if mask>>i&1]
        for num,den in [(1,5),(1,2),(4,5)]:
            z,entries,total=measure(a,edges,num,den)
            u=Fraction(num,den+num);p=Fraction(num,den)
            for i in range(a):
                for v in (1,2):
                    assert Fraction(sum(w for s,w in entries if s[i]==v),total)<=u
                for j in range(a):
                    if i==j:continue
                    assert Fraction(sum(w for s,w in entries if s[i]==1 and s[j]==2),total)<=u*u
                    counts['ordered_pair_bounds']+=1
            # All principal upper events on the full three-state product lattice.
            order={2:0,0:1,1:2}
            events=[{i for i,(s,w) in enumerate(entries) if all(order[x]>=y for x,y in zip(s,t))}
                    for t in product(range(3),repeat=a)]
            weights=[w for s,w in entries]
            masses=[sum(weights[i] for i in event) for event in events]
            for i,E in enumerate(events):
                for j in range(i,len(events)):
                    assert total*sum(weights[k] for k in E&events[j])>=masses[i]*masses[j]
                    counts['principal_association']+=1
            for k in range(min(2,len(edges))+1):
                for rem in combinations(edges,k):
                    reduced=[e for e in edges if e not in rem]
                    z0,_,_=measure(a,reduced,num,den)
                    assert z/z0 >= 1-p*p
                    counts['replacements']+=1
            counts['cores']+=1

# Abstract budget/vertex feasibility, independent of probability values.
for n in range(5,41):
    for m in range(5,2*n-2):
        for initial_a in range(n-1):
            for initial_e in range(min(initial_a*(initial_a-1)//2,m-1-2*initial_a)+1):
                a,e,t=initial_a,initial_e,m-1-2*initial_a-initial_e
                if t<0:continue
                while e+t>=2:
                    assert a<n-2
                    k=min(e,2);assert t>=2-k
                    a+=1;e-=k;t-=2-k
                assert a==(m-1)//2
                if m%2==0: assert a>=2 and e+t==1
                else: assert e==t==0
                counts['budget_states']+=1

def half_reliability(edges):
    return Fraction(sum(success({e for i,e in enumerate(edges) if mask>>i&1})
                        for mask in range(1<<len(edges))),1<<len(edges))
H10=[(0,1)]+[(t,v) for v in range(2,6) for t in (0,1)]+[(2,3)]
H9=H10[:-1]
witness=[str(half_reliability([e for e in H10 if e!=(0,2)])),str(half_reliability(H9))]
assert witness==['413/512','431/512']
out={'status':'PASS; bounded diagnostics, not proof','counts':counts,
     'source_deletion_countermodel':witness,
     'scope':'five-vertex coupling states; all cores through four vertices at p=1/5,1/2,4/5; n<=40 budget states',
     'not_checked':'all increasing functions; unbounded graph orders; literature novelty'}
(D/'independent-evidence.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out))
