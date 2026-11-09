import itertools,json,pathlib
L=pathlib.Path(__file__).resolve().parents[1]
# Independent arithmetic/set checks of already-public objections, no discovery claim.
group=list(range(4));pairs=list(itertools.combinations(group,2));assert all(a^b for a,b in pairs)
checks=[dict(mathdb_id=330176,status='executed',scope='literal low-k inconsistency only, no corrected-source theorem claim',group='C2 x C2 encoded by xor',sequence=group,predicted_length=2+3-1,zero_sum_pairs=0,pairs_checked=len(pairs),novelty=False)]
E={tuple(sorted((3*j+a,3*j+b))) for j in range(4) for a,b in itertools.combinations(range(3),2)}
S=list(itertools.combinations(range(12),5));ind=[s for s in S if all(tuple(sorted(e)) not in E for e in itertools.combinations(s,2))];assert len(E)==12 and not ind
checks.append(dict(mathdb_id=331133,status='executed',scope='source Figure 2 witness',n=12,G1='4K3',G2='K5 + 7K1',edges=[12,10],maximum_degrees=[2,4],lhs=26,rhs=29,five_subsets_checked=len(S),independent_five_subsets=0,novelty=False))
(L/'bounded-checks.json').write_text(json.dumps(checks,indent=2)+'\n');print(json.dumps(checks,indent=2))
