import itertools,json,pathlib
D=pathlib.Path(__file__).resolve().parents[1];V=[(-1,0)]+[(i,j) for i in range(3) for j in range(1,6)]
def d(x,y):return abs(x[1]-y[1]) if x[0]==y[0] else x[1]+y[1]
seq=[(1,1),(2,3),(0,4),(1,5)]
coverage={str(v):[i+1 for i,x in enumerate(seq) if d(v,x)<=3-i] for v in V};assert all(coverage.values())
assert all(d(seq[i],seq[j])>=j-i for i in range(4) for j in range(i+1,4))
assert all(d((i,4),(j,4))==8 for i in range(3) for j in range(i+1,3))
F=list(itertools.product(range(3),range(2)))
def fd(x,y):return abs(x[1]-y[1]) if x[0]==y[0] else 100
bad3=0
for xs in itertools.product(F,repeat=3):
 if all(any(fd(v,x)<=2-i for i,x in enumerate(xs)) for v in F):bad3+=1
assert bad3==0
rec={'spider_arm_edges':[5,5,5],'vertex_count':16,'source_sequence':seq,'coverage':coverage,'source_pairwise_time_separation':True,'nonterminal_depth':4,'nonterminal_pairwise_distance':8,'forest':'3 disjoint P2','forest_3_round_sequences_examined':6**3,'forest_3_round_successes':bad3,'ordinary_refutation_valid':True,'eligibility':'not nominated: printed companion construction plus elementary forest count'}
(D/'outputs/spider-verified.json').write_text(json.dumps(rec,indent=2)+'\n');print(rec)
