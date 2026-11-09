import itertools,json,pathlib
D=pathlib.Path(__file__).resolve().parents[1]
# Independent definition-level enumeration, deliberately not using source formula.
p=[0]*5;q=[0]*5
for a in itertools.permutations(range(5)):
 inv=sum(a[i]>a[j] for i in range(5) for j in range(i+1,5));exc=sum(x>i for i,x in enumerate(a));(p if inv%2==0 else q)[exc]+=1
assert p==[1,11,36,11,1] and q==[0,15,30,15,0]
# P5/t^2=(t+1/t+11/2)^2+15/4, hence positive for every nonzero real t.
# Mycielski K9 graph.
es=list(itertools.combinations(range(9),2))+[(i,9+j) for i in range(9) for j in range(9) if i!=j]+[(18,9+j) for j in range(9)]
a=[set() for _ in range(19)]
for u,v in es:a[u].add(v);a[v].add(u)
cliques10=sum(all(v in a[u] for u,v in itertools.combinations(s,2)) for s in itertools.combinations(range(19),10))
assert cliques10==0
profile=[2,2,2,10,16];assert sum(profile)==32 and min(profile)>=2 and max(profile)<=16 and sum(profile[:3])<8
out={'excedance_n5':{'even':p,'odd':q,'permutations':120,'classification':'source-formula/smallest-parameter correction, excluded'},'biplanar_route':{'base':'Mycielski K9','vertices':19,'edges':len(es),'K10_count':cliques10,'base_edges':es,'subdivision_vertices':19+len(es),'classification':'routine classical construction plus source subdivision forcing, excluded'},'hypercube':{'n':5,'profile':profile,'violated_three_direction_lower_bound':[sum(profile[:3]),8],'classification':'source Remark 3.3, excluded'}}
(D/'exclusion-diagnostics.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
