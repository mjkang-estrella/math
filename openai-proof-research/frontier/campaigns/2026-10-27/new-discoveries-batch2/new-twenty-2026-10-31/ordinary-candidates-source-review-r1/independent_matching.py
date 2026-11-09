import itertools,json,pathlib,resource
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,512*1024**2));resource.setrlimit(resource.RLIMIT_CPU,(20,20))
r=pathlib.Path(__file__).parent
E=[(0,1),(0,2),(2,3),(3,4),(4,5),(0,6),(6,7),(1,8),(8,9),(1,10),(10,11),(4,7)]
# Independent traversal: enumerate endpoint-disjoint edge combinations by cardinality.
C=[]
for k in range(7):
 for c in itertools.combinations(range(12),k):
  vs=[v for i in c for v in E[i]]
  if len(set(vs))==2*k:C.append(frozenset(c))
nu=max(map(len,C));Ms=[m for m in C if len(m)==nu]
pairs=[(a,b) for a in C for b in C if a.isdisjoint(b)]
lam=max(len(a)+len(b) for a,b in pairs);pairs=[(a,b) for a,b in pairs if len(a)+len(b)==lam]
mu=max(len(a) for a,b in pairs);pairs=[(a,b) for a,b in pairs if len(a)==mu]
T=[(m,a,b) for m in Ms for a,b in pairs];o1=max(len(m&(a|b)) for m,a,b in T);T1=[t for t in T if len(t[0]&(t[1]|t[2]))==o1];o2=max(len(m&a) for m,a,b in T1);T2=[t for t in T1 if len(t[0]&t[1])==o2]
w=(frozenset([0,2,4,6,8,10]),frozenset([2,4,5,8,9]),frozenset([1,3,6,7,10]));assert w in T2
P=[7,6,0,1,10,11];Q=[5,4,3,2,0,6,7]
def checkpath(P,A,B):
 ids=[E.index(tuple(sorted((u,v)))) for u,v in zip(P,P[1:])]
 assert len(P)==len(set(P)); assert all((i in A)!=(i in B) for i in ids)
 assert all((ids[j] in A)!=(ids[j+1] in A) for j in range(len(ids)-1))
 assert all(set(E[i]).isdisjoint({P[0],P[-1]}) for i in A^B if i not in ids)
 return ids
pids=checkpath(P,w[0],w[1]);qids=checkpath(Q,w[1],w[2]);sat=min(len(a) for a in C if not any(a<b for b in C))
j={'matchings':len(C),'nu':nu,'maximum_matchings':[sorted(m) for m in Ms],'lambda':lam,'mu':mu,'ordered_triples_i_ii':len(T),'first_overlap':o1,'triples_i_iii':len(T1),'second_overlap':o2,'triples_i_iv':len(T2),'maximal_M_H_path':P,'maximal_M_H_edges':pids,'maximal_H_Hprime_path':Q,'maximal_H_Hprime_edges':qids,'degree7':sum(7 in e for e in E),'usual_saturation_number':sat,'all_optimal_unions_omissions':sorted({tuple(sorted(set(range(12))-(a|b))) for a,b in pairs})}
(r/'independent-matching.json').write_text(json.dumps(j,indent=2));print(json.dumps(j,indent=2))
