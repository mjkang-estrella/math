# Finite certificate: G on {0..8}; (a) every 4-subset has a vertex with no private neighbour (witness);
# (b) classification of all 84 3-subsets; (c) the nine IR-sets and their swap-adjacencies form the path P9.
import itertools,json,hashlib,sys
E=[(0,3),(0,4),(0,6),(0,7),(1,3),(1,5),(1,6),(1,7),(1,8),(2,4),(2,5),(2,7),(2,8),(3,6),(3,8),(4,6),(4,7),(4,8),(5,7),(5,8)]
n=9; nbr={v:set() for v in range(n)}
for a,b in E: nbr[a].add(b); nbr[b].add(a)
cl=lambda v: nbr[v]|{v}
def PN(v,D): return sorted(cl(v)-set().union(*[cl(u) for u in D if u!=v]))
four=[]
for D in itertools.combinations(range(n),4):
    bad=[v for v in D if not PN(v,D)]
    assert bad; four.append({'set':list(D),'vertex_without_private_neighbour':bad[0]})
three=[];IR=[]
for D in itertools.combinations(range(n),3):
    pn={v:PN(v,D) for v in D}
    if all(pn.values()): IR.append(list(D)); three.append({'set':list(D),'irredundant':True,'private_neighbours':{str(v):pn[v] for v in D}})
    else: three.append({'set':list(D),'irredundant':False,'vertex_without_private_neighbour':[v for v in D if not pn[v]][0]})
pairs=[]
for A,B in itertools.combinations(IR,2):
    a=set(A)-set(B); b=set(B)-set(A); adj=len(a)==1 and next(iter(b)) in nbr[next(iter(a))]
    pairs.append({'A':A,'B':B,'adjacent':adj,'swap':[next(iter(a)),next(iter(b))] if len(a)==1 else None})
walk=[[0,1,2],[0,2,7],[0,4,7],[4,6,7],[6,7,8],[1,6,8],[1,3,8],[3,5,8],[3,4,5]]
pathpairs={frozenset((tuple(walk[i]),tuple(walk[i+1]))) for i in range(8)}
assert sorted(map(sorted,IR))==sorted(map(sorted,walk))
for p in pairs: assert p['adjacent']==(frozenset((tuple(p['A']),tuple(p['B']))) in pathpairs)
cert={'graph_vertices':list(range(n)),'edges':E,'num_edges':len(E),'complement_structure':'K_{3,3,3} on parts {0,1,2},{3,4,5},{6,7,8} minus the 7 edges 05,08,14,23,26,37,56',
 'four_subsets':four,'three_subsets':three,'IR_number':3,'IR_sets':IR,'IR_set_pairs':pairs,'path_order':walk}
s=json.dumps(cert,indent=1)
open(sys.argv[1],'w').write(s); print('written',hashlib.sha256(s.encode()).hexdigest(),'4-subsets',len(four),'3-subsets',len(three),'IR sets',len(IR),'adjacent pairs',sum(p['adjacent'] for p in pairs))
