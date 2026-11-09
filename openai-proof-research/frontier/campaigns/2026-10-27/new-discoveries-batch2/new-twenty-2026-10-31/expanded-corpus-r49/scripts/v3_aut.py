# Automorphism group orders (point permutations preserving the line set) and triangle/omega data
# for the counterexample and Pappus; diagnostic identification only.
import itertools, json, resource
resource.setrlimit(resource.RLIMIT_CPU,(200,200))
A=[[0,2,3],[2,4,5],[3,5,8],[2,7,8],[1,3,6],[0,6,8],[0,1,4],[4,6,7],[1,5,7]]
PAP=[[0,1,2],[3,4,5],[6,7,8],[0,4,8],[0,5,7],[1,3,8],[1,5,6],[2,3,7],[2,4,6]]
def aut(lines):
    S={frozenset(l) for l in lines}
    return sum(1 for g in itertools.permutations(range(9)) if {frozenset(g[x] for x in l) for l in S}==S)
print(json.dumps({'counterexample_aut_order':aut(A),'pappus_aut_order':aut(PAP)}))
