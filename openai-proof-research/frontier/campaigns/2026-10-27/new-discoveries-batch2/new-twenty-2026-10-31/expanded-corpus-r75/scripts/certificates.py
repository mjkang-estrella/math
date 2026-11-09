import pathlib,itertools,json,math
from fractions import Fraction as F
D=pathlib.Path(__file__).resolve().parents[1]
# Independent direct face-permutation reconstruction, separate from the exhaustive C enumerator.
P=list(itertools.permutations(range(1,5)));ix={p:i for i,p in enumerate(P)};mask=2987801
nb=[[ix[p[:k][::-1]+p[k:]] for k in (2,3,4)] for p in P]
phi={}
for v in range(24):
 for k in range(3):
  w=nb[v][k];phi[(v,k)]=(w,(k+(2 if mask>>w&1 else 1))%3)
assert len(set(phi.values()))==72
seen=set();faces=[]
for d in phi:
 if d in seen:continue
 q=[];x=d
 while x not in seen:seen.add(x);q.append(x);x=phi[x]
 assert x==d
 faces.append(q)
assert len(faces)==10 and sum(map(len,faces))==72
(D/'outputs/pancake-certificate.json').write_text(json.dumps({'vertices':P,'neighbors_k234':nb,'rotation_mask':mask,'faces':faces,'face_lengths':list(map(len,faces)),'V':24,'E':36,'F':10,'Euler_characteristic':-2,'rotation_surface_genus':2,'formal_topological_bridge':'NOT PROVED IN LEAN'},indent=2))
vals=[F(3,19*24*231)+F(1,23*231),F(1,19*24)-F(1,22)+F(1,23),F(3,19*24*231)+F(1,23*231),F(2,19*24*230)+F(1,22*230)]
assert len(set(vals))==1
(D/'outputs/cayley23-certificate.json').write_text(json.dumps({'n':23,'I':[19,22,23],'hook_dimension':231,'two_row_dimension':230,'normalized_eigenvalues_divided_by_23factorial':[str(x) for x in vals],'eigenvalues':[str(x*math.factorial(23)) for x in vals],'order':['(3,1^20)','(1^23)','(21,1^2)','(2^2,1^19)'],'character_semantic_Lean_bridges':'NOT PROVED'},indent=2))
