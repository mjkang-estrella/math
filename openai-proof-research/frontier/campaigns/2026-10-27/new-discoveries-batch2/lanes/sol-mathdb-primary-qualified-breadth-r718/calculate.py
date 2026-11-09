import json,pathlib,hashlib
O=pathlib.Path(__file__).parent
t=17;n=5*t-10
D=set(range(t-4,t-2))|set(range(t+1,(3*t-9)//2+1))|{(3*t-5)//2,2*t-4}
S=D|{n-x for x in D}
A=[{(v+d)%n for d in S} for v in range(n)]
triangles=sum(1 for u in range(n) for v in A[u] if u<v for w in A[u]&A[v] if v<w)
nonedges=[v for v in range(1,n) if v not in A[0]]
missing=[v for v in nonedges if not A[0]&A[v]]
witnesses={str(v):min(A[0]&A[v]) for v in nonedges if A[0]&A[v]}
assert triangles==0 and missing==[]
z={'mathdb_id':374345,'executed':True,'t':t,'n':n,'distance_set':sorted(D),'degree':len(S),'triangles':triangles,'nonedge_orbits_from_vertex0':len(nonedges),'edge_addition_common_neighbor_witnesses':witnesses,'missing_common_neighbors':missing,'certificate_scope':'Triangle-free and every added nonedge creates a triangle, using translation invariance; does NOT verify independence number or edge-deletion saturation, or any other t.','full_scope_proof':False,'promotion':False}
(O/'bounded-calculations.json').write_text(json.dumps(z,indent=2)+'\n');print(json.dumps(z))
