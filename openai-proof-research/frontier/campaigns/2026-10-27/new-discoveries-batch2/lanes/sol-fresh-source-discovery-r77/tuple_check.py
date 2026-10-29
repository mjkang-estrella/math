import pathlib,itertools,json
D=pathlib.Path(__file__).resolve().parent
exec((D/'check.py').read_text().split('results=[];')[0])
n=5;F=fibers(n);R=[[] for _ in range(n)]
for B,parts in F.items():
 for p,q in itertools.product(parts,repeat=2):R[B.bit_count()-1].append((p,q,parts[p]*parts[q]))
out=[]
for k in range(n-1):
 L=R[k];U=R[k+1];edges=[(i,j) for i,p in enumerate(L) for j,q in enumerate(U) if refines(p[0],q[0]) and refines(p[1],q[1])]
 ok,got,need=coupling([p[2] for p in L],[q[2] for q in U],edges)
 assert ok
 out.append({'lower_rank':k,'left_weight':sum(p[2] for p in L),'right_weight':sum(q[2] for q in U),'kernel_tuple_nodes':[len(L),len(U)],'edges':len(edges),'exact_flow':got,'required':need,'normalized_matching':ok})
print(json.dumps({'n':n,'ell':2,'pairs':out},indent=2))
