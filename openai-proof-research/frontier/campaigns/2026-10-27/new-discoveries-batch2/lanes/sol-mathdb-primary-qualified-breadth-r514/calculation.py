import json,pathlib
out=[]
for n in range(6,21):
 edges={(0,1)}|{(1,b) for b in range(2,n)}|{(a,b) for a in range(2,n) for b in range(a+1,n)}
 assert all((a,b) in edges or (b,a) in edges or any((a,c) in edges and (c,b) in edges or (b,c) in edges and (c,a) in edges for c in range(n)) for a in range(n) for b in range(a+1,n))
 assert not any(a==0 or b==0 for a,b in edges if a!=1 and b!=1)
 out.append({'n':n,'arcs':len(edges),'weak_diameter_at_most_2':True,'vertex_1_is_cut':True})
P=pathlib.Path(__file__).resolve().parent;(P/'calculation.json').write_text(json.dumps({'purpose':'Rejected literal-only construction for 357943, no extremal f_2(n) assertion; no discovery credit','executed':out},indent=2)+'\n')
