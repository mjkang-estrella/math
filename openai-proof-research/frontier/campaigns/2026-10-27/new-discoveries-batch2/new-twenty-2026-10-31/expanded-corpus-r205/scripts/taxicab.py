import pathlib,sys,itertools,json
D=pathlib.Path(__file__).resolve().parents[1];sys.path.insert(0,str(D/'scripts'));import graphlib_local as nx
out=[]
for sphere in [False,True]:
 pts=[p for p in itertools.product(range(-1,2),repeat=3) if not sphere or sum(map(abs,p))==2];n=len(pts)
 for k in [1,2]:
  best=0;noaxis=0;cnt=0
  for dist in itertools.combinations(range(1,7),k):
   G=nx.Graph();G.add_nodes_from(range(n))
   for i,j in itertools.combinations(range(n),2):
    if sum(abs(a-b) for a,b in zip(pts[i],pts[j])) in dist:G.add_edge(i,j)
   for C in nx.find_cliques(G):
    if len(C)<best:continue
    diameter=max((sum(abs(a-b) for a,b in zip(pts[i],pts[j])) for i,j in itertools.combinations(C,2)),default=0)
    axis=any(sum(a!=b for a,b in zip(pts[i],pts[j]))==1 and sum(abs(a-b) for a,b in zip(pts[i],pts[j]))==diameter for i,j in itertools.combinations(C,2))
    if len(C)>best:best=len(C);cnt=0;noaxis=0
    cnt+=1;noaxis+=not axis
  r={'grid':'{-1,0,1}^3','sphere_radius_2':sphere,'points':n,'k':k,'bounded_max':best,'maximum_cliques_across_distance_choices':cnt,'non_axis_maxima':noaxis,'warning':'Only bounded grid optimum; not optimum among all real sets.'};out.append(r);print(json.dumps(r),flush=True)
(D/'outputs/taxicab.json').write_text(json.dumps(out,indent=2))
