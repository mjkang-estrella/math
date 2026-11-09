import pathlib,itertools,resource,os,json,time
resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3));os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]);D=pathlib.Path(__file__).resolve().parents[1];out=[]
for q in [3,7,11,19]:
 pts=list(itertools.product(range(q),repeat=2));sq={x*x%q for x in range(1,q)};N=q*q;A=[0]*N
 for i,(x,y) in enumerate(pts):
  for j,(u,v) in enumerate(pts):
   if i!=j and ((x-u)**2+(y-v)**2)%q in sq:A[i]|=1<<j
 for complete in [True,False]:
  B=A if complete else [((1<<N)-1)^A[i]^(1<<i) for i in range(N)];calls=0;solutions=0;bad=[];capped=False
  def visit(chosen,cand):
   global calls,solutions,capped
   calls+=1
   if calls>5_000_000:capped=True;return
   if len(chosen)==q:
    solutions+=1;x,y=pts[chosen[1]]
    if any((u*y-v*x)%q for u,v in [pts[j] for j in chosen]):bad.append(chosen)
    return
   while cand.bit_count()>=q-len(chosen) and not capped:
    b=cand&-cand;cand-=b;j=b.bit_length()-1;visit(chosen+[j],cand&B[j])
  visit([0],B[0]);row={'id':379296,'q':q,'complete':complete,'scope':'all target-q cliques through origin in full prime-field quadrance graph, translation-normalized; DFS sorted vertex order','nodes':calls,'full_space_completed':not capped,'q_point_sets_found':solutions,'nonlines':[[pts[j] for j in S] for S in bad]};out.append(row);print(json.dumps(row),flush=True);(D/'outputs/quadrance-cliques.json').write_text(json.dumps(out,indent=2))
