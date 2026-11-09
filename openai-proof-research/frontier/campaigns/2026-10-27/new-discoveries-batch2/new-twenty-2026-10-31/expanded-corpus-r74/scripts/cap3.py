import pathlib,json,itertools,os,resource
resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3));os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]);D=pathlib.Path(__file__).resolve().parents[1];pts=list(itertools.product(range(3),repeat=3));index={p:i for i,p in enumerate(pts)};third=[[index[tuple((-a-b)%3 for a,b in zip(x,y))] for y in pts] for x in pts];counts=[0]*28;best=[]
def rec(selected,candidates):
 global best
 counts[len(selected)]+=1
 if len(selected)>len(best):best=selected.copy()
 while candidates:
  b=candidates&-candidates;candidates-=b;i=b.bit_length()-1;forbid=0
  for j in selected:forbid|=1<<third[i][j]
  rec(selected+[i],candidates&~forbid)
rec([0],((1<<27)-1)^1)
out={'id':381218,'space':'all subsets of F3^3 containing origin and no three distinct points with zero sum; every nonempty cap translates to one in this space','counts_by_size':counts,'maximum_support':len(best),'witness':[pts[i] for i in best],'max_zero_sum_free_sequence_length':2*len(best),'reason':'each multiplicity at most two; repeats of a point twice and another point cannot sum to zero in characteristic3'};print(json.dumps(out,indent=2));(D/'outputs/cap3-search.json').write_text(json.dumps(out,indent=2))
