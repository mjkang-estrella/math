import pathlib,itertools,json,os,resource
resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3));os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]);D=pathlib.Path(__file__).resolve().parents[1];out=[]
def norm(S):
 x=min(a for a,b in S);y=min(b for a,b in S);return tuple(sorted((a-x,b-y) for a,b in S))
def area2(S):
 pts=sorted({(a+i,b+j) for a,b in S for i in [0,1] for j in [0,1]})
 def cross(o,a,b):return (a[0]-o[0])*(b[1]-o[1])-(a[1]-o[1])*(b[0]-o[0])
 low=[];high=[]
 for p in pts:
  while len(low)>1 and cross(low[-2],low[-1],p)<=0:low.pop()
  low.append(p)
 for p in reversed(pts):
  while len(high)>1 and cross(high[-2],high[-1],p)<=0:high.pop()
  high.append(p)
 h=low[:-1]+high[:-1];return abs(sum(a[0]*b[1]-a[1]*b[0] for a,b in zip(h,h[1:]+h[:1])))
def arms(S):
 for swap in [False,True]:
  T={(b,a) if swap else (a,b) for a,b in S};width=max(x for x,y in T)+1
  for y in {y for x,y in T}:
   row={(x,y) for x in range(width)}
   if not row<=T:continue
   R=T-row;components=[]
   while R:
    stack=[R.pop()];C=set(stack)
    while stack:
     x,z=stack.pop()
     for p in [(x+1,z),(x-1,z),(x,z+1),(x,z-1)]:
      if p in R:R.remove(p);C.add(p);stack.append(p)
    components.append(C)
   if len(components)<=2 and all(len({x for x,y in C})==1 for C in components):return True
 return False
shapes={((0,0),)}
for n in range(1,10):
 if n>1:shapes={norm(set(S)|{p}) for S in shapes for x,y in S for p in [(x+1,y),(x-1,y),(x,y+1),(x,y-1)] if p not in S}
 best=max(map(area2,shapes));maximizers=[S for S in shapes if area2(S)==best];redundant=[S for S in maximizers if n!=max(x for x,y in S)+max(y for x,y in S)+1];bad=[S for S in maximizers if not arms(S)]
 row={'id':380444,'n':n,'translation_classes':len(shapes),'maximum_twice_area':best,'maximizers':len(maximizers),'positive_total_v':redundant,'row_plus_at_most_two_perpendicular_linear_components_failures':bad,'limitation':'2D only; this tests one precise perpendicular-arm reading, not every interpretation of source iii'};out.append(row);print(json.dumps(row),flush=True);(D/'outputs/polyomino-search.json').write_text(json.dumps(out,indent=2))
