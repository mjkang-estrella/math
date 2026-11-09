import pathlib,json,itertools,functools,sys
@functools.lru_cache(None)
def triang(a,b):
 if b-a<2:return ((),)
 return tuple(tuple(sorted(l+r+((a,k,b),))) for k in range(a+1,b) for l in triang(a,k) for r in triang(k,b))
N=int(sys.argv[1]);ts=triang(0,N-1);tid={t:i for i,t in enumerate(ts)};moves=[]
for t in ts:
 mv=[]
 for i,x in enumerate(t):
  for j in range(i):
   y=t[j];e=set(x)&set(y)
   if len(e)!=2:continue
   a,b=sorted(e);u=next(v for v in x if v not in e);v=next(w for w in y if w not in e)
   nt=tuple(sorted([z for k,z in enumerate(t) if k not in (i,j)]+[tuple(sorted((u,v,a))),tuple(sorted((u,v,b)))]))
   inds=[nt.index(z) for z in t if z not in (x,y)];old=[k for k,z in enumerate(t) if z not in (x,y)]
   new=[k for k,z in enumerate(nt) if z not in t]
   mv.append((i,j,tid[nt],list(zip(old,inds)),new))
 moves.append(mv)
W=1<<(N-2);seen=bytearray(len(ts)*W);comps=0;largest=0;conflict=None
for start in range(len(seen)):
 if seen[start]:continue
 comps+=1;seen[start]=1;q=[start];colors={}
 for state in q:
  ti,mask=divmod(state,W)
  for k,tr in enumerate(ts[ti]):
   c=mask>>k&1
   if tr in colors and colors[tr]!=c:conflict=[start,state,tr];break
   colors[tr]=c
  if conflict:break
  for i,j,ni,mp,new in moves[ti]:
   c=mask>>i&1
   if c!=(mask>>j&1):continue
   nm=sum(((mask>>a)&1)<<b for a,b in mp)+sum((1-c)<<b for b in new);ns=ni*W+nm
   if not seen[ns]:seen[ns]=1;q.append(ns)
 largest=max(largest,len(q))
 if conflict:break
print(json.dumps({'polygon_vertices':N,'triangulations':len(ts),'colored_states':len(seen),'visited':sum(seen),'components':comps,'largest_component':largest,'conflict':conflict}))
