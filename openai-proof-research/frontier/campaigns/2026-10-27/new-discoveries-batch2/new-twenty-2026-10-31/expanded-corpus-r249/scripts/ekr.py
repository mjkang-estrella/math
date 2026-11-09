import pathlib,json,itertools,functools
L=pathlib.Path(__file__).resolve().parents[1];out=[]
for n in range(9,13):
 ds=[(a,b) for a in range(n) for b in range(a+2,n) if (a,b)!=(0,n-1)];di={e:i for i,e in enumerate(ds)}
 def edge(a,b):return 1<<di[a,b] if (a,b) in di else 0
 @functools.lru_cache(None)
 def tri(a,b):
  if b-a<2:return (0,)
  return tuple(l|r|edge(a,c)|edge(c,b) for c in range(a+1,b) for l in tri(a,c) for r in tri(c,b))
 ts=tri(0,n-1);assert len(set(ts))==len(ts)
 stars=[0]*len(ds)
 for j,t in enumerate(ts):
  while t:
   bit=t&-t;stars[bit.bit_length()-1]|=1<<j;t-=bit
 target=max(s.bit_count() for s in stars);best3=best5=0;arg3=arg5=None;count3=count5=0
 for ids in itertools.combinations(range(len(ds)),3):
  a,b,c=(stars[i] for i in ids);v=((a&b)|(a&c)|(b&c)).bit_count();count3+=1
  if v>best3:best3=v;arg3=ids
 if n<=11:
  for ids in itertools.combinations(range(len(ds)),5):
   a,b,c,d,e=(stars[i] for i in ids)
   v=((a&b&(c|d|e))|(a&c&(d|e))|(a&d&e)|(b&c&(d|e))|(b&d&e)|(c&d&e)).bit_count();count5+=1
   if v>best5:best5=v;arg5=ids
 r=dict(polygon_vertices=n,facets=len(ts),diagonals=len(ds),max_star=target,triple_checks=count3,max_triple_majority=best3,arg3=arg3,five_checks=count5,max_five_majority=best5,arg5=arg5);out.append(r);print(r,flush=True)
(L/'ekr-results.json').write_text(json.dumps(out,indent=2))
