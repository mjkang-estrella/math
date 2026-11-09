import itertools,json,pathlib,resource,os
resource.setrlimit(resource.RLIMIT_AS,(2*1024**3,2*1024**3));resource.setrlimit(resource.RLIMIT_CPU,(55,55));os.sched_setaffinity(0, sorted(os.sched_getaffinity(0))[:2]);p=pathlib.Path(__file__).resolve().parent
base=[(0,1),(0,2),(2,3),(0,4),(4,5),(1,6),(6,7),(1,8),(8,9)]
left={0,3,5,6,8};right=set(range(10))-left;extra=[tuple(sorted((a,b))) for a in left for b in right if tuple(sorted((a,b))) not in base];extra=sorted(set(extra))
def analyze(edges):
 e=len(edges);ms=[]
 def rec(i,v,m):
  if i==e:ms.append(m);return
  rec(i+1,v,m);a,b=edges[i];vs=(1<<a)|(1<<b)
  if not(v&vs):rec(i+1,v|vs,m|(1<<i))
 rec(0,0,0);size={m:m.bit_count() for m in ms};nu=max(size.values());maxms=[m for m in ms if size[m]==nu]
 best=(-1,-1);pairs=[]
 for h in ms:
  for j in ms:
   if h&j or size[h]<size[j]:continue
   s=(size[h]+size[j],size[h])
   if s>best:best=s;pairs=[(h,j)]
   elif s==best:pairs.append((h,j))
 if best[1]==nu:return None
 opt=(-1,-1);trip=[]
 for m in maxms:
  for h,j in pairs:
   s=((m&(h|j)).bit_count(),(m&h).bit_count())
   if s>opt:opt=s;trip=[(m,h,j)]
   elif s==opt:trip.append((m,h,j))
 for m,h,j in trip:
  deg=[0]*10;adeg=[0]*10
  for i,(a,b) in enumerate(edges):
   deg[a]+=1;deg[b]+=1
   if (m^h)&(1<<i):adeg[a]+=1;adeg[b]+=1
  bad=[a for a in range(10) if adeg[a]==1 and deg[a]>1]
  if bad:return {'edges':edges,'nu':nu,'lambda':best[0],'mu':best[1],'M':m,'H':h,'Hp':j,'bad_vertices':bad,'matchings':len(ms),'lex':opt}
 return {'survives_ratio':True,'triples':len(trip)}
results=[]
for k in range(4):
 count=0;ratio=0
 for xs in itertools.combinations(extra,k):
  count+=1;a=analyze(base+list(xs))
  if a:
   ratio+=1
   if 'bad_vertices' in a:print('FOUND',json.dumps(a),flush=True);(p/'leaf-witness.json').write_text(json.dumps(a,indent=2));raise SystemExit
 results.append({'added_edges':k,'graphs':count,'ratio_lt_one':ratio});print(results[-1],flush=True)
(p/'leaf-diagnostic.json').write_text(json.dumps(results,indent=2))
