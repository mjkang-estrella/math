import os,resource,json,itertools,datetime,time,functools,operator,math
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]);resource.setrlimit(resource.RLIMIT_AS,(2*1024**3,2*1024**3));resource.setrlimit(resource.RLIMIT_CPU,(90,90))
r=__import__('pathlib').Path(__file__).parent;s=r.parent/'fresh-corpus-r19';start=time.monotonic()
f=json.loads((s/'bicommutative-search.json').read_text())['best_masks'];F=set(f);U={sum(1<<v for v in t) for t in itertools.combinations(range(15),7)}
assert len(f)==len(F)==1505 and F<=U
pairs=0
for a,b in itertools.combinations(f,2):assert a&b;pairs+=1
cover={int(a):b for a,b in json.loads((s/'bicommutative-cover.json').read_text()).items()};assert set(cover)==U-F
for a,b in cover.items():assert b in F and a&b==0
# independently find witnesses, not just consume author's map
own={a:next(b for b in f if a&b==0) for a in sorted(U-F)}
(r/'independent-domination.json').write_text(json.dumps(own,sort_keys=True))
C=sum(1<<v for v in range(8,15));L=[sum(1<<(v+8) for v in t) for t in [(0,1,4),(0,2,5),(0,3,6),(1,2,6),(2,3,4),(4,5,6),(1,3,5)]]
B=[{a for a in U if a&C==l} for l in L]+[{a for a in U if (a&C).bit_count()==t} for t in [2,1,0]]
A=set.union(*B);assert len(A)==1870 and len(A)==sum(map(len,B));assert A=={a for a in U if (a&C).bit_count()<=2 or a&C in L}
assert all(a&b for a,b in itertools.combinations(A,2));assert all(any(a&b==0 for b in A) for a in U-A)
# DP uses winning take, rather than signed author recurrence.
# W at P = Luca minimizes Windsor take; at N = Windsor maximizes own take.
tables=json.loads((s/'candy-bellman-tables.json').read_text());reports={}
for key,table in tables.items():
 dims=table['dimensions'];states=list(itertools.product(*(range(d) for d in dims)));W={};T={};edges=0
 for g in sorted(states,key=sum):
  x=functools.reduce(operator.xor,g,0);choices=[]
  if not any(g): w=0
  elif x==0:
   for i,a in enumerate(g):
    for v in range(a):
     h=g[:i]+(v,)+g[i+1:];choices.append(W[h]);edges+=1
   w=min(choices)
  else:
   for i,a in enumerate(g):
    v=a^x
    if v<a:
     h=g[:i]+(v,)+g[i+1:];choices.append(a-v+W[h]);edges+=1
   w=max(choices)
  W[g]=w;T[g]=sum(g)-2*w
 assert [T[g] for g in states]==table['values_lexicographic']
 root=tuple(d-1 for d in dims);reports[key]={'states':len(states),'legal_edges':edges,'W':W[root],'V':T[root]}
 (r/('independent-values-'+key.replace(',','-')+'.json')).write_text(json.dumps({'dimensions':dims,'W_lexicographic':[W[g] for g in states]}))
# all integer partitions of 12 into >=2 positive parts, not binary assumption
@functools.lru_cache(None)
def partitions(n,lo=1):
 if n==0:return [()]
 return [(a,)+q for a in range(lo,n+1) for q in partitions(n-a,a)]
splits=[p for p in partitions(12) if len(p)>1 and functools.reduce(operator.xor,p,0)==12];assert splits==[(4,8)]
out={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'resource_caps':{'cpus':list(os.sched_getaffinity(0)),'memory_bytes':2*1024**3,'CPU_seconds':90,'outer_wall_seconds':110},'338640':{'size':len(F),'pairs':pairs,'universe':len(U),'outside':len(own),'source_classes':list(map(len,B)),'source_size':len(A)},'339278':{'tables':reports,'positive_splits':splits},'wall_seconds':time.monotonic()-start}
(r/'independent-results.json').write_text(json.dumps(out,indent=2));print(json.dumps(out,indent=2))
