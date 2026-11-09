import os,resource,pathlib,re,json,itertools,time,collections
os.environ['MALLOC_ARENA_MAX']='2'
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
import networkx as nx
lane=pathlib.Path(__file__).resolve().parent; f=lane.parent/'nut-formal-r7q/formal';start=time.monotonic()
# Independent vertex-extension enumeration with exact VF2 isomorphism, no candidate canonicalizer.
level=[nx.empty_graph(1)];counts=[1]
for n in range(2,9):
 buckets=collections.defaultdict(list)
 for g in level:
  avail=[i for i in g if g.degree(i)<3]
  for k in range(1,min(3,len(avail))+1):
   for ns in itertools.combinations(avail,k):
    h=g.copy();h.add_node(n-1);h.add_edges_from((n-1,i) for i in ns)
    key=nx.weisfeiler_lehman_graph_hash(h)
    if not any(nx.is_isomorphic(h,z) for z in buckets[key]):buckets[key].append(h)
 level=[g for z in buckets.values() for g in z];counts.append(len(level))
 assert counts[-1]==[1,1,2,6,10,29,64,194][n-1]
txt=(f/'GraphClosure7_000.lean').read_text();codes=list(map(int,re.search(r'def targets : List Nat := \[(.*?)\]',txt,re.S)[1].split(',')))
cat=[]
for c in codes:
 g=nx.empty_graph(8);g.add_edges_from((i,j) for i in range(8) for j in range(i+1,8) if c>>(8*i+j)&1);cat.append(g)
assert len(cat)==194 and all(nx.is_connected(g) and max(dict(g.degree()).values())<=3 for g in cat)
assert all(any(nx.is_isomorphic(g,h) for h in cat if sorted(dict(g.degree()).values())==sorted(dict(h.degree()).values())) for g in level)
# Bareiss: integer elimination independent of sparse recursive Laplace Lean evaluator.
def det(a):
 a=[r[:] for r in a];n=len(a);prev=1;sgn=1
 for k in range(n-1):
  if a[k][k]==0:
   q=next((i for i in range(k+1,n) if a[i][k]),None)
   if q is None:return 0
   a[k],a[q]=a[q],a[k];sgn=-sgn
  pivot=a[k][k]
  for i in range(k+1,n):
   for j in range(k+1,n):
    val=a[i][j]*pivot-a[i][k]*a[k][j];assert val%prev==0;a[i][j]=val//prev
  for i in range(k+1,n):a[i][k]=0
  prev=pivot
 return sgn*a[-1][-1]
certs=[];kinds=collections.Counter();sample=[]
for file in sorted(f.glob('NewCertificates*.lean')):
 text=file.read_text()
 for m in re.finditer(r'def C(\d+) : .*? := !!\[(.*?)\]\ntheorem certificate\1 : C\1\.(det|adjugate (\d+) (\d+)) = (.*?) := by',text,re.S):
  idx,raw,kind,i,j,rhs=m.groups();a=[[int(z.strip()) for z in row.split(',')] for row in raw.split(';')];assert len(a)==8 and all(len(r)==8 for r in a)
  assert a==list(map(list,zip(*a))) and all(sum(map(abs,r))==3 for r in a)
  semis={a[t][t] for t in range(8) if abs(a[t][t])==1};assert len(semis)<=1
  if kind=='det':b=a;expected=int(re.search(r'-?\d+',rhs)[0]);kinds['det']+=1
  else:
   assert i==j;ii=int(i);b=[[v for y,v in enumerate(r) if y!=ii] for x,r in enumerate(a) if x!=ii];expected=0;kinds['cofactor']+=1
  actual=det(b);assert actual==expected,(file.name,idx,actual,expected)
  certs.append((file.name,int(idx),kind,actual))
assert len(certs)==9172
# Save spread sample explicitly, while checking all claims above.
sample=[certs[i] for i in range(0,len(certs),227)]+[next(x for x in certs if x[2]!='det')]
result={'counts':counts,'catalogue_exact_isomorphism_coverage':True,'certificates_checked':len(certs),'kinds':dict(kinds),'sample':sample,'wall_seconds':time.monotonic()-start,'peak_rss_kib':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,'algorithm':'vertex augmentation + WL buckets + exact VF2; Bareiss exact determinant'}
(lane/'independent-check.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
