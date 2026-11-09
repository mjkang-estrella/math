import pathlib,json,itertools,resource,os,time
from fractions import Fraction
resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3));os.sched_setaffinity(0,set(sorted(os.sched_getaffinity(0))[:2]));L=pathlib.Path(__file__).resolve().parents[1];st=time.monotonic();out={}
# Entire labelled oriented graphs; each pair absent or oriented in either direction.
a=[]
for n in range(1,6):
 es=list(itertools.combinations(range(n),2));cnt=bad1=bad2=badunion=0
 for states in itertools.product(range(3),repeat=len(es)):
  nb=[set() for _ in range(n)];ind=[0]*n
  for (u,v),s in zip(es,states):
   if s==1:nb[u].add(v);ind[v]+=1
   if s==2:nb[v].add(u);ind[u]+=1
  good1=good2=False
  for v in range(n):
   two=set().union(*(nb[w] for w in nb[v]))-nb[v]-{v};d=len(two);good1|=d>=ind[v];good2|=d+len(nb[v])>=2*ind[v]
  cnt+=1;bad1+=not good1;bad2+=not good2;badunion+=not(good1 or good2)
 a.append({'vertices':n,'all_labelled_orientations':cnt,'fail_first':bad1,'fail_second':bad2,'fail_literal_disjunction':badunion})
out['341267']=a
# Smallest explicit path-square diagnostic. Zero discovery credit: endpoint/formula correction.
n=9;k=2;nb=[{j for j in range(n) if 0<abs(i-j)<=k} for i in range(n)];ds=list(map(len,nb));vals=[sum((Fraction(ds[i]-ds[j],ds[i]+ds[j]) for j in nb[i]),Fraction())/ds[i] for i in range(n)]
out['335078']={'m':1,'k':k,'n':n,'values':[str(x) for x in vals],'distinct':len(set(vals)),'claimed':4,'credit':0,'reason':'smallest-parameter failure; no substantive discovery claim'}
out['elapsed']=time.monotonic()-st
(L/'exact-small-results.json').write_text(json.dumps(out,indent=2));print(json.dumps(out,indent=2))
