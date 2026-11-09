import resource,os,time,itertools,json,pathlib
resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3));os.sched_setaffinity(0,set(sorted(os.sched_getaffinity(0))[:2]));st=time.monotonic();n=6;es=list(itertools.combinations(range(n),2));bad=[0,0,0];count=0
for state in itertools.product(range(3),repeat=15):
 nb=[0]*6;ind=[0]*6
 for (u,v),s in zip(es,state):
  if s==1:nb[u]|=1<<v;ind[v]+=1
  elif s==2:nb[v]|=1<<u;ind[u]+=1
 good1=good2=False
 for v in range(6):
  ns=nb[v];two=0
  while ns:
   b=ns&-ns;ns-=b;two|=nb[b.bit_length()-1]
  d=(two&~(nb[v]|(1<<v))).bit_count();good1|=d>=ind[v];good2|=d+nb[v].bit_count()>=2*ind[v]
  if good1 and good2:break
 count+=1;bad[0]+=not good1;bad[1]+=not good2;bad[2]+=not(good1 or good2)
 if count%100000==0:
  print(count,bad,time.monotonic()-st,flush=True)
  if time.monotonic()-st>100:break
L=pathlib.Path(__file__).resolve().parents[1];r={'n':6,'tested_labelled_orientations':count,'total':3**15,'complete':count==3**15,'fail_first':bad[0],'fail_second':bad[1],'fail_literal_disjunction':bad[2],'elapsed':time.monotonic()-st,'ordering':'lexicographic ternary states of lexicographically ordered unordered pairs'};(L/'sullivan6-results.json').write_text(json.dumps(r,indent=2));print(json.dumps(r))
