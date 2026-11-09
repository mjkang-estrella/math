import pathlib,resource,os,itertools,json,functools
resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3));os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]);D=pathlib.Path(__file__).resolve().parents[1];s=(D/'scripts/graph_search.py').read_text();exec(s[s.index('def colorable'):s.index('def matchings')]);out=[]
for n in [3,4]:
 pairs=list(itertools.combinations(range(n),2));count=classII=0;bad=[]
 @functools.lru_cache(None)
 def degree(t):return max(sum(m for e,m in zip(pairs,t) if v in e) for v in range(n))
 @functools.lru_cache(None)
 def isClassI(t):
  if not any(t):return True
  es=[e for e,m in zip(pairs,t) for _ in range(m)];return colorable(es,degree(t),n)
 for counts in itertools.product(range(4),repeat=len(pairs)):
  count+=1
  if isClassI(counts):continue
  es=[e for e,m in zip(pairs,counts) for _ in range(m)];delta=degree(counts);chi=next(k for k in range(delta+1,len(es)+1) if colorable(es,k,n));classII+=1
  for p in range(1,delta+1):
   q=chi-p
   if q>delta or p>q or q<1:continue
   found=False
   for a in itertools.product(*(range(m+1) for m in counts)):
    if degree(a)!=p:continue
    b=tuple(m-x for m,x in zip(counts,a))
    if degree(b)==q and isClassI(a) and isClassI(b):found=True;break
   if not found:bad.append({'multiplicities':counts,'delta':delta,'chi':chi,'p':p,'q':q})
 row={'id':381703,'n':n,'space':'all labeled loopless multigraphs, multiplicity0..3 on each pair, including disconnected; all p,q admissible; all sub-multiplicity partitions; exact edge-color backtracking','graphs':count,'classII':classII,'counterexamples':bad};out.append(row);print(json.dumps(row),flush=True);(D/'outputs/multigraph-search.json').write_text(json.dumps(out,indent=2))
