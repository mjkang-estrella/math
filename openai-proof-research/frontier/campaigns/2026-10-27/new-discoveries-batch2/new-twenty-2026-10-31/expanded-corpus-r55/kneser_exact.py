import itertools,collections,resource,os,json
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]);resource.setrlimit(resource.RLIMIT_CPU,(30,30));resource.setrlimit(resource.RLIMIT_AS,(1024**3,1024**3))
e=list(itertools.combinations(range(1,7),2));hist=collections.Counter()
for f in itertools.combinations(e,11):hist[max(sum(not set(a)&set(b) for b in f) for a in f)]+=1
w=[(x,y) for x in range(1,8) for y in range(x+1,8) if x>=6 or y>=6]
print(json.dumps({'diagnostic_only':True,'compressed_families':sum(hist.values()),'maximum_degree_histogram':dict(hist),'ambient_family':w,'ambient_degrees':{str(a):sum(not set(a)&set(b) for b in w) for a in w},'m':len(w),'smallest_t':6,'dense_check':'21/2 <= 11 <=21'},indent=2))
