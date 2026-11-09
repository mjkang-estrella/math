import os,resource,signal,json,itertools,datetime,time
from pathlib import Path
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]);resource.setrlimit(resource.RLIMIT_AS,(2*1024**3,2*1024**3));resource.setrlimit(resource.RLIMIT_CPU,(20,20));signal.alarm(30)
p=Path(__file__).resolve().parent;s=p.parent/'fresh-corpus-r19';t=time.monotonic()
f=json.loads((s/'bicommutative-search.json').read_text())['best_masks'];F=set(f);U={x for x in range(1<<15) if x.bit_count()==7}
assert len(f)==len(F)==1505 and F<=U
assert all(a&b for a,b in itertools.combinations(f,2))
c={int(a):b for a,b in json.loads((s/'bicommutative-cover.json').read_text()).items()};assert set(c)==U-F
assert all(b in F and not a&b for a,b in c.items())
core=sum(1<<v for v in range(8,15));lines=[sum(1<<v for v in t) for t in [(8,9,12),(8,10,13),(8,11,14),(9,10,14),(10,11,12),(12,13,14),(9,11,13)]]
classes=[{a for a in U if a&core==l} for l in lines]+[{a for a in U if (a&core).bit_count()==j} for j in [2,1,0]];A=set.union(*classes)
assert len(A)==sum(map(len,classes))==1870
out={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'ordinary':'PASS','size':len(F),'unordered_pairs':len(f)*(len(f)-1)//2,'universe':len(U),'outside_witnesses':len(c),'source_class_sizes':list(map(len,classes)),'source_size':len(A),'seconds':time.monotonic()-t,'caps':{'affinity':list(os.sched_getaffinity(0)),'AS_bytes':2*1024**3,'cpu_seconds':20,'wall_seconds':30}}
(p/'finite-recheck.json').write_text(json.dumps(out,indent=2));print(json.dumps(out))
