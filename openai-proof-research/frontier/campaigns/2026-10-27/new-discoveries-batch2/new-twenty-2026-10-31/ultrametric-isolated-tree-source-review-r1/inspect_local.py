import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]);resource.setrlimit(resource.RLIMIT_CPU,(10,10));resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,512*1024**2))
import pathlib,sys,re,json,time,hashlib
L=pathlib.Path(__file__).resolve().parent;p=(L/sys.argv[1]).resolve();assert p.is_relative_to(L);s=p.read_text()
for q in sys.argv[2:]:
 for m in list(re.finditer(re.escape(q),s))[:20]:print('\nMATCH',q,m.start(),s[max(0,m.start()-100):m.start()+4800])
r={'argv':sys.argv,'exit':0,'self_maxrss_kib':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'cpu':10,'as':512*1024**2,'affinity':sorted(os.sched_getaffinity(0)),'scope':'self only'}
t=(L/'receipts'/('inspect-'+str(time.time_ns())+'.json')).resolve();assert t.is_relative_to(L);t.write_text(json.dumps(r,indent=2))
