import os,resource,time,pathlib,json,hashlib,sys,atexit
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
resource.setrlimit(resource.RLIMIT_CPU,(120,120))
resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
p=pathlib.Path(__file__).resolve().parent
r=p.parent/'expanded-corpus-r315'
start=time.monotonic()
def finish():
 u=resource.getrusage(resource.RUSAGE_SELF)
 with (p/'process-receipts.jsonl').open('a') as f: f.write(json.dumps(dict(argv=sys.argv,affinity=sorted(os.sched_getaffinity(0)),CPU_limit=120,AS_limit=6*1024**3,external_wall_limit=140,wall=time.monotonic()-start,cpu=u.ru_utime+u.ru_stime,peak_RSS_KiB=u.ru_maxrss,limitations='self high water; wrapper pre-affinity and not cgroup RSS enforcement; AS bounds RSS indirectly'))+'\n')
atexit.register(finish)
exec(compile((p/sys.argv[1]).read_text(),str(p/sys.argv[1]),'exec'))
