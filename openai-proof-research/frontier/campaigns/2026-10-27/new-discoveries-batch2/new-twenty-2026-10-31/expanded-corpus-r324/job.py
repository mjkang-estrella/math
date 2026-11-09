import os,resource,time,json,pathlib,hashlib,sys,atexit
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
resource.setrlimit(resource.RLIMIT_CPU,(120,120))
resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
P=pathlib.Path(__file__).resolve().parent
start=time.monotonic()
def savejob():
 u=resource.getrusage(resource.RUSAGE_SELF)
 with (P/'resources.jsonl').open('a') as f:f.write(json.dumps(dict(argv=sys.argv,affinity=sorted(os.sched_getaffinity(0)),cpu_limit=120,wall_limit=140,as_limit=6*1024**3,wall=time.monotonic()-start,cpu=u.ru_utime+u.ru_stime,self_peak_RSS_KiB=u.ru_maxrss,group_sampled_RSS='unavailable',service_telemetry='unavailable'))+'\n')
atexit.register(savejob)
exec(compile((P/sys.argv[1]).read_text(),str(P/sys.argv[1]),'exec'))
