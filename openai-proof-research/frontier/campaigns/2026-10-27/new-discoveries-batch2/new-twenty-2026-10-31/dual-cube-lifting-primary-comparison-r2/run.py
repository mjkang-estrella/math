import os,resource,time,datetime,pathlib,json,atexit,sys
os.sched_setaffinity(0,{min(os.sched_getaffinity(0))})
resource.setrlimit(resource.RLIMIT_CPU,(120,120))
resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
p=pathlib.Path(__file__).parent
t=time.monotonic()
def receipt():
 r=resource.getrusage(resource.RUSAGE_SELF); c=resource.getrusage(resource.RUSAGE_CHILDREN)
 with (p/'process-receipts.jsonl').open('a') as f: f.write(json.dumps(dict(job=sys.argv[1],utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),affinity=sorted(os.sched_getaffinity(0)),cpu_limit=120,AS_limit=6*1024**3,wall_s=time.monotonic()-t,user_s=r.ru_utime,system_s=r.ru_stime,maxrss_KiB=r.ru_maxrss,children_user_s=c.ru_utime,children_system_s=c.ru_stime,children_maxrss_KiB=c.ru_maxrss))+"\n")
atexit.register(receipt)
exec(compile(sys.stdin.read(),sys.argv[1],'exec'))
