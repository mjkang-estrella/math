import os,resource,time,pathlib,json,datetime,atexit,sys
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
resource.setrlimit(resource.RLIMIT_CPU,(120,120))
resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
p=pathlib.Path(__file__).parent
a=p.parent/'expanded-corpus-r306'
process_started=time.monotonic()
def receipt():
 r=resource.getrusage(resource.RUSAGE_SELF)
 with (p/'process-receipts.jsonl').open('a') as f:f.write(json.dumps(dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),script=sys.argv[1],affinity=sorted(os.sched_getaffinity(0)),cpu_cap=120,as_cap=6*1024**3,wall_cap=140,elapsed=time.monotonic()-process_started,user_cpu=r.ru_utime,system_cpu=r.ru_stime,maxrss_kib=r.ru_maxrss))+"\n")
atexit.register(receipt)
exec(compile((p/sys.argv[1]).read_text(),str(p/sys.argv[1]),'exec'))
