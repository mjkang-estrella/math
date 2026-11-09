import os,resource,sys,time,json,pathlib,runpy,datetime
resource.setrlimit(resource.RLIMIT_CPU,(120,120))
resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
lane=pathlib.Path(__file__).parent
t=time.monotonic()
try:
 exec(compile(sys.stdin.read(),"<bounded-stdin>","exec"), {"__name__":"__main__"}) if sys.argv[1] == "-" else runpy.run_path(sys.argv[1],run_name="__main__")
finally:
 r=resource.getrusage(resource.RUSAGE_SELF)
 with (lane/"process-log.jsonl").open("a") as f:f.write(json.dumps(dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),script=sys.argv[1],affinity=sorted(os.sched_getaffinity(0)),wall=time.monotonic()-t,cpu=r.ru_utime+r.ru_stime,peak_rss_kib=r.ru_maxrss,cpu_limit=120,as_limit=6*1024**3,external_wall_limit=140))+"\n")
