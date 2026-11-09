import os,resource,signal,time,json,sys,runpy,datetime
from pathlib import Path
q=Path(__file__).resolve().parent
resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3));os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]);signal.alarm(140)
t=time.monotonic();state="error"
try:
 runpy.run_path(sys.argv[1],run_name="__main__");state="completed"
finally:
 with (q/'jobs.jsonl').open('a') as f:f.write(json.dumps(dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),script=sys.argv[1],state=state,wall_s=time.monotonic()-t,cpu_s=resource.getrusage(resource.RUSAGE_SELF).ru_utime,limits=dict(cpu_s=120,wall_s=140,as_bytes=6*1024**3,cpus=2),synchronous=True))+"\n")
