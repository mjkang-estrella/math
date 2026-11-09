import os,resource,sys,time,json,pathlib,hashlib,datetime,urllib.request,urllib.error,subprocess
os.sched_setaffinity(0, sorted(os.sched_getaffinity(0))[:2])
resource.setrlimit(resource.RLIMIT_CPU,(120,120))
resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
P=pathlib.Path(__file__).parent
start=time.time()
try:
 exec(compile(pathlib.Path(sys.argv[1]).read_text(),sys.argv[1],'exec'), dict(globals()))
finally:
 with (P/'jobs.jsonl').open('a') as f:f.write(json.dumps({'script':sys.argv[1],'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'elapsed':time.time()-start,'affinity':sorted(os.sched_getaffinity(0)),'maxrss_kib':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,'cpu_cap':120,'AS_bytes':6*1024**3,'wall_external':140,'children_note':'Only synchronous pdftotext where stated; no detached jobs'})+'\n')
