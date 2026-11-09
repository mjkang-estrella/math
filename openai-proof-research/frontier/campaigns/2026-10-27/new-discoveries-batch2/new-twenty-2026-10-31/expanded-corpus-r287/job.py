import os,sys,resource,subprocess,time,json,pathlib
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
resource.setrlimit(resource.RLIMIT_CPU,(120,120))
resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
p=pathlib.Path(__file__).parent
start=time.time()
r=subprocess.run(sys.argv[1:],timeout=135)
with (p/'jobs.jsonl').open('a') as f: f.write(json.dumps({'argv':sys.argv[1:],'utc_start':start,'wall_seconds':time.time()-start,'exit':r.returncode,'cpus':sorted(os.sched_getaffinity(0)),'cpu_limit_seconds':120,'as_limit_bytes':6*1024**3,'child_reaped':True})+'\n')
if (p/'FINALIZE').exists():
 import hashlib
 manifest={str(f.relative_to(p)):hashlib.sha256(f.read_bytes()).hexdigest() for f in sorted(p.rglob('*')) if f.is_file() and f.name not in ['hash-manifest.json','FINALIZE']}
 (p/'hash-manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
sys.exit(r.returncode)
