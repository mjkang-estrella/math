import os,sys,subprocess,resource,time,json,signal
from pathlib import Path
LANE=Path(__file__).resolve().parent
def limits():
 resource.setrlimit(resource.RLIMIT_CPU,(120,120))
 resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
 os.sched_setaffinity(0, sorted(os.sched_getaffinity(0))[:2])
start=time.time()
p=subprocess.Popen(sys.argv[1:],preexec_fn=limits,start_new_session=True)
timed=False
try: rc=p.wait(timeout=138)
except subprocess.TimeoutExpired:
 timed=True; os.killpg(p.pid,signal.SIGKILL); rc=p.wait()
with (LANE/'jobs.jsonl').open('a') as f: f.write(json.dumps(dict(argv=sys.argv[1:],start=start,elapsed=time.time()-start,returncode=rc,timed_out=timed,reaped=True,cpu_seconds=120,wall_seconds=138,address_space_bytes=6*1024**3,cpu_affinity_max=2))+"\n")
if (LANE/'SEAL').exists():
 import hashlib
 manifest={str(q.relative_to(LANE)):hashlib.sha256(q.read_bytes()).hexdigest() for q in sorted(LANE.rglob('*')) if q.is_file() and q.name!='hash-manifest.json'}
 (LANE/'hash-manifest.json').write_text(json.dumps(manifest,indent=2))
 print('SEALED',len(manifest),'review-lane hashes after child reaped and job log appended')
sys.exit(rc)
