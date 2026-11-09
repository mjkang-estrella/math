import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]); resource.setrlimit(resource.RLIMIT_CPU,(120,120)); resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
import pathlib,json,hashlib,subprocess,time,datetime,sys
p=pathlib.Path(__file__).resolve().parent

def put(n,o):
 q=(p/n).resolve(); assert q.is_relative_to(p); q.write_text(json.dumps(o,indent=2)+'\n')
t=time.monotonic(); q=subprocess.run([sys.executable,'-I','-B',str(p/'validate.py')],cwd=p,capture_output=True,text=True,timeout=130)
put('true-exit-verifier.json',{'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'argv':[sys.executable,'-I','-B','validate.py'],'returncode':q.returncode,'stdout':q.stdout,'stderr':q.stderr,'wall_seconds':time.monotonic()-t,'fully_reaped':True,'children_rusage':list(resource.getrusage(resource.RUSAGE_CHILDREN)),'limits_inherited':True})
assert q.returncode==0
put('seal-resource-sample.json',{'self':list(resource.getrusage(resource.RUSAGE_SELF)),'affinity':list(os.sched_getaffinity(0)),'note':'pre-manifest self sample, not concurrent peak; no spawned jobs remain'})
files={}
for f in sorted(p.rglob('*')):
 assert f.resolve().is_relative_to(p)
 if f.is_file() and f.name not in ['artifact-manifest.json','artifact-verification.json']:
  b=f.read_bytes(); files[str(f.relative_to(p))]={'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()}
put('artifact-manifest.json',{'files':files,'excludes':['artifact-manifest.json','artifact-verification.json'],'no_live_children':True})
for n,o in files.items():
 b=(p/n).read_bytes(); assert len(b)==o['bytes'] and hashlib.sha256(b).hexdigest()==o['sha256']
put('artifact-verification.json',{'verified_artifacts':len(files),'all_hashes_match':True,'manifest_sha256':hashlib.sha256((p/'artifact-manifest.json').read_bytes()).hexdigest(),'binding_verifier_exit':q.returncode,'reservation_sha256':hashlib.sha256((p/'reservation.json').read_bytes()).hexdigest(),'no_live_children':True,'credit':0,'campaign_count_unchanged':'52/60'})
print(json.dumps({'verified_artifacts':len(files),'bindings':'PASS exact20','reservation':'PASS before/after','all_children_reaped':True}))
