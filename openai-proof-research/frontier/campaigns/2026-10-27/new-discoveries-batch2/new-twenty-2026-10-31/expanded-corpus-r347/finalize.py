import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
resource.setrlimit(resource.RLIMIT_CPU,(120,120))
resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
import json,time,hashlib,datetime
from pathlib import Path
L=Path(__file__).resolve().parent
start=time.monotonic()
def sha(b):return hashlib.sha256(b).hexdigest()
def save(n,o):
 p=(L/n).resolve();assert p.is_relative_to(L);p.parent.mkdir(exist_ok=True,parents=True);p.write_text(json.dumps(o,ensure_ascii=False,indent=2)+'\n')
expected='e724eaaf62bab19049af6aa82db66a5eddca94df9a6c189064078ef27a0641b0'
r=(L/'reservation.json').read_bytes();assert sha(r)==expected
d=json.loads((L/'results.json').read_bytes());p=json.loads((L/'provenance.json').read_bytes());assert len(d)==20 and set(map(int,d))==set(json.loads(r)['ids'])
chunks={}
for k,x in p.items():
 b=(L/'literal'/ (k+'.jsonl')).read_bytes(); assert b.endswith(b'\n') and sha(b)==x['raw_sha256'] and json.loads(b)==x['record']==d[k]['parsed_record']
 assert sha(x['record']['statement'].encode())==x['statement_utf8_sha256']
 cp=x['chunk']
 if cp not in chunks:
  assert 'crown' not in cp.lower(); cb=Path(cp).read_bytes();chunks[cp]=(sha(cb),cb.splitlines(keepends=True))
 ch,lines=chunks[cp];assert ch==x['chunk_sha256'] and lines[x['one_based_line']-1]==b
save('reservation-after.json',{'expected':expected,'actual':sha(r),'matches':True,'count':len(d),'literal_bindings_verified':20,'chunk_bindings_verified':len(chunks)})
u=resource.getrusage(resource.RUSAGE_SELF)
save('receipts/finalize-'+str(time.time_ns())+'.json',{'true_exit':0,'affinity':sorted(os.sched_getaffinity(0)),'CPU_limit_s':120,'AS_limit_bytes':6*1024**3,'external_wall_timeout_s':140,'wall':time.monotonic()-start,'self_CPU_s':u.ru_utime+u.ru_stime,'self_peak_RSS_KiB':u.ru_maxrss,'children_launched':0,'jobs_remaining':0,'limits':'self high-water, no concurrent process-group telemetry; receipt records successfully completed provenance checks before manifest verification'})
excluded={'MANIFEST.json','VERIFIED-MANIFEST.json'}
artifacts={}
for f in sorted(L.rglob('*')):
 if f.is_file() and f.name not in excluded:
  assert f.resolve().is_relative_to(L);b=f.read_bytes();artifacts[str(f.relative_to(L))]={'bytes':len(b),'sha256':sha(b)}
save('MANIFEST.json',{'artifacts':artifacts,'excludes':['MANIFEST.json','VERIFIED-MANIFEST.json'],'reason':'Avoid circular self-hashing; verification record binds manifest hash.'})
for n,x in artifacts.items():
 b=(L/n).read_bytes();assert len(b)==x['bytes'] and sha(b)==x['sha256']
save('VERIFIED-MANIFEST.json',{'manifest_sha256':sha((L/'MANIFEST.json').read_bytes()),'verified_artifacts':len(artifacts),'literal_bindings':20,'reservation_before_after_matches':True,'results_count':len(d),'credit':0,'campaign_accepted_new':52,'target':60,'no_execution_dispatched':True,'verification_exit':0,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'jobs_remaining':0})
print(json.dumps({'artifacts_verified':len(artifacts),'literal_bindings':20,'results':len(d),'reservation':sha(r),'credit':0,'campaign':'52/60','jobs_remaining':0}))
