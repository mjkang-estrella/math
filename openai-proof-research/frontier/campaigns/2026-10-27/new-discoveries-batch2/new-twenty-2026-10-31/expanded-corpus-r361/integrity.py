import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]); resource.setrlimit(resource.RLIMIT_CPU,(120,120)); resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
import pathlib,sys,json,hashlib,time,datetime
L=pathlib.Path(__file__).resolve().parent; start=time.monotonic(); run=datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S%f')
def sha(b):return hashlib.sha256(b).hexdigest()
def js(rel,obj):
 p=(L/rel).resolve(); assert p.is_relative_to(L); p.write_text(json.dumps(obj,indent=2)+'\n')
def files(d):
 for p in sorted(d.iterdir()):
  assert not p.is_symlink()
  if any(t in p.name.lower() for t in ['crown','upper-support','reverse-kernel','coordinate-kernel']): continue
  assert p.resolve().is_relative_to(L)
  if p.is_dir():yield from files(p)
  elif p.is_file():yield p
exclude=['manifest.json','manifest-verification.json']
code=0
try:
 R=json.loads((L/'reservation.json').read_text()); results=json.loads((L/'results.json').read_text()); P=json.loads((L/'provenance.json').read_text())
 rh=sha((L/'reservation.json').read_bytes()); assert rh=='df096d6a132ef9b8979807aa56e30b49f77b2dadace0b042508ba8acdd29dcbc'
 assert len(results)==20 and set(results)==set(map(str,R['ids']))==set(P)
 for sid,v in results.items():
  a=P[sid]; raw=(L/f'literals/{sid}.jsonl').read_bytes(); assert sha(raw)==a['raw_sha256'] and raw.endswith(b'\n'); assert json.loads(raw)==v['full_parsed_record']==a['record']; assert sha(v['literal_statement'].encode())==a['statement_sha256']; assert v['accepted_credit']==0 and v['campaign']==dict(accepted_new=52,target_new=60,delta=0)
 if sys.argv[1]=='build':
  u=resource.getrusage(resource.RUSAGE_SELF); js('receipts/process-manifest-build-'+run+'.json',dict(exit_code=0,wall_s=time.monotonic()-start,affinity=sorted(os.sched_getaffinity(0)),CPU_limit=120,AS_limit=6*1024**3,self_peak_RSS_KiB=u.ru_maxrss,self_CPU_s=u.ru_utime+u.ru_stime,external_wall_timeout=140,limitation='Self high-water only'))
  entries={str(p.relative_to(L)):dict(bytes=p.stat().st_size,sha256=sha(p.read_bytes())) for p in files(L) if str(p.relative_to(L)) not in exclude}
  js('manifest.json',dict(created_utc=run,algorithm='SHA256',scope='All regular files inside this lane only; no symlinks or protected names opened.',excluded=exclude,artifacts=entries)); print('Manifest artifacts',len(entries))
 elif sys.argv[1]=='check':
  mb=(L/'manifest.json').read_bytes(); m=json.loads(mb); entries=m['artifacts']; actual={str(p.relative_to(L)) for p in files(L) if str(p.relative_to(L)) not in exclude}; assert actual==set(entries)
  for rel,ent in entries.items():
   p=(L/rel).resolve(); assert p.is_relative_to(L); b=p.read_bytes(); assert len(b)==ent['bytes'] and sha(b)==ent['sha256'],rel
  u=resource.getrusage(resource.RUSAGE_SELF)
  report=dict(utc=run,verified=True,artifact_count=len(entries),manifest_sha256=sha(mb),reservation_sha256=rh,exact_result_count=20,literal_bindings_checked=20,original_chunk_verification='literal-binding-verification.json generated in a separate bounded process',accepted_credit=0,campaign_accepted_new=52,campaign_target_new=60,exit_code=0,wall_s=time.monotonic()-start,affinity=sorted(os.sched_getaffinity(0)),CPU_limit=120,AS_limit=6*1024**3,self_peak_RSS_KiB=u.ru_maxrss,self_CPU_s=u.ru_utime+u.ru_stime,external_wall_timeout=140,limitation='Self high-water only, not concurrent group telemetry',jobs='This synchronous verifier created no children; all earlier synchronous tools and joined fetch executors completed.')
  js('manifest-verification.json',report); print(json.dumps(report))
except:
 code=1; raise
