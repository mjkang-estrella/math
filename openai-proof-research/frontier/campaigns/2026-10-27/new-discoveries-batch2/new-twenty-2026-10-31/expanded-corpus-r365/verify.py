import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]);resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
import pathlib,json,hashlib,time,datetime
L=pathlib.Path(__file__).resolve().parent
start=time.monotonic()
def sha(b):return hashlib.sha256(b).hexdigest()
def js(n,o):
 p=(L/n).resolve();assert p.is_relative_to(L) and not p.is_symlink();p.write_text(json.dumps(o,indent=2,ensure_ascii=False)+'\n')
expected='55699bf7706b976f6e46e55da5904608d868bf20412fb305bda4f39e4612bd6a'
assert sha((L/'reservation.json').read_bytes())==expected
r=json.loads((L/'reservation.json').read_text());x=json.loads((L/'literal-records.json').read_text());out=json.loads((L/'results.json').read_text());assert len(out)==20 and set(out)==set(x)==set(map(str,r['ids']))
cache={};bindings=[]
for k,v in x.items():
 p=pathlib.Path(v['chunk']);assert p.name.startswith('mathdb-normalized-chunk-')
 if str(p) not in cache:
  b=p.read_bytes();cache[str(p)]=(sha(b),b.splitlines(keepends=True))
 h,lines=cache[str(p)];raw=(L/v['raw_file']).read_bytes();assert raw==lines[v['onebasedline']-1];assert sha(raw)==v['raw_sha256'];assert h==v['chunk_sha256'];assert raw.endswith(b'\n');assert json.loads(raw)==v['fullparsedJSON'];assert sha(v['fullparsedJSON']['statement'].encode())==v['statement_utf8_sha256'];assert out[k]['fullparsedJSON']==v['fullparsedJSON'];assert out[k]['credit']==0 and not out[k]['candidate']
 bindings.append({'id':int(k),'verified':True,'onebasedline':v['onebasedline'],'raw_sha256':sha(raw),'chunk_sha256':h,'statement_utf8_sha256':v['statement_utf8_sha256']})
js('binding-verification.json',{'bindings':bindings,'exact20':True,'unique_chunks':len(cache),'reservation_after':sha((L/'reservation.json').read_bytes()),'all_raw_newlines_preserved':True})
u=resource.getrusage(resource.RUSAGE_SELF)
js('final-resource-receipt.json',{'UTC':datetime.datetime.now(datetime.timezone.utc).isoformat(),'affinity':sorted(os.sched_getaffinity(0)),'CPU_limit_s':120,'AS_limit_bytes':6*1024**3,'wall_s_at_snapshot':time.monotonic()-start,'self_CPU_s':u.ru_utime+u.ru_stime,'self_highwater_RSS_KiB':u.ru_maxrss,'current_RSS':[s for s in pathlib.Path('/proc/self/status').read_text().splitlines() if s.startswith('VmRSS:')],'no_children_spawned':True,'other_jobs':'all earlier tool processes exited; pdftotext children reaped and fetch/guard threads joined','true_exit':'see external tool receipt; this snapshot precedes manifest verification','not_group_telemetry':True})
files={}
for p in sorted(L.rglob('*')):
 assert not p.is_symlink()
 if p.is_file() and p.name not in ['actual-hash-manifest.json','verification.json']:
  rel=str(p.relative_to(L));assert not any(t in rel.lower() for t in ['crown','transitive-bunkbed']);b=p.read_bytes();files[rel]={'sha256':sha(b),'bytes':len(b)}
js('actual-hash-manifest.json',{'kind':'actual bytes of lane artifacts; no inferred/dummy hashes','files':files,'excluded_self_and_verification':True})
for n,v in files.items():
 b=(L/n).read_bytes();assert sha(b)==v['sha256'] and len(b)==v['bytes']
assert sha((L/'reservation.json').read_bytes())==expected
js('verification.json',{'manifest_sha256':sha((L/'actual-hash-manifest.json').read_bytes()),'verified_actual_artifact_count':len(files),'exact20_bindings_verified':True,'reservation_sha256_after':expected,'credit':0,'accepted_count_unchanged':'52/60','no_formal_claim':True,'all_assertions_passed':True})
print(json.dumps({'verified_artifacts':len(files),'exact20':True,'reservation_after':expected,'self_highwater_RSS_KiB':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,'wall_s':time.monotonic()-start,'successful_return':True}))
