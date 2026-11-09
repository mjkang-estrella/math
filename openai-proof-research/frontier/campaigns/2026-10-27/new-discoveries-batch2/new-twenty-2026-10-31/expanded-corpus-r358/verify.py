import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]);resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
import pathlib,json,hashlib,time,datetime
L=pathlib.Path(__file__).resolve().parent;t=time.monotonic()
def sha(b):return hashlib.sha256(b).hexdigest()
def write(n,x):
 p=(L/n).resolve();assert p.is_relative_to(L);p.write_text(json.dumps(x,indent=2)+'\n')
expected='9c46d764c5c8ae961a484bbbe33db4a49cf1aa9281c091a38592a77d25ce448e'
assert sha((L/'reservation.json').read_bytes())==expected
r=json.loads((L/'reservation.json').read_bytes());p=json.loads((L/'provenance.json').read_bytes());out=json.loads((L/'results.json').read_bytes())
assert len(r['ids'])==len(out)==len(p)==20
assert set(map(str,r['ids']))==set(out)==set(p)
chunks={};checks=[]
for k,x in p.items():
 path=pathlib.Path(x['chunk']);assert 'pi-mathdb-full-corpus-inventory-r301/corpus/mathdb-normalized-chunk-' in str(path)
 if str(path) not in chunks:
  b=path.read_bytes();chunks[str(path)]=(sha(b),b.splitlines(keepends=True))
 h,lines=chunks[str(path)];raw=lines[x['line']-1]
 assert h==x['chunk_sha256'] and raw.endswith(b'\n') and raw==(L/'literal'/f'{k}.jsonl').read_bytes()
 assert sha(raw)==x['raw_sha256'];rec=json.loads(raw);assert rec==x['record']==json.loads((L/'literal'/f'{k}.json').read_bytes())
 assert sha(rec[x['statement_field']].encode())==x['statement_sha256'] and int(k)==rec['mathdb_id'] and out[k]['credit']==0
 checks.append({'id':int(k),'raw_newline':True,'parsed_record_equal':True,'chunk_hash_equal':True,'raw_hash_equal':True,'statement_hash_equal':True,'one_based_line':x['line']})
write('literal-verification.json',{'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'checks':checks,'count':20,'reservation_sha256':expected})
write('process-verify.json',{'pid':os.getpid(),'exit':0,'elapsed_before_manifest':time.monotonic()-t,'affinity':sorted(os.sched_getaffinity(0)),'cpu_limit':resource.getrlimit(resource.RLIMIT_CPU),'as_limit':resource.getrlimit(resource.RLIMIT_AS),'self_maxrss_kib':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,'scope':'self only; not group peak','spawned_children':0})
# Only this lane is traversed; historical/protected paths are never traversed.
excluded={'artifact-manifest.json','manifest-verification.json'}
manifest={}
for q in sorted(L.rglob('*')):
 if q.is_file() and q.name not in excluded:
  assert q.resolve().is_relative_to(L) and not q.is_symlink();b=q.read_bytes();manifest[str(q.relative_to(L))]={'bytes':len(b),'sha256':sha(b)}
write('artifact-manifest.json',manifest)
for n,v in manifest.items():
 b=(L/n).read_bytes();assert len(b)==v['bytes'] and sha(b)==v['sha256']
write('manifest-verification.json',{'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'artifacts_verified':len(manifest),'manifest_sha256':sha((L/'artifact-manifest.json').read_bytes()),'reservation_sha256':sha((L/'reservation.json').read_bytes()),'literal_bindings_verified':20,'results_key_count':20,'credit':0,'campaign_count':'52/60 unchanged; no recount','exclusions':sorted(excluded),'self_exclusion_reason':'Manifest and verification receipt cannot hash themselves; receipt binds manifest.','exit':0,'live_jobs_owned':0})
print(json.dumps({'artifacts_verified':len(manifest),'literal_bindings_verified':20,'reservation':expected,'results':20,'credit':0,'exit':0}))
