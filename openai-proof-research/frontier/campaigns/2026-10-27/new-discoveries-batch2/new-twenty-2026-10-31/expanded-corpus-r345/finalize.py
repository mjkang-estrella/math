import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
resource.setrlimit(resource.RLIMIT_CPU,(120,120))
resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
import pathlib,json,hashlib,time,sys,traceback,uuid
P=pathlib.Path(__file__).resolve().parent
start=time.monotonic(); expected='52c9800a5758f17c372a83a0ee6755d7da77a9998453da9e5b084a4ec3354886'
def digest(b):return hashlib.sha256(b).hexdigest()
def put(n,x):
 q=(P/n).resolve();assert q.is_relative_to(P);q.write_text(json.dumps(x,indent=2,ensure_ascii=False)+'\n')
ec=0
try:
 r=json.loads((P/'reservation.json').read_bytes());assert digest((P/'reservation.json').read_bytes())==expected
 assert len(r['ids'])==20 and len(set(r['ids']))==20
 results=json.loads((P/'results.json').read_bytes());assert set(results)==set(map(str,r['ids']))
 prov=json.loads((P/'literal-provenance.json').read_bytes());chunk_cache={}
 for id in r['ids']:
  x=prov[str(id)];q=pathlib.Path(x['chunk']).resolve()
  assert q.parent.name=='corpus' and q.name.startswith('mathdb-normalized-chunk-')
  if str(q) not in chunk_cache:
   b=q.read_bytes();chunk_cache[str(q)]=(digest(b),b.splitlines(keepends=True))
  h,lines=chunk_cache[str(q)];assert h==x['chunk_sha256']
  raw=lines[x['line_one_based']-1];assert raw.endswith(b'\n')
  assert raw==(P/f'literal-{id}.jsonl').read_bytes()
  assert digest(raw)==x['raw_sha256']
  rec=json.loads(raw);assert rec==json.loads((P/f'parsed-{id}.json').read_bytes())==x['record']
  assert rec['mathdb_id']==id and digest(rec['statement'].encode())==x['statement_utf8_sha256']
  assert results[str(id)]['literal_statement']==rec['statement'] and results[str(id)]['credit']==0
 put('reservation-after.json',{'sha256':expected,'matches_before':json.loads((P/'reservation-before.json').read_bytes())['sha256']==expected,'exact_count':20,'ids_unchanged':True})
 put('literal-verification.json',{'verified_bindings':20,'chunk_count':len(chunk_cache),'checks':['original chunk hash','one-based line','exact raw bytes','final newline','raw SHA256','full parsed record','statement UTF-8 SHA256','result ID set and literal statement'],'all_passed':True})
except BaseException:
 ec=1;traceback.print_exc()
# All previous work has completed synchronously and no subprocess was launched here.
put('receipts/finalizer-'+str(uuid.uuid4())+'.json',{'exit':ec,'CPU_limit_s':120,'AS_limit_bytes':6*1024**3,'wall_limit_s':140,'affinity':sorted(os.sched_getaffinity(0)),'elapsed_before_manifest':time.monotonic()-start,'self_usage_before_manifest':list(resource.getrusage(resource.RUSAGE_SELF)),'no_children':True,'limits':'Self high-water before final manifest pass, not group/cgroup peak. Outer shell exit independently observed.'})
if ec:sys.exit(ec)
exclude={'artifact-manifest.json','manifest-verification.json'}
manifest={}
for q in sorted(P.rglob('*')):
 if not q.is_file():continue
 assert q.resolve().is_relative_to(P)
 n=str(q.relative_to(P))
 if n in exclude:continue
 b=q.read_bytes();manifest[n]={'sha256':digest(b),'bytes':len(b)}
put('artifact-manifest.json',{'artifacts':manifest,'self_reference_exclusions':sorted(exclude)})
# Verify serialized manifest, never merely the in-memory dictionary.
saved=json.loads((P/'artifact-manifest.json').read_bytes())
for n,x in saved['artifacts'].items():
 b=(P/n).read_bytes();assert digest(b)==x['sha256'] and len(b)==x['bytes']
put('manifest-verification.json',{'artifact_count':len(saved['artifacts']),'all_hashes_and_lengths_verified':True,'manifest_sha256':digest((P/'artifact-manifest.json').read_bytes()),'literal_bindings_verified':20,'reservation_sha256':expected,'campaign_count':'52/60','credit':0,'candidate_count':0,'execution_dispatch':'NONE','self_reference_exclusions':sorted(exclude),'all_own_jobs_synchronously_reaped':True,'finalizer_elapsed_s':time.monotonic()-start,'final_self_peak_RSS_KiB':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss})
print(json.dumps(json.loads((P/'manifest-verification.json').read_bytes())))
