import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]);resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
import runpy,sys
sys.argv=['research.py','verify'];d=runpy.run_path('research.py');globals().update({k:d[k] for k in ['L','r','json','H','dump','receipt']})
p=json.loads((L/'provenance.json').read_text());results=json.loads((L/'results.json').read_text());assert len(results)==20 and set(results)==set(p)==set(map(str,r['ids']))
chunks={};bindings=[]
for i,v in p.items():
 path=d['pathlib'].Path(v['chunk']);assert path.parent.name=='corpus' and path.name.startswith('mathdb-normalized-chunk-')
 if str(path) not in chunks:
  b=path.read_bytes();assert H(b)==v['chunk_sha256'];chunks[str(path)]=b.splitlines(keepends=True)
 raw=chunks[str(path)][v['line']-1];assert raw.endswith(b'\n') and raw==(L/'literal'/f'{i}.jsonl').read_bytes() and H(raw)==v['raw_sha256'];rec=json.loads(raw);assert rec==v['record']==json.loads((L/'literal'/f'{i}.json').read_text());assert H(rec['statement'].encode())==v['statement_sha256'];assert str(rec['mathdb_id'])==i;bindings.append(i)
sha=H((L/'reservation.json').read_bytes());assert sha=='18bb899148b2e2f04a36acb0a8c1ef36e62d617d4e6779da2cf2bee6ad4d12fc';assert (L/'reservation.sha256').read_text().strip()==sha
dump('verification.json',{'reservation_before':'PASS; first validation before extraction','reservation_after_sha256':sha,'fixed_count':20,'exact_keys':True,'rechecked_bindings':bindings,'raw_newlines_preserved':True,'chunk_raw_statement_hashes_verified':True,'parsed_records_equal':True,'credit':0,'campaign':'52/60','task_owned_background_jobs':0,'self_rusage':list(resource.getrusage(resource.RUSAGE_SELF))})
receipt('final-verification')
# Lane-only manifest; never historical traversal.
files={}
for path in sorted(L.rglob('*')):
 assert path.resolve().is_relative_to(L)
 if path.is_file() and path.name not in ['manifest.json','manifest-verification.json']:
  files[str(path.relative_to(L))]={'bytes':path.stat().st_size,'sha256':H(path.read_bytes())}
dump('manifest.json',{'algorithm':'SHA256','excluded':['manifest.json','manifest-verification.json'],'artifacts':files})
m=(L/'manifest.json').read_bytes();j=json.loads(m)
for n,v in j['artifacts'].items():
 b=(L/n).read_bytes();assert H(b)==v['sha256'] and len(b)==v['bytes']
dump('manifest-verification.json',{'manifest_sha256':H(m),'artifacts_verified':len(files),'every_hash_and_size_matches':True,'reservation_sha256':sha,'exact_results':20,'exit':0,'self_rusage':list(resource.getrusage(resource.RUSAGE_SELF))})
print('VERIFIED',len(files),'artifacts; 20 exact bindings; reservation',sha)
