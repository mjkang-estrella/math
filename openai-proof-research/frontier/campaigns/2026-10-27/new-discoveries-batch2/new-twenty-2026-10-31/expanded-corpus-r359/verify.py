import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]);resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
import pathlib,json,hashlib,datetime,time
L=pathlib.Path(__file__).resolve().parent;H=lambda b:hashlib.sha256(b).hexdigest();start=time.monotonic()
def js(n,v):
 p=(L/n).resolve();assert p.is_relative_to(L);p.write_text(json.dumps(v,indent=2)+'\n')
P=json.loads((L/'provenance.json').read_text());R=json.loads((L/'reservation.json').read_text());assert len(R['ids'])==len(set(R['ids']))==20;assert H((L/'reservation.json').read_bytes())=='ed4524d5212fec69c21dd4f90f62e2f6b8007f4758ee3d4fe1e73ae135629630';assert set(json.loads((L/'results.json').read_text()))==set(map(str,R['ids']))
groups={}
for id,p in P.items():groups.setdefault(p['chunk_path'],[]).append((id,p))
for path,entries in groups.items():
 assert 'pi-mathdb-full-corpus-inventory-r301/corpus/mathdb-normalized-chunk-' in path
 b=pathlib.Path(path).read_bytes();lines=b.splitlines(keepends=True)
 for id,p in entries:
  assert H(b)==p['chunk_sha256'];line=lines[p['one_based_line']-1];assert H(line)==p['raw_sha256'];assert line==(L/f'literal/{id}.jsonl').read_bytes();assert line.endswith(b'\n');j=json.loads(line);assert j==json.loads((L/f'literal/{id}.json').read_text())==p['full_parsed_record'];assert H(j['statement'].encode())==p['statement_sha256']
js('original-binding-verification.json',{'original_chunks_verified':len(groups),'literal_bindings_verified':20,'reservation_sha256':H((L/'reservation.json').read_bytes()),'results_exact20':True,'exit':0})
files=[]
# Traversal is confined to this lane. Protected external paths are never enumerated.
for p in sorted(L.rglob('*')):
 if p.is_file() and p.name not in ['artifact-manifest.json','manifest-verification.json']:
  assert p.resolve().is_relative_to(L) and not p.is_symlink();b=p.read_bytes();files.append({'path':str(p.relative_to(L)),'bytes':len(b),'sha256':H(b)})
js('artifact-manifest.json',{'files':files,'excluded_self_and_verification':True})
for x in files:
 b=(L/x['path']).read_bytes();assert len(b)==x['bytes'] and H(b)==x['sha256']
js('manifest-verification.json',{'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'manifest_sha256':H((L/'artifact-manifest.json').read_bytes()),'verified_artifact_count':len(files),'all_hashes_match':True,'original_chunk_and_literal_bindings':20,'reservation_after':H((L/'reservation.json').read_bytes()),'wall_seconds':time.monotonic()-start,'exit':0,'affinity':sorted(os.sched_getaffinity(0)),'self_rusage':list(resource.getrusage(resource.RUSAGE_SELF)),'telemetry':'self only, not concurrent group peak','live_child_jobs':0})
print(json.dumps({'verified_artifacts':len(files),'original_bindings':20,'exact_results':20,'reservation':'unchanged','credit':0,'campaign':'52/60 unchanged','exit':0}))
