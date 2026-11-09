from pathlib import Path
import json,hashlib,resource,datetime,time
resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
t=time.monotonic();p=Path(__file__).resolve().parent;h=lambda b:hashlib.sha256(b).hexdigest();r=json.loads((p/'results.json').read_text());a=json.loads((p/'reservation.json').read_text());expected=(p/'reservation.sha256').read_text().split()[0];actual=h((p/'reservation.json').read_bytes());assert actual==expected
assert set(r)==set(map(str,a['ids'])) and len(r)==20
chunks={}
for k,v in r.items():
 pr=v['provenance'];f=Path(pr['chunk'])
 if str(f) not in chunks:
  b=f.read_bytes();assert h(b)==pr['chunk_sha256'];chunks[str(f)]=b.splitlines(keepends=True)
 line=chunks[str(f)][pr['one_based_line']-1];assert line==(p/pr['raw_file']).read_bytes();assert h(line)==pr['raw_sha256'];record=json.loads(line);assert record['statement']==v['literal_statement'];assert h(record['statement'].encode())==pr['statement_utf8_sha256'];assert v['accepted_credit']==0 and not v['pi_qualified']
(p/'reservation-after.json').write_text(json.dumps({'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'expected':expected,'actual':actual,'passed':True,'exact20keys':True,'assignment_changed':False},indent=2)+'\n')
(p/'final-check.json').write_text(json.dumps({'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'reservation':'PASS','keys':'exact20 PASS','original_chunk_raw_and_statement_hash_recheck':'PASS','credits_claimed':0,'pi_qualified':0,'lean_solver_runs':0,'children':0,'all_tool_sessions_completed':[78988,29075,89385],'script':str(Path(__file__).resolve()),'cpu_seconds':resource.getrusage(resource.RUSAGE_SELF).ru_utime,'maxrss_kib':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,'wall_seconds':time.monotonic()-t},indent=2)+'\n')
manifest={str(f.relative_to(p)):h(f.read_bytes()) for f in sorted(p.rglob('*')) if f.is_file() and f.name!='MANIFEST.sha256.json'}
(p/'MANIFEST.sha256.json').write_text(json.dumps(manifest,indent=2)+'\n');print(json.dumps({'files_hashed':len(manifest),'reservation':actual,'exact_results':len(r),'original_chunks_verified':len(chunks),'validation':'PASS'}))
