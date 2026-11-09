import pathlib,json,hashlib,resource,datetime,os
resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3));os.sched_setaffinity(0,set(sorted(os.sched_getaffinity(0))[:2]))
P=pathlib.Path(__file__).resolve().parent; sha=lambda b:hashlib.sha256(b).hexdigest(); results=json.loads((P/'results.json').read_text()); reserve=json.loads((P/'reservation.json').read_text())
assert len(results)==20 and set(results)==set(map(str,reserve['ids']))
for k,v in results.items():
 raw=(P/'raw'/f'{k}.jsonl').read_bytes(); prov=v['raw_provenance'];assert raw.endswith(b'\n') and raw.decode()==prov['literal_raw_utf8']
 assert sha(raw)==prov['raw_sha256'] and json.loads(raw)==v['record']
 assert sha(v['record']['statement'].encode())==prov['statement_sha256']
 chunk=pathlib.Path(prov['chunk']).read_bytes(); assert sha(chunk)==prov['chunk_sha256']
 assert chunk.splitlines(keepends=True)[prov['one_based_line']-1]==raw
 assert v['accepted_credit']==0
expected=(P/'reservation.sha256').read_text().strip();assert sha((P/'reservation.json').read_bytes())==expected
checks={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'exact_20_keys':True,'raw_embedded_and_individual_lines_verified':20,'literal_chunk_line_hashes_verified':20,'statement_hashes_verified':20,'reservation_after':expected,'accepted_credit':0,'lean_run':False,'numerical_search_run':False,'manifest_self_excluded':True,'verification_script':str(P/'verify.py')}
(P/'verification.json').write_text(json.dumps(checks,indent=2)+'\n')
files={str(f.relative_to(P)):sha(f.read_bytes()) for f in sorted(P.rglob('*')) if f.is_file() and f.name!='hashmanifest.json'}
(P/'hashmanifest.json').write_text(json.dumps({'utc':checks['utc'],'sha256':files,'self_excluded':True},indent=2)+'\n')
for rel,h in files.items():assert sha((P/rel).read_bytes())==h
print(json.dumps(checks));print('Manifest verified:',len(files),'files')
