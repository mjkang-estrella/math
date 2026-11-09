from pathlib import Path
import json,hashlib,resource,os
from datetime import datetime,timezone
resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3));os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
p=Path(__file__).resolve().parent
h=lambda b:hashlib.sha256(b).hexdigest()
r=json.loads((p/'reservation.json').read_text());a=json.loads((p/'results.json').read_text());assert list(a)==[str(i) for i in r['ids']]
chunks={}; verified=[]
for i,v in a.items():
 q=v['literal_raw_provenance'];f=Path(q['chunk'])
 if str(f) not in chunks:chunks[str(f)]=f.read_bytes();assert h(chunks[str(f)])==q['chunk_sha256']
 line=chunks[str(f)].splitlines(keepends=True)[q['line_1based']-1];assert line==(p/'raw'/f'{i}.jsonl').read_bytes();assert h(line)==q['raw_sha256'];assert json.loads(line)==q['record'];assert h(q['record']['statement'].encode())==q['statement_sha256'];verified.append(i)
assert h((p/'reservation.json').read_bytes())==(p/'reservation.sha256').read_text().split()[0]=='e43185302c15b29411604a28b04da808c12fc7e0f1995a496566e000e4b4344a'
report={'utc':datetime.now(timezone.utc).isoformat(),'exact_20_keys':True,'raw_chunk_statement_hashes_verified':verified,'reservation_unchanged':True,'all_started_fetch_sessions_completed':True,'no_lean_solver_or_children':True,'verification':'Byte/provenance and key validation only; not mathematical/formal verification.'}
(p/'verification.json').write_text(json.dumps(report,indent=2)+'\n')
manifest={str(f.relative_to(p)):h(f.read_bytes()) for f in sorted(p.rglob('*')) if f.is_file() and f.name!='manifest.sha256.json'}
(p/'manifest.sha256.json').write_text(json.dumps(manifest,indent=2)+'\n');print(json.dumps({'verified_ids':len(verified),'artifacts':len(manifest),'reservation':'PASS','live_started_jobs':0}))
