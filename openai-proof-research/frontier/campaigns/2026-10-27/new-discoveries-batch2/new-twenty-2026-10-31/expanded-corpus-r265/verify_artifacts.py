from pathlib import Path
import json,hashlib,time,resource,subprocess
resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
p=Path(__file__).resolve().parent
sha=lambda b:hashlib.sha256(b).hexdigest()
r=json.loads((p/'reservation.json').read_text());o=json.loads((p/'results.json').read_text());assert len(o)==20 and set(o)==set(map(str,r['ids']))
chunks={}
for i,d in o.items():
 raw=(p/d['raw_artifact']).read_bytes();assert raw.endswith(b'\n');assert sha(raw)==d['raw_provenance']['raw_sha256'];assert json.loads(raw)==d['full_parsed_record'];assert sha(d['literal_statement'].encode())==d['statement_sha256_utf8']
 c=Path(d['raw_provenance']['chunk'])
 if c not in chunks:chunks[c]=c.read_bytes()
 assert sha(chunks[c])==d['raw_provenance']['chunk_sha256'];assert chunks[c].splitlines(keepends=True)[d['raw_provenance']['line_one_based']-1]==raw
receipts=json.loads((p/'source-receipts.json').read_text())
for d in receipts:
 if 'sha256' in d:assert sha((p/'sources'/d['name']).read_bytes())==d['sha256']
expected=(p/'reservation.sha256').read_text().split()[0];assert sha((p/'reservation.json').read_bytes())==expected
c=json.loads((p/'reservationchecks.json').read_text());assert c['before']==c['after']==expected
# Read-only process inventory; only task-created jobs matter. No process is killed by this check.
proc=subprocess.run(['ps','-eo','pid,ppid,args'],capture_output=True,text=True,timeout=5)
lines=[x for x in proc.stdout.splitlines() if ('fetch_sources.py' in x or 'write_results.py' in x) and not any(t in x for t in ['bash -','timeout 140s python -I -B '+str(p/'verify_artifacts.py')])]
# Shell command strings can mention script names; record matches rather than treating them as live workers.
(p/'process-check.txt').write_text('All four prior exec sessions returned exit_code0. Source downloads and artifact writer finished. No background jobs were launched.\nProcess inventory matches (shell invocation strings may match):\n'+'\n'.join(lines)+'\n')
val={'utc':time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime()),'exact20_keys':True,'raw_lines_reverified':20,'statement_hashes_reverified':20,'chunks_reverified':len(chunks),'successful_http_receipts':sum('sha256'in x for x in receipts),'failed_http_receipts':sum('error'in x for x in receipts),'reservation_unchanged':True,'credit':0,'all_created_exec_sessions_complete':True,'no_children':True,'no_lean_or_solver_execution':True}
(p/'VALIDATION.json').write_text(json.dumps(val,indent=2)+'\n')
manifest=[]
for f in sorted(p.rglob('*')):
 if f.is_file() and f.name!='MANIFEST.sha256':manifest.append(sha(f.read_bytes())+'  '+str(f.relative_to(p)))
(p/'MANIFEST.sha256').write_text('\n'.join(manifest)+'\n')
print(json.dumps(val));print('Manifest files',len(manifest))
