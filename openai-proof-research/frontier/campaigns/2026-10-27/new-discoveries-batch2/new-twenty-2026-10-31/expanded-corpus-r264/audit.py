from pathlib import Path
import json,hashlib,datetime,resource,os
resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
p=Path(__file__).resolve().parent;sha=lambda b:hashlib.sha256(b).hexdigest();r=json.loads((p/'reservation.json').read_text());a=json.loads((p/'literal-provenance.json').read_text());z=json.loads((p/'results.json').read_text());assert list(z)==list(map(str,r['ids'])) and len(z)==20
for i,x in a.items():
 raw=(p/'literal'/f'{i}.jsonl').read_bytes();assert raw.endswith(b'\n');assert sha(raw)==x['raw_sha256'];assert json.loads(raw)==x['record'];assert sha(x['record']['statement'].encode())==x['statement_sha256']
 f=Path(x['chunk']);assert sha(f.read_bytes())==x['chunk_sha256'];original=next(b for n,b in enumerate(f.open('rb'),1) if n==x['line']);assert original==raw
checks=json.loads((p/'reservation-hashchecks.json').read_text());checks.update(after=sha((p/'reservation.json').read_bytes()),after_utc=datetime.datetime.now(datetime.timezone.utc).isoformat());assert checks['before']==checks['after']==checks['expected'];checks['pass']=True;(p/'reservation-hashchecks.json').write_text(json.dumps(checks,indent=2))
z['375479']['historical_status']=z['375479']['historical_status'].replace('r198 ID379820','r198');z['318509']['review_depth']['primary']+=' Definition: P_(n,k) consists of paths obtained from the n-edge directed path by reversing at most k arcs.';z['318509']['remaining_gaps']='Path-family definition now recovered; no uniform threshold construction; all citing bodies/journal versions not audited.'
(p/'results.json').write_text(json.dumps(z,indent=2,ensure_ascii=False))
# Report only processes bearing our specific collection script paths; do not touch other workers.
active=[]
for q in Path('/proc').iterdir():
 if q.name.isdigit() and int(q.name)!=os.getpid():
  try:
   argv=(q/'cmdline').read_bytes().split(b'\0');parts=[t.decode(errors='replace') for t in argv]
   if any(t==str(p/s) for s in ['collect.py','versions.py','extras.py','followups.py','package.py'] for t in parts):active.append({'pid':int(q.name),'argv':parts})
  except (OSError,PermissionError):pass
assert not active,active
(p/'final-audit.json').write_text(json.dumps({'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'exact_20_keys':True,'raw_lines_and_corpus_hashes_verified':True,'frozen_reservation':True,'active_lane_jobs':active,'accepted_credit_changes':0,'remaining_qualification_gaps':True,'no_eligible_candidate':True},indent=2))
(p/'SHA256SUMS').write_text(''.join(sha(f.read_bytes())+'  '+str(f.relative_to(p))+'\n' for f in sorted(p.rglob('*')) if f.is_file() and f.name!='SHA256SUMS'))
print((p/'final-audit.json').read_text());print('manifest files',len((p/'SHA256SUMS').read_text().splitlines()))
