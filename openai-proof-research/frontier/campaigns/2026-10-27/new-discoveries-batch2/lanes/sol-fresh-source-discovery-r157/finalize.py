import json,hashlib,datetime,os
from pathlib import Path
L=Path(__file__).resolve().parent
def sha(b):return hashlib.sha256(b).hexdigest()
def now():return datetime.datetime.now(datetime.timezone.utc).isoformat()
def save(n,j):(L/n).write_text(json.dumps(j,indent=2)+'\n')
http=[json.loads(x) for x in (L/'http.jsonl').read_text().splitlines()]
for r in http:
 if 'sha256' in r:
  b=(L/'sources'/r['name']).read_bytes();assert len(b)==r['bytes'] and sha(b)==r['sha256']
guard=L.parent/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py'
history=json.loads((L/'history-receipt.json').read_bytes())
ctx={}
for n in ['ledger.json','prior-campaign-context.json','NEXT.md']:
 p=L/('context-'+n);b=p.read_bytes();ctx[n]=dict(sha256=sha(b),bytes=len(b))
 if n.endswith('.json'):json.loads(b)
ledger=json.loads((L/'context-ledger.json').read_bytes())
assert (ledger['accepted_count'],ledger['total_accepted_count'],ledger['next_global_outcome_number'])==(9,39,40)
checks=json.loads((L/'checks.json').read_bytes());assert checks['source_resolution'] is False
save('provenance.json',dict(created_utc=now(),status='UNRESOLVED; zero qualifying discoveries',selected_source=dict(authors=['A. Almasi','A. Moradpouri','M. Shahbazi'],arxiv='2503.17880v1',doi='10.1007/JHEP09(2025)208',journal_date='2025-09-26',claim='Entropy Bound Conjecture, Section 4.3 p16; full general-H scope in Section 4.5 pp17-19'),http=http,context=ctx,history=dict(records=len(history['records']),changed=len(history['changed']),missing=history['missing'],base=history['base'],base_sha256=history['base_sha256']),resource_guard=dict(path=str(guard),sha256=sha(guard.read_bytes()),AS_bytes=512*1024**2,group_RSS_bytes=512*1024**2,CPU_seconds=210,wall_seconds=230,nominal_sample_ms=40,sampling_limit='Unsampled transients not excluded',env={'OPENBLAS_NUM_THREADS':'1','OMP_NUM_THREADS':'1','PYTHONDONTWRITEBYTECODE':'1'}),limits=['No universal source proof or counterexample','No independent eligibility clearance; no Lean or manuscript','Companion published body not compared; guessed DOI 404 retained','Two inherited capped path intervals remain','No semantic absence or worldwide priority claim','Supporting checks do not certify any metric CM hypothesis'],web_searches=['arxiv conjecture log-concavity 2026 probability','arxiv conjecture complete monotonicity 2025','Almasi Moradpouri entropy bound','2503.17880 proof conjecture','Regular black holes and complete monotonicity conjecture proof github'],counts=dict(additional=9,total=39,next=40,credit=0),external_actions=False))
exclude={'scientific-freeze.json','finalmanifest.json','manifest-verification.json'}
science=[]
for p in sorted(L.rglob('*')):
 if p.is_file() and p.name not in exclude:
  b=p.read_bytes();science.append(dict(path=str(p.relative_to(L)),sha256=sha(b),bytes=len(b)))
save('scientific-freeze.json',dict(utc=now(),status='immutable scientific snapshot; no later edits authorized by this lane',files=science))
entries=science+[dict(path='scientific-freeze.json',sha256=sha((L/'scientific-freeze.json').read_bytes()),bytes=(L/'scientific-freeze.json').stat().st_size)]
save('finalmanifest.json',dict(utc=now(),files=entries,excludes=['finalmanifest.json (self)','manifest-verification.json (verification receipt)']))
for r in entries:
 b=(L/r['path']).read_bytes();assert len(b)==r['bytes'] and sha(b)==r['sha256']
save('manifest-verification.json',dict(utc=now(),status='PASS',manifest_sha256=sha((L/'finalmanifest.json').read_bytes()),manifest_entries=len(entries),scientific_entries=len(science),http_hashes_verified=sum('sha256' in r for r in http),checks_status=checks['status']))
for p in L.rglob('*'):
 if p.is_file():p.chmod(0o444)
print(json.dumps(json.loads((L/'manifest-verification.json').read_bytes()),indent=2))
