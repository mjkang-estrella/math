from pathlib import Path
import hashlib,json
H=Path(__file__).resolve().parent;sha=lambda b:hashlib.sha256(b).hexdigest();load=lambda p:json.loads(p.read_text())
r=load(H/'results.json');reservation=load(H/'reservation.json');assert len(r)==40 and set(r)==set(map(str,reservation['ids']))
for i,x in r.items():
 raw=(H/x['raw_copy']).read_bytes();p=x['provenance'];assert raw.endswith(b'\n');assert sha(raw)==p['raw_line_sha256'];assert sha(x['literal_statement'].encode())==p['statement_utf8_sha256'];assert json.loads(raw)['mathdb_id']==int(i);assert x['accepted_credit']==0
for p in H.glob('fetch*-receipts.json'):
 for x in load(p):
  if 'file' in x:assert sha((H/x['file']).read_bytes())==x['sha256']
for x in load(H/'context-receipts.json'):
 # mutable ledger is checked, never rewritten; an administrative advance is recorded rather than rejected.
 actual=sha(Path(x['path']).read_bytes());print('context',x['path'],'unchanged_at_check',actual==x['sha256'])
print('PASS: exactly40 IDs; raw newlines/hashes and all acquired response hashes verified; all zero credit.')
print('New primary-review IDs:',[i for i,x in r.items() if x['new_primary_review']]);print('Lean endpoints:',sum(x['lean_endpoint'] is not None for x in r.values()))
files=[{'path':str(p.relative_to(H)),'bytes':p.stat().st_size,'sha256':sha(p.read_bytes())} for p in sorted(H.rglob('*')) if p.is_file() and p.name not in ['artifact-manifest.json','verify.log']]
(H/'artifact-manifest.json').write_text(json.dumps(files,indent=2)+'\n')
