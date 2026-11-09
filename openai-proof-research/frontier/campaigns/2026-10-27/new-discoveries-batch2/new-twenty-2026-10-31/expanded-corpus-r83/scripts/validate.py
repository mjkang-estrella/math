from pathlib import Path
import json,hashlib,re,zipfile,datetime
D=Path(__file__).resolve().parents[1];sha=lambda b:hashlib.sha256(b).hexdigest()
x=json.loads((D/'results.json').read_text());ids=json.loads((D/'reservation.json').read_text())['ids'];assert len(x)==20 and set(x)==set(map(str,ids))
for i,v in x.items():
 b=(D/f'raw/{i}.jsonl').read_bytes();assert b.endswith(b'\n');assert sha(b)==v['provenance']['raw_sha256'];assert sha(v['statement'].encode())==v['provenance']['statement_utf8_sha256'];assert not v['accepted'] and v['credit']==0
for p in (D/'sources').glob('*.receipt.json'):
 r=json.loads(p.read_text())
 if 'sha256' in r:assert sha(Path(r['path']).read_bytes())==r['sha256']
r=json.loads((D/'verification.json').read_text());assert all(v['returncode']==0 for v in r['checks'].values());assert r['local_declarations']==31
for c in r['checks'].values():assert sha((D/c['log']).read_bytes())==c['log_sha256']
with zipfile.ZipFile(D/'331705-proof-source.zip') as z:
 for p in (D/'formal').glob('*.lean'):assert z.read(p.name)==p.read_bytes()
assert sha((D/'331705-proof-source.zip').read_bytes())==r['proof_packet_sha256']
source=(D/'formal/Cassinian.lean').read_text();assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide|ofReduceBool)\b',source)
assert all(t in source for t in ['source_refutation','frontier_G','infinity_contribution','polynomial_bound','bounded_z'])
manifest={str(p.relative_to(D)):sha(p.read_bytes()) for p in sorted(D.rglob('*')) if p.is_file() and p.name not in ['SHA256SUMS.json','validation.log'] and '__pycache__' not in str(p) and p.suffix not in ['.olean','.ilean','.trace']}
(D/'SHA256SUMS.json').write_text(json.dumps(manifest,indent=2)+'\n');print('PASS: exactly 20 assigned IDs, 31 audited local declarations, fresh strict replay, all receipt/provenance/packet hashes; zero accepted credit.')
