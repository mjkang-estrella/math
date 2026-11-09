from pathlib import Path
import json,hashlib,datetime,collections
D=Path(__file__).resolve().parents[1];sha=lambda b:hashlib.sha256(b).hexdigest()
x=json.loads((D/'results.json').read_text());ids=json.loads((D/'reservation.json').read_text())['ids'];assert set(x)==set(map(str,ids));assert len(x)==40
for i,v in x.items():
 raw=(D/f'raw/{i}.jsonl').read_bytes();assert raw.endswith(b'\n');assert sha(raw)==v['provenance']['raw_sha256'];assert sha(v['statement'].encode())==v['provenance']['statement_utf8_sha256']
for f in (D/'sources').glob('*.receipt.json'):
 a=json.loads(f.read_text())
 if 'sha256' in a:assert sha(Path(a['path']).read_bytes())==a['sha256'],f
receipts={n:json.loads((D/f'logs/fresh-{n}.receipt.json').read_text()) for n in ['loop','kernel','audit']};assert all(v['returncode']==0 for v in receipts.values())
audit=(D/'logs/fresh-audit.log').read_text();rows=[l for l in audit.splitlines() if l.startswith('INVENTORY|')];assert len(rows)==28
for r in rows:assert '|false|' in r and '|axiom|' not in r
for f in [D/'formal/Loop.lean']:
 s=f.read_text();assert not any(w in s.split() for w in ['sorry','admit','axiom','unsafe','native_decide','ofReduceBool'])
BIN=Path('/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin')
result={'archived_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'status':'strict_fresh_build_leanchecker_full_local_audit_PASS','local_declarations':len(rows),'axioms':['propext','Classical.choice','Quot.sound'],'receipts':receipts,'binaries':{n:sha((BIN/n).read_bytes()) for n in ['lean','leanchecker']},'expected_mathlib_revision':'d13f23b723b8a846827a245b89c10fc7d3f11612','dependency_trust':'Cached upstream oleans; no source-to-olean attestation or full upstream rebuild. Sampled RSS caps, not cgroup/transient-peak guarantees.','packet_sha256':sha((D/'380362-proof-source.zip').read_bytes()),'accepted_credit':0,'counts_unchanged':True,'outcomes':dict(collections.Counter(v['outcome'] for v in x.values()))}
(D/'verification.json').write_text(json.dumps(result,indent=2)+'\n')
manifest={str(f.relative_to(D)):sha(f.read_bytes()) for f in D.rglob('*') if f.is_file() and f.name!='SHA256SUMS.json' and '__pycache__' not in str(f) and f.suffix not in ['.olean','.ilean','.trace']}
(D/'SHA256SUMS.json').write_text(json.dumps(manifest,indent=2)+'\n');print('PASS:',len(x),'IDs;',len(rows),'local declarations;',len(manifest),'bound files')
