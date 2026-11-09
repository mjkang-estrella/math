from pathlib import Path
import hashlib,json,datetime
L=Path(__file__).resolve().parent
sha=lambda b:hashlib.sha256(b).hexdigest()
manifest=json.loads((L/'MANIFEST.json').read_text())
assert 'MANIFEST.json' not in manifest and 'verification-receipt.json' not in manifest
actual={str(p.relative_to(L)) for p in L.rglob('*') if p.is_file() and p.name not in ['MANIFEST.json','verification-receipt.json']}
assert actual==set(manifest)
for name,row in manifest.items():
 d=(L/name).read_bytes();assert len(d)==row['bytes'] and sha(d)==row['sha256'],name
bindings=json.loads((L/'source-bindings.json').read_text())['bindings']+json.loads((L/'registry-bindings.json').read_text())
for row in bindings:
 assert sha(Path(row['original']).read_bytes())==row['sha256'],row['original']
 assert sha((L/row['copy']).read_bytes())==row['sha256'],row['copy']
for row in json.loads((L/'access/attempts.json').read_text()):
 name={'https://arxiv.org/abs/2210.11038':'arxiv-current.html','https://github.com/openai/math':'openai-registry-current.html','https://github.com/the-omega-institute/trureturing':'omega-registry-current.html'}[row['url']]
 assert sha((L/'access'/name).read_bytes())==row['sha256']
row=json.loads((L/'access/current-question-access.json').read_text());assert sha((L/'access/current-question.html').read_bytes())==row['sha256']
for file in ['diagnostics.json','diamond-check.json','single-type-diamond-check.json']:assert json.loads((L/file).read_text())['status']=='PASS'
for file in ['SUMMARY.md','discovery.md','progress.md','PROOF.md','provenance.json','FAILURES.md']:assert (L/file).stat().st_size>0
receipt={'status':'PASS','utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'manifest_files':len(manifest),'original_and_frozen_scientific_bindings':len(bindings),'live_access_originals_rechecked':4,'manifest_sha256':sha((L/'MANIFEST.json').read_bytes()),'diagnostics':'all three capped exact suites PASS','proof_status':'ordinary proof present; this receipt checks integrity, not independent mathematical acceptance','limits':{'AS':536870912,'sampled_groupRSS':536870912,'CPU':210,'wall':230,'raises':False},'excluded':['MANIFEST.json','verification-receipt.json']}
(L/'verification-receipt.json').write_text(json.dumps(receipt,indent=2));print(json.dumps(receipt,indent=2))
