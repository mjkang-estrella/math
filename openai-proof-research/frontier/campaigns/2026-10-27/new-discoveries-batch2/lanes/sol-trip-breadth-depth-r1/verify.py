from pathlib import Path
import hashlib,json,datetime
L=Path(__file__).resolve().parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
manifest=json.loads((L/'finalmanifest.json').read_text())
assert not any(r['path'] in ['finalmanifest.json','verification-receipt.json'] for r in manifest)
for r in manifest:
 p=L/r['path'];assert sha(p)==r['sha256'] and p.stat().st_size==r['bytes'],str(p)
expected={r['path'] for r in manifest}
assert {str(p.relative_to(L)) for p in L.rglob('*') if p.is_file() and p.name not in ['finalmanifest.json','verification-receipt.json']}==expected
for r in json.loads((L/'freeze.json').read_text()):
 assert sha(L/r['copy'])==r['sha256']
 if not r['administrative']:assert sha(Path(r['original']))==r['sha256']
bindings=json.loads((L/'history-bindings.json').read_text())
for r in bindings:assert sha(Path(r['path']))==r['sha256']
for r in [json.loads(s) for s in (L/'http.jsonl').read_text().splitlines()]:
 if 'sha256' in r:assert any(sha(p)==r['sha256'] for p in (L/'sources').iterdir())
assert not (L/'PROOF.md').exists()
result=dict(status='PASS',utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),manifest_sha256=sha(L/'finalmanifest.json'),manifest_files=len(manifest),history_references=len(bindings),scientific_originals_and_copies='unchanged',administration='snapshot hashes only; no live-equality demand',scientific_status='UNSOLVED; checks do not prove conjecture',counts='9/39/next40 unchanged',limits='external helper_guard AS/groupRSS512MiB CPU210 wall230; no raise')
(L/'verification-receipt.json').write_text(json.dumps(result,indent=2));print(json.dumps(result))
