from pathlib import Path
import hashlib,json
root=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
rows=json.loads((root/'frozen-inputs.json').read_text())
for r in rows:
 assert sha(root/r['copy'])==r['sha256'],r
 if not r['copy'].startswith('administrative/'):
  assert sha(Path(r['original']))==r['sha256'],r
print(json.dumps({'verified_copies':len(rows),'scientific_originals_and_copies':'PASS','administrative':'snapshot only'}))
