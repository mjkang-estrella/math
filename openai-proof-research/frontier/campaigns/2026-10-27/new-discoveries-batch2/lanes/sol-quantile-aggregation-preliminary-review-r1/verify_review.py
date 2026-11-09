from pathlib import Path
import json,hashlib
D=Path(__file__).resolve().parent
H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
manifest=json.loads((D/'manifest.json').read_text())
assert {str(p.relative_to(D)) for p in D.rglob('*') if p.is_file() and p.name not in ['manifest.json','verification-receipt.json']}==set(manifest)
for r,h in manifest.items(): assert H(D/r)==h,r
rows=json.loads((D/'freeze.json').read_text())
n=0
for r in rows:
    assert H(D/r['copy'])==r['sha256'],r
    if not r['copy'].startswith('frozen/administrative/'):
        assert H(Path(r['original']))==r['sha256'],r
        n+=1
candidate=D.parent/'sol-quantile-aggregation-full-r1'
cm=json.loads((D/'frozen/manifest.json').read_text())
for r,h in cm.items(): assert H(candidate/r)==h,r
for row in map(json.loads,(D/'review-http.jsonl').read_text().splitlines()):
    if 'sha256' in row: assert H(D/(row['name']+'.body'))==row['sha256']
out={'status':'PASS','review_manifest_files':len(manifest),'original_scientific_and_candidate_files_unchanged':n,'candidate_manifest_entries_verified':len(cm),'review_manifest_sha256':H(D/'manifest.json'),'administrative_originals':'not rechecked; snapshot only','manifest_excludes':['manifest.json','verification-receipt.json']}
(D/'verification-receipt.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out))
