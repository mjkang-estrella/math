from pathlib import Path
import json,hashlib,datetime,subprocess,sys
L=Path(__file__).resolve().parent
sha=lambda b:hashlib.sha256(b).hexdigest()
excluded={'finalmanifest.json','verification-receipt.json'}
assert set(json.loads((L/'finalmanifest.json').read_text())['exclusions'])==excluded
manifest=json.loads((L/'finalmanifest.json').read_text())['files']
actual={str(p.relative_to(L)) for p in L.rglob('*') if p.is_file() and str(p.relative_to(L)) not in excluded}
assert actual==set(manifest),('inventory mismatch',actual.symmetric_difference(manifest))
for n,h in manifest.items():assert sha((L/n).read_bytes())==h,n
before=[]
for r in json.loads((L/'scientific-freeze.json').read_text()):
    assert sha(Path(r['original']).read_bytes())==r['sha256'],r['original']
    assert sha((L/r['copy']).read_bytes())==r['sha256'],r['copy']
    before.append(r['original'])
p=subprocess.run([sys.executable,str(L/'checks.py')],capture_output=True,check=True)
assert p.stdout==(L/'checks-final.json').read_bytes()
for r in json.loads((L/'scientific-freeze.json').read_text()):
    assert sha(Path(r['original']).read_bytes())==r['sha256']==sha((L/r['copy']).read_bytes())
for n,h in manifest.items():assert sha((L/n).read_bytes())==h,n
receipt=dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),status='PASS',manifest_sha256=sha((L/'finalmanifest.json').read_bytes()),manifest_files=len(manifest),scientific_pairs=len(before),original_copy_before_after='PASS',exact_checker_replay='BYTE_IDENTICAL',exclusions=sorted(excluded),limits='Manifest and this receipt explicitly excluded. Scientific and manifest payload verified after final writes, before/after checker replay. Administrative live files are not scientific bindings.')
(L/'verification-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt,indent=2))
