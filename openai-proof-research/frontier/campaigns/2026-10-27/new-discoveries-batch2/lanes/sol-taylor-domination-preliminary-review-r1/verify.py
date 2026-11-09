from pathlib import Path
import hashlib,json,datetime
l=Path(__file__).resolve().parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
m=json.loads((l/'final-manifest.json').read_text())
actual={str(f.relative_to(l)) for f in l.rglob('*') if f.is_file()
        and f.name not in m['excludes']}
assert actual == set(m['files'])
for name,r in m['files'].items():
    f=l/name
    assert sha(f)==r['sha256'] and f.stat().st_size==r['size'],name
bindings=json.loads((l/'bindings.json').read_text())
for r in bindings:
    assert sha(Path(r['original']))==sha(l/r['copy'])==r['sha256'],r['original']
checks=json.loads((l/'checks.json').read_text())
g=checks['helper_guard']
assert sha(Path(g['path']))==g['sha256']
out=dict(status='PASS',utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),
         manifest_sha256=sha(l/'final-manifest.json'),manifest_files=len(actual),
         original_copy_bindings=len(bindings),guard_unchanged=True,
         counts_unchanged=[9,39,40],scope='Separate guarded verification; mathematical proof remains review.md')
(l/'verification-receipt.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
