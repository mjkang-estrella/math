from pathlib import Path
import hashlib,json,datetime
L=Path(__file__).resolve().parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
m=json.loads((L/'final-manifest.json').read_text())
expected={r['path'] for r in m['files']}
actual={str(p.relative_to(L)) for p in L.rglob('*') if p.is_file() and p.name not in m['excludes']}
assert expected==actual
for r in m['files']:
    p=L/r['path'];assert sha(p)==r['sha256'] and p.stat().st_size==r['bytes']
f=json.loads((L/'freeze.json').read_text())
for r in f['bindings']:
    assert sha(Path(r['copy']))==r['sha256']
    if r['kind'].startswith('scientific'):assert sha(Path(r['original']))==r['sha256']
for r in json.loads((L/'references.json').read_text()):assert sha(Path(r['path']))==r['sha256']
for p in (L/'retrieval').glob('*.freeze.json'):
    r=json.loads(p.read_text());pdf=p.with_name(p.name.replace('.freeze.json','.pdf'))
    if pdf.exists():assert sha(pdf)==r['sha256']
receipt={'status':'PASS','utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'manifest_sha256':sha(L/'final-manifest.json'),'verified_files':len(m['files']),'scientific_originals_and_copies':'unchanged','reused_references':'unchanged','admin':'snapshots verified only','separate_invocation':True}
(L/'verification-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt))
