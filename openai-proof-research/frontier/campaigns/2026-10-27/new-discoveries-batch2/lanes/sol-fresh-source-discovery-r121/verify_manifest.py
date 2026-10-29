from pathlib import Path
import hashlib,json,gzip
L=Path(__file__).resolve().parent
def digest(p):
    h=hashlib.sha256()
    with p.open('rb') as f:
        while b:=f.read(65536):h.update(b)
    return h.hexdigest()
m=json.loads((L/'finalmanifest.json').read_text())
actual={str(p.relative_to(L)) for p in L.rglob('*') if p.is_file() and p.name!='finalmanifest.json'}
assert actual==set(m['files'])
for n,r in m['files'].items():
    p=L/n
    assert p.stat().st_size==r['bytes'] and digest(p)==r['sha256'],n
for r in json.loads((L/'context-receipts.json').read_text()):
    assert digest(L/r['copy'])==r['sha256'],r['copy']
for line in (L/'http.jsonl').read_text().splitlines():
    r=json.loads(line)
    if 'copy' in r:assert digest(L/r['copy'])==r['sha256'],r['copy']
r=json.loads((L/'index-compression.json').read_text());h=hashlib.sha256();n=0
with gzip.open(L/r['compressed'],'rb') as f:
    while b:=f.read(65536):h.update(b);n+=len(b)
assert h.hexdigest()==r['uncompressed_sha256'] and n==r['uncompressed_bytes']
g=json.loads((L/'provenance.json').read_text())['guard']
assert digest(Path(g['path']))==g['sha256']
assert not (L/'PROOF.md').exists()
print(json.dumps({'manifest':'PASS','files':len(actual),'primary_receipts':'PASS','context_snapshots':'PASS','compressed_index':'PASS','guard_unchanged':True,'science':'NO_FULL_ELIGIBLE_RESULT'}))
