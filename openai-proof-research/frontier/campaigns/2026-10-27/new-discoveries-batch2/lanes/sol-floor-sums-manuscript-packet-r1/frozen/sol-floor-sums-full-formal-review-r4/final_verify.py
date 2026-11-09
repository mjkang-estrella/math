from pathlib import Path
import json,hashlib
L=Path(__file__).resolve().parent
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for b in iter(lambda:f.read(1048576),b''):h.update(b)
 return h.hexdigest()
M=json.loads((L/'final-manifest.json').read_text());excluded={'final-manifest.json','final-verification-receipt.json'}
assert set(M)=={str(p.relative_to(L)) for p in L.rglob('*') if p.is_file() and str(p.relative_to(L)) not in excluded}
for n,h in M.items():assert sha(L/n)==h,n
for r in json.loads((L/'original-source-bindings.json').read_text()):assert sha(Path(r['path']))==sha(L/r['copy'])==r['sha256'],r
for r in json.loads((L/'binding.json').read_text()):assert sha(Path(r['path']))==sha(L/'frozen'/r['copy'])==r['sha256'],r
for r in json.loads((L/'immutable-references.json').read_text()):assert sha(Path(r['path']))==r['sha256'],r
assert sha(L.parent/'sol-floor-sums-dag-assembly-formal-r3/source-only.tar.gz')==sha(L/'source-only.tar.gz')==sha(L/'reproduced-source-only.tar.gz')=='17ba800adb3154f5c3929ef076c47b9d1f0adaace1576793faa4154ff19be13f'
p=json.loads((L/'pins-independent.json').read_text());assert sha(Path(p['lean']))==p['lean_sha256']
for r in p['packages']:
 g=Path(p['formal'])/'.lake/packages'/r['name']/'.git';h=(g/'HEAD').read_text().strip()
 if h.startswith('ref: '):h=(g/h[5:]).read_text().strip()
 assert h==r['revision']
a=json.loads((L/'independent-replay-receipt.json').read_text());assert a['status']=='PASS' and a['actual_declarations']==35654 and a['origins']==436
for n,h in M.items():assert sha(L/n)==h,n
out=dict(integrity='PASS',manifest_files=len(M),manifest_sha256=sha(L/'final-manifest.json'),original_copy_bindings='PASS before/after',replay='independent-replay-receipt.json',review='review.md',counts='unchanged 9/39/next40',acceptance='root only; no acceptance by this review')
(L/'final-verification-receipt.json').write_text(json.dumps(out,indent=2));print(out)
