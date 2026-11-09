from pathlib import Path
import json,hashlib,datetime
L=Path(__file__).resolve().parent
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for b in iter(lambda:f.read(1048576),b''):h.update(b)
 return h.hexdigest()
def bindings():
 for r in json.loads((L/'original-source-bindings.json').read_text()):assert sha(Path(r['path']))==sha(L/r['copy'])==r['sha256'],r
 for r in json.loads((L/'binding.json').read_text()):assert sha(Path(r['path']))==sha(L/'frozen'/r['copy'])==r['sha256'],r
 for r in json.loads((L/'immutable-references.json').read_text()):assert sha(Path(r['path']))==r['sha256'],r
 c=L.parent/'sol-floor-sums-dag-assembly-formal-r3/source-only.tar.gz'
 assert sha(c)==sha(L/'source-only.tar.gz')=='17ba800adb3154f5c3929ef076c47b9d1f0adaace1576793faa4154ff19be13f'
bindings()
receipt=json.loads((L/'independent-replay-receipt.json').read_text());assert receipt['status']=='PASS'
out=dict(created_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),role='solo independent review; no children',assigned_lane=str(L),candidate=str(L.parent/'sol-floor-sums-dag-assembly-formal-r3'),archive_sha256=sha(L/'source-only.tar.gz'),scientific_binding_file='binding.json',immutable_predecessors='immutable-references.json',administrative_snapshots={n:sha(L/n) for n in ['ledger.json','prior-campaign-context.json']},formal_receipt=receipt,source_scope='Thanatipanonda–Wong2018 Section4 pp14–15 independent four-variable lower bound only',prior_art='bounded inherited source/prior review; no new live clearance',counts='9 additional /39 total /next40; root alone accepts',failures='FAILURES.md',no_external_actions=True)
(L/'provenance.json').write_text(json.dumps(out,indent=2))
# Objects are disposable local replay products, not part of the source certificate.
for p in (L/'replay').rglob('*'):
 if p.is_file() and p.suffix in ['.olean','.ilean','.ir']:p.unlink()
excluded={'final-manifest.json','final-verification-receipt.json'}
manifest={str(p.relative_to(L)):sha(p) for p in sorted(L.rglob('*')) if p.is_file() and str(p.relative_to(L)) not in excluded}
(L/'final-manifest.json').write_text(json.dumps(manifest,indent=2))
print('manifest',len(manifest),'files; originals/copies unchanged')
