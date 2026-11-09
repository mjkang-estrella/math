from pathlib import Path
import hashlib,json,datetime
L=Path(__file__).resolve().parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
m=json.loads((L/'manifest.json').read_text());checked=0
for name,h in m['sha256'].items():assert sha(L/name)==h,name;checked+=1
assert set(m['sha256'])=={str(p.relative_to(L)) for p in L.rglob('*') if p.is_file() and p.name not in m['excludes']}
history=json.loads((L/'history-screen.json').read_text());base=L.parent/'sol-fresh-source-discovery-r204'
idx=L/'frozen-index/sol-fresh-source-discovery-r204--history-receipt.json'
refs=json.loads(idx.read_text())['records'];original_matches=0;original_changed=0
for r in refs:
 assert sha(base/r['copy'])==r['sha256']
 p=Path(r['original'])
 if p.exists():
  if sha(p)==r['sha256']:original_matches+=1
  else:original_changed+=1
for r in json.loads((L/'freeze.json').read_text()):
 assert sha(Path(r['copy']))==r['sha256']
 if r['kind']!='administrative':assert sha(Path(r['original']))==r['sha256']
for r in history['references']:assert sha(Path(r['copy']))==sha(Path(r['original']))==r['sha256']
for r in json.loads((L/'source-map.json').read_text()):
 assert sha(L/'primary'/(r['id']+'.pdf'))==r['pdf_sha256']
 assert sha(L/'primary'/(r['id']+'.txt'))==r['text_sha256']
receipt=dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),PASS=True,manifest_sha256=sha(L/'manifest.json'),files=checked,immutable_history=len(refs),history_originals_matching=original_matches,history_originals_changed=original_changed,administrative='snapshot-only',scientific_resolution=False)
(L/'verification-receipt.json').write_text(json.dumps(receipt,indent=2));print(json.dumps(receipt))
