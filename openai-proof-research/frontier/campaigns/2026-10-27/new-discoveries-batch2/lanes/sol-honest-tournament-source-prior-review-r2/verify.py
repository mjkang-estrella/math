from pathlib import Path
import hashlib,json,datetime
L=Path(__file__).resolve().parent
def h(p):return hashlib.sha256(p.read_bytes()).hexdigest()
m=json.loads((L/'final-manifest.json').read_text());expected={r['path'] for r in m['files']}
actual={str(p.relative_to(L)) for p in L.rglob('*') if p.is_file() and p.name not in m['excludes']};assert actual==expected
for r in m['files']:
 p=L/r['path'];assert p.stat().st_size==r['bytes'] and h(p)==r['sha256']
bound=json.loads((L/'bindings.json').read_text())['inputs'];n=0
for r in bound:
 if r['administrative']:
  assert h(L/r['copy'])==r['sha256'];continue
 assert h(Path(r['original']))==r['sha256'];n+=1
 if r.get('copy'):assert h(L/r['copy'])==r['sha256']
for r in json.loads((L/'transitive-selected-bindings.json').read_text()):
 assert h(Path(r['original']))==r['sha256'];n+=1
 if r.get('copy'):assert h(Path(r['copy']))==r['sha256']
a=[json.loads(x) for x in (L/'access.jsonl').read_text().splitlines()]
for r in a:
 if r.get('path'):assert h(L/r['path'])==r['sha256']
receipt={'verified_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'result':'PASS','manifest_sha256':h(L/'final-manifest.json'),'manifest_files':len(expected),'scientific_original_bindings_rechecked':n,'requests':len(a),'administrative':'snapshots checked, live originals intentionally not required unchanged','verification':'separate guarded execution after sealing; all outputs and inherited references checked','scope':'integrity only; no novelty clearance or acceptance'}
(L/'final-verification.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt))
