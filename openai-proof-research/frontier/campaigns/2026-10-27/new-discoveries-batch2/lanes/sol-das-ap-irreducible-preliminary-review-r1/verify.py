"""Run separately after the final manifest is written, always via helper_guard.py."""
from pathlib import Path
import hashlib,json,datetime,subprocess,sys
p=Path(__file__).resolve().parent
h=lambda f:hashlib.sha256(f.read_bytes()).hexdigest()
m=json.loads((p/'manifest.json').read_text())
actual={str(f.relative_to(p)) for f in p.rglob('*') if f.is_file() and f.name not in ['manifest.json','receipt.json']}
assert actual==set(m['files'])
for name,digest in m['files'].items():assert h(p/name)==digest,name
freeze=json.loads((p/'freeze.json').read_text())
for row in freeze['scientific']:
    assert h(Path(row['original']))==h(p/row['copy'])==row['sha256'],row['copy']
requests=[json.loads(s) for s in (p/'retrieval/http.jsonl').read_text().splitlines()]
for row in requests:
    assert h(p/'retrieval/original'/row['name'])==h(p/'retrieval/frozen'/row['name'])==row['sha256']
subprocess.run([sys.executable,str(p/'check.py')],check=True)
for name,digest in m['files'].items():assert h(p/name)==digest,name
receipt={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'status':'PASS',
         'manifest_sha256':h(p/'manifest.json'),'manifest_files':len(actual),
         'scientific_pairs':len(freeze['scientific']),'new_response_pairs':len(requests),
         'independent_checker':'PASS rerun; n5 all deletions, n4..40 and cuts',
         'counts':'9 additional / 39 total / next40, unchanged',
         'limitations':'Preliminary review only; journal/novelty holds; no Lean or manuscript'}
(p/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt))
