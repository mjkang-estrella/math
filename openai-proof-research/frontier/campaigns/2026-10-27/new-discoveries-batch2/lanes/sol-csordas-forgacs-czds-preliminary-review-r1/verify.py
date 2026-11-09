from pathlib import Path
import json,hashlib,datetime
L=Path(__file__).resolve().parent
def h(p):return hashlib.sha256(p.read_bytes()).hexdigest()
m=json.loads((L/'MANIFEST.json').read_text());b=json.loads((L/'bindings.json').read_text())
actual={str(p.relative_to(L)) for p in L.rglob('*') if p.is_file() and p.name not in m['excludes']}
assert actual==set(m['files'])
for name,v in m['files'].items():
 p=L/name;assert h(p)==v['sha256'] and p.stat().st_size==v['bytes'],name
for row in b:
 assert h(L/row['copy'])==row['sha256'],row['copy']
 if row['kind']=='scientific':assert h(Path(row['original']))==row['sha256'],row['original']
assert json.loads((L/'exact-evidence.json').read_text())['pass']
assert json.loads((L/'determinant-evidence.json').read_text())['new_determinant_negative']
r={'verified_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'pass':True,'manifest_sha256':h(L/'MANIFEST.json'),'manifest_files_verified':len(actual),'scientific_originals_and_copies_verified':sum(x['kind']=='scientific' for x in b),'administrative_snapshots_only':True,'verification':'separate guarded invocation after final writes; no scientific rerun or checker import'}
(L/'verification-receipt.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r,indent=2))
