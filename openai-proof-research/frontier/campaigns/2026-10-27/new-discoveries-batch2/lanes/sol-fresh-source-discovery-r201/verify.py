from pathlib import Path
import json,hashlib,datetime
L=Path(__file__).resolve().parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
fail=[]; changed=[]
for x in json.loads((L/'primary-freeze.json').read_text()):
    if not sha(Path(x['original']))==sha(L/x['copy'])==x['sha256']:fail.append(x)
rows=json.loads((L/'history-receipt.json').read_text())['records']
for x in rows:
    if sha(L/x['copy'])!=x['sha256']:fail.append(x)
    p=Path(x['original'])
    if not p.exists() or sha(p)!=x['sha256']:changed.append(x['original'])
m=json.loads((L/'finalmanifest.json').read_text());assert set(m['explicit_exclusions'])=={'finalmanifest.json','verification-receipt.json'}
for x in m['files']:
    p=L/x['path']
    if not p.exists() or sha(p)!=x['sha256'] or p.stat().st_size!=x['bytes']:fail.append(x['path'])
listed={x['path'] for x in m['files']}
actual={str(p.relative_to(L)) for p in L.rglob('*') if p.is_file()}-set(m['explicit_exclusions'])
if listed!=actual:fail.append('manifest file set mismatch')
receipt=dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),status='PASS' if not fail else 'FAIL',scientific_original_copy_files=len(json.loads((L/'primary-freeze.json').read_text())),report_snapshot_copies=len(rows),live_mutable_report_changes=changed,manifest_files=len(m['files']),manifest_sha256=sha(L/'finalmanifest.json'),failures=fail,scope='Separate guarded verification after final writes; mutable report changes are not immutable-source failures; no retroactive first-read certification for administrative/report reads.')
(L/'verification-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt));assert not fail
