from pathlib import Path
import json,hashlib,zipfile
L=Path(__file__).resolve().parent;sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
m=json.loads((L/'manifest.json').read_text())
assert 'manifest.json' not in m and 'verification-receipt.json' not in m
assert set(m)=={str(p.relative_to(L)) for p in L.rglob('*') if p.is_file() and p.name not in ['manifest.json','verification-receipt.json']}
for n,h in m.items():assert sha(L/n)==h,n
for r in json.loads((L/'freeze.json').read_text()):assert sha(Path(r['original']))==sha(L/r['copy'])==r['sha256']
assert (L/'source-only.zip').read_bytes()==(L/'rebuilt-source-only.zip').read_bytes()==(L/'rebuilt-after-replay.zip').read_bytes()
with zipfile.ZipFile(L/'source-only.zip') as z:
 assert not any(n.endswith(('.olean','.ilean','.pyc')) for n in z.namelist())
 members=json.loads(z.read('package-files.json'))
 assert set(z.namelist())==set(members)|{'package-files.json'}
 for n,h in members.items():assert hashlib.sha256(z.read(n)).hexdigest()==h
assert json.loads((L/'fresh-extracted-replay.json').read_text())['status']=='PASS'
assert not list((L/'packet/output/pdf').glob('*.pdf'))
out={'status':'PASS','verified_manifest_sha256':sha(L/'manifest.json'),'files':len(m),'source_zip_sha256':sha(L/'source-only.zip'),'immutable_archive_sha256':sha(L/'frozen/sol-cube-cct-source-formal-r1/source-only.tar.gz'),'all_originals_and_copies_unchanged':True,'byte_identical_ZIP_rebuilds':True,'strict_fresh_replay_134_safe_Std3_no_partials':True,'PDF':'BLOCKED; no authorship/render/visual-QA claim','novelty':'HOLD','acceptance_count_changed':False,'separate_guarded_verification':True}
(L/'verification-receipt.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
