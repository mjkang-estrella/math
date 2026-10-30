from pathlib import Path
import hashlib,json,subprocess,sys
L=Path(__file__).resolve().parent
H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
manifest=json.loads((L/'manifest.json').read_text())
assert set(manifest['excluded'])=={'manifest.json','verification-receipt.json'}
actual={str(p.relative_to(L)) for p in L.rglob('*') if p.is_file()}-set(manifest['excluded'])
assert actual==set(manifest['files'])
for name,h in manifest['files'].items():assert H(L/name)==h,name
bindings=json.loads((L/'bindings.json').read_text())
for r in bindings:
    assert H(Path(r['original']))==r['sha256'],r['original']
    assert H(Path(r['copy']))==r['sha256'],r['copy']
refs=0
for fn in ['qualified-original-index.json','alias-refresh.json']:
    for r in json.loads((L/fn).read_text())['records']:
        assert H(Path(r['snapshot_reference']))==r['sha256'],r['snapshot_reference']
        # Historical originals may be mutable. They were refreshed at the recorded
        # time, but only their frozen snapshots are the historical evidence.
        refs+=1
for r in map(json.loads,(L/'http.jsonl').read_text().splitlines()):
    if 'sha256' in r:
        assert H(L/'sources'/r['name'])==r['sha256']
        assert H(L/'frozen'/r['name'])==r['sha256']
    if 'failure_sha256' in r:assert H(L/'failures'/(r['name']+'.body'))==r['failure_sha256']
for pdf in ['diversity','bcc','bcc-stability']:
    q=subprocess.run(['pdftotext','-layout',str(L/'frozen'/(pdf+'.pdf')),'-'],capture_output=True,check=True)
    assert q.stdout==(L/(pdf+'.txt')).read_bytes()
    assert q.stderr==(L/'receipts'/(pdf+'-extraction.stderr')).read_bytes()
q=subprocess.run([sys.executable,str(L/'checks.py')],capture_output=True,check=True)
assert q.stdout==(L/'receipts/checks.stdout').read_bytes()
assert q.stderr==(L/'receipts/checks.stderr').read_bytes()
import datetime
r={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'status':'PASS','manifest_sha256':H(L/'manifest.json'),'files':len(actual),'assigned_frozen_bindings':len(bindings),'historical_references':refs,'scientific_original_copy_hashes':True,'exact_replay':True,'exact_pdf_extraction_replay':True,'excluded':['manifest.json','verification-receipt.json'],'administrative_live_bindings':False}
(L/'verification-receipt.json').write_text(json.dumps(r,indent=2)+'\n')
print(json.dumps(r))
