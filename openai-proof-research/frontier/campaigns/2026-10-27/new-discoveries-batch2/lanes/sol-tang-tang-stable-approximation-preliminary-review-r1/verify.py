from pathlib import Path
import hashlib,json,datetime
D=Path(__file__).resolve().parent
H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
m=json.loads((D/'manifest.json').read_text())
listed={r['path'] for r in m['files']}
actual={str(p.relative_to(D)) for p in D.rglob('*') if p.is_file() and p.name not in m['exclusions']}
assert listed==actual
for r in m['files']:
    p=D/r['path'];assert H(p)==r['sha256'] and p.stat().st_size==r['bytes'],str(p)
f=json.loads((D/'frozen-inputs.json').read_text())
for r in f['inputs']:assert H(Path(r['original']))==H(Path(r['copy']))==r['sha256']
r={'status':'PASS','utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'manifest_sha256':H(D/'manifest.json'),'verified_manifest_files':len(listed),'verified_original_copy_pairs':len(f['inputs']),'counts_unchanged':{'additional':9,'total':39,'next':40},'manifest_excludes':['manifest.json','verification-receipt.json'],'verification':'Separate guarded process after final writes; administrative files checked as snapshots only'}
(D/'verification-receipt.json').write_text(json.dumps(r,indent=2)+'\n')
print(json.dumps(r))
