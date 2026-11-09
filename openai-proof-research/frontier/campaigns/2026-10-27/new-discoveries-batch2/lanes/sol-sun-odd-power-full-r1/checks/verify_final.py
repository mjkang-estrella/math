from pathlib import Path
import hashlib,json,datetime
p=Path(__file__).resolve().parents[1]
h=lambda f:hashlib.sha256(f.read_bytes()).hexdigest()
m=json.loads((p/'manifest.json').read_text());failures=[];checked=[]
assert set(m['excludes'])=={'manifest.json','verification-receipt.json'}
actual={str(f.relative_to(p)) for f in p.rglob('*') if f.is_file() and str(f.relative_to(p)) not in m['excludes']}
if actual!=set(m['files']):failures.append('manifest file set mismatch')
for name,expected in m['files'].items():
 if not (p/name).is_file() or h(p/name)!=expected:failures.append('manifest mismatch: '+name)
for name,key in [('freeze.json','scientific_inputs'),('retrieved-freeze.json','inputs')]:
 for row in json.loads((p/name).read_text())[key]:
  a,b=Path(row['original']),Path(row['copy']);ok=a.is_file() and b.is_file() and h(a)==row['sha256']==h(b)==row['copy_sha256']
  checked.append(dict(original=str(a),copy=str(b),ok=ok))
  if not ok:failures.append('frozen input mismatch: '+str(a))
result=dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),status='PASS' if not failures else 'FAIL',manifest_sha256=h(p/'manifest.json'),explicit_excludes=m['excludes'],manifest_files=len(m['files']),scientific_original_copy_pairs=checked,failures=failures,administrative='Stored snapshots only; live ledger/NEXT deliberately not bound as scientific inputs.',limit='File-integrity verification only, not mathematical certification or prior-art clearance.')
(p/'verification-receipt.json').write_text(json.dumps(result,indent=2));print(json.dumps({k:v for k,v in result.items() if k!='scientific_original_copy_pairs'},indent=2));assert not failures
