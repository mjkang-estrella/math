"""Read-only strict membership/provenance verifier. Expected manifest hash is external."""
from pathlib import Path
import sys,hashlib,json,subprocess
root=Path(__file__).resolve().parent
if len(sys.argv)!=2 or len(sys.argv[1])!=64:raise SystemExit('usage: python -B verify.py EXPECTED_MANIFEST_SHA256')
def h(b):return hashlib.sha256(b).hexdigest()
raw=(root/'manifest.json').read_bytes()
assert h(raw)==sys.argv[1], 'external manifest hash mismatch'
m=json.loads(raw)
files={str(p.relative_to(root)) for p in root.rglob('*') if p.is_file()}
dirs={str(p.relative_to(root)) for p in root.rglob('*') if p.is_dir()}
assert not any(p.is_symlink() for p in root.rglob('*'))
assert files==set(m['files'])|{'manifest.json'},'strict file membership mismatch'
assert dirs==set(m['directories']),'strict directory membership mismatch'
for n,v in m['files'].items():
 b=(root/n).read_bytes();assert len(b)==v['bytes'] and h(b)==v['sha256'],n
canon=root/'private/context/sources__preprints-tree.json'
assert h(canon.read_bytes())=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
tree=json.loads(canon.read_text());assert tree.get('truncated') is False
entries=tree['tree'];by={e['path']:e for e in entries}
inv=json.loads((root/'inventory172.json').read_text())
pre='preprints/A-classification-of-finite-Euclidean-Ramsey-configurations-September-23-2026/'
assert inv==[e for e in entries if e['path'].startswith(pre) and e['type']=='blob']
receipts=json.loads((root/'receipts172.json').read_text())
assert {r['path'].removeprefix('private/') for r in receipts}=={e['path'] for e in inv if not e['path'].endswith('.pdf')}
for r in receipts:
 b=(root/r['path']).read_bytes();git=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
 assert h(b)==r['sha256'] and git==r['git_blob']==by[r['path'].removeprefix('private/')]['sha']
assert h((root/'frozen-scope.md').read_bytes())=='fb60279345c90bfc1cdeab3783106c9d6fb5dbc21011e6d7945e51e6e508fbc8'
r=subprocess.run([sys.executable,'-B',str(root/'check_algebra.py')],capture_output=True,text=True,check=True)
assert json.loads(r.stdout)==json.loads((root/'check-results.json').read_text())
print(json.dumps({'status':'PASS','files':len(files),'directories':len(dirs),'source_blobs':len(receipts),'canonical_entries':len(entries),'algebra':json.loads(r.stdout),'disposition':'TECHNICAL ONLY; no nomination/count change'},indent=2))
