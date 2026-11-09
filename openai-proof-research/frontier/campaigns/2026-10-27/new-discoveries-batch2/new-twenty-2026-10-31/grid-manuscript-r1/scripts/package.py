from pathlib import Path,PurePosixPath
import json,hashlib,zipfile,datetime,os
D=Path.cwd(); sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
# Rebind final supplied snapshot; no writes to upstream files.
b=json.loads((D/'hashes/inputs-before.json').read_text()); a={p:sha(Path(p)) for p in b}; changes=[p for p in b if a[p]!=b[p]]
assert all(p.endswith('/grid-fidelity-r1/REVIEW.md') for p in changes)
for p,h in json.loads((D/'hashes/optional-final-before.json').read_text()).items(): assert sha(Path(p))==h,'Active review changed again; reconcile before delivery'
(D/'hashes/optional-final-after.json').write_text((D/'hashes/optional-final-before.json').read_text())
(D/'hashes/inputs-after.json').write_text(json.dumps(a,indent=2)+'\n')
assert not (D.parent/'grid-fidelity-r1/review.json').exists(),'Read newly arrived final fidelity record'

for p,h in json.loads((D/'hashes/root-late-before.json').read_text()).items(): assert sha(Path(p))==h, 'Root receipt updated: read new version'
(D/'hashes/root-late-after.json').write_text((D/'hashes/root-late-before.json').read_text())
assert sha(D/'grid-formal-r6-source.zip')=='a4068de99037028f817f2f5d1652a97d7508c4419353da95abea04b45b977953'
with zipfile.ZipFile(D/'grid-formal-r6-source.zip') as f: assert not any(Path(n).suffix in ['.olean','.ilean','.so','.o'] for n in f.namelist())
assert json.loads((D/'qa/receipt.json').read_text())['pdf_sha256']==sha(D/'paper.pdf')
for p,h in json.loads((D/'qa/receipt.json').read_text())['images_sha256'].items(): assert sha(D/p)==h
exclude={'DOSSIER-MANIFEST.json','DELIVERY-SHA256.json','package-validation.json','grid-full-dossier.zip'}
files=[p for p in sorted(D.rglob('*')) if p.is_file() and p.relative_to(D).parts[0] not in ['source-extraction','tmp'] and p.name not in exclude]
manifest={str(p.relative_to(D)):{'bytes':p.stat().st_size,'sha256':sha(p)} for p in files}
(D/'DOSSIER-MANIFEST.json').write_text(json.dumps({'note':'Manifest excludes itself and post-package delivery/validation/completion receipts; source-extraction and tmp are redundant intermediates.','files':manifest},indent=2)+'\n')
z=D/'grid-full-dossier.zip'
with zipfile.ZipFile(z,'w',zipfile.ZIP_DEFLATED,compresslevel=6) as f:
 for p in files+[D/'DOSSIER-MANIFEST.json']: f.write(p,p.relative_to(D))
with zipfile.ZipFile(z) as f:
 assert f.testzip() is None
 for n in f.namelist():
  q=PurePosixPath(n); assert not q.is_absolute() and '..' not in q.parts
 for n,v in manifest.items(): assert hashlib.sha256(f.read(n)).hexdigest()==v['sha256']
(D/'package-validation.json').write_text(json.dumps({'crc':'PASS','all_member_hashes':'PASS','safe_relative_names':'PASS','members':len(manifest)+1,'zip_bytes':z.stat().st_size,'no_lean_run':True},indent=2)+'\n')
(D/'DELIVERY-SHA256.json').write_text(json.dumps({n:{'sha256':sha(D/n),'bytes':(D/n).stat().st_size} for n in ['paper.pdf','paper.md','grid-formal-r6-source.zip','grid-full-dossier.zip','DOSSIER-MANIFEST.json']},indent=2)+'\n')
print('Packaged and verified',len(manifest)+1,'members;',z.stat().st_size,'bytes')
