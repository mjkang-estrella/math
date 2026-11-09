from pathlib import Path
import hashlib,zipfile,json
r=Path.cwd();H=lambda f:hashlib.sha256(f.read_bytes()).hexdigest()
assert json.loads((r/'receipts/input-hashes-before.json').read_text())==json.loads((r/'receipts/input-hashes-after.json').read_text())
assert H(r/'lean-source.zip')=='82262a7aa3f6548ebe9e15c3d8f0fef0feb120c5f0f45cc4a6e31eb6a3840a75'
assert H(r/'lean-source.zip')==H(r/'inputs/rlmexc-formal-r1/source.zip')
assert json.loads((r/'receipts/visual-qa.json').read_text())['pdf_sha256']==H(r/'manuscript.pdf')
# No self-referential hashes; package-driver receipt is created after return.
excluded={'MANIFEST.sha256','archives.sha256','paper-source.zip','full-dossier.zip','receipts/cap-package.json'}
files=sorted(f for f in r.rglob('*') if f.is_file() and str(f.relative_to(r)) not in excluded and 'tmp' not in f.relative_to(r).parts)
(r/'MANIFEST.sha256').write_text(''.join(f'{H(f)}  {f.relative_to(r)}\n' for f in files))
source=[r/'manuscript.xml',r/'manuscript-text.md',r/'scripts/build_pdf.py',r/'scripts/recompute.py',r/'scripts/cap.py',r/'REPRODUCE.md']+sorted((r/'outputs').glob('*.json'))
with zipfile.ZipFile(r/'paper-source.zip','w',zipfile.ZIP_DEFLATED) as z:
 for f in source:z.write(f,str(f.relative_to(r)))
with zipfile.ZipFile(r/'full-dossier.zip','w',zipfile.ZIP_DEFLATED) as z:
 for f in files+[r/'MANIFEST.sha256',r/'paper-source.zip']:z.write(f,str(f.relative_to(r)))
for name in ['paper-source.zip','full-dossier.zip']:
 with zipfile.ZipFile(r/name) as z:assert z.testzip() is None
(r/'archives.sha256').write_text(''.join(f'{H(r/name)}  {name}\n' for name in ['paper-source.zip','full-dossier.zip']))
print('Manifest:',len(files),'files; both ZIP CRC tests PASS; frozen inputs and Lean hash PASS')
