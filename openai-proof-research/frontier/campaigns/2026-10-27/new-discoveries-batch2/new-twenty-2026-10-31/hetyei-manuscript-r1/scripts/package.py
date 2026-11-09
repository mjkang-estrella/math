from pathlib import Path
import hashlib,json,zipfile
R=Path(__file__).resolve().parent.parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
# Packaging receipts are external to avoid a self-referential ZIP or manifest.
exclude={'MANIFEST.sha256','PAYLOAD-MANIFEST.sha256','full-dossier.zip','full-dossier.zip.sha256','logs/package.log','receipts/package.json','receipts/dossier-package-check.json','logs/seal.log','receipts/seal.json'}
files=[p for p in sorted(R.rglob('*')) if p.is_file() and str(p.relative_to(R)) not in exclude and not str(p.relative_to(R)).startswith('tmp/')]
(R/'PAYLOAD-MANIFEST.sha256').write_text(''.join(f'{sha(p)}  {p.relative_to(R)}\n' for p in files))
files.append(R/'PAYLOAD-MANIFEST.sha256')
with zipfile.ZipFile(R/'full-dossier.zip','w',compression=zipfile.ZIP_DEFLATED,compresslevel=6) as z:
 for p in files:z.write(p,str(p.relative_to(R)))
with zipfile.ZipFile(R/'full-dossier.zip') as z:
 assert z.testzip() is None
 for p in files:assert hashlib.sha256(z.read(str(p.relative_to(R)))).hexdigest()==sha(p)
report=dict(status='PASS',member_count=len(files),members_byte_identical=True,crc_test=True,archive_sha256=sha(R/'full-dossier.zip'),packet_sha256=sha(R/'source-only.zip'),excluded_external_receipts=sorted(exclude),archive_executed=False)
(R/'receipts/dossier-package-check.json').write_text(json.dumps(report,indent=2)+'\n')
(R/'full-dossier.zip.sha256').write_text(f'{sha(R/"full-dossier.zip")}  full-dossier.zip\n')
print(json.dumps(report,indent=2))
