from pathlib import Path
import json,hashlib,zipfile,re,stat
R=Path(__file__).resolve().parent.parent
h=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for before,after in [('inputs-before.json','inputs-after.json'),('inputs-parent-before.json','inputs-parent-after.json')]:
 manifest=json.loads((R/before).read_text());out={};changed=[]
 for name,entry in manifest.items():
  f=Path(name);out[name]={'sha256':h(f),'bytes':f.stat().st_size}
  if out[name]!=entry:changed.append(name)
 assert not changed,changed
 (R/after).write_text(json.dumps(out,indent=2)+'\n')
# Copies, too, must match the before hashes.
for key in ['inputs-before.json','inputs-parent-before.json']:
 for name,entry in json.loads((R/key).read_text()).items():
  orig=Path(name)
  if orig.is_relative_to(R.parent):dest=R/'evidence'/orig.relative_to(R.parent)
  else:dest=R/'evidence/instructions'/orig.parent.name/orig.name
  assert h(dest)==entry['sha256'],str(dest)
assert h(R/'source-only.zip')=='82e134f245cd795d51695f1a1be8a15b4167212ff4742d18f2a2f0c5ce7ac0c2'
imgs=sorted((R/'qa').glob('page-*.png'));assert len(imgs)==6
(R/'qa/receipt.json').write_text(json.dumps({'paper_sha256':h(R/'paper.pdf'),'pages':6,'render':'pdftoppm -r 110 -png','visual_inspection':'All six final page PNGs viewed individually via view_image. Checked readable prose, no clipping, no overlap, row table, generator list, formulas, draft status, retention caveat and bibliography. Earlier heading/subscript defects corrected before this receipt.','images':{p.name:h(p) for p in imgs}},indent=2)+'\n')
(R/'receipts/input-integrity.json').write_text(json.dumps({'originals_unchanged':True,'copies_identical':True,'primary_input_count':len(json.loads((R/'inputs-before.json').read_text())),'late_parent_receipts':2,'lean_packet_identical':True},indent=2)+'\n')
exclude={'MANIFEST.sha256','full-dossier.zip','full-dossier.zip.sha256','receipts/package-final.json','receipts/archive-verification.json'}
files=[p for p in R.rglob('*') if p.is_file() and str(p.relative_to(R)) not in exclude and 'tmp' not in p.relative_to(R).parts]
(R/'MANIFEST.sha256').write_text(''.join(h(p)+'  '+str(p.relative_to(R))+'\n' for p in sorted(files)))
with zipfile.ZipFile(R/'full-dossier.zip','w',zipfile.ZIP_DEFLATED,compresslevel=6) as z:
 for p in sorted(files+[R/'MANIFEST.sha256']):z.write(p,str(p.relative_to(R)))
(R/'full-dossier.zip.sha256').write_text(h(R/'full-dossier.zip')+'  full-dossier.zip\n')
with zipfile.ZipFile(R/'full-dossier.zip') as z:
 assert z.testzip() is None
 for name in z.namelist():
  p=Path(name);assert not p.is_absolute() and '..' not in p.parts
 for line in z.read('MANIFEST.sha256').decode().splitlines():
  digest,name=line.split('  ',1);assert hashlib.sha256(z.read(name)).hexdigest()==digest
 assert z.read('source-only.zip')==(R/'source-only.zip').read_bytes()
(R/'receipts/archive-verification.json').write_text(json.dumps({'zip_integrity':'PASS','manifest_content_hashes':'PASS','safe_member_paths':True,'byte_identical_packet_inside_archive':True,'sha256':h(R/'full-dossier.zip'),'manifest_exclusions':sorted(exclude),'note':'Outer hash and final packaging/verification receipts are separate sidecars to avoid self-reference.'},indent=2)+'\n')
print(json.dumps({'dossier_bytes':(R/'full-dossier.zip').stat().st_size,'dossier_sha256':h(R/'full-dossier.zip'),'manifest_files':len(files),'frozen_inputs_unchanged':True}))
