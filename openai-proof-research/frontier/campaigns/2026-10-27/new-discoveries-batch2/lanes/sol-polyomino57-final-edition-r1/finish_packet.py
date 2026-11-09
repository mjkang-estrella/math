from pathlib import Path
import json,zipfile,hashlib,difflib,shutil
L=Path('source');old=zipfile.ZipFile('frozen-input.zip')
p=L/'FINAL-EDITION-NOTES.md';p.write_text(p.read_text()+"\nThe manuscript-comparison helper initially expected eight changed paragraphs but observed seven and failed closed. Its expected index set was corrected to the seven actual status/provenance paragraphs; no mathematical text was changed to pass this check. The original venv's relative executable path emitted prefix warnings; later invocations use its absolute path.\n")
shutil.copyfile('CONTENT-IDENTITY.json',L/'CONTENT-IDENTITY.json')
changes=[];diff=[]
for n in old.namelist():
 b=(L/n).read_bytes()
 if b!=old.read(n):
  changes.append(dict(path=n,before_sha256=hashlib.sha256(old.read(n)).hexdigest(),after_sha256=hashlib.sha256(b).hexdigest()))
  if n.endswith(('.txt','.md','.py','.json')):diff.extend(difflib.unified_diff(old.read(n).decode().splitlines(True),b.decode().splitlines(True),fromfile='frozen/'+n,tofile='final/'+n))
assert {v['path'] for v in changes}=={'paper.txt','paper.pdf','README.md','PROVENANCE.json','QA.json','build_pdf.py','verify_packet.py'}
added=[str(p.relative_to(L)) for p in L.rglob('*') if p.is_file() and str(p.relative_to(L)) not in old.namelist()]
assert len(added)==23
Path('EDIT-REPORT.diff').write_text(''.join(diff));Path('EDIT-REPORT.json').write_text(json.dumps(dict(changed=changes,generated_manifest='MANIFEST.json regenerated after report',added=sorted(added),deleted=[],proof_edits=False,authorship_edits=False),indent=2)+'\n')
Path('output/pdf').mkdir(parents=True,exist_ok=True);shutil.copyfile(L/'paper.pdf','output/pdf/polyomino57-final-edition.pdf')
