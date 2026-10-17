#!/usr/bin/env python3
"""Independent actual verifier controls, confined to reviewer copies. MIT."""
from pathlib import Path
import hashlib,json,subprocess,sys,tempfile,shutil
R=Path(__file__).resolve().parent; P=R.parent/'o217-manuscript-r1'
ANCHOR='d698c8aaa65a2c3cce67b5824e15d9ef85c5f5c29ab6a70194faecd8ca9f506b'
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def snapshot(p): return {str(f.relative_to(p)):sha(f) for f in p.rglob('*') if f.is_file()}
before=snapshot(P); rows=[]
with tempfile.TemporaryDirectory(prefix='.integrity-',dir=R) as td:
 f=Path(td)/'packet'; shutil.copytree(P,f)
 def check(name,anchor,want):
  p=subprocess.run([sys.executable,'-B',str(P/'verify.py'),'--root',str(f),'--anchor',anchor],capture_output=True,text=True)
  assert (p.returncode==0)==want,(name,p.stdout,p.stderr)
  rows.append({'name':name,'exit_code':p.returncode,'stdout':p.stdout,'stderr':p.stderr})
 check('exact-copy',ANCHOR,True); check('wrong-anchor','0'*64,False)
 s=f/'main.tex'; raw=s.read_bytes(); s.write_bytes(raw+b'\n% tampered\n'); check('source-tamper',ANCHOR,False); s.write_bytes(raw)
 s.unlink(); check('missing-source',ANCHOR,False); s.write_bytes(raw)
 (f/'extra.txt').write_text('extra'); check('extra-file',ANCHOR,False); (f/'extra.txt').unlink()
 (f/'extra-dir').mkdir(); check('extra-directory',ANCHOR,False); (f/'extra-dir').rmdir()
 s.unlink(); s.symlink_to(P/'main.tex'); check('symlink',ANCHOR,False); s.unlink(); s.write_bytes(raw)
 pdf=f/'output/pdf/fourth-moment-sk-comparison.pdf'; pdfraw=pdf.read_bytes(); pdf.write_bytes(pdfraw+b'\nchanged'); check('pdf-tamper',ANCHOR,False)
 mp=f/'output-manifest.json'; mraw=mp.read_bytes(); m=json.loads(mraw)
 for row in m['files']:
  if row['path']==str(pdf.relative_to(f)): row.update(sha256=sha(pdf),bytes=pdf.stat().st_size)
 mp.write_text(json.dumps(m,indent=2)+'\n'); check('reanchored-pdf-stale-QA',sha(mp),False)
 mp.write_bytes(mraw); pdf.write_bytes(pdfraw); check('restored-copy',ANCHOR,True)
assert before==snapshot(P)
(R/'evidence/integrity-controls.json').write_text(json.dumps({'result':'PASS_INTEGRITY_ONLY','original_unchanged':True,'rows':rows,'original_inventory':before},indent=2)+'\n')
print('Actual manuscript verifier: 2 positive and 8 negative controls passed; original unchanged')
