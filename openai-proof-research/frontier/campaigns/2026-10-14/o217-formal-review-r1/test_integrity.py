#!/usr/bin/env python3
"""Independent controls of sealed author's actual verifier. MIT."""
from pathlib import Path
import hashlib,json,subprocess,sys,tempfile,shutil
R=Path(__file__).resolve().parent; P=R.parent/'o217-formal-v1'; E=R/'evidence'
ANCHOR='121cf88cc61d36d24edeb89f011a1fa2d405292ae389d03f91e3f5aee6a568ce'
def snapshot(p):
 return {f.relative_to(p).as_posix():hashlib.sha256(f.read_bytes()).hexdigest() for f in p.rglob('*') if f.is_file()}
before=snapshot(P); rows=[]
with tempfile.TemporaryDirectory(prefix='.integrity-',dir=R) as td:
 f=Path(td)/'packet'; shutil.copytree(P,f)
 def check(name,anchor,want):
  p=subprocess.run([sys.executable,'-B',str(P/'verify.py'),'--root',str(f),'--anchor',anchor],capture_output=True,text=True)
  assert (p.returncode==0)==want,(name,p.stdout,p.stderr)
  rows.append({'name':name,'exit_code':p.returncode,'stdout':p.stdout,'stderr':p.stderr})
 check('exact-sealed-copy',ANCHOR,True)
 check('wrong-anchor','0'*64,False)
 s=f/'O217.lean'; raw=s.read_bytes()
 s.write_bytes(raw+b'\n-- independent tamper\n'); check('source-tamper',ANCHOR,False); s.write_bytes(raw)
 s.unlink(); check('missing-source',ANCHOR,False); s.write_bytes(raw)
 (f/'extra.txt').write_text('extra'); check('extra-file',ANCHOR,False); (f/'extra.txt').unlink()
 (f/'extra-dir').mkdir(); check('extra-empty-directory',ANCHOR,False); (f/'extra-dir').rmdir()
 s.unlink(); s.symlink_to(P/'O217.lean'); check('symlink-source',ANCHOR,False); s.unlink(); s.write_bytes(raw)
 m=f/'output-manifest.json'; mraw=m.read_bytes(); m.write_bytes(mraw+b' '); check('manifest-tamper',ANCHOR,False); m.write_bytes(mraw)
 check('restored-exact-copy',ANCHOR,True)
assert before==snapshot(P)
(E/'integrity-controls.json').write_text(json.dumps({'result':'PASS_INTEGRITY_ONLY','rows':rows,'sealed_author_unchanged':True,'author_inventory':before},indent=2)+'\n')
print('Independent actual verifier: 2 positive, 7 negative controls passed; author bytes unchanged')
