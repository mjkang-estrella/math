#!/usr/bin/env python3
# Copyright 2026 Myeongjin Kang. SPDX-License-Identifier: MIT
"""Exercise this packet's read-only verifier on isolated copies before final seal.
The resulting record is added before resealing; no mathematical claim is tested.
"""
import hashlib, json, shutil, subprocess, sys
from pathlib import Path
ROOT=Path(__file__).absolute().parents[1]
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def run(root,anchor):
 p=subprocess.run([sys.executable,'-B',str(root/'support/verify.py'),'--anchor',anchor],capture_output=True,text=True)
 return {'exit_code':p.returncode,'stdout':p.stdout.strip(),'stderr':p.stderr.strip()}
def main():
 anchor=sha(ROOT/'manifest.json')
 before={p.relative_to(ROOT).as_posix():sha(p) for p in ROOT.rglob('*') if p.is_file()}
 positive=run(ROOT,anchor)
 assert positive['exit_code']==0,positive
 after={p.relative_to(ROOT).as_posix():sha(p) for p in ROOT.rglob('*') if p.is_file()}
 assert before==after,'positive verifier wrote files'
 wrong=run(ROOT,'0'*64)
 assert wrong['exit_code']!=0 and 'external anchor mismatch' in wrong['stderr'],wrong
 work=ROOT/'.integrity-controls'
 assert not work.exists()
 work.mkdir()
 rows=[{'case':'unaltered','outcome':positive},{'case':'wrong external anchor','outcome':wrong}]
 try:
  for kind in ['changed payload','extra payload','symlink']:
   copy=work/kind.replace(' ','-')
   copy.mkdir()
   for child in ROOT.iterdir():
    if child==work: continue
    dest=copy/child.name
    if child.is_dir(): shutil.copytree(child,dest)
    else: shutil.copyfile(child,dest)
   if kind=='changed payload':
    with (copy/'main.tex').open('a') as f: f.write('\n% changed control\n')
   elif kind=='extra payload': (copy/'unexpected.txt').write_text('extra')
   else: (copy/'unexpected-link').symlink_to('main.tex')
   result=run(copy,anchor)
   assert result['exit_code']!=0,result
   expected={'changed payload':'payload: main.tex','extra payload':'file membership','symlink':'symlink'}[kind]
   assert expected in result['stderr'],result
   rows.append({'case':kind,'outcome':result})
   shutil.rmtree(copy)
 finally: shutil.rmtree(work)
 (ROOT/'checks/integrity-controls.json').write_text(json.dumps({'result':'PASS_INTEGRITY_CONTROLS_ONLY','preseal_anchor_tested':anchor,'positive_verifier_changed_no_file_bytes':True,'rows':rows,'limits':'Copies only; does not establish mathematical correctness. Final manifest is regenerated after this receipt is added.'},indent=2)+'\n')
 print('PASS_INTEGRITY_CONTROLS_ONLY')
if __name__=='__main__':main()
