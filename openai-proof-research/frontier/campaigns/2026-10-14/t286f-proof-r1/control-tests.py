#!/usr/bin/env python3
"""MIT. Reason-checked copied controls for the T286F proof-r1 review verifier.
Usage: control-tests.py EXTERNAL_MANIFEST_SHA256
All scratch copies live in a fresh directory under the system temp dir (never inside this
directory or any frozen packet) and are removed on exit. Output goes to stdout only.
Byte integrity only; not mathematical evidence.
"""
import hashlib,json,os,shutil,subprocess,sys,tempfile
from pathlib import Path

def run(d,anchor):
 c=subprocess.run([sys.executable,'-B',str(d/'verify.py'),anchor],capture_output=True,text=True,cwd='/')
 return {'returncode':c.returncode,'output':(c.stdout+c.stderr).strip()}
EXPECT={'payload':'file inventory mismatch','missing':'file inventory mismatch','extra_file':'file inventory mismatch',
 'extra_empty_directory':'directory inventory mismatch','root_symlink':'symlink ancestor','ancestor_symlink':'symlink ancestor',
 'hardlink':'hardlink:','fifo':'nonregular entry:','nested_manifest':'nested manifest',
 'self_reseal':'external manifest anchor mismatch','wrong_anchor':'external manifest anchor mismatch'}
def main(anchor):
 root=Path(os.path.abspath(__file__)).parent
 base=run(root,anchor)
 if base['returncode']!=0:raise SystemExit('baseline failed: '+base['output'])
 scratch=Path(tempfile.mkdtemp(prefix='t286f-proof-r1-controls-'))
 if root in scratch.parents or scratch==root:raise SystemExit('scratch inside review directory')
 cases={'canonical':base}
 try:
  for name in ['unchanged_copy',*EXPECT]:
   case=scratch/name;case.mkdir();copy=case/'review';shutil.copytree(root,copy,symlinks=True);target=copy;used=anchor
   if name=='payload':
    with (copy/'report.md').open('a') as f:f.write('\nmutation\n')
   elif name=='missing':(copy/'report.md').unlink()
   elif name=='extra_file':(copy/'extra').write_text('x')
   elif name=='extra_empty_directory':(copy/'extra-empty').mkdir()
   elif name=='root_symlink':target=case/'link';target.symlink_to(copy,target_is_directory=True)
   elif name=='ancestor_symlink':
    link=scratch/(name+'-ancestor');link.symlink_to(case,target_is_directory=True);target=link/'review'
   elif name=='hardlink':
    out=case/'outside';shutil.copyfile(copy/'report.md',out);(copy/'report.md').unlink();os.link(out,copy/'report.md')
   elif name=='fifo':os.mkfifo(copy/'pipe')
   elif name=='nested_manifest':(copy/'nested').mkdir();(copy/'nested/manifest.json').write_text('{}')
   elif name=='self_reseal':
    f=copy/'report.md';f.write_text(f.read_text()+'\nmutation\n');m=json.loads((copy/'manifest.json').read_text())
    m['files']['report.md']={'bytes':f.stat().st_size,'sha256':hashlib.sha256(f.read_bytes()).hexdigest()}
    (copy/'manifest.json').write_text(json.dumps(m,indent=2,sort_keys=True)+'\n')
   elif name=='wrong_anchor':used='0'*64
   r=run(target,used);cases[name]=r
   if name=='unchanged_copy':
    if r['returncode']!=0:raise SystemExit('unchanged copy rejected: '+r['output'])
   elif r['returncode']==0 or EXPECT[name] not in r['output']:raise SystemExit('control %s wrong result: %s'%(name,r['output']))
   shutil.rmtree(case)
  return {'status':'PASS_13_REVIEW_CONTROLS','anchor':anchor,'expected_reasons':EXPECT,'cases':cases,
   'limits':'Byte integrity only; not mathematical evidence. Scratch outside the review directory, removed.'}
 finally:shutil.rmtree(scratch,ignore_errors=True)
if __name__=='__main__':
 if len(sys.argv)!=2:raise SystemExit('usage: control-tests.py EXTERNAL_MANIFEST_SHA256')
 print(json.dumps(main(sys.argv[1]),indent=2))
