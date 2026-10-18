#!/usr/bin/env python3
"""MIT. Adapted from author r39 controls. Adversarial copied controls, with exact failure-reason checks.
The scratch directory is created inside the author's packet and removed before
return; the canonical baseline is checked before creation. Output stays external.
"""
import hashlib,json,os,shutil,subprocess,sys,tempfile
from pathlib import Path

def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def run(p,anchor):
 c=subprocess.run([sys.executable,str(p/'verify.py'),anchor],capture_output=True,text=True)
 return {'returncode':c.returncode,'output':(c.stdout+c.stderr).strip()}
def main(anchor):
 root=Path(os.path.abspath(__file__)).parent;baseline=run(root,anchor);assert baseline['returncode']==0,baseline
 scratch=Path(tempfile.mkdtemp(prefix='.control-scratch-',dir=root));cases={'canonical':baseline}
 expected={'payload':'file inventory mismatch','missing':'file inventory mismatch','extra_file':'file inventory mismatch','extra_empty_directory':'directory inventory mismatch','root_symlink':'symlink ancestor','ancestor_symlink':'symlink ancestor','hardlink':'hardlink:','fifo':'nonregular entry:','nested_manifest':'nested manifest','self_reseal':'external manifest anchor mismatch','wrong_anchor':'external manifest anchor mismatch'}
 try:
  for name in ['unchanged_copy',*expected]:
   case=scratch/name;case.mkdir();copy=case/'packet';shutil.copytree(root,copy,ignore=shutil.ignore_patterns('.control-scratch-*'));target=copy;used=anchor
   if name=='payload':
    with (copy/'shifted-product108-work.md').open('a') as f:f.write('\nmutation\n')
   elif name=='missing':(copy/'shifted-product108-work.md').unlink()
   elif name=='extra_file':(copy/'extra').write_text('x')
   elif name=='extra_empty_directory':(copy/'extra-empty').mkdir()
   elif name=='root_symlink':target=case/'link';target.symlink_to(copy,target_is_directory=True)
   elif name=='ancestor_symlink':
    link=scratch/(name+'-ancestor');link.symlink_to(case,target_is_directory=True);target=link/'packet'
   elif name=='hardlink':
    outside=case/'outside';shutil.copyfile(copy/'shifted-product108-work.md',outside);(copy/'shifted-product108-work.md').unlink();os.link(outside,copy/'shifted-product108-work.md')
   elif name=='fifo':os.mkfifo(copy/'pipe')
   elif name=='nested_manifest':(copy/'nested').mkdir();(copy/'nested/manifest.json').write_text('{}')
   elif name=='self_reseal':
    f=copy/'shifted-product108-work.md';f.write_text(f.read_text()+'\nmutation\n');m=json.loads((copy/'manifest.json').read_text());m['files']['shifted-product108-work.md']={'bytes':f.stat().st_size,'sha256':digest(f)};(copy/'manifest.json').write_text(json.dumps(m,indent=2,sort_keys=True)+'\n')
   elif name=='wrong_anchor':used='0'*64
   result=run(target,used);cases[name]=result
   if name=='unchanged_copy':assert result['returncode']==0,result
   else:assert result['returncode']!=0 and expected[name] in result['output'],(name,result)
   shutil.rmtree(case)
  return {'status':'PASS_13_INVENTORY_CONTROLS','baseline_manifest_sha256':anchor,'cases':cases,'limits':'Byte integrity only; no mathematical or contribution gate. Output external to the sealed packet.'}
 finally:shutil.rmtree(scratch)
if __name__=='__main__':
 if len(sys.argv)!=2:raise SystemExit('usage: control-tests.py EXTERNAL_MANIFEST_SHA256')
 print(json.dumps(main(sys.argv[1]),indent=2))
