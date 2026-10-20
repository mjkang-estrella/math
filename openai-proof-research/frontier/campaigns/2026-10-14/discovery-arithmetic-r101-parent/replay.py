#!/usr/bin/env python3
"""Parent artifact and finite diagnostic replay. No mathematical gate."""
import hashlib, json, shutil, stat, subprocess, sys, tempfile
from pathlib import Path
sys.dont_write_bytecode=True
HERE=Path(__file__).resolve().parent
PROJECT=HERE.parents[3]
ROOT=HERE.parent/'fresh-arithmetic-discovery-r101'
ANCHORS={'final':'4020f7e2ad852940ada2fbbd3016931069a591f3bd5b4b401d65188b1ec51563','manifest':'dce7b113094cf321d71ae269743d5f3592efb2acf857f8dd0233f754ecd8eb47','report':'bf6be5afee930ce2d0eede3c61986d6cfa95bbd433eb04ec564bd1fd4cb95a4b'}
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def file_record(p):
 s=p.lstat();assert stat.S_ISREG(s.st_mode)
 return {'type':stat.S_IFMT(s.st_mode),'mode':stat.S_IMODE(s.st_mode),'bytes':s.st_size,'sha256':sha(p),'nlink':s.st_nlink}
def snap(root):
 out={}
 for p in [root,*root.rglob('*')]:
  s=p.lstat();x={'mode':stat.S_IMODE(s.st_mode),'type':stat.S_IFMT(s.st_mode)}
  if p.is_symlink():x['target']=str(p.readlink())
  elif p.is_file():x.update(bytes=s.st_size,sha256=sha(p),nlink=s.st_nlink)
  out[str(p.relative_to(root))]=x
 return out
def run(args,expected=0):
 p=subprocess.run(args,text=True,capture_output=True)
 assert p.returncode==expected,(args,p.returncode,p.stderr)
 return {'exit':p.returncode,'stdout':p.stdout,'stderr':p.stderr}
def main():
 before=snap(ROOT)
 for name,key in [('FINAL.json','final'),('packet/MANIFEST.json','manifest'),('REPORT.md','report')]:assert sha(ROOT/name)==ANCHORS[key]
 assert sha(ROOT/'integrity-results.json')=='47a93b1a827939bb9e41a782066fc6f78845d56a2d25ee4807d9b8f4a9fdf1f7'
 originals=json.loads((ROOT/'packet/private/originals-before.json').read_text())
 bindings={z['path']:file_record(PROJECT/z['path']) for z in originals}
 # For each named original, compare its current hash/copy before and after replay.
 for z in originals:assert sha(PROJECT/z['path'])==z['sha256']
 result={'kind':'PARENT_ARTIFACT_INTAKE_NO_CORRECTNESS_OR_CONTRIBUTION_GATE','anchors':ANCHORS}
 with tempfile.TemporaryDirectory(prefix='replay-',dir=HERE) as td:
  copy=Path(td)/'author';copy.mkdir()
  for name in ['packet','notes']:shutil.copytree(ROOT/name,copy/name)
  for name in ['FINAL.json','REPORT.md']:shutil.copy2(ROOT/name,copy/name)
  args=['--root',str(copy),'--project',str(PROJECT)]
  for name,h in ANCHORS.items():args+=['--'+name+'-sha256',h]
  result['copied_control_replay']=run([sys.executable,'-B',str(copy/'packet/public/check_copied_controls.py'),*args])
  receipt=json.loads((copy/'integrity-results.json').read_text());assert receipt['all_expected']
  result['copied_cases']=receipt['cases'];result['control_receipt_matches']=receipt==json.loads((ROOT/'integrity-results.json').read_text())
  verifier=[sys.executable,'-B',str(copy/'packet/public/verify.py'),*args]
  copy_before=snap(copy)
  result['verification']=run(verifier)
  assert snap(copy)==copy_before
  result['pair_diagnostic']=run([sys.executable,'-B',str(copy/'packet/public/code/pair_sanity.py')])
  assert json.loads(result['pair_diagnostic']['stdout'])==json.loads((ROOT/'packet/public/pair-sanity.json').read_text())
  # Test a locally forged chain against the genuine detached external anchors.
  p=copy/'packet/public/author-proof.md';p.write_text('forged research note\n')
  m=json.loads((copy/'packet/MANIFEST.json').read_text());m['files']['public/author-proof.md'].update(sha256=sha(p),bytes=p.stat().st_size)
  (copy/'packet/MANIFEST.json').write_text(json.dumps(m)+'\n')
  f=json.loads((copy/'FINAL.json').read_text());f['manifest_sha256']=sha(copy/'packet/MANIFEST.json')
  (copy/'FINAL.json').write_text(json.dumps(f)+'\n')
  forged=snap(copy);result['forged_reseal_control']=run(verifier,1);assert snap(copy)==forged
 for z in originals:
  current=file_record(PROJECT/z['path'])
  assert current==bindings[z['path']]
 result.update(verification_summary=json.loads(result['verification']['stdout']),originals_current_unchanged=len(originals),whole_author_root_unchanged=snap(ROOT)==before,copied_controls=8,finite_coherence_pairs=20,all_expected=True)
 assert result['whole_author_root_unchanged']
 result['limits']='Seven supplied controls plus parent forged-local-reseal rejection; root snapshots include original scratch. Named29 originals, not retroactive historical whole-workspace preservation. Exact packet/outside bindings; Python audit hook is not a syscall sandbox. Finite arithmetic and phase-mask note are unreviewed support, not mathematical or acceptance gates.'
 (HERE/'replay.json').write_text(json.dumps(result,indent=2)+'\n')
 print(json.dumps({k:result[k] for k in ['all_expected','verification_summary','originals_current_unchanged','whole_author_root_unchanged','copied_controls','finite_coherence_pairs']}))
if __name__=='__main__':main()
