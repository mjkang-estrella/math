#!/usr/bin/env python3
"""Authenticate prefreeze notes, replay finite checks on copies; no gate."""
import hashlib, json, shutil, stat, subprocess, sys, tempfile
from pathlib import Path
sys.dont_write_bytecode=True
HERE=Path(__file__).resolve().parent
PROJECT=HERE.parents[3]
ROOT=HERE.parent/'fresh-structural-discovery-r136'
ANCHORS={'final':'1c53d5afb3d6fb8b72b17d64e1b10e20af857aad7144927f285cb90869ba7dec','manifest':'d778dd807176909cfde8721ceccf14b8cf5b7ab7cdd1cf58355b2a9259295e36','report':'36c5a124cd535e04a2dbf5098d0376bfeb3c51452b3b19c29cad18b8bb4a29b9'}
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def record(p):
 s=p.lstat();r={'mode':stat.S_IMODE(s.st_mode),'type':stat.S_IFMT(s.st_mode)}
 if p.is_symlink():r['target']=str(p.readlink())
 elif p.is_file():r.update(bytes=s.st_size,sha256=sha(p),nlink=s.st_nlink)
 return r
def snap(root):return {str(p.relative_to(root)):record(p) for p in [root,*root.rglob('*')]}
def run(args,expected=0):
 r=subprocess.run(args,text=True,capture_output=True);assert r.returncode==expected,(args,r.returncode,r.stderr)
 return {'exit':r.returncode,'stdout':r.stdout,'stderr':r.stderr}
def command(root,project,script):
 args=[sys.executable,'-B',str(root/'packet/public'/script),'--root',str(root),'--project',str(project)]
 for k,h in ANCHORS.items():args+=['--'+k+'-sha256',h]
 return args
def main():
 before=snap(ROOT)
 for p,k in [('FINAL.json','final'),('packet/MANIFEST.json','manifest'),('REPORT.md','report')]:assert sha(ROOT/p)==ANCHORS[k]
 entries=[]
 for name in ['originals-before.json','history-inputs-before.json','thin-history-inputs-before.json','additional-inputs-before.json']:
  j=json.loads((ROOT/'packet/private'/name).read_text());entries+=j['files'] if isinstance(j,dict) else j
 stable={x['path']:x for x in entries if x['path']!='frontier/NEW-TEN-2026-10-14.md'};assert len(stable)==29
 originals={rel:record(PROJECT/rel) for rel in stable}
 result={'kind':'PARENT_PREFREEZE_ARTIFACT_INTAKE_NO_MATHEMATICAL_GATE','anchors':ANCHORS}
 result['actual_original_verification']=run(command(ROOT,PROJECT,'verify.py'))
 with tempfile.TemporaryDirectory(prefix='copy-',dir=HERE) as td:
  mirror=Path(td)/'project';copy=mirror/'frontier/campaigns/2026-10-14/fresh-structural-discovery-r136';copy.mkdir(parents=True)
  shutil.copytree(ROOT/'packet',copy/'packet')
  for name in ['FINAL.json','REPORT.md']:shutil.copy2(ROOT/name,copy/name)
  (copy/'work').mkdir()
  for rel in stable:
   p=mirror/rel;p.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(PROJECT/rel,p)
  initial={rel:record(mirror/rel) for rel in stable}
  result['copied_controls']=run(command(copy,mirror,'run_copied_controls.py'))
  receipt=json.loads((copy/'work/control-receipt.json').read_text());assert receipt['all_expected'] and len(receipt['records'])==8
  result['copied_control_cases']=receipt['records']
  result['finite_diagnostic']=run([sys.executable,'-B',str(copy/'packet/public/check_math.py')])
  assert json.loads(result['finite_diagnostic']['stdout'])['K4_exact_marginal_threshold']=='5/3'
  assert all(record(mirror/rel)==r for rel,r in initial.items())
  forged=copy/'work/forged-reseal';forged.mkdir();shutil.copytree(copy/'packet',forged/'packet')
  for name in ['FINAL.json','REPORT.md']:shutil.copy2(copy/name,forged/name)
  p=forged/'packet/public/derivations.md';p.write_text('locally forged note\n')
  m=json.loads((forged/'packet/MANIFEST.json').read_text());m['files']['public/derivations.md'].update(sha256=sha(p),bytes=p.stat().st_size)
  (forged/'packet/MANIFEST.json').write_text(json.dumps(m)+'\n')
  f=json.loads((forged/'FINAL.json').read_text());f['manifest_sha256']=sha(forged/'packet/MANIFEST.json');(forged/'FINAL.json').write_text(json.dumps(f)+'\n')
  state=snap(forged);args=command(copy,PROJECT,'verify.py');args[args.index('--root')+1]=str(forged)
  result['forged_local_reseal']=run(args,1);assert snap(forged)==state
  result['copied_after_controls']=run(command(copy,mirror,'verify.py'))
 assert all(record(PROJECT/rel)==r for rel,r in originals.items())
 result['verification_summary']=json.loads(result['actual_original_verification']['stdout'])
 result.update(all_expected=True,stable_originals_unchanged=29,whole_author_root_unchanged=snap(ROOT)==before,copied_controls_total=9,mutable_navigation_entries=1)
 assert result['whole_author_root_unchanged']
 result['limits']='Named stable29 originals/copies; one mutable ledger excluded. Original bindings followed initial mandatory reads. Exact packet bytes/modes/directory set, not a syscall sandbox or historical semantic reading. Parent current whole-author snapshot includes unsealed work. Eight unmodified supplied controls run in a mirrored disposable project, plus one parent forged-local-reseal rejection; finite K4/triangle checks are support, not mathematical/contribution/acceptance gates.'
 (HERE/'replay.json').write_text(json.dumps(result,indent=2)+'\n')
 print(json.dumps({k:result[k] for k in ['all_expected','verification_summary','stable_originals_unchanged','whole_author_root_unchanged','copied_controls_total','mutable_navigation_entries']}))
if __name__=='__main__':main()
