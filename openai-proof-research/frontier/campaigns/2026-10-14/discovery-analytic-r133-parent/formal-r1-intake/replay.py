#!/usr/bin/env python3
"""Read-only original intake, extracted-source build and copied controls; no gate."""
import hashlib, importlib.util, json, shutil, stat, subprocess, sys, tarfile, tempfile
from pathlib import Path, PurePosixPath
sys.dont_write_bytecode=True
HERE=Path(__file__).resolve().parent
PROJECT=HERE.parents[4]
BASE=PROJECT/'frontier/campaigns/2026-10-14'
ROOT=BASE/'t088p133-formal-v1'
ANCHORS={'FINAL.json':'4fa662b09a569b1120f1fe524e6f7b8d81db0cdd6b021eef8027b1622ab15964','packet/MANIFEST.json':'042edffc552a51b2c5a96cfdfca660de9ced1d2295106765f292dc546dd8210a','REPORT.md':'7c169c608cce6f452cf95ddee16ea1cc37fab8633d474d67d63e82245cdf1476'}
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def snapshot(root):
 out={}
 for p in [root,*root.rglob('*')]:
  s=p.lstat();r={'mode':stat.S_IMODE(s.st_mode),'type':stat.S_IFMT(s.st_mode)}
  if p.is_symlink():r['target']=str(p.readlink())
  elif p.is_file():r.update(bytes=s.st_size,sha256=sha(p),nlink=s.st_nlink)
  out[str(p.relative_to(root))]=r
 return out
def run(args):
 r=subprocess.run(args,text=True,capture_output=True)
 assert r.returncode==0,(args,r.returncode,r.stderr)
 return {'exit':r.returncode,'stdout':r.stdout,'stderr':r.stderr}
def sealed_state(root):
 return {k:v for k,v in snapshot(root).items() if k=='packet' or k.startswith('packet/') or k in ANCHORS}
def main():
 originals=[ROOT,BASE/'fresh-analytic-discovery-r133',BASE/'t088p133-proof-r3']
 before={str(p):snapshot(p) for p in originals}
 for rel,h in ANCHORS.items():assert sha(ROOT/rel)==h
 assert sha(ROOT/'packet/public/T088P133.lean')=='774a43c57993ff182189d28b370b9bb8f46d6342d764d45aa886500827d44de2'
 assert sha(ROOT/'packet/public/Controls.lean')=='bceefda9b93f7ade2919cc83cfdef4a21670e23c7c8de7810873416f2ad5af9f'
 spec=importlib.util.spec_from_file_location('parent_formal_readonly_verifier',ROOT/'packet/public/verify.py')
 v=importlib.util.module_from_spec(spec);spec.loader.exec_module(v)
 result={'kind':'PARENT_IMPLEMENTATION_INTAKE_NO_INDEPENDENT_FORMAL_GATE','anchors':ANCHORS,'original_verification':v.verify(ROOT,*ANCHORS.values(),PROJECT)}
 archive=ROOT/'work/t088p133-formal-v1-source.tar.gz'
 assert sha(archive)=='555e29786e1cf9a665036d639c3c28756a688e167f378d8bc68cbe29fe0bcc5f'
 with tempfile.TemporaryDirectory(prefix='copy-',dir=HERE) as td:
  copy=Path(td)/'extracted';copy.mkdir()
  with tarfile.open(archive,'r:gz') as t:
   members=t.getmembers();paths=[]
   for x in members:
    p=PurePosixPath(x.name);assert not p.is_absolute() and '..' not in p.parts
    assert x.isfile() or x.isdir();assert not x.issym() and not x.islnk()
    assert p.parts and p.parts[0] in {'FINAL.json','REPORT.md','packet'}
    paths.append(x.name)
   assert len(paths)==len(set(paths));t.extractall(copy,filter='data')
  result['extracted_verification']=v.verify(copy,*ANCHORS.values())
  initial=sealed_state(copy)
  result['fresh_build']=run([sys.executable,'-B',str(copy/'packet/public/rebuild.py'),'--output',str(copy/'work/parent-fresh-build'),'--cache',str(BASE/'formal/.lake/packages'),'--lean','/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean'])
  receipt=json.loads((copy/'work/parent-fresh-build/receipt.json').read_text())
  assert receipt['status']=='COMPILED_SCOPED_SUPPORT_AND_CONTROLS_STANDARD_AXIOMS_ONLY'
  author=json.loads((ROOT/'packet/public/validation/receipt.json').read_text())
  for key in ['sources','dependencies','lean_version','lean_binary_sha256','dependency_lock_sha256','declarations','kernel_dependencies']:assert receipt[key]==author[key],key
  assert sha(copy/'work/parent-fresh-build/types-axioms.log')==sha(ROOT/'packet/public/validation/types-axioms.log')
  result['fresh_build_receipt']=receipt
  args=[]
  for name,h in zip(['final','manifest','report'],ANCHORS.values()):args+=['--'+name+'-sha256',h]
  result['copied_controls']=run([sys.executable,'-B',str(copy/'packet/public/integrity_controls.py'),'--output',str(copy/'work/parent-copied-controls'),*args])
  result['control_cases']=json.loads((copy/'work/parent-copied-controls/results.json').read_text());assert len(result['control_cases'])==11
  assert all(x['matched'] for x in result['control_cases'])
  result['extracted_after_build_and_controls']=v.verify(copy,*ANCHORS.values())
  assert sealed_state(copy)==initial
 result['originals_reverified']=v.verify(ROOT,*ANCHORS.values(),PROJECT)
 result['original_roots_unchanged']={str(p):snapshot(p)==before[str(p)] for p in originals}
 assert all(result['original_roots_unchanged'].values())
 result.update(all_expected=True,support_declarations=21,control_declarations=20,full_theorem_formalized=False,formal_gate=False,portable_archive_sha256=sha(archive))
 result['limits']='Fresh own Lean source/control/type-axiom compilation on extracted package, trusted precompiled pinned mathlib/dependencies read-only. No clean dependency rebuild/cache-byte authentication. Exact packet modes/linkcounts/layout and940 used original entries; excluded work scratch not sealed. Independent semantic/scoped formal review remains required; no full geometric formalization, campaign acceptance or release gate.'
 (HERE/'replay.json').write_text(json.dumps(result,indent=2)+'\n')
 print(json.dumps({k:result[k] for k in ['all_expected','original_verification','support_declarations','control_declarations','full_theorem_formalized','formal_gate']}))
if __name__=='__main__':main()
