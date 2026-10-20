#!/usr/bin/env python3
"""Parent copied-review replay and stable-original authentication; scoped only."""
import hashlib, importlib.util, json, shutil, stat, subprocess, sys, tarfile, tempfile
from pathlib import Path, PurePosixPath
sys.dont_write_bytecode=True
HERE=Path(__file__).resolve().parent
PROJECT=HERE.parents[4]
BASE=PROJECT/'frontier/campaigns/2026-10-14'
ROOT=BASE/'t088p133-formal-review-r1'
ANCHORS={'FINAL.json':'d50f1d0309089266f87e13d02a10e49d0b4fed8961031a14cfbdbb983e33943a','packet/MANIFEST.json':'028b5a8d5f5ebad46c5b690e4259e626cfd8d6d045b4a68aac551bee0d3f3978','REPORT.md':'69a03b514296d023e3f16034252931dce413f908c3e6770e8e0dc42876d61ebc'}
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def snapshot(root):
 out={}
 for p in [root,*root.rglob('*')]:
  s=p.lstat();x={'mode':stat.S_IMODE(s.st_mode),'type':stat.S_IFMT(s.st_mode)}
  if p.is_symlink():x['target']=str(p.readlink())
  elif p.is_file():x.update(bytes=s.st_size,sha256=sha(p),nlink=s.st_nlink)
  out[str(p.relative_to(root))]=x
 return out
def run(args):
 r=subprocess.run(args,text=True,capture_output=True);assert r.returncode==0,(args,r.returncode,r.stderr)
 return {'exit':r.returncode,'stdout':r.stdout,'stderr':r.stderr}
def main():
 roots=[BASE/n for n in ['fresh-analytic-discovery-r133','t088p133-proof-r3','t088p133-formal-v1','t088p133-formal-review-r1']]
 before={str(p):snapshot(p) for p in roots}
 for rel,h in ANCHORS.items():assert sha(ROOT/rel)==h
 spec=importlib.util.spec_from_file_location('parent_formal_review_verifier',ROOT/'packet/public/verify.py');v=importlib.util.module_from_spec(spec);spec.loader.exec_module(v)
 result={'kind':'PARENT_SCOPED_FORMAL_REVIEW_ADOPTION_REPLAY','anchors':ANCHORS,'verification':v.verify(ROOT,*ANCHORS.values(),PROJECT)}
 archive=ROOT/'work/t088p133-formal-review-r1-source.tar.gz';assert sha(archive)=='b102f756015164427e0e8a371133b07894ab824f84301afe93df36dde982dcb1'
 with tempfile.TemporaryDirectory(prefix='copied-',dir=HERE) as td:
  copy=Path(td)/'review';copy.mkdir()
  with tarfile.open(archive) as t:
   seen=[]
   for m in t.getmembers():
    p=PurePosixPath(m.name);assert not p.is_absolute() and '..' not in p.parts and p.parts[0] in {'FINAL.json','REPORT.md','packet'} and (m.isfile() or m.isdir())
    seen.append(m.name)
   assert len(seen)==len(set(seen));t.extractall(copy,filter='data')
  result['extracted_verification']=v.verify(copy,*ANCHORS.values())
  result['formal_replay']=run([sys.executable,'-B',str(copy/'packet/public/replay.py'),'--output',str(copy/'work/parent-replay'),'--cache',str(BASE/'formal/.lake/packages'),'--lean','/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean'])
  replay=json.loads((copy/'work/parent-replay/replay.json').read_text());assert replay['all_expected']
  assert len(replay['review_declarations'])==15 and len(replay['semantic_mutations'])==2 and len(replay['exact_controls'])==10
  assert sha(copy/'work/parent-replay/review-types-axioms.log')==sha(ROOT/'packet/public/evidence/review-types-axioms.log')
  result['fresh_formal_replay']=replay
  args=[]
  for label,h in zip(['final','manifest','report'],ANCHORS.values()):args+=['--'+label+'-sha256',h]
  result['review_artifact_controls']=run([sys.executable,'-B',str(copy/'packet/public/integrity_controls.py'),'--output',str(copy/'work/parent-review-controls'),*args])
  cases=json.loads((copy/'work/parent-review-controls/results.json').read_text());assert len(cases)==11 and all(x['matched'] for x in cases)
  result['review_control_cases']=cases
  result['extracted_after_replay']=v.verify(copy,*ANCHORS.values())
 result['originals_reverified']=v.verify(ROOT,*ANCHORS.values(),PROJECT)
 result['original_roots_unchanged']={str(p):snapshot(p)==before[str(p)] for p in roots};assert all(result['original_roots_unchanged'].values())
 result.update(all_expected=True,review_payload_entries=35,review_payload_files=32,stable_original_entries=1647,observation_entries=2,support_declarations=21,implementation_control_declarations=20,review_declarations=15,semantic_mutations=2,exact_configurations=10,implementation_artifact_cases=11,review_artifact_cases=11,full_theorem_formalized=False)
 result['limits']='Fresh own implementation and review sources compiled against trusted pinned precompiled dependencies, not clean-source dependency rebuild or binary-cache authentication. Review original ordinary replay needed the separately anchored implementation at its original project path. Seal/preservation and semantic mutation checks are bounded; private bodies only hash-inventoried, no body-read or syscall-sandbox claim. Deterministic algebra only; no campaign acceptance/manuscript/release gate.'
 (HERE/'replay.json').write_text(json.dumps(result,indent=2)+'\n')
 print(json.dumps({k:result[k] for k in ['all_expected','review_payload_entries','review_payload_files','stable_original_entries','support_declarations','implementation_control_declarations','review_declarations','semantic_mutations','exact_configurations','implementation_artifact_cases','review_artifact_cases','full_theorem_formalized']}))
if __name__=='__main__':main()
