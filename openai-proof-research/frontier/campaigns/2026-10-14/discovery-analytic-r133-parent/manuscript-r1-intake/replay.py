#!/usr/bin/env python3
"""Draft artifact/support intake, not a manuscript or mathematical review."""
import hashlib,json,shutil,stat,subprocess,sys,tempfile
from pathlib import Path
sys.dont_write_bytecode=True
HERE=Path(__file__).resolve().parent
PROJECT=HERE.parents[4]
BASE=PROJECT/'frontier/campaigns/2026-10-14'
ROOT=BASE/'t088p133-manuscript-r1'
ANCHORS={'final':'78f23929122e7620522feb5e5679dd290071f9848a15f892d4806275a83f8a39','manifest':'e7d2588e9783d3f2bd0ec7754e7865be0e5c12ed8609531f5632e80266eccb34','report':'87779f0e8a55fd31920a3345fed238cd70ea99afa26a758d7158e28e69110330'}
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def record(p):
 s=p.lstat();r={'mode':stat.S_IMODE(s.st_mode),'links':s.st_nlink}
 if p.is_symlink():r.update(kind='symlink',target=str(p.readlink()))
 elif p.is_dir():r['kind']='dir'
 else:r.update(kind='file',bytes=s.st_size,sha256=sha(p))
 return r
def snap(root):return {str(p.relative_to(root)):record(p) for p in [root,*root.rglob('*')]}
def run(args):
 r=subprocess.run(args,text=True,capture_output=True);assert r.returncode==0,(args,r.returncode,r.stderr)
 return {'exit':r.returncode,'stdout':r.stdout,'stderr':r.stderr}
def verify(root):
 args=[sys.executable,'-B',str(root/'packet/public/verify.py'),str(root)]
 for k,h in ANCHORS.items():args+=['--'+k+'-sha256',h]
 return run(args)
def main():
 before=snap(ROOT)
 for rel,k in [('FINAL.json','final'),('packet/MANIFEST.json','manifest'),('REPORT.md','report')]:assert sha(ROOT/rel)==ANCHORS[k]
 assert sha(ROOT/'packet/public/verify.py')=='559b66d1a87c0273c7ecdc51bbff02b5b4589217c276ba44cfd6d3a10ab04d91'
 final=json.loads((ROOT/'FINAL.json').read_text());assert sha(ROOT/'private/MANIFEST.json')==final['private_evidence_manifest_sha256']
 private=json.loads((ROOT/'private/MANIFEST.json').read_text())
 for rel,m in private['files'].items():
  p=ROOT/rel;s=p.lstat();assert stat.S_ISREG(s.st_mode) and s.st_nlink==1 and s.st_size==m['bytes'] and stat.S_IMODE(s.st_mode)==m['mode'] and sha(p)==m['sha256']
 originals=json.loads((ROOT/'work/originals-start.json').read_text());assert len(originals)==1046 and originals==json.loads((ROOT/'private/originals-end.json').read_text())
 for rel,m in originals.items():assert record(BASE/rel)==m,rel
 for name in ['fresh-analytic-discovery-r133','t088p133-contribution-r1','t088p133-proof-r3']:
  actual={name}|{str(p.relative_to(BASE)) for p in (BASE/name).rglob('*')};expected={p for p in originals if p==name or p.startswith(name+'/')};assert actual==expected
 result={'kind':'PARENT_MATHEMATICAL_DRAFT_INTAKE_NOT_MANUSCRIPT_REVIEW','anchors':ANCHORS,'verification':verify(ROOT),'private_named_files_authenticated':len(private['files']),'actual_original_entries':len(originals)}
 with tempfile.TemporaryDirectory(prefix='copy-',dir=HERE) as td:
  copy=Path(td)/'draft';copy.mkdir();shutil.copytree(ROOT/'packet',copy/'packet')
  for name in ['FINAL.json','REPORT.md']:shutil.copy2(ROOT/name,copy/name)
  initial=snap(copy/'packet')
  result['exact_support']=run([sys.executable,'-B',str(copy/'packet/public/support/reproduce.py'),str(copy/'build/checks')])
  assert (copy/'build/checks/witness-tables.tex').read_bytes()==(copy/'packet/public/witness-tables.tex').read_bytes()
  result['copied_controls']=run([sys.executable,'-B',str(copy/'packet/public/support/integrity_controls.py'),str(copy),str(copy/'work/parent-controls')])
  cases=json.loads((copy/'work/parent-controls/results.json').read_text());assert len(cases['results'])==12 and all(x['read_only_snapshot_equal'] and x['actual_exit']==x['expected_exit'] for x in cases['results'])
  result['control_cases']=cases['results'];result['post_controls_verification']=verify(copy);assert snap(copy/'packet')==initial
 for rel,m in originals.items():assert record(BASE/rel)==m
 assert snap(ROOT)==before
 result.update(all_expected=True,public_payload_files=52,public_directories=7,copied_cases=12,patterns=10,sparse_coefficients=248,pdf_sha256=sha(ROOT/'packet/public/output/pdf/main.pdf'),whole_author_draft_unchanged=True,formal_integration='PENDING_NEW_IMMUTABLE_ROUND',manuscript_gate=False)
 result['limits']='Public seal covers52 files/7 dirs; separate FINAL-bound private inventory authenticates36 named files only,not complete private tree or public-verifier coverage.1046 actual originals/layouts match; hash checks are not body reads. Exact finite support/tables/copy controls reproduced; old draft PDF not rebuilt because formal integration needs a new immutable PDF round. Implementer17-page visual/repeat-build QA is attributed; parent performs sample layout intake only. Independent final manuscript review and release still required.'
 (HERE/'replay.json').write_text(json.dumps(result,indent=2)+'\n')
 print(json.dumps({k:result[k] for k in ['all_expected','public_payload_files','public_directories','private_named_files_authenticated','actual_original_entries','copied_cases','patterns','sparse_coefficients','whole_author_draft_unchanged','manuscript_gate']}))
if __name__=='__main__':main()
