#!/usr/bin/env python3
"""Bind exact audit inputs/read extents and all outputs; writes only this directory."""
from pathlib import Path
import hashlib,json
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[3]
FROZEN=HERE.parent/'kinetic-formal-v1'
def digest(p):
 b=p.read_bytes();return {'path':str(p.relative_to(ROOT)) if p.is_relative_to(ROOT) else str(p),'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()}
def main():
 inputs=[]
 def add(p,extent,role):inputs.append({**digest(p),'read_extent':extent,'role':role})
 add(ROOT/'AGENTS.md','entire file','repository review instructions')
 add(ROOT/'sources/upstream.json','entire file','stipulated immutable upstream truth pin')
 add(ROOT/'sources/CONTENTS.md','lines 8813-8841; relevant hard-sphere catalogue item','orientation only, not collision-formula evidence')
 tree=ROOT/'sources/preprints-tree.json'
 add(tree,'parsed complete JSON tree; selected exact source path below','immutable complete tree provenance, not entire manuscript reading')
 source_path='preprints/Hard-sphere-fluctuations-on-the-regular-Boltzmann-lifespan-September-23-2026/build/sections/03-dhm-inputs.tex'
 corpus=ROOT/'frontier/sources/i23_kinetic_connected_fluctuations/corpus'/source_path
 add(corpus,'lines 125-157, especially eq:atom-C, eq:atom-O and affine edge positions','actual primary physical collision and affine flight definitions')
 b=corpus.read_bytes();blob=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
 row=next(r for r in json.loads(tree.read_text())['tree'] if r.get('path')==source_path)
 assert row['sha']==blob=='ffa665888b0880d2db70d38e5224930e8220825d'
 add(HERE.parent/'kinetic-repair-r1/candidate.md','lines 1-100, 158-338, 747-812','exact original kinetic target; complete relevant physical chart, pre-first origins and covariance; complete used chaining/transfer exponent passages; not a full analytic proof re-review')
 manifest=json.loads((FROZEN/'outputs.json').read_text())
 for row in manifest['files']:
  p=FROZEN/row['path'];assert digest(p)['sha256']==row['sha256']
  add(p,'entire file','frozen author package; logs/validation are inspected claims, not independent evidence')
 add(FROZEN/'outputs.json','entire file','frozen author package manifest')
 add(HERE.parent/'formal/.lake/packages/mathlib/Mathlib/Analysis/InnerProductSpace/Basic.lean','lines 1009-1017 containing Real.inner_apply','standard library real-line inner product used in exact counterchecks')
 lean=Path('/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean')
 tool=digest(lean)
 prov={'verdict':'PASS for narrow nine-theorem algebra support only','date':'2026-10-14','reviewer':'independent child agent /root/newten_three_state_capacity','write_scope':str(HERE),'stipulated_upstream':{'repository':'https://github.com/openai/math','commit':'fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb','source_path':source_path,'source_git_blob_sha1':blob,'blob_matches_complete_tree':True},'inputs':inputs,'compiler':tool,'mathlib_revision':'d13f23b723b8a846827a245b89c10fc7d3f11612','execution':{'runner':'python run_review.py','fresh_source_olean':True,'author_olean_used':False,'all_nine_exact_types_checked_with_independent_raw_wrappers':True,'positive_runs':3,'independent_audit_theorems':14,'expected_failure_mutations':4,'standard_axioms':['propext','Classical.choice','Quot.sound'],'original_verifier_executed':False,'cache_usage':'Existing compiled pinned dependency cache reused read-only; no dependency rebuild or clean network installation tested.','writes':'Own review directory only. No author edits, commits, staging, shared indexes, or subagents.'},'scope_exclusions':['No formal collision-history construction or entering-root covariance','No formal measure preservation or window estimate','No formal moment bounds, tightness or J1 convergence','No novelty, acceptance, publication or count decision'],'limitations':['Input full files are hashed even where only explicitly listed passages were read.','Pinned upstream theorem truth stipulated; no upstream theorem proof audit.','This does not independently rebuild Lean or all mathlib oleans.']}
 (HERE/'provenance.json').write_text(json.dumps(prov,indent=2)+'\n')
 files=[]
 for p in sorted(HERE.rglob('*')):
  if p.is_file() and p.name!='outputs.json':
   r=digest(p);r['path']=str(p.relative_to(HERE));files.append(r)
 (HERE/'outputs.json').write_text(json.dumps({'manifest_excludes_itself':True,'files':files},indent=2)+'\n')
 print(json.dumps({'review_sha256':digest(HERE/'review.md')['sha256'],'provenance_sha256':digest(HERE/'provenance.json')['sha256'],'outputs_sha256':digest(HERE/'outputs.json')['sha256'],'output_files':len(files)},indent=2))
if __name__=='__main__':main()
