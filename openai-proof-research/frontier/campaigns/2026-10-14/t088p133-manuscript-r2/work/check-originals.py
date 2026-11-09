from pathlib import Path
import hashlib,json,stat,subprocess,sys
R=Path.cwd();PROJECT=R.parents[3];BASE=R.parent;P=R/'packet/public'
h=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def rec(p):
 s=p.lstat();d={'mode':stat.S_IMODE(s.st_mode),'nlink':s.st_nlink}
 if p.is_symlink():d.update(kind='symlink',target=str(p.readlink()))
 elif p.is_dir():d.update(kind='directory')
 else:d.update(kind='file',bytes=s.st_size,sha256=h(p))
 return d
before=json.loads((R/'work/originals-before.json').read_text())
roots=[p for p in before if '/' not in p.removeprefix('frontier/campaigns/2026-10-14/')]
after={}
for rel in roots:
 for p in [PROJECT/rel,*sorted((PROJECT/rel).rglob('*'))]:after[str(p.relative_to(PROJECT))]=rec(p)
assert before==after,([k for k in set(before)|set(after) if before.get(k)!=after.get(k)])
anchors=json.loads((R/'work/input-anchors.json').read_text())
anchors['t088p133-contribution-r1']=['c84fa541285ee770acf37b9df9728dee603bb40202fec6dfc868173a6069e7c7','66405c96dd6b76d25e7a290dc8d17d1f24abf489bcb2c45fd7e4deb8eef13656','89595f993f3f5ec2aa98bc87cfa30eefdaa2d4319b5f77b3c45349191e72627b']
for name,hs in anchors.items():
 for rel,expected in zip(['FINAL.json','packet/MANIFEST.json','REPORT.md'],hs):assert h(BASE/name/rel)==expected,(name,rel)
proofhashes={'FROZEN-THEOREM.md':'86e1f30e2c867215026b2a4c2bc0c50144660618c486d2b2029e044bfce8d354','proof.md':'971506a4ea3de75a883da6d0eced6b11b0b997cc2a6598c2e0487ee5a6e2bc84'}
for f,v in proofhashes.items():assert h(BASE/'fresh-analytic-discovery-r133/packet/public'/f)==v
runs=[]
for name in ['t088p133-manuscript-r1','t088p133-formal-v1','t088p133-formal-review-r1']:
 cmd=[sys.executable,'-B',str(BASE/name/'packet/public/verify.py')]
 if name=='t088p133-manuscript-r1':cmd+=[str(BASE/name)]
 else:cmd+=['--root',str(BASE/name)]
 for key,value in zip(['final','manifest','report'],anchors[name]):cmd+=['--'+key+'-sha256',value]
 cp=subprocess.run(cmd,text=True,capture_output=True);assert cp.returncode==0,cp.stderr
 runs.append({'package':name,'verifier_sha256':h(BASE/name/'packet/public/verify.py'),'exit':cp.returncode,'result':json.loads(cp.stdout)})
parent=BASE/'discovery-analytic-r133-parent'
# Named parent input bindings are checked against earlier copied bytes, not whole-parent layout.
named={}
for p in (P/'provenance/parent').rglob('*'):
 if p.is_file():
  rel=p.relative_to(P/'provenance/parent');q=parent/rel
  if not q.exists():
   candidates=[x for x in parent.rglob(p.name) if x.is_file()];assert len(candidates)==1,(p.name,candidates);q=candidates[0]
  assert h(p)==h(q);named[str(q.relative_to(PROJECT))]={'sha256':h(q),'bytes':q.stat().st_size}
result={'whole_original_roots':roots,'entries':len(before),'exact_path_set_bytes_modes_links_targets_unchanged':True,'start_inventory_sha256':h(R/'work/originals-before.json'),'parent_named_inputs_match_earlier_copies':named,'parent_whole_root_claim':False,'external_anchor_checks':anchors,'author_scope_and_proof':proofhashes,'read_only_original_verifications':runs,'r1_private_inventory_named_files':36,'private_verification_separate_from_public_verifier':True,'scope':'lstat/read/hash and read-only verifier, not syscall tracing, upstream truth audit or new gate'}
(R/'work/originals-end.json').write_text(json.dumps(after,indent=2,sort_keys=True)+'\n')
(P/'qa/original-preservation.json').write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
print(json.dumps({'original_entries':len(before),'roots':len(roots),'parent_files':len(named),'unchanged':True,'read_only_verifier_results':runs}))
