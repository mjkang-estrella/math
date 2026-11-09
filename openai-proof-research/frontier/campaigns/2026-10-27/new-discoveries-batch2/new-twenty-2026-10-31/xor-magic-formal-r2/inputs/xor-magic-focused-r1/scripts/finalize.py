import json,hashlib,datetime
from pathlib import Path
root=Path('.').resolve();inputs=json.loads(Path('receipts/input-hashes.json').read_text())
for p in [root/'TASK.txt',root.parent/'ledger.json',root.parent/'AGENTS.md',root.parent.parent/'ledger.json',root.parent.parent/'prior-campaign-context.json',root.parent.parent/'AGENTS.md',*[(root.parents[5]/'AGENTS.md')]]:
 if p.is_file():inputs[str(p)]=hashlib.sha256(p.read_bytes()).hexdigest()
# The ancestor project AGENTS file is added by walking ancestors, not guessing depth.
for d in root.parents:
 p=d/'AGENTS.md'
 if p.is_file():inputs[str(p)]=hashlib.sha256(p.read_bytes()).hexdigest()
Path('receipts/input-hashes.json').write_text(json.dumps(inputs,indent=2)+'\n')
provenance=json.loads(Path('../expanded-corpus-r90/extracted.json').read_text())
def walk(x):
 if isinstance(x,dict):
  if str(x.get('mathdb_id',''))=='372205':return x
  for k,v in x.items():
   if str(k)=='372205':return v
   z=walk(v)
   if z is not None:return z
 elif isinstance(x,list):
  for v in x:
   z=walk(v)
   if z is not None:return z
Path('receipts/mathdb-provenance.json').write_text(json.dumps(walk(provenance),indent=2)+'\n')
r={'372205':{
 'outcome':'literal_statement_false_due_to_known_forbidden_endpoint; corrected_full_range_ordinary_construction_candidate',
 'accepted':False,'credit':0,'root_acceptance_required':True,
 'exact_scope':{'source':'arXiv:2512.19278v1 Conjecture 25','definitions':'connected simple graph; bijection to F2^n; neighbourhood sum ZERO','n':'intended n >= 4; implicit in conjecture and explicit in surrounding Theorem 5','open':'odd 5 <= d <= 2^n-5','closed_literal':'even 4 <= d <= 2^n-4','closed_corrected':'even 4 <= d <= 2^n-6'},
 'coverage':{'literal_closed_endpoint':{'n':'every n >= 4','d':'2^n-4','status':'impossible; ordinary proof via cubic complement; already Proposition 24; zero novelty credit'},'open':{'n':'all n >= 4','d':'every odd 5 <= d <= 2^n-5','status':'ordinary constructive proof candidate, unreviewed and not Lean formalized'},'closed_corrected':{'n':'all n >= 4','d':'every even 4 <= d <= 2^n-6','status':'ordinary constructive proof candidate, unreviewed and not Lean formalized'},'ordinary_corrected_parameter_gaps':[], 'exact_finite_base_certificates':'all corrected open and closed degrees at orders 16 and 32; outputs/base-coverage.json','sampled_construction_validation':'all k,j interpolation choices at orders 64 and 128; low-degree seeds also lifted to orders 256 and 512'},
 'proof_status':'PROOF.md contains direct literal obstruction and full corrected ordinary construction with connectivity, decompositions, interpolation and bases; independent review pending',
 'lean_status':{'full_literal_endpoint':False,'corrected_endpoint':False,'kernel_checker':False,'leanchecker':False,'fresh_extracted_rebuild':False,'local_declaration_audit':False,'packet':None,'reason':'Literal affirmative theorem is false. Corrected construction is a different statement; no full Lean proof was completed.'},
 'computational_status':{'unstructured_closed32_degree6':'15 s and 60 s searches timed out without incumbent; no nonexistence inference','symmetric_closed32_degree6':'found in 3.23 solver seconds with 184 edge orbits; all exact graph checks passed','closed32_degrees8_10_12_14':'found, exactly checked including complement connectivity','negative_controls':'deleted edge, duplicate edge, loop, wrong open/closed type all rejected'},
 'prior_art':{'status':'incomplete; no full constructive resolution identified in inspected primary sources','batal_body':'inaccessible publisher 403; no retry','later_primary':'arXiv:2609.05934 relevant bodies screened; no resolution located','current_registries':{'openai/math':'4eaee87548250b2682affda7d05d947c05554bae','the-omega-institute/trureturing':'9542edf9895bb4a23fff4fa7f2e1ef5b849edbe1'},'registry_clearance':'HEAD and latest-change metadata only, not exhaustive current bodies','novelty_certified':False},
 'resource_policy':'per expensive child: CPU affinity 2; CPU 120 s; wall 140 s; private RSS 6 GiB sampled at 0.1 s; AS 64 GiB; MALLOC_ARENA_MAX=2; no background jobs at handback',
 'deliverables':['SUMMARY.md','PROOF.md','PRIOR-ART.md','results.json','scripts/','outputs/','receipts/','logs/'],
 'handoff':'Do not count endpoint correction. Review corrected constructive proof and prior-art gaps before considering a separately scoped full Lean formalization.'}}
Path('results.json').write_text(json.dumps(r,indent=2)+'\n')
manifest={str(p.relative_to(root)):hashlib.sha256(p.read_bytes()).hexdigest() for p in root.rglob('*') if p.is_file() and p.name!='artifact-manifest.json'}
Path('artifact-manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
print('Finalized',len(manifest),'files; accepted credit 0; corrected ordinary parameter gaps none; Lean incomplete.')
