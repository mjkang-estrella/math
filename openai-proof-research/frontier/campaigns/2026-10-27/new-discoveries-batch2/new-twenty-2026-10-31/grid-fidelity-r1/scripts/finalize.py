import json,re,hashlib
from pathlib import Path
r=Path(__file__).resolve().parent.parent
logs=list((r/'packet/logs').glob('*.log'))+list((r/'logs').glob('*.log'))
resources=[]
for p in logs:
 for wall,rss,code in re.findall(r'RESOURCE wall_s=([\d.]+) peak_rss_kib=(\d+) exit=(\d+)',p.read_text()):
  resources.append(dict(log=str(p.relative_to(r)),wall_s=float(wall),peak_rss_kib=int(rss),exit=int(code)))
compiled=sorted(p.name.split('-compile-')[-1][:-4] for p in logs if '-compile-' in p.name and 'exit=0' in p.read_text())
checked=sorted(p.name.split('-checker-')[-1][:-4] for p in logs if '-checker-' in p.name and 'exit=0' in p.read_text())
before=(r/'inputs-before.sha256').read_text()
after=(r/'inputs-after.sha256').read_text()
assert before==after
assert (r/'upstream-bound-before.sha256').read_text()==(r/'upstream-bound-after.sha256').read_text()
assert len(compiled)==47 and len(checked)==47
assert 'exit=0' in (r/'logs/sanity-compile.log').read_text()
assert 'exit=0' in (r/'logs/sanity-checker.log').read_text()
assert (r/'logs/forbidden-scan.log').read_text()==''
assert any('GridFinal6.mathdb_343536' in p.read_text() and 'propext, Classical.choice, Quot.sound' in p.read_text() for p in logs if 'compile-GridFinal6' in p.name)
data=dict(
 review_type='INDEPENDENT_FORMAL_FIDELITY_NOT_ACCEPTANCE',
 endpoint='GridFinal6.mathdb_343536',
 packet_sha256='a4068de99037028f817f2f5d1652a97d7508c4419353da95abea04b45b977953',
 verdicts={'A':'PASS','B':'PASS','C':'PASS','D':'QUALIFIED_PASS','E':'QUALIFIED_PASS'},
 verdict_reasons={
 'A':'Literal three-conjunct positive-dimension endpoint; correct definitions, refinement order, complete lattice and full automorphism group; natural-map form also derived.',
 'B':'Every inherited Prop discharged; proof trace and exact references in REVIEW.md.',
 'C':'Independent complete degree-compatible partition enumeration and full automorphism/subgroup enumeration agree; own Lean sanity examples compiled.',
 'D':'All 47 packet modules strictly compiled and leanchecked serially; allowed endpoint axioms only; lexical scan clean. Qualified for initial round-6 prose read before manifest, reviewer replay-driver interruption with detached-child cleanup, audit import warnings, and historical round-6 overlap; root replay remains separate.',
 'E':'Manuscript checklist supplied; stale partial-status prose and literature/access qualifications require editorial integration.'},
 binding={'before':'inputs-before.sha256','after':'inputs-after.sha256','identical':True,'files':len(before.splitlines()),
 'manifest_sha256':hashlib.sha256(before.encode()).hexdigest(),
 'before_first_read':False,
 'timing_note':'Round-6 prose documents were initially read before the first manifest; binding preceded extraction/source review/builds.',
 'upstream_bound_source_unchanged':True},
 formal={'lean_version':'4.34.1','mathlib_revision':'d13f23b723b8a846827a245b89c10fc7d3f11612',
 'compiled_modules':compiled,'leanchecked_modules':checked,
 'endpoint_axioms':['propext','Classical.choice','Quot.sound'],
 'forbidden_tokens':[],'own_sanity_log':'logs/sanity-compile.log',
 'root_decisive_replay_claimed':False},
 semantic={'enumerator':'scripts/enumerate.py','log':'logs/enumeration.log','results':'enumeration.json','lean_examples':'Sanity.lean',
 'method':'Complete restricted-growth partitions within degree classes; literal neighbour-count test; complete full graph automorphism backtracking; exhaustive closed-subset subgroup search.',
 'small_grid_counts':[{k:v for k,v in x.items() if k!='partitions'} for x in json.loads((r/'enumeration.json').read_text())],
 'lean_count_scope':'Kernel-decided distinct equitable label lists; no new Lean completeness/cardinality theorem claimed outside inherited exceptional bounds.'},
 resources={'runner':'packet/scripts/run.sh','watchdog':'packet/scripts/watch.pl',
 'rss_cap_kib':6*1024*1024,'cpus':[30,31],'cpu_s':120,'wall_s':140,'lean_flags':['-j1','-M3500','-DwarningAsError=true'],
 'max_wall_s':max(x['wall_s'] for x in resources),'max_peak_rss_kib':max(x['peak_rss_kib'] for x in resources),
 'one_heavy_process_at_a_time':True,'uninterrupted_watchdog_coverage':False,'reviewer_deviation':'First replay driver exited 143 during Audit6; detached child group survived without watchdog, verified lane-local and terminated; interrupted invocation excluded, audit rerun capped.','background_jobs_left':False,'invocations':resources},
 required_fixes=[
 'Consolidate historical partial/conditional status text, especially grid-formal-r6/PROOF.md:4 and STATEMENT-CORRESPONDENCE.md:20-23.',
 'Manuscript must state all three sentences and positive dimensions, and expose the natural orbit-map lattice isomorphism.',
 'Limit novelty claim to sentence 1 for both dimensions at least 2; preserve known path case, modest significance and unresolved compactness prior-art channel.',
 'Include exact definitions/correspondence, audit and replay evidence, historical resource overlap, and source/prior-art access limits.',
 'Root must perform its separate decisive replay and acceptance decision.'],
 mathematical_source_fixes=[],
 prohibited_actions={'child_agents':False,'git':False,'shared_ledger_edits':False,'network':False,'browser':False,'publication':False,'upload':False,'external_messages':False},
 self_accepted=False,credit=0)
(r/'review.json').write_text(json.dumps(data,indent=2)+'\n')
(r/'resource-summary.json').write_text(json.dumps(resources,indent=2)+'\n')
print(json.dumps({k:data[k] for k in ['verdicts','binding']}))
