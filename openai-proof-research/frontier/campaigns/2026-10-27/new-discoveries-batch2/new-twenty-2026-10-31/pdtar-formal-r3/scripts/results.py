import pathlib,json,hashlib,re,collections,time
D=pathlib.Path(__file__).resolve().parents[1]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
s=json.loads((D/'replay-state.json').read_text());assert s['next']==60
m=json.loads((D/'manifest.json').read_text());before=json.loads((D/'frozen-before.json').read_text());after=json.loads((D/'frozen-after.json').read_text())
logs=D/'replay/extracted/logs';audit=next(logs.glob('*-audit.log'));a=audit.read_text()
assert 'CLOSURE_EQUALS_AUDITED 27' in a and 'violations 0' in a
n=int(re.search(r'AUDIT_TOTAL (\d+)',a)[1]); kinds=collections.Counter(re.findall(r'kind=(\w+)',a))
receipts=[json.loads(p.read_text()) for p in logs.glob('*.receipt.json')];assert len(receipts)==60 and all(p['cap_reason'] is None for p in receipts)
for f,h in m['files'].items():assert sha(D/f)==h
mods=[]
for name in m['modules']:
 p=D/'PDTAR'/(name+'.lean')
 origin='new r3'
 for lane in ['r1','r2b','r2a']:
  if name+'.lean' in before[lane]['modules']:origin='frozen r1' if name in ['Defs','Basic','FortDuality','KstFamily','Core','Remaining'] else lane;break
 mods.append(dict(module='PDTAR.'+name,path=str(p.relative_to(D)),sha256=sha(p),lines=len(p.read_text().splitlines()),origin=origin,strict_compile=True,leanchecker=True))
neg=[]
for entry in s['steps']:
 if '-Neg' in entry['name']:
  text=(logs/(entry['name']+'.log')).read_text()
  assert 'unsolved goals' in text and '⊢' in text,(entry['name'],text)
  neg.append(dict(name=entry['name'].split('-')[-1],log='replay/extracted/logs/'+entry['name']+'.log',returncode=entry['returncode'],false_claim_rejected=True))
assert len(neg)==5
artifacts=['pdtar-source.zip','manifest.json','module-order.json','frozen-before.json','frozen-after.json','replay-state.json','STATEMENT-CORRESPONDENCE.md','REPRODUCE.md','NEXT-ROUND.md']
r=dict(lane='pdtar-formal-r3',mathdb_id=353203,status='PARTIAL_TWO_WITNESS_CLOSED_TWO_RIGIDITY_PROPS_OPEN',self_accepted=False,credit_claimed=0,
 endpoint=dict(unconditional_name='PDTAR.mathdb_353203',unconditional_declared=False,conditional_name='PDTAR.mathdb_353203_conditional',exact_remaining_hypotheses=['PDTAR.StarRigidityRemaining','PDTAR.ThreeThreeRigidityRemaining'],reduction_assumed=False,core_assumed=False,two_witness_assumed=False),
 targets=dict(starRigidityRemaining=False,threeThreeRigidityRemaining=False,twoWitnessRemaining=True),
 modules=mods,total_lean_lines=sum(x['lines'] for x in mods),new_modules=[x['module'] for x in mods if x['origin']=='new r3'],
 frozen_and_sibling_hashes_before=before,frozen_and_sibling_hashes_after=after,merged_inherited_byte_identical=True,
 merge=dict(base_modules=6,r2b_reduction_modules=7,r2a_modules=10,inherited_total=23,module_name_collisions=False,optional_r1_modules_excluded=['PDTAR.Endpoint','PDTAR.Fidelity'],initial_strict_rebuild_before_new_modules=True,initial_build_logs='logs/*-build-*.log'),
 toolchain=dict(lean='4.34.1',mathlib_revision=m['mathlib_revision'],pins=m['pins'],read_only_cache=True),
 validation=dict(fresh_extraction='replay/extracted',steps_completed=s['next'],steps_total=60,strict_rebuild_modules=27,leanchecker_modules=27,audit_total=n,audit_kinds=dict(kinds),audit_violations=0,audit_generated_declarations=True,audit_checks=['unsafe','partial','_unsafe_rec','implemented_by','extern','transitive axioms'],audited_modules=m['modules'],closure_equals_audited=True,closure_modules=27,audit_log=str(audit.relative_to(D)),allowed_axioms=['propext','Classical.choice','Quot.sound'],negative_controls=neg,peak_sampled_process_rss_bytes=max(x['sampled_process_rss_peak_bytes'] for x in receipts),max_step_wall_seconds=max(x['wall_seconds'] for x in receipts),limits='2 CPUs; CPU 120 s; wall 140 s; sampled RSS 6 GiB; MALLOC_ARENA_MAX=2; -j1 -M3500; serial',rss_sampling_seconds=.05,unsampled_transients_excluded=False),
 proof_route='Uniform PD family for arbitrary t >= 1; added edge joins the two-vertex side; triangle obstruction to graph isomorphism; explicit part-swap transport.',
 deviations=['Non-isomorphism uses a triangle obstruction instead of edge counting.','Two rigidity obligations remain open; the authorized partial-round fallback is used.'],
 artifacts={p:dict(path=p,sha256=sha(D/p)) for p in artifacts},
 child_agents=False,git_operations=False,external_actions=False,shared_ledger_edits=False,background_jobs_remaining=False,utc=time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime()))
(D/'results.json').write_text(json.dumps(r,indent=2)+'\n')
print('Audit',n,'declarations;',dict(kinds),'negatives',len(neg),'all checks passed; partial endpoint')
