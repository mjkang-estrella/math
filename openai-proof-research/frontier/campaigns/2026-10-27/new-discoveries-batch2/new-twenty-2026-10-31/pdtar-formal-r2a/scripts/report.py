import pathlib,json,hashlib,re,collections
D=pathlib.Path(__file__).resolve().parents[1]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
m=json.loads((D/'manifest.json').read_text());s=json.loads((D/'replay-state.json').read_text())
assert s['next']==36
log=(D/'replay/extracted/logs/audit.log').read_text()
total=int(re.search(r'AUDIT_TOTAL (\d+); violations 0',log)[1])
mods=[]
for n in m['modules']:
 p=D/f'PDTAR/{n}.lean'
 mods.append(dict(module='PDTAR.'+n,path=str(p.relative_to(D)),sha256=sha(p),lines=len(p.read_text().splitlines()),strict_compile=True,leanchecker=True))
b=json.loads((D/'frozen-before.json').read_text());a={n:sha(D/'PDTAR'/n) for n in b};assert b==a
(D/'frozen-after.json').write_text(json.dumps(a,indent=2)+'\n')
receipts=[json.loads(p.read_text()) for p in (D/'replay/extracted/logs').glob('*.receipt.json')]
r=dict(lane='pdtar-formal-r2a',mathdb_id=353203,status='PARTIAL_CORE_COMPLETE_SMALL_CASES_OPEN_NOT_SELF_ACCEPTED',credit_claimed=0,
 endpoint={'literal_endpoint_closed':False,'reduction_only_endpoint_closed':False,'conditional_name':'PDTAR.mathdb_353203_of_reduction_conditional','additional_explicit_hypotheses':['StarRigidityRemaining','ThreeThreeRigidityRemaining','TwoWitnessRemaining'],'reduction_explicit_hypothesis':'ReductionRemaining'},
 target_status={
 'coreRemaining':{'closed':True,'signature':'CoreRemaining','reduction_required':False},
 'twoRemaining':{'closed':False,'conditional':'PDTAR.twoRemaining_conditional','remaining_prop':'TwoWitnessRemaining'},
 'edgeRemaining_of_reduction':{'closed':True,'signature':'(hR : ReductionRemaining) : EdgeRemaining'},
 'starsRemaining_of_reduction':{'closed':False,'conditional':'PDTAR.starsRemaining_of_reduction_conditional','remaining_prop':'StarRigidityRemaining'},
 'threeThreeRemaining_of_reduction':{'closed':False,'conditional':'PDTAR.threeThreeRemaining_of_reduction_conditional','remaining_prop':'ThreeThreeRigidityRemaining'},
 'mathdb_353203_of_reduction':{'closed':False,'conditional':'PDTAR.mathdb_353203_of_reduction_conditional'}},
 remaining_props={'file':'PDTAR/SmallObligations.lean','names':['StarRigidityRemaining','ThreeThreeRigidityRemaining','TwoWitnessRemaining'],'exact_lean_source':(D/'PDTAR/SmallObligations.lean').read_text()},
 modules=mods,total_lean_lines=sum(x['lines'] for x in mods),new_lean_lines=sum(x['lines'] for x in mods[6:]),
 frozen_base={'input_archive':'../pdtar-formal-r1/pdtar-source.zip','input_archive_sha256':'39ebb60a1e30c558cc2a978dc423a27d3969006bbf21904a788f97a17b4b9b69','hashes_before':b,'hashes_after':a,'byte_identical':True},
 toolchain={'lean':'4.34.1','mathlib_revision_as_supplied':m['mathlib_revision'],'pins':m['pins'],'cache_read_only':True},
 validation={'fresh_extraction':'replay/extracted','serial_steps_completed':s['next'],'serial_steps_total':36,'strict_rebuild':True,'leanchecker_modules':16,'audit_total':total,'audit_kinds':dict(collections.Counter(re.findall(r'kind=(\w+)',log))),'audit_violations':0,'audit_includes_generated_declarations':True,'audit_checks':['unsafe flag','partial flag','_unsafe_rec name','implemented_by attribute','extern attribute','transitive axioms'],'allowed_axioms':['propext','Classical.choice','Quot.sound'],'negative_controls_passed':['empty fort','empty PD set for K(2,3)','omitting (3,3) exclusion from cross-degree theorem (interface check)'],'peak_sampled_process_rss_bytes':max(r['sampled_process_rss_peak_bytes'] for r in receipts),'max_step_wall_seconds':max(r['wall_seconds'] for r in receipts),'resource_cap_failures':sum(r['cap_reason'] is not None for r in receipts),'logs':'replay/extracted/logs','prior_replay':'replay-attempt1/extracted','prior_replay_note':'All mathematical builds, checks and audit passed. Final negative was correctly rejected but parser did not recognize Application type mismatch. Fixture changed to emit Type mismatch; fresh replay repeated all steps.','development_log_limitation':'Initial development log names were reused, overwriting failed development passes. All final replay logs and the entire first replay are retained. See SUMMARY.md.'},
 artifacts={'source_zip':{'path':'pdtar-source.zip','sha256':sha(D/'pdtar-source.zip')},'manifest':{'path':'manifest.json','sha256':sha(D/'manifest.json')},'replay_state':{'path':'replay-state.json','sha256':sha(D/'replay-state.json')},'audit_log':{'path':'replay/extracted/logs/audit.log','sha256':sha(D/'replay/extracted/logs/audit.log')}},
 next_round_plan='SUMMARY.md',reproduction='REPRODUCE.md',no_children=True,no_git_operations=True,no_external_messages=True,no_uploads=True,no_browser_tabs=True,no_network_requests=True)
inputs=['../pdtar-formal-r1/SUMMARY.md','../pdtar-formal-r1/results.json','../pdtar-formal-r1/STATEMENT-CORRESPONDENCE.md','../pdtar-proof-r1/PROOF.md','../pdtar-proof-r1/LEAN-PLAN.md','../pdtar-review-r1/REVIEW.md','../pdtar-proof-r1/sources/r119-cached/2201.01798-PD-recon.tex','../pdtar-proof-r1/sources/r119-cached/2406.05509-CFH24TARarxiv.tex']
r['source_reading_hashes']={n:sha(D/n) for n in inputs}
(D/'results.json').write_text(json.dumps(r,indent=2)+'\n')
print('REPORT',r['status'],'audit',total,'modules',len(mods))
