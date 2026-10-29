import hashlib,json,subprocess,sys
from pathlib import Path
r=Path(__file__).resolve().parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
frozen=subprocess.run([sys.executable,str(r/'verify_frozen.py')],capture_output=True,text=True)
assert frozen.returncode==0,frozen.stderr
(r/'frozen-after.json').write_text(frozen.stdout)
inputs=subprocess.run([sys.executable,str(r/'verify_inputs.py')],capture_output=True,text=True)
assert inputs.returncode==0,inputs.stderr
(r/'inputs-after.json').write_text(inputs.stdout)
assert json.loads(inputs.stdout)==json.loads((r/'inputs-before.json').read_text())
replay=json.loads((r/'replay-fresh/replay-receipt.json').read_text())
assert replay['status']=='FULL_DENSITY_ENDPOINT_SOURCE_ONLY_REPLAY_PASS'
assert replay['full_target_proved'] and replay['source_claim_pass']
archive=json.loads((r/'archive-receipt.json').read_text())
assert archive['sha256']==replay['archive_sha256']==sha(r/'component-source.zip')
axs=sorted(set(a for d in replay['declarations'] for a in d['axioms']))
assert set(axs)<={'propext','Classical.choice','Quot.sound'}
assert {'Renyi.deficit_identity','Renyi.convolution_moment','Renyi.exponential_admissible','Renyi.every_order_counterexample','Renyi.not_source_threshold'} <= {d['name'] for d in replay['declarations']}
out={'status':'FULL_DENSITY_ENDPOINT_PROVED_SOURCE_ONLY_REPLAY_PASS','full_target_proved':True,'source_claim_pass':True,'candidate_credit':0,'counts':[8,38],'root_review_and_integration_pending':True,'archive':archive,'fresh_replay_receipt':'replay-fresh/replay-receipt.json','fresh_replay_receipt_sha256':sha(r/'replay-fresh/replay-receipt.json'),'declaration_count':replay['declaration_count'],'mathematical_module_count':len(replay['modules']),'axiom_union':axs,'actual_type_origin_transitive_axiom_safety_audit':'PASS','initial_own_prebuilt_artifacts':replay['initial_own_prebuilt_artifacts'],'all_frozen_originals_unchanged':True,'all_eight_inherited_mathematical_modules_byte_identical':True,'max_final_replay_group_rss_kib':max(s['peak_group_rss_kib'] for s in replay['steps']),'max_single_build_seconds':max(s['seconds'] for s in replay['steps']),'guard_sha256':sha(r/'guard.py'),'helper_guard_sha256':sha(r/'helper_guard.py'),'replay_guard_sha256':sha(r/'replay_guard.py'),'open_formal_obligations':[]}
(r/'FINAL-RECEIPT.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
