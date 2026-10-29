import hashlib,json
from pathlib import Path
r=Path(__file__).resolve().parent
before=json.loads((r/'inputs-before.json').read_text());after=json.loads((r/'inputs-after.json').read_text())
assert before==after
replay=json.loads((r/'replay-fresh/replay-receipt.json').read_text())
assert replay['status']=='PARTIAL_COMPONENT_SOURCE_ONLY_REPLAY_PASS'
archive=json.loads((r/'archive-receipt.json').read_text())
assert archive['sha256']==replay['archive_sha256']
axs=sorted(set(a for d in replay['declarations'] for a in d['axioms']))
assert set(axs)<={'propext','Classical.choice','Quot.sound'}
out={'status':'INCOMPLETE','full_target_proved':False,'source_claim_pass':False,
 'candidate_credit':0,'archive':archive,'fresh_replay_receipt':'replay-fresh/replay-receipt.json',
 'declaration_count':replay['declaration_count'],'axiom_union':axs,
 'actual_type_origin_axiom_safety_audit':'PASS for the partial component only',
 'frozen_inputs_unchanged_between_recorded_snapshots':True,
 'max_final_replay_group_rss_kib':max(s['peak_group_rss_kib'] for s in replay['steps']),
 'guard_sha256':hashlib.sha256((r/'guard.py').read_bytes()).hexdigest(),
 'helper_guard_sha256':hashlib.sha256((r/'helper_guard.py').read_bytes()).hexdigest(),
 'open_obligations':['tail-deficit identity for actual tent moment',
 'convolution moment algebra and strict comparison','exponential baseline integrals',
 'literal entropy inequality and unconditional source threshold negation']}
(r/'FINAL-RECEIPT.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
