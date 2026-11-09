from pathlib import Path
import json,hashlib,datetime,os
R=Path.cwd()
before=json.loads((R/'receipts/input-before.json').read_text())
after={p:hashlib.sha256(Path(p).read_bytes()).hexdigest() for p in before}
(R/'receipts/input-after.json').write_text(json.dumps(after,indent=2));assert before==after
(R/'receipts/input-integrity.json').write_text(json.dumps({'unchanged':True,'files':len(before)},indent=2))
receipts=[]
for p in (R/'receipts').glob('*.json'):
 j=json.loads(p.read_text())
 if 'peak_private_rss' in j:receipts.append((p.name,j))
positive=[j for n,j in receipts if j['exit']==0]
stats={'positive_calls':len(positive),'peak_private_rss_bytes':max(j['peak_private_rss'] for j in positive),'maximum_wall_seconds':max(j['seconds'] for j in positive),'all_calls_without_watchdog_termination':all(j['termination'] is None for n,j in receipts)}
assert stats['all_calls_without_watchdog_termination']
report={'381433':{'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'role':'independent adversarial reviewer; not acceptance','credit':0,'gates':{'A':{'verdict':'QUALIFIED_PASS','reason':'Survey definitions match; stricter noncomplete source restatement kernel checked; unavailable original/final versions remain qualified.'},'B':{'verdict':'PASS','reason':'Own exact arithmetic confirms Gram identity, all deletion witnesses, alpha 5, upsilon 6, lambda_min -3.'},'C':{'verdict':'PASS','reason':'Fresh strict replay and leanchecker for all 13 packet proof modules plus reviewer; all 167 declarations audited; four negative controls rejected.','resource_stats':stats},'D':{'verdict':'HOLD','reason':'Lawful alternate-route attempts did not obtain material Luz 2019 body; final-version, citation and complete current registry coverage gaps remain.'},'E':{'verdict':'HOLD','reason':'Literal substantive conjecture refutation, but classical ingredients and simple deletion argument demand subsumption/significance adjudication after decisive literature clearance.'}},'objections':['Luz 2019 unread: decisive novelty gate not cleared.','No complete current registry content clearance under commits/HEAD-only access.','Other unread/final-version bodies explicitly listed in REVIEW.md.','Significance is not implied by a correct Lean proof; classical Latin-square/Hoffman ingredients require careful subsumption review.'],'recommendation':'HOLD; retain as a mathematically and formally verified candidate, zero campaign credit pending root ruling.','next_actions':['Obtain lawful readable Luz 2019 body or keep HOLD.','Compare full criteria and examples with the independently verified witness.','Resolve remaining final-version/citation and current registry content gaps within authorized routes.','Root adjudicates significance and acceptance; no parameter-variant padding.'],'inputs_unchanged':True,'packet_sha256':'aefc4cc7ea17aa2ae0797a739ee8ec40b56097c281e0435f403c4e93de47420b','reviewer_endpoint':'IndependentReview.refutes_stricter_source','report':'REVIEW.md','background_jobs_remaining':False}}
(R/'review.json').write_text(json.dumps(report,indent=2)+'\n')
(R/'receipts/process-handback.json').write_text(json.dumps({'task_subprocess_groups_reaped':True,'background_jobs_remaining':False,'external_processes_untouched':True},indent=2))
print(json.dumps(stats,indent=2))
