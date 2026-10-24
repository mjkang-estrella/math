#!/usr/bin/env python3
"""Register the actual distinct Structural214 dispatch, preserving all existing work."""
from pathlib import Path
import copy,datetime,hashlib,json,os
P=Path(__file__).resolve().parent; C=P.parent; PROJECT=C.parents[2]
read=lambda p:json.loads(p.read_bytes()); sha=lambda b:hashlib.sha256(b).hexdigest()
d=read(P/'dispatch.json'); br=read(P/'brief-record.json'); isolation=read(P/'prospective-isolation.json')
owner='164b1204-be68-4540-94bb-0b91055c4381'; now=datetime.datetime.now(datetime.timezone.utc).isoformat()
assert read(P/'runtime.json')['parentThreadId']==isolation['parent_thread']==owner
assert d['status'] in ['queued','running'] and d['providerInstanceId']=='codex' and d['model']=='gpt-6-astra'
assert {e['id']:e['value'] for e in d['options']}=={'reasoningEffort':'xhigh','serviceTier':'default'}
assert sha((PROJECT/br['brief']).read_bytes())==br['brief_sha256']
assert isolation['root_and_brief_absent_when_checked'] and all(e['present'] for e in isolation['initial_brief_checks_before_new_root_or_brief'])
registry=C/'tasks.json'; ledger=PROJECT/'frontier/NEW-TEN-2026-10-14.md'; raw=registry.read_bytes(); lr=ledger.read_bytes()
t=json.loads(raw); old=copy.deepcopy(t)
assert (t['newAccepted'],t['latestAcceptance'],t['remaining'])==(19,'R041',1)
assert t['tasks'][736]['parent_disposition']=='ARCHIVED_PREFREEZE_NO_NOMINEE'
assert not any(e.get('taskId')==d['taskId'] or e.get('brief')==br['brief'] for e in t['tasks'])
idx=len(t['tasks'])
entry=dict(d,parent_thread=owner,role='discovery',round=214,clientRequestId='twenty-20261023-fresh-structural-r214-codex-astra-r1',source_index=338,source_title='positive bisectional curvature and Kähler uniformization',output='frontier/campaigns/2026-10-14/fresh-structural-discovery-r214/',brief=br['brief'],brief_sha256=br['brief_sha256'],brief_bytes=br['brief_bytes'],parent_count_at_dispatch=19,accepted=False,count_change=0,publication='STOPPED',dispatch_receipt='discovery-structural-r214-parent/dispatch.json',prospective_isolation='discovery-structural-r214-parent/prospective-isolation.json',status_provenance='Actual async dispatch response only; no subsequent liveness poll.',parent_full_intake_pending=True)
assert entry['output'].rstrip('/')==isolation['new_root']; t['tasks'].append(entry)
note='Structural213 archived PREFREEZE/no nominee, zero count. Distinct Structural214 discovery dispatched on Source338 positive bisectional curvature and Kähler uniformization, Codex/GPT-6 Astra/xhigh/default. No theorem or grade yet. Campaign 19/20, latest R041, one remaining; publication STOPPED. Existing and foreign task records preserved.'
t['last_parent_progress']=note; s=t['current_work_snapshot']; s.update(observed_utc=now,note=note)
s['structural214_dispatch']={'task_index':idx,'taskId':d['taskId'],'status':d['status'],'source_index':338,'brief':br['brief'],'brief_sha256':br['brief_sha256'],'output':entry['output'],'dispatch_receipt':entry['dispatch_receipt'],'count_change':0}
if 'active_task_indices' in s:s['active_task_indices']=[*s['active_task_indices'],idx]
if 't3_last_polled_running' in s:s['t3_last_polled_running']=[*s['t3_last_polled_running'],d['taskId']]
assert t['tasks'][:-1]==old['tasks']
assert all(t[k]==old[k] for k in old if k not in ['tasks','current_work_snapshot','last_parent_progress'])
assert all(s[k]==v for k,v in old['current_work_snapshot'].items() if k not in ['observed_utc','note','active_task_indices','t3_last_polled_running'])
heading='## Structural214 distinct discovery dispatched: Source338 positive bisectional curvature and Kähler uniformization'; assert heading.encode() not in lr
append='\n## Structural214 distinct discovery dispatched: Source338 positive bisectional curvature and Kähler uniformization\n\nFollowing Structural213’s PREFREEZE/no-nominee archive, a distinct discovery task was dispatched on Source338, uniformization of complete Kähler manifolds with strictly positive holomorphic bisectional curvature. The actual async response confirms **Codex / GPT-6 Astra / xhigh / default**, matching fresh live descriptors. See [complete brief](campaigns/2026-10-14/expanded-target-2026-10-17/fresh-structural-r214-brief.txt) and [dispatch receipt](campaigns/2026-10-14/discovery-structural-r214-parent/dispatch.json).\n\nBefore creating the namespace, parent checked original initial foreign-brief hashes and literal structural214 guards using shared coordination metadata only. All 349 inherited wildcard/no-r patterns and 162 substring exclusions remain; the new pair brings the explicit total to 351. Administrative-heading rejection remains. External-primary selection now explicitly stops at intervening editorial headings and selects any later mathematical appendix separately. No foreign liveness or mathematical body was inspected. Only the exact Source338 catalogue span was displayed; its canonical family has one folder, 16 entries and 14 blobs. Parent read no source theorem/proof body and establishes no history clearance.\n\nThe task must read all operative source, primary and guarded original-history interfaces, complete the strongest compatible construction and then freeze and prove a viable full theorem. Direct complex-Euclidean transfers and source/classical compositions do not alone count. Geometric control, equivariance, parameter dependence and weaker curvature assumptions each require their exact additional compatibility proofs if pursued. No theorem, grade, acceptance or count is assigned. **19/20, latest R041, one remaining; publication STOPPED.**\n'
assert registry.read_bytes()==raw and ledger.read_bytes()==lr
tmp=registry.with_suffix('.structural214.tmp'); tmp.write_text(json.dumps(t,indent=2)+'\n'); assert registry.read_bytes()==raw; os.replace(tmp,registry)
assert ledger.read_bytes()==lr; ledger.write_bytes(lr+append.encode())
out={'observed_utc':now,'added_task_index':idx,'taskId':d['taskId'],'all_previous_tasks_unchanged':True,'foreign_snapshot_entries_preserved':True,'count_change':0,'status_from_actual_dispatch_only':True}
(P/'integration-record.json').write_text(json.dumps(out,indent=2)+'\n'); print(json.dumps(out,indent=2))
