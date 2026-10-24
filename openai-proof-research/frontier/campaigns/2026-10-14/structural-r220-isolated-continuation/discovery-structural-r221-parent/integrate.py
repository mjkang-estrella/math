#!/usr/bin/env python3
"""Register actual distinct Structural221 dispatch; preserve every prior task."""
from pathlib import Path
import copy,datetime,fnmatch,hashlib,json,os
P=Path(__file__).resolve().parent;C=P.parents[1];PROJECT=C.parents[2]
read=lambda p:json.loads(p.read_bytes());sha=lambda b:hashlib.sha256(b).hexdigest()
d=read(P/'dispatch.json');br=read(P/'brief-record.json');iso=read(P/'prospective-isolation.json')
owner='164b1204-be68-4540-94bb-0b91055c4381';now=datetime.datetime.now(datetime.timezone.utc).isoformat()
assert read(P/'runtime.json')['parentThreadId']==owner
assert d['status'] in ['queued','running'] and d['providerInstanceId']=='codex' and d['model']=='gpt-6-astra'
assert {e['id']:e['value'] for e in d['options']}=={'reasoningEffort':'xhigh','serviceTier':'default'}
assert sha((PROJECT/br['brief']).read_bytes())==br['brief_sha256']
assert len(iso['paths_absent_before_creation'])==3 and all(e['literal_present'] for e in iso['foreign_initial_brief_checks'])
assert all(fnmatch.fnmatchcase(x.casefold(),iso['required_literal']) for x in iso['paths_absent_before_creation'])
registry=C/'tasks.json';ledger=PROJECT/'frontier/NEW-TEN-2026-10-14.md'
raw=registry.read_bytes();lr=ledger.read_bytes();t=json.loads(raw);old=copy.deepcopy(t)
assert (t['newAccepted'],t['latestAcceptance'],t['remaining'])==(19,'R041',1)
assert t['tasks'][751]['parent_disposition']=='CLOSED_PASS_TECHNICAL'
assert t['tasks'][752]['parent_disposition']=='ADOPTED_FULL_SCOPE_PASS'
assert t['tasks'][753]['parent_disposition']=='ADOPTED_TECHNICAL_CONDITION_DISCHARGED'
assert not any(e.get('taskId')==d['taskId'] or e.get('brief')==br['brief'] for e in t['tasks'])
idx=len(t['tasks']);parent_rel=str(P.relative_to(C))
entry=dict(d,parent_thread=owner,role='discovery',round=221,clientRequestId='twenty-20261024-fresh-structural-r221-codex-astra-r1',source_index=345,source_title='infinitely many closed geodesic images',output=br['output'],brief=br['brief'],brief_sha256=br['brief_sha256'],brief_bytes=br['brief_bytes'],parent_count_at_dispatch=19,accepted=False,count_change=0,publication='STOPPED',dispatch_receipt=parent_rel+'/dispatch.json',prospective_isolation=parent_rel+'/prospective-isolation.json',isolation_wrapper='structural-r220-isolated-continuation',foreign_initial_exclusion_literal='*structural*r220*',status_provenance='Actual async dispatch response only; no subsequent liveness poll.',parent_full_intake_pending=True)
assert entry['output'].rstrip('/') in iso['paths_absent_before_creation'];t['tasks'].append(entry)
note='Structural220 closed at its unchanged full scope: correctness PASS, contribution TECHNICAL, condition DISCHARGED, zero count; assumptions force B=I qualification retained. Distinct Structural221 discovery dispatched on Source345 closed-geodesic infinitude, Codex/GPT-6 Astra/xhigh/default, inside a fresh wrapper already covered by the foreign initial r220 full-path exclusion. No new theorem or grade yet. Campaign19/20,latestR041,one remaining; publication STOPPED. Existing foreign records preserved.'
t['last_parent_progress']=note;s=t['current_work_snapshot'];s.update(observed_utc=now,note=note)
s['structural221_dispatch']={'task_index':idx,'taskId':d['taskId'],'status':d['status'],'source_index':345,'brief':br['brief'],'brief_sha256':br['brief_sha256'],'output':entry['output'],'dispatch_receipt':entry['dispatch_receipt'],'isolation_wrapper':entry['isolation_wrapper'],'count_change':0}
if 'active_task_indices' in s:s['active_task_indices']=[*s['active_task_indices'],idx]
if 't3_last_polled_running' in s:s['t3_last_polled_running']=[*s['t3_last_polled_running'],d['taskId']]
assert t['tasks'][:-1]==old['tasks']
assert all(t[k]==old[k] for k in old if k not in ['tasks','current_work_snapshot','last_parent_progress'])
assert all(s[k]==v for k,v in old['current_work_snapshot'].items() if k not in ['observed_utc','note','active_task_indices','t3_last_polled_running'])
heading='## Structural221 distinct discovery dispatched: Source345 closed geodesics';assert heading.encode() not in lr
append='\n'+heading+'\n\nFollowing Structural220’s full-scope PASS/TECHNICAL closure, a distinct discovery task was dispatched on Source345, infinitely many closed geodesic images on Riemannian spheres and closed three-manifolds. The actual async response confirms **Codex / GPT-6 Astra / xhigh / default**, matching fresh live descriptors. See [complete brief](campaigns/2026-10-14/expanded-target-2026-10-17/fresh-structural-r220-isolated-r221-brief.txt) and [dispatch receipt](campaigns/2026-10-14/structural-r220-isolated-continuation/discovery-structural-r221-parent/dispatch.json).\n\nThe initial prospective check found that the foreign original INITIAL briefs did not contain the literal structural-r221 exclusion. No default r221 root or brief was created. Parent instead selected a fresh structural-r220-isolated-continuation wrapper and a separately named brief, verified that EVERY planned path matches the already-present literal *structural*r220*, and only then created the new namespace. This uses the existing full-path exclusion without altering foreign briefs or any sealed Structural220 files. Round221 is a distinct source family; the closed theorem is not reopened or renamed. Checks used only the union of snapshot active indices and explicit foreign-parent queued/running/waiting registry metadata, original INITIAL brief hashes and literal matching. No foreign liveness or mathematical body was inspected. [Prospective isolation record](campaigns/2026-10-14/structural-r220-isolated-continuation/discovery-structural-r221-parent/prospective-isolation.json).\n\nAll363 inherited wildcard/no-r patterns and162 substring exclusions remain, with the round221 pair bringing the explicit total to365. Exact Source345 catalogue bytes[579066,580287) were displayed after bounded heading navigation. The canonical family has21 tree entries including its folder and17 blobs. Parent read no source theorem/proof body and establishes no history clearance.\n\nThe task must read all actual operative source and companion proofs, strongest primary interfaces and eligible original history before freezing a target. Supplied infinitude, finite-cover and closed-three-manifold conclusions and internal operations are paid; counting, localization, persistence and changed-category claims require their full additional argument and compatibility analysis. Structural220 stays closed, including the qualification that its joint assumptions force B=I. No new theorem, grade, acceptance or count is assigned. **19/20, latest R041, one remaining; publication STOPPED.**\n'
assert registry.read_bytes()==raw and ledger.read_bytes()==lr
tmp=registry.with_suffix('.structural221.tmp');tmp.write_text(json.dumps(t,indent=2)+'\n');assert registry.read_bytes()==raw;os.replace(tmp,registry)
assert ledger.read_bytes()==lr;ledger.write_bytes(lr+append.encode())
out={'observed_utc':now,'added_task_index':idx,'taskId':d['taskId'],'all_previous_tasks_unchanged':True,'foreign_snapshot_entries_preserved':True,'count_change':0,'status_from_actual_dispatch_only':True,'all_new_paths_prospectively_covered_by_original_foreign_literal':True}
(P/'integration-record.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
