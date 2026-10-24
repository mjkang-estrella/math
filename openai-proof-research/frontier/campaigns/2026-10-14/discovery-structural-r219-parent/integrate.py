#!/usr/bin/env python3
"""Register the actual distinct Structural219 dispatch, preserving existing tasks."""
from pathlib import Path
import copy, datetime, hashlib, json, os
P=Path(__file__).resolve().parent; C=P.parent; PROJECT=C.parents[2]
read=lambda p:json.loads(p.read_bytes()); sha=lambda b:hashlib.sha256(b).hexdigest()
d=read(P/'dispatch.json'); br=read(P/'brief-record.json'); iso=read(P/'prospective-isolation.json')
owner='164b1204-be68-4540-94bb-0b91055c4381'; now=datetime.datetime.now(datetime.timezone.utc).isoformat()
assert read(P/'runtime.json')['parentThreadId']==owner
assert d['status'] in ['queued','running'] and d['providerInstanceId']=='codex' and d['model']=='gpt-6-astra'
assert {e['id']:e['value'] for e in d['options']}=={'reasoningEffort':'xhigh','serviceTier':'default'}
assert sha((PROJECT/br['brief']).read_bytes())==br['brief_sha256']
assert len(iso['paths_absent_before_creation'])==3 and all(e['literal_present'] for e in iso['foreign_initial_brief_checks'])
registry=C/'tasks.json'; ledger=PROJECT/'frontier/NEW-TEN-2026-10-14.md'
raw=registry.read_bytes(); lr=ledger.read_bytes(); t=json.loads(raw); old=copy.deepcopy(t)
assert (t['newAccepted'],t['latestAcceptance'],t['remaining'])==(19,'R041',1)
assert t['tasks'][747]['parent_disposition']=='CLOSED_PASS_TECHNICAL'
assert not any(e.get('taskId')==d['taskId'] or e.get('brief')==br['brief'] for e in t['tasks'])
idx=len(t['tasks'])
entry=dict(d,parent_thread=owner,role='discovery',round=219,clientRequestId='twenty-20261024-fresh-structural-r219-codex-astra-r1',source_index=343,source_title='higher-dimensional symplectic ball packing',output='frontier/campaigns/2026-10-14/fresh-structural-discovery-r219/',brief=br['brief'],brief_sha256=br['brief_sha256'],brief_bytes=br['brief_bytes'],parent_count_at_dispatch=19,accepted=False,count_change=0,publication='STOPPED',dispatch_receipt='discovery-structural-r219-parent/dispatch.json',prospective_isolation='discovery-structural-r219-parent/prospective-isolation.json',status_provenance='Actual async dispatch response only; no subsequent liveness poll.',parent_full_intake_pending=True)
assert entry['output'].rstrip('/') in iso['paths_absent_before_creation']; t['tasks'].append(entry)
note='Structural218 closed full-scope PASS/TECHNICAL, full correctness condition discharged, zero count. Distinct Structural219 discovery dispatched on Source343 higher-dimensional symplectic ball packing, Codex/GPT-6 Astra/xhigh/default. No theorem or grade yet. Campaign 19/20, latest R041, one remaining; publication STOPPED. Existing foreign records preserved.'
t['last_parent_progress']=note; s=t['current_work_snapshot']; s.update(observed_utc=now,note=note)
s['structural219_dispatch']={'task_index':idx,'taskId':d['taskId'],'status':d['status'],'source_index':343,'brief':br['brief'],'brief_sha256':br['brief_sha256'],'output':entry['output'],'dispatch_receipt':entry['dispatch_receipt'],'count_change':0}
if 'active_task_indices' in s: s['active_task_indices']=[*s['active_task_indices'],idx]
if 't3_last_polled_running' in s: s['t3_last_polled_running']=[*s['t3_last_polled_running'],d['taskId']]
assert t['tasks'][:-1]==old['tasks']
assert all(t[k]==old[k] for k in old if k not in ['tasks','current_work_snapshot','last_parent_progress'])
assert all(s[k]==v for k,v in old['current_work_snapshot'].items() if k not in ['observed_utc','note','active_task_indices','t3_last_polled_running'])
heading='## Structural219 distinct discovery dispatched: Source343 symplectic ball packing'; assert heading.encode() not in lr
append='\n## Structural219 distinct discovery dispatched: Source343 symplectic ball packing\n\nFollowing Structural218’s full-scope PASS/TECHNICAL closure, a distinct discovery task was dispatched on Source343, symplectic ball packing in higher dimensions. The actual async response confirms **Codex / GPT-6 Astra / xhigh / default**, matching fresh live descriptors. See [complete brief](campaigns/2026-10-14/expanded-target-2026-10-17/fresh-structural-r219-brief.txt) and [dispatch receipt](campaigns/2026-10-14/discovery-structural-r219-parent/dispatch.json).\n\nBefore creating the namespace, parent checked original initial foreign-brief hashes and literal structural219 guards using the union of active snapshot and explicit foreign-parent queued/running/waiting registry metadata only. All359 inherited wildcard/no-r patterns and162 substring exclusions remain; the new pair brings the explicit total to361. Existing administrative/primary guards remain, with masked editorial classification and lettered subsection boundaries made explicit. No foreign liveness or mathematical body was inspected. Exact Source343 catalogue bytes[577254,578403) were displayed after bounded heading navigation. The canonical family has18 tree entries including its folder and14 blobs. Parent read no source theorem/proof body and establishes no history clearance.\n\nThe task must read all actual operative geometry, surface, six-dimensional, comparison and application mechanisms, strongest primary interfaces and eligible original history before freezing any target. The supplied arbitrary-capacity packing criterion and all internal constructions are paid; strict inequalities, neighborhood embeddings of closed sources and the dimension range must be preserved. Any new parametric, relative, infinite or quantitative result needs its actual distinct proved operation. Structural218 remains closed and excluded. No theorem, grade, acceptance or count is assigned. **19/20, latest R041, one remaining; publication STOPPED.**\n'
assert registry.read_bytes()==raw and ledger.read_bytes()==lr
tmp=registry.with_suffix('.structural219.tmp'); tmp.write_text(json.dumps(t,indent=2)+'\n')
assert registry.read_bytes()==raw; os.replace(tmp,registry)
assert ledger.read_bytes()==lr; ledger.write_bytes(lr+append.encode())
out={'observed_utc':now,'added_task_index':idx,'taskId':d['taskId'],'all_previous_tasks_unchanged':True,'foreign_snapshot_entries_preserved':True,'count_change':0,'status_from_actual_dispatch_only':True}
(P/'integration-record.json').write_text(json.dumps(out,indent=2)+'\n'); print(json.dumps(out,indent=2))
