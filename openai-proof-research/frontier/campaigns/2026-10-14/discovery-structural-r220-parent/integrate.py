#!/usr/bin/env python3
"""Register actual distinct Structural220 dispatch; preserve all prior tasks."""
from pathlib import Path
import copy,datetime,hashlib,json,os
P=Path(__file__).resolve().parent;C=P.parent;PROJECT=C.parents[2]
read=lambda p:json.loads(p.read_bytes());sha=lambda b:hashlib.sha256(b).hexdigest()
d=read(P/'dispatch.json');br=read(P/'brief-record.json');iso=read(P/'prospective-isolation.json')
owner='164b1204-be68-4540-94bb-0b91055c4381';now=datetime.datetime.now(datetime.timezone.utc).isoformat()
assert read(P/'runtime.json')['parentThreadId']==owner
assert d['status'] in ['queued','running'] and d['providerInstanceId']=='codex' and d['model']=='gpt-6-astra'
assert {e['id']:e['value'] for e in d['options']}=={'reasoningEffort':'xhigh','serviceTier':'default'}
assert sha((PROJECT/br['brief']).read_bytes())==br['brief_sha256']
assert len(iso['paths_absent_before_creation'])==3 and all(e['literal_present'] for e in iso['foreign_initial_brief_checks'])
registry=C/'tasks.json';ledger=PROJECT/'frontier/NEW-TEN-2026-10-14.md'
raw=registry.read_bytes();lr=ledger.read_bytes();t=json.loads(raw);old=copy.deepcopy(t)
assert (t['newAccepted'],t['latestAcceptance'],t['remaining'])==(19,'R041',1)
assert t['tasks'][750]['parent_disposition']=='ARCHIVED_PREFREEZE_NO_NOMINEE'
assert not any(e.get('taskId')==d['taskId'] or e.get('brief')==br['brief'] for e in t['tasks'])
idx=len(t['tasks'])
entry=dict(d,parent_thread=owner,role='discovery',round=220,clientRequestId='twenty-20261024-fresh-structural-r220-codex-astra-r1',source_index=344,source_title='metric Blaschke theorem',output='frontier/campaigns/2026-10-14/fresh-structural-discovery-r220/',brief=br['brief'],brief_sha256=br['brief_sha256'],brief_bytes=br['brief_bytes'],parent_count_at_dispatch=19,accepted=False,count_change=0,publication='STOPPED',dispatch_receipt='discovery-structural-r220-parent/dispatch.json',prospective_isolation='discovery-structural-r220-parent/prospective-isolation.json',status_provenance='Actual async dispatch response only; no subsequent liveness poll.',parent_full_intake_pending=True)
assert entry['output'].rstrip('/') in iso['paths_absent_before_creation'];t['tasks'].append(entry)
note='Structural219 archived PREFREEZE/no nominee with derivations and limitations preserved, zero count. Distinct Structural220 discovery dispatched on Source344 metric Blaschke theorem, Codex/GPT-6 Astra/xhigh/default. No theorem or grade yet. Campaign 19/20, latest R041, one remaining; publication STOPPED. Existing foreign records preserved.'
t['last_parent_progress']=note;s=t['current_work_snapshot'];s.update(observed_utc=now,note=note)
s['structural220_dispatch']={'task_index':idx,'taskId':d['taskId'],'status':d['status'],'source_index':344,'brief':br['brief'],'brief_sha256':br['brief_sha256'],'output':entry['output'],'dispatch_receipt':entry['dispatch_receipt'],'count_change':0}
if 'active_task_indices' in s:s['active_task_indices']=[*s['active_task_indices'],idx]
if 't3_last_polled_running' in s:s['t3_last_polled_running']=[*s['t3_last_polled_running'],d['taskId']]
assert t['tasks'][:-1]==old['tasks']
assert all(t[k]==old[k] for k in old if k not in ['tasks','current_work_snapshot','last_parent_progress'])
assert all(s[k]==v for k,v in old['current_work_snapshot'].items() if k not in ['observed_utc','note','active_task_indices','t3_last_polled_running'])
heading='## Structural220 distinct discovery dispatched: Source344 metric Blaschke theorem';assert heading.encode() not in lr
append='\n'+heading+'\n\nFollowing Structural219’s non-nominee archive, a distinct discovery task was dispatched on Source344, the metric Blaschke theorem. The actual async response confirms **Codex / GPT-6 Astra / xhigh / default**, matching fresh live descriptors. See [complete brief](campaigns/2026-10-14/expanded-target-2026-10-17/fresh-structural-r220-brief.txt) and [dispatch receipt](campaigns/2026-10-14/discovery-structural-r220-parent/dispatch.json).\n\nBefore creating the namespace, parent checked original initial foreign-brief hashes and literal structural220 guards using the union of active snapshot and explicit foreign-parent queued/running/waiting registry metadata only. All361 inherited wildcard/no-r patterns and162 substring exclusions remain; the new pair brings the explicit total to363. Administrative and primary boundary guards remain, with primed subresults and adjacent introductions made explicit. No foreign liveness or mathematical body was inspected. Exact Source344 catalogue bytes[578403,579066) were displayed after bounded heading navigation. The canonical family has20 tree entries including its folder and16 blobs. Parent read no source theorem/proof body and establishes no history clearance.\n\nThe task must read all actual operative geometric, Lagrangian, weighted/global comparison, incidence, signature, geodesic-space, volume-algebra and classification mechanisms, strongest primary interfaces and eligible original history before freezing any target. The supplied classification and internal operations are paid; routine invariant transfers, weak-limit assumptions or pointwise-to-parametric upgrades do not themselves supply a substantial proved operation. Structural219 remains archived and excluded. No theorem, grade, acceptance or count is assigned. **19/20, latest R041, one remaining; publication STOPPED.**\n'
assert registry.read_bytes()==raw and ledger.read_bytes()==lr
tmp=registry.with_suffix('.structural220.tmp');tmp.write_text(json.dumps(t,indent=2)+'\n');assert registry.read_bytes()==raw;os.replace(tmp,registry)
assert ledger.read_bytes()==lr;ledger.write_bytes(lr+append.encode())
out={'observed_utc':now,'added_task_index':idx,'taskId':d['taskId'],'all_previous_tasks_unchanged':True,'foreign_snapshot_entries_preserved':True,'count_change':0,'status_from_actual_dispatch_only':True}
(P/'integration-record.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
