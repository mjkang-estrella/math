#!/usr/bin/env python3
"""Register one actual async discovery dispatch; preserve all existing task records."""
from pathlib import Path
import copy,datetime,hashlib,json,os
P=Path(__file__).resolve().parent;C=P.parent;PROJECT=C.parents[2]
read=lambda p:json.loads(p.read_bytes());sha=lambda b:hashlib.sha256(b).hexdigest()
d=read(P/'dispatch.json');br=read(P/'brief-record.json');isolation=read(P/'prospective-isolation.json');owner='164b1204-be68-4540-94bb-0b91055c4381';now=datetime.datetime.now(datetime.timezone.utc).isoformat()
assert d['status']=='running' and d['providerInstanceId']=='codex' and d['model']=='gpt-6-astra'
assert {e['id']:e['value'] for e in d['options']}=={'reasoningEffort':'xhigh','serviceTier':'default'}
assert sha((PROJECT/br['brief']).read_bytes())==br['brief_sha256']
assert isolation['root_and_brief_absent_when_checked'] and all(e['present'] for e in isolation['initial_brief_checks_before_new_root_or_brief'])
registry=C/'tasks.json';ledger=PROJECT/'frontier/NEW-TEN-2026-10-14.md';raw=registry.read_bytes();t=json.loads(raw);old=copy.deepcopy(t);lr=ledger.read_bytes()
assert (t['newAccepted'],t['latestAcceptance'],t['remaining'])==(19,'R041',1)
assert t['tasks'][703]['parent_disposition']=='CLOSED_FULL_SCOPE_PASS_TECHNICAL_ZERO_COUNT'
assert not any(e.get('taskId')==d['taskId'] or e.get('brief')==br['brief'] for e in t['tasks'])
idx=len(t['tasks']);entry=dict(d,parent_thread=owner,role='discovery',round=204,clientRequestId='twenty-20261023-fresh-structural-r204-codex-astra-r1',source_index=328,source_title='Fixed Points of Nonexpansive Maps in Reflexive Banach Spaces',output='frontier/campaigns/2026-10-14/fresh-structural-discovery-r204/',brief=br['brief'],brief_sha256=br['brief_sha256'],brief_bytes=br['brief_bytes'],parent_count_at_dispatch=19,accepted=False,count_change=0,publication='STOPPED',dispatch_receipt='discovery-structural-r204-parent/dispatch.json',prospective_isolation='discovery-structural-r204-parent/prospective-isolation.json',status_provenance='Actual async dispatch response only; no subsequent liveness poll.',parent_full_intake_pending=True)
t['tasks'].append(entry)
note='Structural203 CLOSED full-scope PASS/TECHNICAL, condition DISCHARGED, zero count. Distinct Structural204 discovery dispatched on Source328 nonexpansive fixed points, Codex/GPT-6 Astra/xhigh/default. No author theorem or grade yet. Campaign19/20 latestR041 one remains; publicationSTOPPED. All prior and foreign task records preserved.'
t['last_parent_progress']=note;s=t['current_work_snapshot'];s.update(observed_utc=now,note=note)
s['structural204_dispatch']={'task_index':idx,'taskId':d['taskId'],'status':d['status'],'source_index':328,'brief':br['brief'],'brief_sha256':br['brief_sha256'],'output':entry['output'],'dispatch_receipt':entry['dispatch_receipt'],'count_change':0}
if 'active_task_indices' in s:s['active_task_indices']=[*s['active_task_indices'],idx]
if 't3_last_polled_running' in s:s['t3_last_polled_running']=[*s['t3_last_polled_running'],d['taskId']]
assert t['tasks'][:-1]==old['tasks']
assert all(t[k]==old[k] for k in old if k not in ['tasks','current_work_snapshot','last_parent_progress'])
assert all(s[k]==v for k,v in old['current_work_snapshot'].items() if k not in ['observed_utc','note','active_task_indices','t3_last_polled_running'])
heading='## Structural204 distinct discovery dispatched: Source328 nonexpansive fixed points'
assert heading.encode() not in lr
append='\n'+heading+'\n\nAfter Structural203 closed unchanged at PASS/TECHNICAL with zero count, parent dispatched one distinct discovery task on Source328, Fixed Points of Nonexpansive Maps in Reflexive Banach Spaces. The actual async response selects **Codex / GPT-6 Astra / xhigh / default**, matching the live model descriptors and inherited options. See [complete brief](campaigns/2026-10-14/expanded-target-2026-10-17/fresh-structural-r204-brief.txt) and [dispatch receipt](campaigns/2026-10-14/discovery-structural-r204-parent/dispatch.json).\n\nBefore creation, literal structural204 guards were verified in the original initial foreign briefs identified by shared coordination metadata, using hashes/literal checks only. All 172 inherited wildcard literals, their no-r twins (335 explicit patterns total), every substring guard and all closed targets remain protected. No foreign mathematical body or liveness was inspected. Parent selected only the exact Source328 catalogue slice and complete-tree metadata: one canonical folder, 15 entries/12 blobs. Actual proof/interface, primary and guarded original-history reading remains the discovery agent’s work; no parent semantic source reading or history clearance is claimed.\n\nThe task must identify a proved additional operation after the strongest compatible source/classical reduction, preserve any frozen scope, and return a full author-proof nominee or honest PREFREEZE/no nominee. No grade or count is assigned. **19/20, latest R041, one remaining; publication STOPPED.**\n'
assert registry.read_bytes()==raw and ledger.read_bytes()==lr
tmp=registry.with_suffix('.structural204.tmp');tmp.write_text(json.dumps(t,indent=2)+'\n');assert registry.read_bytes()==raw;os.replace(tmp,registry)
assert ledger.read_bytes()==lr;ledger.write_bytes(lr+append.encode())
out={'observed_utc':now,'added_task_index':idx,'taskId':d['taskId'],'all_previous_tasks_unchanged':True,'foreign_snapshot_entries_preserved':True,'count_change':0,'status_from_actual_dispatch_only':True}
(P/'integration-record.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
