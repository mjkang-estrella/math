#!/usr/bin/env python3
"""Register one actual async discovery dispatch; preserve all existing task records."""
from pathlib import Path
import copy,datetime,hashlib,json,os
P=Path(__file__).resolve().parent;C=P.parent;PROJECT=C.parents[2]
read=lambda p:json.loads(p.read_bytes());sha=lambda b:hashlib.sha256(b).hexdigest()
d=read(P/'dispatch.json');br=read(P/'brief-record.json');isolation=read(P/'prospective-isolation.json');owner='164b1204-be68-4540-94bb-0b91055c4381';now=datetime.datetime.now(datetime.timezone.utc).isoformat()
assert read(P/'runtime.json')['parentThreadId']==isolation['parent_thread']==owner
assert d['status']=='running' and d['providerInstanceId']=='codex' and d['model']=='gpt-6-astra'
assert {e['id']:e['value'] for e in d['options']}=={'reasoningEffort':'xhigh','serviceTier':'default'}
assert sha((PROJECT/br['brief']).read_bytes())==br['brief_sha256']
assert isolation['root_and_brief_absent_when_checked'] and all(e['present'] for e in isolation['initial_brief_checks_before_new_root_or_brief'])
registry=C/'tasks.json';ledger=PROJECT/'frontier/NEW-TEN-2026-10-14.md';raw=registry.read_bytes();t=json.loads(raw);old=copy.deepcopy(t);lr=ledger.read_bytes()
assert (t['newAccepted'],t['latestAcceptance'],t['remaining'])==(19,'R041',1)
assert t['tasks'][708]['parent_disposition']=='ARCHIVED_PREFREEZE_NO_NOMINEE'
assert not any(e.get('taskId')==d['taskId'] or e.get('brief')==br['brief'] for e in t['tasks'])
idx=len(t['tasks']);entry=dict(d,parent_thread=owner,role='discovery',round=205,clientRequestId='twenty-20261023-fresh-structural-r205-codex-astra-r1',source_index=329,source_title='Counterexamples to the duality conjecture for metric entropy',output='frontier/campaigns/2026-10-14/fresh-structural-discovery-r205/',brief=br['brief'],brief_sha256=br['brief_sha256'],brief_bytes=br['brief_bytes'],parent_count_at_dispatch=19,accepted=False,count_change=0,publication='STOPPED',dispatch_receipt='discovery-structural-r205-parent/dispatch.json',prospective_isolation='discovery-structural-r205-parent/prospective-isolation.json',status_provenance='Actual async dispatch response only; no subsequent liveness poll.',parent_full_intake_pending=True)
t['tasks'].append(entry)
note='Structural204 archived PREFREEZE/no nominee, zero count. Distinct Structural205 discovery dispatched on Source329 metric-entropy duality, Codex/GPT-6 Astra/xhigh/default. No author theorem or grade yet. Campaign19/20 latestR041 one remains; publicationSTOPPED. All prior and foreign task records preserved.'
t['last_parent_progress']=note;s=t['current_work_snapshot'];s.update(observed_utc=now,note=note)
s['structural205_dispatch']={'task_index':idx,'taskId':d['taskId'],'status':d['status'],'source_index':329,'brief':br['brief'],'brief_sha256':br['brief_sha256'],'output':entry['output'],'dispatch_receipt':entry['dispatch_receipt'],'count_change':0}
if 'active_task_indices' in s:s['active_task_indices']=[*s['active_task_indices'],idx]
if 't3_last_polled_running' in s:s['t3_last_polled_running']=[*s['t3_last_polled_running'],d['taskId']]
assert t['tasks'][:-1]==old['tasks']
assert all(t[k]==old[k] for k in old if k not in ['tasks','current_work_snapshot','last_parent_progress'])
assert all(s[k]==v for k,v in old['current_work_snapshot'].items() if k not in ['observed_utc','note','active_task_indices','t3_last_polled_running'])
heading='## Structural205 distinct discovery dispatched: Source329 metric-entropy duality'
assert heading.encode() not in lr
append='\n'+heading+'\n\nAfter Structural204 was archived PREFREEZE/no nominee with zero count, parent dispatched one distinct discovery task on Source329, Counterexamples to the duality conjecture for metric entropy. The actual async response selects **Codex / GPT-6 Astra / xhigh / default**, matching the live model descriptors and inherited options. See [complete brief](campaigns/2026-10-14/expanded-target-2026-10-17/fresh-structural-r205-brief.txt) and [dispatch receipt](campaigns/2026-10-14/discovery-structural-r205-parent/dispatch.json).\n\nBefore creation, literal structural205 guards were verified in the original initial foreign briefs identified by shared coordination metadata, using hashes/literal checks only. All 335 inherited explicit wildcard/no-r patterns, every substring guard and all closed targets remain protected. No foreign mathematical body or liveness was inspected. Parent selected only the exact Source329 catalogue slice and complete-tree metadata: one canonical folder, 14 entries/11 blobs. Actual proof/interface, primary and guarded original-history reading remains the discovery agent’s work; no parent semantic source reading or history clearance is claimed.\n\nThe task must identify a proved additional operation after the strongest compatible source/classical reduction, preserve any frozen scope, and return a full author-proof nominee or honest PREFREEZE/no nominee. No grade or count is assigned. **19/20, latest R041, one remaining; publication STOPPED.**\n'
assert registry.read_bytes()==raw and ledger.read_bytes()==lr
tmp=registry.with_suffix('.structural205.tmp');tmp.write_text(json.dumps(t,indent=2)+'\n');assert registry.read_bytes()==raw;os.replace(tmp,registry)
assert ledger.read_bytes()==lr;ledger.write_bytes(lr+append.encode())
out={'observed_utc':now,'added_task_index':idx,'taskId':d['taskId'],'all_previous_tasks_unchanged':True,'foreign_snapshot_entries_preserved':True,'count_change':0,'status_from_actual_dispatch_only':True}
(P/'integration-record.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
