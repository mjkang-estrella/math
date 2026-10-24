#!/usr/bin/env python3
"""Register only the actual Structural209 dispatch, preserving previous task records."""
from pathlib import Path
import copy,datetime,hashlib,json,os
P=Path(__file__).resolve().parent; C=P.parent; PROJECT=C.parents[2]
read=lambda p:json.loads(p.read_bytes()); sha=lambda b:hashlib.sha256(b).hexdigest()
d=read(P/'dispatch.json'); br=read(P/'brief-record.json'); isolation=read(P/'prospective-isolation.json'); owner='164b1204-be68-4540-94bb-0b91055c4381'; now=datetime.datetime.now(datetime.timezone.utc).isoformat()
assert read(P/'runtime.json')['parentThreadId']==isolation['parent_thread']==owner
assert d['status'] in ['queued','running'] and d['providerInstanceId']=='codex' and d['model']=='gpt-6-astra'
assert {e['id']:e['value'] for e in d['options']}=={'reasoningEffort':'xhigh','serviceTier':'default'}
assert sha((PROJECT/br['brief']).read_bytes())==br['brief_sha256']
assert isolation['root_and_brief_absent_when_checked'] and all(e['present'] for e in isolation['initial_brief_checks_before_new_root_or_brief'])
registry=C/'tasks.json'; ledger=PROJECT/'frontier/NEW-TEN-2026-10-14.md'; raw=registry.read_bytes(); t=json.loads(raw); old=copy.deepcopy(t); lr=ledger.read_bytes()
assert (t['newAccepted'],t['latestAcceptance'],t['remaining'])==(19,'R041',1)
assert t['tasks'][719]['parent_disposition']=='ARCHIVED_PREFREEZE_NO_NOMINEE'
assert not any(e.get('taskId')==d['taskId'] or e.get('brief')==br['brief'] for e in t['tasks'])
idx=len(t['tasks']); entry=dict(d,parent_thread=owner,role='discovery',round=209,clientRequestId='twenty-20261023-fresh-structural-r209-codex-astra-r1',source_index=333,source_title='Smooth isometric immersions of closed surfaces into Euclidean four-space',output='frontier/campaigns/2026-10-14/fresh-structural-discovery-r209/',brief=br['brief'],brief_sha256=br['brief_sha256'],brief_bytes=br['brief_bytes'],parent_count_at_dispatch=19,accepted=False,count_change=0,publication='STOPPED',dispatch_receipt='discovery-structural-r209-parent/dispatch.json',prospective_isolation='discovery-structural-r209-parent/prospective-isolation.json',status_provenance='Actual async dispatch response only; no subsequent liveness poll.',parent_full_intake_pending=True)
assert entry['output'].rstrip('/')==isolation['new_root']; t['tasks'].append(entry)
note='Structural208 archived PREFREEZE/no nominee, zero count. Distinct Structural209 discovery dispatched on Source333 smooth isometric immersions of closed surfaces into Euclidean four-space, Codex/GPT-6 Astra/xhigh/default. No author theorem or grade yet. Campaign19/20 latestR041 one remains; publicationSTOPPED. All prior and foreign task records preserved.'
t['last_parent_progress']=note; s=t['current_work_snapshot']; s.update(observed_utc=now,note=note)
s['structural209_dispatch']={'task_index':idx,'taskId':d['taskId'],'status':d['status'],'source_index':333,'brief':br['brief'],'brief_sha256':br['brief_sha256'],'output':entry['output'],'dispatch_receipt':entry['dispatch_receipt'],'count_change':0}
if 'active_task_indices' in s: s['active_task_indices']=[*s['active_task_indices'],idx]
if 't3_last_polled_running' in s: s['t3_last_polled_running']=[*s['t3_last_polled_running'],d['taskId']]
assert t['tasks'][:-1]==old['tasks']
assert all(t[k]==old[k] for k in old if k not in ['tasks','current_work_snapshot','last_parent_progress'])
assert all(s[k]==v for k,v in old['current_work_snapshot'].items() if k not in ['observed_utc','note','active_task_indices','t3_last_polled_running'])
heading='## Structural209 distinct discovery dispatched: Source333 smooth isometric surface immersions'
assert heading.encode() not in lr
append='\n'+heading+'\n\nAfter Structural208 was archived PREFREEZE/no nominee with zero count, parent dispatched one distinct discovery task on Source333, smooth isometric immersions of closed surfaces into Euclidean four-space. The actual async response selects **Codex / GPT-6 Astra / xhigh / default**, matching live descriptors and inherited options. See [complete brief](campaigns/2026-10-14/expanded-target-2026-10-17/fresh-structural-r209-brief.txt) and [dispatch receipt](campaigns/2026-10-14/discovery-structural-r209-parent/dispatch.json).\n\nBefore creating the new namespace, parent checked the literal structural209 guard and hashes of original initial foreign briefs identified by shared coordination metadata. All339 inherited wildcard/no-r patterns and162 substring guards remain; structural209 and its no-r twin bring the explicit total to341. No foreign mathematical body or liveness was inspected. Parent selected only the exact Source333 catalogue slice and canonical subtree metadata: one folder,16entries,14blobs. A prospective heading filter excludes administrative/provenance/contribution-screen sections from mathematical evidence before body display; this does not reopen any old scan. Actual source/primary/guarded-history proof reading remains the discovery agent’s work; no parent source-body reading or history clearance is claimed.\n\nThe task must carry the strongest compatible source/classical reduction and prove an identifiable additional operation before nominating a theorem. No scope weakening or grade shopping on completed families. No author theorem, grade, acceptance or count is assigned. **19/20, latest R041, one remaining; publication STOPPED.**\n'
assert registry.read_bytes()==raw and ledger.read_bytes()==lr
tmp=registry.with_suffix('.structural209.tmp'); tmp.write_text(json.dumps(t,indent=2)+'\n'); assert registry.read_bytes()==raw; os.replace(tmp,registry)
assert ledger.read_bytes()==lr; ledger.write_bytes(lr+append.encode())
out={'observed_utc':now,'added_task_index':idx,'taskId':d['taskId'],'all_previous_tasks_unchanged':True,'foreign_snapshot_entries_preserved':True,'count_change':0,'status_from_actual_dispatch_only':True}
(P/'integration-record.json').write_text(json.dumps(out,indent=2)+'\n'); print(json.dumps(out,indent=2))
