#!/usr/bin/env python3
"""Archive an owned prefreeze discovery, assigning no mathematical grades."""
from pathlib import Path
import copy,datetime,hashlib,json,os
P=Path(__file__).resolve().parent;C=P.parents[1];PROJECT=C.parents[2]
read=lambda p:json.loads(p.read_bytes());now=datetime.datetime.now(datetime.timezone.utc).isoformat()
status=read(P/'task-status.json');replay=read(P/'replay.json');assert status['status']=='completed' and status['workState']=='result_available' and not status['hasPendingChildRuns'];assert replay['author_originals_unchanged']
registry=C/'tasks.json';ledger=PROJECT/'frontier/NEW-TEN-2026-10-14.md';raw=registry.read_bytes();lr=ledger.read_bytes();t=json.loads(raw);old=copy.deepcopy(t);idx=757;e=t['tasks'][idx]
assert e['taskId']==status['taskId'] and e['parent_thread']=='164b1204-be68-4540-94bb-0b91055c4381' and e['parent_full_intake_pending']
assert (t['newAccepted'],t['latestAcceptance'],t['remaining'])==(19,'R041',1)
rel=str(P.relative_to(C));e.update(status='completed',workState='result_available',hasPendingChildRuns=False,parent_full_intake_pending=False,parent_disposition='ARCHIVED_PREFREEZE_NO_NOMINEE',parent_intake=rel+'/intake.json',correctness=None,contribution=None,accepted=False,count_change=0,author_anchors=replay['anchors'])
note='Structural222 archived PREFREEZE/no nominee after complete authored-prose intake and read-only artifact replay. Local plane/frequency calculations retained; critical physical density-center transfer and full packing remain unresolved. No grades/count. Campaign19/20, latestR041, one remaining; publication STOPPED.'
t['last_parent_progress']=note;s=t['current_work_snapshot'];s.update(observed_utc=now,note=note)
if 'active_task_indices' in s:s['active_task_indices']=[x for x in s['active_task_indices'] if x!=idx]
if 't3_last_polled_running' in s:s['t3_last_polled_running']=[x for x in s['t3_last_polled_running'] if x!=status['taskId']]
s['structural222_dispatch']['status']='completed';s['structural222_parent_intake']={'task_index':idx,'disposition':e['parent_disposition'],'intake':e['parent_intake'],'count_change':0,'correctness':None,'contribution':None}
assert all(t['tasks'][i]==old['tasks'][i] for i in range(len(t['tasks'])) if i!=idx)
assert all(t[k]==old[k] for k in old if k not in ('tasks','current_work_snapshot','last_parent_progress'))
allowed={'observed_utc','note','active_task_indices','t3_last_polled_running','structural222_dispatch'};assert all(s[k]==v for k,v in old['current_work_snapshot'].items() if k not in allowed)
heading='## Structural222 prefreeze archive: stationary-varifold local estimates';assert heading.encode() not in lr
append='\n'+heading+'\n\nParent read the complete authored derivations, source-operation comparison, reading limits and handoffs. Schur-complement plane approximation, fixed-scale spatial frequency comparison and homogeneous/high-frequency classification are retained as research calculations. The critical physical density-center transfer still lacks the joint inner-scale/error rate, and a full compatible packing construction remains unproved. No stronger singular-set theorem was frozen or adopted; original I27 scope stays unchanged. [Parent assessment](campaigns/2026-10-14/structural-r220-isolated-continuation/discovery-structural-r222-parent/assessment.md).\n\nRead-only replay matched all three detached anchors,92 selected files and15directories; all185 author files and31directories remained unchanged. Parent bound29 canonical blobs,40 source-read extents,23 coverage records,26 primary extents,eight primary PDFs and four original-history ranges without inheriting semantic proof coverage. Six tiny copied controls passed. Selective primary/history reading, inaccessible errata, extraction limits, late comparisons/recovery, disclosed editorial exposures and Lean404s remain recorded. **PREFREEZE/no nominee; no correctness/contribution grade or count.19/20,latestR041,one remaining; publication STOPPED.**\n'
intake={'observed_utc':now,'task_index':idx,'taskId':status['taskId'],'parent_disposition':e['parent_disposition'],'assessment':str((P/'assessment.md').relative_to(PROJECT)),'artifact_replay':replay,'correctness':None,'contribution':None,'accepted':False,'count_change':0,'publication':'STOPPED'}
(P/'intake.json').write_text(json.dumps(intake,indent=2)+'\n')
assert registry.read_bytes()==raw and ledger.read_bytes()==lr;tmp=registry.with_suffix('.structural222-intake.tmp');tmp.write_text(json.dumps(t,indent=2)+'\n');assert registry.read_bytes()==raw;os.replace(tmp,registry);assert ledger.read_bytes()==lr;ledger.write_bytes(lr+append.encode())
record={'observed_utc':now,'owned_changed_task_indices':[idx],'all_other_tasks_unchanged':True,'foreign_snapshot_entries_preserved':True,'append_only_ledger':True,'count_change':0};(P/'intake-record.json').write_text(json.dumps(record,indent=2)+'\n');print(json.dumps(record))
