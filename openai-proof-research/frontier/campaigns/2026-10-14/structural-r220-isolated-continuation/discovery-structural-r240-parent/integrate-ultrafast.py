#!/usr/bin/env python3
"""Persist the user-requested runtime tier and the same-thread S240 continuation."""
from pathlib import Path
import copy,datetime,json,os
P=Path(__file__).resolve().parent;C=P.parents[1];PROJECT=C.parents[2]
r=json.loads((P/'ultrafast-transition.json').read_bytes());resume=r['resume'];oldstatus=r['stopped_task'];owner='164b1204-be68-4540-94bb-0b91055c4381'
assert oldstatus['status']=='interrupted' and not oldstatus['hasPendingChildRuns']
cfg=r['verified_configuration'];assert cfg['modelSelection']['model']=='gpt-6-astra'
assert {x['id']:x['value']for x in cfg['modelSelection']['options']}=={'reasoningEffort':'xhigh','serviceTier':'ultrafast'}
assert resume['delivery']=='started' and resume['threadId']==cfg['threadId']
registry=C/'tasks.json';ledger=PROJECT/'frontier/NEW-TEN-2026-10-14.md';raw=registry.read_bytes();lr=ledger.read_bytes();t=json.loads(raw);before=copy.deepcopy(t);now=datetime.datetime.now(datetime.timezone.utc).isoformat()
e=t['tasks'][806];assert e['taskId']==oldstatus['taskId'] and e['parent_thread']==owner
assert not any(x.get('taskId')==resume['taskId']for x in t['tasks'])
assert (t['newAccepted'],t['latestAcceptance'],t['remaining'])==(19,'R041',1)
idx=len(t['tasks']);rel=P.relative_to(C).as_posix();e.update(status='interrupted',workState='result_available',hasPendingChildRuns=False,parent_full_intake_pending=False,parent_disposition='CONTINUED_SAME_SCOPE_ULTRAFAST',superseded_by_task_index=idx,superseded_by_taskId=resume['taskId'],status_provenance='Owned terminal stop confirmed for user-requested service-tier change, not a mathematical disposition.')
new={k:copy.deepcopy(e[k])for k in ['parent_thread','role','round','source_index','source_title','output','brief','brief_sha256','brief_bytes','parent_count_at_dispatch','publication','isolation_wrapper','foreign_initial_exclusion_literal']}
new.update(taskId=resume['taskId'],childThreadId=resume['threadId'],childRunId=resume['runId'],providerInstanceId='codex',model='gpt-6-astra',options=cfg['modelSelection']['options'],status=resume['status'],workState='working',parent_full_intake_pending=True,accepted=False,count_change=0,continuation_of_task_index=806,continuation_of_taskId=e['taskId'],clientRequestId='twenty-20261025-r240-resume-ultrafast',dispatch_receipt=rel+'/ultrafast-transition.json',status_provenance='Same-thread resume response; runtime selection independently read back as ultrafast. No later pending-task poll.',runtime_override='User instruction: ultrafast supersedes default-tier text in the unchanged original brief.')
t['tasks'].append(new)
note='User requires ultrafast for all owned work. Parent runtime already ultrafast; S240 resumed in the same thread and author root with verified gpt-6-astra/xhigh/ultrafast. Original default-tier run retained as interrupted technical predecessor. No mathematical scope, grade or count changed; 19/20,latestR041,one remaining; publication STOPPED.'
t['last_parent_progress']=note;s=t['current_work_snapshot'];s.update(observed_utc=now,note=note)
s['structural_runtime_preference']={'parent_thread':owner,'providerInstanceId':'codex','model':'gpt-6-astra','options':{'reasoningEffort':'xhigh','serviceTier':'ultrafast'},'user_instruction':r['user_instruction'],'applies_to':'All current and future tasks owned by this parent; explicitly request and verify ultrafast. Supersedes earlier default service tier instructions.','record':rel+'/ultrafast-transition.json'}
if 'active_task_indices'in s:s['active_task_indices']=[x for x in s['active_task_indices']if x!=806]+[idx]
if 't3_last_polled_running'in s:s['t3_last_polled_running']=[x for x in s['t3_last_polled_running']if x!=e['taskId']]+[resume['taskId']]
s['structural240_dispatch'].update(task_index=idx,taskId=resume['taskId'],status=resume['status'],dispatch_receipt=new['dispatch_receipt'],original_task_index=806,service_tier='ultrafast')
assert all(t['tasks'][i]==before['tasks'][i]for i in range(len(before['tasks']))if i!=806)
assert all(t[k]==before[k]for k in before if k not in('tasks','current_work_snapshot','last_parent_progress'))
allowed={'observed_utc','note','active_task_indices','t3_last_polled_running','structural240_dispatch'}
assert all(s[k]==v for k,v in before['current_work_snapshot'].items()if k not in allowed)
heading='## User runtime instruction: ultrafast for all owned tasks';assert heading.encode()not in lr
append='\n'+heading+'\n\nThe user explicitly requested ultrafast for all tasks. Parent runtime already reports ultrafast. S240 had started on default: it was interrupted solely for the tier change, configured to gpt-6-astra/xhigh/ultrafast with readback verification, and resumed in the same child conversation and exact author root. Existing conversation, files, assignment and any frozen scope are preserved. The original dispatch remains an immutable historical receipt; the new task records the technical continuation. [Transition and verified configuration](campaigns/2026-10-14/structural-r220-isolated-continuation/discovery-structural-r240-parent/ultrafast-transition.json).\n\nEvery future owned discovery and review must explicitly request and verify serviceTier ultrafast; this overrides old default-tier brief headers. Unrelated foreign-parent tasks are not controlled. No mathematical disposition or count changes: **19/20, latest R041, one remaining; publication STOPPED.**\n'
assert registry.read_bytes()==raw and ledger.read_bytes()==lr
tmp=registry.with_suffix('.ultrafast-transition.tmp');tmp.write_text(json.dumps(t,indent=2)+'\n');assert registry.read_bytes()==raw;os.replace(tmp,registry);assert ledger.read_bytes()==lr;ledger.write_bytes(lr+append.encode())
out={'observed_utc':now,'updated_predecessor_index':806,'continuation_task_index':idx,'continuation_taskId':resume['taskId'],'other_tasks_unchanged':True,'foreign_snapshot_preserved':True,'count_change':0}
(P/'ultrafast-integration.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
